:- dynamic(def/2).

:- ['coffee_bat_fct'].

experiment(QueueSize,FileName,TimeOutC,TimeOutP) :- 
        local_time_and_date_as_string(TimeS),
        atom_string(Time,TimeS),
        retractall(def(isFirst(_,_),_)),
        retractall(def(empty(_),_)),
        retractall(def(lastFree(_),_)),
        retractall(def(full(_),_)),
        retractall(def(enqueue(_,_,_),_)),
        retractall(def(dequeue(_,_,_),_)),
        def(isFirst(Q1,P1),QueueSize,F1),
        def(empty(Q2),QueueSize,F2),
        def(lastFree(Q3),QueueSize,F3),
        def(full(Q4),QueueSize,F4),
        def(enqueue(Qold5,P5,Qnew5),QueueSize,F5),
        def(dequeue(Qold6,P6,Qnew6),QueueSize,F6),
        assert(def(isFirst(Q1,P1),F1)),
        assert(def(empty(Q2),F2)),
        assert(def(lastFree(Q3),F3)),
        assert(def(full(Q4),F4)),
        assert(def(enqueue(Qold5,P5,Qnew5),F5)),
        assert(def(dequeue(Qold6,P6,Qnew6),F6)),
        measure_time_with_limit(construct_characteristic_graph(main),
                                TimeOutC,TWC,TCC),
        (TWC = timeout ->
            (Nodes = 'n/a', Edges = 'n/a', 
             TW1 = 'n/a',
             TW2 = 'n/a',
             % TW3 = 'n/a',
             TW4 = 'n/a',
             % TW5 = 'n/a',
             TC1 = 'n/a',
             TC2 = 'n/a',
             % TC3 = 'n/a',
             TC4 = 'n/a'
             % TC5 = 'n/a'
             );
            (number_of_nodes(Nodes),
             number_of_edges(Edges),
             measure_time_with_limit(verify(main,prop1),TimeOutP,TW1,TC1),
             measure_time_with_limit(verify(main,prop2),TimeOutP,TW2,TC2),
             % measure_time_with_limit(verify(main,prop3),TimeOutP,TW3,TC3),
             measure_time_with_limit(verify(main,prop4),TimeOutP,TW4,TC4))),
             % measure_time_with_limit(verify(main,prop5),TimeOutP,TW5,TC5))),
        Row = [Time,
               QueueSize,
               Nodes,
               Edges,
               TWC,TCC,
               TW1,TC1,
               TW2,TC2,
               % TW3,TC3,
               TW4,TC4
               % TW5,TC5
              ],
             append_to_csv(FileName,Row).     

number_of_nodes(Nodes) :-
        cg_number_of_nodes(main,Nodes).
number_of_edges(Edges) :-
        count(cg_edge(main,_,_,_,_), Edges).

def(isFirst(Q,P),N,F) :-
        generate_queue_term_vars(QTerm,N,Vars),
        Vars = [First|Others],
        First = P,
        construct_exists(Others,Q=QTerm,F).
def(empty(Q),N,F) :-
        generate_queue_term_inst(QTerm,N,'#e'),
        F = (Q=QTerm).
def(lastFree(Q),N,F) :-
        generate_queue_term_vars(QTerm,N,Vars),
        instantiate_last(Vars,'#e',QTerm,Vars2),
        construct_exists(Vars2,Q=QTerm,F).
def(full(Q),N,F) :-
        generate_queue_term_vars(QTerm,N,Vars),
        construct_inequalities(Vars,'#e',Inequalities),
        construct_exists(Vars,Inequalities*(Q=QTerm),F).
def(enqueue(Qold,P,Qnew),N,F) :-
        construct_enqueue_disjuncts(Qold,P,Qnew,N,Disj),
        disjoin(Disj,F).
def(dequeue(Qold,P,Qnew),N,F) :-
        N1 is N-1,
        generate_fresh_variables(N1,Vars),
        append(Vars,['#e'],VarsE),
        QoldTerm =.. ['#q',P|Vars],
        QnewTerm =.. ['#q'|VarsE],
        construct_exists(Vars,(Qold=QoldTerm)*(Qnew=QnewTerm),F).

generate_queue_term_vars(QTerm,N,Vars) :-
        generate_fresh_variables(N,Vars),
        QTerm =.. ['#q'|Vars].

generate_fresh_variables(0,[]).
generate_fresh_variables(N,[_Var|Vars]) :-
        N > 0, !,
        N1 is N-1,
        generate_fresh_variables(N1,Vars).

generate_queue_term_inst(QTerm,N,Const) :-
        generate_inst_list(N,Const,List),
        QTerm =.. ['#q'|List].

generate_inst_list(0,_Const,[]).
generate_inst_list(N,Const,[Const|List]) :-
        N > 0, !,
        N1 is N-1,
        generate_inst_list(N1,Const,List).

instantiate_last([Var],Const,_QTerm,[]) :- !,
        Var=Const.
instantiate_last([Var|Vars],Const,QTerm,[Var|Vars2]) :- !,
        instantiate_last(Vars,Const,QTerm,Vars2).

construct_inequalities(Vars,Const,InequalitiesFormula) :-
        construct_inequalities2(Vars,Const,Inequalities),
        conjoin(Inequalities,InequalitiesFormula).

construct_inequalities2([],_Const,[]) :- !.
construct_inequalities2([Var],Const,[-(Var=Const)]) :- !.
construct_inequalities2([Var|Vars],Const,[-(Var=Const)|Inequalities]) :-
        !,
        construct_inequalities2(Vars,Const,Inequalities).

construct_enqueue_disjuncts(Qold,P,Qnew,N,Disj) :-
        construct_enqueue_disjuncts2(Qold,P,Qnew,N,0,Disj).
construct_enqueue_disjuncts2(_Qold,_P,_Qnew,N,N,[]) :- !.
construct_enqueue_disjuncts2(Qold,P,Qnew,N,M,[Disj|Disjuncts]) :-
        M1 is M+1,
        construct_enqueue_disjuncts2(Qold,P,Qnew,N,M1,Disjuncts),
        construct_enqueue_disjunct(Qold,P,Qnew,N,M,Disj).

construct_enqueue_disjunct(Qold,P,Qnew,N,M,Disj) :-
        M1 is N-M,
        M2 is N-M-1,
        generate_fresh_variables(M,Vars),
        generate_inst_list(M1,'#e',EList1),
        generate_inst_list(M2,'#e',EList2),
        construct_inequalities(Vars,'#e',Inequalities),
        append(Vars,EList1,Args1),
        append(Vars,[P|EList2],Args2),
        QoldTerm =.. ['#q'|Args1],
        QnewTerm =.. ['#q'|Args2],
        construct_exists(Vars,Inequalities*(Qold=QoldTerm)*(Qnew=QnewTerm),Disj).

construct_exists([],F,F) :- !.
construct_exists(Vars,F,some(Vars,F)) :- !.
