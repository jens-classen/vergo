%:- module(bdd).

:- use_module(fol).
:- use_module('../lib/utils').

%:- use_module(library(graph_algorithms)).
%:- use_module(library(graphviz)).

:- dynamic bdd_node/4. % table entries
:- dynamic nodes/1.    % highest table index
:- dynamic cached_ite/4.

%:- export construct_bdd/2.

nodes(1).

bdd_node('___undef','___undef','___undef',0).
bdd_node('___undef','___undef','___undef',1).

formula2bdd(Fml,BDD) :-
        preprocess(Fml,FmlP),
        construct_bdd(FmlP,BDD).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% always use variable *lists* in quantifiers
preprocess(some(X,Fml),R) :-
        var(X), !,
        preprocess(some([X],Fml),R).
preprocess(all(X,Fml),R) :-
        var(X), !,
        preprocess(all([X],Fml),R).

% push negation inwards to try the other cases
preprocess(some(Vars,-Fml),R) :-
        push_negation_inside(-Fml,Fml2),
        -Fml \= Fml2, !,
        preprocess(some(Vars,Fml2),R).
preprocess(all(Vars,-Fml),R) :-
        push_negation_inside(-Fml,Fml2),
        -Fml \= Fml2, !,
        preprocess(all(Vars,Fml2),R).

% ?[X]:(X=T)&F --> F with X replaced by T
preprocess(some([X|Vars],Fml),R) :-
        equality_conjunct(X,Y,Fml),!,
        subv(X,Y,Fml,Fml2),
        preprocess(some(Vars,Fml2),R).
% ![X]:~(X=T)|F --> F with X replaced by T
preprocess(all([X|Vars],Fml),R) :-
        inequality_disjunct(X,Y,Fml),!,
        subv(X,Y,Fml,Fml2),
        preprocess(all(Vars,Fml2),R).

% distribute "exists" over disjunction
preprocess(some(Vars,Fml1+Fml2),R) :- !,
        preprocess(some(Vars,Fml1)+some(Vars,Fml2),R).
% distribute "forall" over conjunction
preprocess(all(Vars,Fml1*Fml2),R) :- !,
        preprocess(all(Vars,Fml1)*all(Vars,Fml2),R).

% drop quantifiers for non-appearing variables
preprocess(some(Vars1,Fml),R) :-
        term_variables(Fml,Vars2),
        intersection2(Vars1,Vars2,Vars3),
        Vars1 \= Vars3, !,
        preprocess(some(Vars3,Fml),R).
preprocess(all(Vars1,Fml),R) :-
        term_variables(Fml,Vars2),
        intersection2(Vars1,Vars2,Vars3),
        Vars1 \= Vars3, !,
        preprocess(all(Vars3,Fml),R).

% drop empty quantifiers
preprocess(some([],Fml),R) :- !,
        preprocess(Fml,R).
preprocess(all([],Fml),R) :- !,
        preprocess(Fml,R).

% combine quantifiers
preprocess(some(Vars1,some(Vars2,Fml)),R) :- !,
        append(Vars1,Vars2,Vars),
        preprocess(some(Vars,Fml),R).
preprocess(all(Vars1,all(Vars2,Fml)),R) :- !,
        append(Vars1,Vars2,Vars),
        preprocess(all(Vars,Fml),R).

% reduce scope of existential to conjuncts where that variable appears
preprocess(some(Vars,Fml),R) :-
        conjuncts_with_without(Vars,Fml,ConW,ConWO),
        ConWO \= true, !,
        preprocess(some(Vars,ConW)*ConWO,R).
% reduce scope of universal to conjuncts where that variable appears
preprocess(all(Vars,Fml),R) :-
        disjuncts_with_without(Vars,Fml,DisW,DisWO),
        DisWO \= false, !,
        preprocess(all(Vars,DisW)+DisWO,R).

% recursive preprocessing of subformulas
preprocess(some(Vars,Fml),R) :-
        simplify_atom(some(Vars,Fml),S),
        S \= some(Vars,Fml), !,
        preprocess(S,R).
preprocess(all(Vars,Fml),R) :-
        simplify_atom(all(Vars,Fml),S),
        S \= all(Vars,Fml), !,
        preprocess(S,R).

preprocess(some(Vars,Fml),some(Vars,R)) :- !,
        preprocess(Fml,R).
preprocess(all(Vars,Fml),all(Vars,R)) :- !,
        preprocess(Fml,R).

preprocess(Fml1<=>Fml2,R) :- !,
        preprocess((Fml1=>Fml2)*(Fml2=>Fml1),R).
preprocess(Fml1=>Fml2,R) :- !,
        preprocess((-Fml1)+Fml2,R).
preprocess(Fml1<=Fml2,R) :- !,
        preprocess(Fml1+(-Fml2),R).
preprocess(-some(Vars,Fml),R) :- !,
        push_negation_inside(-Fml,Fml2),
        preprocess(all(Vars,Fml2),R).
preprocess(-all(Vars,Fml),R) :- !,
        push_negation_inside(-Fml,Fml2),
        preprocess(some(Vars,Fml2),R).
preprocess(-Fml,-R) :- !,
        preprocess(Fml,R).
preprocess(Fml1+Fml2,R1+R2) :- !,
        preprocess(Fml1,R1),
        preprocess(Fml2,R2).
preprocess(Fml1*Fml2,R1*R2) :- !,
        preprocess(Fml1,R1),
        preprocess(Fml2,R2).

% else do nothing
preprocess(R,R).

equality_conjunct(X,Y,(A=B)) :-
        X==A,
        Y=B.
equality_conjunct(X,Y,(A=B)) :-
        X==B,
        Y=A.
equality_conjunct(X,Y,Fml1*Fml2) :-
        equality_conjunct(X,Y,Fml1);
        equality_conjunct(X,Y,Fml2).

inequality_disjunct(X,Y,-(A=B)) :-
        X==A,
        Y=B.
inequality_disjunct(X,Y,-(A=B)) :-
        X==B,
        Y=A.
inequality_disjunct(X,Y,Fml1+Fml2) :-
        inequality_disjunct(X,Y,Fml1);
        inequality_disjunct(X,Y,Fml2).

conjuncts_with_without(Vars,Fml1*Fml2,ConW,ConWO) :- !,
        conjuncts_with_without(Vars,Fml1,ConW1,ConWO1),
        conjuncts_with_without(Vars,Fml2,ConW2,ConWO2),
        ConW3 = (ConW1 * ConW2),
        ConWO3 = (ConWO1 * ConWO2),
        remove_true(ConW3,ConW),
        remove_true(ConWO3,ConWO).
conjuncts_with_without(Vars,Fml,Fml,true) :-
        term_variables(Fml,FVars), 
        not(disjoint2(Vars,FVars)), !.
conjuncts_with_without(Vars,Fml,true,Fml) :-
        term_variables(Fml,FVars),
        disjoint2(Vars,FVars).

remove_true(Fml*true,Fml) :- !.
remove_true(true*Fml,Fml) :- !.
remove_true(Fml,Fml).

disjuncts_with_without(Vars,Fml1+Fml2,DisW,DisWO) :- !,
        disjuncts_with_without(Vars,Fml1,DisW1,DisWO1),
        disjuncts_with_without(Vars,Fml2,DisW2,DisWO2),
        DisW3 = (DisW1 + DisW2),
        DisWO3 = (DisWO1 + DisWO2),
        remove_false(DisW3,DisW),
        remove_false(DisWO3,DisWO).
disjuncts_with_without(Vars,Fml,Fml,false) :-
        term_variables(Fml,FVars), 
        not(disjoint2(Vars,FVars)), !.
disjuncts_with_without(Vars,Fml,false,Fml) :-
        term_variables(Fml,FVars),
        disjoint2(Vars,FVars).

remove_false(Fml+false,Fml) :- !.
remove_false(false+Fml,Fml) :- !.
remove_false(Fml,Fml).

push_negation_inside(-(Fml1+Fml2),R1*R2) :- !,
        push_negation_inside(-Fml1,R1),
        push_negation_inside(-Fml2,R2).
push_negation_inside(-(Fml1*Fml2),R1+R2) :- !,
        push_negation_inside(-Fml1,R1),
        push_negation_inside(-Fml2,R2).
push_negation_inside(-all(Vars,Fml),some(Vars,R)) :- !,
        push_negation_inside(-Fml,R).
push_negation_inside(-some(Vars,Fml),all(Vars,R)) :- !,
        push_negation_inside(-Fml,R).
push_negation_inside(-(-Fml),R) :- !,
        push_negation_inside(Fml,R).
push_negation_inside(-(Fml1=>Fml2),R1*R2) :- !,
        push_negation_inside(Fml1,R1),
        push_negation_inside(-Fml2,R2).
push_negation_inside(-(Fml1<=Fml2),R1*R2) :- !,
        push_negation_inside(-Fml1,R1),
        push_negation_inside(Fml2,R2).
push_negation_inside(-(Fml1<=>Fml2),R1+R2) :- !,
        push_negation_inside(-(Fml1=>Fml2),R1),
        push_negation_inside(-(Fml1<=Fml2),R2).
push_negation_inside(Fml,Fml).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

bdd2formula(false,0) :- !.
bdd2formula(true,1) :- !.

bdd2formula(Label,BDD) :-
        bdd_node(Label,1,0,BDD),!.
bdd2formula(-Label,BDD) :-
        bdd_node(Label,0,1,BDD),!.
bdd2formula(Fml,BDD) :-
        bdd_node(Label,1,E,BDD),!,
        bdd2formula(FmlE,E),
        Fml = Label+((-Label)*FmlE).
bdd2formula(Fml,BDD) :-
        bdd_node(Label,0,E,BDD),!,
        bdd2formula(FmlE,E),
        Fml = (-Label)*FmlE.
bdd2formula(Fml,BDD) :-
        bdd_node(Label,T,1,BDD),!,
        bdd2formula(FmlT,T),
        Fml = (Label*FmlT)+(-Label).
bdd2formula(Fml,BDD) :-
        bdd_node(Label,T,0,BDD),!,
        bdd2formula(FmlT,T),
        Fml = Label*FmlT.

bdd2formula(Fml,BDD) :-
        bdd_node(Label,Then,Else,BDD),
        bdd2formula(Fml1,Then),
        bdd2formula(Fml2,Else),!,
        Fml = (Label*Fml1)+((-Label)*Fml2).

simplify_formula_bdd(Fml1,Fml2) :-
        formula2bdd(Fml1,BDD),
        bdd2formula(Fml2,BDD).

construct_bdd(Fml1<=>Fml2,BDD) :- !,
        construct_bdd(Fml1,BDD1),
        construct_bdd(Fml2,BDD2),
        construct_bdd(-Fml2,BDD3),
        ite(BDD1,BDD2,BDD3,BDD).
construct_bdd(Fml1=>Fml2,BDD) :- !,
        construct_bdd(Fml1,BDD1),
        construct_bdd(Fml2,BDD2),
        ite(BDD1,BDD2,1,BDD).
construct_bdd(Fml1<=Fml2,BDD) :- !,
        construct_bdd(Fml1,BDD1),
        construct_bdd(-Fml2,BDD2),
        ite(BDD1,1,BDD2,BDD).
construct_bdd(-Fml1,BDD) :- !,
        construct_bdd(Fml1,BDD1),
        ite(BDD1,0,1,BDD).
construct_bdd(Fml1+Fml2,BDD) :- !,
        construct_bdd(Fml1,BDD1),
        construct_bdd(Fml2,BDD2),
        ite(BDD1,1,BDD2,BDD).
construct_bdd(Fml1*Fml2,BDD) :- !,
        construct_bdd(Fml1,BDD1),
        construct_bdd(Fml2,BDD2),
        ite(BDD1,BDD2,0,BDD).
construct_bdd(true,1) :- !.
construct_bdd(false,0) :- !.
construct_bdd(-true,0) :- !.
construct_bdd(-false,1) :- !.
construct_bdd((X=Y),1) :- X==Y,!.
construct_bdd(-(X=Y),0) :- X==Y, !.
construct_bdd(Atom,BDD) :- !,
        bdd_atom(Atom),
        simplify_atom(Atom,AtomS),
        find_or_add_unique(AtomS,1,0,BDD).

find_or_add_unique(_Label,B,B,B) :- !.
find_or_add_unique(Label,Then,Else,BDD) :-
        bdd_node(Label,Then,Else,BDD),!.
find_or_add_unique(Label,Then,Else,BDD) :-
        retract(nodes(N)),
        N1 is N+1,
        assert(nodes(N1)),
        assert(bdd_node(Label,Then,Else,N1)),
        BDD=N1.

ite(1,F,_G,F) :- !.
ite(0,_F,G,G) :- !.
ite(F,1,0,F)  :- !.
ite(_F,G,G,G) :- !.

ite(F,G,H,R) :- cached_ite(F,G,H,R),!.

ite(F,G,H,R) :-
        bdd_node(LabelF,_,_,F),
        bdd_node(LabelG,_,_,G),
        bdd_node(LabelH,_,_,H),
        least_label(LabelF,LabelG,LabelH,X),
        branch(F,X,1,FT),
        branch(G,X,1,GT),
        branch(H,X,1,HT),
        branch(F,X,0,FF),
        branch(G,X,0,GF),
        branch(H,X,0,HF),
        ite(FT,GT,HT,T),
        ite(FF,GF,HF,E),
        find_or_add_unique(X,T,E,R),
        cache_ite(F,G,H,R).

bdd_conjoin(BDD1,BDD2,BDD) :-
        ite(BDD1,BDD2,0,BDD).
bdd_disjoin(BDD1,BDD2,BDD) :-
        ite(BDD1,1,BDD2,BDD).

least_label(L1,L2,L3,L) :-
        least_label(L1,L2,L4),
        least_label(L3,L4,L).

least_label('___undef',L,L) :- !.
least_label(L,'___undef',L) :- !.

least_label(L1,L2,L1) :-
        L1 @=< L2, !.
least_label(L1,L2,L2) :-
        L1 @>= L2, !.
        
        

branch(Node,Label,_Value,Result) :-
        bdd_node(Label2,_Then,_Else,Node),
        Label \= Label2,
        Result=Node.
branch(Node,Label,1,Result) :-
        bdd_node(Label,Result,_Else,Node).
branch(Node,Label,0,Result) :-
        bdd_node(Label,_Then,Result,Node).

cache_ite(F,G,H,R) :-
        assert(cached_ite(F,G,H,R)).

bdd_atom(some(_Vars,_Fml)).
bdd_atom(all(_Vars,_Fml)).
bdd_atom(Fml) :-
        Fml \= (_ <=> _),
        Fml \= (_  => _),
        Fml \= (_ <=  _),
        Fml \= (-_),
        Fml \= (_ + _),
        Fml \= (_ * _).

simplify_atom(some([X|Vars],Fml),some([X|Vars],Fml2)) :- !,
        term_to_atom(X,A),
        subv(X,A,Fml,Fml3),
        simplify_atom(some(Vars,Fml3),some(Vars,Fml4)),
        subv(A,X,Fml4,Fml2).
simplify_atom(some([],Fml),some([],Fml2)) :- !,
        simplify_formula_bdd(Fml,Fml2).

simplify_atom(all([X|Vars],Fml),all([X|Vars],Fml2)) :- !,
        term_to_atom(X,A),
        subv(X,A,Fml,Fml3),
        simplify_atom(all(Vars,Fml3),all(Vars,Fml4)),
        subv(A,X,Fml4,Fml2).
simplify_atom(all([],Fml),all([],Fml2)) :- !,
        simplify_formula_bdd(Fml,Fml2).

simplify_atom(Atom,Atom).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% BDD Output
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% print (unwinded) BDD 
print_bdd_tree(BDD) :-
        print_bdd_tree2(BDD,0).

print_bdd_tree2(0,N) :-
        print_tabs(N),
        writeln(0).
print_bdd_tree2(1,N) :-
        print_tabs(N),
        writeln(1).

print_bdd_tree2(BDD,N) :-
        bdd_node(L,T,E,BDD),
        print_tabs(N),
        writeln(L),
        N1 is N+1,
        print_bdd_tree2(T,N1),
        print_bdd_tree2(E,N1).

print_tabs(0) :- !.
print_tabs(N) :- !,
        write(' '),
        N1 is N-1,
        print_tabs(N1).

% draw BDD using graphviz interface
draw_bdd :-
        findall(e(N1,N2,1),(bdd_node(_,N2,_,N1),N1\=0,N1\=1),PosEdges),
        findall(e(N1,N2,0),(bdd_node(_,_,N2,N1),N1\=0,N1\=1),NegEdges),
        append(PosEdges,NegEdges,Edges),
        nodes(N),
        make_graph(N,Edges,Graph),
        view_graph(Graph,[edge_attrs_generator:bdd_edge_attr,
                          node_attrs_generator:bdd_node_attr,
                          layout:dot]).

% 0-egde => dashed line
bdd_edge_attr(_Graph,Edge,Attrs) :-
        Edge=e(_N1,_N2,0),
        Attrs=[style="dashed"].
% 1-edge => normal line
bdd_edge_attr(_Graph,Edge,Attrs) :-
        Edge=e(_N1,_N2,1),
        Attrs=[].
% non-leaf-node => label with Label
bdd_node_attr(_Graph,Node,Attrs) :-
        bdd_node(Label,_,_,Node),
        Label\='___undef',
        term_string((Label,Node),LabelS),
        Attrs=[label=LabelS].
% else label with 0 ...
bdd_node_attr(_Graph,0,Attrs) :-
        Attrs=[label=0].
% ... or 1
bdd_node_attr(_Graph,1,Attrs) :-
        Attrs=[label=1].

