/**
 
<module> BDD representation module

This module implements a representation and simplification mechanism for
formulas of first-order logic based on (ordered) binary decision
diagrams (BDD). The idea was sketched in

Jens Claßen: Planning and Verification in the Agent Language Golog.
PhD Thesis, Department of Computer Science, RWTH Aachen University,
2013.

The construction and manipulation algorithms used herein are based
upon the ITE algorithm described in

Karl S. Brace, Richard L. Rudell, and Randal E. Bryant. Efficient
implementation of a BDD package. In Richard C. Smith, editor,
Proceedings of the Twenty-Seventh ACM/IEEE Design Automation
Conference (DAC 1990), pages 40–45. IEEE Computer Society Press, 1990.

for propositional BDDs. Instead of a hash table, facts of the
(dynamic) predicate bdd_node/4 are used to store nodes. Prolog's
built-in term order is used for ordering nodes.

@author  Jens Claßen
@license GPL

 **/

:- module(bdd, [reduce/2]).

:- use_module('../lib/utils').
:- use_module('../reasoning/fol').

%:- use_module(library(graph_algorithms)).
%:- use_module(library(graphviz)).

:- dynamic bdd_node/4. % table entries
:- dynamic nodes/1.    % highest table index
:- dynamic cached_ite/4.
:- dynamic cached_implies/4.

nodes(1).

bdd_node('___undef','___undef','___undef',0).
bdd_node('___undef','___undef','___undef',1).

reduce(Fml1,Fml2) :- !,
        free_variables(Fml1,Vars),
        formula2bdd(Fml1,Vars,BDD),
        bdd2formula(Fml2,Vars,BDD).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Preprocessing
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

free_variables(Fml1*Fml2,Vars) :- !,
        free_variables(Fml1,Vars1),
        free_variables(Fml2,Vars2),
        union2(Vars1,Vars2,Vars).
free_variables(Fml1+Fml2,Vars) :- !,
        free_variables(Fml1,Vars1),
        free_variables(Fml2,Vars2),
        union2(Vars1,Vars2,Vars).
free_variables(-Fml,Vars) :- !,
        free_variables(Fml,Vars).
free_variables(Fml1<=>Fml2,Vars) :- !,
        free_variables(Fml1,Vars1),
        free_variables(Fml2,Vars2),
        union2(Vars1,Vars2,Vars).
free_variables(Fml1=>Fml2,Vars) :- !,
        free_variables(Fml1,Vars1),
        free_variables(Fml2,Vars2),
        union2(Vars1,Vars2,Vars).
free_variables(Fml1<=Fml2,Vars) :- !,
        free_variables(Fml1,Vars1),
        free_variables(Fml2,Vars2),
        union2(Vars1,Vars2,Vars).
free_variables(some(X,Fml),Vars) :-
        var(X), !,
        free_variables(some([X],Fml),Vars).
free_variables(all(X,Fml),Vars) :-
        var(X), !,
        free_variables(all([X],Fml),Vars).
free_variables(some(Vars2,Fml),Vars) :- !,
        free_variables(Fml,Vars3),
        setminus2(Vars3,Vars2,Vars).
free_variables(all(Vars2,Fml),Vars) :- !,
        free_variables(Fml,Vars3),
        setminus2(Vars3,Vars2,Vars).
free_variables(Fml,Vars) :- !,
        term_variables(Fml,Vars).

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
preprocess(some(Vars,Fml),R) :-
        handle_equality_conjuncts(Vars,Fml,Vars2,Fml2),
        some(Vars,Fml) \= some(Vars2,Fml2), !,
        preprocess(some(Vars2,Fml2),R).
% ![X]:~(X=T)|F --> F with X replaced by T
preprocess(all(Vars,Fml),R) :-
        handle_inequality_disjuncts(Vars,Fml,Vars2,Fml2),
        all(Vars,Fml) \= all(Vars2,Fml2), !,
        preprocess(all(Vars2,Fml2),R).

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

% distribute "exists" over disjunction
preprocess(some(Vars,Fml),R) :-
        disjuncts(Fml,Disj),
        distribute_exists_disjuncts(Vars,Disj,Fml2),
        Fml2 \= some(Vars,Fml), !,
        preprocess(Fml2,R).
% distribute "forall" over conjunction
preprocess(all(Vars,Fml),R) :-
        conjuncts(Fml,Conj),
        distribute_forall_conjuncts(Vars,Conj,Fml2),
        Fml2 \= all(Vars,Fml), !,
        preprocess(Fml2,R).

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

% combine quantifiers
preprocess(some(Vars1,some(Var,Fml)),R) :- 
        var(Var), !,
        append(Vars1,[Var],Vars),
        preprocess(some(Vars,Fml),R).
preprocess(some(Vars1,some(Vars2,Fml)),R) :- !,
        append(Vars1,Vars2,Vars),
        preprocess(some(Vars,Fml),R).
preprocess(all(Vars1,all(Var,Fml)),R) :- 
        var(Var), !,
        append(Vars1,[Var],Vars),
        preprocess(all(Vars,Fml),R).
preprocess(all(Vars1,all(Vars2,Fml)),R) :- !,
        append(Vars1,Vars2,Vars),
        preprocess(all(Vars,Fml),R).

% recursive preprocessing of subformulas
preprocess(some(Vars,Fml),R) :-
        preprocess(Fml,Fml2),
        Fml \= Fml2, !,
        preprocess(some(Vars,Fml2),R).
preprocess(all(Vars,Fml),R) :-
        preprocess(Fml,Fml2),
        Fml \= Fml2, !,
        preprocess(all(Vars,Fml2),R).

% apply simple FOL simplifications if possible
preprocess(F,R) :-
        simplify(F,F2),
        F \= F2, !,
        preprocess(F2,R).

% if none of the other cases works
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
preprocess(R,R) :- !.

disjuncts((F1+F2)*F3,F4+F5) :- !,
        disjuncts(F1*F3,F4),
        disjuncts(F2*F3,F5).
disjuncts(F1*(F2+F3),F4+F5) :- !,
        disjuncts(F1*F2,F4),
        disjuncts(F1*F3,F5).     
disjuncts(F1*F2,R) :- !,
        disjuncts(F1,F3),
        disjuncts(F2,F4),
        disjuncts2(F3,F4,R).
disjuncts(F1+F2,F3+F4) :- !,
        disjuncts(F1,F3),
        disjuncts(F2,F4).
disjuncts(F,F).

disjuncts2(F1+F2,F3,R) :- !,
        disjuncts((F1+F2)*F3,R).
disjuncts2(F1,F2+F3,R) :- !,
        disjuncts(F1*(F2+F3),R).
disjuncts2(F1,F2,F1*F2).

distribute_exists_disjuncts(Vars,Fml1+Fml2,R1+R2) :- !,
        distribute_exists_disjuncts(Vars,Fml1,R1),
        distribute_exists_disjuncts(Vars,Fml2,R2).
distribute_exists_disjuncts(Vars,Fml,some(Vars,Fml)).

conjuncts((F1*F2)+F3,F4*F5) :- !,        
        conjuncts(F1+F3,F4),
        conjuncts(F2+F3,F5).
conjuncts(F1+(F2*F3),F4*F5) :- !,
        conjuncts(F1+F2,F4),
        conjuncts(F1+F3,F5).     
conjuncts(F1+F2,R) :- !,
        conjuncts(F1,F3),
        conjuncts(F2,F4),
        conjuncts2(F3,F4,R).
conjuncts(F1*F2,F3*F4) :- !,
        conjuncts(F1,F3),
        conjuncts(F2,F4).
conjuncts(F,F).

conjuncts2(F1*F2,F3,R) :- !,
        conjuncts((F1*F2)+F3,R).
conjuncts2(F1,F2*F3,R) :- !,
        conjuncts(F1+(F2*F3),R).
conjuncts2(F1,F2,F1+F2).

distribute_forall_conjuncts(Vars,Fml1*Fml2,R1*R2) :- !,
        distribute_forall_conjuncts(Vars,Fml1,R1),
        distribute_forall_conjuncts(Vars,Fml2,R2).
distribute_forall_conjuncts(Vars,Fml,all(Vars,Fml)).

handle_equality_conjuncts([X|Vars],Fml,Vars2,Fml3) :-
        equality_conjunct(X,Y,Fml), !,
        subv(X,Y,Fml,Fml2),
        handle_equality_conjuncts(Vars,Fml2,Vars2,Fml3).
handle_equality_conjuncts([X|Vars],Fml,[X|Vars2],Fml2) :-
        handle_equality_conjuncts(Vars,Fml,Vars2,Fml2).
handle_equality_conjuncts([],Fml,[],Fml).

handle_inequality_disjuncts([X|Vars],Fml,Vars2,Fml3) :-
        inequality_disjunct(X,Y,Fml), !,
        subv(X,Y,Fml,Fml2),
        handle_inequality_disjuncts(Vars,Fml2,Vars2,Fml3).
handle_inequality_disjuncts([X|Vars],Fml,[X|Vars2],Fml2) :-
        handle_inequality_disjuncts(Vars,Fml,Vars2,Fml2).
handle_inequality_disjuncts([],Fml,[],Fml).

equality_conjunct(X,Y,(A=B)) :-
        not(A==B), % else no substitution necessary
        X==A,
        Y=B.
equality_conjunct(X,Y,(A=B)) :-
        not(A==B), % else no substitution necessary
        X==B,
        Y=A.
equality_conjunct(X,Y,Fml1*Fml2) :-
        equality_conjunct(X,Y,Fml1);
        equality_conjunct(X,Y,Fml2).

inequality_disjunct(X,Y,-(A=B)) :-
        not(A==B), % else no substitution necessary
        X==A,
        Y=B.
inequality_disjunct(X,Y,-(A=B)) :-
        not(A==B), % else no substitution necessary
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

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% BDD Construction
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

formula2bdd(Fml,Vars,BDD) :- !,
        preprocess(Fml,FmlP),
        construct_bdd(FmlP,Vars,BDD).

bdd2formula(false,_Vars,0) :- !.
bdd2formula(true,_Vars,1) :- !.
bdd2formula(Fml,Vars,BDD) :-
        bdd_node((Fml,Vars),1,0,BDD),!.
bdd2formula(-Fml,Vars,BDD) :-
        bdd_node((Fml,Vars),0,1,BDD),!.
bdd2formula(Fml,Vars,BDD) :-
        bdd_node((Fml2,Vars),1,E,BDD),!,
        bdd2formula(FmlE,Vars,E),
        simplify_deps(Fml2+FmlE,Vars,Fml).
bdd2formula(Fml,Vars,BDD) :-
        bdd_node((Fml2,Vars),0,E,BDD),!,
        bdd2formula(FmlE,Vars,E),
        simplify_deps((-Fml2)*FmlE,Vars,Fml).
bdd2formula(Fml,Vars,BDD) :-
        bdd_node((Fml2,Vars),T,1,BDD),!,
        bdd2formula(FmlT,Vars,T),
        simplify_deps(FmlT+(-Fml2),Vars,Fml).
bdd2formula(Fml,Vars,BDD) :-
        bdd_node((Fml2,Vars),T,0,BDD),!,
        bdd2formula(FmlT,Vars,T),
        simplify_deps(Fml2*FmlT,Vars,Fml).
bdd2formula(Fml,Vars,BDD) :-
        bdd_node((Fml3,Vars),Then,Else,BDD),
        bdd2formula(Fml1,Vars,Then),
        bdd2formula(Fml2,Vars,Else),!,
        simplify_deps((Fml3*Fml1)+((-Fml3)*Fml2),Vars,Fml).

construct_bdd(true,_Vars,1) :- !.
construct_bdd(false,_Vars,0) :- !.
construct_bdd(-true,_Vars,0) :- !.
construct_bdd(-false,_Vars,1) :- !.
construct_bdd((X=Y),_Vars,1) :- X==Y,!.
construct_bdd(-(X=Y),_Vars,0) :- X==Y, !.
construct_bdd(Fml,Vars,BDD) :-
        bdd_atom(Fml), !,
        get_label(Fml,Vars,Label),
        find_or_add_unique(Label,1,0,BDD).
construct_bdd(Fml1<=>Fml2,Vars,BDD) :- !,
        construct_bdd(Fml1,Vars,BDD1),
        construct_bdd(Fml2,Vars,BDD2),
        construct_bdd(-Fml2,Vars,BDD3),
        ite(BDD1,BDD2,BDD3,BDD).
construct_bdd(Fml1=>Fml2,Vars,BDD) :- !,
        construct_bdd(Fml1,Vars,BDD1),
        construct_bdd(Fml2,Vars,BDD2),
        ite(BDD1,BDD2,1,BDD).
construct_bdd(Fml1<=Fml2,Vars,BDD) :- !,
        construct_bdd(Fml1,Vars,BDD1),
        construct_bdd(-Fml2,Vars,BDD2),
        ite(BDD1,1,BDD2,BDD).
construct_bdd(-Fml1,Vars,BDD) :- !,
        construct_bdd(Fml1,Vars,BDD1),
        ite(BDD1,0,1,BDD).
construct_bdd(Fml1+Fml2,Vars,BDD) :- !,
        construct_bdd(Fml1,Vars,BDD1),
        construct_bdd(Fml2,Vars,BDD2),
        ite(BDD1,1,BDD2,BDD).
construct_bdd(Fml1*Fml2,Vars,BDD) :- !,
        construct_bdd(Fml1,Vars,BDD1),
        construct_bdd(Fml2,Vars,BDD2),
        ite(BDD1,BDD2,0,BDD).

find_or_add_unique(_Label,B,B,B) :- !.
find_or_add_unique(Label1,Then,Else,BDD) :-
        bdd_node(Label2,Then,Else,BDD),
        % need this to avoid unifying p(A) with p(f(A))
        % (by default no occur check)
        Label1 =@= Label2, !.
find_or_add_unique(Label,Then,Else,BDD) :- !,
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

least_label(L1,L2,L1) :-
        label_less_than(L1,L2), !.
least_label(L1,L2,L2) :-
        label_less_than(L2,L1), !.

label_less_than(_,'___undef') :- !.
label_less_than((all(_,F1),_),(all(_,F2),_)) :- !,
        F1 @=< F2.
label_less_than((some(_,F1),_),(some(_,F2),_)) :- !,
        F1 @=< F2.
label_less_than((all(_,_),_),(some(_,_),_)) :- !.
label_less_than((all(_,_),_),(_,_)) :- !.
label_less_than((some(_,_),_),(_,_)) :- !.
label_less_than((L1,_),(L2,_)) :-
        L1 \= all(_,_), 
        L1 \= some(_,_),
        L2 \= all(_,_),
        L2 \= some(_,_), !,
        L1 @=< L2.

branch(Node,Label,_Value,Result) :-
        bdd_node(Label2,_Then,_Else,Node),
        Label \=@= Label2,
        Result=Node.
branch(Node,Label,1,Result) :-
        bdd_node(Label2,Then,_Else,Node),
        Label =@= Label2,
        Result=Then.
branch(Node,Label,0,Result) :-
        bdd_node(Label2,_Then,Else,Node),
        Label =@= Label2,
        Result=Else.

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

get_label(some(Vars,Fml),AllVars,L) :- !,
        reduce(Fml,SFml),
        get_canonical_label(some(Vars,SFml),AllVars,L).
get_label(all(Vars,Fml),AllVars,L) :- !,
        reduce(Fml,SFml),
        get_canonical_label(all(Vars,SFml),AllVars,L).
get_label(Atom,AllVars,(Atom,AllVars)).

% idea/todo: look for smallest, equivalent label formula
%get_canonical_label(some(Vars,Fml),AllVars,L) :-
%        bdd_node((some(Vars2,Fml2),AllVars),_,_,_),
%        implies(some(Vars,Fml),some(Vars2,Fml2),AllVars),
%        implies(some(Vars2,Fml2),some(Vars,Fml),AllVars), !,
%        L = (some(Vars2,Fml2),AllVars).
%get_canonical_label(all(Vars,Fml),AllVars,L) :-
%        bdd_node((all(Vars2,Fml2),AllVars),_,_,_),
%        implies(all(Vars,Fml),all(Vars2,Fml2),AllVars),
%        implies(all(Vars2,Fml2),all(Vars,Fml),AllVars), !,
%        L = (all(Vars2,Fml2),AllVars).        
get_canonical_label(Fml,AllVars,(Fml,AllVars)) :- !.

% simplify formulas checking dependencies between subformulas
% (using FOL reasoning / theorem proving)
simplify_deps((Fml3*Fml1)+((-Fml3)*Fml2),Vars,Fml1) :-
        implies(Fml1,Fml2,Vars),
        implies(Fml2,Fml1,Vars), !.
simplify_deps(Fml1+Fml2,Vars,Fml2) :-
        implies(Fml1,Fml2,Vars), !.
simplify_deps(Fml1+Fml2,Vars,Fml1) :-
        implies(Fml2,Fml1,Vars), !.
simplify_deps(Fml1+Fml2,Vars,true) :-
        implies(-Fml1,Fml2,Vars), !.
simplify_deps(Fml1+Fml2,Vars,true) :-
        implies(-Fml2,Fml1,Vars), !.
simplify_deps(Fml1*Fml2,Vars,Fml1) :-
        implies(Fml1,Fml2,Vars), !.
simplify_deps(Fml1*Fml2,Vars,Fml2) :-
        implies(Fml2,Fml1,Vars), !.
simplify_deps(Fml1*Fml2,Vars,false) :-
        implies(Fml1,-Fml2,Vars), !.
simplify_deps(Fml1*Fml2,Vars,false) :-
        implies(Fml2,-Fml1,Vars), !.
simplify_deps(Fml,_Vars,Fml) :- !.

implies(Fml1,-(-Fml2),Vars) :- !,
        implies(Fml1,Fml2,Vars).
implies(Fml1,Fml2,Vars) :-
        cached_implies(Fml1,Fml2,Vars,true), !.
implies(Fml1,Fml2,Vars) :-
        cached_implies(Fml1,Fml2,Vars,false), !, fail.
implies(Fml1,Fml2,Vars) :-
        % as one formula b/c of free variables
        % => use (automatic) universal closure
        valid(all(Vars,Fml1=>Fml2)), !,
        assert(cached_implies(Fml1,Fml2,Vars,true)).
implies(Fml1,Fml2,Vars) :- !,
        assert(cached_implies(Fml1,Fml2,Vars,false)),
        fail.


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

% output all BDD nodes
print_bdd_nodes :-
        nodes(N),
        print_bdd_nodes(N).

print_bdd_nodes(N) :-
        N > -1, !,
        bdd_node(L,T,E,N),
        write(N),
        write(': '), write(L),
        write(' T->'), write(T),
        write(' F->'), write(E),
        write('\n'),
        N1 is N-1,
        print_bdd_nodes(N1).
print_bdd_nodes(_).

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

