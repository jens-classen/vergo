/**
 
<module> FOBDD representation module

This module implements a representation and simplification mechanism for
formulas of first-order logic based on (ordered) binary decision
diagrams (BDD) as described in

Jens Claßen: Symbolic Verification of Golog Programs with First-Order
BDDs. In Proceedings of Sixteenth International Conference on
Principles of Knowledge Representation and Reasoning (KR 2018), pages
524-528, AAAI Press, 2018.

First-order formulas are preprocessed into an equivalent form where
quantifiers have small scopes, and subsequently 'propositionalized' by
regarding remaining quantified subformulas as propositional atoms. The
result is then represented by a classical, propostional BDD (using the
'bdd' module).

The idea is based on the first-order algebraic diagrams proposed in

Scott Sanner and Craig Boutilier: Practical Solution Techniques for
First-Order MDPs. Artificial Intelligence 173(5–6), pages 748–788,
Elsevier 2009.

in particular regarding the preprocessing (preprocess/3) of first-
order formulas, with the difference that Sanner and Boutilier suggest
to apply preprocessing rules 'working from the innermost to the
outermost quantifiers', while we found that the opposite worked better
for our setting.

For the purpose of making verification feasible, further techniques
for the simplification of formulas are included here, namely a
conversion into prime implicate representation
(clausalform:fml2prime_implicates/2) and theorem proving to eliminate
clauses whose de-propositionalized versions are entailed
(simplify_deps_clauses/3).

@author  Jens Claßen
@license GPLv2

 **/

:- module(fobdd, [minimize/2]).

:- use_module('../lib/utils').
:- use_module('../logic/una').
:- use_module('../logic/fol').
:- use_module('../logic/bdd').
:- use_module('../logic/clausalform').

:- dynamic mapping/3.
:- dynamic mappings/1.
:- dynamic cached_implies/4.

mappings(0).

minimize(Fml1,Fml2) :- !,
        minimize(Fml1,Fml2,cnf).

minimize(Fml1,Fml2,ite) :- !,
        free_variables(Fml1,Vars),
        preprocess(Fml1,Vars,Fml3),
        propositionalize(Fml3,Vars,Fml4),
        bdd:minimize2ite(Fml4,Fml5),
        depropositionalize(Fml5,Vars,Fml6),
        simplify_deps(Fml6,Vars,Fml2).

minimize(Fml1,Fml2,dnf) :- !,
        free_variables(Fml1,Vars),
        preprocess(Fml1,Vars,Fml3),
        propositionalize(Fml3,Vars,Fml4),
        bdd:minimize2dnf(Fml4,Fml5),
        depropositionalize(Fml5,Vars,Fml6),
        simplify_deps(Fml6,Vars,Fml2).

minimize(Fml1,Fml2,cnf) :- !,
        free_variables(Fml1,Vars),
        preprocess(Fml1,Vars,Fml3),
        propositionalize(Fml3,Vars,Fml4),
        bdd:minimize2cnf(Fml4,Fml5),
        clausalform:fml2prime_implicates(Fml5,PIs),
        simplify_deps_clauses(PIs,Vars,SPIs),
        clausalform:clauses2cnf(SPIs,Fml6),
        depropositionalize(Fml6,Vars,Fml7),
        simplify_deps(Fml7,Vars,Fml2).

% todo: make application of prime implicates optional
% todo: make choice between (ite|dnf|cnf) optional
% todo: make application of simplify_dep optional

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Preprocessing
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% always use variable *lists* in quantifiers
preprocess(some(X,Fml),Vars,R) :-
        var(X), !,
        preprocess(some([X],Fml),Vars,R).
preprocess(all(X,Fml),Vars,R) :-
        var(X), !,
        preprocess(all([X],Fml),Vars,R).

% drop empty quantifiers
preprocess(some([],Fml),Vars,R) :- !,
        preprocess(Fml,Vars,R).
preprocess(all([],Fml),Vars,R) :- !,
        preprocess(Fml,Vars,R).

% drop quantifiers for non-appearing variables
preprocess(some(Vars1,Fml),Vars,R) :-
        term_variables(Fml,Vars2),
        intersection2(Vars1,Vars2,Vars3),
        Vars1 \= Vars3, !,
        preprocess(some(Vars3,Fml),Vars,R).
preprocess(all(Vars1,Fml),Vars,R) :-
        term_variables(Fml,Vars2),
        intersection2(Vars1,Vars2,Vars3),
        Vars1 \= Vars3, !,
        preprocess(all(Vars3,Fml),Vars,R).

% combine quantifiers
preprocess(some(Vars1,some(Var,Fml)),Vars,R) :- 
        var(Var), !,
        append(Vars1,[Var],Vars2),
        preprocess(some(Vars2,Fml),Vars,R).
preprocess(some(Vars1,some(Vars2,Fml)),Vars,R) :- !,
        append(Vars1,Vars2,Vars3),
        preprocess(some(Vars3,Fml),Vars,R).
preprocess(all(Vars1,all(Var,Fml)),Vars,R) :- 
        var(Var), !,
        append(Vars1,[Var],Vars2),
        preprocess(all(Vars2,Fml),Vars,R).
preprocess(all(Vars1,all(Vars2,Fml)),Vars,R) :- !,
        append(Vars1,Vars2,Vars3),
        preprocess(all(Vars3,Fml),Vars,R).

% ?[X]:(X=T)&F --> F with X replaced by T
preprocess(some(Vars1,Fml),Vars,R) :-
        handle_equality_conjuncts(Vars1,Fml,Vars2,Fml2),
        some(Vars1,Fml) \= some(Vars2,Fml2), !,
        preprocess(some(Vars2,Fml2),Vars,R).
% ![X]:~(X=T)|F --> F with X replaced by T
preprocess(all(Vars1,Fml),Vars,R) :-
        handle_inequality_disjuncts(Vars1,Fml,Vars2,Fml2),
        all(Vars1,Fml) \= all(Vars2,Fml2), !,
        preprocess(all(Vars2,Fml2),Vars,R).

% distribute "exists" over disjunction
preprocess(some(Vars1,Fml),Vars,R) :-
        append(Vars,Vars1,Vars2),
        disjuncts(Fml,Vars2,Disj),
        distribute_exists_disjuncts(Vars1,Disj,Fml2),
        Fml2 \= some(Vars1,Fml), !,
        preprocess(Fml2,Vars,R).
% distribute "forall" over conjunction
preprocess(all(Vars1,Fml),Vars,R) :-
        append(Vars,Vars1,Vars2),
        conjuncts(Fml,Vars2,Conj),
        distribute_forall_conjuncts(Vars1,Conj,Fml2),
        Fml2 \= all(Vars1,Fml), !,
        preprocess(Fml2,Vars,R).

% reduce scope of existential to conjuncts where that variable appears
preprocess(some(Vars1,Fml),Vars,R) :-
        conjuncts_with_without(Vars1,Fml,ConW,ConWO),
        ConWO \= true, !,
        preprocess(some(Vars1,ConW)*ConWO,Vars,R).
% reduce scope of universal to disjuncts where that variable appears
preprocess(all(Vars1,Fml),Vars,R) :-
        disjuncts_with_without(Vars1,Fml,DisW,DisWO),
        DisWO \= false, !,
        preprocess(all(Vars1,DisW)+DisWO,Vars,R).

% apply simple FOL simplifications if possible
preprocess(F,Vars,R) :-
        simplify(F,F2),
        F \= F2, !,
        preprocess(F2,Vars,R).

% apply unique names assumption where possible
preprocess(F,Vars,R) :-
        apply_una(F,F2),
        F \= F2, !,
        preprocess(F2,Vars,R).

% if none of the other cases works
preprocess(Fml1<=>Fml2,Vars,R) :- !,
        preprocess((Fml1=>Fml2)*(Fml2=>Fml1),Vars,R).
preprocess(Fml1=>Fml2,Vars,R) :- !,
        preprocess((-Fml1)+Fml2,Vars,R).
preprocess(Fml1<=Fml2,Vars,R) :- !,
        preprocess(Fml1+(-Fml2),Vars,R).
preprocess(-Fml,Vars,R) :-
        push_negation_inside(-Fml,Fml2),
        -Fml \= Fml2, !,
        preprocess(Fml2,Vars,R).
preprocess(Fml1+Fml2,Vars,R1+R2) :- !,
        preprocess(Fml1,Vars,R1),
        preprocess(Fml2,Vars,R2).
preprocess(Fml1*Fml2,Vars,R1*R2) :- !,
        preprocess(Fml1,Vars,R1),
        preprocess(Fml2,Vars,R2).

% if none of the other cases worked: reduce quantified subformula
preprocess(some(Vars1,Fml),Vars,some(Vars1,R)) :- !,
        append(Vars,Vars1,Vars2),
        preprocess(Fml,Vars2,R1),
        minimize(R1,R).
preprocess(all(Vars1,Fml),Vars,all(Vars1,R)) :- !,
        append(Vars,Vars1,Vars2),
        preprocess(Fml,Vars2,R1),
        minimize(R1,R).

% else do nothing
preprocess(R,_Vars,R) :- !.

disjuncts((F1+F2)*F3,Vars,F4+F5) :- !,
        copy_term((F3,Vars),(F6,Vars)),
        disjuncts(F1*F3,Vars,F4),
        disjuncts(F2*F6,Vars,F5).
disjuncts(F1*(F2+F3),Vars,F4+F5) :- !,
        copy_term((F1,Vars),(F6,Vars)),
        disjuncts(F1*F2,Vars,F4),
        disjuncts(F6*F3,Vars,F5).     
disjuncts(F1*F2,Vars,R) :- !,
        disjuncts(F1,Vars,F3),
        disjuncts(F2,Vars,F4),
        disjuncts2(F3,F4,Vars,R).
disjuncts(F1+F2,Vars,F3+F4) :- !,
        disjuncts(F1,Vars,F3),
        disjuncts(F2,Vars,F4).
disjuncts(F,_Vars,F) :- !.

disjuncts2(F1+F2,F3,Vars,R) :- !,
        disjuncts((F1+F2)*F3,Vars,R).
disjuncts2(F1,F2+F3,Vars,R) :- !,
        disjuncts(F1*(F2+F3),Vars,R).
disjuncts2(F1,F2,_Vars,F1*F2) :- !.

distribute_exists_disjuncts(Vars,Fml1+Fml2,R1+R2) :- !,
        copy_term(Vars,VarsN),
        sub_vars(Vars,VarsN,Fml2,Fml2N),
        distribute_exists_disjuncts(Vars,Fml1,R1),
        distribute_exists_disjuncts(VarsN,Fml2N,R2).
distribute_exists_disjuncts(Vars,Fml,some(Vars,Fml)) :- !.

conjuncts((F1*F2)+F3,Vars,F4*F5) :- !,        
        copy_term((F3,Vars),(F6,Vars)),
        conjuncts(F1+F3,Vars,F4),
        conjuncts(F2+F6,Vars,F5).
conjuncts(F1+(F2*F3),Vars,F4*F5) :- !,
        copy_term((F1,Vars),(F6,Vars)),
        conjuncts(F1+F2,Vars,F4),
        conjuncts(F6+F3,Vars,F5).     
conjuncts(F1+F2,Vars,R) :- !,
        conjuncts(F1,Vars,F3),
        conjuncts(F2,Vars,F4),
        conjuncts2(F3,F4,Vars,R).
conjuncts(F1*F2,Vars,F3*F4) :- !,
        conjuncts(F1,Vars,F3),
        conjuncts(F2,Vars,F4).
conjuncts(F,_Vars,F) :- !.

conjuncts2(F1*F2,F3,Vars,R) :- !,
        conjuncts((F1*F2)+F3,Vars,R).
conjuncts2(F1,F2*F3,Vars,R) :- !,
        conjuncts(F1+(F2*F3),Vars,R).
conjuncts2(F1,F2,_Vars,F1+F2) :- !.

distribute_forall_conjuncts(Vars,Fml1*Fml2,R1*R2) :- !,
        copy_term(Vars,VarsN),
        sub_vars(Vars,VarsN,Fml2,Fml2N),
        distribute_forall_conjuncts(Vars,Fml1,R1),
        distribute_forall_conjuncts(VarsN,Fml2N,R2).
distribute_forall_conjuncts(Vars,Fml,all(Vars,Fml)) :- !.

sub_vars([Var|Vars],[NVar|NVars],Fml,NFml) :- !,
        sub_vars(Vars,NVars,Fml,Fml2),
        subv(Var,NVar,Fml2,NFml).
sub_vars([],[],Fml,Fml) :- !.

handle_equality_conjuncts([X|Vars],Fml,Vars2,Fml3) :-
        equality_conjunct(X,Y,Fml), !,
        subv(X,Y,Fml,Fml2),
        handle_equality_conjuncts(Vars,Fml2,Vars2,Fml3).
handle_equality_conjuncts([X|Vars],Fml,[X|Vars2],Fml2) :- !,
        handle_equality_conjuncts(Vars,Fml,Vars2,Fml2).
handle_equality_conjuncts([],Fml,[],Fml) :- !.

handle_inequality_disjuncts([X|Vars],Fml,Vars2,Fml3) :-
        inequality_disjunct(X,Y,Fml), !,
        subv(X,Y,Fml,Fml2),
        handle_inequality_disjuncts(Vars,Fml2,Vars2,Fml3).
handle_inequality_disjuncts([X|Vars],Fml,[X|Vars2],Fml2) :- !,
        handle_inequality_disjuncts(Vars,Fml,Vars2,Fml2).
handle_inequality_disjuncts([],Fml,[],Fml) :- !.

equality_conjunct(X,Y,(A=B)) :-
        not(A==B), % else no substitution necessary
        X==A,
        Y=B, !.
equality_conjunct(X,Y,(A=B)) :-
        not(A==B), % else no substitution necessary
        X==B,
        Y=A, !.
equality_conjunct(X,Y,Fml1*Fml2) :-
        equality_conjunct(X,Y,Fml1);
        equality_conjunct(X,Y,Fml2).

inequality_disjunct(X,Y,-(A=B)) :-
        not(A==B), % else no substitution necessary
        X==A,
        Y=B, !.
inequality_disjunct(X,Y,-(A=B)) :-
        not(A==B), % else no substitution necessary
        X==B,
        Y=A, !.
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
        disjoint2(Vars,FVars), !.

remove_true(Fml*true,Fml) :- !.
remove_true(true*Fml,Fml) :- !.
remove_true(Fml,Fml) :- !.

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
        disjoint2(Vars,FVars), !.

remove_false(Fml+false,Fml) :- !.
remove_false(false+Fml,Fml) :- !.
remove_false(Fml,Fml) :- !.

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
push_negation_inside(Fml,Fml) :- !.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Propositionalization
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

propositionalize(true,_Vars,true) :- !.
propositionalize(false,_Vars,false) :- !.
propositionalize(Fml1*Fml2,Vars,Fml3*Fml4) :- !,
        propositionalize(Fml1,Vars,Fml3),
        propositionalize(Fml2,Vars,Fml4).
propositionalize(Fml1+Fml2,Vars,Fml3+Fml4) :- !,
        propositionalize(Fml1,Vars,Fml3),
        propositionalize(Fml2,Vars,Fml4).
propositionalize(-Fml1,Vars,-Fml2) :- !,
        propositionalize(Fml1,Vars,Fml2).
propositionalize(Fml1<=>Fml2,Vars,Fml3<=>Fml4) :- !,
        propositionalize(Fml1,Vars,Fml3),
        propositionalize(Fml2,Vars,Fml4).
propositionalize(Fml1=>Fml2,Vars,Fml3=>Fml4) :- !,
        propositionalize(Fml1,Vars,Fml3),
        propositionalize(Fml2,Vars,Fml4).
propositionalize(Fml1<=Fml2,Vars,Fml3<=Fml4) :- !,
        propositionalize(Fml1,Vars,Fml3),
        propositionalize(Fml2,Vars,Fml4).
propositionalize(some(Vars2,Fml),Vars,Atom) :- !,
        get_mapping(some(Vars2,Fml),Vars,Atom).
propositionalize(all(Vars2,Fml),Vars,Atom) :- !,
        get_mapping(all(Vars2,Fml),Vars,Atom).
propositionalize(Fml,Vars,Atom) :- !,
        get_mapping(Fml,Vars,Atom).

get_mapping(QFml,Vars,Atom) :-
        mapping(QFml2,Vars2,Atom), 
        (QFml,Vars) =@= (QFml2,Vars2), !.
get_mapping(QFml,Vars,Atom) :-
        mapping(QFml2,Vars2,Atom), 
        (QFml,Vars) =@= (QFml2,Vars2), !,
        implies(QFml,QFml2,Vars),
        implies(QFml2,QFml,Vars), !.
get_mapping(QFml,Vars,Atom) :- !,
        retract(mappings(N)),
        N1 is N+1,
        assert(mappings(N1)),
        atom_concat('x',N,Atom),
        assert(mapping(QFml,Vars,Atom)).

depropositionalize(true,_Vars,true) :- !.
depropositionalize(false,_Vars,false) :- !.
depropositionalize(Fml1*Fml2,Vars,Fml3*Fml4) :- !,
        depropositionalize(Fml1,Vars,Fml3),
        depropositionalize(Fml2,Vars,Fml4).
depropositionalize(Fml1+Fml2,Vars,Fml3+Fml4) :- !,
        depropositionalize(Fml1,Vars,Fml3),
        depropositionalize(Fml2,Vars,Fml4).
depropositionalize(-Fml1,Vars,-Fml2) :- !,
        depropositionalize(Fml1,Vars,Fml2).
depropositionalize(Fml1<=>Fml2,Vars,Fml3<=>Fml4) :- !,
        depropositionalize(Fml1,Vars,Fml3),
        depropositionalize(Fml2,Vars,Fml4).
depropositionalize(Fml1=>Fml2,Vars,Fml3=>Fml4) :- !,
        depropositionalize(Fml1,Vars,Fml3),
        depropositionalize(Fml2,Vars,Fml4).
depropositionalize(Fml1<=Fml2,Vars,Fml3<=Fml4) :- !,
        depropositionalize(Fml1,Vars,Fml3),
        depropositionalize(Fml2,Vars,Fml4).
depropositionalize(Atom,Vars,Fml) :- !,
        mapping(Fml,Vars,Atom).

% simplify formulas checking dependencies between subformulas
% (using FOL reasoning / theorem proving)
simplify_deps((Fml3*Fml1)+((-Fml3)*Fml2),Vars,Fml) :-
        implies(Fml1,Fml2,Vars),
        implies(Fml2,Fml1,Vars), !,
        simplify_deps(Fml1,Vars,Fml).
simplify_deps(Fml1+Fml2,Vars,Fml) :-
        implies(Fml1,Fml2,Vars), !,
        simplify_deps(Fml2,Vars,Fml).
simplify_deps(Fml1+Fml2,Vars,Fml) :-
        implies(Fml2,Fml1,Vars), !,
        simplify_deps(Fml1,Vars,Fml).
simplify_deps(Fml1+Fml2,Vars,true) :-
        implies(-Fml1,Fml2,Vars), !.
simplify_deps(Fml1+Fml2,Vars,true) :-
        implies(-Fml2,Fml1,Vars), !.
simplify_deps(Fml1*Fml2,Vars,Fml) :-
        implies(Fml1,Fml2,Vars), !,
        simplify_deps(Fml1,Vars,Fml).
simplify_deps(Fml1*Fml2,Vars,Fml) :-
        implies(Fml2,Fml1,Vars), !,
        simplify_deps(Fml2,Vars,Fml).
simplify_deps(Fml1*Fml2,Vars,false) :-
        implies(Fml1,-Fml2,Vars), !.
simplify_deps(Fml1*Fml2,Vars,false) :-
        implies(Fml2,-Fml1,Vars), !.
simplify_deps(Fml1*(Fml2+Fml3),Vars,Fml) :-
        implies(Fml1*Fml2,Fml1*Fml3,Vars), !,
        simplify_deps(Fml1*Fml3,Vars,Fml).
simplify_deps(Fml1*(Fml2+Fml3),Vars,Fml) :-
        implies(Fml1*Fml3,Fml1*Fml2,Vars), !,
        simplify_deps(Fml1*Fml2,Vars,Fml).
simplify_deps((Fml1+Fml2)*Fml3,Vars,Fml) :-
        implies(Fml1*Fml3,Fml2*Fml3,Vars), !,
        simplify_deps(Fml2*Fml3,Vars,Fml).
simplify_deps((Fml1+Fml2)*Fml3,Vars,Fml) :-
        implies(Fml2*Fml3,Fml1*Fml3,Vars), !,
        simplify_deps(Fml1*Fml3,Vars,Fml).
simplify_deps(Fml1*(Fml2+Fml3),Vars,Fml) :-
        implies(Fml3,-Fml1,Vars), !,
        simplify_deps(Fml1*Fml2,Vars,Fml).
simplify_deps(Fml1*(Fml2+Fml3),Vars,Fml) :-
        implies(Fml2,-Fml1,Vars), !,
        simplify_deps(Fml1*Fml3,Vars,Fml).
simplify_deps(Fml1*(Fml2+Fml3),Vars,Fml) :-
        implies(Fml1,-Fml3,Vars), !,
        simplify_deps(Fml1*Fml2,Vars,Fml).
simplify_deps(Fml1*(Fml2+Fml3),Vars,Fml) :-
        implies(Fml1,-Fml2,Vars), !,
        simplify_deps(Fml1*Fml3,Vars,Fml).
simplify_deps((Fml2+Fml3)*Fml1,Vars,Fml) :-
        implies(Fml3,-Fml1,Vars), !,
        simplify_deps(Fml1*Fml2,Vars,Fml).
simplify_deps((Fml2+Fml3)*Fml1,Vars,Fml) :-
        implies(Fml2,-Fml1,Vars), !,
        simplify_deps(Fml1*Fml3,Vars,Fml).
simplify_deps((Fml2+Fml3)*Fml1,Vars,Fml) :-
        implies(Fml1,-Fml3,Vars), !,
        simplify_deps(Fml1*Fml2,Vars,Fml).
simplify_deps((Fml2+Fml3)*Fml1,Vars,Fml) :-
        implies(Fml1,-Fml2,Vars), !,
        simplify_deps(Fml1*Fml3,Vars,Fml).
simplify_deps(Fml1*(Fml2+_Fml3),Vars,Fml) :-
        implies(Fml1,Fml2,Vars), !,
        simplify_deps(Fml1,Vars,Fml).
simplify_deps(Fml1*(_Fml2+Fml3),Vars,Fml) :-
        implies(Fml1,Fml3,Vars), !,
        simplify_deps(Fml1,Vars,Fml).
simplify_deps((Fml2+_Fml3)*Fml1,Vars,Fml) :-
        implies(Fml1,Fml2,Vars), !,
        simplify_deps(Fml1,Vars,Fml).
simplify_deps((_Fml2+Fml3)*Fml1,Vars,Fml) :-
        implies(Fml1,Fml3,Vars), !,
        simplify_deps(Fml1,Vars,Fml).
simplify_deps(Fml1*(Fml2*Fml3),Vars,Fml) :-
        implies(Fml1,Fml2,Vars), !,
        simplify_deps(Fml1*Fml3,Vars,Fml).
simplify_deps(Fml1*(Fml2*Fml3),Vars,Fml) :-
        implies(Fml1,Fml3,Vars), !,
        simplify_deps(Fml1*Fml2,Vars,Fml).
simplify_deps((Fml2*Fml3)*Fml1,Vars,Fml) :-
        implies(Fml1,Fml2,Vars), !,
        simplify_deps(Fml1*Fml3,Vars,Fml).
simplify_deps((Fml2*Fml3)*Fml1,Vars,Fml) :-
        implies(Fml1,Fml2,Vars), !,
        simplify_deps(Fml1*Fml3,Vars,Fml).
simplify_deps(Fml1*Fml2,Vars,Fml3*Fml4) :- !,
        simplify_deps(Fml1,Vars,Fml3),
        simplify_deps(Fml2,Vars,Fml4).
simplify_deps(Fml1+Fml2,Vars,Fml3+Fml4) :- !,
        simplify_deps(Fml1,Vars,Fml3),
        simplify_deps(Fml2,Vars,Fml4).
simplify_deps(Fml,_Vars,Fml) :- !.

simplify_deps_clauses(Clauses,Vars,Clauses2) :- !,
        simplify_deps_clauses2(Clauses,Vars,Clauses3),
        %simplify_deps_clauses3(Clauses4,Vars,Clauses2).
        simplify_deps_clauses4(Clauses3,Vars,Clauses2).

% simplify within each clause
simplify_deps_clauses2([Clause|Clauses],Vars,[Clause2|Clauses2]) :- !,
        simplify_deps_clause(Clause,Vars,Clause2),
        simplify_deps_clauses2(Clauses,Vars,Clauses2).
simplify_deps_clauses2([],_Vars,[]) :- !.

% if L1 (depropositionalized) implies L2 (depropositionalized), remove L1
simplify_deps_clause(Clause,Vars,Clause2) :-
        member(L1,Clause),
        member(L2,Clause),
        L1 \= L2,
        depropositionalize(L1,Vars,Fml1),
        depropositionalize(L2,Vars,Fml2),
        implies(Fml1,Fml2,Vars), !,
        setminus2(Clause,[L1],Clause3),
        simplify_deps_clause(Clause3,Vars,Clause2).
simplify_deps_clause(Clause,_Vars,Clause) :- !.

% if unit clause [L1] (depropositionalized) implies a literal L2
% (depropositionalized) in another clause C2, remove C2
% (this rule is a special case of simplify_deps_clauses4/3)
simplify_deps_clauses3(Clauses,Vars,Clauses2) :-
        member([L1],Clauses),
        member(C2,Clauses),
        [L1] \= C2,
        member(L2,C2),
        depropositionalize(L1,Vars,Fml1),
        depropositionalize(L2,Vars,Fml2),
        implies(Fml1,Fml2,Vars), !,
        setminus2(Clauses,[C2],Clauses3),
        simplify_deps_clauses3(Clauses3,Vars,Clauses2).
simplify_deps_clauses3(Clauses,_Vars,Clauses).

% if a clause C1 (depropositionalized) implies another clause C2
% (depropositionalized), remove C2
simplify_deps_clauses4(Clauses,Vars,Clauses2) :-
        member(C1,Clauses),
        member(C2,Clauses),
        C1 \= C2,
        clauses2cnf([C1],P1),
        clauses2cnf([C2],P2),
        depropositionalize(P1,Vars,Fml1),
        depropositionalize(P2,Vars,Fml2),
        implies(Fml1,Fml2,Vars), !,
        setminus2(Clauses,[C2],Clauses3),
        simplify_deps_clauses4(Clauses3,Vars,Clauses2).
simplify_deps_clauses4(Clauses,_Vars,Clauses).

implies(Fml1,-(-Fml2),Vars) :- !,
        implies(Fml1,Fml2,Vars).
implies(Fml1,Fml2,Vars) :-
        cached_implies(Fml3,Fml4,Vars2,true), 
        (Fml1,Fml2,Vars) =@= (Fml3,Fml4,Vars2), !.
implies(Fml1,Fml2,Vars) :-
        cached_implies(Fml3,Fml4,Vars2,false), 
        (Fml1,Fml2,Vars) =@= (Fml3,Fml4,Vars2), !, 
        fail.
implies(Fml1,Fml2,[]) :-
        entails([Fml1],Fml2), !,
        assert(cached_implies(Fml1,Fml2,[],true)).
implies(Fml1,Fml2,Vars) :-
        % as one formula b/c of free variables
        % => use (automatic) universal closure
        Vars \= [],
        valid(all(Vars,Fml1=>Fml2)), !,
        assert(cached_implies(Fml1,Fml2,Vars,true)).
implies(Fml1,Fml2,Vars) :- !,
        assert(cached_implies(Fml1,Fml2,Vars,false)),
        fail.
