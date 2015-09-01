/**
 
<module> FOBDD representation module

This module implements a representation and simplification mechanism for
formulas of first-order logic based on (ordered) binary decision
diagrams (BDD). The idea was sketched in

Jens Claßen: Planning and Verification in the Agent Language Golog.
PhD Thesis, Department of Computer Science, RWTH Aachen University,
2013.

 **/

:- module(fobdd, [reduce/2]).

:- use_module('../reasoning/fol').
:- use_module('../reasoning/bdd').
:- use_module('../reasoning/clausalform').

:- dynamic mapping/3.
:- dynamic mappings/1.
:- dynamic cached_implies/4.

:- discontiguous preprocess/2.

mappings(0).

reduce(Fml1,Fml2) :- !,
        reduce(Fml1,Fml2,cnf).

reduce(Fml1,Fml2,ite) :- !,
        simplify(Fml1,Fml3),
        preprocess(Fml3,Fml4),
        free_variables(Fml4,Vars),
        propositionalize(Fml4,Vars,Fml5),
        bdd:reduce2ite(Fml5,Fml6),
        depropositionalize(Fml6,Vars,Fml7),
        simplify_deps(Fml7,Vars,Fml2).

reduce(Fml1,Fml2,dnf) :- !,
        simplify(Fml1,Fml3),
        preprocess(Fml3,Fml4),
        free_variables(Fml4,Vars),
        propositionalize(Fml4,Vars,Fml5),
        bdd:reduce2dnf(Fml5,Fml6),
        depropositionalize(Fml6,Vars,Fml7),
        simplify_deps(Fml7,Vars,Fml2).

reduce(Fml1,Fml2,cnf) :- !,
        simplify(Fml1,Fml3),
        preprocess(Fml3,Fml4),
        free_variables(Fml4,Vars),
        propositionalize(Fml4,Vars,Fml5),
        bdd:reduce2cnf(Fml5,Fml6),
        clausalform:fml2prime_implicates(Fml6,PIs),
        simplify_deps_clauses(PIs,Vars,SPIs),
        clausalform:clauses2cnf(SPIs,Fml7),
        depropositionalize(Fml7,Vars,Fml8),
        simplify_deps(Fml8,Vars,Fml2).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Preprocessing
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% always use variable *lists* in quantifiers
preprocess(some(X,Fml),R) :-
        var(X), !,
        preprocess(some([X],Fml),R).
preprocess(all(X,Fml),R) :-
        var(X), !,
        preprocess(all([X],Fml),R).

% drop empty quantifiers
preprocess(some([],Fml),R) :- !,
        preprocess(Fml,R).
preprocess(all([],Fml),R) :- !,
        preprocess(Fml,R).

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

% ?[X]:(X=T)&F --> F with X replaced by T
preprocess(some(Vars,Fml),R) :-
        handle_equality_conjuncts(Vars,Fml,Vars2,Fml2),
        some(Vars,Fml) \= some(Vars2,Fml2), !,
        simplify(some(Vars2,Fml2),Fml3),
        preprocess(Fml3,R).
% ![X]:~(X=T)|F --> F with X replaced by T
preprocess(all(Vars,Fml),R) :-
        handle_inequality_disjuncts(Vars,Fml,Vars2,Fml2),
        all(Vars,Fml) \= all(Vars2,Fml2), !,
        simplify(all(Vars2,Fml2),Fml3),
        preprocess(Fml3,R).

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

% recursive preprocessing of subformulas
preprocess(some(Vars,Fml),R) :- !,
        preprocess(Fml,Fml2),
        preprocess_r(some,Vars,Fml,Fml2,R).
preprocess(all(Vars,Fml),R) :- !,
        preprocess(Fml,Fml2),
        preprocess_r(all,Vars,Fml,Fml2,R).

preprocess_r(some,Vars,Fml,Fml2,R) :-
        Fml \= Fml2, !,
        preprocess(some(Vars,Fml2),R).
preprocess_r(some,Vars,Fml,_Fml2,some(Vars,R1)) :- !,
        reduce(Fml,R1).
preprocess_r(all,Vars,Fml,Fml2,R) :-
        Fml \= Fml2, !,
        preprocess(all(Vars,Fml2),R).
preprocess_r(all,Vars,Fml,_Fml2,all(Vars,R1)) :- !,
        reduce(Fml,R1).

% handle boolean connectives
preprocess(Fml1<=>Fml2,R) :- !,
        preprocess((Fml1=>Fml2)*(Fml2=>Fml1),R).
preprocess(Fml1=>Fml2,R) :- !,
        preprocess((-Fml1)+Fml2,R).
preprocess(Fml1<=Fml2,R) :- !,
        preprocess(Fml1+(-Fml2),R).
preprocess(-Fml,R) :-
        push_negation_inside(-Fml,Fml2),
        -Fml \= Fml2, !,
        preprocess(Fml2,R).
preprocess(Fml1+Fml2,R1+R2) :- !,
        preprocess(Fml1,R1),
        preprocess(Fml2,R2).
preprocess(Fml1*Fml2,R1*R2) :- !,
        preprocess(Fml1,R1),
        preprocess(Fml2,R2).
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
disjuncts(F,F) :- !.

disjuncts2(F1+F2,F3,R) :- !,
        disjuncts((F1+F2)*F3,R).
disjuncts2(F1,F2+F3,R) :- !,
        disjuncts(F1*(F2+F3),R).
disjuncts2(F1,F2,F1*F2) :- !.

distribute_exists_disjuncts(Vars,Fml1+Fml2,R1+R2) :- !,
        copy_term(Vars,VarsN),
        sub_vars(Vars,VarsN,Fml2,Fml2N),
        distribute_exists_disjuncts(Vars,Fml1,R1),
        distribute_exists_disjuncts(VarsN,Fml2N,R2).
distribute_exists_disjuncts(Vars,Fml,some(Vars,Fml)) :- !.

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
conjuncts(F,F) :- !.

conjuncts2(F1*F2,F3,R) :- !,
        conjuncts((F1*F2)+F3,R).
conjuncts2(F1,F2*F3,R) :- !,
        conjuncts(F1+(F2*F3),R).
conjuncts2(F1,F2,F1+F2) :- !.

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
equality_conjunct(X,Y,Fml1*Fml2) :- !,
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
inequality_disjunct(X,Y,Fml1+Fml2) :- !,
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
%get_mapping(QFml,Vars,Atom) :-
%        mapping(QFml2,Vars,Atom),
%        implies(QFml,QFml2,Vars),
%        implies(QFml2,QFml,Vars), !.
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
simplify_deps(Fml1*Fml2,Vars,Fml3*Fml4) :- !,
        simplify_deps(Fml1,Vars,Fml3),
        simplify_deps(Fml2,Vars,Fml4).
simplify_deps(Fml1+Fml2,Vars,Fml3+Fml4) :- !,
        simplify_deps(Fml1,Vars,Fml3),
        simplify_deps(Fml2,Vars,Fml4).
simplify_deps(Fml,_Vars,Fml) :- !.

simplify_deps_clauses([Clause|Clauses],Vars,[Clause2|Clauses2]) :- !,
        simplify_deps_clause(Clause,Vars,Clause2),
        simplify_deps_clauses(Clauses,Vars,Clauses2).
simplify_deps_clauses([],_Vars,[]) :- !.

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

implies(Fml1,-(-Fml2),Vars) :- !,
        implies(Fml1,Fml2,Vars).
implies(Fml1,Fml2,Vars) :-
        cached_implies(Fml1,Fml2,Vars,true), !.
implies(Fml1,Fml2,Vars) :-
        cached_implies(Fml1,Fml2,Vars,false), !, fail.
implies(Fml1,Fml2,[]) :-
        entails([Fml1],Fml2), !,
        assert(cached_implies(Fml1,Fml2,[],true)).
implies(Fml1,Fml2,Vars) :-
        % as one formula b/c of free variables
        % => use (automatic) universal closure
        valid(all(Vars,Fml1=>Fml2)), !,
        assert(cached_implies(Fml1,Fml2,Vars,true)).
implies(Fml1,Fml2,Vars) :- !,
        assert(cached_implies(Fml1,Fml2,Vars,false)),
        fail.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Debugging
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% ensure that every quantifier uses a separate variable symbol
check_variables(Fml) :-
        check_variables(Fml,[],_), !.
check_variables(Fml) :- 
        report_message(['Variable check failed: ', Fml]),
        gtrace.
check_variables(Fml1<=>Fml2,Vars1,Vars2) :- !,
        check_variables(Fml1,Vars1,Vars3),
        check_variables(Fml2,Vars3,Vars2).
check_variables(Fml1<=Fml2,Vars1,Vars2) :- !,
        check_variables(Fml1,Vars1,Vars3),
        check_variables(Fml2,Vars3,Vars2).
check_variables(Fml1=>Fml2,Vars1,Vars2) :- !,
        check_variables(Fml1,Vars1,Vars3),
        check_variables(Fml2,Vars3,Vars2).
check_variables(Fml1*Fml2,Vars1,Vars2) :- !,
        check_variables(Fml1,Vars1,Vars3),
        check_variables(Fml2,Vars3,Vars2).
check_variables(Fml1+Fml2,Vars1,Vars2) :- !,
        check_variables(Fml1,Vars1,Vars3),
        check_variables(Fml2,Vars3,Vars2).
check_variables(-Fml,Vars1,Vars2) :- !,
        check_variables(Fml,Vars1,Vars2).
check_variables(some(Var,Fml),Vars1,Vars2) :-
        var(Var), !,
        check_variables(some([Var],Fml),Vars1,Vars2).
check_variables(some([Var|Vars],Fml),Vars1,Vars2) :-
        not(member2(Var,Vars1)), !,
        check_variables(some(Vars,Fml),[Var|Vars1],Vars2).
check_variables(some([Var|_],_),Vars1,_) :-
        member2(Var,Vars1), !,
        fail.
check_variables(some([],Fml),Vars1,Vars2) :- !,
        check_variables(Fml,Vars1,Vars2).
check_variables(all(Var,Fml),Vars1,Vars2) :-
        var(Var), !,
        check_variables(all([Var],Fml),Vars1,Vars2).
check_variables(all([Var|Vars],Fml),Vars1,Vars2) :-
        not(member2(Var,Vars1)), !,
        check_variables(all(Vars,Fml),[Var|Vars1],Vars2).
check_variables(all([Var|_],_),Vars1,_) :-
        member2(Var,Vars1), !,
        fail.
check_variables(all([],Fml),Vars1,Vars2) :- !,
        check_variables(Fml,Vars1,Vars2).
check_variables(_Fml,Vars,Vars) :- !.