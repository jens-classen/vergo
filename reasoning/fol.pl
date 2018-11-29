:- module(fol, [entails/2,
                inconsistent/1,
                consistent/1,
                valid/1,
                equivalent/2,
                get_reasoner/1,
                set_reasoner/1,
                check_equivalence/2,
                simplify/2,
                disjoin/2,
                conjoin/2,
                free_variables/2,
                op(1130, xfy, <=>),
                op(1110, xfy, <=),
                op(1110, xfy, =>)]).

/* We use the following symbols for writing formulas:

   true
   false

    *  conjunction
    +  disjunction
    -  negation
   <=> equivalence
    => implication
   <=  implication
    
    =  equality

   some(Variable,Formula) existential quantification
   all(Variable,Formula)  universal quantification

   Variables have to be (uppercase) Prolog variables. */


% % TPTP FOF operator definitions from Jens Otten's LeanCoP
% /* Operator definitions for TPTP syntax. */
:- op(1130, xfy, <=>). % equivalence
:- op(1110, xfy, =>).  % implication
:- op(1110, xfy, <=).  % implication
% :- op( 500, fy, ~).    % negation
% :- op( 500,xfy, :).

% :- op(1100, xfy, '|').  % disjunction
% :- op(1000, xfy, &).    % conjunction
% :- op( 500, fy, !).     % universal quantifier
% :- op( 500, fy, ?).     % existential quantifier
% :- op( 400, xfx, =).    % equality
% :- op( 299, fx, $).     % for $true/$false

:- use_module('../reasoning/eprover',
              [entails/2 as eprover_entails,
               inconsistent/1 as eprover_inconsistent,
               consistent/1 as eprover_consistent,
               valid/1 as eprover_valid,
               equivalent/2 as eprover_equivalent]).

:- use_module('../reasoning/vampire',
              [entails/2 as vampire_entails,
               inconsistent/1 as vampire_inconsistent,
               consistent/1 as vampire_consistent,
               valid/1 as vampire_valid,
               equivalent/2 as vampire_equivalent]).

:- use_module('../reasoning/fo2solver',
              [entails/2 as fo2solver_entails,
               inconsistent/1 as fo2solver_inconsistent,
               consistent/1 as fo2solver_consistent,
               valid/1 as fo2solver_valid,
               equivalent/2 as fo2solver_equivalent]).

:- discontiguous(simplify/2).

:- dynamic(reasoner/1).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Reasoner
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% default: E prover
reasoner(eprover).
%reasoner(vampire).
%reasoner(fo2solver).

set_reasoner(X) :- 
        member(X,[eprover,vampire,fo2solver]), !,
        retract(reasoner(_)),
        assert(reasoner(X)).

get_reasoner(X) :-
        reasoner(X).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Reasoning Procedures
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

/* Succeeds if ListOfAxioms entails Conjecture. */
entails(ListOfAxioms,Conjecture) :-
        reasoner(X),
        entails(ListOfAxioms,Conjecture,X).

entails(ListOfAxioms,Conjecture,eprover) :-
        eprover_entails(ListOfAxioms,Conjecture).
entails(ListOfAxioms,Conjecture,vampire) :-
        vampire_entails(ListOfAxioms,Conjecture).
entails(ListOfAxioms,Conjecture,fo2solver) :-
        fo2solver_entails(ListOfAxioms,Conjecture).

/* Succeeds if ListOfFormulas is inconsistent. */
inconsistent(ListOfFormulas) :-
        reasoner(X),
        inconsistent(ListOfFormulas,X).

inconsistent(ListOfFormulas,eprover) :-
        eprover_inconsistent(ListOfFormulas).
inconsistent(ListOfFormulas,vampire) :-
        vampire_inconsistent(ListOfFormulas).
inconsistent(ListOfFormulas,fo2solver) :-
        fo2solver_inconsistent(ListOfFormulas).

/* Succeeds if ListOfFormulas is consistent. */
consistent(ListOfFormulas) :-
        reasoner(X),
        consistent(ListOfFormulas,X).

consistent(ListOfFormulas,eprover) :-
        eprover_consistent(ListOfFormulas).
consistent(ListOfFormulas,vampire) :-
        vampire_consistent(ListOfFormulas).
consistent(ListOfFormulas,fo2solver) :-
        fo2solver_consistent(ListOfFormulas).

/* Succeeds if Formula is valid. */
valid(Formula) :-
        reasoner(X),
        valid(Formula,X).

valid(Formula,eprover) :-
        eprover_valid(Formula).
valid(Formula,vampire) :-
        vampire_valid(Formula).
valid(Formula,fo2solver) :-
        fo2solver_valid(Formula).

/* Succeeds if Formula1 and Formula2 are equivlanet. */
equivalent(Formula1,Formula2) :-
        reasoner(X),
        equivalent(Formula1,Formula2,X).

equivalent(Formula1,Formula2,eprover) :-
        eprover_equivalent(Formula1,Formula2).
equivalent(Formula1,Formula2,vampire) :-
        vampire_equivalent(Formula1,Formula2).
equivalent(Formula1,Formula2,fo2solver) :-
        fo2solver_equivalent(Formula1,Formula2).

% check for equivalence, abort if fails
% useful as assertion for debugging purposes
check_equivalence(F2,F3) :-
        equivalent(F2,F3), !.
check_equivalence(F2,F3) :-  !,
        report_message(['Not equivalent: ']),
        report_message(['Fml1 = ', F2]),
        report_message(['Fml2 = ', F3]),
        gtrace.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Formula Simplification
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

/* simplify(+F,-R)
   simplify formula F to obtain R
   makes 'obvious' simplifications like F&$true => F */

% true, false
simplify(true,true) :- !.
simplify(false,false) :- !.

% equivalence
simplify(F1<=>F2,R) :- 
        simplify(F1,FS1),
        simplify(F2,FS2), !,
        simplify_equiv(FS1,FS2,R).

simplify_equiv(true,false,false) :- !.
simplify_equiv(false,true,false) :- !.
simplify_equiv(F1,F2,true) :-
        F1 == F2, !.
simplify_equiv(F1,F2,F1<=>F2).
             
% implication
simplify(F1=>F2,R) :-
        simplify(F1,FS1),
        simplify(F2,FS2), !,
        simplify_impl(FS1,FS2,R).

simplify_impl(_,true,true) :- !.
simplify_impl(false,_,true) :- !.
simplify_impl(F1,F2,true) :-
        F1 == F2, !.
simplify_impl(F1,F2,F1=>F2).

simplify(F1<=F2,R) :- !,
        simplify(F2=>F1,R).

% disjunction
simplify(F1+F2,R) :-
        simplify(F1,FS1),
        simplify(F2,FS2), !,
        simplify_disj(FS1,FS2,R).

simplify_disj(true,_,true) :- !.
simplify_disj(_,true,true) :- !.
simplify_disj(false,F2,F2) :- !.
simplify_disj(F1,false,F1) :- !.
simplify_disj(-F1,F2,true) :-
        F1 == F2, !.
simplify_disj(F1,-F2,true) :-
        F1 == F2, !.
simplify_disj(F1,F2,R) :-
        F1 == F2, !, R=F1.
simplify_disj(F1,F2,F1+F2).

%conjunction
simplify(F1*F2,R) :-
        simplify(F1,FS1),
        simplify(F2,FS2), !,
        simplify_conj(FS1,FS2,R).

simplify_conj(false,_,false) :- !.
simplify_conj(_,false,false) :- !.
simplify_conj(true,F2,F2) :- !.
simplify_conj(F1,true,F1) :- !.
simplify_conj(-F1,F2,false) :-
        F1 == F2, !.
simplify_conj(F1,-F2,false) :-
        F1 == F2, !.
simplify_conj(F1,F2,R) :-
        F1 == F2, !, R=F1.
simplify_conj(F1,F2,F1*F2).

%negation
simplify(-F,R) :-
        simplify(F,FS), !,
        simplify_neg(FS,R).

simplify_neg(true,false) :- !.
simplify_neg(false,true) :- !.
simplify_neg(-F,F) :- !.
simplify_neg(F,-F).

% quantification
simplify(some(Xs,F1),R) :- !,
        simplify(F1,R1),
        simplify_some(Xs,R1,R).
simplify(all(Xs,F1),R) :- !,
        simplify(F1,R1),
        simplify_all(Xs,R1,R).

simplify_some(_Xs,false,false) :- !.
simplify_some(_Xs,true,true) :- !.
simplify_some(Xs,F,F) :- Xs==[], !.
simplify_some(Xs,F,some(Xs,F)).

simplify_all(_Xs,false,false) :- !.
simplify_all(_Xs,true,true) :- !.
simplify_all(Xs,F,F) :-  Xs==[], !.
simplify_all(Xs,F,all(Xs,F)).

% equality
simplify(X=Y,true) :- 
        X==Y, !.

% base case.
simplify(F,FS) :-
        var(FS), !, FS=F.
simplify(F,FS) :-
        F == FS.

/* conjoin(+L,-F)
   F is the conjunction of the list of formulas L */
conjoin([F],F) :- !.
conjoin([F1,F2|Fs],F1*FR) :- !,
        conjoin([F2|Fs],FR).
conjoin([],true) :- !.

/* disjoin(+L,-F)
   F is the disjunction of the list of formulas L */
disjoin([F],F) :- !.
disjoin([F1,F2|Fs],F1+FR) :- !,
        disjoin([F2|Fs],FR).
disjoin([],false) :- !.
        
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Formula Properties
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% determine free varibles of a formula
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
