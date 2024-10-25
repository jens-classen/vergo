/**

<module> L

This module implements the logic 'L', i.e. first-order logic with a
countable set of standard names as the fixed universe of discourse, as
described in

Hector J. Levesque and Gerhard Lakemeyer: The Logic of Knowledge
Bases. MIT Press, 2001.

Here, a standard name is any Prolog atom starting with '#',
e.g. '#1', '#2', '#bob'.

@author  Jens Claßen
@license GPLv2

 **/

:- module(l, [get_reasoner/1,
              set_reasoner/1,
              entails/2,
              inconsistent/1,
              consistent/1,
              valid/1,
              equivalent/2,
              is_std_name/1,
              simplify/2]).

:- reexport('../logic/fol', [conjuncts/2,
                             conjoin/2,
                             disjuncts/2,
                             disjoin/2,
                             free_variables/2,
                             op(1130, xfy, <=>),
                             op(1110, xfy, <=),
                             op(1110, xfy, =>)]).

:- reexport('../logic/una', [get_fml_std_names/2,
                             get_new_std_name/2,
                             is_std_name/1]).

:- use_module('../logic/cwa').
:- use_module('../logic/una').
:- use_module('../logic/fol', [get_reasoner/1 as fol_get_reasoner,
                               set_reasoner/1 as fol_set_reasoner,
                               entails/2 as fol_entails,
                               inconsistent/1 as fol_inconsistent,
                               simplify/2 as fol_simplify]).

:- dynamic(reasoner/1).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Reasoner
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% default: FOL prover
reasoner(fol).

set_reasoner(X) :-
        fol_set_reasoner(X), !,
        retract(reasoner(_)),
        assert(reasoner(fol)).

get_reasoner(X) :-
        not(reasoner(fol)), !,
        reasoner(X).
get_reasoner(X) :-
        fol_get_reasoner(X), !.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Check formula against set of formulas
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

entails(Formulas,Fml) :-
        reasoner(fol),
        get_names_axioms_from_fmls(uni,[Fml|Formulas],StdNameAxioms),
        union(Formulas,StdNameAxioms,FormulasWithAxioms),
        fol_entails(FormulasWithAxioms,Fml), !.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Check inconsistency of set of formulas
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

inconsistent(Formulas) :-
        reasoner(fol),
        get_names_axioms_from_fmls(uni,Formulas,StdNameAxioms),
        union(Formulas,StdNameAxioms,FormulasWithAxioms),
        fol_inconsistent(FormulasWithAxioms), !.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Check consistency of set of formulas
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

consistent(Formulas) :-
        not(inconsistent(Formulas)), !.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Check validity of formula
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

valid(Formula) :-
        entails([true],Formula), !.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Check equivalence of two formulas
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

equivalent(Formula1,Formula2) :-
        entails([Formula1],Formula2),
        entails([Formula2],Formula1), !.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Formula simplification
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

simplify(F,R) :-
        apply_una(F,F2),
        fol_simplify(F2,R).
