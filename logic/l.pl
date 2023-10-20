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

:- module(l, [entails_l/3,
              inconsistent_l/2,
              consistent_l/2,
              valid_l/2,
              equivalent_l/3,
              is_std_name/1,
              simplify_l/2]).

:- reexport('../logic/fol', [get_reasoner/1,
                             set_reasoner/1,
                             simplify/2,
                             conjuncts/2,
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
:- use_module('../logic/fol').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Check formula against set of formulas
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
                            
entails_l(Formulas,Fml,Truth) :-
        get_names_axioms_from_fmls(uni,[Fml|Formulas],StdNameAxioms),
        union(Formulas,StdNameAxioms,FormulasWithAxioms),
        entails(FormulasWithAxioms,Fml), !,
        Truth = true.
entails_l(_Formulas,_Fml,Truth) :- !,
        Truth = false.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Check inconsistency of set of formulas
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
                            
inconsistent_l(Formulas,Truth) :-
        get_names_axioms_from_fmls(uni,Formulas,StdNameAxioms),
        union(Formulas,StdNameAxioms,FormulasWithAxioms),
        inconsistent(FormulasWithAxioms), !,
        Truth = true.
inconsistent_l(_Formulas,Truth) :- !,
        Truth = false.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Check consistency of set of formulas
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
                            
consistent_l(Formulas,true) :-
        inconsistent_l(Formulas,false), !.
consistent_l(Formulas,false) :-
        inconsistent_l(Formulas,true), !.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Check validity of formula
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
                            
valid_l(Formula,Truth) :-
        entails_l([true],Formula,Truth), !.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Check equivalence of two formulas
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
                            
equivalent_l(Formula1,Formula2,Truth) :-
        entails_l([Formula1],Formula2,true),
        entails_l([Formula2],Formula1,true), !,
        Truth = true.
equivalent_l(_Formula1,_Formula2,Truth) :- !,
        Truth = false.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Formula simplification
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

simplify_l(F,R) :-
        apply_una(F,F2),
        simplify(F2,R).
