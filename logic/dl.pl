/**

<module> DL

This module implements an interface for reasoning in a description
logic, specifically the ALC family as supported by the description
logic reasoner 'Konclude'.

Formulas may contain standard names, represented as Prolog atom
starting with '#', e.g. '#1', '#2', '#bob'.

@author  Jens Claßen
@license GPLv2

 **/

:- module(dl, [entails/2,
               inconsistent/1,
               consistent/1,
               get_fml_std_names/2,
               simplify/2]).

:- reexport('l', [is_std_name/1]).
:- reexport('../logic/una', [get_fml_std_names/2]).

:- use_module('../lib/utils').
:- use_module('../logic/l', [op(1130, xfy, <=>),
                             op(1110, xfy, <=),
                             op(1110, xfy, =>)]).
:- use_module('../logic/una').
:- use_module('../reasoners/konclude',
              [entails/3 as entails_konclude,
               inconsistent/2 as inconsistent_konclude,
               consistent/2 as consistent_konclude]).

:- discontiguous simplify/2.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Check formula against set of formulas
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
                            
entails(Formulas,Fml) :-
        get_fml_std_names([Fml|Formulas],Names),
        entails_konclude(Formulas,Names,Fml), !.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Check inconsistency of set of formulas
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
                            
inconsistent(Formulas) :-
        get_fml_std_names(Formulas,Names),
        inconsistent_konclude(Formulas,Names), !.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Check consistency of set of formulas
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
                            
consistent(Formulas) :-
        get_fml_std_names(Formulas,Names),
        consistent_konclude(Formulas,Names), !.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Helper predicates
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% thing, nothing
simplify(thing,thing) :- !.
simplify(nothing,nothing) :- !.

% nominals
simplify(oneof([]),nothing) :- !.
simplify(oneof(Os),oneof(O2s)) :- !,
        sort(Os,O2s).

% conjunction
simplify(and(C),R) :-
        simplify_list(C,CS), !,
        sort(CS,CS2),
        simplify_and(CS2,R).

simplify_and([],thing) :- !.
simplify_and(C,nothing) :-
        member(nothing,C), !.
simplify_and(C,C2) :-
        member(thing,C), !,
        setminus2(C,[thing],C3),
        simplify_and(C3,C2).
simplify_and(C,C2) :-
        member(and(C3),C), !,
        setminus2(C,[and(C3)],C4),
        append(C4,C3,C5),
        simplify_and(C5,C2).
simplify_and(C,C2) :-
        member(oneof(O1),C),
        member(oneof(O2),C),
        O1 \= O2, !,
        setminus2(C,[oneof(O1),oneof(O2)],C3),
        intersection2(O1,O2,O),
        simplify(oneof(O),OS),
        simplify_and([OS|C3],C2).
simplify_and(C,C2) :-
        member(not(oneof(O1)),C),
        member(not(oneof(O2)),C),
        O1 \= O2, !,
        setminus2(C,[not(oneof(O1)),not(oneof(O2))],C3),
        union2(O1,O2,O),
        simplify(not(oneof(O)),OS),
        simplify_and([OS|C3],C2).
simplify_and(C,C2) :-
        member(oneof(O1),C),
        member(not(oneof(O2)),C), !,
        setminus2(C,[oneof(O1),not(oneof(O2))],C3),
        setminus2(O1,O2,O),
        simplify(oneof(O),OS),
        simplify_and([OS|C3],C2).
simplify_and(C,C2) :-
        member(only(R,A),C),
        member(only(R,B),C),
        A \= B, !,
        setminus2(C,[only(R,A),only(R,B)],C3),
        simplify(only(R,and([A,B])),S),
        simplify_and([S|C3],C2).
simplify_and(C,C2) :-
        member(not(A),C),
        member(A,C), !,
        C2 = nothing.
simplify_and([C],C) :- !.
simplify_and(C,and(C)) :- !.

% disjunction
simplify(or(C),R) :-
        simplify_list(C,CS), !,
        sort(CS,CS2),
        simplify_or(CS2,R).

simplify_or([],nothing) :- !.
simplify_or(C,thing) :-
        member(thing,C), !.
simplify_or(C,C2) :-
        member(nothing,C), !,
        setminus2(C,[nothing],C3),
        simplify_or(C3,C2).
simplify_or(C,C2) :-
        member(or(C3),C), !,
        setminus2(C,[or(C3)],C4),
        append(C4,C3,C5),
        simplify_or(C5,C2).
simplify_or(C,C2) :-
        member(oneof(O1),C),
        member(oneof(O2),C),
        O1 \= O2, !,
        setminus2(C,[oneof(O1),oneof(O2)],C3),
        union2(O1,O2,O),
        simplify(oneof(O),OS),
        simplify_or([OS|C3],C2).
simplify_or(C,C2) :-
        member(not(oneof(O1)),C),
        member(not(oneof(O2)),C),
        O1 \= O2, !,
        setminus2(C,[not(oneof(O1)),not(oneof(O2))],C3),
        intersection2(O1,O2,O),
        simplify(not(oneof(O)),OS),
        simplify_or([OS|C3],C2).
simplify_or(C,C2) :-
        member(oneof(O1),C),
        member(not(oneof(O2)),C), !,
        setminus2(C,[oneof(O1),not(oneof(O2))],C3),
        setminus2(O2,O1,O),
        simplify(oneof(O),OS),
        simplify_or([OS|C3],C2).
simplify_or(C,C2) :-
        member(exists(R,A),C),
        member(exists(R,B),C),
        A \= B, !,
        setminus2(C,[exists(R,A),exists(R,B)],C3),
        simplify(exists(R,or([A,B])),S),
        simplify_or([S|C3],C2).
simplify_or(C,C2) :-
        member(not(A),C),
        member(A,C), !,
        C2 = thing.
simplify_or([C],C) :- !.
simplify_or(C,or(C)) :- !.

% negation
simplify(not(C),R) :-
        simplify(C,CS), !,
        simplify_not(CS,R).

simplify_not(thing,nothing) :- !.
simplify_not(nothing,thing) :- !.
simplify_not(not(C),C) :- !.
simplify_not(C,not(C)) :- !.

% quantification
simplify(exists(R,C),Res) :- !,
        simplify(C,CS),
        simplify_exists(R,CS,Res).
simplify(only(R,C),Res) :- !,
        simplify(C,CS),
        simplify_only(R,CS,Res).

simplify_exists(_R,nothing,nothing) :- !.
simplify_exists(R,C,exists(R,C)) :- !.
simplify_only(_R,thing,thing) :- !.
simplify_only(R,C,only(R,C)) :- !.

% TBox assertions
simplify(subsumedBy(C1,C2),Res) :- !,
        simplify(C1,C1S),
        simplify(C2,C2S),
        simplify_subsumedBy(C1S,C2S,Res).

simplify_subsumedBy(_C,thing,true) :- !.
simplify_subsumedBy(nothing,_C,true) :- !.
simplify_subsumedBy(C1,C2,subsumedBy(C1,C2)) :- !.

% Abox assertions
simplify(concept_assertion(C,N),concept_assertion(CS,N)) :- !,
        simplify(C,CS).
simplify(role_assertion(R,N1,N2),role_assertion(R,N1,N2)) :- !.

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
simplify_equiv(true,X,X) :- !.
simplify_equiv(X,true,X) :- !.
simplify_equiv(false,X,-X) :- !.
simplify_equiv(X,false,-X) :- !.
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
simplify_impl(true,F2,F2) :- !.
simplify_impl(F1,false,-F1) :- !.
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

% otherwise do nothing
simplify(F,F) :- !.

simplify_list([],[]) :- !.
simplify_list([F|Fs],[S|Ss]) :- !,
        simplify(F,S),
        simplify_list(Fs,Ss).

% todo: is there a normal form that can be used for simplification?
