/**
 
transfinal_simple

This file provides predicates for the construction of the transition
system according to what is described in the papers

Benjamin Zarrieß and Jens Claßen:
Verifying CTL* Properties of Golog Programs over Local-Effect Actions.
In Proceedings of the Twenty-First European Conference on Artificial Intelligence (ECAI 2014),
IOS Press, 2014.

Benjamin Zarrieß and Jens Claßen:
On the Decidability of Verifying LTL Properties of Golog Programs. 
Technical Report 13-10, Chair of Automata Theory, TU Dresden, Dresden, Germany, 2013.

@author  Jens Claßen
@license GPLv2

 **/

:- use_module('../logic/cwa').
:- use_module('program_simplify').

/**
 * trans(+Prog1,?Act,?Prog2,?Cond) is nondet
 *
 * There is a transition from program Prog1 to program Prog2
 * via (possibly non-ground) action Act under condition Cond.
 **/
trans(A,A,[],F) :-
        poss(A,F).
trans(A,A,[],F) :-
        poss(A,Types,F),
        type_cons(Types).
trans([D1|D2],A,DP,F) :-
        trans(D1,A,G,F),
        flatten([G|D2],DP).
trans([D1|D2],A,DP,F1*F2) :-
        final(D1,F1),
        trans(D2,A,DP,F2).
trans(nondet(D1,D2),A,DP,F) :-
        trans(D1,A,DP,F);
        trans(D2,A,DP,F).
trans(conc(D1,D2),A,conc(D1P,D2),F) :-
        trans(D1,A,D1P,F).
trans(conc(D1,D2),A,conc(D1,D2P),F) :-
        trans(D2,A,D2P,F).
trans(star(D),A,DP,F) :-
        trans(D,A,G,F),
        flatten([G|star(D)],DP).

trans(pick(Var,Domain,D),A,DP,F) :-
        is_type_element(Domain,Element),
        subv(Var,Element,D,D2),
        trans(D2,A,DP,F).

trans(D,A,DP,F) :-
        progdef(D,M),
        trans(M,A,DP,F).

final(test(F),F).
final([D1|D2],F1*F2) :-
        final(D1,F1),
        final(D2,F2).
final(nondet(D1,D2),F1+F2) :-
        final(D1,F1),
        final(D2,F2).
final(conc(D1,D2),F1*F2) :-
        final(D1,F1),
        final(D2,F2).
final(star(_D),true).
final([],true).

final(pick(Var,Domain,D),F) :-
        is_type_element(Domain,Element),
        subv(Var,Element,D,D2),
        final(D2,F).

final(D,F) :-
        progdef(D,M),
        final(M,F).

/**
 * step(+Prog1,?Act,?Prog2,?Cond1) is nondet
 *
 * This predictate is a meta-relation over trans/6 that integrates
 * "sink" states for program termination and failure, thus
 * extending finite execution paths to infinite ones. This is
 * mainly used for verification.
 **/
step(D,A,DP,F) :-
        trans(D,A,DP,F).
step(D,terminate,terminated,F) :-
        final(D,F).
step(D,fail,failed,(-F1)*(-F2)) :-
        D \= terminated,
        final(D,F1),
        findall(FP,trans(D,_A,_DP,FP),L),
        disjoin(L,F2).
step(D,fail,failed,-F2) :-
        D \= terminated,
        not(final(D,_F1)),
        findall(FP,trans(D,_A,_DP,FP),L),
        disjoin(L,F2).
step(terminated,terminate,terminated,true).
step(failed,fail,failed,true).

type_cons([X-T|XTs]) :-
        is_type_element(T,X),
        type_cons(XTs).
type_cons([]).
