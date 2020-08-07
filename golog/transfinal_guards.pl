/**
 
<module> transfinal_guards

This module provides predicates defining a transition semantics for
Golog programs that also serves as a set of rules for constructing the
characteristic graphs of such programs. This is a new version that
uses "guards" as transition conditions, i.e. sequences that
arbitrarily alternate between pick quantifiers and condition formulas.

@author  Jens Claßen
@license GPLv2

 **/
:- module(transfinal_guards, [step/4, trans/4, final/2,
                              guardcond/2, guardcond/3]).

:- use_module('../logic/cwa').
:- use_module('program_simplify').

:- multifile user:ignore_preconditions/0.

/**
 * trans(+Prog1,?Guard,?Action,?Prog2) is nondet
 *
 * There is a transition from program Prog1 to program Prog2 via 
 * (possibly non-ground) action Action, guarded by Guard. 
 **/
trans(A,[],A,[]) :-
        user:ignore_preconditions,
        var(A), !.
trans(A,[],A,[]) :-
        user:ignore_preconditions,
        nonvar(A),
        (poss(A,_);poss(A,_,_)), !.
trans(A,[test(poss(A))],A,[]) :-
        not(user:ignore_preconditions),
        var(A), !.
trans(A,[test(poss(A))],A,[]) :-
        not(user:ignore_preconditions),
        nonvar(A),
        (poss(A,_);poss(A,_,_)), !.
trans(test(_),_,_,_) :- !, 
        fail.
trans([],_,_,_) :- !, 
        fail.
trans([D1|D2],G,A,DP) :-
        trans(D1,G,A,D1P),
        flatten([D1P|D2],DP).
trans([D1|D2],[test(F1)|G],A,DP) :-
        final(D1,F1),
        F1 \= false, % filter out false early
        trans(D2,G,A,DP).
trans(nondet(D1,D2),G,A,DP) :-
        trans(D1,G,A,DP);
        trans(D2,G,A,DP).
trans(pick(Var,D),[pick(Var)|G],A,DP) :-
        trans(D,G,A,DP).
trans(pick(Var,Domain,D),G,A,DP) :-
        is_type_element(Domain,Element),
        subv(Var,Element,D,D2),
        trans(D2,G,A,DP).
trans(conc(D1,D2),G,A,conc(D1P,D2)) :-
        trans(D1,G,A,D1P).
trans(conc(D1,D2),G,A,conc(D1,D2P)) :-
        trans(D2,G,A,D2P).
trans(star(D),G,A,DP) :-
        trans(D,G,A,D1P),
        flatten([D1P,star(D)],DP).
% trans([D1,star(D)],[test(F)|G],A,DP) :-
%         final(D1,F),
%         trans(D,G,A,D1P),
%         flatten([D1P,star(D)],DP).
trans(D,G,A,DP) :-
        progdef(D,M),
        trans(M,G,A,DP).

/**
 * step(+Prog1,?Guard,?Act,?Prog2) is nondet
 *
 * This predictate is a meta-relation over trans/4 that integrates
 * "sink" states for program termination and failure, thus
 * extending finite execution paths to infinite ones. This is
 * mainly used for verification.
 **/
step(D,G,A,DP) :-
        trans(D,G,A,DP).
step(D,[test(F)],terminate,terminated) :-
        final(D,F).
step(D,[test(F)],fail,failed) :-
        D \= terminated,
        D \= failed,
        final(D,TermCond),
        findall(-GuardCond,
                (trans(D,G,_A,_DP),
                 guardcond(G,GuardCond)),
                NegGuardConds),
        conjoin([-TermCond|NegGuardConds],F).
step(D,[test(F)],fail,failed) :-
        D \= terminated,
        D \= failed,
        not(final(D,_)),
        findall(-GuardCond,
                (trans(D,G,_A,_DP),
                 guardcond(G,GuardCond)),
                NegGuardConds),
        conjoin(NegGuardConds,F).
step(terminated,[],terminate,terminated).
step(failed,[],fail,failed).

/**
  * final(+Prog,?Cond) is nondet
  *
  * The program Prog is final (may terminate) if condition Cond
  * holds.
  **/
final(A,F) :-
        var(A), !, F=false.
final(A,F) :-
        (poss(A,_);poss(A,_,_)), !, F=false.
final(fail,false) :- !.
final(test(F),F).
final([],true).
final([D1|D2],F1*F2) :-
        final(D1,F1),
        final(D2,F2).
final(nondet(D1,D2),F1+F2) :-
        final(D1,F1),
        final(D2,F2).
final(pick(Var,D),some(Var,F)) :-
        final(D,F).
final(pick(Var,Domain,D),F) :-
        is_type_element(Domain,Element),
        subv(Var,Element,D,D2),
        final(D2,F).
final(conc(D1,D2),F1*F2) :-
        final(D1,F1),
        final(D2,F2).
final(star(_D),true).
final(D,F) :-
        progdef(D,M),
        final(M,F).

/**
  * guardcond(+Guard,-Result) is det
  *
  * Result is the "guard condition" of Guard applied to "true",
  * i.e. true preceded by existential quantifiers (=picks) and
  * subformulas corresponding to test conditions.
  **/
guardcond(G,R) :-
        guardcond(G,true,R).

/**
  * guardcond(+Guard,+InputFormula,-Result) is det
  *
  * Result is the "guard condition" of Guard applied to InputFormula,
  * i.e. InputFormula preceded by existential quantifiers (=picks) and
  * subformulas corresponding to test conditions.
  **/
guardcond([],I,I) :- !.
guardcond([test(F)|G],I,F*R) :- !,
        guardcond(G,I,R).
guardcond([pick(Var)|G],I,some(Var,R)) :- !,
        guardcond(G,I,R).

is_action(A) :- 
        var(A), !.
is_action(A) :-
        nonvar(A), !,
        (poss(A,_);poss(A,_,_)).
