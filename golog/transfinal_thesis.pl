/**
 
<module> transfinal_thesis

This modiles provides predicates defining a transition semantics for
Golog programs that also serves as a set of rules for constructing the
characteristic graphs of such programs. Cf.

Jens Claßen: Planning and Verification in the Agent Language Golog.
PhD Thesis, Department of Computer Science, RWTH Aachen University,
2013.

@author  Jens Claßen
@license GPLv2

 **/
:- module(transfinal_thesis, [step/6, trans/6, trans/4, final/2]).

:- use_module('../logic/cwa').
:- use_module('program_simplify').

:- multifile user:ignore_preconditions.

/**
 * trans(+Prog1,?Act,?Prog2,?Cond) is nondet
 *
 * There is a transition from program Prog1 to program Prog2
 * via ground action Act if condition Cond holds in the situation
 * before executing Act.
 *
 * TODO: we want to *determine* the ground action
 *
 **/
trans(Prog1,Act,Prog2,Cond) :-
        ground(Act),
        trans(Prog1,Act,Prog2,Cond1,Vars,Cond2),
        Cond = Cond1*some(Vars,Cond2), !.

/**
 * trans(+Prog1,?Act,?Prog2,?Cond1,?Vars:List,?Cond2) is nondet
 *
 * There is a transition from program Prog1 to program Prog2
 * via (possibly non-ground) action Act, where Vars is the list of
 * variables to be instantiated, Cond1 the condition to be evaluted
 * before variable instantiation and Cond2 the condition to be
 * evaluated after variable instantiation.
 **/
trans(A,A,[],true,[],true) :-
        user:ignore_preconditions,
        var(A), !.
trans(A,A,[],true,[],true) :-
        user:ignore_preconditions,
        nonvar(A),
        (poss(A,_);poss(A,_,_)), !.
trans(A,A,[],true,[],poss(A)) :-
        not(user:ignore_preconditions),
        var(A), !.
trans(A,A,[],true,[],poss(A)) :-
        not(user:ignore_preconditions),
        nonvar(A),
        (poss(A,_);poss(A,_,_)), !.
trans(test(_),_,_,_,_,_) :- !, 
        fail.
trans([],_,_,_,_,_) :- !, 
        fail.
trans([D1|D2],A,DP,F1,Vars,F2) :-
        trans(D1,A,D1P,F1,Vars,F2),
        flatten([D1P|D2],DP).
trans([D1|D2],A,DP,F2,Vars,F1*F2P) :-
        flatten(D2,[D3|_]),
        (not(D3 = star(_)); % star case handled below
         var(D3)),
        final(D1,F1),
        trans(D2,A,DP,F2,Vars,F2P).
trans(nondet(D1,D2),A,DP,F1,Vars,F2) :-
        trans(D1,A,DP,F1,Vars,F2);
        trans(D2,A,DP,F1,Vars,F2).
trans(pick(Var,D),A,DP,F1,[Var|Vars],F2) :-
        trans(D,A,DP,F1,Vars,F2).
trans(pick(Var,Domain,D),A,DP,F1,Vars,F2) :-
        is_type_element(Domain,Element),
        subv(Var,Element,D,D2),
        trans(D2,A,DP,F1,Vars,F2).
trans(conc(D1,D2),A,conc(D1P,D2),F1,Vars,F2) :-
        trans(D1,A,D1P,F1,Vars,F2).
trans(conc(D1,D2),A,conc(D1,D2P),F1,Vars,F2) :-
        trans(D2,A,D2P,F1,Vars,F2).
trans(star(D),A,DP,true,Vars,F2) :-
        trans(D,A,G,true,Vars,F2),
        flatten([G,star(D)],DP).
trans([D1,star(D)],A,DP,F*F1,Vars,F2) :-
        final(D1,F),
        trans(D,A,G,F1,Vars,F2),
        flatten([G,star(D)],DP).
trans(D,A,DP,F1,Vars,F2) :-
        progdef(D,M),
        trans(M,A,DP,F1,Vars,F2).

/**
 * step(+Prog1,?Act,?Prog2,?Cond1,?Vars:List,?Cond2) is nondet
 *
 * This predictate is a meta-relation over trans/6 that integrates
 * "sink" states for program termination and failure, thus
 * extending finite execution paths to infinite ones. This is
 * mainly used for verification.
 **/
step(D,A,DP,F1,Vars,F2) :-
        trans(D,A,DP,F1,Vars,F2).
step(D,terminate,terminated,F,[],true) :-
        final(D,F).
step(D,fail,failed,(-F1)*(-F2),[],true) :-
        D \= terminated,
        final(D,F1),
        findall(FP1*some(Vars,FP2),
                trans(D,_A,_DP,FP1,Vars,FP2),
                L),
        disjoin(L,F2).
step(D,fail,failed,-F2,[],true) :-
        D \= terminated,
        not(final(D,_F1)),
        findall(FP1*some(Vars,FP2),
                trans(D,_A,_DP,FP1,Vars,FP2),
                L),
        disjoin(L,F2).
step(terminated,terminate,terminated,true,[],true).
step(failed,fail,failed,true,[],true).

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

is_action(A) :- 
        var(A), !.
is_action(A) :-
        nonvar(A), !,
        (poss(A,_);poss(A,_,_)).
