/**
 
transfinal_guards

This file provides predicates for defining a transition semantics for
Golog programs that also serves as a set of rules for constructing the
characteristic graphs of such programs. This is a new version that
uses "guards" as transition conditions, i.e. sequences that
arbitrarily alternate between pick quantifiers and condition formulas.

@author  Jens Claßen
@license GPL

 **/

:- multifile include_preconditions/0.

/**
 * trans(+Prog1,?Guard,?Action,?Prog2) is nondet
 *
 * There is a transition from program Prog1 to program Prog2 via 
 * (possibly non-ground) action Action, guarded by Guard. 
 **/
trans(A,[],A,[]) :-
        not(include_preconditions),
        var(A), !.
trans(A,[],A,[]) :-
        not(include_preconditions),
        nonvar(A),
        prim_action(A), !.
trans(A,[test(poss(A))],A,[]) :-
        include_preconditions,
        var(A), !.
trans(A,[test(poss(A))],A,[]) :-
        include_preconditions,
        nonvar(A),
        prim_action(A), !.
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
        domain(Domain,Element),
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
        prim_action(A), !, F=false.
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
        domain(Domain,Element),
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
        prim_action(A).

progdef(if(C,T,E),
        nondet([test(C),T],[test(-C),E])).
progdef(while(C,D),
        [star([test(C),D]),test(-C)]).
progdef(loop(D),
        while(true,D)).
progdef(Name,Def) :-
        program(Name,Def).

simplify_program(A,D) :-
        var(A), !, D=A.
simplify_program(A,A) :-
        prim_action(A), !.
simplify_program(L,P) :-
        is_list(L), !,
        simplify_program_list(L,P).
simplify_program(nondet(P1,P2),P) :-
        simplify_program(P1,PS1),
        simplify_program(P2,PS2), !,
        simplify_nondet(PS1,PS2,P).
simplify_program(conc(P1,P2),conc(NP1,NP2)) :- !,
        simplify_program(P1,NP1),
        simplify_program(P2,NP2). 
simplify_program(star(P),star(NP)) :- !,
        simplify_program(P,NP).
simplify_program(pick(Var,Domain,P),pick(Var,Domain,NP)) :- !,
        simplify_program(P,NP).
simplify_program(pick(Var,P),pick(Var,NP)) :- !,
        simplify_program(P,NP).
simplify_program(test(F),R) :- !,
        simplify_test(F,R).
simplify_program(P,NP) :-
        progdef(P,D), !,
        simplify_program(D,NP).
simplify_program(fail,fail) :- !.
simplify_program(failed,failed) :- !.
simplify_program(terminate,terminate) :- !.
simplify_program(terminated,terminated) :- !.

simplify_nondet(P1,P2,R) :-
        P1==P2, !, R=P1.
simplify_nondet(P1,P2,nondet(P1,P2)) :- !.

simplify_test(F,R) :-
        simplify(F,FS), !,
        simplify_test2(FS,R).
simplify_test2(true,[]) :- !.
simplify_test2(false,fail) :- !.
simplify_test2(F,test(F)) :- !.

simplify_program_list(L,P) :- !,
        simplify_program_list2(L,LS),
        flatten(LS,LF),
        simplify_program_list3(LF,P).
simplify_program_list2([],[]).
simplify_program_list2([P|Ps],[NP|NPs]) :- !,
        simplify_program(P,NP),
        simplify_program_list2(Ps,NPs).
simplify_program_list3([P],P) :- !.
simplify_program_list3(L,P) :- !,
        flatten(L,P).
