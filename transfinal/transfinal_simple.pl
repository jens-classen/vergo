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
@license GPL

 **/

trans(A,A,[],F) :-
        prim_action(A),
        poss(A,F).
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
        domain(Domain,Element),
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
        domain(Domain,Element),
        subv(Var,Element,D,D2),
        final(D2,F).

final(D,F) :-
        progdef(D,M),
        final(M,F).

progdef(if(C,T,E),
        nondet([test(C),T],[test(-C),E])).
progdef(while(C,D),
        [star([test(C),D]),test(-C)]).
progdef(loop(D),
        while(true,D)).

progdef(Name,Def) :-
        program(Name,Def).

step(D,A,DP,F) :-
        trans(D,A,DP,F).
step(D,terminate,terminated,F) :-
        final(D,F).
step(D,fail,failed,(-F1)*(-F2)) :-
        final(D,F1),
        findall(FP,trans(D,_A,_DP,FP),L),
        disjoin(L,F2).
step(D,fail,failed,-F2) :-
        not(final(D,_F1)),
        findall(FP,trans(D,_A,_DP,FP),L),
        disjoin(L,F2).
step(terminated,terminate,terminated,true).
step(failed,fail,failed,true).

simplify_program(A,D) :-
        var(A), !, D=A.
simplify_program(A,A) :-
        prim_action(A), !.
simplify_program(L,P) :-
        is_list(L), !,
        simplify_program_list(L,LP),
        flatten(LP,P).
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

simplify_program_list([],[]).
simplify_program_list([P|Ps],[NP|NPs]) :-
        simplify_program(P,NP),
        simplify_program_list(Ps,NPs).
