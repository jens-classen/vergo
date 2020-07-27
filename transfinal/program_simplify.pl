/**

<module> Program Simplification

This module provides functionality for simplifying Golog programs.

@author  Jens Claßen
@license GPLv2

 **/
:- module(program_simplify, [simplify_program/2, progdef/2]).

:- use_module('../../logic/fol', [simplify/2]).

simplify_program(A,D) :-
        var(A), !, D=A.
simplify_program(A,A) :-
        (poss(A,_);poss(A,_,_)), !. % primitive action
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

progdef(if(C,T,E),
        nondet([test(C),T],[test(-C),E])).
progdef(while(C,D),
        [star([test(C),D]),test(-C)]).
progdef(loop(D),
        while(true,D)).
progdef(Name,Def) :-
        program(Name,Def).
