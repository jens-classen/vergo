/**
 
transfinal_cgraph

This file provides predicates for defining a transition semantics for
Golog programs that also serves as a set of rules for constructing the
characteristic graphs of such programs. Cf.

Jens Claßen: Planning and Verification in the Agent Language Golog.
PhD Thesis, Department of Computer Science, RWTH Aachen University,
2013.

@author  Jens Claßen
@license GPL

 **/

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
        not(include_preconditions),
        var(A), !.
trans(A,A,[],true,[],true) :-
        not(include_preconditions),
        nonvar(A),
        prim_action(A), !.
trans(A,A,[],true,[],poss(A)) :-
        include_preconditions,
        var(A), !.
trans(A,A,[],true,[],poss(A)) :-
        include_preconditions,
        nonvar(A),
        prim_action(A), !.
trans(test(_),_,_,_,_,_) :- !, 
        fail.
trans([],_,_,_,_,_) :- !, 
        fail.
trans([D1|D2],A,DP,F1,Vars,F2) :-
        trans(D1,A,D1P,F1,Vars,F2),
        flatten([D1P|D2],DP).
trans([D1|D2],A,DP,F2,Vars,F1*F2P) :-
        final(D1,F1),
        trans(D2,A,DP,F2,Vars,F2P).
trans(nondet(D1,D2),A,DP,F1,Vars,F2) :-
        trans(D1,A,DP,F1,Vars,F2);
        trans(D2,A,DP,F1,Vars,F2).
trans(pick(Var,D),A,DP,F1,[Var|Vars],F2) :-
        trans(D,A,DP,F1,Vars,F2).
trans(pick(Var,Domain,D),A,DP,F1,Vars,F2) :-
        domain(Domain,Element),
        subv(Var,Element,D,D2),
        trans(D2,A,DP,F1,Vars,F2).
trans(conc(D1,D2),A,conc(D1P,D2),F1,Vars,F2) :-
        trans(D1,A,D1P,F1,Vars,F2).
trans(conc(D1,D2),A,conc(D1,D2P),F1,Vars,F2) :-
        trans(D2,A,D2P,F1,Vars,F2).
trans(star(D),A,DP,true,Vars,F2) :-
        trans(D,A,G,true,Vars,F2),
        flatten([G|star(D)],DP).
trans([D1|star(D)],A,DP,F*F1,Vars,F2) :-
        final(D1,F),
        trans(D,A,G,F1,Vars,F2),
        flatten([G|star(D)],DP).
trans(D,A,DP,F1,Vars,F2) :-
        progdef(D,M),
        trans(M,A,DP,F1,Vars,F2).

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
