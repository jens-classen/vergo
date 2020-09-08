/**

<module> Ligression (Literal Regression)

This module implements a variant of the Situation Calculus regression
operator that works over sets of literals rather than actions, the
idea being that such literal sets represent the (cumulated) effects of
a (sequence of) action(s).

A similar operation was introduced in

Yongmei Liu and Gerhard Lakemeyer: "On First-Order Definability and
Computability of Progression for Local-Effect Actions and Beyond". In:
Proceedings of the Twenty-First International Joint Conference on
Artificial Intelligence (IJCAI 2009). AAAI Press, 2009, pp. 860–866.

to compute the progression of a local-effect action theory, and used
in 

Benjamin Zarrieß and Jens Claßen: "Verifying CTL* Properties of Golog
Programs over Local-effect Actions". In: Proceedings of the
Twenty-First European Conference on Artificial Intelligence (ECAI
2014). IOS Press, 2014, pp. 939–944.

for the verification of Golog programs over local-effect actions by
means of abstraction.

@author  Jens Claßen
@license GPLv2

 **/
:- module(ligression, [ligress/3]).

:- use_module('../logic/def').
:- use_module('../logic/l', [op(1130, xfy, <=>),
                             op(1110, xfy, <=),
                             op(1110, xfy, =>)]).
:- use_module('../logic/una', [is_std_name/1,
                               get_fml_std_names/2]).
:- use_module('../logic/cwa').

:- multifile user:rel_fluent/1.
:- multifile user:rel_fluent/2.
:- multifile user:rel_rigid/1.
:- multifile user:rel_rigid/2.
:- multifile user:poss/2.
:- multifile user:poss/3.
:- multifile user:causes_true/3.
:- multifile user:causes_false/3.
:- multifile user:def/2.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Ligression for general formulas
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

ligress(F,E,R) :-
        user:def(F,D), !,
        ligress(D,E,R).
ligress(F1<=>F2,E,R1<=>R2) :- !,
        ligress(F1,E,R1),
        ligress(F2,E,R2).
ligress(F1=>F2,E,R1=>R2) :- !,
        ligress(F1,E,R1),
        ligress(F2,E,R2).
ligress(F1<=F2,E,R1<=R2) :- !,
        ligress(F1,E,R1),
        ligress(F2,E,R2).
ligress(F1+F2,E,R1+R2) :- !,
        ligress(F1,E,R1),
        ligress(F2,E,R2).
ligress(F1*F2,E,R1*R2) :- !,
        ligress(F1,E,R1),
        ligress(F2,E,R2).
ligress(-F1,E,-R1) :- !,
        ligress(F1,E,R1).
ligress(some(Xs,F1),E,some(Xs,R1)) :- !,
        ligress(F1,E,R1).
ligress(all(Xs,F1),E,all(Xs,R1)) :- !,
        ligress(F1,E,R1).
ligress(X=Y,_,X=Y) :- !.
ligress(true,_,true) :- !.
ligress(false,_,false) :- !.

ligress(concept_assertion(C,N),[],concept_assertion(C,N)) :- !.
ligress(concept_assertion(C,N),E,concept_assertion(CR,N)) :- !,
        ligress_dl(C,E,CR).
ligress(role_assertion(R,N1,N2),[],role_assertion(R,N1,N2)) :- !.
ligress(role_assertion(R,N1,N2),E,Result) :- !,
        ligress(concept_assertion(exists(R,oneof([N2])),N1),E,Result).

ligress(poss(A),E,R) :-
        user:poss(A,F), !,
        ligress(F,E,R).
ligress(poss(A),E,R) :-
        user:poss(A,T,F1), !,
        types_cons(T,F2),
        conjoin([F1|F2],F),
        ligress(F,E,R).

ligress(Atom,[],Atom) :- !.
ligress(Atom,E,(Atom+RP)*RN) :-
        ligress_pos(Atom,E,RP),
        ligress_neg(Atom,E,RN).

ligress_pos(_Atom,[],false) :- !.
ligress_pos(Atom,[L|E],(Equalities+RP)) :-
        Atom=..[F|Args],
        L=..[F|Args2],
        length(Args,N),
        length(Args2,N),!,
        pos_equalities(Args,Args2,Equalities),
        ligress_pos(Atom,E,RP).
ligress_pos(Atom,[_|E],RP) :-
        ligress_pos(Atom,E,RP).

pos_equalities([Arg1|Args1],[Arg2|Args2],Equalities) :- 
        is_std_name(Arg1),
        is_std_name(Arg2),
        % same names => true
        Arg1=Arg2, !,
        pos_equalities(Args1,Args2,Equalities).
pos_equalities([Arg1|_Args1],[Arg2|_Args2],false) :- 
        is_std_name(Arg1),
        is_std_name(Arg2),
        % distinct names => true
        not(Arg1=Arg2), !.
pos_equalities([Arg1|Args1],[Arg2|Args2],(Arg1=Arg2)*Equalities) :-
        pos_equalities(Args1,Args2,Equalities).
pos_equalities([],[],true).

ligress_neg(_Atom,[],true) :- !.
ligress_neg(Atom,[-L|E],Inequalities*RN) :-
        Atom=..[F|Args],
        L=..[F|Args2],
        length(Args,N),
        length(Args2,N),!,
        neg_inequalities(Args,Args2,Inequalities),
        ligress_neg(Atom,E,RN).
ligress_neg(Atom,[_|E],RN) :-
        ligress_neg(Atom,E,RN).

neg_inequalities([Arg1|Args1],[Arg2|Args2],Inequalities) :- 
        is_std_name(Arg1),
        is_std_name(Arg2),
        % same names => false
        Arg1=Arg2, !,
        neg_inequalities(Args1,Args2,Inequalities).
neg_inequalities([Arg1|_Args1],[Arg2|_Args2],true):- 
        is_std_name(Arg1),
        is_std_name(Arg2),
        % distinct names => true
        not(Arg1=Arg2), !.
neg_inequalities([Arg1|Args1],[Arg2|Args2],-(Arg1=Arg2)+Inequalities) :-
        neg_inequalities(Args1,Args2,Inequalities).
neg_inequalities([],[],false).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Ligression for concepts of the description logic ALCO_U
% (according to Benjamin Zarriess' note from 2015-09-08)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

ligress_dl(thing,_E,thing) :- !.
ligress_dl(nothing,_E,nothing) :- !.
ligress_dl(not(C),E,not(D)) :- !,
        ligress_dl(C,E,D).
ligress_dl(and(Cs),E,and(Rs)) :- !,
        ligress_dl_list(Cs,E,Rs).
ligress_dl(or(Cs),E,or(Rs)) :- !,
        ligress_dl_list(Cs,E,Rs).
ligress_dl(oneof(Ns),_E,oneof(Ns)) :- !.
ligress_dl(exists(R,C),E,Result) :- !,
        get_fml_std_names(subsumedBy(nothing,exists(R,C)),Ind1),
        get_fml_std_names(E,Ind2),
        append(Ind1,Ind2,Ind),
        ligress_dl(C,E,Res),
        findall(and([oneof([A]),exists(R,and([oneof([B]),Res]))]),
                (member(A,Ind),
                 member(B,Ind),
                 L =.. [R,A,B],
                 not(member(L,E)),
                 not(member(-L,E))),
                R3s),
        findall(and([oneof([A]),exists(universal,and([oneof([B]),Res]))]),
                (member(L,E), L =.. [R,A,B]),
                R4s),                    
        R1 = and([not(oneof(Ind)),exists(R,Res)]),
        R2 = and([oneof(Ind),exists(R,and([not(oneof(Ind)),Res]))]),
        R3 = or(R3s),
        R4 = or(R4s),
        Result = or([R1,R2,R3,R4]).
ligress_dl(only(R,C),E,Result) :- !,
        get_fml_std_names(subsumedBy(nothing,only(R,C)),Ind1),
        get_fml_std_names(E,Ind2),
        append(Ind1,Ind2,Ind),
        ligress_dl(C,E,Res),
        findall(or([not(oneof([A])),all(R,or([not(oneof([B])),Res]))]),
                (member(A,Ind),
                 member(B,Ind),
                 L =.. [R,A,B],
                 not(member(L,E)),
                 not(member(-L,E))),
                R3s),
        findall(or([not(oneof([A])),exists(universal,and([oneof([B]),Res]))]),
                (member(L,E), L =.. [R,A,B]),
                R4s),                    
        R1 = or([oneof(Ind),all(R,Res)]),
        R2 = or([not(oneof(Ind)),all(R,or([oneof(Ind),Res]))]),
        R3 = or(R3s),
        R4 = and(R4s),
        Result = or([R1,R2,R3,R4]).
ligress_dl(C,E,R) :- !,
        findall(A,(member(L,E), L =.. [C,A]),PosInd),
        findall(B,(member(-L,E), L =.. [C,B]),NegInd),
        R = or([and([C,not(oneof(NegInd))]),oneof(PosInd)]).

ligress_dl_list([C|Cs],E,[R|Rs]) :- !,
        ligress_dl(C,E,R),
        ligress_dl_list(Cs,E,Rs).
ligress_dl_list([],_E,[]) :- !.
