:- module(una, [apply_una/2]).

:- use_module('../lib/utils').
:- use_module('../logic/cwa').
:- use_module('../logic/l').
:- use_module('../projection/regression', [isfluent/1,isrigid/1]).

:- multifile user:poss/2.
:- multifile user:poss/3.

apply_una(true,true) :- !.
apply_una(false,false) :- !.
apply_una(poss(A),poss(A)) :- !.
apply_una(exo(A),exo(A)) :- !.
apply_una(sf(A),sf(A)) :- !.
apply_una(F,F) :- isfluent(F), !.
apply_una(F,F) :- isrigid(F), !.
apply_una(F,F) :- def(F,_), !.

apply_una((X=Y),true) :- X==Y, !.
apply_una(-(X=Y),false) :- X==Y, !.

apply_una(-(X=Y),InEqualities) :-
        nonvar(X), nonvar(Y),
        unique_name(X),
        unique_name(Y),
        X =.. [A|XArgs], Y =..[A|YArgs], !,
        make_inequalities(XArgs,YArgs,InEqualities2),
        apply_una(InEqualities2,InEqualities).
apply_una(-(X=Y),true) :-
        nonvar(X), nonvar(Y),
        unique_name(X),
        unique_name(Y),
        X =.. [A|_], Y =.. [B|_],
        A \= B, !.
apply_una((X=Y),Equalities) :-
        nonvar(X), nonvar(Y),
        unique_name(X),
        unique_name(Y),
        X =.. [A|XArgs], Y =..[A|YArgs], !,
        make_equalities(XArgs,YArgs,Equalities2),
        apply_una(Equalities2,Equalities).
apply_una((X=Y),false) :-
        nonvar(X), nonvar(Y),
        unique_name(X),
        unique_name(Y),
        X =.. [A|_], Y =.. [B|_],
        A \= B, !.

apply_una(-F1,-F2) :- !,
        apply_una(F1,F2).
apply_una((F1+F2),(F3+F4)) :- !,
        apply_una(F1,F3),
        apply_una(F2,F4).
apply_una((F1*F2),(F3*F4)) :- !,
        apply_una(F1,F3),
        apply_una(F2,F4).
apply_una((F1<=>F2),(F3<=>F4)) :- !,
        apply_una(F1,F3),
        apply_una(F2,F4).
apply_una((F1=>F2),(F3=>F4)) :- !,
        apply_una(F1,F3),
        apply_una(F2,F4).
apply_una((F1<=F2),(F3<=F4)) :- !,
        apply_una(F1,F3),
        apply_una(F2,F4).
apply_una(some(A,F),R) :-
        var(A), !,
        apply_una(some([A],F),R).
apply_una(all(A,F),R) :-
        var(A), !,
        apply_una(all([A],F),R).
% ?[A]:(?[X]:(A=f(X))&F) --> ?[X]:F with A replaced by f(X)
apply_una(some([A],F1),some(Vars,F4)) :- % (*)
        action_equality_conjunct(A,Act,F1,F2,Vars), !,
        subv(A,Act,F2,F3),
        apply_una(F3,F4).
% ![A]:(![X]:(-(A=f(X)))|F) --> ![X]:F with A replaced by f(X)
apply_una(all([A],F1),all(Vars,F4)) :- % (**)
        action_inequality_disjunct(A,Act,F1,F2,Vars), !,
        subv(A,Act,F2,F3),
        apply_una(F3,F4).
% simplification using standard names
apply_una(some([X],-(Y=Z)),true) :-
        X==Y,
        unique_name(Z), !.
apply_una(some([X],-(Z=Y)),true) :-
        X==Y,
        unique_name(Z), !.
apply_una(all([X],(Y=Z)),false) :-
        X==Y,
        unique_name(Z), !.
apply_una(all([X],(Z=Y)),false) :-
        X==Y,
        unique_name(Z), !.
apply_una(some(Vars,F1),some(Vars,F2)) :- !,
        apply_una(F1,F2).
apply_una(all(Vars,F1),all(Vars,F2)) :- !,
        apply_una(F1,F2).
apply_una(some_t(Vars,F1),some_t(Vars,F2)) :- !,
        apply_una(F1,F2).
apply_una(all_t(Vars,F1),all_t(Vars,F2)) :- !,
        apply_una(F1,F2).
apply_una(after(A,F1),after(A,F2)) :- !,
        apply_una(F1,F2).
apply_una(know(F1),know(F2)) :- !,
        apply_una(F1,F2).

apply_una(F,F) :- !.

make_equalities([],[],true) :- !.
make_equalities([X],[Y],(X=Y)) :- !.
make_equalities([X|Xs],[Y|Ys],(X=Y)*Equ) :-  !,
        make_equalities(Xs,Ys,Equ).
make_inequalities([],[],false) :- !.
make_inequalities([X],[Y],-(X=Y)) :- !.
make_inequalities([X|Xs],[Y|Ys],(-(X=Y))+Equ) :- !,
        make_inequalities(Xs,Ys,Equ).

unique_name(X) :-
        poss(X,_);
        poss(X,_,_);
        X == fail; X == terminate;
        X =.. [F|_], is_stdname(F).

/**
  * action_equality_conjunct(-A,-Act,+Fml1,-Fml2,-Vars) is nondet
  *
  * If A is an existentially quantified variable representing an
  * action, this predicate looks for a conjunct in formula Fml1 
  * of the form some(Vars,(A=Act)*F) (modulo ordering) that will be
  * replaced by F in the process. Act and Vars will be returned such
  * that A can be substituted by Act and some([A],...) by 
  * some(Vars,...) in the process in rule (*) of apply_una above.
  *
  * @arg A    a (logical) variable, representing an action
  * @arg Act  a (non-variable) action term
  * @arg Fml1 a formula
  * @arg Fml2 resulting formula
  * @arg Vars quantified variables
  */
action_equality_conjunct(A,Act,(X=Y),(X=Y),[]) :-
        A==X,
        nonvar(Y),
        unique_name(Y),
        Act=Y, !.
action_equality_conjunct(A,Act,(X=Y),(X=Y),[]) :-
        A==Y,
        nonvar(X),
        unique_name(X),
        Act=X, !.
action_equality_conjunct(A,Act,some_t(VTs,F),Fml2,Vars) :- !,
        untype(some_t(VTs,F),Fml1),
        action_equality_conjunct(A,Act,Fml1,Fml2,Vars).
action_equality_conjunct(A,Act,some(Vars,F),F,Vars) :- !,
        action_equality_conjunct(A,Act,F,F,[]).
action_equality_conjunct(A,Act,-all_t(VTs,F),Fml2,Vars) :- !,
        untype(all_t(VTs,F),Fml1),
        action_equality_conjunct(A,Act,-Fml1,Fml2,Vars).
action_equality_conjunct(A,Act,-all(Vars,F),-F,Vars) :- !,
        action_inequality_disjunct(A,Act,F,F,[]). % sign change (!)
action_equality_conjunct(X,Y,Fml1*Fml2,Fml1P*Fml2,Vars) :-
        action_equality_conjunct(X,Y,Fml1,Fml1P,Vars), !.
action_equality_conjunct(X,Y,Fml1*Fml2,Fml1*Fml2P,Vars) :-
        action_equality_conjunct(X,Y,Fml2,Fml2P,Vars), !.

/**
  * action_inequality_disjunct(-A,-Act,+Fml1,-Fml2,-Vars) is nondet
  *
  * If A is a universally quantified variable representing an
  * action, this predicate looks for a disjunct in formula Fml1 
  * of the form all(Vars,(-(A=Act))+F) (modulo ordering) that will be
  * replaced by F in the process. Act and Vars will be returned such
  * that A can be substituted by Act and all([A],...) by 
  * all(Vars,...) in the process in rule (**) of apply_una above.
  *
  * @arg A    a (logical) variable, representing an action
  * @arg Act  a (non-variable) action term
  * @arg Fml1 a formula
  * @arg Fml2 resulting formula
  * @arg Vars quantified variables
  */
action_inequality_disjunct(A,Act,-(X=Y),-(X=Y),[]) :-
        A==X,
        nonvar(Y),
        unique_name(Y),
        Act=Y, !.
action_inequality_disjunct(A,Act,-(X=Y),-(X=Y),[]) :-
        A==Y,
        nonvar(X),
        unique_name(X),
        Act=X, !.
action_inequality_disjunct(A,Act,all_t(VTs,F),Fml2,Vars) :- !,
        untype(all_t(VTs,F),Fml1),
        action_inequality_disjunct(A,Act,Fml1,Fml2,Vars).
action_inequality_disjunct(A,Act,all(Vars,F),F,Vars) :- !,
        action_inequality_disjunct(A,Act,F,F,[]).
action_inequality_disjunct(A,Act,-some_t(VTs,F),Fml2,Vars) :- !,
        untype(some_t(VTs,F),Fml1),
        action_inequality_disjunct(A,Act,-Fml1,Fml2,Vars).
action_inequality_disjunct(A,Act,-some(Vars,F),-F,Vars) :- !,
        action_equality_conjunct(A,Act,F,F,[]). % sign change (!)
action_inequality_disjunct(X,Y,Fml1+Fml2,Fml1P+Fml2,Vars) :-
        action_inequality_disjunct(X,Y,Fml1,Fml1P,Vars), !.
action_inequality_disjunct(X,Y,Fml1+Fml2,Fml1+Fml2P,Vars) :-
        action_inequality_disjunct(X,Y,Fml2,Fml2P,Vars), !.
