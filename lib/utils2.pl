:- module(utils).

:- export subset2/2.
:- export intersection2/3.
:- export disjoint2/2.
:- export member2/2.
:- export forall/2.
:- export subv/4.

subset2([X|Xs],Ys) :-
        member2(X,Ys),
        subset2(Xs,Ys).
subset2([],_Ys).

intersection2([X|Xs],Ys,[X|Zs]) :-
        member2(X,Ys), !,
        intersection2(Xs,Ys,Zs).
intersection2([_|Xs],Ys,Zs) :-
        intersection2(Xs,Ys,Zs).
intersection2([],_,[]).

disjoint2([X|Xs],Ys) :-
        not(member2(X,Ys)),
        disjoint2(Xs,Ys).
disjoint2([],_Ys).

member2(X,[Y|_L]) :- X == Y.
member2(X,[_|L]) :- member2(X,L).
member2(_,[]) :- fail.


% do Action for each Goal
forall(Goal,Action):-
        Goal,
	(Action
	->	fail
	;	!,fail).
forall(_,_).

               /*  T2 is T1 with X1 replaced by X2  */
subv(X1,X2,T1,T2) :- var(T1), T1 == X1, !, T2 = X2.
subv(_,_,T1,T2)   :- var(T1), !, T2 = T1.
subv(X1,X2,T1,T2) :- T1 == X1, !, T2 = X2.
subv(X1,X2,T1,T2) :- T1 =..[F|L1], subvl(X1,X2,L1,L2), T2 =..[F|L2].

subvl(_,_,[],[]).
subvl(X1,X2,[T1|L1],[T2|L2]) :- subv(X1,X2,T1,T2), subvl(X1,X2,L1,L2).
