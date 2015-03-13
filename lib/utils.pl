:- module(utils, 
          [subv/4,
           subvl/4,
           report_message/1,
           count/2,
           atom_string/2,
           string_codes/2,
           subset2/2,
           intersection2/3,
           setminus2/3,
           disjoint2/2,
           member2/2,
           forall/2]).

/*  T2 is T1 with X1 replaced by X2  */
subv(X1,X2,T1,T2) :- var(T1), T1 == X1, !, T2 = X2.
subv(_,_,T1,T2)   :- var(T1), !, T2 = T1.
subv(X1,X2,T1,T2) :- T1 == X1, !, T2 = X2.
subv(X1,X2,T1,T2) :- T1 =..[F|L1], subvl(X1,X2,L1,L2), T2 =..[F|L2].

subvl(_,_,[],[]).
subvl(X1,X2,[T1|L1],[T2|L2]) :- subv(X1,X2,T1,T2), subvl(X1,X2,L1,L2).

/* Print a mesage */
report_message([L|Ls]) :- !, print(L), report_message(Ls).
report_message([]) :- !, print('\n').
report_message(M) :- report_message([M]).

/* Count solutions */
count(G, Count) :-
        aggregate_all(count, G, Count).

/* Renaming SWI 6.4.1 -> 6.6.0 */
atom_string(A,S) :- string_to_atom(S,A).
string_codes(S,C) :- string_to_list(S,C).

/* Set operations based on _term_ equality, not unification */
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

setminus2([X|Xs],Ys,[X|Zs]) :-
        not(member2(X,Ys)), !,
        setminus2(Xs,Ys,Zs).
setminus2([_X|Xs],Ys,Zs) :-
        setminus2(Xs,Ys,Zs).
setminus2([],_,[]).

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
