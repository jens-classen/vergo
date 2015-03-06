:- module(utils, 
          [subv/4,
           subvl/4,
           report_message/1,
           count/2,
           atom_string/2,
           string_codes/2]).

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
