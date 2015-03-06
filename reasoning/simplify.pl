
% easy simplifications using "nil"
%% simplify_program(A,B) :- var(A), !, var(B), A=B. % action variable
%% simplify_program(A,A) :- 
%%         primitive_action(A), !.
simplify_program(do(A),do(A)).
simplify_program(?($true),nil).
simplify_program(nil,nil).
simplify_program(?(F),?(FS)) :- 
        simplify_formula(F,FS).
simplify_program((D1;D2),nil) :- 
        simplify_program(D1,nil), 
        simplify_program(D2,nil), !.
simplify_program((D1;D2),D1S) :- 
        simplify_program(D2,nil),
        simplify_program(D1,D1S), !.
simplify_program((D1;D2),D2S) :- 
        simplify_program(D1,nil),
        simplify_program(D2,D2S), !.
simplify_program((D1;D2),(D1S;D2S)) :-
        simplify_program(D1,D1S),
        simplify_program(D2,D2S).
simplify_program((D1|D2),(D1S|D2S)) :- 
        simplify_program(D1,D1S), 
        simplify_program(D2,D2S).
simplify_program(pi(X,D),pi(X,DS)) :- 
        simplify_program(D,DS).
simplify_program(conc(D1,D2),conc(D1S,D2S)) :- 
        simplify_program(D1,D1S), 
        simplify_program(D2,D2S).
simplify_program(star(nil),nil) :- !.
simplify_program(star(D),star(DS)) :- 
        simplify_program(D,DS).
simplify_program(conc(D1,D2),nil) :-
        simplify_program(D1,nil),
        simplify_program(D2,nil), !.
simplify_program(conc(D1,D2),D1S) :-
        simplify_program(D2,nil),
        simplify_program(D1,D1S), !.
simplify_program(conc(D1,D2),D2S) :-
        simplify_program(D1,nil),
        simplify_program(D2,D2S), !.
simplify_program(conc(D1,D2),conc(D1S,D2S)) :-
        simplify_program(D1,D1S),
        simplify_program(D2,D2S).

simplify_program(D,DS) :- def_construct(D,Def), simplify_program(Def,DS).
simplify_program(D,DS) :- program(D,Def), simplify_program(Def,DS).

% easy simplifications using "$true" and "$false"
%simplify_formula(X=Y,$false) :- atom(X), atom(Y), X \=Y. % standard names= atoms
simplify_formula(X=Y,$true) :- X==Y,!.
simplify_formula(X=Y,$false) :- % unique names for actions
        nonvar(X), nonvar(Y),
        precondition(X,_),
        precondition(Y,_),
        X =.. [A|_], Y =.. [B|_],
        A \= B, !.
simplify_formula(X=Y,Equalities) :-
        nonvar(X), nonvar(Y),
        precondition(X,_),
        precondition(Y,_),
        X =.. [A|XArgs], Y =..[A|YArgs],!,
        make_equalities(XArgs,YArgs,Equalities).
simplify_formula(X=Y,X=Y).

%% %simplify_formula(X!=Y,$true) :- atom(X), atom(Y), X \=Y. % standard names= atoms
%% simplify_formula(X!=Y,$false) :- X==Y,!.
%% simplify_formula(X!=Y,$true) :- % unique names for actions
%%         precondition(X,_),
%%         precondition(Y,_),
%%         X =.. [A|_], Y =.. [B|_],
%%         A \= B,!.
%% simplify_formula(X!=Y,Inequalities) :-
%%         precondition(X,_),
%%         precondition(Y,_),
%%         X =.. [A|XArgs], Y =..[A|YArgs],!,
%%         make_inequalities(XArgs,YArgs,Inequalities).
%% simplify_formula(X!=Y,X!=Y).

simplify_formula(F,F) :- (isfluent(F); F=poss(_); F=exo(_); F=occ(_)),!.
simplify_formula($true,$true) :- !.
simplify_formula($false,$false) :- !.
simplify_formula(~F,$false) :-
        simplify_formula(F,$true),!.
simplify_formula(~F,$true) :-
        simplify_formula(F,$false),!.
simplify_formula(~F,~FS) :- !,
        simplify_formula(F,FS).
simplify_formula((F1&F2),$false) :- 
        simplify_formula(F1,$false);
        simplify_formula(F2,$false).
simplify_formula((F1&F2),$true) :-
        simplify_formula(F1,$true),
        simplify_formula(F2,$true), !.
simplify_formula((F1&F2),F1S) :-
        simplify_formula(F2,$true), !,
        simplify_formula(F1,F1S).
simplify_formula((F1&F2),F2S) :-
        simplify_formula(F1,$true), !,
        simplify_formula(F2,F2S).
simplify_formula((F1&F2),(F1S&F2S)) :-
        simplify_formula(F1,F1S),
        simplify_formula(F2,F2S).
simplify_formula((F1|F2),$true) :- 
        simplify_formula(F1,$true);
        simplify_formula(F2,$true).
simplify_formula((F1|F2),$false) :-
        simplify_formula(F1,$false),
        simplify_formula(F2,$false), !.
simplify_formula((F1|F2),F1) :-
        simplify_formula(F2,$false).
simplify_formula((F1|F2),F2) :-
        simplify_formula(F1,$false).
simplify_formula((F1|F2),(F1S|F2S)) :-
        simplify_formula(F1,F1S),
        simplify_formula(F2,F2S).
simplify_formula(?[]:F,FS) :- !,
        simplify_formula(F,FS).
simplify_formula(![]:F,FS) :- !,
        simplify_formula(F,FS).
simplify_formula(?_Vars:F,$true) :- 
        simplify_formula(F,$true),!.
simplify_formula(?_Vars:F,$false) :-
        simplify_formula(F,$false),!.
simplify_formula(!_Vars:F,$true) :-
        simplify_formula(F,$true),!.
simplify_formula(!_Vars:F,$false) :-
        simplify_formula(F,$false),!.
simplify_formula(?Vars:F,?Vars:FS) :-
        simplify_formula(F,FS).
simplify_formula(!Vars:F,!Vars:FS) :-
        simplify_formula(F,FS).

simplify_formula(F,FS) :- def(F,Def), simplify_formula(Def,FS).

