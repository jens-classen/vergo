%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Regression
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- use_module(utils).

% poss if A is a variable => big disjunction over all cases
poss(A,Precondition) :- var(A), !, 
        % action+precondition with free variables => quantify
        findall(?Vars:(C=B & Phi),
                 (precondition(B,Phi),
                  term_variables((B,Phi),Vars),
                  Vars \= []),
                 QuantifiedPreconds),
        % action+precondition without free vars
        findall((C=B & Phi),
                (precondition(B,Phi),
                 term_variables((B,Phi),[])),
                NonQuantifiedPreconds),
        % combine them in big disjunction
        append(QuantifiedPreconds,NonQuantifiedPreconds,Preconds),
        bind_action_variable(Preconds,Preconds2,A), % unify the Cs
                                                    % with A
        make_disjunction(Preconds2,Precondition).
% poss if A is nonvar => take its precondition axiom
poss(A,Precondition) :- nonvar(A), !, precondition(A,Precondition).

bind_action_variable([],[],_).
bind_action_variable([?Vars:(_C=B & Phi)|D1],[?Vars:(A=B & Phi)|D2],A) :-
        bind_action_variable(D1,D2,A).
bind_action_variable([(_C=B & Phi)|D1],[(A=B & Phi)|D2],A) :-
        bind_action_variable(D1,D2,A).

make_disjunction([P],P) :- !.
make_disjunction([P|Ps], (P | D)) :- make_disjunction(Ps,D).
make_disjunction([],$true).



% fluent: everything that has an SSA
isfluent(F) :- F \= (_=_), ssa(F,_,_).
isfluent(F) :- F  = (X=_), nonvar(X), ssa((X=_),_,_). % don't unify with equalities over variables
isfluent(F) :- F  = (_=X), nonvar(X), ssa((X=_),_,_). % don't unify with equalities over variables

% action: everything that has a precondition axiom...
primitive_action(A) :- nonvar(A), precondition(A,_).
% ... or that is an action variable
primitive_action(A) :- var(A).

regress(S,?[A]:((poss(A)&exo(A))&F),Result) :- !,
        subv(A,requestCoffee(P),F,F1),
        %regress(S,~full(queue)&(?[P]:F1),Result).
        regress(S,~full&(?[P]:F1),Result).

regress(S,poss(A),Result) :- poss(A,Precondition), !, regress(S,Precondition,Result).
regress(S,exo(A),Result) :- exo(A,ExoCondition), !, regress(S,ExoCondition,Result).
regress([A|S],occ(T),Result) :- !, regress(S,A=T,Result).
regress([],occ(T),occ(T)) :- !.
regress([A|S],Fluent,Result) :- isfluent(Fluent), ssa(Fluent,A,Formula), !, regress(S,Formula,Result).
regress([A|S],(T=F),Result) :- isfluent((T=F)), ssa((F=T),A,Formula), !, regress(S,Formula,Result).

regress(S,after(A,Formula),Result) :- !, regress([A|S],Formula,Result).

regress(S,~F,Result) :- !, regress(S,F,NResult), Result=(~NResult).
regress(S,F1|F2,Result) :- !, regress(S,F1,Result1), regress(S,F2,Result2), Result=(Result1|Result2).
regress(S,F1&F2,Result) :- !, regress(S,F1,Result1), regress(S,F2,Result2), Result=(Result1&Result2).
regress(S,? Vars : Formula,Result) :- !, regress(S,Formula,Result1),
        Result = (? Vars : Result1).
regress(S,! Vars : Formula,Result) :- !, regress(S,Formula,Result1),
        Result = (! Vars : Result1).
regress(S,F1 <=> F2,Result) :- !, 
        regress(S,F1,Result1), 
        regress(S,F2,Result2), Result = (Result1 <=> Result2).
regress(S,F1  => F2,Result) :- !, 
        regress(S,F1,Result1), 
        regress(S,F2,Result2), Result = (Result1  => Result2).
regress(S,Formula,Result) :- def(Formula,Definition), !, regress(S,Definition,Result).

regress(_S,(X=Y),(X=Y)) :- !.
regress([],Fluent,Fluent) :- isfluent(Fluent), !.
regress(_,$true,$true) :- !.
regress(_,$false,$false) :- !.

regress(Fml,Res) :- !, regress([],Fml,Res).


apply_una(poss(A),poss(A)).
apply_una(exo(A),exo(A)).
apply_una(occ(A),occ(A)).
apply_una(F,F) :- isfluent(F).
apply_una($true,$true).
apply_una($false,$false).

apply_una((X=Y),$true) :- X==Y,!.
apply_una(~(X=Y),$false) :- X==Y,!.

apply_una(~(X=Y),InEqualities) :-
        nonvar(X), nonvar(Y),
        precondition(X,_),
        precondition(Y,_),
        X =.. [A|XArgs], Y =..[A|YArgs],!,
        make_inequalities(XArgs,YArgs,InEqualities).
apply_una(~(X=Y),$true) :-
        nonvar(X), nonvar(Y),
        precondition(X,_),
        precondition(Y,_),
        X =.. [A|_], Y =.. [B|_],
        A \= B, !.
apply_una((X=Y),Equalities) :-
        nonvar(X), nonvar(Y),
        precondition(X,_),
        precondition(Y,_),
        X =.. [A|XArgs], Y =..[A|YArgs],!,
        make_equalities(XArgs,YArgs,Equalities).
apply_una((X=Y),$false) :-
        nonvar(X), nonvar(Y),
        precondition(X,_),
        precondition(Y,_),
        X =.. [A|_], Y =.. [B|_],
        A \= B, !.

apply_una(~(X=Y),InEqualities) :-
        nonvar(X), nonvar(Y),
        standardname(X), standardname(Y),
        X =.. [F|XArgs], Y =..[F|YArgs],!,
        make_inequalities(XArgs,YArgs,InEqualities).
apply_una(~(X=Y),$true) :-
        nonvar(X), nonvar(Y),
        standardname(X), standardname(Y),
        X =.. [A|_], Y =.. [B|_],
        A \= B, !.
apply_una((X=Y),Equalities) :-
        nonvar(X), nonvar(Y),
        standardname(X), standardname(Y),
        X =.. [A|XArgs], Y =..[A|YArgs],!,
        make_equalities(XArgs,YArgs,Equalities).
apply_una((X=Y),$false) :-
        nonvar(X), nonvar(Y),
        standardname(X), standardname(Y),
        X =.. [A|_], Y =.. [B|_],
        A \= B, !.

apply_una((X=Y),(X=Y)).

apply_una(~F1,~F2) :- 
        apply_una(F1,F2).
apply_una((F1|F2),(F3|F4)) :-
        apply_una(F1,F3),
        apply_una(F2,F4).
apply_una((F1&F2),(F3&F4)) :-
        apply_una(F1,F3),
        apply_una(F2,F4).
apply_una(?Vars:F1,?Vars:F2) :-
        apply_una(F1,F2).
apply_una(!Vars:F1,!Vars:F2) :-
        apply_una(F1,F2).
apply_una((F1<=>F2),(F3<=>F4)) :-
        apply_una(F1,F3),
        apply_una(F2,F4).
apply_una((F1=>F2),(F3=>F4)) :-
        apply_una(F1,F3),
        apply_una(F2,F4).


make_equalities([X],[Y],(X=Y)).
make_equalities([X|Xs],[Y|Ys],(X=Y)&Equ) :-
        make_equalities(Xs,Ys,Equ).
make_inequalities([X],[Y],~(X=Y)).
make_inequalities([X|Xs],[Y|Ys],(~(X=Y))|Equ) :-
        make_equalities(Xs,Ys,Equ).

