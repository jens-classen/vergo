%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Regression
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- use_module('../lib/utils').
:- use_module('../reasoning/fol').

% poss if A is a variable => big disjunction over all cases
precond(A,Precondition) :- var(A), !, 
        % action+precondition with free variables => quantify
        findall(some(Vars,((C=B)*Phi)),
                 (poss(B,Phi),
                  term_variables((B,Phi),Vars),
                  Vars \= []),
                 QuantifiedPreconds),
        % action+precondition without free vars
        findall(((C=B)*Phi),
                (poss(B,Phi),
                 term_variables((B,Phi),[])),
                NonQuantifiedPreconds),
        % combine them in big disjunction
        append(QuantifiedPreconds,NonQuantifiedPreconds,Preconds),
        bind_action_variable(Preconds,Preconds2,A), % unify the Cs with A
        disjoin(Preconds2,Precondition).
precond(A,Precondition) :- nonvar(A), !,
        poss(A,Precondition).

% exo if A is a variable => big disjunction over all cases
exocond(A,Exocondition) :- var(A), !, 
        % action+exocondition with free variables => quantify
        findall(some(Vars,((C=B)*Phi)),
                 (exo(B,Phi),
                  term_variables((B,Phi),Vars),
                  Vars \= []),
                 QuantifiedExoconds),
        % action+exocondition without free vars
        findall(((C=B)*Phi),
                (exo(B,Phi),
                 term_variables((B,Phi),[])),
                NonQuantifiedExoconds),
        % combine them in big disjunction
        append(QuantifiedExoconds,NonQuantifiedExoconds,Exoconds),
        bind_action_variable(Exoconds,Exoconds2,A), % unify the Cs with A
        disjoin(Exoconds2,Exocondition).
exocond(A,Exocondition) :- nonvar(A), !,
        exo(A,Exocondition).

ssa(Fluent,A,Condition) :- rel_fluent(Fluent), var(A), !, 
        % action+poscondition with free variables => quantify
        findall(some(Vars,((C=B)*Phi)),
                 (causes_true(B,Fluent,Phi),
                  term_variables((B,Phi),Vars),
                  Vars \= []),
                 QuantifiedPosconds),
        % action+poscondition without free vars
        findall(((C=B)*Phi),
                (causes_true(B,Fluent,Phi),
                 term_variables((B,Phi),[])),
                NonQuantifiedPosconds),
        % combine them in big disjunction
        append(QuantifiedPosconds,NonQuantifiedPosconds,Posconds),
        bind_action_variable(Posconds,Posconds2,A), % unify the Cs with A
        disjoin(Posconds2,Poscondition),
        % action+negcondition with free variables => quantify
        findall(some(Vars,((C=B)*Phi)),
                 (causes_false(B,Fluent,Phi),
                  term_variables((B,Phi),Vars),
                  Vars \= []),
                 QuantifiedNegconds),
        % action+negcondition without free vars
        findall(((C=B)*Phi),
                (causes_false(B,Fluent,Phi),
                 term_variables((B,Phi),[])),
                NonQuantifiedNegconds),
        % combine them in big disjunction
        append(QuantifiedNegconds,NonQuantifiedNegconds,Negconds),
        bind_action_variable(Negconds,Negconds2,A), % unify the Cs with A
        disjoin(Negconds2,Negcondition),
        Condition2 = Poscondition+Fluent*(-Negcondition),
        simplify(Condition2,Condition).
ssa(Fluent,A,Condition) :- rel_fluent(Fluent), nonvar(A), !,
        ssa(Fluent,B,Condition3),
        B=A,
        apply_una(Condition3,Condition2),
        simplify(Condition2,Condition).
 
ssa((Fluent=Y),A,Condition) :- fun_fluent(Fluent), var(A), !, 
        % action+condition with free variables => quantify
        findall(some(Vars,((C=B)*Phi)),
                 (causes(B,Fluent,Y,Phi),
                  term_variables((B,Phi),Vars),
                  Vars \= []),
                 QuantifiedConds),
        % action+condition without free vars
        findall(((C=B)*Phi),
                (causes(B,Fluent,Y,Phi),
                 term_variables((B,Phi),[])),
                NonQuantifiedConds),
        % combine them in big disjunction
        append(QuantifiedConds,NonQuantifiedConds,Conds),
        bind_action_variable(Conds,Conds2,A), % unify the Cs with A
        disjoin(Conds2,Cond),
        copy_term((Cond,Y),(CondC,X)),
        Condition2 = Cond+(Fluent=Y)*(-some(X,CondC)),
        simplify(Condition2,Condition).
ssa((Fluent=Y),A,Condition) :- fun_fluent(Fluent), nonvar(A), !,
        ssa((Fluent=Y),B,Condition3),
        B=A,
        apply_una(Condition3,Condition2),
        simplify(Condition2,Condition).       

bind_action_variable([],[],_).
bind_action_variable([some(Vars,((_C=B)*Phi))|D1],[some(Vars,((A=B)*Phi))|D2],A) :-
        bind_action_variable(D1,D2,A).
bind_action_variable([((_C=B)*Phi)|D1],[((A=B)*Phi)|D2],A) :-
        bind_action_variable(D1,D2,A).

isfluent(F) :- rel_fluent(F).
isfluent((F=_)) :- fun_fluent(F).

regress(S,poss(A),Result) :- 
        precond(A,Precondition), !, 
        regress(S,Precondition,Result).
regress(S,exo(A),Result) :- 
        exocond(A,ExoCondition), !, 
        regress(S,ExoCondition,Result).
%regress([A|S],occ(T),Result) :- !, 
%        regress(S,A=T,Result).
%regress([],occ(T),occ(T)) :- !.
regress([A|S],Fluent,Result) :- 
        rel_fluent(Fluent), 
        ssa(Fluent,A,Formula), !, 
        regress(S,Formula,Result).
regress([A|S],(Fluent=Y),Result) :- 
        fun_fluent(Fluent), 
        ssa((Fluent=Y),A,Formula), !, 
        regress(S,Formula,Result).
regress(S,after(A,Formula),Result) :- !, 
        regress([A|S],Formula,Result).
regress(S,-F,Result) :- !, 
        regress(S,F,NResult),
        Result=(-NResult).
regress(S,F1+F2,Result) :- !, 
        regress(S,F1,Result1),
        regress(S,F2,Result2),
        Result=(Result1+Result2).
regress(S,F1*F2,Result) :- !, 
        regress(S,F1,Result1),
        regress(S,F2,Result2),
        Result=(Result1*Result2).
regress(S,some(Vars,Formula),Result) :- !,
        regress(S,Formula,Result1),
        Result=some(Vars,Result1).
regress(S,forall(Vars,Formula),Result) :- !,
        regress(S,Formula,Result1),
        Result=forall(Vars,Result1).
regress(S,F1<=>F2,Result) :- !, 
        regress(S,F1,Result1), 
        regress(S,F2,Result2),
        Result=(Result1<=>Result2).
regress(S,F1=>F2,Result) :- !, 
        regress(S,F1,Result1), 
        regress(S,F2,Result2),
        Result=(Result1=>Result2).
regress(S,F1<=F2,Result) :- !, 
        regress(S,F1,Result1), 
        regress(S,F2,Result2),
        Result=(Result1<=Result2).
regress(S,Formula,Result) :- 
        def(Formula,Definition), !, 
        regress(S,Definition,Result).

regress(_S,(X=Y),(X=Y)) :- !.
regress([],Fluent,Fluent) :- isfluent(Fluent), !.
regress(_,true,true) :- !.
regress(_,false,false) :- !.

regress(Fml,Res) :- !, regress([],Fml,Res).


apply_una(poss(A),poss(A)).
apply_una(exo(A),exo(A)).
apply_una(F,F) :- isfluent(F).
apply_una(true,true).
apply_una(false,false).

apply_una((X=Y),true) :- X==Y,!.
apply_una(-(X=Y),false) :- X==Y,!.

apply_una(-(X=Y),InEqualities) :-
        nonvar(X), nonvar(Y),
        prim_action(X),
        prim_action(Y),
        X =.. [A|XArgs], Y =..[A|YArgs],!,
        make_inequalities(XArgs,YArgs,InEqualities).
apply_una(-(X=Y),true) :-
        nonvar(X), nonvar(Y),
        prim_action(X),
        prim_action(Y),
        X =.. [A|_], Y =.. [B|_],
        A \= B, !.
apply_una((X=Y),Equalities) :-
        nonvar(X), nonvar(Y),
        prim_action(X),
        prim_action(Y),
        X =.. [A|XArgs], Y =..[A|YArgs],!,
        make_equalities(XArgs,YArgs,Equalities).
apply_una((X=Y),false) :-
        nonvar(X), nonvar(Y),
        prim_action(X),
        prim_action(Y),
        X =.. [A|_], Y =.. [B|_],
        A \= B, !.

apply_una(-(X=Y),InEqualities) :-
        nonvar(X), nonvar(Y),
        stdname(X), stdname(Y),
        X =.. [F|XArgs], Y =..[F|YArgs],!,
        make_inequalities(XArgs,YArgs,InEqualities).
apply_una(-(X=Y),true) :-
        nonvar(X), nonvar(Y),
        stdname(X), stdname(Y),
        X =.. [A|_], Y =.. [B|_],
        A \= B, !.
apply_una((X=Y),Equalities) :-
        nonvar(X), nonvar(Y),
        stdname(X), stdname(Y),
        X =.. [A|XArgs], Y =..[A|YArgs],!,
        make_equalities(XArgs,YArgs,Equalities).
apply_una((X=Y),false) :-
        nonvar(X), nonvar(Y),
        stdname(X), stdname(Y),
        X =.. [A|_], Y =.. [B|_],
        A \= B, !.

apply_una((X=Y),(X=Y)).

apply_una(-F1,-F2) :- 
        apply_una(F1,F2).
apply_una((F1+F2),(F3+F4)) :-
        apply_una(F1,F3),
        apply_una(F2,F4).
apply_una((F1*F2),(F3*F4)) :-
        apply_una(F1,F3),
        apply_una(F2,F4).
apply_una(some(Vars,F1),some(Vars,F2)) :-
        apply_una(F1,F2).
apply_una(forall(Vars,F1),forall(Vars,F2)) :-
        apply_una(F1,F2).
apply_una((F1<=>F2),(F3<=>F4)) :-
        apply_una(F1,F3),
        apply_una(F2,F4).
apply_una((F1=>F2),(F3=>F4)) :-
        apply_una(F1,F3),
        apply_una(F2,F4).
apply_una((F1<=F2),(F3<=F4)) :-
        apply_una(F1,F3),
        apply_una(F2,F4).


make_equalities([],[],true).
make_equalities([X],[Y],(X=Y)).
make_equalities([X|Xs],[Y|Ys],(X=Y)*Equ) :-
        make_equalities(Xs,Ys,Equ).
make_inequalities([],[],false).
make_inequalities([X],[Y],-(X=Y)).
make_inequalities([X|Xs],[Y|Ys],(-(X=Y))+Equ) :-
        make_equalities(Xs,Ys,Equ).
