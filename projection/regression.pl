%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Regression
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- use_module('../lib/utils').
:- use_module('../reasoning/fol').

:- multifile prim_action/1.
:- multifile rel_fluent/1.
:- multifile fun_fluent/1.
:- multifile rel_rigid/1.
:- multifile fun_rigid/1.
:- multifile poss/1.
:- multifile causes_true/3.
:- multifile causes_false/3.
:- multifile ssa_inst/3.
:- multifile causes/4.
:- multifile def/2.
:- multifile exo/2.
:- multifile senses/2.
:- multifile senses/3.
:- multifile stdname/1.
:- multifile include_preconditions/0.
:- multifile sensing_style/1.

:- dynamic(stdname/1).

% poss if A is a variable => big disjunction over all cases
precond(A,Precondition) :- var(A), !, 
        condition(poss(B,Phi),Phi,B,A,Precondition).
% poss if A is instantiated => take predefined axiom
precond(A,Precondition) :- nonvar(A),
        poss(A,Precondition), !.
% poss otherwise: false
precond(_,false) :- !.
            
% exo if A is a variable => big disjunction over all cases
exocond(A,Exocondition) :- var(A), !, 
        condition(exo(B,Phi),Phi,B,A,Exocondition).
% exo if A is instantiated => take predefined axiom
exocond(A,Exocondition) :- nonvar(A),
        exo(A,Exocondition), !.
% exo otherwise: false
exocond(_,false) :- !.

% sf if A is a variable => big disjunction over all cases
sfcond(A,Sensecondition) :- var(A), sensing_style(truth), !, 
        condition(senses(B,Phi),Phi,B,A,Sensecondition).
% sf if A is instantiated => take predefined axiom
sfcond(A,Sensecondition) :- nonvar(A), sensing_style(truth),
        senses(A,Sensecondition), !.
% sf otherwise: true
sfcond(_,true) :- sensing_style(truth), !.

% sf if A is a variable => big disjunction over all cases
sfcond(A,Y,Sensecondition) :- var(A), sensing_style(object), !,
        condition(senses(B,Y,Phi),Phi,B,A,Cond),
        copy_term((Cond,Y,A),(CondC,Y,A)),
        subv(Y,X,CondC,CondD), % Y may not be a variable
        Condition2 = Cond+(-some(X,CondD)*(Y=ok)),
        simplify(Condition2,Sensecondition).
% sf if A is instantiated => take predefined axiom
sfcond(A,Y,Sensecondition) :- nonvar(A), sensing_style(object),
        senses(A,Y,Sensecondition).
% sf otherwise: "ok"
sfcond(_,Y,(Y=ok)) :- sensing_style(object), !.
% ok is a standard name
stdname(ok).

% ssa if exists pre-instantiated axiom by user => use it
ssa(Fluent,A,Condition) :- ssa_inst(Fluent,A,Condition), !.
% ssa if A is a variable => big disjunction over all cases
ssa(Fluent,A,Condition) :- rel_fluent(Fluent), var(A), !,
        condition(causes_true(B,Fluent,Phi),Phi,B,A,Poscondition),
        condition(causes_false(B,Fluent,Phi),Phi,B,A,Negcondition),
        Condition2 = Poscondition+Fluent*(-Negcondition),
        simplify(Condition2,Condition).
% ssa if A is instantiated => instantiate
ssa(Fluent,A,Condition) :- rel_fluent(Fluent), nonvar(A), !,
        ssa(Fluent,B,Condition3), B=A,
        apply_una(Condition3,Condition2),
        simplify(Condition2,Condition).
 
% ssa if exists pre-instantiated axiom by user => use it
ssa(Fluent=Y,A,Condition) :- ssa_inst(Fluent=Y,A,Condition), !.
% ssa if A is a variable => big disjunction over all cases
ssa(Fluent=Y,A,Condition) :- fun_fluent(Fluent), var(A), !,
        condition(causes(B,Fluent,Y,Phi),Phi,B,A,Cond),
        copy_term((Cond,Y,A),(CondC,Y,A)),
        subv(Y,X,CondC,CondD), % Y may not be a variable
        Condition2 = Cond+(Fluent=Y)*(-some(X,CondD)),
        simplify(Condition2,Condition).
% ssa if A is instantiated => instantiate
ssa(Fluent=Y,A,Condition) :- fun_fluent(Fluent), nonvar(A), !,
        ssa(Fluent=Y,B,Condition3), B=A,
        apply_una(Condition3,Condition2),
        simplify(Condition2,Condition).       

condition(Pattern,Phi,B,A,Condition) :-
        % free variables in Pattern (except Phi and B)
        term_variables(Pattern,FreeVars2),
        setminus2(FreeVars2,[B,Phi],FreeVars),
        % findall instances of Pattern
        findall((FreeVars,Vars,((_C=B)*Phi)),
                (Pattern, 
                 free_variables((B=B)*Phi,Vars2),
                 setminus2(Vars2,FreeVars,Vars)),
                Conds),
        % build a formula with quantifiers over conditions
        construct_disjuncts(Conds,Conditions,A,FreeVars),
        disjoin(Conditions,Condition2),
        simplify(Condition2,Condition).

construct_disjuncts([],[],_,_).
construct_disjuncts([E|D1],[Cond|D2],A,FreeVars) :-
        E = (FreeVars,[],((_C=B)*Phi)), !,
        Cond = ((A=B)*Phi),
        construct_disjuncts(D1,D2,A,FreeVars).
construct_disjuncts([E|D1],[Cond|D2],A,FreeVars) :-
        E = (FreeVars,Vars,((_C=B)*Phi)), !,
        Cond = some(Vars,((A=B)*Phi)),
        construct_disjuncts(D1,D2,A,FreeVars).

isfluent(F) :- 
        rel_fluent(F2), 
        unifiable(F,F2,_). % don't unify (b/c of free vars)
isfluent((F=_)) :- 
        nonvar(F), 
        fun_fluent(F2),
        unifiable(F,F2,_). % don't unify (b/c of free vars)

isrigid(F) :- 
        rel_rigid(F2),
        unifiable(F,F2,_). % don't unify (b/c of free vars)
isrigid((F=_)) :- 
        nonvar(F), 
        fun_rigid(F2),
        unifiable(F,F2,_). % don't unify (b/c of free vars)

regress(S,poss(A),Result) :- 
        precond(A,Precondition), !, 
        regress(S,Precondition,Result).
regress(S,exo(A),Result) :- 
        exocond(A,ExoCondition), !, 
        regress(S,ExoCondition,Result).
regress(S,sf(A),Result) :- 
        sfcond(A,Sensecondition), !, 
        regress(S,Sensecondition,Result).
regress(S,SFA=Y,Result) :- 
        nonvar(SFA),
        SFA=sf(A),
        sfcond(A,Y,Sensecondition), !, 
        regress(S,Sensecondition,Result).
regress([A|S],Fluent,Result) :- 
        isfluent(Fluent), 
        ssa(Fluent,A,Formula), !, 
        regress(S,Formula,Result).
regress(_S,Rigid,Rigid) :- 
        isrigid(Rigid), !.
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
regress(S,all(Vars,Formula),Result) :- !,
        regress(S,Formula,Result1),
        Result=all(Vars,Result1).
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

regress([],know(Formula),know(Result)) :- !,
        regress(Formula,Result).
regress([A|S],know(Formula),Result) :-
        sensing_style(truth), !,
        regress(S,
                (sf(A) * know(sf(A)=>after(A,Formula)))
                + (-sf(A) * know((-sf(A))=>after(A,Formula))),
                Result).
regress([A|S],know(Formula),Result) :-
        sensing_style(object), !,
        regress(S,
                some(X,(sf(A)=X)*know((sf(A)=X)=>after(A,Formula))),
                Result).

regress(_S,(X=Y),(X=Y)) :- !.
regress([],Fluent,Fluent) :- isfluent(Fluent), !.
regress(_,true,true) :- !.
regress(_,false,false) :- !.

regress(Fml,Res) :- !, regress([],Fml,Res).

apply_una(true,true) :- !.
apply_una(false,false) :- !.
apply_una(poss(A),poss(A)) :- !.
apply_una(exo(A),exo(A)) :- !.
apply_una(sf(A),sf(A)) :- !.
apply_una(F,F) :- isfluent(F), !.
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
% ?[A]:(?[X]:(A=f(X))&F) --> ?[X]:F with A replaced by f(X)
apply_una(some([A],F1),some(Vars,F4)) :- % (*)
        action_equality_conjunct(A,Act,F1,F2,Vars), !,
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
        prim_action(X);
        stdname(X).

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
action_equality_conjunct(A,Act,some(Vars,F),F,Vars) :- !,
        action_equality_conjunct(A,Act,F,F,[]).
action_equality_conjunct(X,Y,Fml1*Fml2,Fml1P*Fml2,Vars) :-
        action_equality_conjunct(X,Y,Fml1,Fml1P,Vars), !.
action_equality_conjunct(X,Y,Fml1*Fml2,Fml1*Fml2P,Vars) :-
        action_equality_conjunct(X,Y,Fml2,Fml2P,Vars), !.
