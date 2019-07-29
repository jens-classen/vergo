%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Regression
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- module(regression, [regress/2,
                       regress/3,
                       isfluent/1,
                       isrigid/1]).

:- use_module('../lib/utils').
:- use_module('../reasoning/fol').
:- use_module('../reasoning/l').
:- use_module('../reasoning/una').

:- multifile user:prim_action/1.
:- multifile user:rel_fluent/1.
:- multifile user:fun_fluent/1.
:- multifile user:rel_rigid/1.
:- multifile user:fun_rigid/1.
:- multifile user:poss/1.
:- multifile user:causes_true/3.
:- multifile user:causes_false/3.
:- multifile user:ssa_inst/3.
:- multifile user:causes/4.
:- multifile user:def/2.
:- multifile user:exo/2.
:- multifile user:senses/2.
:- multifile user:senses/3.
:- multifile user:include_preconditions/0.
:- multifile user:sensing_style/1.

% poss if A is a variable => big disjunction over all cases
precond(A,Precondition) :- var(A), !, 
        condition(user:poss(B,Phi),Phi,B,A,Precondition).
% poss if A is instantiated => take predefined axiom
precond(A,Precondition) :- nonvar(A),
        user:poss(A,Precondition), !.
% poss otherwise: false
precond(_,false) :- !.

% exo if A is a variable => big disjunction over all cases
exocond(A,Exocondition) :- var(A), !, 
        condition(user:exo(B,Phi),Phi,B,A,Exocondition).
% exo if A is instantiated => take predefined axiom
exocond(A,Exocondition) :- nonvar(A),
        user:exo(A,Exocondition), !.
% exo otherwise: false
exocond(_,false) :- !.

% sf if A is a variable => big disjunction over all cases
sfcond(A,Sensecondition) :- var(A), sensing_style(truth), !, 
        condition(user:senses(B,Phi),Phi,B,A,Sensecondition).
% sf if A is instantiated => take predefined axiom
sfcond(A,Sensecondition) :- nonvar(A), sensing_style(truth),
        user:senses(A,Sensecondition), !.
% sf otherwise: false
sfcond(_,false) :- user:sensing_style(truth), !.

% sf if A is a variable => big disjunction over all cases
sfcond(A,Y,Sensecondition) :- var(A), user:sensing_style(object), !,
        condition(user:senses(B,Y,Phi),Phi,B,A,Cond),
        copy_term((Cond,Y,A),(CondC,Y,A)),
        subv(Y,X,CondC,CondD), % Y may not be a variable
        Condition2 = Cond+(-some(X,CondD)*(Y = '#ok')),
        simplify(Condition2,Sensecondition).
% sf if A is instantiated => take predefined axiom
sfcond(A,Y,Sensecondition) :- nonvar(A), user:sensing_style(object),
        user:senses(A,Y,Sensecondition).
% sf otherwise: '#ok'
sfcond(_,Y,(Y = '#ok')) :- user:sensing_style(object), !.

% ssa if exists pre-instantiated axiom by user => use it
ssa(Fluent,A,Condition) :- ssa_inst(Fluent,A,Condition), !.
% ssa if A is a variable => big disjunction over all cases
ssa(Fluent,A,Condition) :- user:rel_fluent(Fluent), var(A), !,
        condition(user:causes_true(B,Fluent,Phi),Phi,B,A,Poscondition),
        condition(user:causes_false(B,Fluent,Phi),Phi,B,A,Negcondition),
        Condition2 = Poscondition+Fluent*(-Negcondition),
        simplify(Condition2,Condition).
% ssa if A is instantiated => instantiate
ssa(Fluent,A,Condition) :- user:rel_fluent(Fluent), nonvar(A), !,
        ssa(Fluent,B,Condition3), B=A,
        apply_una(Condition3,Condition2),
        simplify(Condition2,Condition).
 
% ssa if exists pre-instantiated axiom by user => use it
ssa(Fluent=Y,A,Condition) :- ssa_inst(Fluent=Y,A,Condition), !.
% ssa if A is a variable => big disjunction over all cases
ssa(Fluent=Y,A,Condition) :- user:fun_fluent(Fluent), var(A), !,
        condition(user:causes(B,Fluent,Y,Phi),Phi,B,A,Cond),
        copy_term((Cond,Y,A),(CondC,Y,A)),
        subv(Y,X,CondC,CondD), % Y may not be a variable
        Condition2 = Cond+(Fluent=Y)*(-some(X,CondD)),
        simplify(Condition2,Condition).
% ssa if A is instantiated => instantiate
ssa(Fluent=Y,A,Condition) :- user:fun_fluent(Fluent), nonvar(A), !,
        ssa(Fluent=Y,B,Condition3), B=A,
        apply_una(Condition3,Condition2),
        simplify(Condition2,Condition).       

condition(Pattern,Phi,B,A,Condition) :- !,
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

construct_disjuncts([],[],_,_) :- !.
construct_disjuncts([E|D1],[Cond|D2],A,FreeVars) :-
        E = (FreeVars,[],((_C=B)*Phi)), !,
        Cond = ((A=B)*Phi),
        construct_disjuncts(D1,D2,A,FreeVars).
construct_disjuncts([E|D1],[Cond|D2],A,FreeVars) :-
        E = (FreeVars,Vars,((_C=B)*Phi)), !,
        Cond = some(Vars,((A=B)*Phi)),
        construct_disjuncts(D1,D2,A,FreeVars).

isfluent(F) :- 
        user:rel_fluent(F2),
        unifiable(F,F2,_). % don't unify (b/c of free vars)
isfluent((F=_)) :- 
        nonvar(F), 
        user:fun_fluent(F2),
        unifiable(F,F2,_). % don't unify (b/c of free vars)

isrigid(F) :- 
        user:rel_rigid(F2),
        unifiable(F,F2,_). % don't unify (b/c of free vars)
isrigid((F=_)) :- 
        nonvar(F), 
        user:fun_rigid(F2),
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
regress(S,after(A,Formula),Result) :-
        not(is_list(A)), !,
        regress([A|S],Formula,Result).
regress(S,after([],Formula),Result) :- !,
        regress(S,Formula,Result).
regress(S,after([A|As],Formula),Result) :- !,
        regress([A|S],after(As,Formula),Result).
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
        user:def(Formula,Definition), !, 
        regress(S,Definition,Result).

regress([],know(Formula),know(Result)) :- !,
        regress(Formula,Result).
regress([A|S],know(Formula),Result) :-
        user:sensing_style(truth), !,
        regress(S,
                (sf(A) * know(sf(A)=>after(A,Formula)))
                + (-sf(A) * know((-sf(A))=>after(A,Formula))),
                Result).
regress([A|S],know(Formula),Result) :-
        user:sensing_style(object), !,
        regress(S,
                some(X,(sf(A)=X)*know((sf(A)=X)=>after(A,Formula))),
                Result).

regress(_S,(X=Y),(X=Y)) :- !.
regress([],Fluent,Fluent) :- isfluent(Fluent), !.
regress(_,true,true) :- !.
regress(_,false,false) :- !.

regress(Fml,Res) :- !, regress([],Fml,Res).
