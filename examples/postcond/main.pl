
:- dynamic(ssa_inst/3).
:- dynamic(stdname/1).
:- dynamic(domain/2).
:- dynamic(program/2).
:- dynamic(property/3).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Reasoner
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- use_module('../../logic/fol').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Program Semantics
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- ['../../transfinal/transfinal_guards'].

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Projection
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- use_module('../../projection/regression').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Verification Algorithm
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- ['../../verification/fixpoint_ctl'].

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Translation
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- use_module('../../lib/utils').

:- op(1130, xfy, <=>). % equivalence
:- op(1110, xfy, =>).  % implication
:- op(1110, xfy, <=).  % implication
:- op( 500, fy, -).    % negation
:- op( 500,xfy, :).

:- op(1100, xfy, v).  % disjunction
:- op(1000, xfy, &).    % conjunction
:- op( 500, fy, !).     % universal quantifier
:- op( 500, fy, ?).     % existential quantifier
:- op( 400, xfx, ~).    % equality
:- op( 599, xfy, #).

initall. % do nothing
 
preprocess :- !,
        
        % rel_fluent
        findall(rel_fluent(Fluent),
                (predList(PredList),
                 member(P,PredList),
                 type_info(P,Types),
                 length(Types,N),
                 anonymous_list(N,Args),
                 Fluent =.. [P|Args]),
                RelFluents),
        assert_list(RelFluents),
        
        % types = rigids
        findall(rel_rigid(Rigid),
                (tdomain(Dom, _),
                 Rigid =.. [Dom, _]),
                RelRigids),
        assert_list(RelRigids),
        
        % preds w/o perform clause = rigids
        findall(rel_rigid(Rigid),
                (pred(RigidP),
                 not(perform(RigidP,_) <=> _),
                 RigidP =.. [P|Args],
                 length(Args,N),
                 anonymous_list(N,Ano),
                 Rigid =.. [P|Ano]),               
                RelRigids2),
        assert_list(RelRigids2),
        
        % preconditions
        findall(poss(Action,Condition),
                ((poss(Action) <=> TCondition),
                 translate_fml(TCondition,Condition)),
                PreConditions),
        assert_list(PreConditions),

        % SSA for rel_fluents
        findall(ssa_inst(Fluent,Action,Condition),
                ((perform(Fluent,Action) <=> TCondition),
                 translate_fml(TCondition,Condition)),
                SSAs),
        assert_list(SSAs),
        
        % SSA for types
        findall(ssa_inst(Fluent,_,Fluent),
                (tdomain(Dom, _),
                 Fluent =.. [Dom, _]),
                SSAs2),
        assert_list(SSAs2),
        
        % SSAs for other fluents
        findall(ssa_inst(Fluent,Action,Fluent),
                (rel_fluent(Fluent),
                 prim_action(Action),
                 not(perform(Fluent,Action) <=> _)),
                SSAs3),
        assert_list(SSAs3),
        
        % standard names (?)
        findall(stdname(X),
                (tdomain(_Dom,List),
                 member(X,List)),
                StandardNames),
        assert_list(StandardNames),
        
        % domains/types
        findall(domain(Dom,Elm),
                (tdomain(Dom, List),
                 member(Elm,List)),
                Domains),
        assert_list(Domains),
        
        % initial theories
        % todo: CWA!!!
        findall(initially(Fml),
                (init_states([State]),
                 member(Fml,State)),
                Inits),
        assert_list(Inits).

assert_list([Fact|Facts]) :-
        assert(Fact),
        assert_list(Facts).
assert_list([]).

anonymous_list(0,[]).
anonymous_list(N,[_|L]) :-
        N > 0, !,
        N1 is N-1,
        anonymous_list(N1,L).

gove(Precond,Program,Postcond) :-
        retractall(program(_,_)),
        retractall(property(_,_,_)),
        translate_program(Program,TProgram),
        translate_fml(Precond,TPrecond),
        translate_fml(Postcond,TPostcond),
        assert(program(program,[test(TPrecond),TProgram])),
        assert(property(property,program,unipostcond(TPostcond))),
        construct_characteristic_graph(program),
        verify(program,property).

translate_fml(all([[CVar,Dom]|VarDoms],Fml),all(Var,DomExp => TSFml)) :- !,
        DomExp =.. [Dom, Var],
        translate_fml(all(VarDoms,Fml),TFml),
        duplicate_term((_X,TFml),(Y,_TTFml)), % fresh variable
        subv(CVar,Y,TFml,TSFml),
        Var = Y.
translate_fml(all([],Fml),TFml) :- !,
        translate_fml(Fml,TFml).
translate_fml(some([[CVar,Dom]|VarDoms],Fml),some(Var,DomExp*TSFml)) :- !,
        DomExp =.. [Dom, Var],
        translate_fml(all(VarDoms,Fml),TFml),
        duplicate_term((_X,TFml),(Y,_TTFml)), % fresh variable
        subv(CVar,Y,TFml,TSFml),
        Var = Y.
translate_fml(some([],Fml),TFml) :- !,
        translate_fml(Fml,TFml).
translate_fml(Fml1&Fml2,Fml3*Fml4) :- !,
        translate_fml(Fml1,Fml3),
        translate_fml(Fml2,Fml4).
translate_fml(Fml1 v Fml2,Fml3+Fml4) :- !,
        translate_fml(Fml1,Fml3),
        translate_fml(Fml2,Fml4).
translate_fml(-Fml1,-Fml2) :- !,
        translate_fml(Fml1,Fml2).
translate_fml((X ~ Y),(X=Y)) :- !.
translate_fml(F,F) :- !.

translate_program(while(Cond,Prog),while(TCond,TProg)) :- !,
        translate_fml(Cond,TCond),
        translate_program(Prog,TProg).
translate_program(P1#P2,nondet(TP1,TP2)) :- !,
        translate_program(P1,TP1),
        translate_program(P2,TP2).
translate_program(P1:P2,[TP1,TP2]) :- !,
        translate_program(P1,TP1),
        translate_program(P2,TP2).
translate_program(pi([[CVar,Dom]|VarDoms],Prog),pick(Var,Dom,TSProg)) :- !,
        translate_program(pi(VarDoms,Prog),TProg),
        duplicate_term((_X,TProg),(Y,_TTProg)), % fresh_variable
        subv(CVar,Y,TProg,TSProg),
        Var = Y.
translate_program(pi([],Prog),TProg) :- !,
        translate_program(Prog,TProg).
translate_program(?(Fml),test(TFml))  :- !,
        translate_fml(Fml,TFml).
translate_program(P,P) :- !.

include_preconditions.
