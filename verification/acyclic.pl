/**
 
<module> acyclic

This module provides functionality for reasoning with so-called
acyclic action theories, to be used for verification, as described in
the paper

Benjamin Zarrieß and Jens Claßen:
Decidable Verification of Golog Programs over Non-Local Effect Actions.
In Proceedings of the 13th AAAI Conference on Artificial Intelligence (AAAI 2016),
pages 1109-1115, AAAI Press, 2016.

@author  Jens Claßen
@license GPLv2

 **/
:- module('acyclic', [preprocess_actions/1,
                      bat_type/1,
                      effect_description/5,
                      determine_effects/4,
                      apply_effects/3,
                      simplify_fml/2,
                      regression/3,
                      is_entailed/2,
                      is_inconsistent/1]).

:- use_module('../lib/utils').

:- use_module('../logic/cwa').
:- use_module('../logic/l', [entails/2 as entails_l,
                             inconsistent/1 as inconsistent_l,
                             simplify/2 as simplify_l,
                             conjoin/2, conjuncts/2, free_variables/2,
                             op(1130, xfy, <=>),
                             op(1110, xfy, <=),
                             op(1110, xfy, =>)]).

:- use_module('../logic/dl', [entails/2 as entails_dl,
                             inconsistent/1 as inconsistent_dl,
                             simplify/2 as simplify_dl]).

:- use_module('../logic/fobdd', [minimize/2 as minimize_l]).

:- use_module('../projection/ligression').

:- use_module('../projection/progression').

:- use_module('characteristic_graphs_guards').

:- multifile user:base_logic/1.
:- multifile user:causes_true/3.
:- multifile user:causes_false/3.

% TODO: integrate CWA
% :- multifile user:causes_true/4.
% :- multifile user:causes_false/4.

:- discontiguous(is_entailed/3).
:- discontiguous(is_inconsistent/2).

:- dynamic
   bat_type/1,
   effect_description/5.

% Note: caching of is_entailed/2 etc. should not be done using
% unification, as this might create artifacts such as 'some(X,f(X,a))'
% unifying with 'some(Y,f(a,Y))', yielding 'some(a,f(a,a))'. Term
% variance (=@=/2) avoids this. Using Prolog's built-in tabling
% mechanism for this is considerably faster than a manual
% implementation.
:- table
   is_entailed/2,
   is_inconsistent/1,
   simplify_fml/2,
   minimize_fml/2,
   regression/3.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Preprocess Actions
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

preprocess_actions(Program) :-
        determine_eff_con(Program),
        check_bat_type.

determine_eff_con(Program) :- % untyped fluent, positive effect
        cg_edge(Program,_NodeID,_Guard,Action,_NewNodeID),
        action_template(Action,ActionT,Vars),
        causes_true(ActionT,Fluent,Condition),
        user:rel_fluent(Fluent),
        eff_con(Condition,Vars,Eff,Con),
        not(effect_description(+,Fluent,ActionT,Eff,Con)),
        assert(effect_description(+,Fluent,ActionT,Eff,Con)),
        fail.
determine_eff_con(Program) :- % typed fluent, positive effect
        cg_edge(Program,_NodeID,_Guard,Action,_NewNodeID),
        action_template(Action,ActionT,Vars),
        causes_true(ActionT,Fluent,Condition),
        user:rel_fluent(Fluent,Types),
        types_cons(Types,TyCons),
        eff_con(Condition,Vars,Eff,Con),
        conjoin([Eff|TyCons],Eff2),
        not(effect_description(+,Fluent,ActionT,Eff2,Con)),
        assert(effect_description(+,Fluent,ActionT,Eff2,Con)),
        fail.
determine_eff_con(Program) :- % untyped fluent, negative effect
        cg_edge(Program,_NodeID,_Guard,Action,_NewNodeID),
        action_template(Action,ActionT,Vars),
        causes_false(ActionT,Fluent,Condition),
        eff_con(Condition,Vars,Eff,Con),
        not(effect_description(-,Fluent,ActionT,Eff,Con)),
        assert(effect_description(-,Fluent,ActionT,Eff,Con)),
        fail.
determine_eff_con(Program) :- % typed fluent, negative effect
        cg_edge(Program,_NodeID,_Guard,Action,_NewNodeID),
        action_template(Action,ActionT,Vars),
        causes_false(ActionT,Fluent,Condition),
        user:rel_fluent(Fluent,Types),
        types_cons(Types,TyCons),
        eff_con(Condition,Vars,Eff,Con),
        conjoin([Eff|TyCons],Eff2),
        not(effect_description(+,Fluent,ActionT,Eff2,Con)),
        assert(effect_description(+,Fluent,ActionT,Eff2,Con)),
        fail.
determine_eff_con(_Program).

action_template(Action,ActionT,Vars) :-
        Action =.. [A|Args],
        generate_fresh_variables(Args,Vars),
        ActionT =.. [A|Vars], !.

generate_fresh_variables([_|Args],[_X|Vars]) :- !,
        generate_fresh_variables(Args,Vars).
generate_fresh_variables([],[]) :- !.

eff_con(Condition,Vars,Eff,Con) :- !,
        conjuncts(Condition,Conjuncts),
        eff_con2(Conjuncts,Vars,EffC,ConC),
        conjoin(EffC,Eff),
        conjoin(ConC,Con).
eff_con2([Conj|Conjuncts],Vars,EffC,[Conj|ConC]) :-
        free_variables(Conj,CVars),
        subset2(CVars,Vars), !,
        eff_con2(Conjuncts,Vars,EffC,ConC).
eff_con2([Conj|Conjuncts],Vars,[Conj|EffC],ConC) :- !,
        eff_con2(Conjuncts,Vars,EffC,ConC).
eff_con2([],_Vars,[],[]) :- !.

% TODO: bat_type should depend on program

check_bat_type :-
        not((effect_description(_,_,_,Eff,_),
             Eff \= true)), !,
        report_message_r(['Action theory is local-effect. Proceeding...']),
        assert(bat_type('local-effect')).
check_bat_type :-
        not(dg_cycle), !,
        report_message_r(['Action theory is acyclic. Proceeding...']),
        assert(bat_type(acyclic)).
check_bat_type :- !,
        report_message_r(err,
                         ['Action theory is NOT local-effect or acyclic! Aborting...']),
        fail.

dg_cycle :-
        dg_edge(F1,F2),
        dg_path(F2,F1).
dg_edge(F1,F2) :-
        effect_description(_S1,F1,_A1,Eff1,_C1),
        effect_description(_S2,F2,_A2,_Eff2,_C2),
        mentions_fluent(Eff1,[F2]), !.
dg_path(F1,F1).
dg_path(F1,F2) :-
        dg_edge(F1,F3),
        dg_path(F3,F2).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Regression
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

determine_effects(Formulas,Effects,Action,NewEffects) :-
        findall(Effect,is_effect(Formulas,Effects,Action,Effect),NewEffects).

is_effect(Formulas,Effects,Action,Effect) :-
        bat_type(acyclic),
        effect_description(Sign,Fluent,Action,Eff,Con),
        regression(Con,Effects,RCon),
        is_entailed(Formulas,RCon),
        Effect=(Sign,Fluent,Eff).

is_effect(Formulas,Effects,Action,Effect) :-
        bat_type('local-effect'),
        effect_description('+',Fluent,Action,_,Condition),
        regression(Condition,Effects,RegressedCondition),
        is_entailed(Formulas,RegressedCondition),
        Effect=Fluent.
is_effect(Formulas,Effects,Action,Effect) :-
        bat_type('local-effect'),
        effect_description('-',Fluent,Action,_,Condition),
        regression(Condition,Effects,RegressedCondition),
        is_entailed(Formulas,RegressedCondition),
        Effect=(-Fluent).

apply_effects(CurEffects,NewEffects,ResEffects) :- 
        bat_type(acyclic), !,
        findall(Effect,is_res_effect(CurEffects,NewEffects,Effect),
                ResEffects2),
        variant_sort(ResEffects2,ResEffects).
apply_effects(CurEffects,NewEffects,ResEffects) :- 
        bat_type('local-effect'), !,
        apply_neg_effects(CurEffects,NewEffects,NewEffects2),
        apply_pos_effects(NewEffects2,NewEffects,ResEffects2),
        sort(ResEffects2,ResEffects).

is_res_effect(CurEffects,NewEffects,Effect) :-
        member((Sign,Fluent,Eff),NewEffects),
        regression(Eff,CurEffects,REff),
        minimize_fml(REff,REffS),
        % simplify_fml(REff,REffS),
        REffS \= false,
        Effect = (Sign,Fluent,REffS).
is_res_effect(CurEffects,NewEffects,Effect) :-
        member((+,Fluent,Eff),CurEffects),
        neg_new_effects(Fluent,CurEffects,NewEffects,NegRPhiPs),
        conjoin([Eff|NegRPhiPs],REff),
        minimize_fml(REff,REffS),
        % simplify_fml(REff,REffS),
        REffS \= false,
        Effect = (+,Fluent,REffS).
is_res_effect(CurEffects,_NewEffects,Effect) :-
        member((-,Fluent,Eff),CurEffects),
        Effect = (-,Fluent,Eff).

neg_new_effects(Fluent,CurEffects,NewEffects,NegRPhiPs) :-
        % need bagof to avoid copying Fluent with new variables
        bagof(NegRPhiP,
              (member((-,Fluent,PhiP),NewEffects),
               regression(PhiP,CurEffects,RPhiP),
               NegRPhiP=(-RPhiP)),
              NegRPhiPs), !.
% bagof fails if there are no solutions
neg_new_effects(_,_,_,[]) :- !.

apply_neg_effects([-Eff|CurEffects],NewEffects,ResEffects) :-
        member(Eff,NewEffects), !,
        apply_neg_effects(CurEffects,NewEffects,ResEffects).
apply_neg_effects([-Eff|CurEffects],NewEffects,[-Eff|ResEffects]) :-
        apply_neg_effects(CurEffects,NewEffects,ResEffects).
apply_neg_effects([Eff|CurEffects],NewEffects,ResEffects) :-
        member(-Eff,NewEffects), !,
        apply_neg_effects(CurEffects,NewEffects,ResEffects).
apply_neg_effects([Eff|CurEffects],NewEffects,[Eff|ResEffects]) :-
        apply_neg_effects(CurEffects,NewEffects,ResEffects).
apply_neg_effects([],_NewEffects,[]).

apply_pos_effects([Eff|CurEffects],NewEffects,ResEffects) :-
        member(Eff,NewEffects), !,
        apply_pos_effects(CurEffects,NewEffects,ResEffects).
apply_pos_effects([Eff|CurEffects],NewEffects,[Eff|ResEffects]) :-
        apply_pos_effects(CurEffects,NewEffects,ResEffects).
apply_pos_effects([],NewEffects,NewEffects).

% regression: use "ligression" and simplify
regression(F,E,R) :- !,
        ligress(F,E,R1),
        simplify_fml(R1,R).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Formula Simplification
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% quick simplification
simplify_fml(F,R) :-
        user:base_logic(L), !,
        simplify_fml(L,F,R).
simplify_fml(F,R) :- !,
        simplify_fml(l,F,R).
simplify_fml(l,F,R) :- !,
        simplify_l(F,R).
simplify_fml(dl,F,R) :- !,
        simplify_dl(F,R).

% slower minimization to eliminate equivalent effect descriptors
minimize_fml(F,R) :-
        user:base_logic(L), !,
        minimize_fml(L,F,R).
minimize_fml(F,R) :- !,
        minimize_fml(l,F,R).
minimize_fml(l,F,R) :- !,
        minimize_l(F,R).
minimize_fml(dl,F,R) :- !,
        % TODO: need a corresponding minimize/2 for DLs for acyclic case
        simplify_dl(F,R).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Reasoning: Use L or DL
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

is_entailed(Formulas,Formula) :-
        user:base_logic(L), !,
        is_entailed(L,Formulas,Formula).
is_entailed(Formulas,Formula) :- !,
        is_entailed(l,Formulas,Formula). % default

is_inconsistent(Formulas) :-
        user:base_logic(L), !,
        is_inconsistent(L,Formulas).
is_inconsistent(Formulas) :- !,
        is_inconsistent(l,Formulas). % default

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% L reasoning
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

is_entailed(l,Formulas,Formula) :-
        entails_l(Formulas,Formula), !.

is_inconsistent(l,Formulas) :-
        inconsistent_l(Formulas), !.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% DL reasoning
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

is_entailed(dl,Formulas,Formula) :-
        entails_dl(Formulas,Formula), !.

is_inconsistent(dl,Formulas) :-
        inconsistent_dl(Formulas), !.
