/**

<module> Planner

This module implements a simple progression-based planner for Golog.

It uses the iterative-deepening version of the well-known A* algorithm
with a heuristic function that is a simplified variant of the "ignore
delete lists" relaxation. More specifically, in the computation of the
heuristic value it is assumed that all actions can be executed
simultaneously.

Planning is possible for all action theories for which progression is
supported, however the heuristic function only takes positive effects
for typed fluents subject to the closed-world assumption (CWA) into
consideration. This means that planning will work best for action
theories that can be mapped to PDDL's ADL fragment.

So far, action costs and metrics are not supported.

@author  Jens Claßen
@license GPLv2

**/
:- module(planner, [get_plan/3, get_plan/4]).

:- use_module('../kbs/l_kb').
:- use_module('../lib/env').
:- use_module('../lib/utils').
:- use_module('../logic/cwa').
:- use_module('../projection/progression').

:- multifile user:goal/2.
:- multifile user:def/2.
:- multifile user:metric/2.
:- multifile user:type/1.
:- multifile user:subtype/2.
:- multifile user:domain/2.
:- multifile user:cwa/1.
:- multifile user:rel_fluent/2.
:- multifile user:fun_fluent/3.
:- multifile user:rel_rigid/2.
:- multifile user:fun_rigid/3.
:- multifile user:causes_true/3.
:- multifile user:causes_false/3.
:- multifile user:causes/4.

:- dynamic estimate_cached/3.
:- dynamic h_value_cached/3.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Main Method
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

/**
  * get_plan(++KB,+Goal,-Plan) is det.
  *
  * This predicate calls the planner on the given KB as initial state
  * with the given goal, and will return an action sequence as plan,
  * if one exists.
  *
  * @arg KB   the identifier (handle) of the KB containing facts to
  *           be used for the initial state; use 'userdb' to work on
  *           facts given by user:initially/1
  * @arg Goal a goal, either in the form of a formula, or the name of
  *           a goal formula defined through goal/2 or def/2
  * @arg Plan a sequence (list) of actions representing a solution
  *           plan, or 'fail'
  */
get_plan(KB,Goal,Plan) :-
        get_plan(KB,Goal,none,Plan).

/**
  * get_plan(++KB,+Goal,+Metric,-Plan) is det.
  *
  * Similar as get_plan/2, but additionally uses a plan metric.
  *
  * @tbd todo: so far the metric is ignored
  *
  * @arg KB     the identifier (handle) of the KB containing facts to
  *             be used for the initial state; use 'userdb' to work on
  *             facts given by user:initially/1
  * @arg Goal   a goal, either in the form of a formula, or the name
  *             of a goal formula defined through goal/2 or def/2
  * @arg Metric a metric, either in the form of a term minimize(Exp)
  *             or maximize(Exp), or the name of a metric defined
  *             through metric/2, or 'none'
  * @arg Plan   a sequence (list) of actions representing a solution
  *             plan, or 'fail'
  */
get_plan(KB,Goal,Metric,Plan) :-
        goal_fml(Goal,GoalF),
        metric_def(Metric,MetricF),
        copy_kb(KB,[]),
        retractall(h_value_cached(_,_,_)),
        retractall(estimate_cached(_,_,_)),
        idastar(0,[],GoalF,MetricF,Solution),
        reverse(Solution,Plan).
get_plan(_KB,_Goal,_Metric,fail).

% goal is a defined goal, defined formula, or given directly
goal_fml(Goal,GoalF) :-
        user:goal(Goal,GoalF), !.
goal_fml(Goal,GoalF) :-
        user:def(Goal,GoalF), !.
goal_fml(Goal,Goal) :- !.

% metric is a defined metric or given directly
metric_def(Name,MetricF) :-
        user:metric(Name,MetricF), !.
metric_def(MetricF,MetricF) :- !.

% iterative deepening A*
idastar(Limit,Init,Goal,_Metric,Plan) :-
        report_message(info,['IDA* iteration with f limit ',Limit]),
        expand(0,Init,Goal,Limit,Plan).
idastar(Limit,Init,Goal,Metric,Plan) :-
        Limit2 is Limit+1,
        idastar(Limit2,Init,Goal,Metric,Plan).

% expand a node
expand(G,Path,Goal,Limit,Solution) :-
        % compute F value
        h_value(Path,Goal,H),
        G+H =< Limit,
        expand2(G,Path,Goal,Limit,Solution).
expand2(_G,Path,Goal,_Limit,Solution) :-
        % goal found
        entails_kb(Path,Goal,true),
        Solution = Path.
expand2(G,Path,Goal,Limit,Solution) :-
        % expand by one action
        poss(Action,Args,Precondition),
        is_instance(Args,Action),
        entails_kb(Path,Precondition,true),
        progress(Path,Action,[Action|Path]),
        Cost = 1,
        expand(G+Cost,[Action|Path],Goal,Limit,Solution).

% heuristic value by relaxation
h_value(Path,Goal,H) :- !,
        findall(F,(kb_axiom(Path,F),rel_fluent(F,_)),State),
        estimate(State,Goal,H),
        report_message(debug,['Path: ',Path]),
        report_message(debug,['Goal: ',Goal]),
        report_message(debug,['H   : ',H]),
        assert(h_value_cached(Path,Goal,H)).

% note: don't cache h_value or estimate, too expensive

% relaxation: in every step, add all positive effects for all actions
% to the relaxed state; count number of steps it takes to satisfy the
% (positive part of the) goal formula
estimate(State,Goal,0) :-
        est_sat(State,Goal), !,
        assert(estimate_cached(State,Goal,0)).
estimate(State,Goal,I+1) :-
        findall(F,(causes_true(A,F,Cond),
                   poss(A,Args,Pre),
                   is_instance(Args,A),
                   est_sat(State,Pre*Cond)),
                Adds),
        union2(State,Adds,State2),
        sort(State2,State3),
        State \= State3, !,
        estimate(State3,Goal,I),
        assert(estimate_cached(State,Goal,I+1)).

% check whether relaxed state satisfies the positive parts of a
% formula (ignoring negated parts and universal quantification)
est_sat(_State,true) :- !.
est_sat(State,F) :-
       rel_fluent(F,_),
       member(F,State).
est_sat(_State,-F) :-
       rel_fluent(F,_).
est_sat(State,F1*F2) :-
        est_sat(State,F1),
        est_sat(State,F2).
est_sat(State,F1+F2) :-
        est_sat(State,F1);
        est_sat(State,F2).
est_sat(State,F1=>F2) :-
        est_sat(State,(-F1)+F2).
est_sat(State,F1<=F2) :-
        est_sat(State,F1+(-F2)).
est_sat(State,F1<=>F2) :-
        est_sat(State,(F1=>F2)*(F2=>F1)).
est_sat(State,some_t(_,F)) :-
        est_sat(State,F).
est_sat(_State,all_t(_,_F)).
est_sat(State,-(F1*F2)) :-
        est_sat(State,(-F1)+(-F2)).
est_sat(State,-(F1+F2)) :-
        est_sat(State,(-F1)*(-F2)).
est_sat(_State,-some_t(_,_F)).
est_sat(State,-all_t(_,F)) :-
        est_sat(State,-F).
