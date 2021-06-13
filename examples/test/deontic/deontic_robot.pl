/**
 
Example Scenario for Compiling Deontic Constraints into Planning Problem

This file uses an approach for expressing deontic constraints by
means of conditionals over program expressions that induce a ranking
over the set of available actions, as described in

Jens Claßen and James Delgrande: "Dyadic Obligations over Complex
Actions as Deontic Constraints in the Situation Calculus", in
Proceedings of KR 2020, AAAI Press.

The ranking induced by the constraints is then represented as action
costs, to be used by a PDDL planner. Since so far no PDDL planner
supports state-dependent action costs out of the box, a re-compilation
step is used that splits up actions accordingly.

This approach is still work in progress.

@author  Jens Claßen
@license GPLv2

 **/


:- use_module('../../../agents/kbagent').
:- use_module('../../../golog/deontic_constraints').
:- use_module('../../../lib/utils').
:- use_module('../../../planning/pddl_parser').
:- use_module('../../../planning/pddl_planner').

:- initialization(parse_pddl_domain(file('deontic_robot.pddl'),userdb,_)).

domain(aspect,X) :- member(X,['#quietly','#nonquietly']).
domain(room,X) :- member(X,['#office','#supplies','#closet']).
domain(door,X) :- member(X,['#door_a','#door_b']).
domain(physob,X) :- member(X,['#box_1','#box_2']).

initially(in('#office','#robot')).
initially(in('#supplies','#box_1')).
initially(in('#closet','#box_2')).

initially(connects('#door_a','#office','#supplies')).
initially(connects('#door_a','#supplies','#office')).
initially(connects('#door_b','#supplies','#closet')).
initially(connects('#door_b','#closet','#supplies')).

% Forrester
drule(pick(X,pick(Y,open(X,Y))) ~> pick(X,open(X,'#quietly'))).
drule(pick(X,pick(Y,close(X,Y))) ~> pick(X,close(X,'#quietly'))).

% % Chisholm
% drule(pick(R1,pick(R2,go_through('#door_a',R1,R2))) '~a>' pick(X,close('#door_a',X))).
% drule(pick(R1,pick(R2,go_through('#door_b',R1,R2))) '~a>' pick(X,close('#door_b',X))).

% drule(pick(R1,pick(R2,pick(O,push_through(O,'#door_a',R1,R2)))) '~a>' pick(X,close('#door_a',X))).
% drule(pick(R1,pick(R2,pick(O,push_through(O,'#door_b',R1,R2)))) '~a>' pick(X,close('#door_b',X))).

goal(g1,in('#office','#box_2')).

run1 :-
        get_plan(userdb,g1,Plan),
        write(Plan).

run2 :-
        findall(Rule,drule(Rule),Rules),
        construct_ranking(Rules,userdb),
        create_action_costs(userdb),
        get_plan(userdb,g1,deontic,Plan),
        write(Plan).

print_bat :-
        listing(type(_)),
        listing(subtype(_,_)),
        listing(rel_fluent(_,_)),
        listing(fun_fluent(_,_,_)),
        listing(cwa(_)),
        listing(poss(_,_)),
        listing(poss(_,_,_)),
        listing(causes_true(_,_,_)),
        listing(causes_false(_,_,_)),
        listing(causes(_,_,_,_)).
