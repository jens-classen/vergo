/**

Dish Robot using Description Logics

This domain is a variant of the dish robot that uses description
logics as base logic. Its purpose is for testing verification by
abstraction based on description logics. Everything here should work
exactly the same as in the standard encoding using logic L, i.e. the
two specifications are equivalent.

@author  Jens Claßen
@license GPLv2

**/

:- use_module('../../verification/abstraction_acyclic').
:- use_module('../../lib/utils').

:- discontiguous causes_true/3.
:- discontiguous causes_false/3.

:- dynamic(initially/1).
:- dynamic(domain/2).

base_logic(dl).

use_sink_states.

initially(subsumedBy(exists(dirtyDish,thing),nothing)).
initially(subsumedBy(onRobot,nothing)).

rel_fluent(dirtyDish(_,_)).
rel_fluent(onRobot(_)).

poss(requestDDR(X,_),
     -concept_assertion(exists(dirtyDish,thing),X) *
     -concept_assertion(onRobot,X)).
poss(load(X,Y),
     role_assertion(dirtyDish,X,Y)).
poss(unload(X),
     concept_assertion(onRobot,X)).
poss(gotoRoom(_),
     true).
poss(gotoKitchen,
     true).

causes_true(requestDDR(X,Y),dirtyDish(X,Y),true).
causes_false(load(X,Y),dirtyDish(X,Y),true).

causes_true(load(X,_Y),onRobot(X),true).
causes_false(unload(X),onRobot(X),true).

type(dish).
type(room).

domain(dish,'#d1').
domain(dish,'#d2').
domain(room,'#r1').
domain(room,'#r2').

program(control,
        loop([while(concept_assertion(exists(universal,onRobot),'#d1'),
                    % "something on robot"
                    pick(X,dish,unload(X))),
              pick(Y,room,[gotoRoom(Y),
                           while(concept_assertion(exists(universal,
                                                        exists(dirtyDish,
                                                               oneof([Y]))),
                                                   '#d1'),
                                 % "some dirty dish in Y"
                                 pick(X,dish,load(X,Y)))
                          ]
                  ),
              gotoKitchen
             ]
            )
       ).

program(exog,
        loop(pick(X,dish,
                  pick(Y,room,
                       requestDDR(X,Y)))
            )
       ).

program(main,
        conc(control,exog)).

property(prop1,
         main,
         somepath(always(role_assertion(dirtyDish,'#d1','#r1')))).
property(prop2,
         main,
         allpaths(eventually(-role_assertion(dirtyDish,'#d1','#r1')))).
property(prop3,
         main,
         allpaths(eventually(role_assertion(dirtyDish,'#d1','#r1')))).
property(prop4,
         main,
         somepath(until(-concept_assertion(exists(dirtyDish,thing),'#d1'),
                        concept_assertion(exists(dirtyDish,thing),'#d1')))).
property(prop5,
         main,
         allpaths(eventually(concept_assertion(exists(universal,
                                                    exists(dirtyDish,
                                                         thing)),
                                               '#dummy')))).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Testing
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Properties when initial KB is included
expected_outcome(prop1,yes,false).
expected_outcome(prop2,yes,true).
expected_outcome(prop3,yes,false).
expected_outcome(prop4,yes,true).
expected_outcome(prop5,yes,false).

% Properties when initial KB is not included
expected_outcome(prop1,no,false).
expected_outcome(prop2,no,false). % d1 might be dirty initially
expected_outcome(prop3,no,false).
expected_outcome(prop4,no,true).
expected_outcome(prop5,no,false).

:- begin_tests('abstraction_local-effect_dl').

test(abstraction_with_initial_kb) :- !,
        retract(user:domain(dish,'#d2')), % to make test not
        retract(user:domain(room,'#r2')), % too long
        compute_abstraction(main),
        check_prop(prop1,yes),
        check_prop(prop2,yes),
        check_prop(prop3,yes),
        check_prop(prop4,yes),
        check_prop(prop5,yes).

test(abstraction_without_initial_kb) :- !,
        retractall(user:initially(_)),
        compute_abstraction(main),
        check_prop(prop1,no),
        check_prop(prop2,no),
        check_prop(prop3,no),
        check_prop(prop4,no),
        check_prop(prop5,no).

:- end_tests('abstraction_local-effect_dl').

check_prop(P,I) :-
        verify(P,T),
        check_result(P,I,T), !.

check_result(P,I,T) :-
        assertion(expected_outcome(P,I,T)),
        check_result2(P,I,T).
check_result2(P,I,T) :-
        expected_outcome(P,I,T), !,
        report_message(info,['Outcome for ',P,' is as expected!']).
check_result2(P,_I,_T) :- !,
        report_message(info,['Outcome for ',P,
                             ' is different from what expected!']).
