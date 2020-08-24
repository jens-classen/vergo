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

:- use_module('../../verification/abstraction_local-effect').
:- use_module('../../lib/utils').

:- discontiguous causes_true/3.
:- discontiguous causes_false/3.

base_logic(dl).

initially(subsumedBy(some(dirtyDish,thing),nothing)).
initially(subsumedBy(onRobot,nothing)).

rel_fluent(dirtyDish(_,_)).
rel_fluent(onRobot(_)).

poss(requestDDR(X,_),
     -concept_assertion(some(dirtyDish,thing),X) *
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

% only one dish and two rooms for testing, otherwise too slow
domain(dish,'#d1').
domain(room,'#r1').
domain(room,'#r2').

program(control,
        loop([while(concept_assertion(some(universal,onRobot),'#d1'),
                    % "something on robot"
                    pick(X,dish,unload(X))),
              pick(Y,room,[gotoRoom(Y),
                           while(concept_assertion(some(universal,
                                                        some(dirtyDish,
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
         somepath(until(-concept_assertion(some(dirtyDish,thing),'#d1'),
                        concept_assertion(some(dirtyDish,thing),'#d1')))).
property(prop5,
         main,
         allpaths(eventually(concept_assertion(some(universal,
                                                    some(dirtyDish,
                                                         thing)),
                                               '#dummy')))).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Testing
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

expected_outcome(prop1,false).
expected_outcome(prop2,true).
expected_outcome(prop3,false).
expected_outcome(prop4,true).
expected_outcome(prop5,false).

:- begin_tests('abstraction_local-effect_dl').

test(abstraction) :- !,
        compute_abstraction(main),
        check_prop(prop1),
        check_prop(prop2),
        check_prop(prop3),
        check_prop(prop4),
        check_prop(prop5).

check_prop(P) :-
        verify(P,T),
        check_result(P,T), !.

check_result(P,T) :-
        assertion(expected_outcome(P,T)),
        check_result2(P,T).
check_result2(P,T) :-
        expected_outcome(P,T), !,
        report_message(info,['Outcome for ',P,' is as expected!']).
check_result2(P,_T) :- !,
        report_message(info,['Outcome for ',P,
                             ' is different from what expected!']).

:- end_tests('abstraction_local-effect_dl').
