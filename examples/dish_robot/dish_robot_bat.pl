:- use_module('../../verification/abstraction_local-effect',
              [compute_abstraction/1 as compute_abstraction_le,
               verify/2 as verify_le]).
:- use_module('../../verification/abstraction_acyclic',
              [compute_abstraction/1 as compute_abstraction_ac,
               verify/2 as verify_ac]).
:- use_module('../../lib/utils').

:- discontiguous causes_true/3.
:- discontiguous causes_false/3.

:- dynamic(initially/1).
:- dynamic(domain/2).

use_sink_states.

initially(- some([X,Y],dirtyDish(X,Y))).
initially(- some(X,onRobot(X))).

rel_fluent(dirtyDish(_,_)).
rel_fluent(onRobot(_)).

poss(requestDDR(X,_),
     (- some(Y,dirtyDish(X,Y)) * - onRobot(X))).
poss(load(X,Y),
     dirtyDish(X,Y)).
poss(unload(X),
     onRobot(X)).
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
        loop([while(some(X,onRobot(X)),
                     pick(X,dish,unload(X))),
              pick(Y,room,[gotoRoom(Y),
                           while(some(X,dirtyDish(X,Y)),
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
         somepath(always(dirtyDish('#d1','#r1')))).
property(prop2,
         main,
         allpaths(eventually(-dirtyDish('#d1','#r1')))).
property(prop3,
         main,
         allpaths(eventually(dirtyDish('#d1','#r1')))).
property(prop4,
         main,
         somepath(until(-some(X,dirtyDish('#d1',X)),some(X,dirtyDish('#d1',X))))).
property(prop5,
         main,
         allpaths(eventually(some([X,Y],dirtyDish(X,Y))))).
% not yet supported!
% property(prop6,
%         main,
%         some([X,Y],somepath(always(dirtyDish(X,Y))))).

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

:- begin_tests('abstraction_local-effect').

test(abstraction_with_initial_kb) :- !,
        set_initial_kb(true),
        set_domains(2),
        compute_abstraction_le(main),
        check_prop(prop1,yes,le),
        check_prop(prop2,yes,le),
        check_prop(prop3,yes,le),
        check_prop(prop4,yes,le),
        check_prop(prop5,yes,le).

test(abstraction_without_initial_kb) :- !,
        set_initial_kb(false),
        set_domains(1),
        compute_abstraction_le(main),
        check_prop(prop1,no,le),
        check_prop(prop2,no,le),
        check_prop(prop3,no,le),
        check_prop(prop4,no,le),
        check_prop(prop5,no,le).

:- end_tests('abstraction_local-effect').

:- begin_tests('abstraction_acyclic').

test(abstraction_with_initial_kb) :- !,
        set_initial_kb(true),
        set_domains(2),
        compute_abstraction_ac(main),
        check_prop(prop1,yes,ac),
        check_prop(prop2,yes,ac),
        check_prop(prop3,yes,ac),
        check_prop(prop4,yes,ac),
        check_prop(prop5,yes,ac).

test(abstraction_without_initial_kb) :- !,
        set_initial_kb(false),
        set_domains(1),
        compute_abstraction_ac(main),
        check_prop(prop1,no,ac),
        check_prop(prop2,no,ac),
        check_prop(prop3,no,ac),
        check_prop(prop4,no,ac),
        check_prop(prop5,no,ac).

:- end_tests('abstraction_acyclic').

set_initial_kb(WithKB) :-
        retractall(user:initially(_)),
        (WithKB=true ->
            (assert(user:initially(- some([X,Y],dirtyDish(X,Y)))),
             assert(user:initially(- some(X,onRobot(X)))));
            true).

set_domains(2) :-
        retractall(user:domain(_,_)),
        assert(user:domain(dish,'#d1')),
        assert(user:domain(dish,'#d2')),
        assert(user:domain(room,'#r1')),
        assert(user:domain(room,'#r2')).

set_domains(1) :-
        retractall(user:domain(_,_)),
        assert(user:domain(dish,'#d1')),
        assert(user:domain(room,'#r1')).

check_prop(P,I,le) :-
        verify_le(P,T),
        check_result(P,I,T), !.

check_prop(P,I,ac) :-
        verify_ac(P,T),
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
