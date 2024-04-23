%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Basic Action Theory for dish cleaning robot
% - test domain for synthesis algorithm
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- use_module('../../verification/synthesis_acyclic').
:- use_module('../../lib/utils').
:- use_module('../../logic/l').

:- discontiguous causes_true/3.
:- discontiguous causes_false/3.

:- dynamic(initially/1).
:- dynamic(domain/2).

initially(room('#r1')).
% initially(room('#r2')).
initially(all(X,at(X)<=>(X='#kitchen'))).
initially(all(X,new(X)<=>(((X='#d1')+(X='#d2'))*all(Y,(-dirtyDish(X,Y)))*(-onRobot(X))))).
% initially(all(X,new(X)<=>(((X='#d1')+(X='#d2'))))).
% initially(all(X,new(X)<=>(X='#d1'))).
% initially(all([X,Y],(-dirtyDish(X,Y)))).
% initially(all(X,(-onRobot(X)))).

rel_fluent(dirtyDish(_,_)).
rel_fluent(onRobot(_)).
rel_fluent(at(_)).
rel_fluent(new(_)).
rel_rigid(room(_)).

exo(requestDDR(_,_),true).

poss(requestDDR(X,Y),new(X)*room(Y)).
poss(load(_X,Y),at(Y)).
poss(unload(X),onRobot(X)*at('#kitchen')).
poss(goto(X),room(X)+(X='#kitchen')).

causes_true(requestDDR(X,Y),dirtyDish(X,Y),true).
causes_false(load(X,Y),dirtyDish(X,Y),true).

causes_true(load(X,_Y),onRobot(X),true).
causes_false(unload(X),onRobot(X),true).

causes_false(requestDDR(X,_Y),new(X),true).

causes_true(goto(X),at(X),true).
causes_false(goto(_Y),at(_X),true).

type(dish).
type(room).

domain(dish,'#d1').
% domain(dish,'#d2').
domain(room,'#r1').
% domain(room,'#r2').

program(control,
        star([while(some(X,onRobot(X)),
                     pick(X,dish,unload(X))),
              pick(Y,room,[goto(Y),
                           while(some(X,dirtyDish(X,Y)),
                                  pick(X,dish,load(X,Y)))
                          ]
                  ),
              goto('#kitchen')
             ]
            )
       ).

program(exog,
        star(pick(X,dish,
                  pick(Y,room,
                       requestDDR(X,Y)))
            )
       ).

program(main,
        conc(control,exog)).

program(testpr,star(nondet(goto('#kitchen'),goto('#r1')))).

program(testpr2,[star(nondet(goto('#kitchen'),goto('#r1'))),
                 test(onRobot('#d3'))]). % to get non-trivial final

property(prop1,
         eventually(always(-some([X,Y],dirtyDish(X,Y))))).

property(prop2,
         eventually(at('#r1'))).  % for testing

property(prop3,
         always(at('#kitchen'))).  % for testing

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Testing
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- begin_tests('synthesis_acyclic').

test(synthesis_with_initial_kb) :- !,
        %set_initial_kb(true),
        set_domains(1),
        synthesize(main,prop1).

:- end_tests('synthesis_acyclic').

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

