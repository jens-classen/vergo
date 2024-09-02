%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Basic Action Theory for dish cleaning robot
% - test domain for synthesis algorithm
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- use_module('../../verification/synthesis_acyclic').
:- use_module('../../lib/utils').
:- use_module('../../logic/l').
:- use_module('../../logic/cwa').

:- discontiguous causes_true/3.
:- discontiguous causes_false/3.

:- dynamic(initially/1).
:- dynamic(domain/2).

initially(all(X,dish(X)<=>F)) :- type_description(X,dish,F).
initially(all(X,room(X)<=>F)) :- type_description(X,room,F).
initially(all(X,at(X)<=>(X='#kitchen'))).
initially(all(X,new(X)<=>(dish(X)*all(Y,(-dirtyDish(X,Y)))*(-onRobot(X))))).
initially(all(X,onRobot(X)=>(dish(X)*(-some(Y,dirtyDish(X,Y)))))).
initially(all([X,Y],dirtyDish(X,Y)=>(dish(X)*room(Y)*(-onRobot(X))))).

rel_fluent(dirtyDish(_,_)).
rel_fluent(onRobot(_)).
rel_fluent(at(_)).
rel_fluent(new(_)).
rel_rigid(dish(_)).
rel_rigid(room(_)).

exo(requestDDR(_,_),true).

poss(load(X,Y),dirtyDish(X,Y)*at(Y)).
poss(unload(X),onRobot(X)*at('#kitchen')).
poss(requestDDR(X,Y),new(X)*room(Y)).
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
domain(dish,'#d2').
domain(room,'#r1').

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

property(prop1,
         eventually(always(-some([X,Y],dirtyDish(X,Y))))).
