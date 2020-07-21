:- discontiguous causes_true/3.
:- discontiguous causes_false/3.

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
