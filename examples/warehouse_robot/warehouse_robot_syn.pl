%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Basic Action Theory for warehouse robot
% - benchmark domain for synthesis algorithm
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- use_module('../../verification/synthesis_acyclic').
:- use_module('../../lib/utils').
:- use_module('../../logic/l').
:- use_module('../../logic/cwa').

:- discontiguous causes_true/3.
:- discontiguous causes_false/3.

:- dynamic(initially/1).
:- dynamic(domain/2).

initially(all(X,shelf(X)<=>F)) :- type_description(X,shelf,F).
initially(all(X,box(X)<=>F)) :- type_description(X,box,F).
initially(all(X,some(Y,in(X,Y))=>((-shelf(X))*(-box(X))))).
initially(some(X,wrap(X))).
initially(all(X,-holding(X))).
initially(all(X,-broken(X))).
initially(rat('#s1')).
initially(all(X,box(X)=>at(X,'#s1'))).
initially(all([X,Y],(in(X,Y)*box(Y))=>at(X,'#s1'))).
initially(all(Y,((-(Y='#s1'))=>(-rat(Y)*all(X,(-at(X,Y))))))).
initially(all([X,Y],in(X,Y)=>(-wrap(X)))).

rel_fluent(in(_,_)).
rel_fluent(broken(_)).
rel_fluent(at(_,_)).
rel_fluent(rat(_)).
rel_fluent(holding(_)).
rel_rigid(shelf(_)).
rel_rigid(box(_)).
rel_rigid(wrap(_)).
rel_rigid(fragile(_)).

exo(drop(_),true).

poss(take(X,Y),at(X,Y)*rat(Y)).
poss(move(X,Y),rat(X)*shelf(Y)*(-(X=Y))).
poss(put(X,Y),holding(X)*rat(Y)).
poss(addwrap(X),some(Y,rat(Y)*at(X,Y))).
poss(drop(X),holding(X)).

causes_true(move(_X,Y),rat(Y),true).
causes_false(move(Y,_Z),rat(Y),true).

causes_true(move(_Z,Y),at(X,Y),some(V,holding(V)*((V=X)+in(X,V)))).
causes_false(move(Y,_Z),at(X,Y),some(V,holding(V)*((V=X)+in(X,V)))).

causes_true(take(X,_Y),holding(X),true).
causes_false(put(X,_Y),holding(X),true).

causes_true(drop(Y),broken(X),in(X,Y)*fragile(X)
                                      *(-some(Z,in(Z,Y)*wrap(Z)))).

causes_true(addwrap(Y),in(X,Y),wrap(X)).

type(shelf).
type(box).
type(wrap).

domain(shelf,'#s1').
domain(shelf,'#s2').
domain(box,'#b1').

program(maybe(P),nondet([],P)).

program(main,
        star(pick(L0,shelf,
                   pick(L1,shelf,
                        [maybe(move(L0,L1)),
                         pick(B,box,
                              [maybe(addwrap(B)),
                               take(B,'#s1'),
                               maybe(drop(B)),
                               pick(L2,shelf,
                                    [move(L1,L2),
                                     put(B,L2)
                                    ])
                              ])
                        ])
                 )
            )
       ).

property(prop1,
         eventually(all([O,B],(box(B)*in(O,B))=>(-broken(O)*at(O,'#s2'))))).

property(prop2,
         eventually(all(X,in(X,'#b1')=>(-broken(X)*at(X,'#s2'))))).
