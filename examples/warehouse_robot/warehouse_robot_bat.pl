% Incomplete draft for an encoding of the warehouse robot domain.
% Uses nonlocal action effects and decision-theoretic aspects.

:- discontiguous causes_true/3.
:- discontiguous causes_false/3.

initially(on('#s1','#box')).
%initially(all(Y,someatl(1,X,on(X,Y))).
initially(all(X,-bubblewrap(X) + -fragile(X))).
initially(contains('#box','#vase')).
initially(all(X,-contains('#box',X) + fragile(X))).
              
              
prim_action(crash(_)).
prim_action(drop(_)).
prim_action(repair(_)).
prim_action(move(_,_,_)).

rel_fluent(on(_,_)).
rel_fluent(bubblewrap(_)).
rel_fluent(fragile(_)).
rel_fluent(contains(_,_)).
rel_fluent(broken(_)).
rel_fluent(noBW(_)).

poss(crash(_),true).
poss(drop(_),true).
poss(repair(_),true).
poss(move(_,_,_),true).

causes_true(crash(S),broken(X),on(S,X)+(X=S)).
causes_true(drop(V),broken(X),contains(V,X)*fragile(X)*noBW(V)).
causes_false(repair(S),broken(X),(S=X) * -fragile(X)).

causes_true(move(V,_S1,S2),on(X,Y),(Y=S2)*(contains(V,X)+(X=V))).
causes_false(move(V,S1,_S2),on(X,Y),(Y=S1)*(contains(V,X)+(X=V))).

program(moves,
        nondet(move('#box','#s1','#s2'),
               nondet(drop('#box'),
                      crash('#s2')))
       ).

program(main,
        star(moves)).

property(prop1,
         main,
         somepath(eventually(on('#s1','#box')))).
