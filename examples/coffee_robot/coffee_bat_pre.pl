%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Basic Action Theory for coffee delivery robot
% - finite queue of size 2
% - queue represented by relational fluent
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% verification algorithm to be tested
:- use_module('../../verification/fixpoint_ctl').

:- discontiguous causes_true/3.
:- discontiguous causes_false/3.
:- discontiguous rel_fluent/1.
:- discontiguous def/2.

rel_fluent(hasCoffee(_)).
rel_fluent(holdingCoffee).
rel_fluent(queue(_,_)).

def(first(P),
    some(P2,queue(P,P2))).
def(last(P),
    some(P2,queue(P2,P))).
def(empty,
    queue('#e','#e')).
def(enqueue(Xo,Yo,P,X,Y),
    ((Xo='#e')*(Yo='#e')*(X=P)*(Y='#e'))
    +some(X1,(-(X1='#e'))*(Xo=X1)*(Yo='#e')*(X=X1)*(Y=P))).
def(dequeue(Xo,Yo,P,X,Y),
    some(X2,(Xo=P)*(Yo=X2)*(X=X2)*(Y='#e'))).

initially(all(X,-hasCoffee(X))).
initially(-holdingCoffee).
initially(empty).

poss(requestCoffee(P),-(P='#e')*last('#e')).
poss(selectRequest(P),-(P='#e')*first(P)).
poss(pickupCoffee,-holdingCoffee).
poss(bringCoffee(_P),holdingCoffee).
poss(wait,true).

causes_true(requestCoffee(P),queue(X,Y),some([Xo,Yo],queue(Xo,Yo)*enqueue(Xo,Yo,P,X,Y))).
causes_false(requestCoffee(P),queue(Xo,Yo),some([X,Y],queue(Xo,Yo)*enqueue(Xo,Yo,P,X,Y))).
causes_true(selectRequest(P),queue(X,Y),some([Xo,Yo],queue(Xo,Yo)*dequeue(Xo,Yo,P,X,Y))).
causes_false(selectRequest(P),queue(Xo,Yo),some([X,Y],queue(Xo,Yo)*dequeue(Xo,Yo,P,X,Y))).

causes_true(pickupCoffee,holdingCoffee,true).
causes_false(bringCoffee(_),holdingCoffee,true).

causes_true(bringCoffee(P),hasCoffee(P),true).
causes_false(requestCoffee(P),hasCoffee(P),true).

program(agt,
        loop(if(-empty,
                pick(P,[selectRequest(P),
                        pickupCoffee,
                        bringCoffee(P)
                       ]
                    ),
                wait)
            )
       ).

program(env,
        loop(pick(P,requestCoffee(P)))).

program(main,
        conc(agt,env)).

property(prop1,
         main,
         somepath(until(empty,holdingCoffee))).

property(prop2,
         main,
         somepath(always(-some(P,hasCoffee(P))))).
