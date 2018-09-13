%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Basic Action Theory for coffee delivery robot, queue size 2
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- discontiguous causes_true/3.
:- discontiguous causes_false/3.
:- discontiguous rel_fluent/1.
:- discontiguous def/2.

initially(empty).
initially(all(A,-occ(A))).

prim_action(wait).
prim_action(requestCoffee(_)).
prim_action(selectRequest(_)).
prim_action(pickupCoffee).
prim_action(bringCoffee(_)).

rel_fluent(holdingCoffee).
rel_fluent(queue(_,_)).
rel_fluent(occ(_)).

poss(wait,true).
poss(requestCoffee(P),-(P='#e')*lastFree).
poss(selectRequest(P),-(P='#e')*isFirst(P)).
poss(pickupCoffee,-holdingCoffee).
poss(bringCoffee(_P),holdingCoffee).

causes_true(pickupCoffee,holdingCoffee,true).
causes_false(bringCoffee(_),holdingCoffee,true).

causes_true(requestCoffee(P),queue(X,Y),some([Xo,Yo],queue(Xo,Yo)*enqueue(Xo,Yo,P,X,Y))).
causes_false(requestCoffee(P),queue(Xo,Yo),some([X,Y],queue(Xo,Yo)*enqueue(Xo,Yo,P,X,Y))).
causes_true(selectRequest(P),queue(X,Y),some([Xo,Yo],queue(Xo,Yo)*dequeue(Xo,Yo,P,X,Y))).
causes_false(selectRequest(P),queue(Xo,Yo),some([X,Y],queue(Xo,Yo)*dequeue(Xo,Yo,P,X,Y))).

causes_true(A,occ(B),(A=B)).
causes_false(A,occ(B),-(A=B)).

def(isFirst(P),
    some(P2,queue(P,P2))).
def(empty,    
    queue('#e','#e')).
def(lastFree,
    some(P,queue(P,'#e'))).
def(full,
    some([P1,P2],(-(P1='#e'))*(-(P2='#e'))*queue(P1,P2))).
def(enqueue(Xo,Yo,P,X,Y),
    ((Xo='#e')*(Yo='#e')*(X=P)*(Y='#e'))
    +some(X1,(-(X1='#e'))*(Xo=X1)*(Yo='#e')*(X=X1)*(Y=P))).
def(dequeue(Xo,Yo,P,X,Y), 
    some(X2,(Xo=P)*(Yo=X2)*(X=X2)*(Y='#e'))).

exo(requestCoffee(_),true).

include_preconditions. % everything is precondition-extended
% use_sink_states.     % do not use sink states for termination+failure

program(coffee,
        loop(if(-empty,
                pick(P,[selectRequest(P),
                        pickupCoffee,
                        bringCoffee(P)
                       ]
                    ),
                wait)
            )
       ).

program(exog,
        loop(pick(A,[test(exo(A)),A]))).

program(exog_finite,
        star(pick(X,requestCoffee(X)))).

program(main,
        conc(coffee,exog)).

property(prop1,
         main,
         somepath(next(empty))).

property(prop2,
         main,
         somepath(until(empty,holdingCoffee))).

property(prop3,
         main,
         allpaths(always(occ(requestCoffee(X))
                         =>eventually(occ(selectRequest(X)))))).

property(prop4,
         main,
         somepath(always(-some(P,occ(selectRequest(P)))))).

property(prop5,
         exog_finite,
         postcond(full)).
