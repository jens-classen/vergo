%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Basic Action Theory for coffee delivery robot, queue size 2
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- use_module('../../reasoning/fol').

:- discontiguous causes_true/3.
:- discontiguous causes_false/3.
:- discontiguous rel_fluent/1.

initially(empty(queue)).
initially(forall(A,-occ(A))).

prim_action(wait).
prim_action(requestCoffee(_)).
prim_action(selectRequest(_)).
prim_action(pickupCoffee).
prim_action(bringCoffee(_)).

rel_fluent(holdingCoffee).
fun_fluent(queue).
rel_fluent(occ(_)).

poss(wait,true).
poss(requestCoffee(P),-(P=e)*lastFree(queue)).
poss(selectRequest(P),-(P=e)*isFirst(queue,P)).
poss(pickupCoffee,-holdingCoffee).
poss(bringCoffee(_P),holdingCoffee).

causes_true(pickupCoffee,holdingCoffee,true).
causes_false(bringCoffee(_),holdingCoffee,true).

causes(requestCoffee(P),queue,Y,enqueue(queue,P,Y)).
causes(selectRequest(P),queue,Y,dequeue(queue,P,Y)).

causes_true(A,occ(A),true).
causes_false(A,occ(B),-(A=B)).

def(isFirst(Q,P),
    (some(P2,Q=q(P,P2)))).
def(empty(Q),    
    Q=q(e,e)).
def(lastFree(Q),
    some(P,Q=q(P,e))).
def(full(Q),     
    some([P1,P2],(-(P1=e))*(-(P2=e))*(Q=q(P1,P2)))).
def(enqueue(Qold,P,Qnew),
    ((Qold=q(e,e))*(Qnew=q(P,e)))
    +(some(X1,(-(X1=e))*(Qold=q(X1,e))*(Qnew=q(X1,P))))).
def(dequeue(Qold,P,Qnew), 
    some(X2,(Qold=q(P,X2))*(Qnew=q(X2,e)))).

exo(requestCoffee(_),true).

stdname(e).
stdname(q(_,_)).

program(coffee,
        loop(if(-empty(queue),
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

program(main,
        conc(coffee,exog)).

program(coffee_exo_p,executable(coffee_exo)).

property(prop1,
         main,
         allpaths(always(occ(requestCoffee(X))
                         =>eventually(occ(selectRequest(X)))))).

property(prop2,
         main,
         somepath(always(-some(P,occ(selectRequest(P)))))).

