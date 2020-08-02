%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Basic Action Theory for coffee delivery robot
% - infinite "queue" (actually, a stack)
% - queue represented by functional fluent
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% verification algorithm to be tested
:- use_module('../../verification/fixpoint_ctl').

:- use_module('../../lib/utils').
:- use_module('../../logic/l').
:- use_module('../../projection/regression').

:- discontiguous causes_true/3.
:- discontiguous causes_false/3.
:- discontiguous rel_fluent/1.
:- discontiguous def/2.

initially(empty(queue)).
initially(all(A,-occ(A))).

rel_fluent(holdingCoffee).
fun_fluent(queue).
rel_fluent(occ(_)).

poss(wait,true).
poss(requestCoffee(P),-(P='#e')*lastFree(queue)).
poss(selectRequest(P),-(P='#e')*isFirst(queue,P)).
poss(pickupCoffee,-holdingCoffee).
poss(bringCoffee(_P),holdingCoffee).

causes_true(pickupCoffee,holdingCoffee,true).
causes_false(bringCoffee(_),holdingCoffee,true).

causes(requestCoffee(P),queue,Y,enqueue(queue,P,Y)).
causes(selectRequest(P),queue,Y,dequeue(queue,P,Y)).

causes_true(A,occ(B),(A=B)).
causes_false(A,occ(B),-(A=B)).

def(isFirst(Q,P),
    (some(P2,Q='#q'(P,P2)))).
def(empty(Q),    
    Q='#nil').
def(lastFree(_Q),
    true).
def(full(_Q),
    false).
def(enqueue(Qold,P,Qnew),
    Qnew='#q'(P,Qold)).
def(dequeue(Qold,P,Qnew),
    Qold='#q'(P,Qnew)).

exo(requestCoffee(_),true).

include_preconditions. % everything is precondition-extended
% use_sink_states.     % do not use sink states for termination+failure
% use_path_labels.     % assume a path always exists

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

program(exog_finite,
        star(pick(X,requestCoffee(X)))).

program(main,
        conc(coffee,exog)).

property(prop1,
         main,
         somepath(next(empty(queue)))).

property(prop2,
         main,
         somepath(until(empty(queue),holdingCoffee))).

property(prop3,
         main,
         allpaths(always(occ(requestCoffee(X))
                         =>eventually(occ(selectRequest(X)))))).

property(prop4,
         main,
         somepath(always(-some(P,occ(selectRequest(P)))))).

property(prop5,
         exog_finite,
         postcond(full(queue))).
