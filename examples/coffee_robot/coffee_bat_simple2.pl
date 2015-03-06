%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Basic Action Theory for coffee delivery robot, queue size 2
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% action preconditions
precondition(wait,$true).
precondition(requestCoffee(P),(q2=e)&(~(P=e))).
precondition(selectRequest(P),(q1=P)&(~(P=e))).
precondition(pickupCoffee,~holdingCoffee).
precondition(bringCoffee(_P),holdingCoffee).

% successor state axioms
ssa(holdingCoffee, wait, holdingCoffee).
ssa(holdingCoffee, pickupCoffee, $true).
ssa(holdingCoffee, bringCoffee(_P), $false).
ssa(holdingCoffee, requestCoffee(_P), holdingCoffee).
ssa(holdingCoffee, selectRequest(_P), holdingCoffee).
ssa(q1=P, wait, q1=P).
ssa(q2=P, wait, q2=P).
ssa(q1=P1, requestCoffee(P2), (((P1=P2)&(q1=e)&(q2=e)) | ((q1=P1)&(q2=e)))).
ssa(q2=P1, requestCoffee(P2), ((P1=P2)&(~(q1=e))&(q2=e)) | ((q1=e)&(q2=e)&(P1=e))).
ssa(q1=P1, selectRequest(_P2), (q2=P1)).
ssa(q2=P1, selectRequest(_P2), (P1=e)).
ssa(q1=P, pickupCoffee, q1=P).
ssa(q2=P, pickupCoffee, q2=P).
ssa(q1=P1, bringCoffee(_P), q1=P1).
ssa(q2=P1, bringCoffee(_P), q2=P1).

% exogenous actions
exo(A,?[P] : A = requestCoffee(P)).

program(coffee,loop(if(empty,do(wait),pi(P,do(selectRequest(P));do(pickupCoffee);do(bringCoffee(P)))))).
program(exo,star(pi(A,?exo(A);do(A)))).

program(coffee_exo,conc(coffee,exo)).
program(coffee_exo_p,executable(coffee_exo)).

program(simple, loop(do(pickupCoffee);do(bringCoffee(bob)))).

property(prop2,somepath(always(~(?[P]:occ(selectRequest(P)))))).

def(empty, (q1=e)&(q2=e)).
def(full, (~(q1=e))&(~(q2=e))).

standardname(e).
standardname(bob).

