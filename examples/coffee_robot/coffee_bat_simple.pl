%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Basic Action Theory for coffee delivery robot, queue size 2
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% action preconditions
precondition(wait,$true).
precondition(requestCoffee(_P),~full).
precondition(selectRequest(_P),~empty).
precondition(pickupCoffee,~holdingCoffee).
precondition(bringCoffee(_P),holdingCoffee).

% successor queue axioms
ssa(holdingCoffee,A, A=pickupCoffee | holdingCoffee & ~ ? [P] : A = bringCoffee(P)).
ssa(queue=Y, wait, queue=Y).
ssa(queue=Y, requestCoffee(_P), (queue=empty & Y=halffull)|(queue=halffull & Y=full)).
ssa(queue=Y, selectRequest(_P), (queue=halffull & Y=empty)|(queue=full & Y = halffull)).
ssa(queue=Y, pickupCoffee, queue=Y).
ssa(queue=Y, bringCoffee(_P), queue=Y).

% exogenous actions
exo(A,?[P] : A = requestCoffee(P)).

program(coffee,loop(if(empty,do(wait),pi(P,do(selectRequest(P));do(pickupCoffee);do(bringCoffee(P)))))).
program(exo,star(pi(A,?exo(A);do(A)))).

program(coffee_exo,conc(coffee,exo)).
program(coffee_exo_p,executable(coffee_exo)).

property(prop2,somepath(always(~(?[P]:occ(selectRequest(P)))))).

axiom(~(empty = halffull)).
axiom(~(empty = full)).
axiom(~(halffull = full)).
axiom(state=full <=> (~(state = empty) & ~(state=halffull))).
axiom(state=empty <=> (~(state = full) & ~(state=halffull))).
axiom(state=halffull <=> (~(state = empty) & ~(state=full))).

uno(q(_,_)).

def(full, queue=full).
def(empty, queue=empty).
