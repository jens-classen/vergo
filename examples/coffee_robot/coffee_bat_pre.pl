%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Basic Action Theory for coffee delivery robot, queue size 2
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% action preconditions
precondition(wait,$true).
precondition(requestCoffee(_P),~full).
precondition(selectRequest(P),isFirst(P)).
precondition(pickupCoffee,~holdingCoffee).
precondition(bringCoffee(_P),holdingCoffee).

% successor state axioms
ssa(holdingCoffee, A, A=pickupCoffee | holdingCoffee & ~ ? [P] : A = bringCoffee(P)).
ssa(queue(X,Y), wait, queue(X,Y)).
ssa(queue(X,Y), requestCoffee(P), ?[X1,Y1]: (queue(X1,Y1) & enqueue(X1,Y1,P,X,Y))).
ssa(queue(X,Y), selectRequest(P), ?[X1,Y1]: (queue(X1,Y1) & dequeue(X1,Y1,P,X,Y))).
ssa(queue(X,Y), pickupCoffee, queue(X,Y)).
ssa(queue(X,Y), bringCoffee(_P), queue(X,Y)).
        
%ssa(queue(X,Y),    A, (?[P,Xp,Yp] : (A = requestCoffee(P) & enqueue(Xp,Yp,P,X,Y)) |
%                       ?[P,Xp,Yp] : (A = selectRequest(P) & dequeue(Xp,Yp,P,X,Y)) |
%                       (queue(X,Y) & ~ (?[P] : (A =requestCoffee(P) | A = selectRequest(P)))))).

% definitions
def(isFirst(P),           (~(P = e) & ?[P2] : queue(P,P2))).
def(empty,                queue(e,e)).
def(full,                 ?[P1,P2] : (~(P1 = e) & ~(P2 = e) & queue(P1,P2))).
def(enqueue(Xo,Yo,P,X,Y), (~(P = e) & Xo = e & Yo = e & X = P & Y = e) |
                          (~(P = e) & ~(Xo = e) & Yo = e & X = Xo & Y = P)).
def(dequeue(Xo,Yo,P,X,Y), (~(P = e) & P = Xo & X = Yo & Y = e)).

% exogenous actions
exo(A,?[P] : A = requestCoffee(P)).

program(coffee,loop(if(empty,do(wait),pi(P,do(selectRequest(P));do(pickupCoffee);do(bringCoffee(P)))))).
program(exo,star(pi(A,?exo(A);do(A)))).

program(coffee_exo,conc(coffee,exo)).
program(coffee_exo_p,executable(coffee_exo)).

property(prop2,somepath(always(~(?[P]:occ(selectRequest(P)))))).

axiom(_) :- fail.
uno(_) :- fail.