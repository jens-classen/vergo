%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Basic Action Theory for coffee delivery robot, queue size 2
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% action preconditions
precondition(wait,$true).
precondition(requestCoffee(_P),~full(queue)).
precondition(selectRequest(P),isFirst(P,queue)).
precondition(pickupCoffee,~holdingCoffee).
precondition(bringCoffee(_P),holdingCoffee).

% successor state axioms
ssa(holdingCoffee,A, A=pickupCoffee | holdingCoffee & ~ ? [P] : A = bringCoffee(P)).
ssa(queue=Y, requestCoffee(P), enqueue(queue,P,Y)).
ssa(queue=Y, selectRequest(P), dequeue(queue,P,Y)).
ssa(queue=Y,             wait, queue=Y).
ssa(queue=Y,     pickupCoffee, queue=Y).
ssa(queue=Y,  bringCoffee(_P), queue=Y).

%ssa(queue=Y,      A, (?[P1] : (A = requestCoffee(P1) & enqueue(queue,P1,Y)) |
%                      ?[P2] : (A = selectRequest(P2) & dequeue(queue,P2,Y)) |
%                      (queue = Y & ~ (?[P3] : (A = requestCoffee(P3) | A = selectRequest(P3)))))).

% definitions
def(isFirst(P,Q),         (~(P = e) & ?[P2] : Q = q(P,P2))).
def(empty(Q),              Q = q(e,e)).
def(full(Q),               ?[P1,P2] : ~(P1 = e) & ~(P2 = e) & Q = q(P1,P2)).
def(enqueue(Qold,P,Qnew), (~(P = e) & (Qold = q(e,e) & Qnew = q(P,e))|
                                         (?[X1] : ~(X1 = e) & Qold = q(X1,e) & Qnew = q(X1,P)))).
def(dequeue(Qold,P,Qnew), (~(P = e) & ?[X2] : (Qold = q(P,X2) & Qnew = q(X2,e)))).

% exogenous actions
exo(A,?[P] : A = requestCoffee(P)).

program(coffee,loop(if(empty(queue),do(wait),pi(P,do(selectRequest(P));do(pickupCoffee);do(bringCoffee(P)))))).
program(exo,star(pi(A,?exo(A);do(A)))).

program(coffee_exo,conc(coffee,exo)).
program(coffee_exo_p,executable(coffee_exo)).

property(prop2,somepath(always(~(?[P]:occ(selectRequest(P)))))).

%axiom(![X1,Y1,X2,Y2]:((q(X1,Y1) = q(X2,Y2)) => (X1=X2 & Y1=Y2))).
%axiom(![X,Y]:(~(q(X,Y) = e))).
axiom(?[X,Y]:(queue=q(X,Y))).

% unique names assumption for q/2.
uno(q(_,_)).
uno(e).
