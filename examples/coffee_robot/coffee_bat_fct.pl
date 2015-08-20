%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Basic Action Theory for coffee delivery robot, queue size 2
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

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

causes_true(A,occ(B),(A=B)).
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
stdname(bob).

include_preconditions. % everything is precondition-extended

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

property(prop1,
         main,
         somepath(next(empty(queue)))).

property(prop2,
         main,
         allpaths(always(occ(requestCoffee(X))
                         =>eventually(occ(selectRequest(X)))))).

property(prop3,
         main,
         somepath(always(-some(P,occ(selectRequest(P)))))).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Testing
% -------
% Reconstruction of full Example 5.35 from Appendix B.2 of
% 
% Jens Claßen: Planning and Verification in the Agent Language Golog.
% PhD Thesis, Department of Computer Science, RWTH Aachen University,
% 2013.
%
% It turned out that there is an error in the thesis for label (*)
% below, and hence label (**) is also wrong as a consequence. The end
% result (and all other label formulas) are correct though, with the
% only difference being that the method converges one iteration
% earlier.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

test :-
        construct_characteristic_graph(main),
        check(main,prop3,R),
        report_message(['Result is: ', R]),
        check_expected_labels(main,prop3).

check_expected_labels(P,Phi) :-
        expected_label(P,Phi,I,N,Psi1),
        actual_label(P,Phi,I,N,Psi2),
        report_equivalence(I,N,Psi1,Psi2),
        fail.
check_expected_labels(_,_).

actual_label(P,Prop,I,N,Psi) :-
        property(Prop,P,somepath(always(Phi))),
        cg_label(P,eg(Phi),I,N,Psi).

report_equivalence(I,N,Psi1,Psi2) :-
        regress(Psi1,Psi3), % to macro-expand defined formulas
        equivalent(Psi3,Psi2), !.
report_equivalence(I,N,Psi1,_Psi2) :-
        report_message(['Unexpected label for node ', N, ' in iteration ', I,
                        ': ', Psi1]).

def(phi,-some(X, occ(selectRequest(X)))).

expected_label(main,prop3,0,0,phi).
expected_label(main,prop3,0,1,phi).
expected_label(main,prop3,0,2,phi).

expected_label(main,prop3,1,0,phi*lastFree(queue)).
expected_label(main,prop3,1,1,phi*(lastFree(queue)+(-holdingCoffee))).
expected_label(main,prop3,1,2,phi*(lastFree(queue)+holdingCoffee)).

expected_label(main,prop3,2,0,phi*empty(queue)).
expected_label(main,prop3,2,1,phi*(empty(queue)+(-holdingCoffee))).
expected_label(main,prop3,2,2,phi*lastFree(queue)*(empty(queue)+holdingCoffee)).

expected_label(main,prop3,3,0,phi*empty(queue)).
expected_label(main,prop3,3,1,phi*lastFree(queue)*(-holdingCoffee)).
%expected_label(main,prop3,3,2,phi*lastFree(queue)*holdingCoffee).    (*)
expected_label(main,prop3,3,2,phi*empty(queue)*holdingCoffee).

expected_label(main,prop3,4,0,phi*empty(queue)).
%expected_label(main,prop3,4,1,phi*lastFree(queue)*(-holdingCoffee)). (**)
expected_label(main,prop3,4,1,phi*empty(queue)*(-holdingCoffee)).
expected_label(main,prop3,4,2,phi*empty(queue)*holdingCoffee).

expected_label(main,prop3,5,0,phi*empty(queue)).
expected_label(main,prop3,5,1,phi*empty(queue)*(-holdingCoffee)).
expected_label(main,prop3,5,2,phi*empty(queue)*holdingCoffee).

%expected_label(main,prop3,6,0,phi*empty(queue)).
%expected_label(main,prop3,6,1,phi*empty(queue)*(-holdingCoffee)).
%expected_label(main,prop3,6,2,phi*empty(queue)*holdingCoffee).
