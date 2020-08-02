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

test(Program,Prop) :-
        construct_characteristic_graph(Program),
        check(Program,Prop,R),
        report_message(['Result is: ', R]),
        check_expected_labels(Program,Prop).

check_expected_labels(Prog,Phi) :-
        expected_label(Prog,Phi,I,N,Psi1),
        actual_label(Prog,Phi,I,N,Psi2),
        report_equivalence(I,N,Psi1,Psi2),
        fail.
check_expected_labels(_,_).

actual_label(Prog,Prop,I,N,Psi) :-
        property(Prop,Prog,somepath(next(Phi))),
        cg_label(Prog,ex(Phi),I,N,Psi).
actual_label(Prog,Prop,I,N,Psi) :-
        property(Prop,Prog,somepath(always(Phi))),
        cg_label(Prog,eg(Phi),I,N,Psi).
actual_label(Prog,Prop,I,N,Psi) :-
        property(Prop,Prog,somepath(until(Phi1,Phi2))),
        cg_label(Prog,eu(Phi1,Phi2),I,N,Psi).

report_equivalence(I,N,Psi1,Psi2) :-
        regress(Psi1,Psi3), % to macro-expand defined formulas
        equivalent_l(Psi3,Psi2), !,
        report_message(['Label for node ', N, ' in iteration ', I,
                        ' is as expected.']).
report_equivalence(I,N,Psi1,_Psi2) :-
        report_message(['Unexpected label for node ', N, ' in iteration ', I,
                        ': ', Psi1]).

def(phi,-some(X, occ(selectRequest(X)))).

% labels for somepath(always(-some(P,occ(selectRequest(P)))))
expected_label(main,prop4,0,0,phi).
expected_label(main,prop4,0,1,phi).
expected_label(main,prop4,0,2,phi).

expected_label(main,prop4,1,0,phi*lastFree(queue)).
expected_label(main,prop4,1,1,phi*(lastFree(queue)+(-holdingCoffee))).
expected_label(main,prop4,1,2,phi*(lastFree(queue)+holdingCoffee)).

expected_label(main,prop4,2,0,phi*empty(queue)).
expected_label(main,prop4,2,1,phi*(empty(queue)+(-holdingCoffee))).
expected_label(main,prop4,2,2,phi*lastFree(queue)*(empty(queue)+holdingCoffee)).

expected_label(main,prop4,3,0,phi*empty(queue)).
expected_label(main,prop4,3,1,phi*lastFree(queue)*(-holdingCoffee)).
%expected_label(main,prop4,3,2,phi*lastFree(queue)*holdingCoffee).    % (*)
expected_label(main,prop4,3,2,phi*empty(queue)*holdingCoffee).

expected_label(main,prop4,4,0,phi*empty(queue)).
%expected_label(main,prop4,4,1,phi*lastFree(queue)*(-holdingCoffee)). % (**)
expected_label(main,prop4,4,1,phi*empty(queue)*(-holdingCoffee)).
expected_label(main,prop4,4,2,phi*empty(queue)*holdingCoffee).

expected_label(main,prop4,5,0,phi*empty(queue)).
expected_label(main,prop4,5,1,phi*empty(queue)*(-holdingCoffee)).
expected_label(main,prop4,5,2,phi*empty(queue)*holdingCoffee).

%expected_label(main,prop4,6,0,phi*empty(queue)).
%expected_label(main,prop4,6,1,phi*empty(queue)*(-holdingCoffee)).
%expected_label(main,prop4,6,2,phi*empty(queue)*holdingCoffee).
