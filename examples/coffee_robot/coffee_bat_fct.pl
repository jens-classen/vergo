%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Basic Action Theory for coffee delivery robot
% - finite queue of size 2
% - queue represented by functional fluent
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% verification algorithm to be tested
:- use_module('../../verification/fixpoint_ctl').

:- use_module('../../verification/fixpoint_ctl_thesis',
              [construct_characteristic_graph/1 as
               construct_characteristic_graph_thesis,
               verify/2 as verify_thesis]).
               
:- use_module('../../lib/utils').
:- use_module('../../logic/def').
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
    Q='#q'('#e','#e')).
def(lastFree(Q),
    some(P,Q='#q'(P,'#e'))).
def(full(Q),
    some([P1,P2],(-(P1='#e'))*(-(P2='#e'))*(Q='#q'(P1,P2)))).
def(enqueue(Qold,P,Qnew),
    ((Qold='#q'('#e','#e'))*(Qnew='#q'(P,'#e')))
    +(some(X1,(-(X1='#e'))*(Qold='#q'(X1,'#e'))*(Qnew='#q'(X1,P))))).
def(dequeue(Qold,P,Qnew), 
    some(X2,(Qold='#q'(P,X2))*(Qnew='#q'(X2,'#e')))).

exo(requestCoffee(_),true).

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
% Testing: Intermediate label formulas for Examples 5.35 and 5.38 from
% 
% Jens Claßen: Planning and Verification in the Agent Language Golog.
% PhD Thesis, Department of Computer Science, RWTH Aachen University,
% 2013.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- discontiguous expected_label/5.
:- discontiguous expected_max_iteration/3.

% Example 5.35 (prop4)
% It turned out that there is an error in the thesis for label (*)
% below, and hence label (**) is also wrong as a consequence. The end
% result (and all other label formulas) are correct though, with the
% only difference being that the method converges one iteration
% earlier.

def(phi,-some(X, occ(selectRequest(X)))).

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

expected_max_iteration(main,prop4,5).
%expected_max_iteration(main,prop4,6).

% Example 5.38 (prop2) 

% Again, the labels the method produces differs from the ones stated
% in the thesis due to the fact that in the latter, it is implicitly
% assumed (as a provable state constraint) that the 'queue' fluent
% always has a term as its value that represents a queue (here:
% #q(...,...)).

expected_label(main,prop2,0,0,holdingCoffee).
%expected_label(main,prop2,0,1,false).
expected_label(main,prop2,0,1,holdingCoffee).
expected_label(main,prop2,0,2,holdingCoffee).

expected_label(main,prop2,1,0,holdingCoffee).
expected_label(main,prop2,1,1,empty(queue)+holdingCoffee).
%expected_label(main,prop2,1,1,empty(queue)*(-holdingCoffee)).
expected_label(main,prop2,1,2,holdingCoffee).
%expected_label(main,prop2,1,2,holdingCoffee+empty(queue)).

expected_label(main,prop2,2,0,holdingCoffee).
expected_label(main,prop2,2,1,empty(queue)+holdingCoffee).
%expected_label(main,prop2,2,1,empty(queue)*(-holdingCoffee)).
expected_label(main,prop2,2,2,holdingCoffee).
%expected_label(main,prop2,2,2,holdingCoffee+empty(queue)).

expected_max_iteration(main,prop2,2).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Test of new fixpoint verification method
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- begin_tests(fixpoint_ctl).

test(checkeu) :-
        test_prog_prop(main,prop2).

test(checkeg) :-
        test_prog_prop(main,prop4).

test_prog_prop(Program,Prop) :-
        construct_characteristic_graph(Program),
        fixpoint_ctl:check_ctl(Program,Prop,LabelSet), !,
        check_expected_labels(Program,Prop,LabelSet).

check_expected_labels(Prog,Prop,LabelSet) :-
        expected_max_iteration(Prog,Prop,Iter), !,
        check_expected_labels(Prog,Prop,Iter,LabelSet).
check_expected_labels(Prog,Prop,Iter,LabelSet) :-
        Iter == 0, !,
        check_expected_labels_by_nodes(Prog,Prop,Iter,LabelSet).
check_expected_labels(Prog,Prop,Iter,LabelSet) :- !,
        Iter1 is Iter-1,
        previous_label_set(Prog,Prop,LabelSet,PreviousLabelSet),
        check_expected_labels(Prog,Prop,Iter1,PreviousLabelSet),
        check_expected_labels_by_nodes(Prog,Prop,Iter,LabelSet).

check_expected_labels_by_nodes(Prog,Prop,Iter,LabelSet) :-
        cg_number_of_nodes(Prog,N), !,
        check_expected_labels_by_nodes(Prog,Prop,0,N,Iter,LabelSet).
check_expected_labels_by_nodes(_Prog,_Prop,N,N,_Iter,_LabelSet) :- !.
check_expected_labels_by_nodes(Prog,Prop,J,N,Iter,LabelSet) :-
        expected_label(Prog,Prop,Iter,J,Psi1),
        fixpoint_ctl:label(Prog,J,Psi2,LabelSet), !,
        report_equivalence(Iter,J,Psi1,Psi2),
        J1 is J+1,
        check_expected_labels_by_nodes(Prog,Prop,J1,N,Iter,LabelSet).

previous_label_set(Prog,Prop,Labels,Previous) :-
        property(Prop,Prog,somepath(always(_Phi))),
        fixpoint_ctl:labelset(Prog,Previous*_,Labels), !.
previous_label_set(Prog,Prop,Labels,Previous) :-
        property(Prop,Prog,somepath(until(_Phi1,_Phi2))),
        fixpoint_ctl:labelset(Prog,Previous+_,Labels), !.

:- end_tests(fixpoint_ctl).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Test of old fixpoint verification method
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- begin_tests(fixpoint_ctl_thesis).

test(checkeu) :-
        test_prog_prop(main,prop2).

test(checkeg) :-
        test_prog_prop(main,prop4).

test_prog_prop(Program,Prop) :-
        construct_characteristic_graph_thesis(Program),
        fixpoint_ctl_thesis:check(Program,Prop,R),
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
        fixpoint_ctl_thesis:cg_label(Prog,ex(Phi),I,N,Psi).
actual_label(Prog,Prop,I,N,Psi) :-
        property(Prop,Prog,somepath(always(Phi))),
        fixpoint_ctl_thesis:cg_label(Prog,eg(Phi),I,N,Psi).
actual_label(Prog,Prop,I,N,Psi) :-
        property(Prop,Prog,somepath(until(Phi1,Phi2))),
        fixpoint_ctl_thesis:cg_label(Prog,eu(Phi1,Phi2),I,N,Psi).

:- end_tests(fixpoint_ctl_thesis).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Shared code for all tests
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

report_equivalence(I,N,Psi1,Psi2) :-
        expand_defs(Psi1,Psi3),
        equivalent_l(Psi3,Psi2,Equiv), !,
        report_equivalence2(I,N,Psi1,Equiv),
        assertion(equivalent_l(Psi3,Psi2,true)).
report_equivalence2(I,N,_Psi1,true) :- !,
        report_message(['Label for node ', N, ' in iteration ', I,
                        ' is as expected.']).
report_equivalence2(I,N,Psi1,_) :- !,
        report_message(['Unexpected label for node ', N, ' in iteration ', I,
                        ': ', Psi1]).
