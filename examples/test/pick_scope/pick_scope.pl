%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Basic Action Theory for testing correct scopes of pick
% operators in the characteristic graph.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- use_module('../../../verification/fixpoint_ctl_thesis').

:- discontiguous causes_true/3.
:- discontiguous causes_false/3.
:- discontiguous rel_fluent/1.

rel_fluent(predicate(_)).

poss(action(_),true).

causes_true(action(Y),predicate(Y),true).

ignore_preconditions.

/** Footnote 5, page 190 in
Jens Claßen: Planning and Verification in the Agent Language Golog.
PhD Thesis, Department of Computer Science, RWTH Aachen University,
2013.
**/
program(testprog1,
        star(pick(Y,[action(Y),test(predicate(Y))]))).

/** Similar to coffee robot control program. **/
program(testprog2,
        loop([test(predicate(a)),
              pick(Y,[action(Y),action(a),action(Y)])])).

/** Similar to program simulating exogenous actions. **/
program(testprog3,
        loop(pick(A,[test(predicate(A)),A]))).

/** These should all succeed! **/
test :-
        construct_characteristic_graph(testprog1),
        cg_edge(testprog1,0,action(Y),1,true,[Y],true),
        cg_edge(testprog1,1,action(Y),1,predicate(Y),[Y],true).
test2 :-
        construct_characteristic_graph(testprog2),
        (cg_edge(testprog2,0,action(Y),1,predicate(a),[Y],true);
         cg_edge(testprog2,0,action(Y),1,true,[Y],predicate(a))),
        cg_edge(testprog2,1,action(a),2,true,[],true),
        cg_edge(testprog2,2,action(Y),0,true,[],true).
test3 :-
        construct_characteristic_graph(testprog3),
        cg_edge(testprog3,0,action(Y),0,true,[Y],predicate(Y)).
