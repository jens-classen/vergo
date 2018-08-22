%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Basic Action Theory for testing correct scopes of pick
% operators in the characteristic graph.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- discontiguous causes_true/3.
:- discontiguous causes_false/3.
:- discontiguous rel_fluent/1.

prim_action(action(_)).

rel_fluent(predicate(_)).

poss(action(_),true).

causes_true(action(Y),predicate(Y),true).

%include_preconditions.

program(main,
        star(pick(Y,[action(Y),test(predicate(Y))]))).

% this should succeed!
test :-
        construct_characteristic_graph(main),
        cg_edge(main,1,action(Y),1,true,[Y],predicate(Y)).
