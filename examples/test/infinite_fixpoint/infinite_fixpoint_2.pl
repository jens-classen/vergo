%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Simple Example that generates an infinite fixpoint, i.e.
% the fixpoint verification method will not terminate (the
% solution here would have to be a second-order formula that
% expresses the property that initially, there are infinitely 
% many objects on the floor, but not on the table).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- use_module('../../../verification/fixpoint_ctl').

:- discontiguous causes_true/3.
:- discontiguous causes_false/3.
:- discontiguous rel_fluent/1.

initially(some(X,(onfloor(X)*(-ontable(X))))).

rel_fluent(onfloor(_)).
rel_fluent(ontable(_)).

poss(put_on_table(_),true).

causes_false(put_on_table(X),onfloor(X),true).
causes_true(put_on_table(X),ontable(X),true).

program(main,
        while(some(X,(onfloor(X)*(-ontable(X)))),
               pick(X,[test(onfloor(X)*(-ontable(X))),
                       put_on_table(X)]))).

property(prop1,
         main,
         somepath(always(some(X,(onfloor(X)*(-ontable(X))))))).

run_infinite :-
        construct_characteristic_graph(main),
        verify(main,prop1).
