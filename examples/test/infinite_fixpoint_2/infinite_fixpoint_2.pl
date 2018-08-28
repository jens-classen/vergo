%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Simple Example that generates an infinite fixpoint, i.e.
% the fixpoint verification method will not terminate (the
% solution here would have to be a second-order formula that
% expresses the property that initially, there are infinitely 
% many objects on the floor, but not on the table).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- discontiguous causes_true/3.
:- discontiguous causes_false/3.
:- discontiguous rel_fluent/1.

initially(some(X,(onfloor(X)*(-ontable(X))))).

prim_action(put_on_table(_)).

rel_fluent(onfloor(_)).
rel_fluent(ontable(_)).

poss(put_on_table(_),true).

causes_false(put_on_table(X),onfloor(X),true).
causes_true(put_on_table(X),ontable(X),true).

%include_preconditions. % no precondition extension

program(main,
        while(some(X,(onfloor(X)*(-ontable(X)))),
               pick(X,[test(onfloor(X)*(-ontable(X))),
                       put_on_table(X)]))).

property(prop1,
         main,
         somepath(always(some(X,(onfloor(X)*(-ontable(X))))))).
