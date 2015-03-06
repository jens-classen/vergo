:- discontiguous causes_true/3.
:- discontiguous causes_false/3.

initially(p).

prim_action(a).
prim_action(b).

rel_fluent(p).

poss(a,p).
poss(b,-p).

causes_true(b,p,-p).
causes_false(a,p,p).

program(control,loop([a,b])).

property(prop1, somepath(always(p))).
