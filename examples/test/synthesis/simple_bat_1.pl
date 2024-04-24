/**

simple_bat

A simple BAT, mainly for testing purposes.

@author  Jens Claßen
@license GPLv2

**/

:- use_module('../../../verification/synthesis_acyclic').

:- discontiguous causes_true/3.
:- discontiguous causes_false/3.

initially(p).
initially(q).

rel_fluent(p).
rel_fluent(q).

poss(a,p).
poss(b,-p).

causes_true(b,p,-p).
causes_false(a,p,p).

program(main,star([a,b])).

property(prop1,next(-p)).

property(prop2,eventually(-p)).

property(prop3,always(q)).