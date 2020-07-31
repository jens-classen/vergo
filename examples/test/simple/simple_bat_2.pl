/**

simple_bat

A simple BAT, mainly for testing purposes.

@author  Jens Claßen
@license GPLv2


**/

:- ['../../../verification/abstraction_local-effect'].

:- discontiguous causes_true/3.
:- discontiguous causes_false/3.

initially(true).

rel_fluent(p).

poss(a,true).
poss(b,true).

stdname(n).

causes_true(b,p,true).
causes_false(a,p,true).

include_preconditions.

program(fin,nondet([a,a],[a,b])).


program(control,loop([a,b])).

property(prop1, 
         control,
         somepath(always(p))).

property(fin,somepath(nextstate(allpaths(nextstate(p))))
             +somepath(nextstate(allpaths(nextstate(-p))))).
