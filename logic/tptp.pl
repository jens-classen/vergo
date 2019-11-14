
:- module(tptp).

:- export op(1130, xfy, <=>). % equivalence
:- export op(1110, xfy, =>).  % implication
:- export op(1110, xfy, <=).   % implication
:- export op( 500, fy, ~).    % negation
:- export op( 500,xfy, :).

:- export op(1100, xfy, '|').  % disjunction
:- export op(1000, xfy, &).    % conjunction
:- export op( 500, fy, !).     % universal quantifier
:- export op( 500, fy, ?).     % existential quantifier
:- export op( 400, xfx, =).    % equality
:- export op( 299, fx, $).     % for $true/$false

%:- export op(1130, xfy, <~>).  % negated equivalence
%:- export op(1100, xfy, '~|'). % negated disjunction
%:- export op(1000, xfy, ~&).   % negated conjunction
%:- export op( 300, xf, !).     % negated equality (for !=)
