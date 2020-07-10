/**
 
<module> Rational Closure

This module implements a non-monotonic reasoner for conditionals
according to algorithm for finite knowledge bases presented in

Daniel J. Lehmann and Menachem Magidor: "What does a conditional
knowledge base entail?" Artificial Intelligence, 55(1):1–60, 1992.

This implementation uses 'L' as base logic, i.e. first-order logic
with a countable set of standard names as the fixed universe of
discourse, of which propositional logic is a subset.

@author  Jens Claßen
@license GPLv2

 **/

:- module(rational_closure, [rc_entails/3,
                             construct_ranking/1,
                             print_ranking/0,
                             rc_rank/2,
                             op(1150, xfy, ~>)]).

/* In addition to the symbols from module 'fol', we introduce a new
   operator '~>' for defeasible, non-material implication. */

:- op(1150, xfy, ~>).

:- use_module('l').
:- use_module('../lib/utils').

:- dynamic(rcpart/2).
:- dynamic(rcmax/1).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Rational Closure
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

/**
 * rc_rank(+Fml,-Rank) is det
 *
 * Returns the numeric rank Rank of a formula Fml according to the
 * ranking induced by the conditional KB. Returns 'inf' (positive
 * infinity) in case the formula has no rank.
 */
rc_rank(Fml,R) :-
        min_non_exceptional_rank(Fml,R).

/**
 * rc_entails(+Left,+Right,-Result) is det
 *
 * Returns the truth value Result of whether the conditional
 * 'Left~>Right' is entailed by the conditional KB.
 */
rc_entails(Left,Right,true) :-
        min_non_exceptional_rank(Left,K),
        rcpart(K,Rules),
        exceptional(Left*(-Right),Rules), !.
rc_entails(_Left,_Right,false).

min_non_exceptional_rank(Fml,K) :-
        min_non_exceptional_rank(Fml,0,K).
min_non_exceptional_rank(Fml,I,K) :-
        rcpart(I,Rules),
        exceptional(Fml,Rules), !,
        I1 is I+1,
        min_non_exceptional_rank(Fml,I1,K).
min_non_exceptional_rank(Fml,K,K) :-
        rcpart(K,Rules),
        \+ exceptional(Fml,Rules), !.
min_non_exceptional_rank(_Fml,_I,K) :- !,
        K is inf.

/**
 * construct_ranking(+RuleSet) is det
 *
 * Given a list of conditionals RuleSet as KB, constructs an internal
 * representation (through dynamic predicates) of a ranking according
 * to rational closure. Prints a warning to standard output in case the
 * RuleSet does not satisfy Lehmann and Magidors admissibility criterion.
 */
construct_ranking(RuleSet) :- !,
        retractall(rcpart(_,_)),
        retractall(rcmax(_)),
        materialize(RuleSet,RuleSetM),
        assert(rcpart(0,RuleSetM)),
        construct_ranking_recursive(0).
construct_ranking_recursive(I) :-
        rcpart(I,Rules),
        exceptional_rules(RulesEx,Rules),
        length(RulesEx,LengthEx),
        length(Rules,Length),
        LengthEx < Length, !, % proper subset
        I1 is I+1,
        assert(rcpart(I1,RulesEx)),
        construct_ranking_recursive(I1).
construct_ranking_recursive(I) :- !,
        assert(rcmax(I)),
        check_admissibility(I).

check_admissibility(I) :-
        rcpart(I,[]), !.
check_admissibility(_) :- !,
        report_message(['Warning: The provided set of conditionals is not admissible!']).

exceptional_rules(RulesEx,Rules) :-
        findall((B=>H),
                (member((B=>H),Rules),
                 exceptional(B,Rules)),
                RulesEx).
exceptional(Fml,Rules) :-
        inconsistent_l([Fml|Rules],true).

materialize([],[]).
materialize([(B~>H)|Rules],[(B=>H)|RulesM]) :-
        materialize(Rules,RulesM).

/**
 * print_ranking is det
 *
 * Prints a presentation of the internal representation of the KB to
 * standard output.
 */
print_ranking :- !,
        rcpart(I,Rules),
        write(I),
        write(':\n'),
        write_readable(Rules),
        write('\n'),
        fail.
print_ranking.
