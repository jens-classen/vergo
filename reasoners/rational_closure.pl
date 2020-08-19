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

:- module(rational_closure, [rc_entails/4,
                             construct_ranking/2,
                             print_ranking/1,
                             rc_rank/3,
                             op(1150, xfy, ~>)]).

/* In addition to the symbols from module 'fol', we introduce a new
   operator '~>' for defeasible, non-material implication. */

:- op(1150, xfy, ~>).

:- use_module('../logic/l').
:- use_module('../lib/utils').

:- dynamic(rcpart/3).
:- dynamic(rcmax/2).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Rational Closure
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

/**
 * rc_rank(++KBID,+Fml,-Rank) is det
 *
 * Returns the numeric rank Rank of a formula Fml according to the
 * ranking induced by the specified conditional KB. Returns 'inf'
 * (positive infinity) in case the formula has no rank.
 */
rc_rank(KB,Fml,R) :-
        min_non_exceptional_rank(KB,Fml,R).

/**
 * rc_entails(++KBID,+Left,+Right,-Result) is det
 *
 * Returns the truth value Result of whether the conditional
 * 'Left~>Right' is entailed by the specified conditional KB.
 */
rc_entails(KB,Left,Right,true) :-
        min_non_exceptional_rank(KB,Left,K),
        rcpart(KB,K,Rules),
        exceptional(Left*(-Right),Rules), !.
rc_entails(_KB,_Left,_Right,false).

min_non_exceptional_rank(KB,Fml,K) :-
        min_non_exceptional_rank(KB,Fml,0,K).
min_non_exceptional_rank(KB,Fml,I,K) :-
        rcpart(KB,I,Rules),
        exceptional(Fml,Rules), !,
        I1 is I+1,
        min_non_exceptional_rank(KB,Fml,I1,K).
min_non_exceptional_rank(KB,Fml,K,K) :-
        rcpart(KB,K,Rules),
        \+ exceptional(Fml,Rules), !.
min_non_exceptional_rank(_KB,_Fml,_I,K) :- !,
        K is inf.

/**
 * construct_ranking(++KBID,+RuleSet) is det
 *
 * Given a list of conditionals RuleSet as KB, constructs an internal
 * representation (through dynamic predicates) of a ranking according
 * to rational closure. Prints a warning to standard output in case the
 * RuleSet does not satisfy Lehmann and Magidors admissibility criterion.
 */
construct_ranking(KB,RuleSet) :- !,
        retractall(rcpart(KB,_,_)),
        retractall(rcmax(KB,_)),
        materialize(RuleSet,RuleSetM),
        assert(rcpart(KB,0,RuleSetM)),
        construct_ranking_recursive(KB,0).
construct_ranking_recursive(KB,I) :-
        rcpart(KB,I,Rules),
        exceptional_rules(RulesEx,Rules),
        length(RulesEx,LengthEx),
        length(Rules,Length),
        LengthEx < Length, !, % proper subset
        I1 is I+1,
        assert(rcpart(KB,I1,RulesEx)),
        construct_ranking_recursive(KB,I1).
construct_ranking_recursive(KB,I) :- !,
        assert(rcmax(KB,I)),
        check_admissibility(KB,I).

check_admissibility(KB,I) :-
        rcpart(KB,I,[]), !.
check_admissibility(_,_) :- !,
        report_message(warn,['Warning: The provided set of conditionals is not admissible!']).

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
 * print_ranking(++KBID) is det
 *
 * Prints a presentation of the internal representation of the KB to
 * standard output.
 */
print_ranking(KB) :- !,
        rcpart(KB,I,Rules),
        write(I),
        write(':\n'),
        write_readable(Rules),
        write('\n'),
        fail.
print_ranking.
