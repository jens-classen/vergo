/**
 
<module> System Z

This module implements a non-monotonic reasoner for conditionals
according to the formalization described in 

Judea Pearl: "System Z: A Natural Ordering of Defaults with Tractable
Applications to Nonmonotonic Reasoning". In: Proceedings of the Third
Conference on Theoretical Aspects on Reasoning about Knowledge (TARK
1990). Morgan Kaufmann Publishers Inc., 1990, pp. 121–135.

This implementation uses 'L' as base logic, i.e. first-order logic
with a countable set of standard names as the fixed universe of
discourse, of which propositional logic is a subset.

@author  Jens Claßen
@license GPLv2

 **/

:- module(system_z, [one_entails/3,
                     construct_partition/2,
                     print_partition/1,
                     z_rank/3,
                     op(1150, xfy, ~>)]).

/* In addition to the symbols from module 'fol', we introduce a new
   operator '~>' for defeasible, non-material implication. */

:- op(1150, xfy, ~>).

:- use_module('../logic/l').
:- use_module('../lib/utils').

:- dynamic(zpart/3).
:- dynamic(zmax/2).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% System Z
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%TODO: zero-entailment

/**
 * one_entails(++KBID,+Left,+Right) is det
 *
 * Succeeds if the conditional 'Left~>Right' is 1-entailed by the
 * specified conditional KB.
 */
one_entails(KB,Left,Right) :-
        z_rank(KB,Left*Right,I1),
        z_rank(KB,Left*(-Right),I2),
        I1 < I2, !.

/**
 * z_rank(++KBID,+Fml,-Rank) is det
 *
 * Returns the numeric rank Rank of a formula Fml according to the
 * partition induced by the specified conditional KB. Returns 'inf'
 * (positive infinity) in case the formula has no rank.
 */
z_rank(KB,Fml,I) :- !,
        zmax(KB,N),
        z_rank(KB,Fml,I,N,[]).
z_rank(KB,Fml,I,N,RuleSet1) :-
        zpart(KB,N,RuleSetN),
        append(RuleSet1,RuleSetN,RuleSet),
        tolerates(RuleSet,Fml), !,
        N1 is N-1,
        z_rank(KB,Fml,I,N1,RuleSet).
z_rank(KB,_Fml,I,N,_RuleSet) :-
        zmax(KB,N), !,
        I is inf. % infinity instead of zmax+1
z_rank(_KB,_Fml,I,N,_RuleSet) :- !,
        I is N+1.

/**
 * construct_partition(++KBID,+RuleSet) is det
 *
 * Given a list of conditionals RuleSet as KB, constructs an internal
 * representation (through dynamic predicates) of a partition according
 * to System Z. Prints a warning to standard output in case the
 * RuleSet does not satisfy Pearl's consistency criterion.
 */
construct_partition(KB,RuleSet) :- !,
        retractall(zpart(KB,_,_)),
        retractall(zmax(KB,_)),
        materialize(RuleSet,RuleSetM),
        partition(RuleSetM,Partition),
        assert_partition(KB,Partition).
assert_partition(_,[]) :- !.
assert_partition(KB,[(I,Rules)|Partition]) :- !,
        assert(zpart(KB,I,Rules)),
        retractall(zmax(KB,_)),
        assert(zmax(KB,I)),
        assert_partition(KB,Partition).

partition(RuleSet,Partition) :-
        partition(RuleSet,0,Partition).
partition([],_I,[]) :- !.
partition(Rest,I,[(I,TRules)|Partition]) :-
        tolerated_rules(Rest,TRules),
        TRules \= [], !,
        setminus2(Rest,TRules,NewRest),
        I1 is I+1,
        partition(NewRest,I1,Partition).
partition(Rest,I,Rules) :- !,
        Rules = [(I,Rest)],
        report_message(warn,['Warning: The provided set of conditionals is not consistent!']).
% partition(_Rest,_I,_Rules) :- !,
%         report_message(error,['Error constructing ranking partition in System Z!']),
%         report_message(error,['The provided set of conditionals is not consistent!']),
%         report_message(error,['Aborting...']),
%         abort.

tolerated_rules(RuleSet,ToleratedRuleSet) :- !,
        findall(Rule,
                (member(Rule,RuleSet),
                 tolerates(RuleSet,Rule)),
                ToleratedRuleSet).        
tolerates(RuleSetMat,(Body=>Head)) :- !,
        conjoin([Body,Head|RuleSetMat],F),
        consistent([F]).
tolerates(RuleSet,Fml) :- !,
        tolerates(RuleSet,(Fml=>true)).

materialize([],[]).
materialize([(B~>H)|Rules],[(B=>H)|RulesM]) :-
        materialize(Rules,RulesM).

/**
 * print_partition(++KBID) is det
 *
 * Prints a presentation of the internal representation of the KB to
 * standard output.
 */
print_partition(KB) :- !,
        zpart(KB,I,Rules),
        write(I),
        write(':\n'),
        write_readable(Rules),
        write('\n'),
        fail.
print_partition.
