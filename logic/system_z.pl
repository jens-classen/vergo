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
                     construct_partition/1,
                     print_partition/0,
                     z_rank/2,
                     op(1150, xfy, ~>)]).

/* In addition to the symbols from module 'fol', we introduce a new
   operator '~>' for defeasible, non-material implication. */

:- op(1150, xfy, ~>).

:- use_module('l').
:- use_module('../lib/utils').

:- dynamic(zpart/2).
:- dynamic(zmax/1).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% System Z
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%TODO: zero-entailment

one_entails(Left,Right,true) :-
        z_rank(Left*Right,I1),
        z_rank(Left*(-Right),I2),
        I1 < I2, !.
one_entails(_,_,false).

z_rank(Fml,I) :- !,
        zmax(N),
        z_rank(Fml,I,N,[]).
z_rank(Fml,I,N,RuleSet1) :-
        zpart(N,RuleSetN),
        append(RuleSet1,RuleSetN,RuleSet),
        tolerates(RuleSet,Fml), !,
        N1 is N-1,
        z_rank(Fml,I,N1,RuleSet).
z_rank(_Fml,I,N,_RuleSet) :-
        zmax(N), !,
        I is inf. % infinity instead of zmax+1
z_rank(_Fml,I,N,_RuleSet) :- !,
        I is N+1.

construct_partition(RuleSet) :- !,
        retractall(zpart(_,_)),
        retractall(zmax(_)),
        materialize(RuleSet,RuleSetM),
        partition(RuleSetM,Partition),
        assert_partition(Partition).
assert_partition([]).
assert_partition([(I,Rules)|Partition]) :-
        assert(zpart(I,Rules)),
        retractall(zmax(_)),
        assert(zmax(I)),
        assert_partition(Partition).

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
        report_message(['Warning: The provided set of conditionals is not consistent!']).
% partition(_Rest,_I,_Rules) :- !,
%         report_message(['Error constructing ranking partition in System Z!']),
%         report_message(['The provided set of conditionals is not consistent!']),
%         report_message(['Aborting...']),
%         abort.

tolerated_rules(RuleSet,ToleratedRuleSet) :- !,
        findall(Rule,
                (member(Rule,RuleSet),
                 tolerates(RuleSet,Rule)),
                ToleratedRuleSet).        
tolerates(RuleSetMat,(Body=>Head)) :- !,
        conjoin([Body,Head|RuleSetMat],F),
        consistent_l([F],true).
tolerates(RuleSet,Fml) :- !,
        tolerates(RuleSet,(Fml=>true)).

materialize([],[]).
materialize([(B~>H)|Rules],[(B=>H)|RulesM]) :-
        materialize(Rules,RulesM).

print_partition :- !,
        zpart(I,Rules),
        write(I),
        write(':\n'),
        write_readable(Rules),
        write('\n'),
        fail.
print_partition.
