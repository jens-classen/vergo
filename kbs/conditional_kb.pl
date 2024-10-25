/**

<module> Knowledge Base under Conditional Base Logic

This module encapsulates a data structure for managing and accessing a
single or multiple knowledge bases whose formulas are conditionals
(Pearl's System Z, Lehmann and Magidor's Rational Closure).

Knowledge bases are identified through a unique identifier that be can
be any fully grounded Prolog term, e.g. a name such as 'kb1'.

@author  Jens Claßen
@license GPLv2

*/
:- module('conditional_kb', [initialize_kb/1,
                             entails_kb/2,
                             print_kb/1,
                             rank/3,
                             get_reasoner/1,
                             set_reasoner/1,
                             op(1150, xfy, ~>)]).

:- use_module('../logic/def').
:- use_module('../reasoners/rational_closure').
:- use_module('../reasoners/system_z').
:- use_module('../lib/utils').

:- dynamic(reasoner/1).
:- dynamic user:initially/1.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Reasoner
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% default: Rational Closure
reasoner(rational_closure).
%reasoner(system_z).

set_reasoner(X) :-
        member(X,[rational_closure,system_z]), !,
        retract(reasoner(_)),
        assert(reasoner(X)).

get_reasoner(X) :-
        reasoner(X).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Initialize
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

/**
  * initialize_kb(++KBID) is det.
  *
  * Initializes a new knowledge base from facts provided by means of
  * the initially/1 predicate in user space, usually as part of a
  * basic action theory. If a knowledge base with the specified
  * identifier already exists, it will be overwritten.
  *
  * @arg KBID the identifier (handle) to be used for the KB, must be a
  *           ground term
 **/
initialize_kb(KBID) :-
        reasoner(rational_closure), !,
        findall((BP~>HP),
                (user:initially(B~>H),
                 expand_defs(B,BP),
                 expand_defs(H,HP)),
                KBCond),
        findall((true~>FmlP),
                (initially(Fml),
                 Fml \= (_~>_),
                 expand_defs(Fml,FmlP)),
                KBNonCond),
        append(KBCond,KBNonCond,KB),
        construct_ranking(KBID,KB).

initialize_kb(KBID) :-
        reasoner(system_z), !,
        findall((BP~>HP),
                (user:initially(B~>H),
                 expand_defs(B,BP),
                 expand_defs(H,HP)),
                KBCond),
        findall((true~>FmlP),
                (initially(Fml),
                 Fml \= (_~>_),
                 expand_defs(Fml,FmlP)),
                KBNonCond),
        append(KBCond,KBNonCond,KB),
        construct_partition(KBID,KB).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Check formula against initial theory
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

/**
  * entails_kb(++KBID,+Fml) is det.
  *
  * Succeeds iff the provided formula is entailed in conditional logic
  * by the given knowledge base.
  *
  * @arg KBID  the identifier (handle) of the KB in question, must be
  *            a ground term
  * @arg Fml   a term representing a formula (may be a conditional)
 **/
entails_kb(KB,(B~>H)) :-
        reasoner(rational_closure),
        expand_defs(B,BP),
        expand_defs(H,HP),
        rc_entails(KB,BP,HP), !.

entails_kb(KB,Fml) :-
        reasoner(rational_closure),
        Fml \= (_~>_),
        expand_defs(Fml,FmlP),
        rc_entails(KB,true,FmlP), !.

entails_kb(KB,(B~>H)) :-
        reasoner(system_z),
        expand_defs(B,BP),
        expand_defs(H,HP),
        one_entails(KB,BP,HP), !.

entails_kb(KB,Fml) :-
        reasoner(system_z),
        Fml \= (_~>_),
        expand_defs(Fml,FmlP),
        one_entails(KB,true,FmlP), !.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Rank of a formula
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

/**
  * rank(++KBID,+Fml,-Rank) is det.
  *
  * Returns the rank of the provided formula for the specified
  * knowledge base.
  *
  * @arg KBID the identifier (handle) of the KB in question, must be
  *           a ground term
  * @arg Fml  a term representing a formula
  * @arg Rank a numerical rank
 **/
rank(KB,Fml,R) :-
        reasoner(rational_closure),
        rc_rank(KB,Fml,R).

rank(KB,Fml,R) :-
        reasoner(system_z),
        z_rank(KB,Fml,R).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Pretty-print KB
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

/**
  * print_kb(++KBID) is det.
  *
  * Pretty-prints the knowledge base with the given identifier to
  * standard output.
  *
  * @arg KBID the identifier (handle) of the KB in question, must be
  *           a ground term
 **/
print_kb(KB) :-
        reasoner(rational_closure), !,
        print_ranking(KB).

print_kb(KB) :-
        reasoner(system_z), !,
        print_partition(KB).
