:- module('conditional_kb', [initialize_kb/0,
                             entails_initially/2,
                             print_kb/0,
                             extend_initial_kb_by/1,
                             rank/2,
                             get_reasoner/1,
                             set_reasoner/1,
                             op(1150, xfy, ~>)]).

:- use_module('def').
:- use_module('rational_closure').
:- use_module('system_z').
:- use_module('../lib/utils').

:- dynamic(reasoner/1).

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

initialize_kb :-
        reasoner(rational_closure),
        findall((BP~>HP),
                (initially(B~>H),
                 expand_defs(B,BP),
                 expand_defs(H,HP)),
                KBCond),
        findall((true~>FmlP),
                (initially(Fml),
                 Fml \= (_~>_),
                 expand_defs(Fml,FmlP)),
                KBNonCond),
        append(KBCond,KBNonCond,KB),
        construct_ranking(KB).

initialize_kb :-
        reasoner(system_z),
        findall((BP~>HP),
                (initially(B~>H),
                 expand_defs(B,BP),
                 expand_defs(H,HP)),
                KBCond),
        findall((true~>FmlP),
                (initially(Fml),
                 Fml \= (_~>_),
                 expand_defs(Fml,FmlP)),
                KBNonCond),
        append(KBCond,KBNonCond,KB),
        construct_partition(KB).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Check formula against initial theory
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

entails_initially((B~>H),Truth) :-
        reasoner(rational_closure),
        expand_defs(B,BP),
        expand_defs(H,HP),
        rc_entails(BP,HP,Truth), !.

entails_initially(Fml,Truth) :-
        reasoner(rational_closure),
        Fml \= (_~>_),
        expand_defs(Fml,FmlP),
        rc_entails(true,FmlP,Truth), !.

entails_initially((B~>H),Truth) :-
        reasoner(system_z),
        expand_defs(B,BP),
        expand_defs(H,HP),
        one_entails(BP,HP,Truth), !.

entails_initially(Fml,Truth) :-
        reasoner(system_z),
        Fml \= (_~>_),
        expand_defs(Fml,FmlP),
        one_entails(true,FmlP,Truth), !.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Rank of a formula
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

rank(Fml,R) :-
        reasoner(rational_closure),
        rc_rank(Fml,R).

rank(Fml,R) :-
        reasoner(system_z),
        z_rank(Fml,R).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Pretty-print KB
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

print_kb :-
        reasoner(rational_closure), !,
        print_ranking.

print_kb :-
        reasoner(system_z), !,
        print_partition.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Extend initial theory by new formula
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% todo: make this optional, may be costly
extend_initial_kb_by(Fml) :-
        entails_initially(Fml,true), !.
% we need to reconstruct the partition/ranking
extend_initial_kb_by(Fml) :- !,
        assert(initially(Fml)),
        initialize_kb.
