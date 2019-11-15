:- module('system_z_kb', [initialize_kb/0,
                          entails_initially/2,
                          print_kb/0,
                          extend_initial_kb_by/1,
                          op(1150, xfy, ~>)]).

:- use_module('def').
:- use_module('system_z').
:- use_module('../lib/utils').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Initialize
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

initialize_kb :-
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
        expand_defs(B,BP),
        expand_defs(H,HP),
        one_entails(BP,HP,Truth), !.

entails_initially(Fml,Truth) :-
        Fml \= (_~>_),
        expand_defs(Fml,FmlP),
        one_entails(true,FmlP,Truth), !.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Pretty-print KB
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

print_kb :- !,
        print_partition.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Extend initial theory by new formula
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% todo: make this optional, may be costly
extend_initial_kb_by(Fml) :-
        entails_initially(Fml,true), !.
extend_initial_kb_by(Fml) :- !,
        assert(initially(Fml)).
