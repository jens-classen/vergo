:- module(l_kb, [entails_initially/2,
                 extend_initial_kb_by/1,
                 print_kb/0]).

:- use_module('def').
:- use_module('l').
:- use_module('../lib/utils').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Check formula against initial theory
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

entails_initially(Fml,Truth) :-
        expand_defs(Fml,FmlP),
        findall(IniFml,
                (initially(IniFml2),
                 expand_defs(IniFml2,IniFml)),
                KB),
        entails_l(KB,FmlP, Truth), !.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Pretty-print KB
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

print_kb :-
        initially(F),
        write_readable(F),
        write('\n'),
        fail.
print_kb.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Extend initial theory by new formula
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% todo: make this optional, may be costly
extend_initial_kb_by(Fml) :-
        entails_initially(Fml,true), !.
extend_initial_kb_by(Fml) :- !,
        assert(initially(Fml)).
