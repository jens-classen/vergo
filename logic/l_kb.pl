:- module(l_kb, [initialize_kb/0,
                 entails_initially/2,
                 extend_initial_kb_by/1,
                 print_kb/0]).

:- reexport(['l']).

:- use_module('cwa').
:- use_module('def').
:- use_module('l').
:- use_module('una').
:- use_module('../lib/utils').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Initialize
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

initialize_kb. % nothing to do

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Check formula against initial theory
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

entails_initially(Fml,Truth) :-
        apply_cwa(Fml,FmlP), % includes macro expansion
        entails_initially2(FmlP,Truth).

% don't call theorem prover on 'true'
entails_initially2(true,true) :- !.
% call theorem prover only on non-trivial formula
entails_initially2(Fml,Truth) :-
        findall(IniFml,
                initial_axiom(IniFml),
                KB),
        entails_l(KB,Fml, Truth), !.

initial_axiom(F) :-
        initially(F2),
        not(cwa(F2)), % CWA is compiled away from queries
        apply_cwa(F2,F3),
        apply_una(F3,F4),
        simplify(F4,F).

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
