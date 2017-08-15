:- module(l_kb, [entails_initially/2,
                 extend_initial_kb_by/1,
                 print_kb/0]).

:- use_module('l').

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

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Helper predicates
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

expand_defs(Fml1,Fml2) :-
        nonvar(Fml1),
        def(Fml1,Fml3), !,
        expand_defs(Fml3,Fml2).
expand_defs(Fml1,Fml2) :-
        nonvar(Fml1),
        not(atomic(Fml1)), !,
        Fml1 =.. [Fml3|Fml4],
        expand_defs(Fml3,Fml5),
        expand_defs_list(Fml4,Fml6),
        Fml2 =.. [Fml5|Fml6].
expand_defs(Fml,Fml) :- !.

expand_defs_list([],[]) :- !.
expand_defs_list([X|Xs],[Y|Ys]) :- !,
        expand_defs(X,Y),
        expand_defs_list(Xs,Ys).
