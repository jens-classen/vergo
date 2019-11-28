:- module(def, [expand_defs/2]).

:- use_module('l').
:- use_module('../lib/utils').

:- multifile user:def/2.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Macro expand defined formulas
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

expand_defs(Fml1,Fml2) :-
        nonvar(Fml1),
        user:def(Fml1,Fml3), !,
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
