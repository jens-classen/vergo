:- use_module(library(jpl)).

:- dynamic(wumpusworld/1).

mapdir('#n','north').
mapdir('#e','east').
mapdir('#s','south').
mapdir('#w','west').

create :-
        retractall(wumpusworld(_)),
        jpl_new('WumpusWorld',[3,3],X),
        assert(wumpusworld(X)).

do_action(move(Dir),false) :-
        wumpusworld(X),
        mapdir(Dir,JDir),
        jpl_call(X,moveAgent,[JDir],_).

do_action(pick,false) :-
        wumpusworld(X),
        jpl_call(X,grabGold,[],_).

do_action(shoot(Dir),Result) :-
        wumpusworld(X),
        mapdir(Dir,JDir),
        jpl_call(X,shoot,[JDir],@(Result)).

do_action(senseStench,Truth) :-
        wumpusworld(X),
        jpl_call(X,stench,[],@(Truth)).

do_action(senseBreeze,Truth) :-
        wumpusworld(X),
        jpl_call(X,breeze,[],@(Truth)).

do_action(senseGold,Truth) :-
        wumpusworld(X),
        jpl_call(X,glitter,[],@(Truth)).

destroy :-
        wumpusworld(X),
        jpl_call(X,setVisible,[@(false)],_).
