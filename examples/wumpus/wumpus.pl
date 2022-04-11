%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Wumpus World (simple version without direction)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% agent
:- use_module('../../agents/kbagent').

% simulator
:- ['wumpus_sim'].

:- discontiguous causes_true/3.
:- discontiguous causes_false/3.
:- discontiguous rel_fluent/1.
:- discontiguous def/2.

:- dynamic grid_size/1.

grid_size(3). % default for testing, overwritten in main file

sensing_style(truth).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Basic Action Theory
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

initially(at('#room-0-0')).
initially(-wumpus('#room-0-0')).
initially(-pit('#room-0-0')).
% initially(-hasGold). % by CWA
initially(hasArrow).
initially(wumpusAlive).
initially(all_t([X-loc,Y-loc],(wumpus(X)*wumpus(Y))=>(X=Y))).

initially(adj(R1,D,R2)) :-
        domain(coordinate,X1),
        domain(coordinate,X2),
        domain(coordinate,Y1),
        domain(coordinate,Y2),
        ((D = '#n', X2 is X1, Y2 is Y1+1);
         (D = '#w', X2 is X1-1, Y2 is Y1);
         (D = '#s', X2 is X1, Y2 is Y1-1);
         (D = '#e', X2 is X1+1, Y2 is Y1)),
        atomic_list_concat(['#room', X1, Y1], '-', R1),
        atomic_list_concat(['#room', X2, Y2], '-', R2).

initially(facing(R1,D,R2)) :-
        initially(adj(R1,D,R2)).
initially(facing(R1,D,R2)) :-
        initially(adj(R1,D,R3)),
        initially(facing(R3,D,R2)).

type(dir).
type(loc).

domain(dir,D) :-
        member(D, ['#n','#w','#s','#e']).
domain(loc,L) :-
        domain(coordinate,X),
        domain(coordinate,Y),
        atomic_list_concat(['#room', X, Y], '-', L).
domain(coordinate,X) :-
        grid_size(G),
        N is G-1,
        between(0,N,X).

rel_fluent(at(X),       [X-loc]).
rel_fluent(wumpusAlive, []).
rel_fluent(hasArrow,    []).
rel_fluent(hasGold,     []).
rel_fluent(gold(X),     [X-loc]).

rel_rigid(adj(X,Y,Z),    [X-loc,Y-dir,Z-loc]).
rel_rigid(facing(X,Y,Z), [X-loc,Y-dir,Z-loc]).
rel_rigid(pit(X),        [X-loc]).
rel_rigid(wumpus(X),     [X-loc]).

cwa(at(_)).
cwa(adj(_,_,_)).
cwa(facing(_,_,_)).
cwa(hasGold).
cwa(hasArrow).
cwa(wumpusAlive).

poss(senseStench, [],      true).
poss(senseBreeze, [],      true).
poss(senseGold,   [],      true).
poss(shoot(X),    [X-dir], hasArrow).
poss(pick,        [],      some_t([X-loc],at(X)*gold(X))).
poss(move(D),     [D-dir], some_t([R1-loc,R2-loc],at(R1)*adj(R1,D,R2))).

causes_true(move(D), at(R2), some_t([R1-loc],at(R1)*adj(R1,D,R2))).
causes_false(move(_), at(R1), at(R1)).

causes_false(shoot(D), wumpusAlive, aimingAtWumpus(D)).
causes_false(shoot(_), hasArrow, true).
senses(shoot(D), wumpusAlive*aimingAtWumpus(D)).

causes_true(pick, hasGold, some_t([X-loc],at(X)*gold(X))).
causes_false(pick, gold(X), at(X)).

senses(senseStench,wumpusNearby).
senses(senseBreeze,pitNearby).
senses(senseGold,some_t([X-loc],at(X)*gold(X))).

def(wumpusNearby,some_t([R1-loc,D-dir,R2-loc],at(R1)*adj(R1,D,R2)*wumpus(R2))).
def(pitNearby,some_t([R1-loc,D-dir,R2-loc],at(R1)*adj(R1,D,R2)*pit(R2))).
def(aimingAtWumpus(D),some_t([R1-loc,R2-loc],at(R1)*wumpus(R2)*facing(R1,D,R2))).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Top-Level
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

initialize :-
        initialize(3).

initialize(GridSize) :-
        retractall(grid_size(_)),
        assert(grid_size(GridSize)),
        create,             % wumpus_sim
        init(progression).  % kbagent

% todo: what if action not possible? (Java exception, sensing result?)
perform(Action) :-
        ask(poss(Action),true),
        do_action(Action,SensingResult),  % wumpus_sim
        execute(Action,SensingResult).    % kbagent

finalize :-
        destroy.
