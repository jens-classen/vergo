%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Wumpus World (version with direction)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- ['../../agents/kbagent_r'].

% todo: nested functional fluents
% todo: definitions (grid, adjacency)

:- discontiguous causes_true/3.
:- discontiguous causes_false/3.
:- discontiguous rel_fluent/2.
:- discontiguous def/2.

sensing_style(truth).
include_preconditions.
progression_style(adl).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Basic Action Theory
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

initially(inDungeon).
initially(location(locWumpus)).
initially(locRobot=loc(1,1)).
initially(dirRobot=right).
initially(all(X,(isGold(X) => location(X)))).
initially(-hasGold).
initially(all(X,(isPit(X) => location(X)))).
initially(hasArrow).
initially(aliveWumpus).
initially(all(X,(visited(X) <=> X=loc(1,1)))).

rel_fluent(inDungeon,        []).
fun_fluent(locWumpus,   loc, []).
fun_fluent(locRobot,    loc, []).
fun_fluent(dirRobot,    dir, []).
rel_fluent(isGold(X),        [X - loc]).
rel_fluent(hasGold,          []).
rel_fluent(isPit(X),         [X - loc]).
rel_fluent(hasArrow,         []).
rel_fluent(aliveWumpus,      []).
rel_fluent(visited(X),       [X - loc]).

cwa(inDungeon).
cwa(hasGold).
cwa(hasArrow).
cwa(aliveWumpus).
cwa(visited(_)).
% locRobot and dirRobot are functional fluents => CWA holds

poss(smell, true).
poss(senseBreeze, true).
poss(senseGold, true).
poss(shootFwd, hasArrow).
poss(pickGold, isGold(locRobot)).
poss(moveFwd, -(inTheEdge(locRobot,dirRobot))).
poss(turn, true).
poss(climb, true).
poss(enter, true).
poss(scream, true).

causes_true(enter, inDungeon, true).
causes_false(climb, inDungeon, locRobot=loc(1,1)).

causes(moveFwd, locRobot, Y, apply(dirRobot,[locRobot,Y])).

causes(turn, dirRobot, Y, rotateRight(dirRobot,Y)).

causes_false(pickGold, isGold(L), locRobot=L).

causes_true(pickGold, hasGold, true).

causes_false(shootFwd, hasArrow, true).

causes_false(scream, aliveWumpus, true).

causes_true(moveFwd, visited(L), apply(dirRobot,[locRobot,L])).

senses(smell,adj(locRobot,locWumpus)).
senses(senseBreeze,some(X,(adj(locRobot,X)*isPit(X)))).
senses(senseGold,isGold(locRobot)).

exo(scream).
