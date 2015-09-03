%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Basic Action Theory for Wumpus world, grid size 8x8
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% todo: domains
% todo: nested functional fluents
% todo: CWA
% todo: definitions (grid, adjacency)

:- discontiguous causes_true/3.
:- discontiguous causes_false/3.
:- discontiguous rel_fluent/1.
:- discontiguous def/2.

sensing_style(truth).
include_preconditions.

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

prim_action(smell).
prim_action(senseBreeze).
prim_action(senseGold).
prim_action(shootFwd).
prim_action(pickGold).
prim_action(moveFwd).
prim_action(turn).
prim_action(climb).
prim_action(enter).
prim_action(scream).

rel_fluent(inDungeon).
fun_fluent(locWumpus).
fun_fluent(locRobot).
fun_fluent(dirRobot).
rel_fluent(isGold(_)).  % domain: location
rel_fluent(hasGold).
rel_fluent(isPit(_)).   % domain: location
rel_fluent(hasArrow).
rel_fluent(aliveWumpus).
rel_fluent(visited(_)). % domain: location

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
