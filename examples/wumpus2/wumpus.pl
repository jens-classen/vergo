%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Basic Action Theory for (simple version) of Wumpus world
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% todo: domains
% todo: CWA
% todo: definitions (grid, adjacency)
% todo: exogenous actions (howl)
% todo: shooting

:- discontiguous causes_true/3.
:- discontiguous causes_false/3.
:- discontiguous rel_fluent/1.
:- discontiguous def/2.

sensing_style(truth).
include_preconditions.

initially(inDungeon).
initially(at(room(1,1)).
initially(-hasGold).
initially(hasArrow).
initially(wumpusAlive).

% todo: initially adj

domain(loc, L) :- 
        L = room(X,Y),
        member(X,[1,2,3,4,5,6,7,8]),
        member(Y,[1,2,3,4,5,6,7,8]).
domain(dir, D) :-
        member(D, [n,w,s,e]).

prim_action(senseStench).
prim_action(senseBreeze).
prim_action(senseGold).
%prim_action(shoot(_)).   % domain: direction
prim_action(pick).
prim_action(move(_)).    % domain: direction

rel_fluent(at).
rel_fluent(wumpusAlive).
rel_fluent(hasArrow).
rel_fluent(hasGold).
rel_fluent(gold(_)).     % domain: location

rel_rigid(adj(_,_,_)).   % domains: location, direction, location
rel_rigid(pit(_)).       % domain: location
rel_rigid(wumpus(_)).    % domain: location

poss(senseStench, true).
poss(senseBreeze, true).
poss(senseGold, true).
poss(shoot, hasArrow).
poss(pick, some([X],at(X)*gold(X))).
poss(move(D), some([R1,R2],at(R1)*adj(R1,D,R2)).

causes_true(move(D), at(R2), some([R1],at(R1)*adj(R1,D,R2))).
causes_false(move(D), at(R1), at(R1)).

%causes_false(shoot(D), wumpusAlive, aimingAtWumpus(D)).
%causes_false(shoot(D), hasArrow, true).

causes_true(pick, hasGold, some([X],at(X)*gold(X))).
causes_false(pick, gold(X), at(X)).

senses(senseStench,wumpusNearby).
senses(senseBreeze,pitNearby).
senses(senseGold,some([X],at(X)*gold(X))).

def(wumpusNearby, some([R1,D,R2],at(R1)*adj(R1,D,R2)*wumpus(R2))).
def(pitNearby, some([R1,D,R2],at(R1)*adj(R1,D,R2)*pit(R2))).
%def(aimingAtWumpus(D), some([R1,R2],at(R1)*wumpus(R2)*facing(R1,D,R2))).
