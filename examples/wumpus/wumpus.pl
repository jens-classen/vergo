%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Basic Action Theory for (simple version) of Wumpus world
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% todo: domains

:- discontiguous causes_true/3.
:- discontiguous causes_false/3.
:- discontiguous rel_fluent/1.
:- discontiguous def/2.

:- dynamic grid_size/1.

sensing_style(truth).
include_preconditions.
progression_style(adl).

initially(at('#room-0-0')).
% initially(-hasGold). % by CWA
initially(hasArrow).
initially(wumpusAlive).
initially(all([X,Y],(wumpus(X)*wumpus(Y))=>(X=Y))).

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

domain(dir, D) :-
        member(D, ['#n','#w','#s','#e']).
domain(loc, L) :- 
        domain(coordinate,X),
        domain(coordinate,Y),
        atomic_list_concat(['#room', X, Y], '-', L).
domain(coordinate,X) :-
        grid_size(G),
        N is G-1,
        between(0,N,X).
        %member(X, [0,1,2]).

rel_fluent(at(_)).       % domain: location
rel_fluent(wumpusAlive).
rel_fluent(hasArrow).
rel_fluent(hasGold).
rel_fluent(gold(_)).     % domain: location

rel_rigid(adj(_,_,_)).   % domains: location, direction, location
rel_rigid(facing(_,_,_)).% domains: location, direction, location
rel_rigid(pit(_)).       % domain: location
rel_rigid(wumpus(_)).    % domain: location

cwa(at(_)).
cwa(adj(_,_,_)).
cwa(facing(_,_,_)).
cwa(hasGold).
cwa(hasArrow).
cwa(wumpusAlive).

poss(senseStench, true).
poss(senseBreeze, true).
poss(senseGold, true).
poss(shoot(_), hasArrow).                        % domain: direction
poss(pick, some([X],at(X)*gold(X))).
poss(move(D), some([R1,R2],at(R1)*adj(R1,D,R2))).% domain: direction

causes_true(move(D), at(R2), some([R1],at(R1)*adj(R1,D,R2))).
causes_false(move(_), at(R1), at(R1)).

causes_false(shoot(D), wumpusAlive, aimingAtWumpus(D)).
causes_false(shoot(_), hasArrow, true).
senses(shoot(D), wumpusAlive*aimingAtWumpus(D)).

causes_true(pick, hasGold, some([X],at(X)*gold(X))).
causes_false(pick, gold(X), at(X)).

senses(senseStench,wumpusNearby).
senses(senseBreeze,pitNearby).
senses(senseGold,some([X],at(X)*gold(X))).

def(wumpusNearby, some([R1,D,R2],at(R1)*adj(R1,D,R2)*wumpus(R2))).
def(pitNearby, some([R1,D,R2],at(R1)*adj(R1,D,R2)*pit(R2))).
def(aimingAtWumpus(D), some([R1,R2],at(R1)*wumpus(R2)*facing(R1,D,R2))).
