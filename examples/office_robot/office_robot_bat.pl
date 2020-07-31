%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Basic Action Theory for a simple robot example, as presented
% in Examples 3.26 and 3.34 from
%
% Jens Claßen: Planning and Verification in the Agent Language Golog.
% PhD Thesis, Department of Computer Science, RWTH Aachen University,
% 2013.
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- ['../../agents/kbagent_r'].

:- use_module('../../lib/utils').

% todo: numerical fluents 

initially(-some(X,holding(X))).
initially(loc('#robot')='#hallway').
initially(loc('#cup')='#kitchen').
initially(-heavy('#cup')).
initially(nextTo(office('#ann'),'#hallway') * 
          nextTo(office('#bob'),'#hallway') *
          nextTo('#kitchen','#hallway')).
initially(all(X,all(Y,nextTo(X,Y)=>nextTo(Y,X)))).
% initially((distance(office('#ann'),'#hallway')=5) *
%           (distance(office('#bob'),'#hallway')=3) *
%           (distance('#kitchen','#hallway')=4)).
% initially(all(X,all(Y,distance(X,Y)=distance(Y,X)))).
% initially(some(X,chargingStation(X)*loc(X)=office('#bob'))).
initially(person('#ann')).
initially(person('#bob')).
initially(room(office('#ann')) * 
          room(office('#bob')) *
          room('#kitchen')).
initially(all(X,room(X)=>location(X))).

rel_fluent(holding(_)).
fun_fluent(loc(_)).
% fun_fluent(energy).

rel_rigid(heavy(_)).
rel_rigid(nextTo(_,_)).
% fun_rigid(distance(_,_)).
% rel_rigid(chargingStation(_)).
rel_rigid(office(_)).
rel_rigid(person(_)).
rel_rigid(room(_)).
rel_rigid(location(_)).

poss(goto(Y),    location(Y)*nextTo(loc('#robot'),Y)).
poss(pickup(Y),  some(X,(loc(Y)=X)*(loc('#robot')=X)) *
                 -some(X,holding(X)) *
                 -heavy(Y)).
poss(putdown(Y), holding(Y)).
% poss(recharge,   some(X,rechargingStation(X)*(loc(X)=loc('#robot'))).
% poss(A,          (energy > 0)).

causes(goto(Y),loc(X),Y,(X='#robot')+holding(X)).

causes_true(pickup(Y),holding(X),(X=Y)).
causes_false(putdown(Y),holding(X),(X=Y)).

% causes(goto(X),energy,Y,(Y=energy-3*distance(X,loc('#robot')))).
% causes(pickup(X),energy,Y,(Y=energy-10)).
% causes(putdown(X),energy,Y,(Y=energy-10)).
% causes(recharge,energy,Y,(Y=100).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Testing
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

expect(1, [], -holding('#cup'), true).
expect(2, [], poss(pickup('#cup')), false).
expect(3, [], poss(goto(loc('#cup'))), true).
expect(4, [goto(loc('#cup'))], (loc('#robot')='#kitchen'), true).
% expect(5, [goto(loc('#cup'))], (energy=38), true).
expect(6, [goto(loc('#cup'))], poss(pickup('#cup')), true).
expect(7, [goto(loc('#cup')), pickup('#cup')], holding('#cup'), true).

check(History, Query, Outcome) :-
        report_message(['Querying ask(after(', History, ',', Query,
                        ')...']),
        ask(after(History,Query), ActualOutcome),
        report_message(['  Expected Outcome: ', Outcome]),
        report_message(['  Actual   Outcome: ', ActualOutcome]),
        report_message([]),
        ActualOutcome = Outcome.

:- begin_tests(regression).

test(all) :-
        init,
        forall(expect(_P,H,Q,O),check(H,Q,O)).

:- end_tests(regression).
