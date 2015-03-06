:- discontiguous causes_true/3.
:- discontiguous causes_false/3.

domain(machine,M) :- 
        member(M,[m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12]).
domain(type,T) :-
        member(T,[t1,t2,t3,t4,t5]).
domain(product,P)  :-
        member(P,[s0,s1,s2,p1,p2,p3]).
domain(robot,R) :-
        member(R,[r1,r2,r3]).
domain(location,L) :-
        member(L,[lm1,lm2,lm3,lm4,lm5,lm6,lm7,lm8,lm9,lm10,lm11,lm12,lr1,lr2,insertion,input,delivery]).

rel_fluent(machine_type(_,_)).
rel_fluent(machine_state(_,_)).
rel_fluent(machine_location(_,_)).
rel_fluent(machine_haspuck(_,_)).

rel_fluent(robot_location(_,_)).
rel_fluent(robot_haspuck(_,_)).



% 4x T1, 3x T2, 2x T3, 2x T4, 1x T5
initially(all([X,Y],
              machine_type(X,Y)<=>
                               ((X=m1*Y=t1)+
                                (X=m2*Y=t1)+
                                (X=m3*Y=t1)+
                                (X=m4*Y=t1)+
                                (X=m5*Y=t2)+
                                (X=m6*Y=t2)+
                                (X=m7*Y=t2)+
                                (X=m8*Y=t3)+
                                (X=m9*Y=t3)+
                                (X=m10*Y=t4)+
                                (X=m11*Y=t4)+
                                (X=m12*Y=t5)))).

initially(all([X,Y],
              machine_state(X,Y)<=>
                               ((X=m1*Y=ready)+
                                (X=m2*Y=ready)+
                                (X=m3*Y=ready)+
                                (X=m4*Y=ready)+
                                (X=m5*Y=ready)+
                                (X=m6*Y=ready)+
                                (X=m7*Y=ready)+
                                (X=m8*Y=ready)+
                                (X=m9*Y=ready)+
                                (X=m10*Y=ready)+
                                (X=m11*Y=ready)+
                                (X=m12*Y=ready)))).

initially(all([X,Y],
              machine_location(X,Y)<=>
                               ((X=m1*Y=lm1)+
                                (X=m2*Y=lm2)+
                                (X=m3*Y=lm3)+
                                (X=m4*Y=lm4)+
                                (X=m5*Y=lm5)+
                                (X=m6*Y=lm6)+
                                (X=m7*Y=lm7)+
                                (X=m8*Y=lm8)+
                                (X=m9*Y=lm9)+
                                (X=m10*Y=lm10)+
                                (X=m11*Y=lm11)+
                                (X=m12*Y=lm12)))).

initially(all[X,Y],-machine_haspuck(X,Y)).

initially(all([X,Y],
              robot_location(X,Y)<=>
                               ((X=r1*Y=insertion)+
                                (X=r2*Y=insertion)+
                                (X=r3*Y=insertion)))).

initially(all[X,Y],-robot_haspuck(X,Y)).

% macro for CWA?

% Skill: finish_puck_at
prim_action(finish_puck_at(_Robot,_Machine)).
poss(finish_puck_at(Robot,Machine)).
causes_true().
causes_false().

% % Skill: finish_puck_at_deliver =(?) deliver_puck
% prim_action().
% poss().
% causes_true().
% causes_false().

% % Skill: get_s0
% The robot drives to the insertion area, picks up a puck and then turns towards the field. 
% prim_action().
% poss().
% causes_true().
% causes_false().

% % Skill: get_produced
% prim_action().
% poss().
% causes_true().
% causes_false().

% % Skill: get_consumed
% prim_action().
% poss().
% causes_true().
% causes_false().

% % Skill: take_puck_to
% prim_action().
% poss().
% causes_true().
% causes_false().

% % Skill: drive_to
% prim_action().
% poss().
% causes_true().
% causes_false().

% % Skill: store_puck
% prim_action().
% poss().
% causes_true().
% causes_false().

% % Skill: get_stored_puck
% prim_action().
% poss().
% causes_true().
% causes_false().

% % exogenous action: order

% % exogenous action: machine downtime

% % failure: skill failure, misplaced puck (=>junk), switch of
% % delivery gates