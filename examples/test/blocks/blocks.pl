/**
 
Blocks World Domain for Testing

This file implements a blocks world scenario, specifically for testing
progression techniques described in the paper

Yongmei Liu and Gerhard Lakemeyer: "On First-Order Definability and
Computability of Progression for Local-Effect Actions and Beyond". In:
Proc. IJCAI 2009, AAAI Press, pp. 860–866.

@author  Jens Claßen
@license GPLv2

 **/
:- use_module('../../../kbs/l_kb').
:- use_module('../../../projection/progression').
:- use_module('../../../lib/utils').

:- discontiguous causes_true/3.
:- discontiguous causes_false/3.

initially(clear('#a')).
initially(on('#a','#b')).
initially(clear('#c')).
initially(all(X,clear(X)=>eh(X))).
initially(all([X,Y],on(X,Y)=>(-clear(Y)))).

rel_fluent(clear(_)).
rel_fluent(on(_,_)).
rel_fluent(eh(_)). % "even height"

poss(move(_,_,_),true).

causes_true(move(_Y,X,_Z),clear(X),true).
causes_false(move(_Y,_Z,X),clear(X),true).

causes_true(move(X,_Z,Y),on(X,Y),true).
causes_false(move(X,Y,_Z),on(X,Y),true).

causes_true(move(X,_Y,Z),eh(X),-eh(Z)).
causes_false(move(X,_Y,Z),eh(X),eh(Z)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Testing
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

expected_progression(clear('#a')).
expected_progression(all(X,((X='#c')+(-(X='#b'))*(-(X='#c'))*clear(X))
                           => ((X='#a')+(-(X='#a'))*eh(X)))).
expected_progression(all([X,Y],((X='#a')*(Y='#b')
                               +((-(X='#a'))+(-(Y='#b')))
                               *((-(X='#a'))+(-(Y='#c')))
                               *on(X,Y)) 
                               => (-((Y='#c')+(-(Y='#b'))*(-(Y='#c'))*
                                     clear(Y))))).
expected_progression(clear('#b')).
expected_progression(-clear('#c')).
expected_progression(-on('#a','#b')).
expected_progression(on('#a','#c')).
expected_progression(eh('#a')<=>(-eh('#c'))).

:- begin_tests('progression_local-effect').

test(progresson) :- !,
        initialize_kb(kb0),
        progress(local_effect,kb0,move('#a','#b','#c'),kb1),
        report_message(info, ['Progressed KB is:']),
        print_kb(kb1),
        check_progression(kb1).

check_progression(KB) :-
        check_kb_entails_expected_fmls(KB),
        check_expected_fmls_entail_kb(KB).

check_kb_entails_expected_fmls(KB) :-
        forall(expected_progression(Fml),
               check_kb_entails_expected_fml(KB,Fml)).

check_kb_entails_expected_fml(KB,Fml) :-
        (entails_kb(KB,Fml) -> Truth=true;Truth=false),
        report_entailment(Fml,Truth),
        assertion(entails_kb(KB,Fml)).

report_entailment(Fml,true) :-
        report_message(['Formula ', Fml,
                        ' is entailed by the progression as expected.']).
report_entailment(Fml,false) :-
        report_message(['Formula ', Fml,
                        ' is not entailed by the progression!']).

check_expected_fmls_entail_kb(KB) :-
        findall(Fml,expected_progression(Fml),Fmls),
        forall(kb_axiom(KB,Axiom),
               check_fmls_entail_axiom(Fmls,Axiom)).

check_fmls_entail_axiom(Fmls,Axiom) :-
        (entails(Fmls,Axiom) -> Truth=true;Truth=false),
        report_entailment2(Axiom,Truth),
        assertion(entails(Fmls,Axiom)).

report_entailment2(Fml,true) :-
        report_message(['KB Formula ', Fml,
                        ' is entailed by expected progression.']).
report_entailment2(Fml,false) :-
        report_message(['KB Formula ', Fml,
                        ' is not entailed by expected progression!']).

:- end_tests('progression_local-effect').
