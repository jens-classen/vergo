:- discontiguous(regress/3).
:- discontiguous(apply_una/2).

:- use_module(tptp).
:- use_module(clausalform).

:- [verification].
%:- [coffee_bat_simple].
%:- [regression].
%:- [characteristic_graphs].
%:- [simplify].

:- dynamic label/3.
:- dynamic loop/1.
:- dynamic iteration/1.
:- dynamic new_label/0.

:- dynamic pre/5.
:- dynamic pre1_cached/5.
:- dynamic pre2/1.
:- dynamic pre3/3.

loccons1(occ(selectRequest(p))=>u1).
loccons2((occ(requestCoffee(p))&(~(u1)))=>u2).
loccons(L1 & L2) :- loccons1(L1), loccons2(L2).

trans1(u1 <=> (occ(selectRequest(p))|u1p)).
trans2(u2 <=> ((occ(requestCoffee(p))&(~(u1)))|u2p)).
trans(T1 & T2) :- trans1(T1), trans2(T2).

accept1((~u1)|occ(selectRequest(p))).
accept2((~u2)|(occ(requestCoffee(p))&(~u1))).
accall(accept1 & accept2).

regress([_],u1,u1p).
regress([_],u2,u2p).
regress([],u1,u1).
regress([],u2,u2).
regress([],u1p,u1p).
regress([],u2p,u2p).

%% regress([A],accept1,((accept1|Acc1)&(~AccAll))) :- accept1(XAcc1),
%%         regress([A],XAcc1,Acc1), accall(AccAll).
%% regress([A],accept2,((accept2|Acc2)&(~AccAll))) :- accept2(XAcc2),
%%         regress([A],XAcc2,Acc2), accall(AccAll).
regress([A],accept1,Acc1|(accept1 & (~AccAll))) :- accept1(XAcc1),
        regress([A],XAcc1,Acc1), accall(AccAll).
regress([A],accept2,Acc2|(accept2 & (~AccAll))) :- accept2(XAcc2),
        regress([A],XAcc2,Acc2), accall(AccAll).
regress([],accept1,accept1).
regress([],accept2,accept2).


apply_una(u1,u1).
apply_una(u2,u2).
apply_una(u1p,u1p).
apply_una(u2p,u2p).
apply_una(accept1,accept1).
apply_una(accept2,accept2).

checkLTL_initialize(D,_Phi) :-
        materialize_graph(D),
        loccons(LocCons),
        accall(AccAll),
        simplify_formula_dnf(LocCons&(~AccAll),Fml),
        make_labels(D,Fml,Labels),
        attach_labels(D,Labels,0).

go :- init, iterate.

iterate :- step, check_conv.

check_conv :- loop(1), converged, !,
        writeln("---------------------"),
        writeln("Switching to 2nd loop"),
        writeln("---------------------"),
        retract(loop(1)),
        assert(loop(2)),
        iterate.
check_conv :- loop(2), converged,
        writeln("---------------------"),
        writeln("2nd loop converged!  "),
        writeln("---------------------"),
        iteration(I),
        label(I,0,F),
        writeln("Resulting formula is:"),
        simplify_formula_dnf(u2=>F,F1),
        writeln(F1).
check_conv :- iterate.

init :- writeln("Initializing..."),
        materialize_graph(coffee_exo_p), assert(iteration(0)),
        assert(loop(1)), init_labels.

init_labels :-
        findall(Node,node(coffee_exo_p,_,_,Node),Nodes),
        loccons(LocCons),
        accall(AccAll),
        simplify_formula_dnf(LocCons&AccAll,Fml),
        init_labels(Nodes,Fml).
init_labels([Node|Nodes],Fml) :-
        assert_label(0,Node,Fml),
        init_labels(Nodes,Fml).
init_labels([],_).
        
step :- retract(iteration(I)), Iteration is I+1,
        assert(iteration(Iteration)),
        write("Entering iteration "),
        write(Iteration),
        write("... ------------------------------------------\n"),
        step_labels(Iteration),
        garbage_collect,
        combine_labels(Iteration). %experimental!

converged :- iteration(I), I1 is I-1,
        all_axioms(Axioms),
        label(I,0,F1),
        label(I1,0,F2),
        label(I,1,F3),
        label(I1,1,F4),
        label(I,2,F5),
        label(I1,2,F6),
        equivalent(F1,F2,Axioms),
        equivalent(F3,F4,Axioms),
        equivalent(F5,F6,Axioms).


step_labels(Iteration) :-
        loop(1),!,
        I is Iteration-1,
        %assert((label(Iteration,Node,Fml) :- label(I,Node,Fml))),
        forall(label(I,Node,Fml),assert(label(Iteration,Node,Fml))),
        findall((Node2,Xs,T,Psi,Node3,Fml2),
                (edge(coffee_exo_p,Node2,Xs,T,Psi,Node3),
                 label(I,Node3,Fml2)),
                EdgeLabels),
        retractall(new_label),
        step_labels2(Iteration,EdgeLabels).

step_labels(Iteration) :-
        loop(2),!,
        I is Iteration-1,
        findall((Fml1,Node1,Xs,T,Psi,Node2,Fml2),
                (edge(coffee_exo_p,Node1,Xs,T,Psi,Node2),
                 label(I,Node2,Fml2),
                 label(I,Node1,Fml1)),
                LabelEdgeLabels),
        step_labels3(Iteration,LabelEdgeLabels).

step_labels2(Iteration,[(Node,Xs,T,Psi,Node2,Fml)|EdgeLabels]) :-
        write("creating label for "),
        write((Node,T,Node2)), write("\n"), flush(output),
        pre(Xs,T,Psi,Fml,Fml2),!,
        assert_label(Iteration,Node,Fml2),
        step_labels2(Iteration,EdgeLabels).
step_labels2(_,[]).

step_labels3(Iteration,[(Fml1,Node1,Xs,T,Psi,Node2,Fml2)|LabelEdgeLabels]) :-
        write("creating label for "),
        write((Node1,T,Node2)), write("\n"), flush(output),
        pre(Xs,T,Psi,Fml2,Fml3),!,
        Fml4 = (Fml1 & Fml3),
        simplify_formula_dnf(Fml4,Fml5),
        assert_label(Iteration,Node1,Fml5),
        step_labels3(Iteration,LabelEdgeLabels).
step_labels3(_,[]).


assert_label(Iteration,Node,Fml) :-
        label(Iteration,Node,Fml2),
        all_axioms(Axioms),
        equivalent(Fml,Fml2,Axioms),
        write("Equivalent label exists already! ... "),
        assert_label_smallest(Iteration,Node,Fml,Fml2).
%%         retract(label(Iteration,Node,Fml2)),
%%         smallest_formula(Fml,Fml2,Fml3),
%%         assert(label(Iteration,Node,Fml3)),
%%         writeln("Retracted equivalent formula!").
assert_label(Iteration,Node,Fml) :-
        writeln("Added new label."),
        writeln((Node,Fml)),
        assert(label(Iteration,Node,Fml)),!,
        assert(new_label).

assert_label_smallest(Iteration,Node,Fml,Fml2) :-
        formula_size(Fml,S1),
        formula_size(Fml2,S2),
        S2 =< S1,!,
        write(" Keeping existing one.\n").
assert_label_smallest(Iteration,Node,Fml,Fml2) :-
        retract(label(Iteration,Node,Fml2)),
        assert(label(Iteration,Node,Fml)),
        writeln(" Using new one.\n").

%% label_loop1(Node,Fml,0) :-
%%         node(coffee_exo_p,_Dp,_Phip,Node),
%%         loccons(LocCons),
%%         accall(AccAll),
%%         simplify_formula_dnf(LocCons&(~AccAll),Fml).
%% 
%% label_loop1(Node,Fml,Iteration) :-
%%         Iteration > 0,
%%         I is Iteration - 1,
%%         label_loop1(Node,Fml,I).
%% 
%% label_loop1(Node,Fml,Iteration) :-
%%         Iteration > 0,
%%         I is Iteration - 1,
%%         edge(coffee_exo_p,Node,Xs,T,Psi,Node2),
%%         label_loop1(Node2,Fml2,I),
%%         pre(Xs,T,Psi,Fml2,Fml).
%% 
%% label_loop2(Node,Fml,Iteration) :-
%%         conv_loop1(Iteration),
%%         label_llop1(Node,Fml,Iteration).



pre(Xs,T,Psi,Fml2,Fml) :-
        pre1(Xs,T,Psi,Fml2,Fml5),
        pre2(Fml8),
        pre3(Fml5,Fml8,Fml).

pre1(Xs,T,Psi,Fml2,Fml5) :- var(T),
        pre1_cached(Xs,var(T),Psi,Fml2,Fml5).
pre1(Xs,T,Psi,Fml2,Fml5) :- nonvar(T),
        pre1_cached(Xs,T,Psi,Fml2,Fml5).

pre1(Xs,T,Psi,Fml2,Fml5) :-
        regress((?Xs:(Psi & after(T,Fml2))),Fml3),
        apply_una(Fml3,Fml4),
        simplify_formula_dnf(Fml4,Fml5),%,
        cache_pre1(Xs,T,Psi,Fml2,Fml5).
pre2(Fml8) :-
        trans(Trans),
        regress(Trans,Fml6),
        apply_una(Fml6,Fml7),
        simplify_formula_dnf(Fml7,Fml8),
        cache(pre2(Fml8)).
pre3(Fml5,Fml8,Fml) :-
        loccons(LocCons),
        elim([u1p,u2p],LocCons&(Fml8&Fml5),Fml9),
        simplify_formula_dnf(Fml9,Fml),
        cache(pre3(Fml5,Fml8,Fml)).

cache(Goal) :- asserta(Goal).

cache_pre1(Xs,T,Psi,Fml2,Fml5) :-
        nonvar(T),!,
        cache(pre1_cached(Xs,T,Psi,Fml2,Fml5)).
cache_pre1(Xs,T,Psi,Fml2,Fml5) :-
        var(T),!,
        cache(pre1_cached(Xs,var(T),Psi,Fml2,Fml5)).

combine_labels(Iteration) :-
        findall((I,N,F),(label(I,N,F),
                         I=Iteration),
                CurrentLabels),
        retractall(label(Iteration,_,_)),
        generate_empty_labels(Iteration),
        combine_labels2(CurrentLabels).
combine_labels2([(I,N,F1)|Labels]) :-
        retract(label(I,N,F2)),
        simplify_formula_dnf(F1|F2,F3),
        assert(label(I,N,F3)),
        combine_labels2(Labels).
combine_labels2([]).
   
        
generate_empty_labels(Iteration) :-
        findall(N,node(coffee_exo_p,_,_,N),Nodes),
        generate_empty_labels2(Iteration,Nodes).
generate_empty_labels2(Iteration,[N|Nodes]) :-
        assert(label(Iteration,N,$false)),
        generate_empty_labels2(Iteration,Nodes).
generate_empty_labels2(_,[]).





checkLTL_iterate1(D,LastIteration) :-
        I is LastIteration + 1,
        preimage_ltl(D,LastIteration,PreLabels),
        current_labels(D,LastIteration,CurLabels),
        append(CurLabels,PreLabels,NewLabels),
        simplify_labels(NewLabels,NewSimpleLabels),
        prune_instances(NewSimpleLabels,Labels),
        eliminate_false_labels(Labels,NonfalseLabels),
        eliminate_equivalent_labels(NonfalseLabels,DisjLabels),
        attach_labels(D,DisjLabels,I).

checkLTL_iterate2(D,LastIteration) :-
        I is LastIteration + 1,
        preimage_ltl(D,LastIteration,PreLabels),
        current_labels(D,LastIteration,CurLabels),
        conjoin_labels(CurLabels,PreLabels,NewLabels),
        simplify_labels(NewLabels,NewSimpleLabels),
        prune_instances(NewSimpleLabels,Labels),
        eliminate_false_labels(Labels,NonfalseLabels),
        eliminate_equivalent_labels(NonfalseLabels,DisjLabels),
        attach_labels(D,DisjLabels,I).

checkLTL_convergence(D,Iteration) :-
        current_labels(D,Iteration,CurLabels),
        previous_labels(D,Iteration,PreLabels),
        check_counterparts(CurLabels,PreLabels),
        check_counterparts(PreLabels,CurLabels).

preimage_ltl(D,I,PreLabels) :-
        trans(Trans),
        loccons(LocCons),
        findall((Node,(LocCons&Trans&(?Xs:(Psi & after(T,Phipp)))),(Node,T,Path)),
                (node(D,_Dp,_Phip,Node),
                 edge(D,Node,Xs,T,Psi,Node2),
                 label(D,Node2,Phipp,I,Path)),
                PreLabels1),
        elim_regress_simpl_labels(PreLabels1,PreLabels).

elim_regress_simpl_labels([(Node,Phi,Path)|Labels],[(Node,PhiRS,Path)|Labels2]) :-
        elim_regress_simpl(Phi,PhiRS),
        elim_regress_simpl_labels(Labels,Labels2).
elim_regress_simpl_labels([],[]).



elim_regress_simpl(Fml1,Fml2) :-
        regress(Fml1,Fml3),
        apply_una(Fml3,Fml4),
        simplify_formula_dnf(Fml4,Fml5),
        elim([u1p,u2p],Fml5,Fml6),
        simplify_formula_dnf(Fml6,Fml2).

