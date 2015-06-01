
%:- use_module(transform).
:- use_module(tptp).

:- [coffee_bat_simple2].
:- [regression].
:- [characteristic_graphs].
:- [simplify].

:- discontiguous(property/2).

:- use_module(library(ic)).
:- lib(graph_algorithms), lib(graphviz).


% todo: support full TPTP syntax (inequalities,...)

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Verification Algorithms
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%checkEG%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
checkEG_initialize(D,Phi) :-
        materialize_graph(D),
        make_labels(D,Phi,Labels),
        attach_labels(D,Labels,0).

checkEG_iteration(D,LastIteration) :-
        I is LastIteration + 1,
        preimage(D,LastIteration,PreLabels),!,
        current_labels(D,LastIteration,CurLabels),!,
        conjoin_labels(CurLabels,PreLabels,NewLabels),!,
        simplify_labels(NewLabels,NewSimpleLabels),!,
        %prune_instances(NewSimpleLabels,Labels),
        %eliminate_false_labels(NewSimpleLabels,NonfalseLabels),
        eliminate_equivalent_labels(NewSimpleLabels,DisjLabels),!,
        attach_labels(D,DisjLabels,I).

checkEG_convergence(D,Iteration) :-
        current_labels(D,Iteration,CurLabels),
        previous_labels(D,Iteration,PreLabels),
        check_counterparts(CurLabels,PreLabels),!,
        check_counterparts(PreLabels,CurLabels).

%%%%Preimage%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
preimage(D,I,PreLabels) :-
        findall((Node,(?Xs:(Psi & after(T,Phipp))),(Node,T,Path)),
                (%node(D,_Dp,_Phip,Node),
                 edge(D,Node,Xs,T,Psi,Node2),
                 label(D,Node2,Phipp,I,Path)),
                PreLabels1),
        regress_and_simplify_labellist(PreLabels1,PreLabels).


current_labels(D,I,CurLabels) :-
        findall((Node,Phi,Path),
                label(D,Node,Phi,I,Path),
                CurLabels).

previous_labels(D,I,Labels) :-
        I1 is I - 1,
        current_labels(D,I1,Labels).


regress_and_simplify_labellist([(Node,Phi,Path)|Labels],[(Node,PhiRS,Path)|Labels2]) :-
        regress_and_simplify(Phi,PhiRS),
        regress_and_simplify_labellist(Labels,Labels2).
regress_and_simplify_labellist([],[]).


regress_and_simplify(Fml1,Fml2) :-
        regress(Fml1,Fml3),
        apply_una(Fml3,Fml4),
        simplify_formula_dnf(Fml4,Fml2).

simplify_labels([],[]).
simplify_labels([(N,Phi,Path)|Labels],[(N,PhiS,Path)|SimpleLabels]) :-
        simplify_formula_dnf(Phi,PhiS),
        simplify_labels(Labels,SimpleLabels).

eliminate_equivalent_labels(Labels1,Labels2) :-
        eliminate_equivalent_labels2(Labels1,Labels2,[]).

eliminate_equivalent_labels2([Label|Labels],Labels2,SoFar) :-
        find_smallest_representative(Label,Labels,Smallest,NonequivLabels),
        eliminate_equivalent_labels2(NonequivLabels,Labels2,[Smallest|SoFar]).
eliminate_equivalent_labels2([],Labels2,Labels2).

find_smallest_representative(Label,Labels,Smallest,Nonequiv) :-
        find_smallest_representative2(Label,Labels,Smallest,Nonequiv,[]).

find_smallest_representative2((Node,Phi,Path1),[(Node,Phi2,Path2)|Labels],Smallest,Nonequiv,SoFar) :-
        all_axioms(Axioms),
        equivalent(Phi,Phi2,Axioms), !,
        smallest_formula(Phi,Phi2,Phi3),
        find_smallest_representative2((Node,Phi3,Path1 + Path2),Labels,Smallest,Nonequiv,SoFar).
find_smallest_representative2((Node,Phi,Path1),[(Node,Phi2,Path2)|Labels],Smallest,Nonequiv,SoFar) :- !,
        find_smallest_representative2((Node,Phi,Path1),Labels,Smallest,Nonequiv,[(Node,Phi2,Path2)|SoFar]).
find_smallest_representative2((Node1,Phi1,Path1),[(Node2,Phi2,Path2)|Labels],Smallest,Nonequiv,SoFar) :-
        Node1 \= Node2, !,
        find_smallest_representative2((Node1,Phi1,Path1),Labels,Smallest,Nonequiv,[(Node2,Phi2,Path2)|SoFar]).
find_smallest_representative2(Label,[],Label,Nonequiv,Nonequiv).

smallest_formula(Phi1,Phi2,Phi3) :-
        formula_size(Phi1,S1),
        formula_size(Phi2,S2),
        (S1 =< S2 -> Phi3=Phi1; Phi3=Phi2).

formula_size(Phi,S) :-
        term_string(Phi,String),
        string_list(String,List),
        length(List,S).
        
eliminate_false_labels(Labels1,Labels2) :-
        eliminate_false_labels2(Labels1,Labels2,[]).

eliminate_false_labels2([(_N,Phi,_Path)|Labels1],Labels2,SoFar) :-
        all_axioms(Axioms),
        equivalent(Phi,($false),Axioms), !,
        eliminate_false_labels2(Labels1,Labels2,SoFar).
eliminate_false_labels2([(N,Phi,Path)|Labels1],Labels2,SoFar) :-
        eliminate_false_labels2(Labels1,Labels2,[(N,Phi,Path)|SoFar]).
eliminate_false_labels2([],SoFar,SoFar).



%%%%Convergence%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
check_counterparts([(Node,Phi,_Path)|Labels],Labels2) :-
        check_counterparts2(Node,Phi,Labels2),
        check_counterparts(Labels,Labels2).
check_counterparts([],_).

check_counterparts2(Node,Phi,[(Node,Phi2,_Path)|_Labels]) :-
        all_axioms(Axioms),
        equivalent(Phi,Phi2,Axioms),!.
check_counterparts2(Node,Phi,[_Label|Labels]) :-
        check_counterparts2(Node,Phi,Labels).

conjoin_labels(Labels1,Labels2,Labels) :-
        findall((Node,(Phi1&Phi2),(Path1&Path2)),
                (member((Node,Phi1,Path1),Labels1),
                 member((Node,Phi2,Path2),Labels2)),
                Labels).

%%%%Labels%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
make_labels(D,Fml,Labels) :-
        number_of_nodes(D,N),
        make_labels2(D,Fml,0,N,Labels).
make_labels2(D,Phi,N1,N2,[(N1,Phi,N1)|Labels]) :-
        N1 < N2, !,
        N3 is N1 + 1,
        make_labels2(D,Phi,N3,N2,Labels).
make_labels2(_D,_Phi,N,N,[]).

attach_labels(D,[(N1,Phi,Path)|Labels],Iteration) :-
        assert(label(D,N1,Phi,Iteration,Path)),
        attach_labels(D,Labels,Iteration).
attach_labels(_D,[],_Iteration).

all_axioms(Axioms) :-
        findall(Axiom,axiom(Axiom),Axioms).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% CTLstar
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

property(prop1,~somepath(coffee_exp_p,until($true,occ(requestCoffee(p))&(~(until($true,occ(selectRequest(p)))))))).

collect_temporal_subforms(until(Phi1,Phi2),[until(Phi1,Phi2)|SubForms]) :- !,
        collect_temporal_subforms(Phi1,SubForms1),
        collect_temporal_subforms(Phi2,SubForms2),
        append(SubForms1,SubForms2,SubForms).
collect_temporal_subforms(next(Phi),[next(Phi)|SubForms]) :- !,
        collect_temporal_subforms(Phi,SubForms).
collect_temporal_subforms(Phi,SubForms) :-
        (Phi = (Phi1&Phi2);
         Phi = (Phi1|Phi2);
         Phi = (Phi1=>Phi2);
         Phi = (Phi1<=>Phi2)),!,
        collect_temporal_subforms(Phi1,SubForms1),
        collect_temporal_subforms(Phi2,SubForms2),
        append(SubForms1,SubForms2,SubForms).
collect_temporal_subforms(Phi,SubForms) :-
        (Phi = (~Phi1);
         Phi = (!_Vars:Phi1);
         Phi = (?_Vars:Phi1)), !,
        collect_temporal_subforms(Phi1,SubForms).
collect_temporal_subforms(_Lit,[]).

generate_local_consistency([until(Phi1,Phi2)|Temporals],[Psi1,Psi2|Consistency]) :- !,
        Psi1 = (Phi2 => until(Phi1,Phi2)),
        Psi2 = ((until(Phi1,Phi2) & (~Phi2)) => Phi1),
        generate_local_consistency(Temporals,Consistency).
generate_local_consistency([_Temporal|Temporals],Consistency) :-
        generate_local_consistency(Temporals,Consistency).
generate_local_consistency([],[]).

generate_expansion_laws([until(Phi1,Phi2)|Temporals],[Psi|Expansions]) :-
        Psi = (until(Phi1,Phi2) <=> (Phi2 | Phi1 & until_(Phi1,Phi2))),
        generate_expansion_laws(Temporals,Expansions).
generate_expansion_laws([next(Phi)|Temporals],[Psi|Expansions]) :-
        Psi = (next(Phi) <=> next_(Phi)),
        generate_expansion_laws(Temporals,Expansions).
generate_expansion_laws([],[]).

make_aux_fluents(Temporals,TempFluents) :-
        make_aux_fluents2(Temporals,TempFluents,1).

make_aux_fluents2([until(Phi1,Phi2)|Temporals],[TempFluent|TempFluents],N) :-
        integer_atom(N,NA),
        concat_atoms(u,NA,U),
        concat_atoms(up,NA,UP),
        free_variables(until(Phi1,Phi2),Vars),
        append(U,Vars,F),
        append(UP,Vars,FP),
        T =.. F,
        TP =.. FP,
        TempFluent=(until(Phi1,Phi2),T,TP),
        N1 is N + 1,
        make_aux_fluents2(Temporals,TempFluents,N1).
make_aux_fluents2([next(Phi)|Temporals],[TempFluent|TempFluents],N) :-
        integer_atom(N,NA),
        concat_atoms(x,NA,X),
        concat_atoms(xp,NA,XP),
        free_variables(next(Phi),Vars),
        append(X,Vars,F),
        append(XP,Vars,FP),
        T =.. F,
        TP =.. FP,
        TempFluent=(next(Phi),T,TP),
        N1 is N + 1,
        make_aux_fluents2(Temporals,TempFluents,N1).
make_aux_fluents2([],[],_N).



        

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Testing
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

start :- checkEG_initialize(coffee_exo_p,~(?[P]:occ(selectRequest(P)))),
        assert(it(0)), print_labels.
next  :- retract(it(N)), checkEG_iteration(coffee_exo_p,N), N1 is N+1,
        assert(it(N1)), print_labels.
conv  :- it(I), checkEG_convergence(coffee_exo_p,I).
print_labels :- it(I), coverof((N,F,P),label(coffee_exo_p,N,F,I,P),L), print_label_list(L,I).

print_label_list(Labels, I) :-
        write("[Labels in iteration "), write(I),
        write("]---------------------\n"),
        print_label_list2(Labels).
print_label_list2([Label|Labels]) :-
        print_label(Label),
        print_label_list2(Labels).
print_label_list2([]) :-
        write("--------------------------------------------\n").

print_label((N,F,_P)) :-
%%         write("At node "), write(N), write(":\n"),
%%         write(F), write("\n"),
%%         write("Paths: "), write(P), write("\n").
        write("<"), write(N), write(","),
        write(F), 
        %write(","), write(P), 
        write(">\n").


% do Action for each Goal
forall(Goal,Action):-
        Goal,
	(Action
	->	fail
	;	!,fail).
forall(_,_).
