
:- use_module(tptp).
:- use_module(clausalform).

:- [coffee_bat_simple2].
:- [regression].
:- [characteristic_graphs].
:- [simplify].
:- [bdd].

:- use_module(library(ic)).

:- dynamic cached_label/4.

% todo: support full TPTP syntax (inequalities,...)

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Verification Algorithms
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%checkEG%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

check_label(P,I,N,BDD) :-
        cached_label(P,I,N,BDD),!.

check_label(eg(D,Phi),0,N,BDD) :-
        number_of_nodes(D,M),
        N<M,
        formula2bdd(Phi,BDD),
        assert(cached_label(eg(D,Phi),0,N,BDD)).
check_label(eg(D,Phi),I,N,BDD) :-
        I > 0, I1 is I-1,
        preimage(eg(D,Phi),I1,N,PreBDD),
        check_label(eg(D,Phi),I1,N,OldBDD),
        bdd_conjoin(PreBDD,OldBDD,BDD),
        assert(cached_label(eg(D,Phi),I,N,BDD)).

check_convergence(eg(D,Phi),I) :-
        check_convergence(eg(D,Phi),I,0).
check_convergence(eg(D,Phi),I,N) :-
        number_of_nodes(D,M),
        N < M,
        I1 is I-1,
        check_label(eg(D,Phi),I,N,BDD1),
        check_label(eg(D,Phi),I1,N,BDD2),
        BDD1 = BDD2,
        N1 is N+1,
        check_convergence(eg(D,Phi),I,N1).
check_convergence(eg(D,_Phi),_I,N) :-
        number_of_nodes(D,M),
        N=M.

preimage(eg(D,Phi),I,N,BDD) :-
        findall(edge(D,N,Xs,T,Psi,N2),edge(D,N,Xs,T,Psi,N2),Edges),
        make_disjunction(eg(D,Phi),I,Edges,BDD).

make_disjunction(eg(D,Phi),I,[edge(D,_N,Xs,T,Psi,N2)|Edges],BDD) :-
        check_label(eg(D,Phi),I,N2,N2BDD),
        bdd2formula(N2Fml,N2BDD),
        regress(?Xs:(Psi&after(T,N2Fml)),N2RFml),
        apply_una(N2RFml,N2RUFml),
        formula2bdd(N2RUFml,N2RBDD),
        make_disjunction(eg(D,Phi),I,Edges,BDD1),
        bdd_disjoin(BDD1,N2RBDD,BDD).
make_disjunction(_,_,[],0).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Testing
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

test_prop(eg(D,~(?[P]:occ(selectRequest(P))))) :- test_prog(D).
test_prog(coffee_exo_p).

%test_prop(eg(conc(simple,loop(do(wait))),~holdingCoffee)).
%test_prog(conc(simple,loop(do(wait)))).

start :- 
        test_prog(D),
        test_prop(P),
        materialize_graph(D),
        assert(it(0)),
        print_labels(P,0).

next :- 
        retract(it(I)),
        I1 is I+1,
        assert(it(I1)),
        test_prop(P),
        print_labels(P,I1).

conv  :- 
        it(I), 
        test_prop(P),
        check_convergence(P,I).

print_labels(P,I) :-
        write("[Labels in iteration "), write(I),
        write("]---------------------\n"),
        print_labels(P,I,0).
print_labels(P,I,N) :-
        test_prog(D),
        number_of_nodes(D,M),
        N < M,
        check_label(P,I,N,BDD),
        bdd2formula(Fml,BDD),
        print_label(N,Fml,BDD),
        N1 is N+1,
        print_labels(P,I,N1).
print_labels(_P,_I,M) :-
        test_prog(D),
        number_of_nodes(D,M),
        write("--------------------------------------------\n").

print_label(N,Fml,BDD) :-
        write("<"), write(N), write(","),
        write(Fml), 
        write(" ("), write(BDD), write(")"),
        write(">\n").

