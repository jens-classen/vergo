
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
% characteristic graphs
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% graph_initial(Program,SubProgram,Phi):
%%   <SubProgram,Phi> is initial node for graph of Program.

%% graph_node(Program,SubProgram,Phi):
%%   <SubProgram,Phi> is a node in the graph of program

%% graph_edge(Program,SP1,TC1,Vars,Action,Condition,SP2,TC2):
%%   There is an edge in the graph of Program from node <SP1,TC1>
%%   with Action to <SP2,TC2>, where the variables in Vars have to 
%%   be picked and Condition is the transition condition.

:- use_module(library(graph_algorithms)).
:- use_module(library(graphviz)).

:- discontiguous(graph_initial/3).
:- discontiguous(graph_node/3).
:- discontiguous(graph_edge/8).



% test
graph_initial(?(Phi),?(Phi),Phi).
graph_node(?(Phi),?(Phi),Phi).

% primitive action
graph_initial(do(A),do(A),$false).
graph_node(do(A),do(A),$false).
graph_node(do(_A),nil,$true).
graph_edge(do(A),do(A),$false,[],A,$true,nil,$true).

% sequence
graph_initial((D1;D2),(D1;D2),Phi1 & Phi2) :- 
        graph_initial(D1,_D1I,Phi1), 
        graph_initial(D2,_D2I,Phi2).
graph_node((D1;D2),(D1p;D2I),Phi1p & Phi2) :-
        graph_initial(D2,D2I,Phi2),
        graph_node(D1,D1p,Phi1p).
graph_node((_D1;D2),D2p,Phi2p) :-
        graph_node(D2,D2p,Phi2p).
graph_edge((D1;D2),(D1p;D2),(Phi1p & Phi2),Xs,T,Psi1,(D1pp;D2),(Phi1pp & Phi2)) :-
        graph_edge(D1,D1p,Phi1p,Xs,T,Psi1,D1pp,Phi1pp),
        graph_initial(D2,_D2I,Phi2).
graph_edge((D1;D2),(D1p;D2),(Phi1p & Phi2),Xs,T,(Psi2 & Phi1p),D2p,Phi2p) :-
        graph_node(D1,D1p,Phi1p),
        graph_edge(D2,D2I,Phi2,Xs,T,Psi2,D2p,Phi2p),
        graph_initial(D2,D2I,Phi2).
graph_edge((_D1;D2),D2p,Phi2p,Xs,T,Psi,D2pp,Phi2pp) :-
        graph_node(D2,D2p,Phi2p),
        graph_edge(D2,D2p,Phi2p,Xs,T,Psi,D2pp,Phi2pp).

% nondet. choice
graph_initial((D1|D2),(D1I|D2I),(Phi1 | Phi2)) :-
        graph_initial(D1,D1I,Phi1),
        graph_initial(D2,D2I,Phi2).
graph_node((D1|D2),(D1I|D2I),(Phi1|Phi2)) :-
        graph_initial((D1|D2),(D1I|D2I),(Phi1 | Phi2)).
graph_node((D1|D2),D,F) :-
        graph_node(D1,D,F);
        graph_node(D2,D,F).
graph_edge((D1|D2),(D1I|D2I),(Phi1 | Phi2),Xs,T,Psi,D1p,Phi1p) :-
        graph_initial((D1|D2),(D1I|D2I),(Phi1 | Phi2)),
        graph_edge(D1,D1I,Phi1,Xs,T,Psi,D1p,Phi1p).
graph_edge((D1|D2),(D1I|D2I),(Phi1 | Phi2),Xs,T,Psi,D2p,Phi2p) :-
        graph_initial((D1|D2),(D1I|D2I),(Phi1 | Phi2)),
        graph_edge(D2,D2I,Phi2,Xs,T,Psi,D2p,Phi2p).
graph_edge((D1|D2),Dp,Phip,Xs,T,Psi,Dpp,Phipp) :-
        graph_edge(D1,Dp,Phip,Xs,T,Psi,Dpp,Phipp);
        graph_edge(D2,Dp,Phip,Xs,T,Psi,Dpp,Phipp).

% nondet. choice of argument
graph_initial(pi(Y,D), pi(Y,D),?[Y]:Phi) :-
        graph_initial(D,_DI,Phi).
graph_node(pi(Y,D), pi(Y,D),?[Y]:Phi) :-
        graph_initial(D,_DI,Phi).
graph_node(pi(_Y,D),Dp,Fp) :-
        graph_node(D,Dp,Fp).
graph_edge(pi(Y,D),pi(Y,D),?[Y]:Phi,[Y|Xs],T,Psi,Dp,Phip) :-
        var(Y),
        graph_initial(D,DI,Phi),
        graph_edge(D,DI,Phi,Xs,T,Psi,Dp,Phip).
graph_edge(pi(_Y,D),Dp,Phip,Xs,T,Psi,Dpp,Phipp) :-
        graph_edge(D,Dp,Phip,Xs,T,Psi,Dpp,Phipp),
        not(graph_initial(D,Dp,Phip)).

% concurrency (interleaving)
graph_initial(conc(D1,D2), conc(D1I,D2I),(Phi1 & Phi2)) :-
        graph_initial(D1,D1I,Phi1),
        graph_initial(D2,D2I,Phi2).
graph_node(conc(D1,D2),conc(D1p,D2p),(Phi1p & Phi2p)) :-
        graph_node(D1,D1p,Phi1p),
        graph_node(D2,D2p,Phi2p).
graph_edge(conc(D1,_D2), conc(D1p,D2p),(Phi1p & Phi2p),Xs,T,Psi,conc(D1pp,D2p),(Phi1pp & Phi2p)) :-
        graph_edge(D1,D1p,Phi1p,Xs,T,Psi,D1pp,Phi1pp).
graph_edge(conc(_D1,D2), conc(D1p,D2p),(Phi1p & Phi2p),Xs,T,Psi,conc(D1p,D2pp),(Phi1p & Phi2pp)) :-
        graph_edge(D2,D2p,Phi2p,Xs,T,Psi,D2pp,Phi2pp).

% iteration
graph_initial(star(D), star(D),$true).
graph_node(star(D),Dp,Fp) :-
        graph_initial(star(D),Dp,Fp).
graph_node(star(D),Dp;star(D),Phi1p) :-
        graph_node(D,Dp,Phi1p).
graph_edge(star(D),star(D),$true, Xs,T,Psi, (Dp;star(D)),Phip) :-
        graph_initial(D,DI,Phi),
        graph_edge(D,DI,Phi,Xs,T,Psi,Dp,Phip).
graph_edge(star(D),(Dp;star(D)),Phip, Xs,T,Psi, Dpp;star(D),Phipp) :-
        graph_edge(D,Dp,Phip,Xs,T,Psi,Dpp,Phipp).
graph_edge(star(D),(Dp;star(D)),Phip,Xs,T,(Psi & Phipp),star(D),$true) :-
        graph_edge(D,Dp,Phip,Xs,T,Psi,_Dpp,Phipp).

% defined constructs
def_construct(if(Phi,D1,D2),(?(Phi);D1)|(?(~Phi);D2)).
def_construct(while(Phi,D), star(?(Phi);D);?(~Phi)).
def_construct(loop(D),while($true,D)).

def_construct(executable(?(Phi)),?(Phi)).
def_construct(executable(do(A)),(?(poss(A));do(A))).
def_construct(executable(D1;D2),(D1E;D2E)) :- 
        def_construct(executable(D1),D1E),
        def_construct(executable(D2),D2E).
def_construct(executable(D1|D2),(D1E|D2E)) :- 
        def_construct(executable(D1),D1E),
        def_construct(executable(D2),D2E).
def_construct(executable(pi(Y,D)),pi(Y,DE)) :-
        def_construct(executable(D),DE).
def_construct(executable(conc(D1,D2)),conc(D1E,D2E)) :-
        def_construct(executable(D1),D1E),
        def_construct(executable(D2),D2E).
def_construct(executable(star(D)),star(DE)) :-
        def_construct(executable(D),DE).
def_construct(executable(D),DE) :- 
        def_construct(D,Def), 
        def_construct(executable(Def),DE).
def_construct(executable(D),DE) :- 
        program(D,Def),
        def_construct(executable(Def),DE).

graph_initial(D,Dp,Phip) :- def_construct(D,Def), graph_initial(Def,Dp,Phip).
graph_node(D,Dp,Phip) :- def_construct(D,Def), graph_node(Def,Dp,Phip).
graph_edge(D,Dp,Phip,Xs,T,Psi,Dpp,Phipp) :- def_construct(D,Def), graph_edge(Def,Dp,Phip,Xs,T,Psi,Dpp,Phipp).

% named programs
graph_initial(D,Dp,Phip) :- program(D,Def), graph_initial(Def,Dp,Phip).
graph_node(D,Dp,Phip) :- program(D,Def), graph_node(Def,Dp,Phip).
graph_edge(D,Dp,Phip,Xs,T,Psi,Dpp,Phipp) :- program(D,Def), graph_edge(Def,Dp,Phip,Xs,T,Psi,Dpp,Phipp).

% materialize graph: collect nodes and edges, simplify and assert
materialize_graph(D) :-
        graph(D,V0,V,E),
        materialize_nodes(D,V0,V),
        materialize_edges(D,E).

materialize_nodes(D,V0,V) :-
        subtract(V,[V0],VNI),
        materialize_node(D,V0,0),
        materialize_nodes(D,VNI,1).
materialize_nodes(D,[V|Vs],N) :-
        materialize_node(D,V,N),
        N1 is N+1,
        materialize_nodes(D,Vs,N1).
materialize_nodes(D,[],N) :-
        assert(number_of_nodes(D,N)).

materialize_node(D,gnode(Dp,Phip),N) :-
        assert(node(D,Dp,Phip,N)).

materialize_edges(D,[E|Es]):-
        materialize_edge(D,E),
        materialize_edges(D,Es).
materialize_edges(_D,[]).

materialize_edge(D,gedge(Dp,Phip,Xs,T,Psi,Dpp,Phipp)) :-
        node(D,Dp,Phip,N1),
        node(D,Dpp,Phipp,N2),
        assert(edge(D,N1,Xs,T,Psi,N2)).

dematerialize_graph(D) :-
        retract_all(node(D,_,_,_)),
        retract_all(edge(D,_,_,_,_,_)),
        retract(number_of_nodes(D,_)).

% determine graph (makes simplifications)
graph(D,V0,V,E) :-
        graph_initial(D,Di,Phi),
        simplify_node(gnode(Di,Phi),V0),
        collect_nodes_edges(D,gnode(Di,Phi),Vp,Ep),
        simplify_nodes(Vp,VS),
        simplify_edges(Ep,ES),
        prune_instances(VS,VR),
        prune_instances(ES,ES2),
        reverse(VR,V),
        eliminate_impossible_edges(ES2,E).

% collect all *reachable* nodes and edges
collect_nodes_edges(D,V0,V,E) :-
        traverse_graph(D,[V0],[],V,[],E).

traverse_graph(D,[gnode(Dp,Phip)|Vs],VVisited,V,EVisited,E) :-
        findall(Edge,
                (graph_edge(D,Dp,Phip,Xs,T,Psi,Dpp,Phipp),
                 Edge=gedge(Dp,Phip,Xs,T,Psi,Dpp,Phipp)),
                NewEdges),
        findall(Node,
                (member(gedge(Dp,Phip,Xs,T,Psi,Dpp,Phipp),NewEdges),
                 Node=gnode(Dpp,Phipp),
                 not(member(Node,VVisited)),
                 not(member(Node,[gnode(Dp,Phip)|Vs]))),
                NewNodes),
        append(Vs,NewNodes,VsNew),
        append(EVisited,NewEdges,EVisitedNew),!,
        traverse_graph(D,VsNew,[gnode(Dp,Phip)|VVisited],V,EVisitedNew,E).
traverse_graph(_D,[],V,V,E,E).            
         
simplify_nodes([V|Vs],[VS|VsS]) :-
        simplify_node(V,VS),
        simplify_nodes(Vs,VsS).
simplify_nodes([],[]).

simplify_edges([E|Es],[ES|EsS]) :-
        simplify_edge(E,ES),
        simplify_edges(Es,EsS).
simplify_edges([],[]).

simplify_node(gnode(D,F),gnode(DS,FS)) :-
        simplify_program(D,DS),
        simplify_formula(F,FS).
simplify_edge(gedge(Dp,Phip,Xs,T,Psi,Dpp,Phipp),gedge(DpS,PhipS,Xs,T,PsiS,DppS,PhippS)) :-
        simplify_node(gnode(Dp,Phip),gnode(DpS,PhipS)),
        simplify_node(gnode(Dpp,Phipp),gnode(DppS,PhippS)),
        simplify_formula(Psi,PsiS).


% remove edges having '$false' as transition condition
eliminate_impossible_edges([gedge(_Dp,_Phip,_Xs,_T,$false,_Dpp,_Phipp)|Edges],EEdges) :- !,
        eliminate_impossible_edges(Edges,EEdges).
eliminate_impossible_edges([E|Edges],[E|EEdges]) :-
        eliminate_impossible_edges(Edges,EEdges).
eliminate_impossible_edges([],[]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Graph Output
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% pretty print to standard output
pretty_print_graph(D) :-
        graph(D,V0,Vs,E),
        pretty_print_graph(D,V0,Vs,E).

pretty_print_graph(D,V0,Vs,E) :-
        % take v0 as first element
        subtract(Vs,[V0],V1),
        V = [V0|V1],
        write('\nG['), write(D), write('] = <v0,V,E>, where\n\n'),
        pretty_print_nodes(V),
        pretty_print_edges(E,V).

pretty_print_nodes(V) :-
        length(V,N), N1 is N-1,
        write('V = {v0,...,v'),
        write(N1), write('}, where \n'),
        pretty_print_nodes2(V,0).
pretty_print_nodes2([V|Vs],N) :-
        V = gnode(D,Phi),
        write('\tv'), write(N), write(' = < '),
        write(D), write(','), write(Phi), write(' >\n'),
        N1 is N+1,
        pretty_print_nodes2(Vs,N1).
pretty_print_nodes2([],_N) :-
        write('\n').

pretty_print_edges(E,V) :-
        write('E = {\t'),
        pretty_print_edges2(E,V).
pretty_print_edges2([E|Es],V) :-
        E = gedge(Dp,Phip,Xs,T,Psi,Dpp,Phipp),
        node_id(gnode(Dp,Phip),V,ID1),
        node_id(gnode(Dpp,Phipp),V,ID2),
        write(ID1), write(' ---'),
        (Xs\=[] -> (write(Xs),write(':'));true),
        write(T), 
        (Psi\=($true) -> (write('/'), write(Psi));true),
        write('---> '),
        write(ID2), write('\n\t'),
        pretty_print_edges2(Es,V).
pretty_print_edges2([],_V) :-
        write('}\n\n').

node_id(Node,V,ID) :-
        node_id2(Node,V,N),
        integer_atom(N,NA),
        concat_atoms(v,NA,ID).
node_id2(Node,[Node|_],0) :- !.
node_id2(Node,[V|Vs],N) :-
        Node\=V,!,
        node_id2(Node,Vs,N1),
        N is N1+1.

% draw graph using graphviz interface
draw_graph(D) :-
        materialize_graph(D),
        findall(e(N1,N2,(Xs,T,Psi)),
                (edge(D,N1p,Xs,T,Psi,N2p),
                 N1 is N1p + 1,
                 N2 is N2p + 1),
                Edges),
        number_of_nodes(D,N),
        make_graph(N,Edges,Graph),
        view_graph(Graph,[edge_attrs_generator:edge_attr,layout:dot]),
        dematerialize_graph(D).

edge_attr(_Graph,Edge,Attrs) :-
        Edge=e(_N1,_N2,(Xs,T,Psi)),
        (Xs=[] -> S1=""; term_to_string(Xs,S1)),
        (Psi=($true) -> S3=""; term_to_string(Psi,S3)),
        term_to_string(T,S2),
        concat_string([S1,":",S2,":",S3],S),
        %string_length(S,SLen),
        %Len is SLen / 4,
        Attrs=[label=S,len=5].

term_to_string(T, S) :-
    open(string(""), write, Stream),
    printf(Stream, "%mw", [T]),
    get_stream_info(Stream, name, S),
    close(Stream).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Simplification
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% easy simplifications using "nil"
%% simplify_program(A,B) :- var(A), !, var(B), A=B. % action variable
%% simplify_program(A,A) :- 
%%         primitive_action(A), !.
simplify_program(do(A),do(A)).
simplify_program(?($true),nil).
simplify_program(nil,nil).
simplify_program(?(F),?(FS)) :- 
        simplify_formula(F,FS).
simplify_program((D1;D2),nil) :- 
        simplify_program(D1,nil), 
        simplify_program(D2,nil), !.
simplify_program((D1;D2),D1S) :- 
        simplify_program(D2,nil),
        simplify_program(D1,D1S), !.
simplify_program((D1;D2),D2S) :- 
        simplify_program(D1,nil),
        simplify_program(D2,D2S), !.
simplify_program((D1;D2),(D1S;D2S)) :-
        simplify_program(D1,D1S),
        simplify_program(D2,D2S).
simplify_program((D1|D2),(D1S|D2S)) :- 
        simplify_program(D1,D1S), 
        simplify_program(D2,D2S).
simplify_program(pi(X,D),pi(X,DS)) :- 
        simplify_program(D,DS).
simplify_program(conc(D1,D2),conc(D1S,D2S)) :- 
        simplify_program(D1,D1S), 
        simplify_program(D2,D2S).
simplify_program(star(nil),nil) :- !.
simplify_program(star(D),star(DS)) :- 
        simplify_program(D,DS).
simplify_program(conc(D1,D2),nil) :-
        simplify_program(D1,nil),
        simplify_program(D2,nil), !.
simplify_program(conc(D1,D2),D1S) :-
        simplify_program(D2,nil),
        simplify_program(D1,D1S), !.
simplify_program(conc(D1,D2),D2S) :-
        simplify_program(D1,nil),
        simplify_program(D2,D2S), !.
simplify_program(conc(D1,D2),conc(D1S,D2S)) :-
        simplify_program(D1,D1S),
        simplify_program(D2,D2S).

simplify_program(D,DS) :- def_construct(D,Def), simplify_program(Def,DS).
simplify_program(D,DS) :- program(D,Def), simplify_program(Def,DS).

% easy simplifications using "$true" and "$false"
%simplify_formula(X=Y,$false) :- atom(X), atom(Y), X \=Y. % standard names= atoms
simplify_formula(X=Y,$true) :- X==Y,!.
simplify_formula(X=Y,$false) :- % unique names for actions
        nonvar(X), nonvar(Y),
        precondition(X,_),
        precondition(Y,_),
        X =.. [A|_], Y =.. [B|_],
        A \= B, !.
simplify_formula(X=Y,Equalities) :-
        nonvar(X), nonvar(Y),
        precondition(X,_),
        precondition(Y,_),
        X =.. [A|XArgs], Y =..[A|YArgs],!,
        make_equalities(XArgs,YArgs,Equalities).
simplify_formula(X=Y,X=Y).

%% %simplify_formula(X!=Y,$true) :- atom(X), atom(Y), X \=Y. % standard names= atoms
%% simplify_formula(X!=Y,$false) :- X==Y,!.
%% simplify_formula(X!=Y,$true) :- % unique names for actions
%%         precondition(X,_),
%%         precondition(Y,_),
%%         X =.. [A|_], Y =.. [B|_],
%%         A \= B,!.
%% simplify_formula(X!=Y,Inequalities) :-
%%         precondition(X,_),
%%         precondition(Y,_),
%%         X =.. [A|XArgs], Y =..[A|YArgs],!,
%%         make_inequalities(XArgs,YArgs,Inequalities).
%% simplify_formula(X!=Y,X!=Y).

simplify_formula(F,F) :- (isfluent(F); F=poss(_); F=exo(_); F=occ(_)),!.
simplify_formula($true,$true) :- !.
simplify_formula($false,$false) :- !.
simplify_formula(~F,$false) :-
        simplify_formula(F,$true),!.
simplify_formula(~F,$true) :-
        simplify_formula(F,$false),!.
simplify_formula(~F,~FS) :- !,
        simplify_formula(F,FS).
simplify_formula((F1&F2),$false) :- 
        simplify_formula(F1,$false);
        simplify_formula(F2,$false).
simplify_formula((F1&F2),$true) :-
        simplify_formula(F1,$true),
        simplify_formula(F2,$true), !.
simplify_formula((F1&F2),F1S) :-
        simplify_formula(F2,$true), !,
        simplify_formula(F1,F1S).
simplify_formula((F1&F2),F2S) :-
        simplify_formula(F1,$true), !,
        simplify_formula(F2,F2S).
simplify_formula((F1&F2),(F1S&F2S)) :-
        simplify_formula(F1,F1S),
        simplify_formula(F2,F2S).
simplify_formula((F1|F2),$true) :- 
        simplify_formula(F1,$true);
        simplify_formula(F2,$true).
simplify_formula((F1|F2),$false) :-
        simplify_formula(F1,$false),
        simplify_formula(F2,$false), !.
simplify_formula((F1|F2),F1) :-
        simplify_formula(F2,$false).
simplify_formula((F1|F2),F2) :-
        simplify_formula(F1,$false).
simplify_formula((F1|F2),(F1S|F2S)) :-
        simplify_formula(F1,F1S),
        simplify_formula(F2,F2S).
simplify_formula(?[]:F,FS) :- !,
        simplify_formula(F,FS).
simplify_formula(![]:F,FS) :- !,
        simplify_formula(F,FS).
simplify_formula(?_Vars:F,$true) :- 
        simplify_formula(F,$true),!.
simplify_formula(?_Vars:F,$false) :-
        simplify_formula(F,$false),!.
simplify_formula(!_Vars:F,$true) :-
        simplify_formula(F,$true),!.
simplify_formula(!_Vars:F,$false) :-
        simplify_formula(F,$false),!.
simplify_formula(?Vars:F,?Vars:FS) :-
        simplify_formula(F,FS).
simplify_formula(!Vars:F,!Vars:FS) :-
        simplify_formula(F,FS).

simplify_formula(F,FS) :- def(F,Def), simplify_formula(Def,FS).

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

