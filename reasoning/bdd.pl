/**
 
<module> BDD representation module

This module implements a representation and simplification mechanism
for propositional formulas based on (ordered) binary decision diagrams
(BDD).

The construction and manipulation algorithms used herein are based
upon the ITE algorithm described in

Karl S. Brace, Richard L. Rudell, and Randal E. Bryant. Efficient
implementation of a BDD package. In Richard C. Smith, editor,
Proceedings of the Twenty-Seventh ACM/IEEE Design Automation
Conference (DAC 1990), pages 40–45. IEEE Computer Society Press, 1990.

Instead of a hash table, facts of the (dynamic) predicate bdd_node/4
are used to store nodes. Prolog's built-in term order is used for
ordering nodes.

@author  Jens Claßen
@license GPL

 **/

:- module(bdd, [minimize2ite/2,
                minimize2dnf/2,
                minimize2cnf/2]).

:- use_module('../reasoning/fol').
:- use_module('../lib/utils').

%:- use_module(library(graph_algorithms)).
%:- use_module(library(graphviz)).

:- dynamic bdd_node/4. % table entries
:- dynamic nodes/1.    % highest table index
:- dynamic cached_ite/4.

nodes(1).

bdd_node('___undef','___undef','___undef',0).
bdd_node('___undef','___undef','___undef',1).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% BDD Construction
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% minimize using BDDs
minimize2ite(Fml1,Fml2) :- !,
        formula2bdd(Fml1,BDD),
        bdd2formula(BDD,Fml2).

minimize2dnf(Fml1,Fml2) :- !,
        formula2bdd(Fml1,BDD),
        bdd2dnf(BDD,Fml2).

minimize2cnf(Fml1,Fml2) :- !,
        formula2bdd(Fml1,BDD),
        bdd2cnf(BDD,Fml2).

% formula to BDD
formula2bdd(true,1) :- !.
formula2bdd(false,0) :- !.
formula2bdd(-true,0) :- !.
formula2bdd(-false,1) :- !.
formula2bdd(Fml,BDD) :-
        bdd_atom(Fml), !,
        find_or_add_unique(Fml,1,0,BDD).
formula2bdd(Fml1<=>Fml2,BDD) :- !,
        formula2bdd(Fml1,BDD1),
        formula2bdd(Fml2,BDD2),
        formula2bdd(-Fml2,BDD3),
        ite(BDD1,BDD2,BDD3,BDD).
formula2bdd(Fml1=>Fml2,BDD) :- !,
        formula2bdd(Fml1,BDD1),
        formula2bdd(Fml2,BDD2),
        ite(BDD1,BDD2,1,BDD).
formula2bdd(Fml1<=Fml2,BDD) :- !,
        formula2bdd(Fml1,BDD1),
        formula2bdd(-Fml2,BDD2),
        ite(BDD1,1,BDD2,BDD).
formula2bdd(-Fml1,BDD) :- !,
        formula2bdd(Fml1,BDD1),
        ite(BDD1,0,1,BDD).
formula2bdd(Fml1+Fml2,BDD) :- !,
        formula2bdd(Fml1,BDD1),
        formula2bdd(Fml2,BDD2),
        ite(BDD1,1,BDD2,BDD).
formula2bdd(Fml1*Fml2,BDD) :- !,
        formula2bdd(Fml1,BDD1),
        formula2bdd(Fml2,BDD2),
        ite(BDD1,BDD2,0,BDD).

% BDD to if-then-else formula
bdd2formula(0,false) :- !.
bdd2formula(1,true) :- !.
bdd2formula(BDD,Fml) :-
        bdd_node(Fml,1,0,BDD),!.
bdd2formula(BDD,-Fml) :-
        bdd_node(Fml,0,1,BDD),!.
bdd2formula(BDD,Fml2+FmlE) :-
        bdd_node(Fml2,1,E,BDD),!,
        bdd2formula(E,FmlE).
bdd2formula(BDD,(-Fml2)*FmlE) :-
        bdd_node(Fml2,0,E,BDD),!,
        bdd2formula(E,FmlE).
bdd2formula(BDD,FmlT+(-Fml2)) :-
        bdd_node(Fml2,T,1,BDD),!,
        bdd2formula(T,FmlT).
bdd2formula(BDD,Fml2*FmlT) :-
        bdd_node(Fml2,T,0,BDD),!,
        bdd2formula(T,FmlT).
bdd2formula(BDD,(Fml3*Fml1)+((-Fml3)*Fml2)) :-
        bdd_node(Fml3,Then,Else,BDD),
        bdd2formula(Then,Fml1),
        bdd2formula(Else,Fml2),!.

% BDD to disjunctive normal form
bdd2dnf(BDD,Fml) :- !,
        findall(SPFml,
                (path2one(BDD,PFml),
                 simplify(PFml,SPFml)),
                Paths),
        disjoin(Paths,Fml).
path2one(1,true).
path2one(BDD,Fml*FmlT) :-
        bdd_node(Fml,T,_E,BDD),
        path2one(T,FmlT).
path2one(BDD,-Fml*FmlE) :-
        bdd_node(Fml,_T,E,BDD),
        path2one(E,FmlE).

% BDD to conjunctive normal form
bdd2cnf(BDD,Fml) :- !,
        findall(SPFml,
                (path2zero(BDD,PFml),
                 simplify(PFml,SPFml)),
                Paths),
        conjoin(Paths,Fml).
path2zero(0,false).
path2zero(BDD,-Fml+FmlT) :-
        bdd_node(Fml,T,_E,BDD),
        path2zero(T,FmlT).
path2zero(BDD,Fml+FmlE) :-
        bdd_node(Fml,_T,E,BDD),
        path2zero(E,FmlE).


% BDD operations
bdd_conjoin(BDD1,BDD2,BDD) :-
        ite(BDD1,BDD2,0,BDD).
bdd_disjoin(BDD1,BDD2,BDD) :-
        ite(BDD1,1,BDD2,BDD).
bdd_equival(BDD1,BDD2,BDD) :-
        bdd_negate(BDD2,BDD3),
        ite(BDD1,BDD2,BDD3).
bdd_negated(BDD1,BDD) :-
        ite(BDD1,0,1,BDD).
        

% ITE algorithm
ite(1,F,_G,F) :- !.
ite(0,_F,G,G) :- !.
ite(F,1,0,F)  :- !.
ite(_F,G,G,G) :- !.
ite(F,G,H,R) :- cached_ite(F,G,H,R),!.
ite(F,G,H,R) :-
        bdd_node(LabelF,_,_,F),
        bdd_node(LabelG,_,_,G),
        bdd_node(LabelH,_,_,H),
        least_label(LabelF,LabelG,LabelH,X),
        branch(F,X,1,FT),
        branch(G,X,1,GT),
        branch(H,X,1,HT),
        branch(F,X,0,FF),
        branch(G,X,0,GF),
        branch(H,X,0,HF),
        ite(FT,GT,HT,T),
        ite(FF,GF,HF,E),
        find_or_add_unique(X,T,E,R),
        cache_ite(F,G,H,R).

cache_ite(F,G,H,R) :-
        assert(cached_ite(F,G,H,R)).

% find node with (Label,Then,Else) or create one
find_or_add_unique(_Label,B,B,B) :- !.
find_or_add_unique(Label1,Then,Else,BDD) :-
        bdd_node(Label2,Then,Else,BDD),
        % need this to avoid unifying p(A) with p(f(A))
        % (by default no occur check)
        Label1 =@= Label2, !.
find_or_add_unique(Label,Then,Else,BDD) :- !,
        retract(nodes(N)),
        N1 is N+1,
        assert(nodes(N1)),
        assert(bdd_node(Label,Then,Else,N1)),
        BDD=N1.

% label order: use Prolog term order, 
% '___undef' is the highest of all
least_label(L1,L2,L3,L) :-
        least_label(L1,L2,L4),
        least_label(L3,L4,L).
least_label(L1,L2,L1) :-
        label_less_than(L1,L2), !.
least_label(L1,L2,L2) :-
        label_less_than(L2,L1), !.
label_less_than(_,'___undef') :- !.
label_less_than(L1,L2) :- 
        L1 \=@= '___undef', !,
        L1 @=< L2.

% get Result node when Label==Value at Node
branch(Node,Label,_Value,Result) :-
        bdd_node(Label2,_Then,_Else,Node),
        Label \=@= Label2,
        Result = Node.
branch(Node,Label,1,Result) :-
        bdd_node(Label2,Then,_Else,Node),
        Label =@= Label2,
        Result = Then.
branch(Node,Label,0,Result) :-
        bdd_node(Label2,_Then,Else,Node),
        Label =@= Label2,
        Result = Else.

% succeeds if Fml is an atom
bdd_atom(Fml) :-
        Fml \= (_ <=> _),
        Fml \= (_  => _),
        Fml \= (_ <=  _),
        Fml \= (-_),
        Fml \= (_ + _),
        Fml \= (_ * _).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% BDD Output
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% print (unwinded) BDD 
print_bdd_tree(BDD) :-
        print_bdd_tree2(BDD,0).

print_bdd_tree2(0,N) :-
        print_tabs(N),
        writeln(0).
print_bdd_tree2(1,N) :-
        print_tabs(N),
        writeln(1).

print_bdd_tree2(BDD,N) :-
        bdd_node(L,T,E,BDD),
        print_tabs(N),
        writeln(L),
        N1 is N+1,
        print_bdd_tree2(T,N1),
        print_bdd_tree2(E,N1).

print_tabs(0) :- !.
print_tabs(N) :- !,
        write(' '),
        N1 is N-1,
        print_tabs(N1).

% output all BDD nodes
print_bdd_nodes :-
        nodes(N),
        print_bdd_nodes(N).

print_bdd_nodes(N) :-
        N > -1, !,
        bdd_node(L,T,E,N),
        write(N),
        write(': '), write(L),
        write(' T->'), write(T),
        write(' F->'), write(E),
        write('\n'),
        N1 is N-1,
        print_bdd_nodes(N1).
print_bdd_nodes(_).

% draw BDD using graphviz interface
draw_bdd :-
        findall(e(N1,N2,1),(bdd_node(_,N2,_,N1),N1\=0,N1\=1),PosEdges),
        findall(e(N1,N2,0),(bdd_node(_,_,N2,N1),N1\=0,N1\=1),NegEdges),
        append(PosEdges,NegEdges,Edges),
        nodes(N),
        make_graph(N,Edges,Graph),
        view_graph(Graph,[edge_attrs_generator:bdd_edge_attr,
                          node_attrs_generator:bdd_node_attr,
                          layout:dot]).

% 0-egde => dashed line
bdd_edge_attr(_Graph,Edge,Attrs) :-
        Edge=e(_N1,_N2,0),
        Attrs=[style="dashed"].
% 1-edge => normal line
bdd_edge_attr(_Graph,Edge,Attrs) :-
        Edge=e(_N1,_N2,1),
        Attrs=[].
% non-leaf-node => label with Label
bdd_node_attr(_Graph,Node,Attrs) :-
        bdd_node(Label,_,_,Node),
        Label\='___undef',
        term_string((Label,Node),LabelS),
        Attrs=[label=LabelS].
% else label with 0 ...
bdd_node_attr(_Graph,0,Attrs) :-
        Attrs=[label=0].
% ... or 1
bdd_node_attr(_Graph,1,Attrs) :-
        Attrs=[label=1].
