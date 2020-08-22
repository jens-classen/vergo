:- module(konclude, [entails/2,
                     inconsistent/1,
                     consistent/1,
                     simplify/2,
                     op(1130, xfy, <=>),
                     op(1110, xfy, <=),
                     op(1110, xfy, =>)]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Interface to Konclude Description Logic Reasoner
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

/* We use the following symbols for writing formulas:

   1. concepts

      nothing
      thing
      <concept>
      not(.)
      and([...])
      or([...])
      oneof([...]) (for nominals)
      some(.,.)
      only(.,.)

   2. roles

      universal
      <role>
      not(.)  (only in ABox assertions)

   3. TBox axioms

      subsumedBy(.,.)      

   4. Abox assertions

      concept_assertion(Concept,Name)
      role_assertion(Role,Name1,Name2)

      boolean combinations using -,*,+,<=>,=>,<=

 */

:- op(1130, xfy, <=>). % equivalence
:- op(1110, xfy, =>).  % implication
:- op(1110, xfy, <=).  % implication

:- use_module('../lib/env').
:- use_module('../lib/utils').

:- discontiguous write_axiom/2.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% DL Reasoning
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

/* Succeeds if Ontology entails Conjecture. */
entails(Ontology,Conjecture) :- !,
        add_to_ontology(Ontology,-Conjecture,NOntology),
        inconsistent(NOntology).

/* Succeeds if Ontology is inconsistent. */
inconsistent(Ontology) :- !,
        not(consistent(Ontology)).

/* Succeeds if Ontology is consistent. */
consistent(Ontology) :- !,
        consistent_konclude(Ontology).

/* Succeeds if Ontology is consistent. Uses Konclude DL reasoner. */
consistent_konclude(Ontology) :- !,
        temp_file(File),
        writeToFile(Ontology, File),
        process_create(path('Konclude'), 
                       ['consistency',
                        '-i', File],
                       [stdout(pipe(Output)), % pipe to parse result
                        process(PID)]),       % need PID for exit status
        process_wait(PID, _Status), !,        % wait for completion
        read_string(Output,"","",_,String),
        check_konclude_result(String).        % return value

check_konclude_result(String) :- 
        sub_string(String,_,_,_N,"error"), !,
        temp_file(File),
        report_message(error,['Konclude reported an error:']),
        report_message(error,['Aborting...']),
        report_message(error,[String]),
        report_message(error,['Check ', File, '.']),
        abort.
check_konclude_result(String) :-
        sub_string(String,_,_,_N,"is consistent."), !.
check_konclude_result(String) :-
        sub_string(String,_,_,_N,"is inconsistent."), !,
        fail.
check_konclude_result(String) :- 
        temp_file(File),
        report_message(error,['Unexpected Konclude output:']),
        report_message(error,['Aborting...']),
        report_message(error,[String]),
        report_message(error,['Check ', File, '.']),
        abort.

temp_file(File) :- !,
        temp_dir(TempDir),
        string_concat(TempDir, '/owl2.ofn', File).

writeToFile(Ontology, FileName) :- !,
        open(FileName, write, Stream),
        write_ontology(Stream, Ontology),
	close(Stream).

write_ontology(Stream, ontology(Names, Concepts, Roles, ABox, TBox)) :- !,
        URL = 'http://example.com/owl/temp',
        write_prefixes(Stream, URL),
        write(Stream, 'Ontology( <'),
        write(Stream, URL),
        write(Stream, '>\n'),
        write_name_declarations(Stream, Names),
        write_conc_declarations(Stream, Concepts),
        write_role_declarations(Stream, Roles),
        write_axioms(Stream, ABox),
        write_axioms(Stream, TBox),
        write(Stream, ')\n').

write_ontology(Stream, Axioms) :-
        is_list(Axioms), !,
        URL = 'http://example.com/owl/temp',
        write_prefixes(Stream, URL),
        write(Stream, 'Ontology( <'),
        write(Stream, URL),
        write(Stream, '>\n'),
        write_axioms(Stream, Axioms),
        write(Stream, ')\n').

write_prefixes(Stream, URL) :- !,
        write(Stream, 'Prefix(:=<'),
        write(Stream, URL),
        write(Stream, '#>)\n'),
        write(Stream, 'Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)\n'),
        write(Stream, 'Prefix(owl:=<http://www.w3.org/2002/07/owl#>)\n').

write_axioms(Stream, [Axiom|Axioms]) :- !,
        write_axiom(Stream, Axiom),
        write_axioms(Stream, Axioms).
write_axioms(_Stream, []).

write_name_declarations(Stream, [Name|Names]) :- !,
        write(Stream, '  Declaration( NamedIndividual( :'),
        write(Stream, Name),
        write(Stream,  ' ) )\n'),
        write_name_declarations(Stream, Names).
write_name_declarations(Stream, []) :- !,
        write(Stream, '\n').

write_conc_declarations(Stream, [Concept|Concepts]) :- !,
        write(Stream, '  Declaration( Class( :'),
        write(Stream, Concept),
        write(Stream,  ' ) )\n'),
        write_conc_declarations(Stream, Concepts).
write_conc_declarations(Stream, []) :- !,
        write(Stream, '\n').

write_role_declarations(Stream, [Role|Roles]) :- !,
        write(Stream, '  Declaration( ObjectProperty( :'),
        write(Stream, Role),
        write(Stream,  ' ) )\n'),
        write_role_declarations(Stream, Roles).
write_role_declarations(Stream, []) :- !,
        write(Stream, '\n').

write_axiom(Stream, subsumedBy(C1,C2)) :- !,
        write(Stream, '  SubClassOf(\n'),
        write_concept(Stream, 2, C1),
        write_concept(Stream, 2, C2),
        write(Stream, '   )\n').

write_concept(Stream, Indent, thing) :- !,
        write_indent(Stream,Indent),
        write(Stream, 'owl:Thing\n').
write_concept(Stream, Indent, nothing) :- !,
        write_indent(Stream,Indent),
        write(Stream, 'owl:Nothing\n').
write_concept(Stream, Indent, and(Concepts)) :- !,
        write_indent(Stream,Indent),
        write(Stream, 'ObjectIntersectionOf(\n'),
        IndentN = Indent + 1,
        write_concepts(Stream, IndentN, Concepts),
        write_indent(Stream,Indent),
        write(Stream, ')\n').
write_concept(Stream, Indent, or(Concepts)) :- !,
        write_indent(Stream,Indent),
        write(Stream, 'ObjectUnionOf(\n'),
        IndentN = Indent + 1,
        write_concepts(Stream, IndentN, Concepts),
        write_indent(Stream,Indent),
        write(Stream, ')\n').
write_concept(Stream, Indent, not(Concept)) :- !,
        write_indent(Stream,Indent),
        write(Stream, 'ObjectComplementOf(\n'),
        IndentN = Indent + 1,
        write_concept(Stream, IndentN, Concept),
        write_indent(Stream,Indent),
        write(Stream, ')\n').
write_concept(Stream, Indent, oneof(Names)) :- !,
        write_indent(Stream,Indent),
        write(Stream, 'ObjectOneOf(\n'),
        write_name_list(Stream,Names),
        write(Stream, ')\n').
write_concept(Stream, Indent, some(Role,Concept)) :- !,
        write_indent(Stream,Indent),
        write(Stream, 'ObjectSomeValuesFrom(\n'),
        IndentN = Indent + 1,
        write_role(Stream, IndentN, Role),
        write_concept(Stream, IndentN, Concept),
        write_indent(Stream,Indent),
        write(Stream, ')\n').
write_concept(Stream, Indent, all(Role,Concept)) :- !,
        write_indent(Stream,Indent),
        write(Stream, 'ObjectAllValuesFrom(\n'),
        IndentN = Indent + 1,
        write_role(Stream, IndentN, Role),
        write_concept(Stream, IndentN, Concept),
        write_indent(Stream,Indent),
        write(Stream, ')\n').
write_concept(Stream, Indent, Prim) :- !,
        write_indent(Stream,Indent),
        write(Stream, ':'),
        write(Stream, Prim),
        write(Stream, '\n').

write_concepts(Stream, Indent, [Concept|Concepts])  :- !,
        write_concept(Stream,Indent,Concept),
        write_concepts(Stream,Indent,Concepts).
write_concepts(_Stream, _Indent, []) :- !.

write_role(Stream, Indent, universal) :- !,
        write_indent(Stream,Indent),
        write(Stream, 'owl:topObjectProperty\n').
write_role(Stream, Indent, Prim) :- !,
        write_indent(Stream,Indent),
        write(Stream, ':'),
        write(Stream, Prim),
        write(Stream, '\n').

write_name_list(Stream, [Name|Names]) :- !,
        write(Stream, ' :'),
        write(Stream, Name),
        write(Stream, ' '),
        write_name_list(Stream,Names).
write_name_list(_Stream, []) :- !.

write_axiom(Stream, concept_assertion(C,N)) :- !,
        write(Stream, '  ClassAssertion(\n'),
        write_concept(Stream, 2, C),
        write_name(Stream, 2, N),
        write(Stream, '   )\n').
write_axiom(Stream, role_assertion(R,N1,N2)) :- !,
        write(Stream, '  ObjectPropertyAssertion(\n'),
        write_role(Stream, 2, R),
        write_name(Stream, 2, N1),
        write_name(Stream, 2, N2),
        write(Stream, '   )\n').
write_axiom(Stream, A1*A2) :- !,
        write_axiom(Stream, A1),
        write_axiom(Stream, A2).
write_axiom(Stream, BAxiom) :- !,
        boolaxiom2assertion(BAxiom, Assertion),
        write_axiom(Stream, Assertion).

write_name(Stream, Indent, Name) :- !,
        write_indent(Stream,Indent),
        write(Stream, ':'),
        write(Stream, Name),
        write(Stream, '\n').        

write_indent(Stream, Indent) :-
        Indent > 0, !,
        write(Stream, '  '),
        IndentN is Indent-1,
        write_indent(Stream, IndentN).
write_indent(_Stream, Indent) :-
        Indent = 0, !.

boolaxiom2assertion(Axiom, Assertion) :- !,
        get_names_roles(Axiom, NamesRoles),
        get_new_name(NewName),
        construct_concept(Axiom, NamesRoles, Concept),
        Assertion=concept_assertion(Concept,NewName).

get_names_roles(A1*A2, NamesRoles) :- !,
        get_names_roles(A1, NR1),
        get_names_roles(A2, NR2),
        union(NR1, NR2, NamesRoles).
get_names_roles(A1+A2, NamesRoles) :- !,
        get_names_roles(A1, NR1),
        get_names_roles(A2, NR2),
        union(NR1, NR2, NamesRoles).
get_names_roles(A1<=>A2, NamesRoles) :- !,
        get_names_roles(A1, NR1),
        get_names_roles(A2, NR2),
        union(NR1, NR2, NamesRoles).
get_names_roles(A1=>A2, NamesRoles) :- !,
        get_names_roles(A1, NR1),
        get_names_roles(A2, NR2),
        union(NR1, NR2, NamesRoles).
get_names_roles(A1<=A2, NamesRoles) :- !,
        get_names_roles(A1, NR1),
        get_names_roles(A2, NR2),
        union(NR1, NR2, NamesRoles).
get_names_roles(-A, NamesRoles) :- !,
        get_names_roles(A, NamesRoles).
get_names_roles(Atom, NamesRoles) :-
        Atom = concept_assertion(_C,N), !,
        get_new_role(N,R),
        NamesRoles = [(N,R)].
get_names_roles(Atom, NamesRoles) :-
        Atom = role_assertion(_R,N1,N2), !,
        get_new_role(N1,R1),
        get_new_role(N2,R2),
        NamesRoles = [(N1,R1),(N2,R2)].

get_new_role(Name,Role) :- !,
        atom_concat('__role_',Name,Role).

get_new_name('__dummy') :- !.

construct_concept(Axiom, NamesRoles, Concept) :- !,
        construct_concept2(NamesRoles, CList),
        construct_concept3(Axiom, NamesRoles, C),
        append(CList, [C], Conjuncts),
        Concept = and(Conjuncts).

construct_concept2([(N,R)|NamesRoles], [some(R,oneof([N])),all(R,oneof([N]))|Conjuncts]) :- !,
        construct_concept2(NamesRoles,Conjuncts).
construct_concept2([],[]) :- !.

construct_concept3(A1*A2, NamesRoles, and([R1,R2])) :- !,
        construct_concept3(A1, NamesRoles, R1),
        construct_concept3(A2, NamesRoles, R2).
construct_concept3(A1+A2, NamesRoles, or([R1,R2])) :- !,
        construct_concept3(A1, NamesRoles, R1),
        construct_concept3(A2, NamesRoles, R2).
construct_concept3(A1<=>A2, NamesRoles, Concept) :- !,
        construct_concept3((A1=>A2)*(A2=>A1), NamesRoles, Concept).
construct_concept3(A1=>A2, NamesRoles, Concept) :- !,
        construct_concept3((-A1)+A2, NamesRoles, Concept).
construct_concept3(A1<=A2, NamesRoles, Concept) :- !,
        construct_concept3(A1+(-A2), NamesRoles, Concept).
construct_concept3(-A, NamesRoles, not(C)) :- !,
        construct_concept3(A, NamesRoles, C).
construct_concept3(concept_assertion(C,N), NamesRoles, Concept) :- !,
        member((N,R), NamesRoles),
        Concept = some(R,C).
construct_concept3(role_assertion(R,N1,N2), NamesRoles, Concept) :- !,
        member((N1,R1), NamesRoles),
        Concept = some(R1,some(R,oneof([N2]))).

% add formula to ontology: distinguish the two representation styles
add_to_ontology(ontology(Names, Concepts, Roles, ABox, TBox), Formula,
                NOntology) :-
        (Formula = concept_assertion(_,_);
         Formula = role_assertion(_,_,_)), !,
        NOntology = ontology(Names,Concepts,Roles,[Formula|ABox],
                             TBox).
add_to_ontology(ontology(Names, Concepts, Roles, ABox, TBox), Formula,
                NOntology) :-
        Formula = subsumedBy(_,_), !,
        NOntology = ontology(Names,Concepts,Roles,ABox,
                             [Formula|TBox]).
add_to_ontology(Ontology,Formula,[Formula|Ontology]) :-  !.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Formula Simplification
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% change nothing so far
simplify(F,F).