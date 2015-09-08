:- module(dl, [inconsistent/1,
               consistent/1]).

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

 */

:- use_module('../lib/env').
:- use_module('../lib/utils').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% DL Reasoning
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

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
        sub_string(String,_,_,_N,"(error)"), !,
        temp_file(File),
        report_message(['Konclude reported an error:']),
        report_message(['Aborting...']),
        report_message([String]),
        report_message(['Check ', File, '.']),
        abort.        
check_konclude_result(String) :-
        sub_string(String,_,_,_N,"is consistent."), !.
check_konclude_result(String) :-
        sub_string(String,_,_,_N,"is inconsistent."), !,
        fail.

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
        write_abox(Stream, ABox),
        write_tbox(Stream, TBox),
        write(Stream, ')\n').

write_prefixes(Stream, URL) :- !,
        write(Stream, 'Prefix(:=<'),
        write(Stream, URL),
        write(Stream, '/>)\n'),
        write(Stream, 'Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)\n'),
        write(Stream, 'Prefix(owl:=<http://www.w3.org/2002/07/owl#>)\n').

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

write_tbox(Stream, [TBA|TBAs]) :- !,
        write_tbox_axiom(Stream, TBA),
        write_tbox(Stream, TBAs).
write_tbox(Stream, []) :- !,
        write(Stream, '\n').

write_abox(Stream, [ABA|ABAs]) :-  !,
        write_abox_axiom(Stream, ABA),
        write_abox(Stream, ABAs).
write_abox(Stream, []) :- !,
        write(Stream, '\n').

write_tbox_axiom(Stream, subsumedBy(C1,C2)) :- !,
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

write_abox_axiom(Stream, concept_assertion(C,N)) :- !,
        write(Stream, '  ClassAssertion(\n'),
        write_concept(Stream, 2, C),
        write_name(Stream, 2, N),
        write(Stream, '   )\n').
write_abox_axiom(Stream, role_assertion(R,N1,N2)) :- !,
        write(Stream, '  ObjectPropertyAssertion(\n'),
        write_role(Stream, 2, R),
        write_name(Stream, 2, N1),
        write_name(Stream, 2, N2),
        write(Stream, '   )\n').        

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
