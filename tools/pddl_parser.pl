%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% File:        pddl_parser.pl
%
% Author:      Jens Claßen
%              mailto:classen@kbsg.rwth-aachen.de
%
% Exported predicates:
%
%      parse_pddl_domain_string(+String,-Axioms)
%
%         String is a string that contains a PDDL domain
%                description according to the BNF of 
%                PDDL 3.0 [Gerivini & Long 2005]
%         Axioms is a list of Prolog axioms that constitute
%                the translation of the PDDL domain into
%                a Basic Action Theory of IndiGolog
%                [Claßen et al. 2007]
%
%      parse_pddl_problem_string(+String,-Axioms)
%
%         String is a string that contains a PDDL problem
%                instance description according to the BNF of 
%                PDDL 3.0 [Gerivini & Long 2005]
%         Axioms is a list of Prolog axioms that constitute
%                the translation of the PDDL problem into
%                the initial theory of a Basic Action Theory of
%                IndiGolog [Claßen et al. 2007]
%
%      parse_pddl_domain_file(+InFile,+OutFile)
%
%         same as parse_pddl_domain_string/2, but reads the PDDL
%         domain description from file InFile and writes the
%         axioms into OutFile
%
%      parse_pddl_problem_file(+InFile,OutFile)
%
%         same as parse_pddl_problem_string/2, but reads the PDDL
%         problem instance description from file InFile and 
%         writes the axioms into file OutFile
%
%      Currently, the following requirement tags are supported:
%
%         :strips
%         :typing
%         :negative-preconditions
%         :disjunctive-preconditions
%         :equality
%         :existential-preconditions
%         :universal-preconditions
%         :quantified-preconditions
%         :conditional-effects
%         :adl
%
% References:
%
%      [Gerivini & Long 2005] Gerivini, A. and Long, D. 2005. BNF
%           description of PDDL3.0.
%
%      [Claßen et al. 2007] Claßen, J.; Eyerich, P.; Lakemeyer, G.;
%           and Nebel, B. 2007. Towards and integration of Golog 
%           and planning. In Proceedings of IJCAI-07, AAAI Press.
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% TODO: include discontiguous directives

:- module(pddl_parser, [parse_pddl_domain_string/2,
                        parse_pddl_problem_string/2,
                        parse_pddl_domain_file/2,
                        parse_pddl_problem_file/2]).

:- use_module(library(dcg/basics)).

:- use_module('../lib/env').
:- use_module('../lib/utils').
:- use_module('../reasoning/fol').

:- dynamic requirement/1.

%:- mode parse_pddl_domain_string(+,-).
parse_pddl_domain_string(String,Axioms) :-
        string_codes(String,Codes),
        phrase(pddl_domain(Axioms),Codes).

%:- mode parse_pddl_problem_string(+,-).
parse_pddl_problem_string(String,Axioms) :-
        string_codes(String,Codes),
        phrase(pddl_problem(Axioms),Codes).

%:- mode parse_pddl_domain_file(+,+).
parse_pddl_domain_file(InFile,OutFile) :-
        phrase_from_file(pddl_domain(axioms(Domain,
                                            Type_Axioms,
                                            Constant_Axioms,
                                            Predicate_Axioms,
                                            Function_Axioms,
                                            Constraint_Axioms,
                                            Structure_Axioms)),
                         InFile),
        open(OutFile, write, Stream2),
        write_domain_header(Stream2, Domain),
        write_directives(Stream2),
        write_rules(Stream2, Type_Axioms, "Typing Axioms"),
        write_rules(Stream2, Constant_Axioms, "Constant Definitions"),
        write_rules(Stream2, Predicate_Axioms, "Predicate Definitions"),
        write_rules(Stream2, Function_Axioms, "Function Definitions"),
        write_rules(Stream2, Constraint_Axioms, "Constraints"),
        write_rules(Stream2, Structure_Axioms, "Structures (Actions)"),
        close(Stream2).

%:- mode parse_pddl_problem_file(+,+).
parse_pddl_problem_file(InFile,OutFile) :-
        phrase_from_file(axioms(Problem,
                                Domain,
                                ObjectAxioms,
                                InitAxioms,
                                GoalAxioms),
                         InFile),
        open(OutFile, write, Stream2),
        write_problem_header(Stream2, Problem, Domain),
        write_rules(Stream2, ObjectAxioms, "Objects"),
        write_rules(Stream2, InitAxioms, "Initial Values"),
        write_rules(Stream2, GoalAxioms, "Goal"),
        close(Stream2).

write_directives(Stream) :-
        forall(member(X,["domain/2",
                         "rel_fluent/1",
                         "prim_action/1",
                         "poss/2",
                         "causes_true/3",
                         "causes_false/3",
                         "fluent_parameter_types/2",
                         "action_parameter_types/2"]),
               (write(Stream, ":- discontiguous "),
                write(Stream, X),
                write(Stream, ".\n"))).

write_rules(Stream, Axioms, Header) :-
        write(Stream,
              "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n"),
        write(Stream, "% "), write(Stream, Header), write(Stream, "\n"),
        write(Stream,
              "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n\n"),
        write_rules2(Stream, Axioms).

write_rules2(Stream, [Axiom|Axioms]) :-
        write_axiom_readable(Stream,Axiom),
        %write_axiom(Stream,Axiom),
        write_rules2(Stream,Axioms).
write_rules2(Stream, []) :- write(Stream, "\n\n").

write_axiom(Stream, Axiom) :-
        write_term(Stream, Axiom, [quoted(true),fullstop(true),nl(true)]).

write_axiom_readable(Stream, Axiom) :-
        \+ \+ (numbervars(Axiom,0,_),
               write_term(Stream, Axiom, [numbervars(true),
                                          quoted(true),
                                          fullstop(true),
                                          nl(true)
                                         ])
              ).

write_domain_header(Stream, DomainName) :-
        write(Stream,
              "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n"),
        write(Stream,
              "%\n% Golog axiomatization translated from PDDL domain \""),
        write(Stream, DomainName), write(Stream, "\"\n%\n% "),
        write_time(Stream), write(Stream, "\n%\n"),
        write(Stream,
              "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n\n\n").

write_problem_header(Stream, Problem, Domain) :-
        write(Stream,
              "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n"),
        write(Stream,
              "%\n% Golog axiomatization of problem \""),
        write(Stream, Problem), write(Stream, "\" for PDDL domain \""),
        write(Stream, Domain), write(Stream, "\"\n%\n% "),
        write_time(Stream), write(Stream, "\n%\n"),
        write(Stream,
              "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n\n\n").

write_time(Stream ):- write(Stream, "Generated by PDDL parser at "),
        local_time_and_date_as_string(TimeAndDate),
        write(Stream, TimeAndDate).
        

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%:- lib(hash).
%:- local reference(variables).

debug_mode(true).

parse_string(String,PDDL) :-
        phrase(PDDL,String).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% PDDL grammar starts here
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% PDDL Domains
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

pddl_domain(axioms(Domain, Type_Axioms, Constant_Axioms,
                   Predicate_Axioms, Function_Axioms,
                   Constraint_Axioms, Structure_Axioms)) -->
        ws,
        ascii("("), ws,
        ascii("define"), ws,
        ascii("("), ws,
        ascii("domain"), wp, !,
	{announce_pro("PDDL domain description")},
        pddl_domain_name(Domain), ws,
        ascii(")"), ws,
        ([]; pddl_requirements, ws),
        ([],{Type_Axioms=[]};
         pddl_type_definitions(Type_Axioms), ws),
        ([],{Constant_Axioms=[]};
         pddl_constant_defs(Constant_Axioms), ws),
        ([],{Predicate_Axioms=[]};
         pddl_predicate_defs(Predicate_Axioms), ws),
        ([],{Function_Axioms=[]};
         pddl_functions_defs(Function_Axioms), ws),
        ([],{Constraint_Axioms=[]};
         pddl_constraints(Constraint_Axioms), ws),
        pddl_structure_def_star(Structure_Axioms), ws,
        ascii(")"), ws, !,
        {announce_suc("PDDL domain description")}.

pddl_domain_name(Name) -->
        pddl_name_atom(Name).
 
% Requirements %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

pddl_requirements -->
        ascii("("), ws,
        ascii(":requirements"), wp, !,
        {retractall(requirement(_))},
        {announce_pro("requirements")},
        pddl_requirement_plus, ws,
        ascii(")"), !,
        {announce_suc("requirements")}.

pddl_requirement_plus -->
        pddl_requirement, wp,
        pddl_requirement_plus.
pddl_requirement_plus -->
        pddl_requirement.

pddl_requirement -->
        ascii(":strips"),
        {assert(requirement(strips))};
        ascii(":typing"),
        {assert(requirement(typing))};
        ascii(":negative-preconditions"),
        {assert(requirement(negative-preconditions))};
        ascii(":disjunctive-preconditions"),
        {assert(requirement(disjunctive-preconditions))};
        ascii(":equality"),
        {assert(requirement(equality))};
        ascii(":existential-preconditions"),
        {assert(requirement(existential-preconditions))};
        ascii(":universal-preconditions"),
        {assert(requirement(universal-preconditions))};
        ascii(":quantified-preconditions"),
        {assert(requirement(existential-preconditions)),
         assert(requirement(universal-preconditions))};
        ascii(":conditional-effects"),
        {assert(requirement(conditional-effects))};
        ascii(":fluents"),
        {assert(requirement(numeric-fluents)),
         assert(requirement(object-fluents))};
        ascii(":numeric-fluents"),
        {assert(requirement(numeric-fluents))};
        ascii(":adl"),
        {assert(requirement(strips)),
         assert(requirement(typing)),
         assert(requirement(negative-preconditions)),
         assert(requirement(disjunctive-preconditions)),
         assert(requirement(equality)),
         assert(requirement(existential-preconditions)),
         assert(requirement(universal-preconditions)),
         assert(requirement(conditional-effects))};
        ascii(":durative-actions"),
        {assert(requirement(durative-actions))};
        ascii(":duration-inequalities"),
        {assert(requirement(duration-inequalities))};
        ascii(":continuous-effects"),
        {assert(requirement(continuous-effects))};
        ascii(":derived-predicates"),
        {assert(requirement(derived-predicates))};
        ascii(":timed-initial-literals"),
        {assert(requirement(timed-initial-literals))};
        ascii(":preferences"),
        {assert(requirement(preferences))};
        ascii(":constraints"),
        {assert(requirement(constraints))};
        ascii(":action-costs"),
        {assert(requirement(action-costs))}.

must_support(R) :-
        requirement(R), !.
must_support(R) :-
        not(requirement(R)), !,
        write(user_error, "Requirement "),
        write(user_error, R),
        write(user_error, " is necessary for this domain,"),
        write(user_error, " but not declared!\n"),% fail.
        write(user_error, "Proceeding nonetheless...\n"),
        flush_output(user_error).

cannot_compile(F) :-
        write(user_error, "Cannot compile feature "),
        write(user_error, F),
        write(user_error,"!\n"),
        write(user_error, "Proceeding nonetheless...\n"),
        flush_output(user_error).

% Types %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

pddl_type_definitions(Axioms) -->
        ascii("("), ws,
        ascii(":types"), wp, !,
        {announce_pro("types")},
        {must_support(typing)},
        pddl_typed_list_name(Types), ws,
        ascii(")"), ws, !,
        {type_declaration(Types,Axioms1)},
        {subtypes_declaration(Types,Axioms2)},
        {append(Axioms1,Axioms2,Axioms)},
        {announce_suc("types")}.

pddl_typed_list_name(Types) -->
       pddl_name_star(Types).
pddl_typed_list_name([Type|Types]) -->
        pddl_name_plus(Names), wp,
        ascii("-"), wp, %note: spaces before and after "-"!
        pddl_type(Type_name), wp,
        {must_support(typing)},
        {Type_name = either(ENames) ->
            Type =.. [either, ENames, Names];
            Type =.. [Type_name, Names]},
        pddl_typed_list_name(Types).

pddl_name_star([]) --> [].
pddl_name_star(Names) -->
        pddl_name_plus(Names).

pddl_name_plus([Name]) -->
        pddl_name_atom(Name).
pddl_name_plus([Name|Names]) -->
        pddl_name_atom(Name), wp,
        pddl_name_star(Names).

pddl_type(either(Names)) -->
        ascii("("), ws,
        ascii("either"), wp,
        pddl_primitive_type_plus(Names), ws,
        ascii(")").
pddl_type(Name) -->
        pddl_primitive_type(Name).

pddl_primitive_type(Name) -->
        pddl_name_atom(Name).
pddl_primitive_type(object) -->
        ascii("object").

pddl_primitive_type_plus([Name]) -->
        pddl_primitive_type(Name).
pddl_primitive_type_plus([Name|Names]) -->
        pddl_name_atom(Name), wp,
        pddl_primitive_type_plus(Names).

% Constants %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

pddl_constant_defs(Axioms) -->
        ascii("("), ws,
        ascii(":constants"), wp, !,
        {announce_pro("constants")},
        pddl_typed_list_name(ConstantsDefs), ws,
        ascii(")"), !,
        {constants_declaration(ConstantsDefs,Axioms)},
        {announce_suc("constants")}.

% Predicates %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

pddl_predicate_defs(Axioms) -->
        ascii("("), ws,
        ascii(":predicates"), wp, !,
        {announce_pro("predicates")},
        pddl_atomic_formula_skeleton_plus(FluentAxioms,
                                          TypingAxioms), ws,
        ascii(")"), !,
        {append(FluentAxioms,TypingAxioms,Axioms)},
        {announce_suc("predicates")}.

pddl_atomic_formula_skeleton_plus([Axiom1],[Axiom2]) -->
        pddl_atomic_formula_skeleton(Axiom1,Axiom2).
pddl_atomic_formula_skeleton_plus([Axiom1|Axioms1],
                                  [Axiom2|Axioms2]) -->
        pddl_atomic_formula_skeleton(Axiom1,Axiom2), ws,
        pddl_atomic_formula_skeleton_plus(Axioms1,Axioms2).

pddl_atomic_formula_skeleton(Axiom1,Axiom2) -->
        ascii("("), ws,
        pddl_predicate(PName), wp,
        pddl_typed_list_variable(Variables,Types), ws,
        {pddl_vars_to_prolog_vars(Variables,PVariables),
         Head =.. [PName|PVariables],
         Axiom1 = (rel_fluent(Head)),
         Axiom2 = (fluent_parameter_types(PName,Types))},
        ascii(")").

pddl_predicate(Name) -->
        pddl_name_atom(Name).

% no type given => object as default
pddl_typed_list_variable(Variables,Types) -->
        pddl_variable_star(Variables),
        {list_same_length(object,Variables,Types)}.
pddl_typed_list_variable(Variables,Types) -->
        pddl_variable_plus(CVariables), wp,
        ascii("-"), wp, %note: spaces before and after "-"!
        pddl_type(Type_Name), ws,
        {must_support(typing)},
        {append(CVariables,RVariables,Variables),
         list_same_length(Type_Name,CVariables,CTypes),
         append(CTypes,RTypes,Types)},
        pddl_typed_list_variable(RVariables,RTypes).

pddl_variable_star([]) --> [].
pddl_variable_star(Vars) -->
        pddl_variable_plus(Vars).

pddl_variable_plus([Var]) -->
        pddl_variable(Var).
pddl_variable_plus([Var|Vars]) -->
        pddl_variable(Var), wp,
        pddl_variable_plus(Vars).

pddl_variable(Var) -->
        ascii("?"),
        pddl_name_atom(Name),
        {atom_concat('?',Name,Var)}.

% Functions %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

pddl_functions_defs([]) -->
        ascii("("), ws,
        ascii(":functions"), wp, !,
        {announce_pro("functions")},
        {must_support(fluents),
         cannot_compile(fluents)},
        pddl_function_typed_list_atomic_function_skeleton, ws,
        ascii(")"), !,
        {announce_suc("functions")}.

pddl_function_typed_list_atomic_function_skeleton -->
	pddl_atomic_function_skeleton_plus, ws,
        ascii("-"), ws,
        pddl_function_type, wp,
        pddl_function_typed_list_atomic_function_skeleton.
pddl_function_typed_list_atomic_function_skeleton --> [].
pddl_function_typed_list_atomic_function_skeleton -->
	{must_support(numeric-fluents)},
        pddl_atomic_function_skeleton_plus. % default type: number

pddl_function_type -->
        ascii("number"), !,
        {must_support(numeric-fluents)}.
pddl_function_type -->
        pddl_type(_), !,
        {must_support(typing)},
        {must_support(object-fluents)}.

pddl_atomic_function_skeleton_plus -->
        pddl_atomic_function_skeleton.
pddl_atomic_function_skeleton_plus -->
        pddl_atomic_function_skeleton, ws,
        pddl_atomic_function_skeleton_plus.

pddl_atomic_function_skeleton -->
        ascii("("), ws,
        pddl_function_symbol(_), wp,
        pddl_typed_list_variable(_,_), ws,
        ascii(")").

pddl_function_symbol(F) -->
        pddl_name_atom(F).

% Constraints %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

pddl_constraints([]) -->
        ascii("("), ws,
        ascii(":constraints"), ws, !,
        {announce_pro("constraints")},
        {must_support(constraints),
         cannot_compile(constraints)},
        pddl_con_gd, ws,
        ascii(")"), !,
        {announce_suc("constraints")}.

pddl_con_gd -->
        ascii("("), ws,
        ascii("and"), wp,
        pddl_con_gd_star, ws,
        ascii(")").
pddl_con_gd -->
        ascii("("), ws,
        ascii("forall"), ws,
        ascii("("),
        pddl_typed_list_variable(_,_), ws,
        ascii(")"), ws,
        pddl_con_gd, ws,
        ascii(")").
pddl_con_gd -->
        ascii("("), ws,
        ascii("at end"), wp,
        pddl_gd(_,_,_,_), ws,
        ascii(")").
pddl_con_gd -->
        ascii("("), ws,
        ascii("always"), wp,
        pddl_gd(_,_,_,_), ws,
        ascii(")").
pddl_con_gd -->
        ascii("("), ws,
        ascii("sometime"), wp,
        pddl_gd(_,_,_,_), ws,
        ascii(")").
pddl_con_gd -->
        ascii("("), ws,
        ascii("within"), wp,
        pddl_number(_), wp,
        pddl_gd(_,_,_,_), ws,
        ascii(")").
pddl_con_gd -->
        ascii("("), ws,
        ascii("at-most-once"), wp,
        pddl_gd(_,_,_,_), ws,
        ascii(")").
pddl_con_gd -->
        ascii("("), ws,
        ascii("sometime-after"), wp,
        pddl_gd(_,_,_,_), wp,
        pddl_gd(_,_,_,_), ws,
        ascii(")").
pddl_con_gd -->
        ascii("("), ws,
        ascii("sometime-before"), wp,
        pddl_gd(_,_,_,_), wp,
        pddl_gd(_,_,_,_), ws,
        ascii(")").
pddl_con_gd -->
        ascii("("), ws,
        ascii("always-within"), wp,
        pddl_number(_), wp,
        pddl_gd(_,_,_,_), wp,
        pddl_gd(_,_,_,_), ws,
        ascii(")").
pddl_con_gd -->
        ascii("("), ws,
        ascii("hold-during"), wp,
        pddl_number(_), wp,
        pddl_number(_), wp,
        pddl_gd(_,_,_,_), ws,
        ascii(")").
pddl_con_gd -->
        ascii("("), ws,
        ascii("hold-after"), wp,
        pddl_number(_), wp,
        pddl_gd(_,_,_,_), ws,
        ascii(")").

pddl_number(N) -->
        pddl_integer(C),
        {number_codes(N,C)}.
pddl_number(F) -->
        pddl_float(C),
        {number_codes(F,C)}.

pddl_integer(C) -->
        digit_plus(C).
pddl_float(C) -->
        digit_plus(C1),
        ascii("."),
        digit_plus(C2),
        {append(C1,[46|C2],C)}.

digit_plus([C]) -->
        [C],
        {digit(C)}.
digit_plus([C|Cs]) -->
        [C],
        {digit(C)},
        digit_plus(Cs).

pddl_con_gd_star --> [].
pddl_con_gd_star -->
        pddl_con_gd, ws,
        pddl_con_gd_star.

% Structures (Actions) %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

pddl_structure_def_star([]) --> [].
pddl_structure_def_star(Axioms) -->
        pddl_structure_def(Axioms1), ws,
        pddl_structure_def_star(Axioms2),
        {append(Axioms1,Axioms2,Axioms)}.

pddl_structure_def(Axioms) -->
        pddl_action_def(Axioms).
pddl_structure_def(Axioms) -->
        pddl_durative_action_def(Axioms).
pddl_structure_def(Axioms) -->
        pddl_derived_def(Axioms).

pddl_action_def(Axioms) -->
        ascii("("), ws,
        ascii(":action"), wp, !,
        {announce_pro("action")},
        pddl_action_symbol(Symbol), wp,
        {announce_cur(Symbol)},
        ascii(":parameters"), ws,
        ascii("("), ws,
        pddl_typed_list_variable(Variables,Types), ws,
        ascii(")"), ws, !,
        {announce_fin(Symbol,"parameters")},
        pddl_action_def_body(Symbol,Variables,Types,
                             Preconds,Effects), ws,
        ascii(")"), !,
        {construct_action_axioms(Axioms,Symbol,Variables,
                                 Types,Preconds,Effects)},
        {announce_fin(Symbol,"body")},
        {announce_suc("action")}.

pddl_action_symbol(Symbol) -->
        pddl_name_atom(Symbol).

pddl_action_def_body(Symbol,Variables,Types,Preconds,Effects) -->
	([], {Preconds=[]};
         ascii(":precondition"), !, wp,
         pddl_emptyOr(pddl_pre_gd(Symbol,Variables,Types,Preconds),Preconds)),
	{announce_fin(Symbol,"preconditions")},	ws,
	([], {Effects=[]};
         ascii(":effect"), !, wp,
         pddl_emptyOr(pddl_effect(Symbol,Variables,Types,Effects),Effects)).

pddl_emptyOr(_,[]) -->
        ascii("("), ws,
        ascii(")"), !.
pddl_emptyOr(X,_) --> X.

pddl_pre_gd_star(_,_,_,[]) --> [].
pddl_pre_gd_star(S,V,T,[G|GL]) -->
        pddl_pre_gd(S,V,T,G), ws,
        pddl_pre_gd_star(S,V,T,GL).

pddl_pre_gd(S,V,T,G) -->
        pddl_pref_gd(S,V,T,G).
pddl_pre_gd(S,V,T,and(GL)) -->
        ascii("("), ws,
        ascii("and"), wp,
        pddl_pre_gd_star(S,V,T,GL), ws,
        ascii(")").
pddl_pre_gd(S,V,T,forall(V1,T1,G)) -->
        ascii("("), ws,
        ascii("forall"), ws,
        {must_support(universal-preconditions)},
	ascii("("), ws,
        pddl_typed_list_variable(V1,T1), ws,
        ascii(")"), wp,
        {append(V,V1,V2), append(T,T1,T2)},
        pddl_pre_gd(S,V2,T2,G), ws,
        ascii(")").

pddl_pref_gd(_,_,_,_) -->
        ascii("("), ws,
        ascii(":preference"), wp,
        {must_support(preferencenes)},
        {cannot_compile(preferences)},
        ([]; pddl_pref_name(_), wp),
        pddl_gd(_,_,_,_), ws, ascii(")").
pddl_pref_gd(S,V,T,G) -->
        pddl_gd(S,V,T,G).

pddl_pref_name(Name) -->
        pddl_name_atom(Name).

pddl_gd(_,V,T,G) -->
        pddl_atomic_formula_term(V,T,G).
pddl_gd(_,V,T,G) -->
        pddl_literal_term(V,T,G),
        {must_support(negative-preconditions)}.
pddl_gd(S,V,T,and(GL)) -->
        ascii("("), ws,
        ascii("and"), ws,
        pddl_gd_star(S,V,T,GL), ws,
        ascii(")").
pddl_gd(S,V,T,or(GL)) -->
        ascii("("), ws,
        ascii("or"), ws,
        {must_support(disjunctive-preconditions)},
        pddl_gd_star(S,V,T,GL), ws,
        ascii(")").
pddl_gd(S,V,T,neg(G)) -->
        ascii("("), ws,
        ascii("not"), ws,
        {must_support(disjunctive-preconditions)},
        pddl_gd(S,V,T,G), ws,
        ascii(")").
pddl_gd(S,V,T,impl(G1,G2)) -->
        ascii("("), ws,
        ascii("imply"), ws,
        {must_support(disjunctive-preconditions)},
        pddl_gd(S,V,T,G1), ws,
        pddl_gd(S,V,T,G2), ws,
        ascii(")").
pddl_gd(S,V,T,some(V1,T1,G)) -->
        ascii("("), ws,
        ascii("exists"), ws,
        {must_support(existential-preconditions)},
        ascii("("), ws,
        pddl_typed_list_variable(V1,T1), ws,
        ascii(")"), ws,
        {append(V,V1,V2), append(T,T1,T2)},
        pddl_gd(S,V2,T2,G), ws,
        ascii(")").
pddl_gd(S,V,T,all(V1,T1,G)) -->
        ascii("("), ws,
        ascii("forall"), ws,
        {must_support(universal-preconditions)},
        ascii("("), ws,
        pddl_typed_list_variable(V1,T1), ws,
        ascii(")"), ws,
        {append(V,V1,V2), append(T,T1,T2)},
        pddl_gd(S,V2,T2,G), ws,
        ascii(")").
pddl_gd(_,_,_,_) -->
        pddl_f_comp,
        {must_support(numeric-fluents),
         cannot_compile(fluents)}.

pddl_gd_star(_,_,_,[]) --> [].
pddl_gd_star(S,V,T,[G|GL]) -->
        pddl_gd(S,V,T,G), ws,
        pddl_gd_star(S,V,T,GL).

pddl_f_comp -->
        ascii("("), ws,
        pddl_binary_comp, ws,
        pddl_f_exp(_,_,_), wp,
        pddl_f_exp(_,_,_), ws,
        ascii(")").

pddl_literal_term(V,T,G) -->
        pddl_atomic_formula_term(V,T,G).
pddl_literal_term(V,T,neg(G)) -->
        ascii("("), ws,
        ascii("not"), ws,
        pddl_atomic_formula_term(V,T,G), ws,
        ascii(")").

pddl_atomic_formula_term(V,T,G) -->
        ascii("("), ws,
        pddl_predicate(Name), wp,
        pddl_term_star(V,T,Terms), ws,
        ascii(")"),
        {G=..[Name|Terms]}.

pddl_atomic_formula_term(V,T,(T1 = T2)) -->
        ascii("("), ws,
        ascii("="), wp,
        {must_support(equality)},
        pddl_term(V,T,T1), wp,
        pddl_term(V,T,T2), ws,
        ascii(")").

pddl_term_star(_,_,[]) --> [].
pddl_term_star(V,T,[Term]) -->
        pddl_term(V,T,Term).
pddl_term_star(V,T,[Term|Terms]) -->
        pddl_term(V,T,Term), wp,
        pddl_term_star(V,T,Terms).

pddl_term(_,_,Constant) -->
        pddl_name_atom(Constant).
pddl_term(V,_,Variable) -->
        pddl_variable(Variable),
        {member(Variable,V)}.
pddl_term(V,T,FTerm) -->
        pddl_function_term(V,T,FTerm),
        {must_support(object-fluents)}.

pddl_function_term(V,T,FTerm) -->
        ascii("("), ws,
        pddl_function_symbol(Symbol), wp,
        pddl_term_star(V,T,Terms), ws,
        ascii(")"),
        {FTerm =.. [Symbol|Terms]},
        {must_support(object-fluents)}.

pddl_f_exp(_,_,N) -->
        pddl_number(N),
        {must_support(numeric-fluents)}.
pddl_f_exp(V,T,Exp) -->
        ascii("("), ws,
        pddl_binary_op(Op), ws,
        pddl_f_exp(V,T,Exp1), wp,
        pddl_f_exp(V,T,Exp2), ws,
        ascii(")"),
        {Exp =.. [Op,Exp1,Exp2]},
        {must_support(numeric-fluents)}.
pddl_f_exp(V,T,Exp) -->
        ascii("("), ws,
        pddl_multi_op(Op), ws,
        pddl_f_exp(V,T,Exp1), wp,
        pddl_f_exp_plus(V,T,Exps2), ws,
        ascii(")"),
        {apply_multi_op(Op,[Exp1|Exps2],Exp)},
        {must_support(numeric-fluents)}.
pddl_f_exp(V,T,Exp) -->
        ascii("("), ws,
        ascii("-"), ws,
        pddl_f_exp(V,T,Exp1), ws,
        ascii(")"),
        {Exp =.. ['-',Exp1]},
        {must_support(numeric-fluents)}.
pddl_f_exp(V,T,Head) -->
        pddl_f_head(V,T,Head),
        {must_support(numeric-fluents)}.

pddl_f_exp_plus(V,T,Exp) -->
        pddl_f_exp(V,T,Exp).
pddl_f_exp_plus(V,T,[Exp|Exps]) -->
        pddl_f_exp(V,T,Exp), wp,
        pddl_f_exp_plus(V,T,Exps).

pddl_f_head(V,T,Head) -->
        ascii("("), ws,
        pddl_function_symbol(F), wp,
        pddl_term_star(V,T,Terms), ws,
        ascii(")"),
        {Head =.. [F|Terms]}.
pddl_f_head(_,_,Head) -->
        pddl_function_symbol(Head).

pddl_binary_op(X) -->
        pddl_multi_op(X).
pddl_binary_op('-') -->
        ascii("-").
pddl_binary_op('/') -->
        ascii("/").

pddl_multi_op('*') -->
        ascii("*").
pddl_multi_op('+') -->
        ascii("+").

pddl_binary_comp -->
        ascii(">");
        ascii("<");
        ascii("=");
        ascii(">=");
        ascii("<=").

pddl_effect(S,V,T,and(EL)) -->
        ascii("("), ws,
        ascii("and"), ws,
        pddl_c_effect_star(S,V,T,EL), ws,
        ascii(")").
pddl_effect(S,V,T,E) -->
        pddl_c_effect(S,V,T,E).

pddl_c_effect(S,V,T,forall(V1,T1,E)) -->
        ascii("("), ws,
        ascii("forall"), ws,
        {must_support(conditional-effects)},
        ascii("("), ws,
        % BNF requires "pddl_typed_list_variable_star,
        % however this should be equivalent:
        pddl_typed_list_variable(V1,T1), ws,
        ascii(")"), ws,
        {append(V,V1,V2), append(T,T1,T2)},
	pddl_effect(S,V2,T2,E), ws,
        ascii(")").
pddl_c_effect(S,V,T,when(G,E)) -->
        ascii("("), ws,
        ascii("when"), ws,
        {must_support(conditional-effects)},
        pddl_gd(S,V,T,G), ws,
        pddl_cond_effect(S,V,T,E), ws,
        ascii(")").
pddl_c_effect(S,V,T,E) -->
        pddl_p_effect(S,V,T,E).

pddl_c_effect_star(_,_,_,[]) --> [].
pddl_c_effect_star(S,V,T,[E|EL]) -->
        pddl_c_effect(S,V,T,E), ws,
        pddl_c_effect_star(S,V,T,EL).

pddl_p_effect(_,V,T,del(E)) -->
        ascii("("), ws,
        ascii("not"), ws,
        pddl_atomic_formula_term(V,T,E), ws,
        ascii(")").
pddl_p_effect(_,V,T,add(E)) -->
        pddl_atomic_formula_term(V,T,E).
pddl_p_effect(_,_,_,_) -->
        ascii("("), ws,
        pddl_assign_op, wp,
        {must_support(numeric-fluents),
         cannot_compile(numeric-fluents)},
        pddl_f_head(_,_,_), wp,
        pddl_f_exp(_,_,_), ws,
        ascii(")").
pddl_p_effect(_,_,_,_) -->
        ascii("("), ws,
        ascii("assign"), wp,
        {must_support(object-fluents),
         cannot_compile(object-fluents)},
        pddl_function_term(_,_,_), wp,
        pddl_term(_,_,_), ws,
        ascii(")").
pddl_p_effect(_,_,_,_) -->
        ascii("("), ws,
        ascii("assign"), wp,
        {must_support(object-fluents),
         cannot_compile(object-fluents)},
        pddl_function_term(_,_,_), wp,
        ascii("undefined"), ws,
        ascii(")").

pddl_p_effect_star(_,_,_,[]) --> [].
pddl_p_effect_star(S,V,T,[E|EL]) -->
        pddl_p_effect(S,V,T,E),	ws,
        pddl_p_effect_star(S,V,T,EL).

pddl_cond_effect(S,V,T,and(EL)) -->
        ascii("("), ws,
        ascii("and"), ws,
        pddl_p_effect_star(S,V,T,EL), ws,
        ascii(")").
pddl_cond_effect(S,V,T,E) -->
        pddl_p_effect(S,V,T,E).

pddl_assign_op -->
        ascii("assign");
        ascii("scale-up");
        ascii("scale-down");
        ascii("increase");
        ascii("decrease").

% Durative Actions %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

pddl_durative_action_def(Axioms) -->
        ascii("("), ws,
        ascii(":durative-action"), wp, !,
        {must_support(durative-actions)},
        {cannot_compile(durative-actions)},
        {announce_pro("durative action")},
        pddl_da_symbol(Symbol), wp,
        ascii(":parameters"), ws,
        ascii("("), ws,
        pddl_typed_list_variable(Variables,Types), ws,
        ascii(")"), ws,
        pddl_da_def_body(Symbol,Variables,Types,
                         Duration,Conds,Effects), ws,
        ascii(")"), !,
        {construct_durative_action_axioms(Axioms,Symbol,Variables,Types,
                                          Duration,Conds,Effects)},
        {announce_fin(Symbol,"body")},
        {announce_suc("durative action")}.

pddl_da_symbol(Name) -->
        pddl_name_atom(Name).

pddl_da_def_body(Symbol,Variables,Types,Duration,Conds,Effects) -->
        ascii(":duration"), ws,
        pddl_duration_constraint(Variables,Types,Duration), ws,
        ascii(":condition"), ws,
        pddl_emptyOr(pddl_da_gd(Symbol,Variables,Types,Conds),
                     Conds), ws,
        ascii(":effect"), ws,
        pddl_emptyOr(pddl_da_effect(Symbol,Variables,Types,Effects),Effects).

pddl_da_gd(Symbol,Variables,Types,Conds) -->
        pddl_pref_timed_gd(Symbol,Variables,Types,Conds).
pddl_da_gd(Symbol,Variables,Types,and(Conds)) -->
        ascii("("), ws,
        ascii("and"), ws,
        pddl_da_gd_star(Symbol,Variables,Types,Conds), ws,
        ascii(")").
pddl_da_gd(Symbol,Variables,Types,all(V,T,G)) -->
        ascii("("), ws,
        ascii("forall"), ws,
        {must_support(universal-preconditions)},
        ascii("("), ws,
        pddl_typed_list_variable(V1,T1), ws,
        {append(Variables,V1,V), append(Types,T1,T)},
        ascii(")"), ws,
        pddl_da_gd(Symbol,V,T,G), ws,
        ascii(")").

pddl_da_gd_star(_Symbol,_Variables,_Types,[]) --> [].
pddl_da_gd_star(Symbol,Variables,Types,[Cond|Conds]) -->
        pddl_da_gd(Symbol,Variables,Types,Cond), ws,
        pddl_da_gd_star(Symbol,Variables,Types,Conds).

pddl_pref_timed_gd(Symbol,Variables,Types,Conds) -->
        pddl_timed_gd(Symbol,Variables,Types,Conds).
pddl_pref_timed_gd(Symbol,Variables,Types,pddl_timed_pref(Conds)) -->
        ascii("("), ws,
        ascii("preference"), ws,
        {must_support(preferences)},
        pddl_timed_gd(Symbol,Variables,Types,Conds), ws,
        ascii(")").
pddl_pref_timed_gd(Symbol,Variables,Types,
                   pddl_timed_pref(Name,Conds)) -->
        ascii("("), ws,
        ascii("preference"), wp,
        {must_support(preferences)},
        pddl_pref_name(Name), ws,
        pddl_timed_gd(Symbol,Variables,Types,Conds), ws,
        ascii(")").

pddl_timed_gd(Symbol,Variables,Types,pddl_at(TimeSpecifier,Goal)) -->
        ascii("("), ws,
        ascii("at"), wp,
        pddl_time_specifier(TimeSpecifier), ws,
        pddl_gd(Symbol,Variables,Types,Goal), ws,
        ascii(")").
pddl_timed_gd(Symbol,Variables,Types,pddl_over(Interval,Goal)) -->
        ascii("("), ws,
        ascii("over"), wp,
        pddl_interval(Interval), ws,
        pddl_gd(Symbol,Variables,Types,Goal), ws,
        ascii(")").

pddl_time_specifier(start) -->
        ascii("start").
pddl_time_specifier(end) -->
        ascii("end").

pddl_interval(all) -->
        ascii("all").

pddl_duration_constraint(V,T,and(DurationConstraints)) -->
        ascii("("), ws,
        ascii("and"),
        {must_support(duration-inequalities)},
        pddl_simple_duration_constraint_plus(V,T,
                                             DurationConstraints), ws,
        ascii(")").
pddl_duration_constraint(_,_,true) -->
        ascii("("), ws,
        ascii(")").
pddl_duration_constraint(V,T,Duration) -->
        pddl_simple_duration_constraint(V,T,Duration).

pddl_simple_duration_constraint(Variables,Types,
                                pddl_d_op(Op,Value)) -->
        ascii("("), ws,
        pddl_d_op(Op), ws,
        ascii("?duration"), wp,
        pddl_d_value(Variables,Types,Value), ws,
        ascii(")").
pddl_simple_duration_constraint(Variables,Types,
                                pddl_at(TimeSpecifier,Constraint)) -->
        ascii("("), ws,
        ascii("at"), wp,
        pddl_time_specifier(TimeSpecifier), ws,
        pddl_simple_duration_constraint(Variables,Types,
                                        Constraint), ws,
        ascii(")").

pddl_simple_duration_constraint_plus(Variables,Types,[Constraint]) -->
	pddl_simple_duration_constraint(Variables,Types,Constraint).
pddl_simple_duration_constraint_plus(Variables,Types,
                                     [Constraint|Constraints]) -->
	pddl_simple_duration_constraint(Variables,Types,
                                        Constraint), ws,
	pddl_simple_duration_constraint_plus(Variables,Types,Constraints).

pddl_d_op(lessthan) -->
        ascii("<="),
        {must_support(duration-inequalities)}.
pddl_d_op(greaterthan) -->
        ascii(">="),
        {must_support(duration-inequalities)}.
pddl_d_op(equals) -->
        ascii("=").

pddl_d_value(_,_,Number) -->
        pddl_number(Number).
pddl_d_value(V,T,Exp) -->
        pddl_f_exp(V,T,Exp),
        {must_support(numeric-fluents)}.

pddl_da_effect(Symbol,Variables,Types,and(Effects)) -->
        ascii("("), ws,
        ascii("and"), ws,
        pddl_da_effect_star(Symbol,Variables,Types,Effects), ws,
        ascii(")").
pddl_da_effect(Symbol,Variables,Types,Effect) -->
        pddl_timed_effect(Symbol,Variables,Types,Effect).
pddl_da_effect(Symbol,Variables,Types,forall(V1,T1,Effects)) -->
        ascii("("), ws,
        ascii("forall"), ws,
        {must_support(conditional-effects)},
        ascii("("), ws,
        pddl_typed_list_variable(V1,T1), ws,
        {append(Variables,V1,V), append(Types,T1,T)},
        ascii(")"), ws,
        pddl_da_effect(Symbol,V,T,Effects), ws,
        ascii(")").
pddl_da_effect(Symbol,Variables,Types,when(G,E)) -->
        ascii("("), ws,
        ascii("when"), ws,
        {must_support(conditional-effects)},
        pddl_da_gd(Symbol,Variables,Types,G), ws,
        pddl_timed_effect(Symbol,Variables,Types,E), ws,
        ascii(")").

pddl_da_effect_star(_Symbol,_Variables,_Types,[]) --> [].
pddl_da_effect_star(Symbol,Variables,Types,[Effect|Effects]) -->
        pddl_da_effect(Symbol,Variables,Types,Effect), ws,
        pddl_da_effect_star(Symbol,Variables,Types,Effects).

pddl_timed_effect(Symbol,Variables,Types,
                  pddl_at(TimeSpecifier,Effects)) -->
        ascii("("), ws,
        ascii("at"), wp,
        pddl_time_specifier(TimeSpecifier), ws,
        pddl_cond_effect(Symbol,Variables,Types,Effects), ws,
        ascii(")").
pddl_timed_effect(_Symbol,Variables,Types,
                  pddl_at(TimeSpecifier,Effects)) -->
        ascii("("), ws,
        ascii("at"), wp,
        pddl_time_specifier(TimeSpecifier), ws,
        pddl_f_assign_da(Variables,Types,Effects), ws,
        ascii(")"),
        {must_support(numeric-fluents)}.
pddl_timed_effect(_Symbol,Variables,Types,
                  pddl_assign(Op,Head,Exp)) -->
        ascii("("), ws,
        pddl_assign_op_t(Op), wp,
        {must_support(continuous-effects)},
        {must_support(numeric-fluents)},
        pddl_f_head(Variables,Types,Head), wp,
        pddl_f_exp_t(Variables,Types,Exp), ws,
        ascii(")").

pddl_assign_op_t(increase) -->
        ascii("increase").
pddl_assign_op_t(increase) -->
        ascii("decrease").

pddl_f_exp_t(V,T,Exp * 'pddl_#t') -->
        ascii("("), ws,
        ascii("*"), wp,
        pddl_f_exp(V,T,Exp), wp,
        ascii("#t"), ws,
        ascii(")").
pddl_f_exp_t(V,T,'pddl_#t' * Exp) -->
        ascii("("), ws,
        ascii("*"), wp,
        ascii("#t"), wp,
        pddl_f_exp(V,T,Exp), ws,
        ascii(")").
pddl_f_exp_t(_,_,'pddl_#t') -->
        ascii("#t").

pddl_f_assign_da(V,T,pddl_f_assign_da(Op,Head,Exp)) -->
        ascii("("), ws,
        pddl_assign_op(Op), wp,
        pddl_f_head(V,T,Head), wp,
        pddl_f_exp_da(V,T,Exp), ws,
        ascii(")").

pddl_f_exp_da(V,T,Exp) -->
        ascii("("),
        pddl_binary_op(Op), ws,
        pddl_f_exp_da(V,T,Exp1), wp,
        pddl_f_exp_da(V,T,Exp2), ws,
        ascii(")"),
        {Exp =.. [Op,Exp1,Exp2]}.
pddl_f_exp_da(V,T,Exp) -->
        ascii("("),
        pddl_multi_op(Op), ws,
        pddl_f_exp_da(V,T,Exp1), wp,
        pddl_f_exp_da_plus(V,T,Exps2), ws,
        ascii(")"),
        {apply_multi_op(Op,[Exp1|Exps2],Exp)}.
pddl_f_exp_da(V,T,Exp) -->
        ascii("("), ws,
        ascii("-"), ws,
        pddl_f_exp_da(V,T,Exp1), ws,
        ascii(")"),
        {Exp =.. ['-',Exp1]}.
pddl_f_exp_da(_,_,'pddl_duration') -->
        ascii("?duration"),
        {must_support(duration-inequalities)}.
pddl_f_exp_da(V,T,Exp) -->
        pddl_f_exp(V,T,Exp).

% Derived Predicates%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

pddl_derived_def([]) -->
        ascii("("), ws,
        ascii(":derived"), wp, !,
        {must_support(derived-predicates),
         cannot_compile(derived-predicates)},
        pddl_atomic_formula_skeleton(_,_), wp,
        pddl_gd(_,_,_,_), ws,
        ascii(")").

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% PDDL Problems
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

pddl_problem(axioms(Problem,Domain,ObjectAxioms,
                    InitAxioms,GoalAxioms)) -->
        ws,
        ascii("("), ws,
        ascii("define"), ws,
        ascii("("), ws,
        ascii("problem"), ws,
        pddl_problem_name(Problem), ws,
        ascii(")"), ws,
        ascii("("), ws,
        ascii(":domain"), ws,
        pddl_problem_domain(Domain), ws,
        ascii(")"), ws,
        ([]; pddl_problem_requirements, ws),
        ([]; pddl_object_declarations(ObjectAxioms), ws),
        pddl_init(InitAxioms), ws,
        pddl_goal(GoalAxioms), ws,
        ([]; pddl_problem_constraints, ws),
        ([]; pddl_metric_spec, ws),
        ([]; pddl_length_spec, ws),
        ascii(")"), ws.

pddl_problem_name(Name) -->
        pddl_name_atom(Name).

pddl_problem_domain(Name) -->
        pddl_name_atom(Name). % maybe put a test here?

pddl_problem_requirements -->
        pddl_requirements.

pddl_object_declarations(Axioms) -->
        ascii("("), ws,
        ascii(":objects"), wp, !,
        {announce_pro("objects")},
        pddl_typed_list_name(ObjectsDefs), ws,
        ascii(")"), !,
        {constants_declaration(ObjectsDefs,Axioms)},
        {announce_suc("objects")}.

pddl_init(Axioms) -->
        ascii("("), ws,
        ascii(":init"), wp, !,
        {announce_pro("init")},
        pddl_init_el_star(Axioms), ws,
        ascii(")"),
        {announce_suc("init")}.

pddl_init_el_star([Axiom|Axioms]) -->
        pddl_init_el(Axiom), ws,
        pddl_init_el_star(Axioms).
pddl_init_el_star([]) --> [].

pddl_init_el(initially(Atom,true)) -->
        pddl_literal_name(Atom).
pddl_init_el([]) -->
        ascii("("), ws,
        ascii("at"), wp,
        {must_support(timed-initial-literals),
         cannot_compile(timed-initial-literals)},
        pddl_number(_), ws,
        pddl_literal_name(_), ws,
        ascii(")").
pddl_init_el([]) -->
        ascii("("), ws,
        ascii("="), ws,
        {must_support(numeric-fluents),
         cannot_compile(numeric-fluents)},
        pddl_basic_function_term(_), wp,
        pddl_number(_), ws,
        ascii(")").
pddl_init_el([]) -->
        ascii("("), ws,
        ascii("="), ws,
        {must_support(object-fluents),
         cannot_compile(object-fluents)},
        pddl_basic_function_term(_), wp,
        pddl_name_atom(_), ws,
        ascii(")").

pddl_basic_function_term(Symbol) -->
        pddl_function_symbol(Symbol).
pddl_basic_function_term(Term) -->
        ascii("("), ws,
        pddl_function_symbol(Symbol), wp,
        pddl_name_star(Names), ws,
        ascii(")"),
        {Term =..[Symbol|Names]}.

pddl_literal_name(Axiom) -->
        pddl_atomic_formula_name(Axiom).
pddl_literal_name(Axiom) -->
        ascii("("), ws,
        ascii("not"), wp,
        pddl_atomic_formula_name(Axiom), ws,
        ascii(")").

pddl_atomic_formula_name(Atom) -->
        ascii("("), ws,
        pddl_predicate(PName), wp,
        pddl_name_star(Names), ws,
        ascii(")"),
        {Atom =.. [PName|Names]}.
pddl_atomic_formula_name((N1 = N2)) -->
        ascii("("), ws,
        ascii("="), wp,
        {must_support(equality)},
        pddl_name_atom(N1), wp,
        pddl_term(N2), ws,
        ascii(")").

pddl_goal([goal(F)]) -->
        ascii("("), ws,
        ascii(":goal"), wp, !,
        {announce_pro("goal")},
        pddl_pre_gd(goal,[],[],Preconds), ws,
        ascii(")"),
        {convert_precondition_formula(Preconds,F),
         announce_suc("goal")}.

pddl_problem_constraints -->
        ascii("("), ws,
        ascii(":constraints"), wp, !,
        {must_support(constraints),
         cannot_compile(constraints)},
        pddl_pref_con_gd, ws,
        ascii(")").

pddl_pref_con_gd -->
        ascii("("), ws,
        ascii("and"), wp,
        pddl_pref_con_gd_star, ws,
        ascii(")").
pddl_pref_con_gd -->
        ascii("("), ws,
        ascii("forall"), ws,
        {must_support(universal-preconditions)},
        ascii("("), ws,
        pddl_typed_list_variable(_,_), ws,
        ascii(")"), ws,
        pddl_con_gd, ws,
        ascii(")").
pddl_pref_con_gd -->
        ascii("("), ws,
        ascii("preference"), wp,
        {must_support(preferences),
         cannot_compile(preferences)},
        ([]; pddl_pref_name(_), ws),
        pddl_con_gd, ws,
        ascii(")").
pddl_pref_con_gd -->
        pddl_con_gd.

pddl_pref_con_gd_star --> [].
pddl_pref_con_gd_star -->
        pddl_pref_con_gd, ws,
        pddl_pref_con_gd_star.

pddl_metric_spec -->
        ascii("("), ws,
        ascii(":metric"), wp, !,
        {must_support(numeric-fluents)},
        pddl_optimization, wp,
        pddl_metric_f_exp, ws,
        ascii(")").

pddl_optimization -->
        ascii("minimize");
        ascii("maximize").

pddl_metric_f_exp -->
        ascii("("), ws,
        pddl_binary_op(_), wp,
        pddl_metric_f_exp, wp,
        pddl_metric_f_exp, ws,
        ascii(")").
pddl_metric_f_exp --> ascii("("), ws,
        pddl_multi_op(_), wp,
        pddl_metric_f_exp, wp,
        pddl_metric_f_exp_plus, ws,
        ascii(")").
pddl_metric_f_exp --> ascii("("), ws,
        ascii("-"), ws,
        pddl_metric_f_exp, ws,
        ascii(")").
pddl_metric_f_exp -->
        pddl_number(_).
pddl_metric_f_exp -->
        ascii("("), ws,
        pddl_function_symbol(_), wp,
        pddl_name_star(_), ws,
        ascii(")").
pddl_metric_f_exp -->
        pddl_function_symbol(_).
pddl_metric_f_exp -->
        ascii("total-time").
pddl_metric_f_exp -->
        ascii("("), ws,
        ascii("is-violated"), wp, !,
        {must_support(preferences)},
        pddl_pref_name(_), ws,
        ascii(")").

pddl_metric_f_exp_plus -->
        pddl_metric_f_exp.
pddl_metric_f_exp_plus -->
        pddl_metric_f_exp, wp,
        pddl_metric_f_exp_plus.

pddl_length_spec -->
        ascii("("), ws,
        ascii(":length"), wp,
        ([]; ascii("("), ws,
             ascii(":serial"), wp,
             pddl_integer(_), ws,
             ascii(")"), ws),
        ([]; ascii("("), ws,
             ascii(":parallel"), wp,
             pddl_integer(_), ws,
             ascii(")"), ws),
        ascii(")"). %deprecated since PDDL 2.1

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Auxiliary stuff
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

pddl_name_atom(Name) --> 
        pddl_name2(CList),
        {string_codes(String,CList),
         atom_string(Name,String)}.
pddl_name2([C|List]) -->
        pddl_name_first_char(C),
        pddl_name_char_list(List).

% first character of a name is a letter
pddl_name_first_char(C) --> [C],
        {uppercasechar(C);
         lowercasechar(C)}.

pddl_name_char(C) --> [C],
        {uppercasechar(C);
         lowercasechar(C)}.
pddl_name_char(C) --> [C],
        {C=95; C=45}. % C="_", C="-"
pddl_name_char(C) --> [C],
        {digit(C)}.

pddl_name_char_list([]) --> [].
pddl_name_char_list([C|List]) -->
        pddl_name_char(C),
        pddl_name_char_list(List).

uppercasechar(C) :-
        C>=65, C=<90. % C>="A" , C=<"Z"
lowercasechar(C) :-
        C>=97, C=<122. % C>="a" , C=<"z"
digit(C) :-
        C>=48, C=<57. % C>="0" , C=<"9"

first_char_to_upper(StringLower,StringUpper) :-
        string_codes(StringLower,[CLower|List]),
        char_to_upper(CLower,CUpper),
	string_codes(StringUpper,[CUpper|List]).
char_to_upper(CLower,CUpper) :-
        lowercasechar(CLower) -> CUpper is CLower-32 ; CUpper=CLower.

% "white plus"
wp --> pddl_white, !, ws.

% "white star"
ws --> pddl_white, !, ws.
ws --> [].

pddl_white --> [C],
        {C=59} /* ";" */, !,
        all_to_end_of_line.
pddl_white --> [C],
        {whitespace(C)}, !.
whitespace(32). % " "
whitespace(9).  % "\t"
whitespace(13). % "\r"
whitespace(10). % "\n"
whitespace(12). % "\f"

all_to_end_of_line -->
        pddl_newline, !.
all_to_end_of_line --> [_],
        all_to_end_of_line.

pddl_newline --> [10]. % "\n"

ascii(String) -->
        {string_codes(String, List)},
        checkList(List).

checkList([]) --> [].
checkList([A|L]) --> [A],
        checkList(L).

% for testing and debugging
stuff --> char_star.

char_star --> [].
char_star --> [_],
        char_star.

% debugging outputs
announce_pro(X) :-
        (debug_mode(true) ->
            (write("Processing "),
             write(X),
             write("...\n"),
             flush_output(user_output));
            true).
announce_suc(X) :-
        (debug_mode(true) ->
            (write("Succeeded processing "),
             write(X),
             write(".\n"),
             flush_output(user_output));
            true).
announce_cur(X) :-
        (debug_mode(true) ->
            (write("Currently processing structure >>"),
             write(X),
             write("<<.\n"),
             flush_output(user_output));
            true).
announce_fin(S,X) :-
        (debug_mode(true) ->
            (write("Finished part >>"),
             write(X),
             write("<< of structure >>"),
             write(S), write("<<.\n"),
             flush_output(user_output));
            true).

% list_same_length(X,L,L1) creates a list L1 of the same length as L with only X's
list_same_length(X,[_|L],[X|L1]) :-
        list_same_length(X,L,L1).
list_same_length(_,[],[]).

apply_multi_op(_Op,[E],E) :- !.
apply_multi_op(Op,[E|Es],Exp) :- !,
        apply_multi_op(Op,Es,Exp2),
        Exp =.. [Op,E,Exp2].

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Helping predicates for generating Golog clauses 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

construct_action_axioms(Axioms,Symbol,Variables,Types,Preconds,Effects) :-
        pddl_vars_to_prolog_vars(Variables,PVariables),
        Action_Term =.. [Symbol | PVariables],
        convert_precondition_formula(Preconds,CPreconds),
        convert_effect_formula(Action_Term,Effects,LCEffects),
        substitute_pddl_vars((CPreconds,LCEffects),
                             Variables,PVariables,
                             (CVPreconds,LCVEffects)),
	Axioms = [(prim_action(Action_Term)),
                  (action_parameter_types(Symbol,Types)),
                  (poss(Action_Term,CVPreconds))|
                  LCVEffects].

% Given a list of PDDL variables of the form '?variablename',
% constructs a list of the same length with fresh Prolog variables.
pddl_vars_to_prolog_vars([],[]) :- !.
pddl_vars_to_prolog_vars([_Var|Vars],[PVar|PVars]) :- !,
        copy_term(_X,PVar), % _X is a new variable
        pddl_vars_to_prolog_vars(Vars,PVars).

% Substitue all PDDL variables by the corresponding Prolog variables.
substitute_pddl_vars(X,[],[],X) :- !.
substitute_pddl_vars(X,[Var|Vars],[PVar|PVars],R) :- !,
        subv(Var,PVar,X,Y),
        substitute_pddl_vars(Y,Vars,PVars,R).

% Convert (pseudo-) precondition (obtained from parsing) into one that
% IndiGolog accepts; basically, multi-ary "and"s, "or"s etc. are
% turned into nested formulas.
convert_precondition_formula(and([]),true).
convert_precondition_formula(and([F]), FC) :-
        convert_precondition_formula(F,FC).
convert_precondition_formula(and([F|FL]),F*AF) :-
        convert_precondition_formula(and(FL),AF).
convert_precondition_formula(or([]),false).
convert_precondition_formula(or([F]), FC) :- 
        convert_precondition_formula(F,FC).
convert_precondition_formula(or([F|FL]),F+AF) :-
        convert_precondition_formula(or(FL),AF).
convert_precondition_formula(impl(F1,F2),CF1=>CF2) :-
        convert_precondition_formula(F1,CF1),
        convert_precondition_formula(F2,CF2).
convert_precondition_formula(neg(F),-NF) :-
        convert_precondition_formula(F,NF).
convert_precondition_formula(all([],[],F),CF) :-
        convert_precondition_formula(F,CF).
convert_precondition_formula(all([V],[T],F),all(V,T,CF)) :-
        convert_precondition_formula(F,CF).
convert_precondition_formula(all([V|VL],[T|TL],F),all(V,T,CF)) :-
        convert_precondition_formula(all(VL,TL,F),CF).
convert_precondition_formula(some([],[],F),CF) :-
        convert_precondition_formula(F,CF).
convert_precondition_formula(some([V],[T],F),some(V,T,CF)) :-
        convert_precondition_formula(F,CF).
convert_precondition_formula(some([V|VL],[T|TL],F),some(V,T,CF)) :-
        convert_precondition_formula(some(VL,TL,F),CF).
convert_precondition_formula(X,X). % atom

% Convert (pseudo-) effect (obtained from parsing) into one that
% IndiGolog accepts; typing restrictions for the affected predicates
% as well as quantified variables have to be considered-
convert_effect_formula(AT,E,LCE) :-
        % additional params = quantified variables and their types
        convert_effect_formula(AT,[],[],E,LCE).
convert_effect_formula(_AT,_Vs,_Ts,and([]),[]).
convert_effect_formula(AT,Vs,Ts,and([E|Es]),ACEs) :-
        convert_effect_formula(AT,Vs,Ts,E,CE),
        convert_effect_formula(AT,Vs,Ts,and(Es),CEs),
        append(CE,CEs,ACEs).
convert_effect_formula(AT,_Vs,_Ts,add(A),CE) :-
        CE=[(causes_true(AT,A,true))].
convert_effect_formula(AT,_Vs,_Ts,del(D),CE) :-
        CE=[(causes_false(AT,D,true))].
convert_effect_formula(AT,Vs,Ts,forall(QVs,VTs,F),CEs) :-
        append(QVs,Vs,VL), append(VTs,Ts,TL),
        convert_effect_formula(AT,VL,TL,F,CEs).
convert_effect_formula(AT,_Vs,_Ts,when(PF,add(A)),CE) :-
        convert_precondition_formula(PF,CPF),
        CE=[(causes_true(AT,A,CPF))].
convert_effect_formula(AT,_Vs,_Ts,when(PF,del(D)),CE) :-
        convert_precondition_formula(PF,CPF),
        CE=[(causes_false(AT,D,CPF))].
convert_effect_formula(_AT,_Vs,_Ts,when(_PF,and([])),[]).
convert_effect_formula(AT,Vs,Ts,when(PF,and([AD|ADs])),CEs) :-
        convert_effect_formula(AT,Vs,Ts,when(PF,AD),CE1),
        convert_effect_formula(AT,Vs,Ts,when(PF,and(ADs)),CE2),
        append(CE1,CE2,CEs).

% Convert the list of types with associated constants into Prolog
% clauses.
constants_declaration([ConstantsDef|Defs], [Axiom|Axioms]) :-
        ConstantsDef =.. [Type, ConstantsList],
        Axiom_Header = domain(Type,X),
        Axiom = (Axiom_Header :- member(X,ConstantsList)),
        constants_declaration(Defs,Axioms).
constants_declaration([],[]).

% For additional typing axioms of the form
% "subtypes(vehicle,[car,truck])."
subtypes_declaration([either(_,_)|Types],Axioms) :-
        subtypes_declaration(Types,Axioms).
subtypes_declaration([TypeDef|Defs],[Axiom|Axioms]) :-
        TypeDef =.. [Type,SubtypesList], !,
        Axiom = (subtypes(Type,SubtypesList)),
        subtypes_declaration(Defs,Axioms).
subtypes_declaration([_|Defs],Axioms) :-
        subtypes_declaration(Defs,Axioms).
subtypes_declaration([],[]).

type_declaration(_Types,[Axiom]) :- !,
        Axiom = (domain(Domain,X) :- subtypes(Domain,Subtypes),
                                     member(Subtype,Subtypes),
                                     domain(Subtype,X)).

flatten_typelist(ETs,[S|SL],[F|Fs]) :-
        F =..[S,ETs],
        flatten_typelist(ETs,SL,Fs).
flatten_typelist(_,[],[]).

process_subtypeslist([SubType],X,T) :- !,
        T = domain(SubType,X).
process_subtypeslist([SubType|SubTypes],X, (T ; Ts)) :-
        T = domain(SubType,X),
        process_subtypeslist(SubTypes,X,Ts).

construct_durative_action_axioms([],_Symbol,_Variables,_Types,
                                 _Duration,_Conds,_Effects). % TODO
