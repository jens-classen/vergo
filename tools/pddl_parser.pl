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

% TODO: handle identifiers consisting of capital letters correctly
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
	parse_string(String, pddl_domain(Axioms)).
%:- mode parse_pddl_problem_string(+,-).
parse_pddl_problem_string(String,Axioms) :-
	parse_string(String, pddl_problem(Axioms)).

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

pddl_domain(axioms(Domain,Type_Axioms,Constant_Axioms,Predicate_Axioms,
                   Function_Axioms,Constraint_Axioms,Structure_Axioms)) 
                    --> pddl_white_star, ascii("("), pddl_white_star,
                        ascii("define"), pddl_white_star, ascii("("),
			pddl_white_star, ascii("domain"), !, 
			{announce_pro("PDDL domain description")},
			pddl_white_plus,
			pddl_domain_name(Domain), pddl_white_star,
			ascii(")"), pddl_white_star,
			([]; pddl_requirements, pddl_white_star),
			([],{Type_Axioms=[]}; 
			    pddl_type_definitions(Type_Axioms), pddl_white_star),
			([],{Constant_Axioms=[]};
			    pddl_constant_defs(Constant_Axioms), pddl_white_star),
			([],{Predicate_Axioms=[]};
			    pddl_predicate_defs(Predicate_Axioms), pddl_white_star),
			([],{Function_Axioms=[]};
			    pddl_functions_defs(Function_Axioms), pddl_white_star),
			([],{Constraint_Axioms=[]};
			    pddl_constraints(Constraint_Axioms), pddl_white_star),
			pddl_structure_def_star(Structure_Axioms),
                        pddl_white_star, 
			ascii(")"), pddl_white_star, !,
			{announce_suc("PDDL domain description")}.

pddl_domain_name(Name) --> pddl_name_atom(Name).
 
% Requirements %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

pddl_requirements --> ascii("("), pddl_white_star,
                      ascii(":requirements"), !,
                      {retractall(requirement(_))},
		      {announce_pro("requirements")},
		      pddl_white_plus, pddl_requirement_plus,
		      pddl_white_star, ascii(")"), !,
		      {announce_suc("requirements")}.

pddl_requirement_plus --> pddl_requirement, pddl_white_plus, pddl_requirement_plus.
pddl_requirement_plus --> pddl_requirement.

pddl_requirement --> ascii(":strips"),
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
		     {assert(requirement(fluents))};
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
		     ascii(":derived-predicates"),
		     {assert(requirement(derived-predicates))};
		     ascii(":timed-initial-literals"),
		     {assert(requirement(timed-initial-literals))};
		     ascii(":preferences"),
		     {assert(requirement(preferences))};
		     ascii(":constraints"),
		     {assert(requirement(constraints))};
		     ascii(":duration-inequalities"),
		     {assert(requirement(duration-inequalities))};
		     ascii(":continuous-effects"),
		     {assert(requirement(continuous-effects))}.

must_support(R) :- requirement(R), !.
must_support(R) :- not(requirement(R)), !, 
	           write(user_error, "Requirement "), write(user_error, R),
		   write(user_error, " is necessary for this domain, but not declared!\n"),% fail.
		   write(user_error, "Proceeding nonetheless...\n"), flush_output(user_error).

cannot_compile(F) :- write(user_error, "Cannot compile feature "), write(user_error, F), write(user_error,"!\n"),
	             write(user_error, "Proceeding nonetheless...\n"), flush_output(user_error).

% Types %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

pddl_type_definitions(Axioms) --> ascii("("), pddl_white_star,
	                                ascii(":types"), !,
					{announce_pro("types")},
					{must_support(typing)},
					pddl_white_plus, 
				        pddl_typed_list_name(Types),
				        pddl_white_star, ascii(")"),
				        pddl_white_star, !,
                                        {type_declaration(Types,Axioms1)},
                                        {subtypes_declaration(Types,Axioms2)},
                                        {append(Axioms1,Axioms2,Axioms)},
					{announce_suc("types")}.

pddl_typed_list_name(Types) --> pddl_name_star(Types).
pddl_typed_list_name([Type]) --> pddl_name_plus(Names), pddl_white_star, ascii("-"),
	                               pddl_white_star, pddl_type(Type_name),
				       {Type_name = either(ENames) ->
                                           Type =.. [either, ENames, Names];
                                           Type =.. [Type_name, Names]}.
pddl_typed_list_name([Type|Types]) --> pddl_name_plus(Names), pddl_white_star, ascii("-"),
	                               pddl_white_star,
                                       pddl_type(Type_name),
                                       {Type_name = either(ENames) ->
                                           Type =.. [either, ENames, Names];
                                           Type =.. [Type_name, Names]},
	                               pddl_white_plus, pddl_typed_list_name(Types).

pddl_name_star([])           --> [].
pddl_name_star(Names)        --> pddl_name_plus(Names).

pddl_name_plus([Name]) --> pddl_name_atom(Name).
pddl_name_plus([Name|Names]) --> pddl_name_atom(Name), pddl_white_plus,
                                 pddl_name_star(Names).

pddl_type(Name)          --> pddl_primitive_type(Name).
pddl_type(either(Names)) --> ascii("("), pddl_white_star, ascii("either"),
	                     pddl_white_plus, pddl_primitive_type_plus(Names),
	                     pddl_white_star, ascii(")").

pddl_primitive_type(Name) --> pddl_name_atom(Name).

pddl_primitive_type_plus([Name])       --> pddl_primitive_type(Name).
pddl_primitive_type_plus([Name|Names]) --> pddl_name_atom(Name), pddl_white_plus,
	                                   pddl_primitive_type_plus(Names).

% Constants %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

pddl_constant_defs(Axioms) --> ascii("("), pddl_white_star,
                               ascii(":constants"), !,
			       {announce_pro("constants")},
			       pddl_white_plus,
			       pddl_typed_list_name(ConstantsDefs),
			       pddl_white_star, ascii(")"), !,
                               {constants_declaration(ConstantsDefs,Axioms)},
			       {announce_suc("constants")}.

% Predicates %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

pddl_predicate_defs(Axioms) --> ascii("("), pddl_white_star,
	                        ascii(":predicates"), !, 
				{announce_pro("predicates")},
				pddl_white_plus,
				pddl_atomic_formula_skeleton_plus(FluentAxioms,TypingAxioms),
				pddl_white_star, ascii(")"), !,
                                {append(FluentAxioms,TypingAxioms,Axioms)},
				{announce_suc("predicates")}.

pddl_atomic_formula_skeleton_plus([Axiom1],[Axiom2]) --> pddl_atomic_formula_skeleton(Axiom1,Axiom2).
pddl_atomic_formula_skeleton_plus([Axiom1|Axioms1],[Axiom2|Axioms2]) --> pddl_atomic_formula_skeleton(Axiom1,Axiom2),
	                              pddl_white_star,
				      pddl_atomic_formula_skeleton_plus(Axioms1,Axioms2).

pddl_atomic_formula_skeleton(Axiom1,Axiom2) --> ascii("("), pddl_white_star,
                                 pddl_predicate(PName), pddl_white_plus,
				 pddl_typed_list_variable(Variables,Types),
                                 {pddl_vars_to_prolog_vars(Variables,PVariables),
                                  Head =.. [PName|PVariables],
                                  Axiom1 = (rel_fluent(Head)),
                                  Axiom2 = (fluent_parameter_types(PName,Types))},
				 pddl_white_star, ascii(")").

pddl_predicate(Name) --> pddl_name_atom(Name).

% no type given => object as default
pddl_typed_list_variable(Variables,Types) --> pddl_variable_star(Variables),
                                              {list_same_length(object,Variables,Types)}.

pddl_typed_list_variable(Variables,Types) --> 
	                     {must_support(typing)},
			     pddl_variable_plus(Variables), 
	                     pddl_white_star,
	                     ascii("-"), pddl_white_star,
			     pddl_type(Type_Name),
			     {list_same_length(Type_Name,Variables,Types)}.
			     
pddl_typed_list_variable(Variables,Types) --> 
	                     {must_support(typing)},
			     pddl_variable_plus(CVariables), 
                             pddl_white_star,
	                     ascii("-"), pddl_white_star,
			     pddl_type(Type_Name), pddl_white_plus,
			     {append(CVariables,RVariables,Variables),
			      list_same_length(Type_Name,CVariables,CTypes),
			      append(CTypes,RTypes,Types)},
			     pddl_typed_list_variable(RVariables,RTypes). 

pddl_variable_star([]) --> [].
pddl_variable_star(Vars) --> pddl_variable_plus(Vars).

pddl_variable_plus([Var]) --> pddl_variable(Var).
pddl_variable_plus([Var|Vars]) --> pddl_variable(Var), pddl_white_plus,
                       pddl_variable_plus(Vars).

pddl_variable(Var) -->
        ascii("?"),
        pddl_name_atom(Name),
        {atom_concat('?',Name,Var)}.

% Functions %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

pddl_functions_defs([]) --> ascii("("), pddl_white_star,
	                        ascii(":functions"), !,
				{announce_pro("functions")},
				{must_support(fluents),
				 cannot_compile(fluents)},
				pddl_white_plus,
				pddl_function_typed_list_atomic_function_skeleton,
				pddl_white_star,
				ascii(")"), !,
				{announce_suc("functions")}.

pddl_function_typed_list_atomic_function_skeleton -->
	pddl_atomic_function_skeleton_star.
pddl_function_typed_list_atomic_function_skeleton -->
	{must_support(typing)},
	pddl_atomic_function_skeleton_plus,
	pddl_white_star,
	ascii("-"),
	pddl_white_star,
	pddl_function_type,
	pddl_white_plus,
	pddl_function_typed_list_atomic_function_skeleton.
pddl_function_typed_list_atomic_function_skeleton -->
	{must_support(typing)},
	pddl_atomic_function_skeleton_plus,
	pddl_white_star,
	ascii("-"),
	pddl_white_star,
	pddl_function_type.

% BNF says number, but should be normal type.
pddl_function_type --> pddl_type(_). %number.???

pddl_atomic_function_skeleton_star --> [].
pddl_atomic_function_skeleton_star --> pddl_atomic_function_skeleton_plus.

pddl_atomic_function_skeleton_plus --> pddl_atomic_function_skeleton.
pddl_atomic_function_skeleton_plus --> pddl_atomic_function_skeleton,
                                       pddl_white_star,
				       pddl_atomic_function_skeleton_plus.

pddl_atomic_function_skeleton --> ascii("("), pddl_white_star,
	                          pddl_function_symbol,
                                  pddl_white_plus,
                                  pddl_typed_list_variable(_,_),
                                  pddl_white_star,
                                  ascii(")").

pddl_function_symbol --> pddl_name_atom(_).

% Constraints %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

pddl_constraints([]) --> ascii("("), pddl_white_star,
	                     ascii(":constraints"), !,
			     {announce_pro("constraints")},
			     {must_support(constraints),
			      cannot_compile(constraints)},
			     pddl_white_star,
			     pddl_con_gd,
			     pddl_white_star, ascii(")"), !,
			     {announce_suc("constraints")}.

pddl_con_gd --> ascii("("), pddl_white_star, ascii("and"),
                pddl_con_gd_star.
pddl_con_gd --> ascii("("), pddl_white_star,
	        ascii("forall"),
		pddl_white_star, ascii("("),
		pddl_typed_list_variable(_,_),
		pddl_white_star, ascii(")"),
		pddl_white_star, 
		pddl_con_gd, pddl_white_star,
		ascii(")").
pddl_con_gd --> ascii("("), pddl_white_star,
	        ascii("at end"), pddl_white_plus,
		pddl_gd(_,_,_,_), pddl_white_star, ascii(")").
pddl_con_gd --> ascii("("), pddl_white_star,
	        ascii("at end"), pddl_white_plus,
		pddl_gd(_,_,_,_), pddl_white_star, ascii(")").
pddl_con_gd --> ascii("("), pddl_white_star,
	        ascii("always"), pddl_white_plus,
		pddl_gd(_,_,_,_), pddl_white_star, ascii(")").
pddl_con_gd --> ascii("("), pddl_white_star,
	        ascii("sometime"), pddl_white_plus,
		pddl_gd(_,_,_,_), pddl_white_star, ascii(")").
pddl_con_gd --> ascii("("), pddl_white_star,
	        ascii("within"), pddl_white_plus,
		pddl_number(_), pddl_white_plus,
		pddl_gd(_,_,_,_), pddl_white_star, ascii(")").
pddl_con_gd --> ascii("("), pddl_white_star,
	        ascii("at-most-once"), pddl_white_plus,
		pddl_gd(_,_,_,_), pddl_white_star, ascii(")").
pddl_con_gd --> ascii("("), pddl_white_star,
	        ascii("sometime-after"), pddl_white_plus,
		pddl_gd(_,_,_,_), pddl_white_plus, pddl_gd(_,_,_,_),
		pddl_white_star, ascii(")").
pddl_con_gd --> ascii("("), pddl_white_star,
	        ascii("sometime-before"), pddl_white_plus,
		pddl_gd(_,_,_,_), pddl_white_plus, pddl_gd(_,_,_,_),
		pddl_white_star, ascii(")").
pddl_con_gd --> ascii("("), pddl_white_star,
	        ascii("always-within"), pddl_white_plus,
		pddl_number(_), pddl_white_plus,
		pddl_gd(_,_,_,_), pddl_white_plus, pddl_gd(_,_,_,_),
		pddl_white_star, ascii(")").
pddl_con_gd --> ascii("("), pddl_white_star,
	        ascii("hold-during"), pddl_white_plus,
		pddl_number(_), pddl_white_plus, 
		pddl_number(_), pddl_white_plus,
		pddl_gd(_,_,_,_), pddl_white_star, ascii(")").
pddl_con_gd --> ascii("("), pddl_white_star,
	        ascii("hold-after"), pddl_white_plus,
		pddl_number(_), pddl_white_plus,
		pddl_gd(_,_,_,_), pddl_white_star, ascii(")").

pddl_number(N) --> pddl_integer(C), {number_codes(N,C)}.
pddl_number(F) --> pddl_float(C), {number_codes(F,C)}.

pddl_integer(C) --> digit_plus(C).
pddl_float(C)   --> digit_plus(C1), ascii("."), digit_plus(C2), {append(C1,[46|C2],C)}.

digit_plus([C]) --> [C], {digit(C)}.
digit_plus([C|Cs]) --> [C], {digit(C)}, digit_plus(Cs).

pddl_con_gd_star --> [].
pddl_con_gd_star --> pddl_con_gd, pddl_white_star, pddl_con_gd_star.

% Structures (Actions) %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

pddl_structure_def_star([]) --> [].
pddl_structure_def_star(Axioms) --> pddl_structure_def(Axioms1),
                                    pddl_white_star,
				    pddl_structure_def_star(Axioms2),
				    {append(Axioms1,Axioms2,Axioms)}.

pddl_structure_def(Axioms) --> pddl_action_def(Axioms).
pddl_structure_def(Axioms) --> pddl_durative_action_def(Axioms).
pddl_structure_def(Axioms) --> pddl_derived_def(Axioms).

pddl_action_def(Axioms) --> ascii("("), pddl_white_star,
                            ascii(":action"), !,
			    {announce_pro("action")},
			    pddl_white_plus,
			    pddl_action_symbol(Symbol), 
			    pddl_white_plus,
			    {announce_cur(Symbol)},
			    ascii(":parameters"), pddl_white_star,
			    ascii("("), pddl_white_star,
			    pddl_typed_list_variable(Variables,Types),
			    pddl_white_star, ascii(")"), !,
			    {announce_fin(Symbol,"parameters")},
			    pddl_white_star,
			    pddl_action_def_body(Symbol,Variables,Types,Preconds,Effects),
			    pddl_white_star, ascii(")"), !,
			    {construct_action_axioms(Axioms,Symbol,Variables,Types,Preconds,Effects)},
			    {announce_fin(Symbol,"body")},
			    {announce_suc("action")}.

pddl_action_symbol(Symbol) --> pddl_name_atom(Symbol).

pddl_action_def_body(Symbol,Variables,Types,Preconds,Effects) --> 
	([], {Preconds=[]}; ascii(":precondition"), !, pddl_white_plus,
	pddl_emptyOr(pddl_pre_gd(Symbol,Variables,Types,Preconds),Preconds)),
	{announce_fin(Symbol,"preconditions")},
	pddl_white_star,
	([], {Effects=[]}; ascii(":effect"), !, pddl_white_plus,
	pddl_emptyOr(pddl_effect(Symbol,Variables,Types,Effects),Effects)).

pddl_emptyOr(_,[]) --> ascii("("), pddl_white_star, ascii(")"), !.
pddl_emptyOr(X,_) --> X.

pddl_pre_gd_star(_,_,_,[]) --> [].
pddl_pre_gd_star(S,V,T,[G|GL]) --> pddl_pre_gd(S,V,T,G),
	pddl_white_star, pddl_pre_gd_star(S,V,T,GL).

pddl_pre_gd(S,V,T,G) --> pddl_pref_gd(S,V,T,G).
pddl_pre_gd(S,V,T,and(GL)) --> ascii("("), pddl_white_star, ascii("and"), pddl_white_plus,
	        pddl_pre_gd_star(S,V,T,GL), pddl_white_star, ascii(")").
pddl_pre_gd(S,V,T,forall(V1,T1,G)) --> ascii("("), pddl_white_star, ascii("forall"),
	        {must_support(universal-preconditions)},
		pddl_white_star, ascii("("), pddl_white_star,
		pddl_typed_list_variable(V1,T1),
		pddl_white_star, ascii(")"), pddl_white_plus,
		{append(V,V1,V2), append(T,T1,T2)},
		pddl_pre_gd(S,V2,T2,G), pddl_white_star, ascii(")").

pddl_pref_gd(_,_,_,_) --> ascii("("), pddl_white_star,
                 ascii(":preference"),
		 {must_support(preferencenes)},
		 {cannot_compile(preferences)},
		 pddl_white_plus,
		 ([]; pddl_pref_name(_), pddl_white_plus),
		 pddl_gd(_,_,_,_), pddl_white_star, ascii(")").
pddl_pref_gd(S,V,T,G) --> pddl_gd(S,V,T,G).

pddl_pref_name(Name) --> pddl_name_atom(Name).

pddl_gd(_,V,T,G) --> pddl_atomic_formula_term(V,T,G).
pddl_gd(_,V,T,G) --> pddl_literal_term(V,T,G), {must_support(negative-preconditions)}.
pddl_gd(S,V,T,and(GL)) --> ascii("("), pddl_white_star, ascii("and"),
            pddl_white_star, pddl_gd_star(S,V,T,GL),
	    pddl_white_star, ascii(")"). 
pddl_gd(S,V,T,or(GL)) --> ascii("("), pddl_white_star, ascii("or"), 
            {must_support(disjunctive-preconditions)},
	    pddl_white_star,
	    pddl_gd_star(S,V,T,GL), pddl_white_star, ascii(")").
pddl_gd(S,V,T,neg(G)) --> ascii("("), pddl_white_star, ascii("not"),
	    {must_support(disjunctive-preconditions)},
	    pddl_white_star, pddl_gd(S,V,T,G), pddl_white_star,
	    ascii(")").
pddl_gd(S,V,T,impl(G1,G2)) --> ascii("("), pddl_white_star, ascii("imply"),
	    {must_support(disjunctive-preconditions)},
	    pddl_white_star, pddl_gd(S,V,T,G1), pddl_white_star,
	    pddl_gd(S,V,T,G2), pddl_white_star, ascii(")").
pddl_gd(S,V,T,some(V1,T1,G)) --> ascii("("), pddl_white_star, ascii("exists"),
	    {must_support(existential-preconditions)},
	    pddl_white_star, ascii("("), pddl_white_star,
	    pddl_typed_list_variable(V1,T1), pddl_white_star,
	    ascii(")"), {append(V,V1,V2), append(T,T1,T2)}, 
	    pddl_white_star, pddl_gd(S,V2,T2,G), pddl_white_star,
	    ascii(")").
pddl_gd(S,V,T,all(V1,T1,G)) --> ascii("("), pddl_white_star, ascii("forall"),
	    {must_support(universal-preconditions)},
	    pddl_white_star, ascii("("), pddl_white_star,
	    pddl_typed_list_variable(V1,T1), pddl_white_star,
	    ascii(")"), {append(V,V1,V2), append(T,T1,T2)},
	    pddl_white_star, pddl_gd(S,V2,T2,G), pddl_white_star,
	    ascii(")").
pddl_gd(_,_,_,_) --> pddl_f_comp, {must_support(fluents), cannot_compile(fluents)}.

pddl_gd_star(_,_,_,[]) --> [].
pddl_gd_star(S,V,T,[G|GL]) --> pddl_gd(S,V,T,G), pddl_white_star, pddl_gd_star(S,V,T,GL).

pddl_f_comp --> ascii("("), pddl_white_star, pddl_binary_comp,
	        pddl_white_star, pddl_f_exp, pddl_white_plus,
		pddl_f_exp, pddl_white_star, ascii(")").


pddl_literal_term(V,T,G) --> pddl_atomic_formula_term(V,T,G).
pddl_literal_term(V,T,neg(G)) --> ascii("("), pddl_white_star, ascii("not"),
                      pddl_white_star, pddl_atomic_formula_term(V,T,G),
		      pddl_white_star, ascii(")").

pddl_atomic_formula_term(V,T,G) --> ascii("("), pddl_white_star,
	                     pddl_predicate(Name), pddl_white_plus,
			     pddl_term_star(V,T,Terms), pddl_white_star,
			     ascii(")"), {G=..[Name|Terms]}.

% begin: this is not in the BNF, but should be

pddl_atomic_formula_term(V,T,(T1 = T2)) --> ascii("("), pddl_white_star, ascii("="),
                             pddl_white_plus, 
			     {must_support(equality)},
			     pddl_term(V,T,T1),
			     pddl_white_plus, pddl_term(V,T,T2),
			     pddl_white_star, ascii(")").

% end: this is not in BNF, but should be

pddl_term_star(_,_,[]) --> [].
pddl_term_star(V,T,[Term]) --> pddl_term(V,T,Term).
pddl_term_star(V,T,[Term|Terms]) --> pddl_term(V,T,Term), pddl_white_plus, pddl_term_star(V,T,Terms).

pddl_term(_,_,Constant) --> pddl_name_atom(Constant).
pddl_term(V,_,Variable) --> pddl_variable(Variable), {member(Variable,V)}.

pddl_f_exp(N) --> pddl_number(N).
pddl_f_exp(Exp) --> ascii("("), pddl_white_star, pddl_binary_op(Op),
               pddl_white_star, pddl_f_exp(Exp1), pddl_white_plus,
	       pddl_f_exp(Exp2), pddl_white_star, ascii(")"), {Exp =.. [Op,Exp1,Exp2]}.
pddl_f_exp(Exp) --> ascii("("), pddl_white_star, ascii("-"),
	       pddl_white_star, pddl_f_exp(Exp1), pddl_white_star,
	       ascii(")"), {Exp =.. ['-',Exp1]}.
pddl_f_exp(Head) --> pddl_f_head(Head).

pddl_f_head(Head) --> ascii("("), pddl_white_star, pddl_function_symbol(F),
	        pddl_white_plus, pddl_term_star(_V,_T,Terms), pddl_white_star,
		ascii(")"), {Head =.. [F|Terms]}.
pddl_f_head(Head) --> pddl_function_symbol(Head).

pddl_binary_op(X) --> pddl_multi_op(X).
pddl_binary_op('-') --> ascii("-").
pddl_binary_op('/') --> ascii("/").

pddl_multi_op('*') --> ascii("*").
pddl_multi_op('+') --> ascii("+").

pddl_binary_comp --> ascii(">"); ascii("<"); ascii("="); ascii(">=").

pddl_effect(S,V,T,and(EL)) --> ascii("("), pddl_white_star, ascii("and"),
	        pddl_white_star, pddl_c_effect_star(S,V,T,EL),
	        pddl_white_star, ascii(")").
pddl_effect(S,V,T,E) --> pddl_c_effect(S,V,T,E).

pddl_c_effect(S,V,T,forall(V1,T1,E)) --> ascii("("), pddl_white_star, ascii("forall"),
	          {must_support(conditional-effects)},
		  pddl_white_star, ascii("("), pddl_white_star,
		  % BNF requires "pddl_typed_list_variable_star,
		  % however this should be equivalent:
		  pddl_typed_list_variable(V1,T1), pddl_white_star,
		  ascii(")"), 
		  {append(V,V1,V2), append(T,T1,T2)},
		  pddl_white_star, pddl_effect(S,V2,T2,E),
		  pddl_white_star, ascii(")").
pddl_c_effect(S,V,T,when(G,E)) --> ascii("("), pddl_white_star, ascii("when"),
	          {must_support(conditional-effects)},
		  pddl_white_star, pddl_gd(S,V,T,G), pddl_white_star,
		  pddl_cond_effect(S,V,T,E), pddl_white_star, ascii(")").
pddl_c_effect(S,V,T,E) --> pddl_p_effect(S,V,T,E).

pddl_c_effect_star(_,_,_,[]) --> [].
pddl_c_effect_star(S,V,T,[E|EL]) --> pddl_c_effect(S,V,T,E),
	pddl_white_star, pddl_c_effect_star(S,V,T,EL).

pddl_p_effect(_,V,T,del(E)) --> ascii("("), pddl_white_star, ascii("not"),
	          pddl_white_star, pddl_atomic_formula_term(V,T,E),
		  pddl_white_star, ascii(")").
pddl_p_effect(_,V,T,add(E)) --> pddl_atomic_formula_term(V,T,E).
pddl_p_effect(_,_,_,_) --> ascii("("), pddl_white_star, pddl_assign_op,
	          {must_support(fluents), cannot_compile(fluents)},
		  pddl_white_plus, pddl_f_head(_), pddl_white_plus, pddl_f_exp,
		  pddl_white_star, ascii(")").

pddl_p_effect_star(_,_,_,[]) --> [].
pddl_p_effect_star(S,V,T,[E|EL]) --> pddl_p_effect(S,V,T,E),
	pddl_white_star, pddl_p_effect_star(S,V,T,EL).

pddl_cond_effect(S,V,T,and(EL)) --> ascii("("), pddl_white_star, ascii("and"),
	             pddl_white_star, pddl_p_effect_star(S,V,T,EL),
		     pddl_white_star, ascii(")").
pddl_cond_effect(S,V,T,E) --> pddl_p_effect(S,V,T,E).

pddl_assign_op --> ascii("assign"); ascii("scale-up");
	           ascii("scale-down"); ascii("increase");
		   ascii("decrease").


% Durative Actions %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

pddl_durative_action_def(Axioms) --> ascii("("), pddl_white_star,
	                        ascii(":durative-action"), !,
                                {must_support(durative-actions)},
                                {cannot_compile(durative-actions)},
				{announce_pro("durative action")},
				pddl_white_plus, pddl_da_symbol(Symbol),
				pddl_white_plus, ascii(":parameters"),
				pddl_white_star, ascii("("),
				pddl_white_star,
				pddl_typed_list_variable(Variables,Types),
				pddl_white_star, ascii(")"),
				pddl_white_star, pddl_da_def_body(Symbol,Variables,Types,Duration,Conds,Effects),
				pddl_white_star, ascii(")"), !,
                                {construct_durative_action_axioms(Axioms,Symbol,Variables,Types,Duration,Conds,Effects)},
			        {announce_fin(Symbol,"body")},
				{announce_suc("durative action")}.

pddl_da_symbol(Name) --> pddl_name_atom(Name).

pddl_da_def_body(Symbol,Variables,Types,Duration,Conds,Effects) --> ascii(":duration"), pddl_white_star,
	             pddl_duration_constraint(Duration), pddl_white_star,
		     ascii(":condition"), pddl_white_star,
		     pddl_emptyOr(pddl_da_gd(Symbol,Variables,Types,Conds),Conds), pddl_white_star,
		     ascii(":effect"), pddl_white_star,
		     pddl_emptyOr(pddl_da_effect(Symbol,Variables,Types,Effects),Effects).

pddl_da_gd(Symbol,Variables,Types,Conds) --> pddl_pref_timed_gd(Symbol,Variables,Types,Conds).
pddl_da_gd(Symbol,Variables,Types,and(Conds)) --> ascii("("), pddl_white_star, ascii("and"),
	       pddl_white_star, pddl_da_gd_star(Symbol,Variables,Types,Conds), pddl_white_star,
	       ascii(")").
pddl_da_gd(Symbol,Variables,Types,all(V,T,G)) --> ascii("("), pddl_white_star, ascii("forall"),
	       {must_support(universal-preconditions)},
	       pddl_white_star, ascii("("), pddl_white_star,
	       pddl_typed_list_variable(V1,T1), pddl_white_star,
               {append(Variables,V1,V), append(Types,T1,T)},
	       ascii(")"), pddl_white_star, pddl_da_gd(Symbol,V,T,G),
	       pddl_white_star, ascii(")").

pddl_da_gd_star(_Symbol,_Variables,_Types,[]) --> [].
pddl_da_gd_star(Symbol,Variables,Types,[Cond|Conds]) --> pddl_da_gd(Symbol,Variables,Types,Cond), pddl_white_star, pddl_da_gd_star(Symbol,Variables,Types,Conds).

pddl_pref_timed_gd(Symbol,Variables,Types,Conds) --> pddl_timed_gd(Symbol,Variables,Types,Conds).
pddl_pref_timed_gd(Symbol,Variables,Types,pddl_timed_pref(Conds)) --> ascii("("), pddl_white_star,
	               ascii("preference"),
		       {must_support(preferences)}, pddl_white_star,
		       pddl_timed_gd(Symbol,Variables,Types,Conds), pddl_white_star, ascii(")").
pddl_pref_timed_gd(Symbol,Variables,Types,pddl_timed_pref(Name,Conds)) --> ascii("("), pddl_white_star,
	               ascii("preference"),
		       {must_support(preferences)}, pddl_white_plus,
		       pddl_pref_name(Name), pddl_white_star, pddl_timed_gd(Symbol,Variables,Types,Conds),
		       pddl_white_star, ascii(")").

pddl_timed_gd(Symbol,Variables,Types,pddl_at(TimeSpecifier,Goal)) --> ascii("("), pddl_white_star, ascii("at"),
	          pddl_white_plus, pddl_time_specifier(TimeSpecifier),
		  pddl_white_star, pddl_gd(Symbol,Variables,Types,Goal), pddl_white_star,
		  ascii(")").
pddl_timed_gd(Symbol,Variables,Types,pddl_over(Interval,Goal)) --> ascii("("), pddl_white_star, ascii("over"),
	          pddl_white_plus, pddl_interval(Interval), pddl_white_star,
		  pddl_gd(Symbol,Variables,Types,Goal), pddl_white_star, ascii(")").

pddl_time_specifier(start) --> ascii("start").
pddl_time_specifier(end) --> ascii("end").

pddl_interval(all) --> ascii("all").

pddl_duration_constraint(and(DurationConstraints)) --> ascii("("), pddl_white_star,
	                     ascii("and"),
			     {must_support(duration-inequalities)}, 
			     pddl_simple_duration_constraint_plus(DurationConstraints),
			     pddl_white_star, ascii(")").
pddl_duration_constraint(true) --> ascii("("), pddl_white_star, ascii(")").
pddl_duration_constraint(Duration) --> pddl_simple_duration_constraint(Duration).

pddl_simple_duration_constraint(pddl_d_op(Op,Value)) --> ascii("("), pddl_white_star,
	                            pddl_d_op(Op), pddl_white_star,
				    ascii("?duration"),
				    pddl_white_plus, pddl_d_value(Value),
				    pddl_white_star, ascii(")").
pddl_simple_duration_constraint(pddl_at(TimeSpecifier,Constraint)) --> ascii("("), pddl_white_star,
	                            ascii("at"), pddl_white_plus,
				    pddl_time_specifier(TimeSpecifier),
				    pddl_white_star,
				    pddl_simple_duration_constraint(Constraint),
				    pddl_white_star, ascii(")").

pddl_simple_duration_constraint_plus([Constraint]) -->
	pddl_simple_duration_constraint(Constraint).
pddl_simple_duration_constraint_plus([Constraint|Constraints]) -->
	pddl_simple_duration_constraint(Constraint),
	pddl_white_star,
	pddl_simple_duration_constraint_plus(Constraints).

pddl_d_op(lessthan) --> ascii("<="), {must_support(duration-inequalities)}.
pddl_d_op(greaterthan) --> ascii(">="), {must_support(duration-inequalities)}.
pddl_d_op(equals) --> ascii("=").

pddl_d_value(Number) --> pddl_number(Number).
pddl_d_value(Exp) --> pddl_f_exp(Exp), {must_support(fluents)}.

pddl_da_effect(Symbol,Variables,Types,and(Effects)) --> ascii("("), pddl_white_star, ascii("and"),
	           pddl_white_star, pddl_da_effect_star(Symbol,Variables,Types,Effects),
		   pddl_white_star, ascii(")").
pddl_da_effect(Symbol,Variables,Types,Effect) --> pddl_timed_effect(Symbol,Variables,Types,Effect).
pddl_da_effect(Symbol,Variables,Types,forall(V1,T1,Effects)) --> ascii("("), pddl_white_star, ascii("forall"),
	           {must_support(conditional-effects)},
		   pddl_white_star, ascii("("), pddl_white_star,
		   pddl_typed_list_variable(V1,T1), pddl_white_star,
                   {append(Variables,V1,V), append(Types,T1,T)},
		   ascii(")"), pddl_white_star, pddl_da_effect(Symbol,V,T,Effects),
		   pddl_white_star, ascii(")").
pddl_da_effect(Symbol,Variables,Types,when(G,E)) --> ascii("("), pddl_white_star, ascii("when"),
	           {must_support(conditional-effects)},
		   pddl_white_star, pddl_da_gd(Symbol,Variables,Types,G), pddl_white_star,
		   pddl_timed_effect(Symbol,Variables,Types,E), pddl_white_star, ascii(")").
pddl_da_effect(Symbol,Variables,Types,pddl_assign(Op,Head,Exp)) --> ascii("("), pddl_white_star, pddl_assign_op(Op),
	           {must_support(fluents)}, pddl_white_plus,
		   pddl_f_head(Head), pddl_white_plus, pddl_f_exp_da(Exp),
		   pddl_white_star, ascii(")").

pddl_da_effect_star(_Symbol,_Variables,_Types,[]) --> [].
pddl_da_effect_star(Symbol,Variables,Types,[Effect|Effects]) --> pddl_da_effect(Symbol,Variables,Types,Effect), pddl_white_star,
	                pddl_da_effect_star(Symbol,Variables,Types,Effects).


pddl_timed_effect(Symbol,Variables,Types,pddl_at(TimeSpecifier,Effects)) --> ascii("("), pddl_white_star, ascii("at"),
	              pddl_white_plus, pddl_time_specifier(TimeSpecifier),
		      pddl_white_star, pddl_a_effect(Symbol,Variables,Types,Effects), pddl_white_star,
		      ascii(")").
pddl_timed_effect(Symbol,Variables,Types,pddl_at(TimeSpecifier,Effects)) --> ascii("("), pddl_white_star, ascii("at"),
	              pddl_white_plus, pddl_time_specifier(TimeSpecifier),
		      pddl_white_star, pddl_f_assign_da(Effects),
		      pddl_white_star, ascii(")").

pddl_timed_effect(Symbol,Variables,Types,pddl_assign(Op,Head,Exp)) --> ascii("("), pddl_white_star, pddl_assign_op_t(Op),
	              {must_support(continuous-effects)},
		      pddl_white_plus, pddl_f_head(Head), pddl_white_plus,

		      % pddl_f_assign_da, % BNF of PDDL 3   (Geriving&Long 2005)
		      pddl_f_exp_t(Exp),       % BNF of PDDL 2.1 (For&Long 2003)

		      pddl_white_star, ascii(")").

% Begin: This is missing in PDDL 3 BNF, took it from Fox&Long 2003

pddl_assign_op_t(increase) --> ascii("increase").
pddl_assign_op_t(increase) --> ascii("decrease").

pddl_f_exp_t(Exp * 'pddl_#t') --> ascii("("), pddl_white_star, ascii("*"),
	         pddl_white_plus, pddl_f_exp(Exp), pddl_white_plus,
		 ascii("#t"), pddl_white_star, ascii(")"). 
pddl_f_exp_t('pddl_#t' * Exp) --> ascii("("), pddl_white_star, ascii("*"),
	         pddl_white_plus, ascii("#t"), pddl_white_plus,
		 pddl_f_exp(Exp), pddl_white_star, ascii(")").
pddl_f_exp_t('pddl_#t') --> ascii("#t").

% End.

% Begin: The following is also missing; it is my guess.

pddl_a_effect(Symbol,Variables,Types,Effects) --> pddl_effect(Symbol,Variables,Types,Effects). % I hope this is right :)

% End.

pddl_f_assign_da(pddl_f_assign_da(Op,Head,Exp)) --> ascii("("), pddl_white_star, pddl_assign_op(Op),
	             pddl_white_plus, pddl_f_head(Head), pddl_white_plus,
		     pddl_f_exp_da(Exp), pddl_white_star, ascii(")").

pddl_f_exp_da(Exp) --> ascii("("), pddl_binary_op(Op), pddl_white_star,
	          pddl_f_exp_da(Exp1), pddl_white_plus, pddl_f_exp_da(Exp2),
		  pddl_white_star, ascii(")"), {Exp =.. [Op,Exp1,Exp2]}.
pddl_f_exp_da(Exp) --> ascii("("), pddl_white_star, ascii("-"),
	          pddl_white_star, pddl_f_exp_da(Exp1), pddl_white_star,
		  ascii(")"), {Exp =.. ['-',Exp1]}.
pddl_f_exp_da('pddl_duration') --> ascii("?duration"),
                  {must_support(duration-inequalities)}.
pddl_f_exp_da(Exp) --> pddl_f_exp(Exp).

% Derived Predicates%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% This is what is required by the BNF...
%pddl_derived_def --> ascii("("), pddl_white_star, ascii(":derived"),
% 	              pddl_white_plus, pddl_typed_list_variable(_,_),
%	              pddl_white_plus, pddl_gd, pddl_white_star,
%		      ascii(")").

% ...but I think this was meant:
pddl_derived_def([]) --> ascii("("), pddl_white_star, ascii(":derived"), !,
	                     {must_support(derived-predicates),
                              cannot_compile(derived-predicates)},
                             pddl_white_plus, pddl_atomic_formula_term(_,_,_),
			     pddl_white_plus, pddl_gd(_,_,_,_), pddl_white_star,
			     ascii(")").

% i.e. atomic formula instead of typed variable list.
% Cp. also Edelkamp & Hoffmann 2004, p. 4

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% PDDL Problems
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

pddl_problem(axioms(Problem,Domain,ObjectAxioms,InitAxioms,GoalAxioms)) --> 
        pddl_white_star, ascii("("), pddl_white_star,
        ascii("define"), pddl_white_star, ascii("("),
        pddl_white_star, ascii("problem"),
        pddl_white_star, pddl_problem_name(Problem),
        pddl_white_star, ascii(")"), pddl_white_star,
        ascii("("), pddl_white_star,
        ascii(":domain"), pddl_white_star,
        pddl_problem_domain(Domain), pddl_white_star,
        ascii(")"), pddl_white_star,
        ([]; pddl_problem_requirements, pddl_white_star),
        ([]; pddl_object_declarations(ObjectAxioms), pddl_white_star),
        pddl_init(InitAxioms), pddl_white_star,
        pddl_goal(GoalAxioms), pddl_white_star,
        ([]; pddl_problem_constraints, pddl_white_star),
        ([]; pddl_metric_spec, pddl_white_star),
        ([]; pddl_length_spec, pddl_white_star),
        ascii(")"), pddl_white_star.

pddl_problem_name(Name) --> pddl_name_atom(Name).

pddl_problem_domain(Name) -->  pddl_name_atom(Name). % maybe put a test here?

pddl_problem_requirements --> pddl_requirements.

pddl_object_declarations(Axioms) --> ascii("("), pddl_white_star,
                               ascii(":objects"), !,
			       {announce_pro("objects")},
			       pddl_white_plus,
			       pddl_typed_list_name(ObjectsDefs),
			       pddl_white_star, ascii(")"), !,
                               {constants_declaration(ObjectsDefs,Axioms)},
			       {announce_suc("objects")}.

pddl_init(Axioms) --> ascii("("), pddl_white_star, ascii(":init"), !,
                      {announce_pro("init")},
                      pddl_white_plus,
                      pddl_init_el_star(Axioms),
                      pddl_white_star, ascii(")"),
                      {announce_suc("init")}.

pddl_init_el_star([Axiom|Axioms]) --> pddl_init_el(Axiom), pddl_white_star,
                                      pddl_init_el_star(Axioms).
pddl_init_el_star([]) --> [].

pddl_init_el(initially(Atom,true)) --> pddl_literal_name(Atom).
pddl_init_el([]) --> ascii("("), pddl_white_star, ascii("="),
        {must_support(fluents), cannot_compile(fluents)},
        pddl_white_star, pddl_f_head(_), pddl_white_plus, pddl_number(_),
        pddl_white_star, ascii(")").
pddl_init_el([]) --> ascii("("), pddl_white_star, ascii("at"),
        {must_support(timed-initial-literals), cannot_compile(timed-initial-literals)},
        pddl_white_plus, pddl_number(_), pddl_white_star,
        pddl_literal_name(_), pddl_white_star, ascii(")").

pddl_literal_name(Axiom) --> pddl_atomic_formula_name(Axiom).
pddl_literal_name(Axiom) --> ascii("("), pddl_white_star,
        ascii("not"), pddl_white_plus,
        pddl_atomic_formula_name(Axiom), pddl_white_star, ascii(")").

pddl_atomic_formula_name(Atom) --> ascii("("), pddl_white_star,
        pddl_predicate(PName), pddl_white_plus, pddl_name_star(Names),
        pddl_white_star, ascii(")"), {Atom =.. [PName|Names]}.


pddl_goal([goal(F)]) --> ascii("("), pddl_white_star, ascii(":goal"), !,
        {announce_pro("goal")}, pddl_white_plus, pddl_pre_gd(goal,[],[],Preconds),
        pddl_white_star, ascii(")"),
        {convert_precondition_formula(Preconds,F), announce_suc("goal")}.

pddl_problem_constraints --> ascii("("), pddl_white_star,
        ascii(":constraints"), !, {must_support(constraints),
                                   cannot_compile(constraints)},
        pddl_white_plus, pddl_pref_con_gd, pddl_white_star,
        ascii(")").

pddl_pref_con_gd --> ascii("("), pddl_white_star, ascii("and"),
        pddl_white_plus, pddl_pref_con_gd_star, pddl_white_star,
        ascii(")").
pddl_pref_con_gd --> ascii("("), pddl_white_star, ascii("forall"),
        {must_support(universal-preconditions)},
        pddl_white_star, ascii("("), pddl_white_star,
        pddl_typed_list_variable(_,_), pddl_white_star, ascii(")"),
        pddl_white_star, pddl_con_gd, pddl_white_star, ascii(")").
pddl_pref_con_gd --> ascii("("), pddl_white_star,
        ascii("preference"), {must_support(preferences),
                               cannot_compile(preferences)},
        pddl_white_plus, ([]; pddl_pref_name(_), pddl_white_star),
        pddl_con_gd, pddl_white_star, ascii(")").
pddl_pref_con_gd --> pddl_con_gd.

pddl_pref_con_gd_star --> [].
pddl_pref_con_gd_star --> pddl_pref_con_gd, pddl_white_star,
        pddl_pref_con_gd_star.

pddl_metric_spec --> ascii("("), pddl_white_star,
        ascii(":metric"), !,
        pddl_white_plus, pddl_optimization,
        pddl_white_plus, pddl_metric_f_exp, pddl_white_star,
        ascii(")").

pddl_optimization --> ascii("minimize"); ascii("maximize").

pddl_metric_f_exp --> ascii("("), pddl_white_star, pddl_binary_op,
        pddl_white_plus, pddl_metric_f_exp, pddl_white_plus,
        pddl_metric_f_exp, pddl_white_star, ascii(")").
pddl_metric_f_exp --> ascii("("), pddl_white_star, pddl_multi_op,
        pddl_white_plus, pddl_metric_f_exp, pddl_white_plus,
        pddl_metric_f_exp_plus, pddl_white_star, ascii(")").
pddl_metric_f_exp --> ascii("("), pddl_white_star, ascii("-"),
        pddl_white_star, pddl_metric_f_exp, pddl_white_star,
        ascii(")").
pddl_metric_f_exp --> pddl_number(_).
pddl_metric_f_exp --> ascii("("), pddl_white_star,
        pddl_function_symbol, pddl_white_plus, pddl_name_star(_),
        pddl_white_star, ascii(")").
pddl_metric_f_exp --> pddl_function_symbol.
pddl_metric_f_exp --> ascii("total-time").
pddl_metric_f_exp --> ascii("("), pddl_white_star,
        ascii("is-violated"), pddl_white_plus, pddl_pref_name(_),
        pddl_white_star, ascii(")").

pddl_metric_f_exp_plus --> pddl_metric_f_exp.
pddl_metric_f_exp_plus --> pddl_metric_f_exp, pddl_white_plus, pddl_metric_f_exp_plus.

pddl_length_spec --> []. % this is defined nowhere :(

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Auxiliary stuff
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

pddl_name_atom(Name) --> 
        pddl_name2(CList),
        {string_codes(String,CList),
         atom_string(Name,String)}.
pddl_name2([C|List]) --> pddl_name_first_char(C), pddl_name_char_list(List).

% first character of a name is a letter
pddl_name_first_char(C) --> [C], {uppercasechar(C); lowercasechar(C)}.

pddl_name_char(C) --> [C], {uppercasechar(C); lowercasechar(C)}.
pddl_name_char(C) --> [C], {C=95; C=45}. % C="_", C="-"
pddl_name_char(C) --> [C], {digit(C)}.

pddl_name_char_list([]) --> [].
pddl_name_char_list([C|List]) --> pddl_name_char(C), pddl_name_char_list(List).

uppercasechar(C) :- C>=65, C=<90. % C>="A" , C=<"Z"
lowercasechar(C) :- C>=97, C=<122. % C>="a" , C=<"z"
digit(C) :- C>=48, C=<57. % C>="0" , C=<"9"

first_char_to_upper(StringLower,StringUpper) :-
        string_codes(StringLower,[CLower|List]),
	char_to_upper(CLower,CUpper),
	string_codes(StringUpper,[CUpper|List]).
char_to_upper(CLower,CUpper) :- lowercasechar(CLower) -> CUpper is CLower-32 ; CUpper=CLower.

pddl_white_plus --> pddl_white, !, pddl_white_star.
pddl_white_star --> pddl_white, !, pddl_white_star.
pddl_white_star --> [].

pddl_white --> [C], ({C=59} /* ";" */, !, all_to_end_of_line ; {whitespace(C), !}).
whitespace(32). % " "
whitespace(9).  % "\t"
whitespace(13). % "\r"
whitespace(10). % "\n"
whitespace(12). % "\f"

all_to_end_of_line --> pddl_newline, !.
all_to_end_of_line --> [_], all_to_end_of_line.

pddl_newline --> [10]. % "\n"

ascii(String) --> {string_codes(String, List)}, checkList(List).

checkList([]) --> [].
checkList([A|L]) --> [A], checkList(L).

% for testing and debugging
stuff --> char_star.

char_star --> [].
char_star --> [_], char_star.

% debugging outputs
announce_pro(X) :- (debug_mode(true) -> (write("Processing "),
                                         write(X), write("...\n"), flush_output(user_output)); true).
announce_suc(X) :- (debug_mode(true) -> (write("Succeeded processing "), write(X),
	write(".\n"), flush_output(user_output)); true).
announce_cur(X) :- (debug_mode(true) -> (write("Currently processing structure >>"),
	write(X), write("<<.\n"), flush_output(user_output)); true).
announce_fin(S,X) :- (debug_mode(true) -> (write("Finished part >>"), write(X), 
	write("<< of structure >>"), write(S), write("<<.\n"), flush_output(user_output)); true).

% list_same_length(X,L,L1) creates a list L1 of the same length as L with only X's
list_same_length(X,[_|L],[X|L1]) :- list_same_length(X,L,L1).
list_same_length(_,[],[]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Helping predicates for generating Golog clauses 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

construct_action_axioms(Axioms,Symbol,Variables,Types,Preconds,Effects) :-
        pddl_vars_to_prolog_vars(Variables,PVariables),
        Action_Term =.. [Symbol | PVariables],
        convert_precondition_formula(Preconds,CPreconds),
        convert_effect_formula(Action_Term,Effects,LCEffects),
        substitute_pddl_vars((CPreconds,LCEffects),Variables,PVariables,(CVPreconds,LCVEffects)),
	Axioms = [(prim_action(Action_Term)),
                  (action_parameter_types(Symbol,Types)),
                  (poss(Action_Term,CVPreconds))|
                  LCVEffects].

% Given a list of PDDL variables of the form '?variablename',
% constructs a list of the same length with fresh Prolog variables.
pddl_vars_to_prolog_vars([],[]) :- !.
pddl_vars_to_prolog_vars([_Var|Vars],[PVar|PVars]) :- !,
        copy_term(_X,PVar),
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
convert_effect_formula(AT,E,LCE) :- convert_effect_formula(AT,[],[],E,LCE).
                                   % additional params = quantified variables
                                   % and their types
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

% Convert the list of types with associated constants into Prolog clauses.
constants_declaration([ConstantsDef|Defs], [Axiom|Axioms]) :-
        ConstantsDef =.. [Type, ConstantsList],
        Axiom_Header = domain(Type,X),
        Axiom = (Axiom_Header :- member(X,ConstantsList)),
        constants_declaration(Defs,Axioms).
constants_declaration([],[]).

% For additional typing axioms of the form "subtypes(vehicle,[car,truck])."
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
