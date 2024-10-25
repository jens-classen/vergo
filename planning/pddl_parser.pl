/**

PDDL Parser

This module provides predicates for parsing domain and problem
descriptions in the Planning Domain Definition Language (PDDL), and
translating them into an equivalent description in terms of a Golog
action theory.

Parsing works for the full language of PDDL 3.1 [Kovacs 2011].
Translation [Claßen 2013, Ch. 4], [Claßen et al. 2007] is currently
supported for the ADL fragment only; everything else will be ignored.
More precisely, the following requirement flags are covered:

         :strips
         :typing
         :negative-preconditions
         :disjunctive-preconditions
         :equality
         :existential-preconditions
         :universal-preconditions
         :quantified-preconditions
         :conditional-effects
         :adl
         :fluents
         :numeric-fluents
         :object-fluents
         :action-costs

References:

      [Claßen et al. 2007] Claßen, J.; Eyerich, P.; Lakemeyer, G.;
           and Nebel, B. 2007. Towards an integration of Golog
           and planning. In Proceedings of IJCAI-07, AAAI Press.

      [Claßen 2013] Claßen, J. 2013. Planning and Verification in the
           Agent Language Golog. PhD Thesis, Department of Computer
           Science, RWTH Aachen University, 2013.

      [Kovacs 2011] Kovacs, D.L. BNF Definition of PDDL3.1:
           completely corrected, without comments.

@author  Jens Claßen
@license GPLv2

**/

:- module(pddl_parser, [parse_pddl_domain/3,
                        parse_pddl_problem/3]).

:- use_module(library(dcg/basics)).

:- use_module('../lib/env').
:- use_module('../lib/utils').
:- use_module('../logic/l').

:- dynamic requirement/1.

:- dynamic user:type/1.
:- dynamic user:subtype/2.
:- dynamic user:rel_fluent/2.
:- dynamic user:fun_fluent/3.
:- dynamic user:cwa/1.
:- dynamic user:poss/3.
:- dynamic user:causes_true/3.
:- dynamic user:causes_false/3.
:- dynamic user:causes/4.
:- dynamic user:goal/2.
:- dynamic user:metric/2.

/**
  * parse_pddl_domain(++From,+To,-SymbolTable) is semidet.
  *
  * Parses a PDDL domain definition and translates it to equivalent
  * axioms for a Golog action theory. The PDDL definition can either
  * be provided as a string, or by means of passing the path of a PDDL
  * file. Similarly, Golog axioms can be returned in the form of a
  * Prolog term containing lists with axioms of the different types
  * (that can then be asserted to the current DB), or written to a
  * file, or asserted directly into user space. Additionally, a
  * "symbol table" is returned, i.e. a term that holds the domain name
  * and information (names, arities, types) about types, predicates,
  * functions, and constants. The symbol table of the associated
  * domain is to be provided when parsing a PDDL problem description.
  *
  * @arg From        a term of the form string(String), or
  *                  a term of the form file(FileName)
  * @arg To          a term of the form axioms(Axioms), or
  *                  a term of the form file(File), or 'userdb'
  * @arg SymbolTable a term of the form dom(D,T,C,P,F,FT)
  */
parse_pddl_domain(string(String),To,Symbols) :- !,
        string_codes(String,Codes),
        phrase(pddl_domain(Symbols,Axioms),Codes),
        parse_pddl_result(Axioms,To).
parse_pddl_domain(file(File),To,Symbols) :- !,
        phrase_from_file(pddl_domain(Symbols,Axioms),File),
        parse_pddl_result(Axioms,To).

/**
  * parse_pddl_problem(++From,+To,++SymbolTable) is semidet.
  *
  * Parses a PDDL problem definition and translates it to equivalent
  * axioms for a Golog action theory. The PDDL definition can either
  * be provided as a string, or by means of passing the path of a PDDL
  * file. Similarly, Golog axioms can be returned in the form of a
  * Prolog term containing lists with axioms of the different types
  * (that can then be asserted to the current DB), or written to a
  * file, or asserted directly into user space. Additionally, a
  * "symbol table" needs to be provided, i.e. a term that holds the
  * domain name and information (names, arities, types) about types,
  * predicates, functions, and constants, and is the result of parsing
  * a PDDL domain description.
  *
  * @arg From        a term of the form string(String), or
  *                  a term of the form file(FileName)
  * @arg To          a term of the form axioms(Axioms), or
  *                  a term of the form file(File), or 'userdb'
  * @arg SymbolTable a term of the form dom(D,T,C,P,F,FT)
  */
parse_pddl_problem(string(String),To,Symbols) :- !,
        string_codes(String,Codes),
        phrase(pddl_problem(Symbols,Axioms),Codes),
        parse_pddl_result(Axioms,To).
parse_pddl_problem(file(File),To,Symbols) :- !,
        phrase_from_file(pddl_problem(Symbols,Axioms),File),
        parse_pddl_result(Axioms,To).

parse_pddl_result(AxiomsT,axioms(Axioms)) :-
        AxiomsT =.. [domax,_Domain|AxiomsL], !,
        flatten(AxiomsL,Axioms).
parse_pddl_result(Axioms,file(File)) :-
        Axioms = domax(Domain,Type_Axioms,Constant_Axioms,
                       Predicate_Axioms,Function_Axioms,
                       Constraint_Axioms,Structure_Axioms), !,
        open(File, write, Stream),
        write_domain_header(Stream, Domain),
        write_directives(Stream),
        write_rules(Stream, Type_Axioms, "Typing Axioms"),
        write_rules(Stream, Constant_Axioms, "Constant Definitions"),
        write_rules(Stream, Predicate_Axioms, "Predicate Definitions"),
        write_rules(Stream, Function_Axioms, "Function Definitions"),
        write_rules(Stream, Constraint_Axioms, "Constraints"),
        write_rules(Stream, Structure_Axioms, "Structures (Actions)"),
        close(Stream).
parse_pddl_result(AxiomsT,axioms(Axioms)) :-
        AxiomsT =.. [proax,_Problem,_Domain|AxiomsL], !,
        flatten(AxiomsL,Axioms).
parse_pddl_result(Axioms,file(File)) :-
        Axioms = proax(Problem,Domain,ObjectAxioms,InitAxioms,
                       GoalAxioms,MetricAxioms),
        open(File, write, Stream),
        write_problem_header(Stream, Problem, Domain),
        write_rules(Stream, ObjectAxioms, "Objects"),
        write_rules(Stream, InitAxioms, "Initial Values"),
        write_rules(Stream, GoalAxioms, "Goal"),
        write_rules(Stream, MetricAxioms, "Metric"),
        close(Stream).
parse_pddl_result(AxiomsT,userdb) :-
        AxiomsT =.. [domax,_Domain|AxiomsL], !,
        flatten(AxiomsL,Axioms),
        forall(member(Axiom,Axioms),assert(user:Axiom)).
parse_pddl_result(AxiomsT,userdb) :-
        AxiomsT =.. [proax,_Problem,_Domain|AxiomsL], !,
        flatten(AxiomsL,Axioms),
        forall(member(Axiom,Axioms),assert(user:Axiom)).

write_directives(Stream) :- !,
        forall(member(X,["type/1",
                         "subtype/2",
                         "rel_fluent/2",
                         "fun_fluent/3",
                         "cwa/1",
                         "poss/3",
                         "causes_true/3",
                         "causes_false/3",
                         "causes/4"]),
               (write(Stream, ":- discontiguous "),
                write(Stream, X),
                write(Stream, ".\n"))),
        write(Stream, "\n\n").

write_rules(Stream, Axioms, Header) :- !,
        write(Stream,
              "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n"),
        write(Stream, "% "), write(Stream, Header), write(Stream, "\n"),
        write(Stream,
              "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n\n"),
        write_rules2(Stream, Axioms).

write_rules2(Stream, [Axiom|Axioms]) :- !,
        write_axiom_readable(Stream,Axiom),
        %write_axiom(Stream,Axiom),
        write_rules2(Stream,Axioms).
write_rules2(Stream, []) :- write(Stream, "\n\n").

write_axiom(Stream, Axiom) :- !,
        write_term(Stream, Axiom,
                   [quoted(true),fullstop(true),nl(true)]).

write_axiom_readable(Stream, Axiom) :- !,
        \+ \+ (numbervars(Axiom,0,_),
               write_term(Stream, Axiom, [numbervars(true),
                                          quoted(true),
                                          fullstop(true),
                                          nl(true)
                                         ])
              ).

write_domain_header(Stream, DomainName) :- !,
        write(Stream,
              "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n"),
        write(Stream,
              "%\n% Golog axiomatization translated from PDDL domain \""),
        write(Stream, DomainName), write(Stream, "\"\n%\n% "),
        write_time(Stream), write(Stream, "\n%\n"),
        write(Stream,
              "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n\n").

write_problem_header(Stream, Problem, Domain) :- !,
        write(Stream,
              "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n"),
        write(Stream,
              "%\n% Golog axiomatization of problem \""),
        write(Stream, Problem), write(Stream, "\" for PDDL domain \""),
        write(Stream, Domain), write(Stream, "\"\n%\n% "),
        write_time(Stream), write(Stream, "\n%\n"),
        write(Stream,
              "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n\n\n").

write_time(Stream ):- !,
        write(Stream, "Generated by PDDL parser at "),
        local_time_and_date_as_string(TimeAndDate),
        write(Stream, TimeAndDate).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% PDDL grammar starts here
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% PDDL Domains
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

pddl_domain(D,domax(Domain, Type_Axioms, Constant_Axioms,
                    Predicate_Axioms, Function_Axioms,
                    Constraint_Axioms, Structure_Axioms)) -->
        ws, "(", ws, "define", ws,"(", ws, "domain", wp, !,
        pddl_domain_name(Domain), ws, ")", ws,
        ([]; pddl_requirements, ws),
        ([],{Types=[object], Type_Axioms=[type(object)]};
         pddl_type_definitions(Types, Type_Axioms), ws),
        ([],{Constants=[], Constant_Axioms=[]};
         pddl_constant_defs(Constants, Constant_Axioms), ws),
        ([],{Predicates=[], Predicate_Axioms=[]};
         pddl_predicate_defs(Predicates, Predicate_Axioms), ws),
        ([],{Functions=[], FTypes=[], Function_Axioms=[]};
         pddl_functions_defs(Functions, FTypes, Function_Axioms), ws),
        ([],{Constraint_Axioms=[]};
         pddl_constraints(Constraint_Axioms), ws),
        {D = dom(Domain, Types, Constants, Predicates, Functions,
                 FTypes)},
        pddl_structure_def_star(D, Structure_Axioms), ws,
        ")", ws, !,
        {announce_suc("PDDL domain description")}.

pddl_domain_name(Name) -->
        pddl_name_atom(Name,'').
 
% Requirements %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

pddl_requirements -->
        "(", ws, ":requirements", wp, !,
        {retractall(requirement(_))},
        pddl_requirement_plus, ws, ")", !,
        {announce_suc("requirements")}.

pddl_requirement_plus -->
        pddl_requirement, wp,
        pddl_requirement_plus.
pddl_requirement_plus -->
        pddl_requirement.

pddl_requirement -->
        ":strips",
        {assert(requirement(strips))};
        ":typing",
        {assert(requirement(typing))};
        ":negative-preconditions",
        {assert(requirement(negative-preconditions))};
        ":disjunctive-preconditions",
        {assert(requirement(disjunctive-preconditions))};
        ":equality",
        {assert(requirement(equality))};
        ":existential-preconditions",
        {assert(requirement(existential-preconditions))};
        ":universal-preconditions",
        {assert(requirement(universal-preconditions))};
        ":quantified-preconditions",
        {assert(requirement(quantified-preconditions))};
        ":conditional-effects",
        {assert(requirement(conditional-effects))};
        ":fluents",
        {assert(requirement(fluents))};
        ":numeric-fluents",
        {assert(requirement(numeric-fluents))};
        ":adl",
        {assert(requirement(adl))};
        ":durative-actions",
        {assert(requirement(durative-actions))};
        ":duration-inequalities",
        {assert(requirement(duration-inequalities))};
        ":continuous-effects",
        {assert(requirement(continuous-effects))};
        ":derived-predicates",
        {assert(requirement(derived-predicates))};
        ":timed-initial-literals",
        {assert(requirement(timed-initial-literals))};
        ":preferences",
        {assert(requirement(preferences))};
        ":constraints",
        {assert(requirement(constraints))};
        ":action-costs",
        {assert(requirement(action-costs))}.

map_requirement(quantified-preconditions,existential-preconditions).
map_requirement(quantified-preconditions,universal-preconditions).

map_requirement(fluents,numeric-fluents).
map_requirement(fluents,object-fluents).

map_requirement(adl,strips).
map_requirement(adl,typing).
map_requirement(adl,negative-preconditions).
map_requirement(adl,disjunctive-preconditions).
map_requirement(adl,equality).
map_requirement(adl,existential-preconditions).
map_requirement(adl,universal-preconditions).
map_requirement(adl,conditional-effects).

map_requirement(action-costs,fluents).
map_requirement(action-costs,numeric-fluents).
% todo: action costs only allow limited use of numeric fluents,
% cf. [Kovacs 2011] Section 1.3

requires(R) :-
        requires2(R),
        check_support(R).
requires2(R) :-
        requirement(R), !.
requires2(R) :-
        map_requirement(R2,R),
        requirement(R2), !. % e.g. R2=adl, R=conditional-effects
requires2(R) :-
        map_requirement(R,R2),
        requirement(R2), !. % e.g. R2=object-fluents, R=fluents

check_support(R) :-
        supports_requirement(R), !.
check_support(R) :- !,
        report_message(warn,
                       ['Requirement ',R,' is not supported so far!']),
        report_message(warn,
                       ['Proceeding to parse, but will not translate...']).

% supported so far
supports_requirement(strips).
supports_requirement(typing).
supports_requirement(negative-preconditions).
supports_requirement(disjunctive-preconditions).
supports_requirement(equality).
supports_requirement(existential-preconditions).
supports_requirement(universal-preconditions).
supports_requirement(quantified-preconditions).
supports_requirement(conditional-effects).
supports_requirement(adl).
supports_requirement(fluents).
supports_requirement(numeric-fluents).
supports_requirement(object-fluents).
supports_requirement(action-costs).

% not supported so far
supports_requirement(constraints) :- fail.
supports_requirement(preferences) :- fail.
supports_requirement(durative-actions) :- fail.
supports_requirement(timed-initial-literals) :- fail.
supports_requirement(derived-predicates) :- fail.

% Types %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

pddl_type_definitions(Types, Axioms) -->
        {requires(typing)},
        "(", ws, ":types", wp, !,
        pddl_typed_list_name(Types2,Axioms2,subtype,''), ws,
        ")", ws, !,
        {Types = [object|Types2],          % include by default
         Axioms = [type(object)|Axioms2]}, % include by default
        {announce_suc("types")}.

pddl_typed_list_name(Types,[Axiom],Pred,Prefix) -->
       pddl_name_star(Types,Prefix),
       {Head =.. [Pred,object,X],
        Axiom = (Head :- member(X,Types))}.
% this separate rule is needed b/c there may be no whitespace at end
pddl_typed_list_name([Type],[Axiom],Pred,Prefix) -->
        {requires(typing)},
        pddl_name_plus(Names,Prefix),
        wp, "-", wp, %note: spaces before and after "-"!
        pddl_type(Type_name), % <<< *no* whitespace here!
        {Type_name = either(ENames) ->
            Type =.. [either, ENames, Names];
            Type =.. [Type_name, Names]},
        {Head =.. [Pred,Type_name,X],
         Axiom = (Head :- member(X,Names))}.
pddl_typed_list_name([Type|Types],[Axiom|Axioms],Pred,Prefix) -->
        {requires(typing)},
        pddl_name_plus(Names,Prefix),
        wp, "-", wp, %note: spaces before and after "-"!
        pddl_type(Type_name), wp, % <<< whitespace here!
        {Type_name = either(ENames) ->
            Type =.. [either, ENames, Names];
            Type =.. [Type_name, Names]},
        {Head =.. [Pred,Type_name,X],
         Axiom = (Head :- member(X,Names))},
        pddl_typed_list_name(Types,Axioms,Pred,Prefix).

pddl_name_star([],_) --> [].
pddl_name_star(Names,Prefix) -->
        pddl_name_plus(Names,Prefix).

pddl_name_plus([Name],Prefix) -->
        pddl_name_atom(Name,Prefix).
pddl_name_plus([Name|Names],Prefix) -->
        pddl_name_atom(Name,Prefix), wp,
        pddl_name_star(Names,Prefix).

pddl_type(either(Names)) -->
        "(", ws, "either", wp,
        pddl_primitive_type_plus(Names), ws,
        ")".
pddl_type(Name) -->
        pddl_primitive_type(Name).

pddl_primitive_type(Name) -->
        pddl_name_atom(Name,'').
pddl_primitive_type(object) -->
        "object".

pddl_primitive_type_plus([Name]) -->
        pddl_primitive_type(Name).
pddl_primitive_type_plus([Name|Names]) -->
        pddl_name_atom(Name,''), wp,
        pddl_primitive_type_plus(Names).

% Constants %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

pddl_constant_defs(Constants, Axioms) -->
        "(", ws, ":constants", wp, !,
        pddl_typed_list_name(Constants,Axioms,domain,'#'), ws,
        ")", !,
        {announce_suc("constants")}.

% Predicates %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

pddl_predicate_defs(Predicates, Axioms) -->
        "(", ws, ":predicates", wp, !,
        pddl_atomic_formula_skeleton_plus(Predicates,CAxioms,PAxioms), ws,
        ")", !,
        {append(PAxioms,CAxioms,Axioms)},
        {announce_suc("predicates")}.

pddl_atomic_formula_skeleton_plus([Predicate],[CAxiom],[PAxiom]) -->
        pddl_atomic_formula_skeleton(Predicate,CAxiom,PAxiom).
pddl_atomic_formula_skeleton_plus([Predicate|Predicates],
                                  [CAxiom|CAxioms],
                                  [PAxiom|PAxioms]) -->
        pddl_atomic_formula_skeleton(Predicate,CAxiom,PAxiom), ws,
        pddl_atomic_formula_skeleton_plus(Predicates,CAxioms,PAxioms).

pddl_atomic_formula_skeleton(Predicate,CAxiom,PAxiom) -->
        "(", ws, pddl_predicate(PName), wp,
        pddl_typed_list_variable(Variables,Types,PVariables,VarTypes),
        ws, ")",
        {Predicate = pred(PName,Variables,Types),
         Head =.. [PName|PVariables],
         PAxiom = rel_fluent(Head,VarTypes),
         CAxiom = cwa(Head)}.

pddl_predicate(Name) -->
        pddl_name_atom(Name,'').

% no type given => object as default
pddl_typed_list_variable(PDDLVars,Types,PrologVars,VarTypes) -->
        pddl_variable_star(PDDLVars,Types,PrologVars,VarTypes,object).
pddl_typed_list_variable(PDDLVars,Types,PrologVars,VarTypes) -->
        {requires(typing)},
        pddl_variable_plus(PDDLVars1,Types1,PrologVars1,VarTypes1,
                           TypeName),
        wp, "-", wp, %note: spaces before and after "-"!
        pddl_type(TypeName), ws,
        pddl_typed_list_variable(PDDLVars2,Types2,PrologVars2,
                                 VarTypes2),
        {append(PDDLVars1,PDDLVars2,PDDLVars),
         append(Types1,Types2,Types),
         append(PrologVars1,PrologVars2,PrologVars),
         append(VarTypes1,VarTypes2,VarTypes)}.

pddl_variable_star([],[],[],[],_) --> [].
pddl_variable_star(PDDLVars,Types,PrologVars,VarTypes,DefaultType) -->
        pddl_variable_plus(PDDLVars,Types,PrologVars,VarTypes,
                           DefaultType).

pddl_variable_plus([Var],[Type],[PVar],[VarType],DefaultType) -->
        pddl_variable(Var,Type,PVar,VarType,DefaultType).
pddl_variable_plus([Var|Vars],[Type|Types],[PVar|PVars],
                   [VarType|VarTypes],DefaultType) -->
        pddl_variable(Var,Type,PVar,VarType,DefaultType), wp,
        pddl_variable_plus(Vars,Types,PVars,VarTypes,DefaultType).

pddl_variable(Var,Type,PVar,PVar-Type,Type) -->
        "?", pddl_name_atom(Name,''),
        {atom_concat('?',Name,Var)},
        {copy_term(_X,PVar)}. % create new Prolog variable

% Functions %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

pddl_functions_defs(Functions,Types,Axioms) -->
        {requires(fluents)},
        "(", ws, ":functions", wp, !,
        pddl_function_typed_list_atomic_function_skeleton(Functions,
                                                          Types,
                                                          FAxioms,
                                                          CAxioms), ws,
        ")", !,
        {append(FAxioms,CAxioms,Axioms)},
        {announce_suc("functions")}.

pddl_function_typed_list_atomic_function_skeleton(Functions,Types,
                                                  FAxioms,CAxioms) -->
	{requires(numeric-fluents)},
        pddl_atomic_function_skeleton_plus(Functions,Types,FAxioms,
                                           CAxioms,
                                           number). % default type
pddl_function_typed_list_atomic_function_skeleton([],[],[],[]) --> [].
pddl_function_typed_list_atomic_function_skeleton(Functions,Types,
                                                  FAxioms,CAxioms) -->
	pddl_atomic_function_skeleton_plus(Functions1,Types1,FAxioms1,
                                           CAxioms1,Type),
        wp, "-", wp,
        pddl_function_type(Type), ws,
        pddl_function_typed_list_atomic_function_skeleton(Functions2,
                                                          Types2,
                                                          FAxioms2,
                                                          CAxioms2),
        {append(Functions1,Functions2,Functions),
         append(Types1,Types2,Types),
         append(FAxioms1,FAxioms2,FAxioms),
         append(CAxioms1,CAxioms2,CAxioms)}.

pddl_function_type(number) -->
        {requires(numeric-fluents)},
        "number", !.
pddl_function_type(Type) -->
        {requires(typing)},
        {requires(object-fluents)},
        pddl_type(Type), !.

pddl_atomic_function_skeleton_plus([Function],[Type],[FAxiom],[CAxiom],
                                   Type) -->
        pddl_atomic_function_skeleton(Function,Type,FAxiom,CAxiom).
pddl_atomic_function_skeleton_plus([Function|Functions],[Type|Types],
                                   [FAxiom|FAxioms],[CAxiom|CAxioms],
                                   Type) -->
        pddl_atomic_function_skeleton(Function,Type,FAxiom,CAxiom), ws,
        pddl_atomic_function_skeleton_plus(Functions,Types,FAxioms,
                                           CAxioms,Type).

pddl_atomic_function_skeleton(Function,Type,FAxiom,CAxiom) -->
        "(", ws,
        pddl_function_symbol(Symbol), ws,
        pddl_typed_list_variable(Types,Variables,PVariables,VarTypes),
        ws,
        {Function = func(Symbol,Types,Variables),
         Head =.. [Symbol|PVariables],
         FAxiom = fun_fluent(Head,Type,VarTypes),
         CAxiom = cwa(Head=_)},
        ")".

pddl_function_symbol(F) -->
        pddl_name_atom(F,'').

% Constraints %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

pddl_constraints([]) -->
        {requires(constraints)},
        "(", ws, ":constraints", ws, !,
        pddl_con_gd, ws, ")", !,
        {announce_suc("constraints")}.

pddl_con_gd -->
        "(", ws, "and", wp, pddl_con_gd_star, ws, ")".
pddl_con_gd -->
        "(", ws, "forall", ws, "(",
        pddl_typed_list_variable(_,_,_,_), ws,
        ")", ws, pddl_con_gd, ws, ")".
pddl_con_gd -->
        "(", ws, "at end", wp,
        pddl_gd(_,_,_,_,_,_), ws, ")".
pddl_con_gd -->
        "(", ws, "always", wp,
        pddl_gd(_,_,_,_,_,_), ws, ")".
pddl_con_gd -->
        "(", ws, "sometime", wp,
        pddl_gd(_,_,_,_,_,_), ws, ")".
pddl_con_gd -->
        "(", ws, "within", wp,
        pddl_number(_), wp,
        pddl_gd(_,_,_,_,_,_), ws, ")".
pddl_con_gd -->
        "(", ws, "at-most-once", wp,
        pddl_gd(_,_,_,_,_,_), ws, ")".
pddl_con_gd -->
        "(", ws, "sometime-after", wp,
        pddl_gd(_,_,_,_,_,_), wp,
        pddl_gd(_,_,_,_,_,_), ws, ")".
pddl_con_gd -->
        "(", ws, "sometime-before", wp,
        pddl_gd(_,_,_,_,_,_), wp,
        pddl_gd(_,_,_,_,_,_), ws, ")".
pddl_con_gd -->
        "(", ws, "always-within", wp,
        pddl_number(_), wp,
        pddl_gd(_,_,_,_,_,_), wp,
        pddl_gd(_,_,_,_,_,_), ws, ")".
pddl_con_gd -->
        "(", ws, "hold-during", wp,
        pddl_number(_), wp,
        pddl_number(_), wp,
        pddl_gd(_,_,_,_,_,_), ws, ")".
pddl_con_gd -->
        "(", ws, "hold-after", wp,
        pddl_number(_), wp,
        pddl_gd(_,_,_,_,_,_), ws, ")".

pddl_number(N) -->
        pddl_integer(C),
        {number_codes(N,C)}.
pddl_number(F) -->
        pddl_float(C),
        {number_codes(F,C)}.

pddl_integer(C) -->
        digit_plus(C).
pddl_float(C) -->
        digit_plus(C1), ".", digit_plus(C2),
        {append(C1,[46|C2],C)}.

digit_plus([C]) -->
        digit(C).
digit_plus([C|Cs]) -->
        digit(C),
        digit_plus(Cs).

pddl_con_gd_star --> [].
pddl_con_gd_star -->
        pddl_con_gd, ws,
        pddl_con_gd_star.

% Structures (Actions) %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

pddl_structure_def_star(_,[]) --> [].
pddl_structure_def_star(D,Axioms) -->
        pddl_structure_def(D,Axioms1), ws,
        pddl_structure_def_star(D,Axioms2),
        {append(Axioms1,Axioms2,Axioms)}.

pddl_structure_def(D,Axioms) -->
        pddl_action_def(D,Axioms).
pddl_structure_def(D,Axioms) -->
        pddl_durative_action_def(D,Axioms).
pddl_structure_def(D,Axioms) -->
        pddl_derived_def(D,Axioms).

pddl_action_def(D,Axioms) -->
        "(", ws, ":action", wp, !,
        pddl_action_symbol(Symbol), wp,
        ":parameters", ws, "(", ws,
        pddl_typed_list_variable(Variables,Types,PVariables,VarTypes),
        ws, ")", ws,
        {check_types(D,Types)}, !,
        {announce_fin(Symbol,"parameters")},
        pddl_action_def_body(D,Symbol,Variables,Types,PVariables,
                             VarTypes,Precond,EffAxioms), ws, ")", !,
        {ActionTerm =.. [Symbol | PVariables],
         Axioms = [(poss(ActionTerm,VarTypes,Precond))|
                   EffAxioms]},
        {announce_fin(Symbol,"body")},
        {announce_suc("action")}.

pddl_action_symbol(Symbol) -->
        pddl_name_atom(Symbol,'').

pddl_action_def_body(D,Symbol,Variables,Types,PVariables,VarTypes,
                     Precond,EffAxioms) -->
        ([], {Precond=true};
         ":precondition", !, wp,
         pddl_emptyOr(pddl_pre_gd(D,Variables,Types,PVariables,
                                  VarTypes,Precond),
                      Precond,true)),
        {announce_fin(Symbol,"preconditions")},	ws,
	([], {EffAxioms=[]};
         ":effect", !, wp,
         {ActionTerm =.. [Symbol|PVariables]},
         pddl_emptyOr(pddl_effect(D,ActionTerm,Variables,Types,
                                  PVariables,VarTypes,EffAxioms),
                      EffAxioms,[])).

pddl_emptyOr(_,Y,Z) -->
        "(", ws, ")", !, {Y=Z}.
pddl_emptyOr(X,_,_) --> X.

pddl_pre_gd_star(_,_,_,_,_,[]) --> [].
pddl_pre_gd_star(D,V,T,PV,VT,[G|GL]) -->
        pddl_pre_gd(D,V,T,PV,VT,G), ws,
        pddl_pre_gd_star(D,V,T,PV,VT,GL).

pddl_pre_gd(D,V,T,PV,VT,G) -->
        pddl_pref_gd(D,V,T,PV,VT,G).
pddl_pre_gd(D,V,T,PV,VT,G) -->
        "(", ws, "and", wp,
        pddl_pre_gd_star(D,V,T,PV,VT,GL), ws, ")",
        {conjoin(GL,G)}.
pddl_pre_gd(D,V,T,PV,VT,all_t(VT1,G)) -->
        {requires(universal-preconditions)},
        "(", ws, "forall", ws,
        "(", ws, pddl_typed_list_variable(V1,T1,PV1,VT1), ws, ")", wp,
        {check_types(D,T1)},
        {append(V,V1,V2), append(T,T1,T2),
         append(PV,PV1,PV2), append(VT,VT1,VT2)},
        pddl_pre_gd(D,V2,T2,PV2,VT2,G), ws, ")".

pddl_pref_gd(_,_,_,_,_,_) -->
        {requires(preferences)},
        "(", ws, ":preference", wp,
        ([]; pddl_pref_name(_), wp),
        pddl_gd(_,_,_,_,_,_), ws, ")".
pddl_pref_gd(D,V,T,PV,VT,G) -->
        pddl_gd(D,V,T,PV,VT,G).

pddl_pref_name(Name) -->
        pddl_name_atom(Name,'').

pddl_gd(D,V,T,PV,VT,G) -->
        pddl_atomic_formula_term(V,T,PV,VT,G),
        {check_atom(D,V,T,PV,G)}.
pddl_gd(D,V,T,PV,VT,G) -->
        {requires(negative-preconditions)},
        pddl_literal_term(V,T,PV,VT,G),
        {check_lit(D,V,T,PV,G)}.
pddl_gd(D,V,T,PV,VT,G) -->
        "(", ws, "and", ws,
        pddl_gd_star(D,V,T,PV,VT,GL), ws, ")",
        {conjoin(GL,G)}.
pddl_gd(D,V,T,PV,VT,G) -->
        {requires(disjunctive-preconditions)},
        "(", ws, "or", ws,
        pddl_gd_star(D,V,T,PV,VT,GL), ws, ")",
        {disjoin(GL,G)}.
pddl_gd(D,V,T,PV,VT,-G) -->
        {requires(disjunctive-preconditions)},
        "(", ws, "not", ws,
        pddl_gd(D,V,T,PV,VT,G), ws, ")".
pddl_gd(D,V,T,PV,VT,G1=>G2) -->
        {requires(disjunctive-preconditions)},
        "(", ws, "imply", ws,
        pddl_gd(D,V,T,PV,VT,G1), ws,
        pddl_gd(D,V,T,PV,VT,G2), ws, ")".
pddl_gd(D,V,T,PV,VT,some_t(VT1,G)) -->
        {requires(existential-preconditions)},
        "(", ws, "exists", ws,
        "(", ws, pddl_typed_list_variable(V1,T1,PV1,VT1), ws, ")", ws,
        {append(V,V1,V2), append(T,T1,T2),
         append(PV,PV1,PV2), append(VT,VT1,VT2)},
        pddl_gd(D,V2,T2,PV2,VT2,G), ws, ")".
pddl_gd(D,V,T,PV,VT,all_t(VT1,G)) -->
        {requires(universal-preconditions)},
        "(", ws, "forall", ws,
        "(", ws, pddl_typed_list_variable(V1,T1,PV1,VT1), ws,")", ws,
        {append(V,V1,V2), append(T,T1,T2),
         append(PV,PV1,PV2), append(VT,VT1,VT2)},
        pddl_gd(D,V2,T2,PV2,VT2,G), ws, ")".
pddl_gd(D,V,T,PV,VT,Comp) -->
        {requires(numeric-fluents)},
        pddl_f_comp(D,V,T,PV,VT,Comp).

pddl_gd_star(_,_,_,_,_,[]) --> [].
pddl_gd_star(D,V,T,PV,VT,[G|GL]) -->
        pddl_gd(D,V,T,PV,VT,G), ws,
        pddl_gd_star(D,V,T,PV,VT,GL).

pddl_f_comp(D,V,T,PV,VT,Comp) -->
        "(", ws, pddl_binary_comp(Op), ws,
        pddl_f_exp(D,V,T,PV,VT,Exp1), wp,
        pddl_f_exp(D,V,T,PV,VT,Exp2), ws, ")",
        {Comp =.. [Op,Exp1,Exp2]}.

pddl_literal_term(V,T,PV,VT,G) -->
        pddl_atomic_formula_term(V,T,PV,VT,G).
pddl_literal_term(V,T,PV,VT,-G) -->
        "(", ws, "not", ws,
        pddl_atomic_formula_term(V,T,PV,VT,G), ws, ")".

pddl_atomic_formula_term(V,T,PV,VT,G) -->
        "(", ws, pddl_predicate(Name), wp,
        pddl_term_star(V,T,PV,VT,Terms), ws, ")",
        {G=..[Name|Terms]}.

pddl_atomic_formula_term(V,T,PV,VT,(T1 = T2)) -->
        {requires(equality)},
        "(", ws, "=", wp,
        pddl_term(V,T,PV,VT,T1), wp,
        pddl_term(V,T,PV,VT,T2), ws, ")".

pddl_term_star(_,_,_,_,[]) --> [].
pddl_term_star(V,T,PV,VT,[Term]) -->
        pddl_term(V,T,PV,VT,Term).
pddl_term_star(V,T,PV,VT,[Term|Terms]) -->
        pddl_term(V,T,PV,VT,Term), wp,
        pddl_term_star(V,T,PV,VT,Terms).

pddl_term(_,_,_,_,Constant) -->
        pddl_name_atom(Constant,'#').
pddl_term(V,_,PV,_,PVariable) -->
        pddl_variable(Variable,_,PVariable,_,_),
        {nth0(Idx,V,Variable),
         nth0(Idx,PV,PVariable)}.
pddl_term(V,T,PV,VT,FTerm) -->
        {requires(object-fluents)},
        pddl_function_term(V,T,PV,VT,FTerm).

pddl_function_term(V,T,PV,VT,FTerm) -->
        {requires(object-fluents)},
        "(", ws,
        pddl_function_symbol(Symbol), wp,
        pddl_term_star(V,T,PV,VT,Terms), ws, ")",
        {FTerm =.. [Symbol|Terms]}.

pddl_f_exp(_,_,_,_,_,N) -->
        {requires(numeric-fluents)},
        pddl_number(N).
pddl_f_exp(D,V,T,PV,VT,Exp) -->
        {requires(numeric-fluents)},
        "(", ws, pddl_binary_op(Op), ws,
        pddl_f_exp(D,V,T,PV,VT,Exp1), wp,
        pddl_f_exp(D,V,T,PV,VT,Exp2), ws, ")",
        {Exp =.. [Op,Exp1,Exp2]}.
pddl_f_exp(D,V,T,PV,VT,Exp) -->
        {requires(numeric-fluents)},
        "(", ws, pddl_multi_op(Op), ws,
        pddl_f_exp(D,V,T,PV,VT,Exp1), wp,
        pddl_f_exp_plus(D,V,T,PV,VT,Exps2), ws, ")",
        {apply_multi_op(Op,[Exp1|Exps2],Exp)}.
pddl_f_exp(D,V,T,PV,VT,Exp) -->
        {requires(numeric-fluents)},
        "(", ws, "-", ws,
        pddl_f_exp(D,V,T,PV,VT,Exp1), ws, ")",
        {Exp =.. ['-',Exp1]}.
pddl_f_exp(D,V,T,PV,VT,Head) -->
        {requires(numeric-fluents)},
        pddl_f_head(V,T,PV,VT,Head),
        {check_fhead(D,V,T,PV,Head)}.

pddl_f_exp_plus(D,V,T,PV,VT,Exp) -->
        pddl_f_exp(D,V,T,PV,VT,Exp).
pddl_f_exp_plus(D,V,T,PV,VT,[Exp|Exps]) -->
        pddl_f_exp(D,V,T,PV,VT,Exp), wp,
        pddl_f_exp_plus(D,V,T,PV,VT,Exps).

pddl_f_head(V,T,PV,VT,Head) -->
        "(", ws, pddl_function_symbol(F), wp, % <<< whitespace
        pddl_term_star(V,T,PV,VT,Terms), ws, ")",
        {Head =.. [F|Terms]}.
pddl_f_head(_,_,_,_,Head) -->
        "(", ws, pddl_function_symbol(F), ws, % <<< no whitespace
        ")",
        {Head = F}.
pddl_f_head(_,_,_,_,Head) -->
        pddl_function_symbol(Head).

pddl_binary_op(X) --> pddl_multi_op(X).
pddl_binary_op('-') --> "-".
pddl_binary_op('/') --> "/".

pddl_multi_op('*') --> "*".
pddl_multi_op('+') --> "+".

pddl_binary_comp('>') --> ">".
pddl_binary_comp('=') --> "=".
pddl_binary_comp('<') --> "<".
pddl_binary_comp('>=') --> ">=".
pddl_binary_comp('<=') --> "<=".

pddl_effect(D,AT,V,T,PV,VT,Axioms) -->
        "(", ws, "and", ws,
        pddl_c_effect_star(D,AT,V,T,PV,VT,Axioms), ws, ")".
pddl_effect(D,AT,V,T,PV,VT,Axioms) -->
        pddl_c_effect(D,AT,V,T,PV,VT,Axioms).

pddl_c_effect(D,AT,V,T,PV,VT,Axioms) -->
        {requires(conditional-effects)},
        "(", ws, "forall", ws,
        "(", ws, pddl_typed_list_variable(V1,T1,PV1,VT1), ws, ")", ws,
        {check_types(D,T1)},
        {append(V,V1,V2), append(T,T1,T2),
         append(PV,PV1,PV2), append(VT,VT1,VT2)},
        pddl_effect(D,AT,V2,T2,PV2,VT2,Axioms), ws, ")".
pddl_c_effect(D,AT,V,T,PV,VT,Axioms) -->
        {requires(conditional-effects)},
        "(", ws, "when", ws,
        pddl_gd(D,V,T,PV,VT,G), ws,
        pddl_cond_effect(D,AT,V,T,PV,VT,G,Axioms), ws, ")".
pddl_c_effect(D,AT,V,T,PV,VT,[Axiom]) -->
        pddl_p_effect(D,AT,V,T,PV,VT,true,Axiom).

pddl_c_effect_star(_,_,_,_,_,_,[]) --> [].
pddl_c_effect_star(D,AT,V,T,PV,VT,Axioms) -->
        pddl_c_effect(D,AT,V,T,PV,VT,Axioms1), ws,
        pddl_c_effect_star(D,AT,V,T,PV,VT,Axioms2),
        {append(Axioms1,Axioms2,Axioms)}.

pddl_p_effect(D,AT,V,T,PV,VT,Cond,(causes_false(AT,E,Cond))) -->
        "(", ws, "not", ws,
        pddl_atomic_formula_term(V,T,PV,VT,E), ws, ")",
        {check_atom(D,V,T,PV,E)}.
pddl_p_effect(D,AT,V,T,PV,VT,Cond,(causes_true(AT,E,Cond))) -->
        pddl_atomic_formula_term(V,T,PV,VT,E),
        {check_atom(D,V,T,PV,E)}.
pddl_p_effect(D,AT,V,T,PV,VT,Cond,(causes(AT,Head,Y,Cond2))) -->
        {requires(numeric-fluents)},
        "(", ws, pddl_assign_op(Head,Exp,Ass), wp,
        pddl_f_head(V,T,PV,VT,Head), wp,
        pddl_f_exp(D,V,T,PV,VT,Exp), ws, ")",
        {check_fhead(D,V,T,PV,Head)},
        {simplify((Y=Ass)*Cond,Cond2)}.
pddl_p_effect(D,AT,V,T,PV,VT,Cond,(causes(AT,F,Y,Cond2))) -->
        {requires(object-fluents)},
        "(", ws, "assign", wp,
        pddl_function_term(V,T,PV,VT,F), wp,
        pddl_term(V,T,PV,VT,Val), ws, ")",
        {check_function(D,V,T,F,PV,Type)},
        {check_term(D,V,T,PV,Val,Type)},
        {simplify((Y=Val)*Cond,Cond2)}.
pddl_p_effect(D,AT,V,T,PV,VT,Cond,(causes(AT,F,Y,Cond2))) -->
        {requires(object-fluents)},
        "(", ws, "assign", wp,
        pddl_function_term(V,T,PV,VT,F), wp,
        "undefined", ws, ")",
        {check_function(D,V,T,PV,F,_)},
        {simplify((Y=undefined)*Cond,Cond2)}.
pddl_p_effect_star(_,_,_,_,_,_,_,[]) --> [].
pddl_p_effect_star(D,AT,V,T,PV,VT,Cond,[Axiom|Axioms]) -->
        pddl_p_effect(D,AT,V,T,PV,VT,Cond,Axiom), ws,
        pddl_p_effect_star(D,AT,V,T,PV,VT,Cond,Axioms).

pddl_cond_effect(D,AT,V,T,PV,VT,Cond,Axioms) -->
        "(", ws, "and", ws,
        pddl_p_effect_star(D,AT,V,T,PV,VT,Cond,Axioms), ws, ")".
pddl_cond_effect(D,AT,V,T,PV,VT,Cond,[Axiom]) -->
        pddl_p_effect(D,AT,V,T,PV,VT,Cond,Axiom).

pddl_assign_op(_F,Val,Val) --> "assign".
pddl_assign_op(F,Val,(F*Val)) --> "scale-up".
pddl_assign_op(F,Val,(F/Val)) --> "scale-down".
pddl_assign_op(F,Val,(F+Val)) --> "increase".
pddl_assign_op(F,Val,(F-Val)) --> "decrease".

% Durative Actions %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

pddl_durative_action_def(D,Axioms) -->
        {requires(durative-actions)},
        "(", ws, ":durative-action", wp, !,
        pddl_da_symbol(Symbol), wp,
        ":parameters", ws,
        "(", ws, pddl_typed_list_variable(Variables,Types,PVariables,
                                          VarTypes), ws, ")", ws,
        {check_types(D,Types)},
        pddl_da_def_body(D,ActS,ActE,Variables,Types,PVariables,
                         VarTypes,StartCond,EndCond,EffAxiomsS,
                         EffAxiomsE), ws, ")", !,
        {Act = [Symbol | PVariables],
         ActS =.. [start|Act],
         ActE =.. [end|Act],
         AxiomsS = [(poss(ActS,VarTypes,StartCond))|EffAxiomsS],
         AxiomsE = [(poss(ActE,VarTypes,EndCond))|EffAxiomsE],
         append(AxiomsS,AxiomsE,Axioms)},
        {announce_fin(Symbol,"body")},
        {announce_suc("durative action")}.

pddl_da_symbol(Name) -->
        pddl_name_atom(Name,'').

pddl_da_def_body(D,ActS,ActE,Variables,Types,PVariables,VarTypes,
                 StartCond,EndCond,EffAxiomsS,EffAxiomsE) -->
        ":duration", !, ws, % todo: duration constraints
        pddl_duration_constraint(D,Variables,Types,PVariables,VarTypes,
                                 DurVar,_DurStartCon,_DurEndCond), ws,
        ":condition", !, ws,
        pddl_emptyOr(pddl_da_gd(D,Variables,Types,PVariables,VarTypes,
                                StartCond,EndCond),
                     (StartCond,EndCond),(true,true)), ws,
        ":effect", !, ws,
        pddl_emptyOr(pddl_da_effect(D,ActS,ActE,Variables,Types,
                                    PVariables,VarTypes,DurVar,
                                    EffAxiomsS,EffAxiomsE),
                     (EffAxiomsS,EffAxiomsE),([],[])).

pddl_da_gd(D,Variables,Types,PVariables,VarTypes,StartCond,EndCond) -->
        pddl_pref_timed_gd(D,Variables,Types,PVariables,VarTypes,
                           StartCond,EndCond).
pddl_da_gd(D,Variables,Types,PVariables,VarTypes,StartCond,EndCond) -->
        "(", ws, "and", ws,
        pddl_da_gd_star(D,Variables,Types,PVariables,VarTypes,
                        StartCondL,EndCondL), ws, ")",
        {conjoin(StartCondL,StartCond), conjoin(EndCondL,EndCond)}.
pddl_da_gd(D,Variables,Types,PVariables,VarTypes,StartCond,EndCond) -->
        {requires(universal-preconditions)},
        "(", ws, "forall", ws,
        "(", ws, pddl_typed_list_variable(V1,T1,PV1,VT1), ws,
        ")", ws,
        {check_types(D,T1)},
        {append(Variables,V1,V),
         append(Types,T1,T),
         append(PVariables,PV1,PV),
         append(VarTypes,VT1,VT)},
        pddl_da_gd(D,V,T,PV,VT,SC,EC), ws, ")",
        {(SC = true -> StartCond = true; StartCond = all_t(VT1,SC)),
         (EC = true -> EndCond = true; EndCond = all_t(VT1,EC))}.

pddl_da_gd_star(_D,_Variables,_PVariables,_Types,_VarTypes,[],[]) -->
        [].
pddl_da_gd_star(D,Variables,Types,PVariables,VarTypes,
                [StartCond|StartCondL],[EndCond|EndCondL]) -->
        pddl_da_gd(D,Variables,Types,PVariables,VarTypes,StartCond,
                   EndCond), ws,
        pddl_da_gd_star(D,Variables,Types,PVariables,VarTypes,
                        StartCondL,EndCondL).

pddl_pref_timed_gd(D,Variables,Types,PVariables,VarTypes,EndCond,
                   StartCond) -->
        pddl_timed_gd(D,Variables,Types,PVariables,VarTypes,EndCond,
                      StartCond).
pddl_pref_timed_gd(D,Variables,Types,PVariables,VarTypes,EndCond,
                   StartCond) -->
        {requires(preferences)},
        "(", ws, "preference", ws,
        pddl_timed_gd(D,Variables,Types,PVariables,VarTypes,
                      _StartCond1,_EndCond1), ws, ")",
        {fixme('preferences'),
         StartCond = true, EndCond = true}.
pddl_pref_timed_gd(D,Variables,Types,PVariables,VarTypes,StartCond,
                   EndCond) -->
        {requires(preferences)},
        "(", ws, "preference", wp,
        pddl_pref_name(_Name), ws,
        pddl_timed_gd(D,Variables,Types,PVariables,VarTypes,
                      _StartCond1,_EndCond1), ws, ")",
        {fixme('preferences'),
         StartCond = true, EndCond = true}.

pddl_timed_gd(D,Variables,Types,PVariables,VarTypes,StartCond,EndCond)
        -->
        "(", ws, "at", wp,
        pddl_time_specifier(TimeSpecifier), ws,
        pddl_gd(D,Variables,Types,PVariables,VarTypes,Goal),
        ws, ")",
        {TimeSpecifier = start -> (StartCond = Goal, EndCond = true);
                                  (StartCond = true, EndCond = Goal)}.
pddl_timed_gd(D,Variables,Types,PVariables,VarTypes,StartCond,EndCond)
        -->
        "(", ws, "over", wp,
        pddl_interval(_Interval), ws,
        pddl_gd(D,Variables,Types,PVariables,VarTypes,_Goal),
        ws, ")",
        {fixme('interval constraints'),
         StartCond = true, EndCond = true}.

pddl_time_specifier(start) --> "start".
pddl_time_specifier(end) --> "end".

pddl_interval(all) --> "all".

pddl_duration_constraint(D,V,T,PV,VT,DurVar,SDurCon,EDurCon) -->
        {requires(duration-inequalities)},
        "(", ws, "and",
        pddl_simple_duration_constraint_plus(D,V,T,PV,VT,DurVar,
                                             SDurCons,EDurCons), ws,
        ")",
        {conjoin(SDurCons,SDurCon), conjoin(EDurCons,EDurCon)}.
pddl_duration_constraint(_,_,_,_,_,_,true,true) -->
        "(", ws, ")".
pddl_duration_constraint(D,V,T,PV,VT,DurVar,SDurCon,EDurCon) -->
        pddl_simple_duration_constraint(D,V,T,PV,VT,
                                        DurVar,SDurCon,EDurCon).

% Possible bug in PDDL 3.1 grammar: the following rules allow nesting
% of (at start ...) and (at end ...) conditions. Here we assume this
% doesn't happen, and that no time specifier defaults to "at start".

pddl_simple_duration_constraint(D,V,T,PV,VT,DV,SCon,ECon) -->
        "(", ws, pddl_d_op(Op), ws,
        "?duration", wp,
        pddl_d_value(D,V,T,PV,VT,Value), ws, ")",
        {SCon =.. [Op,DV,Value], ECon = true}.
pddl_simple_duration_constraint(D,V,T,PV,VT,DV,SCon,ECon) -->
        "(", ws, "at", wp,
        pddl_time_specifier(TimeSpecifier), ws,
        pddl_simple_duration_constraint(D,V,T,PV,VT,DV,SCon1,_ECon1), ws, ")",
        {TimeSpecifier = start ->
            (SCon = SCon1, ECon = true);
            (SCon = true,  ECon = SCon1)}.

pddl_simple_duration_constraint_plus(D,V,T,PV,VT,DV,[SCon],[ECon]) -->
	pddl_simple_duration_constraint(D,V,T,PV,VT,DV,SCon,ECon).
pddl_simple_duration_constraint_plus(D,V,T,PV,VT,DV,
                                     [SCon|SCons],[ECon|ECons]) -->
	pddl_simple_duration_constraint(D,V,T,PV,VT,DV,SCon,ECon), ws,
	pddl_simple_duration_constraint_plus(D,V,T,PV,VT,DV,SCons,ECons).

pddl_d_op('<=') -->
        {requires(duration-inequalities)},
        "<=".
pddl_d_op('>=') -->
        {requires(duration-inequalities)},
        ">=".
pddl_d_op('=') -->
        "=".

pddl_d_value(_,_,_,_,_,Number) -->
        pddl_number(Number).
pddl_d_value(D,V,T,PV,VT,Exp) -->
        {requires(numeric-fluents)},
        pddl_f_exp(D,V,T,PV,VT,Exp).

pddl_da_effect(D,ATS,ATE,Variables,Types,PVariables,VarTypes,DV,
               EffAxiomsS,EffAxiomsE) -->
        "(", ws, "and", ws,
        pddl_da_effect_star(D,ATS,ATE,Variables,Types,PVariables,DV,
                            VarTypes,EffAxiomsS,EffAxiomsE), ws, ")".
pddl_da_effect(D,ATS,ATE,Variables,Types,PVariables,VarTypes,DV,
               EffAxiomsS,EffAxiomsE) -->
        pddl_timed_effect(D,ATS,ATE,Variables,Types,PVariables,
                          VarTypes,DV,true,true,EffAxiomsS,
                          EffAxiomsE).
pddl_da_effect(D,ATS,ATE,Variables,Types,PVariables,VarTypes,DV,
               EffAxiomsS,EffAxiomsE) -->
        {requires(conditional-effects)},
        "(", ws, "forall", ws,
        "(", ws, pddl_typed_list_variable(V1,T1,PV1,VT1), ws,
        ")", ws,
        {check_types(D,T1)},
        {append(Variables,V1,V),
         append(Types,T1,T),
         append(PVariables,PV1,PV),
         append(VarTypes,VT1,VT)},
        pddl_da_effect(D,ATS,ATE,V,T,PV,VT,DV,EffAxiomsS,EffAxiomsE),
        ws, ")".
pddl_da_effect(D,ATS,ATE,Variables,Types,PVariables,VarTypes,DV,
               EffAxiomsS,EffAxiomsE) -->
        {requires(conditional-effects)},
        "(", ws, "when", ws,
        pddl_da_gd(D,Variables,Types,PVariables,VarTypes,SCond,ECond),
        ws,
        pddl_timed_effect(D,ATS,ATE,Variables,Types,PVariables,
                          VarTypes,DV,SCond,ECond,EffAxiomsS,
                          EffAxiomsE),
        ws, ")".

pddl_da_effect_star(_D,_ATS,_ATE,_Variables,_Types,_PVariables,
                    _VarTypes,_DV,[],[]) --> [].
pddl_da_effect_star(D,ATS,ATE,Variables,Types,PVariables,VarTypes,DV,
                    EffAxiomsS,EffAxiomsE) -->
        pddl_da_effect(D,ATS,ATE,Variables,Types,PVariables,VarTypes,
                       DV,EffAxiomsS1,EffAxiomsE1), ws,
        pddl_da_effect_star(D,ATS,ATE,Variables,Types,PVariables,DV,
                            VarTypes,EffAxiomsS2,EffAxiomsE2),
        {append(EffAxiomsS1,EffAxiomsS2,EffAxiomsS),
         append(EffAxiomsE1,EffAxiomsE2,EffAxiomsE)}.

pddl_timed_effect(D,ATS,ATE,Variables,Types,PVariables,VarTypes,_DV,
                  SCond,ECond,EffAxiomsS,EffAxiomsE) -->
        "(", ws, "at", wp,
        pddl_time_specifier(TimeSpecifier), ws,
        {TimeSpecifier = start ->
            (AT = ATS,
             SCond = Cond,
             ECond = true, % start effect = only depends on start
             EffAxiomsS = Axioms,
             EffAxiomsE = []);
            (AT = ATE,
             SCond = true, % todo: inter-temporal-effects
             ECond = Cond,
             EffAxiomsS = [],
             EffAxiomsE = Axioms)},
        pddl_cond_effect(D,AT,Variables,Types,PVariables,VarTypes,
                         Cond,Axioms), ws, ")".
pddl_timed_effect(D,ATS,ATE,Variables,Types,PVariables,VarTypes,DV,
                  SCond,ECond,EffAxiomsS,EffAxiomsE) -->
        {requires(numeric-fluents)},
        "(", ws, "at", wp,
        pddl_time_specifier(TimeSpecifier), ws,
        {TimeSpecifier = start ->
            (SCond = Cond2,
             ECond = true,  % start effect = only depends on start
             EffAxiomsS = [causes(ATS,Head,Y,Cond)],
             EffAxiomsE = []);
            (SCond = true,  % todo: inter-temporal-effects
             ECond = Cond2,
             EffAxiomsS = [],
             EffAxiomsE = [causes(ATE,Head,Y,Cond)])},
        pddl_f_assign_da(D,Variables,Types,PVariables,VarTypes,DV,Head,
                         Ass), ws, ")",
        {simplify((Y=Ass)*Cond2,Cond)}.
pddl_timed_effect(D,_ATS,_ATE,Variables,Types,PVariables,VarTypes,_DV,
                  [],[]) -->
        {requires(continuous-effects)},
        {requires(numeric-fluents)},
        {fixme('continuous effects')},
        "(", ws, pddl_assign_op_t(Head,Exp,_Ass), wp,
        pddl_f_head(Variables,Types,PVariables,VarTypes,Head), wp,
        {check_fhead(D,Variables,Types,PVariables,Head)},
        pddl_f_exp_t(D,Variables,Types,PVariables,VarTypes,Exp), ws,
        ")".

pddl_assign_op_t(F,Val,(F+Val)) --> "increase".
pddl_assign_op_t(F,Val,(F-Val)) --> "decrease".

pddl_f_exp_t(D,V,T,PV,VT,Exp * 'pddl_#t') -->
        "(", ws, "*", wp,
        pddl_f_exp(D,V,T,PV,VT,Exp), wp,
        "#t", ws, ")".
pddl_f_exp_t(D,V,T,PV,VT,'pddl_#t' * Exp) -->
        "(", ws, "*", wp,
        "#t", wp,
        pddl_f_exp(D,V,T,PV,VT,Exp), ws, ")".
pddl_f_exp_t(_,_,_,_,_,'pddl_#t') -->
        "#t".

pddl_f_assign_da(D,V,T,PV,VT,DV,Head,Ass) -->
        "(", ws, pddl_assign_op(Head,Exp,Ass), wp,
        pddl_f_head(V,T,PV,VT,Head), wp,
        {check_fhead(D,V,T,PV,Head)},
        pddl_f_exp_da(D,V,T,PV,VT,DV,Exp), ws, ")".

pddl_f_exp_da(D,V,T,PV,VT,DV,Exp) -->
        "(", pddl_binary_op(Op), ws,
        pddl_f_exp_da(D,V,T,PV,VT,DV,Exp1), wp,
        pddl_f_exp_da(D,V,T,PV,VT,DV,Exp2), ws, ")",
        {Exp =.. [Op,Exp1,Exp2]}.
pddl_f_exp_da(D,V,T,PV,VT,DV,Exp) -->
        "(", pddl_multi_op(Op), ws,
        pddl_f_exp_da(D,V,T,PV,VT,DV,Exp1), wp,
        pddl_f_exp_da_plus(D,V,T,PV,VT,DV,Exps2), ws, ")",
        {apply_multi_op(Op,[Exp1|Exps2],Exp)}.
pddl_f_exp_da(D,V,T,PV,VT,DV,Exp) -->
        "(", ws, "-", ws, pddl_f_exp_da(D,V,T,PV,VT,DV,Exp1), ws, ")",
        {Exp =.. ['-',Exp1]}.
pddl_f_exp_da(_,_,_,_,_,DurationVar,DurationVar) -->
        {requires(duration-inequalities)},
        "?duration".
pddl_f_exp_da(D,V,T,PV,VT,_DV,Exp) -->
        pddl_f_exp(D,V,T,PV,VT,Exp).

% Derived Predicates%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

pddl_derived_def(D,[]) -->
        {requires(derived-predicates)},
        "(", ws, ":derived", wp, !,
        pddl_atomic_formula_skeleton(_,_), wp,
        % TODO: check types of skeleton
        pddl_gd(D,_,_,_,_,_), ws, ")".

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% PDDL Problems
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

pddl_problem(D,proax(Problem,Domain,ObjectAxioms,
                     InitAxioms,GoalAxioms,MetricAxioms)) -->
        ws,
        "(", ws, "define", ws,
        "(", ws, "problem", ws,
        pddl_problem_name(Problem), ws, ")", ws,
        "(", ws, ":domain", ws,
        pddl_problem_domain(Domain), ws, ")", ws, !,
        ([]; pddl_problem_requirements, ws),
        ([],{O=[], ObjectAxioms=[]};
         pddl_object_declarations(O,ObjectAxioms), ws),
        {D = dom(Domain,T,C,P,F,FT),
         append(C,O,CO),
         DP = dom((Domain,Problem),T,CO,P,F,FT)},
        pddl_init(DP,InitAxioms), ws,
        pddl_goal(DP,GoalAxioms), ws,
        ([]; pddl_problem_constraints, ws),
        ([],{MetricAxioms=[]};
         pddl_metric_spec(DP,MetricAxioms), ws),
        ([]; pddl_length_spec, ws), ")", !, ws.

pddl_problem_name(Name) -->
        pddl_name_atom(Name,'').

pddl_problem_domain(Name) -->
        pddl_name_atom(Name,''). % maybe put a test here?

pddl_problem_requirements -->
        pddl_requirements.

pddl_object_declarations(ObjectsDefs,Axioms) -->
        "(", ws, ":objects", wp, !,
        pddl_typed_list_name(ObjectsDefs,Axioms,domain,'#'), ws,
        ")", !,
        {announce_suc("objects")}.

pddl_init(D,Axioms) -->
        "(", ws, ":init", wp, !,
        pddl_init_el_star(D,Axioms), ws, ")",
        {announce_suc("init")}.

pddl_init_el_star(D,[Axiom|Axioms]) -->
        pddl_init_el(D,Axiom), ws,
        pddl_init_el_star(D,Axioms).
pddl_init_el_star(_,[]) --> [].

pddl_init_el(D,initially(Atom)) -->
        pddl_literal_name(Atom),
        {check_atom(D,[],[],[],Atom)}.
pddl_init_el(_D,initially(true)) --> % TODO
        {requires(timed-initial-literals)},
        "(", ws, "at", wp,
        pddl_number(_), ws,
        pddl_literal_name(_), ws, ")".
        % TODO: check literal
pddl_init_el(D,initially(Function = Number)) -->
        {requires(numeric-fluents)},
        "(", ws, "=", ws,
        pddl_basic_function_term(Function), wp,
        {check_fhead(D,[],[],[],Function)},
        pddl_number(Number), ws, ")".
pddl_init_el(D,initially(Function = Object)) -->
        {requires(object-fluents)},
        "(", ws, "=", ws,
        pddl_basic_function_term(Function), wp,
        {check_function(D,[],[],[],Function)},
        pddl_name_atom(Object,'#'), ws, ")".

pddl_basic_function_term(Symbol) -->
        pddl_function_symbol(Symbol).
pddl_basic_function_term(Term) -->
        "(", ws, pddl_function_symbol(Symbol), ws,
        pddl_name_star(Names,'#'), ws, ")",
        {Term =..[Symbol|Names]}.

pddl_literal_name(Axiom) -->
        pddl_atomic_formula_name(Axiom).
pddl_literal_name(Axiom) -->
        "(", ws, "not", wp, pddl_atomic_formula_name(Axiom), ws, ")".

pddl_atomic_formula_name(Atom) -->
        "(", ws, pddl_predicate(PName), wp,
        pddl_name_star(Names,'#'), ws,")",
        {Atom =.. [PName|Names]}.
pddl_atomic_formula_name((N1 = N2)) -->
        {requires(equality)},
        "(", ws, "=", wp,
        pddl_name_atom(N1,''), wp,
        pddl_name_atom(N2,''), ws, ")".

pddl_goal(D,[goal(P,G)]) -->
        "(", ws, ":goal", wp, !,
        pddl_pre_gd(D,[],[],[],[],G), ws, ")",
        {D = dom((_,P),_,_,_,_,_)}, % goal ID = problem name
        {announce_suc("goal")}.

pddl_problem_constraints -->
        {requires(constraints)},
        "(", ws, ":constraints", wp, !,
        pddl_pref_con_gd, ws, ")".

pddl_pref_con_gd -->
        "(", ws, "and", wp,
        pddl_pref_con_gd_star, ws, ")".
pddl_pref_con_gd -->
        {requires(universal-preconditions)},
        "(", ws, "forall", ws,
        "(", ws, pddl_typed_list_variable(_,_,_,_), ws, ")", ws,
        pddl_con_gd, ws, ")".
pddl_pref_con_gd -->
        {requires(preferences)},
        "(", ws, "preference", wp,
        ([]; pddl_pref_name(_), ws),
        pddl_con_gd, ws, ")".
pddl_pref_con_gd -->
        pddl_con_gd.

pddl_pref_con_gd_star --> [].
pddl_pref_con_gd_star -->
        pddl_pref_con_gd, ws,
        pddl_pref_con_gd_star.

pddl_metric_spec(D,[metric(P,M)]) -->
        {requires(numeric-fluents)},
        "(", ws, ":metric", wp, !,
        {D = dom((_,P),_,_,_,_,_)}, % metric ID = problem name
        pddl_optimization(O), wp,
        pddl_metric_f_exp(D,E), ws, ")",
        {M =.. [O,E]}.

pddl_optimization(minimize) --> "minimize".
pddl_optimization(maximize) --> "maximize".

pddl_metric_f_exp(D,Exp) -->
        "(", ws, pddl_binary_op(Op), wp,
        pddl_metric_f_exp(D,Exp1), wp,
        pddl_metric_f_exp(D,Exp2), ws, ")",
        {Exp =.. [Op,Exp1,Exp2]}.
pddl_metric_f_exp(D,Exp) -->
        "(", ws, pddl_multi_op(Op), wp,
        pddl_metric_f_exp(D,Exp1), wp,
        pddl_metric_f_exp_plus(D,Exps2), ws, ")",
        {apply_multi_op(Op,[Exp1|Exps2],Exp)}.
pddl_metric_f_exp(D,-Exp) -->
        "(", ws, "-", ws,
        pddl_metric_f_exp(D,Exp), ws, ")".
pddl_metric_f_exp(_,Number) -->
        pddl_number(Number).
pddl_metric_f_exp(D,Exp) -->
        "(", ws, pddl_function_symbol(F), ws,
        pddl_name_star(Names,'#'), ws, ")",
        {Exp =.. [F|Names]},
        {check_fhead(D,[],[],[],Exp)}.
pddl_metric_f_exp(D,F) -->
        pddl_function_symbol(F),
        {check_fhead(D,[],[],[],F)}.
pddl_metric_f_exp(_D,'total-time') -->
        "total-time".
pddl_metric_f_exp(_D,'is-violated'(N)) -->
        {requires(preferences)},
        "(", ws, "is-violated", wp, !,
        pddl_pref_name(N), ws, ")".
        % todo: check pref name!

pddl_metric_f_exp_plus(D,[Exp]) -->
        pddl_metric_f_exp(D,Exp).
pddl_metric_f_exp_plus(D,[Exp|Exps]) -->
        pddl_metric_f_exp(D,Exp), wp,
        pddl_metric_f_exp_plus(D,Exps).

pddl_length_spec -->
        "(", ws, ":length", wp, !,
        ([]; "(", ws, ":serial", wp,
             pddl_integer(_), ws, ")", ws),
        ([]; "(", ws, ":parallel", wp,
             pddl_integer(_), ws, ")", ws), ")".
        %deprecated since PDDL 2.1

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Auxiliary stuff
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

pddl_name_atom(Name,Prefix) -->
        pddl_name_atom2(Cs),
        {atom_codes(Name2,Cs),
         downcase_atom(Name2,Name3), % PDDL not case-sensitive!
         atom_concat(Prefix,Name3,Name)}.
pddl_name_atom2([C|Cs]) -->
        pddl_letter(C), % first char must be a letter
        pddl_name_char_list(Cs).

pddl_letter(C) --> [C], {C>=65, C=<90}. % A..Z
pddl_letter(C) --> [C], {C>=97, C=<122}. % a..z

pddl_name_char(C) --> pddl_letter(C).
pddl_name_char(C) --> [C], {C=95; C=45}. % "_" or "-"
pddl_name_char(C) --> digit(C).

pddl_name_char_list([]) --> [].
pddl_name_char_list([C|List]) -->
        pddl_name_char(C),
        pddl_name_char_list(List).

% "white plus"
wp --> pddl_white, !, ws.

% "white star"
ws --> pddl_white, !, ws.
ws --> [].

pddl_white --> ";", !, string_without("\n",_). % skip rest of line
pddl_white --> blank, !.

% debugging outputs
announce_suc(X) :-
        report_message(debug,['Succeeded processing ',X,'.']).
announce_fin(S,X) :-
        report_message(debug,['Finished part <',X,'> ',
                              'of structure <',S,'>.']).

fixme(X) :-
        report_message(warn,['Compilation of ',X,
                             ' not yet implemented.']).

apply_multi_op(_Op,[E],E) :- !.
apply_multi_op(Op,[E|Es],Exp) :- !,
        apply_multi_op(Op,Es,Exp2),
        Exp =.. [Op,E,Exp2].

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Test predicates to check whether all symbols have been declared
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

check_types(D,CTypes) :-
        D = dom(_,Types,_,_,_,_),
        check_types2(CTypes,Types).
check_types2([],_Types) :- !.
check_types2([CT|CTs],Types) :-
        check_type(CT,Types),
        check_types2(CTs,Types).
check_type(object,_Types) :- !.
check_type(number,_Types) :- !.
check_type(CT,Types) :-
        member(CT,Types), !.
check_type(CT,Types) :-
        member(ST,Types),
        ST =.. [_,Names],
        member(CT,Names), !.
check_type(CT,Types) :-
        member(ET,Types),
        ET = either(_ENames,Names),
        member(CT,Names), !.

check_atom(D,V,T,PV,A) :-
        D = dom(_,_,_,Predicates,_,_),
        A =.. [PredSymbol|Args],
        member(pred(PredSymbol,_ArgNames,ArgTypes),Predicates), !,
        check_terms(D,V,T,PV,Args,ArgTypes).
check_atom(D,V,T,PV,A) :-
        A = (Arg1 = Arg2), !,
        check_terms(D,V,T,PV,[Arg1,Arg2],[object,object]).

check_lit(D,V,T,PV,-A) :- !,
        check_atom(D,V,T,PV,A).
check_lit(D,V,T,PV,A) :- !,
        check_atom(D,V,T,PV,A).

check_terms(_,_,_,_,[],[]) :- !.
check_terms(D,V,T,PV,[Term|Terms],[TType|TTypes]) :- !,
        check_term(D,V,T,PV,Term,TType),
        check_terms(D,V,T,PV,Terms,TTypes).
check_term(D,V,T,PV,Term,TType) :-
        check_constant(D,V,T,PV,Term,TType);
        check_variable(D,V,T,PV,Term,TType);
        check_function(D,V,T,PV,Term,TType).

check_constant(D,_,_,_,Constant,Type) :-
        atom(Constant),
        D = dom(_,_,Constants,_,_,_),
        member(ConstantDef,Constants),
        ((ConstantDef =.. [CType,ConstantList],
          member(Constant,ConstantList));
         (ConstantDef = Constant, CType = object)),
        check_subtype(D,CType,Type).
check_variable(D,_V,T,PV,Variable,Type) :-
        nth02(I,PV,Variable), !, % check term equality (Prolog var)
        nth0(I,T,VType),         % unify VType
        check_subtype(D,VType,Type).
check_function(D,V,T,PV,Function,Type) :-
        nonvar(Function), !,
        Function =.. [FName|FArgs],
        D = dom(_,_,_,_,Functions,FTypes),
        nth0(I,Functions,func(FName,_FArgNames,FArgTypes)),
        nth0(I,FTypes,FType),
        check_subtype(D,FType,Type),
        check_terms(D,V,T,PV,FArgs,FArgTypes).

check_fhead(D,V,T,PV,H) :- !,
        check_function(D,V,T,PV,H,number).

% check_subtype(D,SubType,Type)
% succeeds if SubType is a subtype of Type according to D
check_subtype(_,Type,Type) :- !.
check_subtype(_,_Type,object) :- !.
check_subtype(_,Type,either(Types)) :-
        member(Type,Types), !.
check_subtype(D,Type,either(Types)) :- !,
        member(Type2,Types),
        check_subtype(D,Type,Type2).
check_subtype(D,SubType,Type) :-
        D = dom(_,Types,_,_,_,_),
        member(STD,Types),
        STD =.. [Type,SubTypes],
        check_subtype_list(D,SubType,SubTypes).

% check_subtype_list(D,SubType,Types)
% succeeds if SubType is a subtype of one of Types according to D
check_subtype_list(D,SubType,[Type]) :- !,
        check_subtype(D,SubType,Type).
check_subtype_list(D,SubType,[Type|_Types]) :-
        check_subtype(D,SubType,Type), !.
check_subtype_list(D,SubType,[_|Types]) :- !,
        check_subtype_list(D,SubType,Types).
