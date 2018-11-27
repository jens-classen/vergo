/** <module> fo2solver

This module implements an interface to the FO²-Solver from 

http://forsyte.at/people/kotek/fo2-solver/

and as described in 

Shachar Itzhaky et al.:
On the Automated Verification of Web Applications with Embedded SQL
In Proceedings of the Twentieth International Conference on Database Theory (ICDT 2017),
Schloss Dagstuhl - Leibniz-Zentrum fuer Informatik, 2017.

The purpose of this module is to provide one of multiple alternative
implementations of a reasoner to be used by the FOL module.

@author  Jens Claßen
@license GPL

 **/

:- module(fo2solver, [entails/2,
                      inconsistent/1,
                      consistent/1,
                      valid/1,
                      equivalent/2,
                      op(1130, xfy, <=>),
                      op(1110, xfy, <=),
                      op(1110, xfy, =>)]).

/* We use the following symbols for writing formulas:

   true
   false

    *  conjunction
    +  disjunction
    -  negation
   <=> equivalence
    => implication
   <=  implication
    
    =  equality

   some(Variable,Formula) existential quantification
   all(Variable,Formula)  universal quantification

   Variables have to be (uppercase) Prolog variables. */


% % TPTP FOF operator definitions from Jens Otten's LeanCoP
% /* Operator definitions for TPTP syntax. */
:- op(1130, xfy, <=>). % equivalence
:- op(1110, xfy, =>).  % implication
:- op(1110, xfy, <=).  % implication
% :- op( 500, fy, ~).    % negation
% :- op( 500,xfy, :).

% :- op(1100, xfy, '|').  % disjunction
% :- op(1000, xfy, &).    % conjunction
% :- op( 500, fy, !).     % universal quantifier
% :- op( 500, fy, ?).     % existential quantifier
% :- op( 400, xfx, =).    % equality
% :- op( 299, fx, $).     % for $true/$false

:- use_module('../lib/env').
:- use_module('../lib/utils').

fo2solver_dir(Path) :-
        getenv('PATH_FO2SOLVER', Path).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Interface to FO²-Solver
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

/* Succeeds if ListOfFormulas is consistent. */
consistent(ListOfFormulas) :-
        fo2_solver(ListOfFormulas,Result), !,
        Result = sat.

/* Succeeds if ListOfFormulas is inconsistent. */
inconsistent(ListOfFormulas) :-
        fo2_solver(ListOfFormulas,Result), !,
        Result = unsat.

/* Succeeds if ListOfAxioms entails Conjecture. */
entails(ListOfAxioms,Conjecture) :-
        inconsistent([-Conjecture|ListOfAxioms]).

/* Succeeds if Formula is valid. */
valid(Formula) :-
        inconsistent([-Formula]).

/* Succeeds if Formula1 and Formula2 are equivalent. */
equivalent(Formula1,Formula2) :-
        inconsistent([(Formula1*(-Formula2))+((-Formula1)*Formula2)]).

/* Calls FO²-Solver on Formulas, Result is either 'sat' or 'unsat'. */
fo2_solver(Formulas,Result) :-
        fo2solver_dir(SolverDir),
        working_directory(WorkDir,SolverDir),
        temp_file(File),
        writeToFile(Formulas, File),
        process_create(path('java'), 
                       ['-jar', 'FO2solver-wrapper.jar',
                        File],                
                       [stdout(pipe(Output)), % pipe to parse result
                        stderr(pipe(Output)),
                        process(PID)]),       % need PID for exit status
        process_wait(PID, _Status), !,        % wait for completion
        read_string(Output,"","",_,String),
        close(Output),
        get_fo2_solver_result(String,Result), % return value
        working_directory(_,WorkDir).
        
fo2_solver(_Formulas,_Result) :-
        report_message(['Failed while attempting to use FO²-Solver!']),
        report_message(['Aborting...']),
        report_message(['Check your settings! (PATH_FO2SOLVER variable set?)']),
        abort.
        
get_fo2_solver_result(String, sat) :-
        sub_string(String,_,_,_N,"SATISFIABLE by"), !.
get_fo2_solver_result(String, unsat) :-
        sub_string(String,_,_,_N,"UNSATISFIABLE"), !.
get_fo2_solver_result(String,_) :- !,
        temp_file(File),
        report_message(['Unexpected FO²-Solver output:']),
        report_message(['Aborting...']),
        report_message([String]),
        report_message(['Check ', File, '.']),
        abort.

temp_file(File) :-
        temp_dir(TempDir),
        string_concat(TempDir, '/fo2problem.smt2', File).

writeToFile(Formulas, FileName) :-
        open(FileName, write, Stream),
        write(Stream, '(declare-sort V 0)\n'),
        writeDeclarations(Stream, Formulas),
        write(Stream, '(assert\n'),
        write(Stream, '(and\n'),
        writeFormulas(Stream, Formulas),
        write(Stream, '))(check-sat)\n'),
	close(Stream).
        
/* writeFormulas(+Stream, +Formulas)
   Writes Formulas to Stream in SMT-LIBv2 syntax. */
writeFormulas(_Stream, []).
writeFormulas(Stream, [Formula|Formulas]) :-
        convert_formula_to_fo2(Formula,CFormula),
        write_formula(Stream, CFormula),
        write(Stream, '\n'),
        writeFormulas(Stream, Formulas).

/* convert_formula_to_fo2(+Formula,-ConvertedFormula)

   Converts formula to FO^2 in the sense that ConvertedFormula is the
   result of instantiating one of the two variable symbols in Formula
   by 'x' and the other by 'y'. Should Formula contain more than two
   variable symbols, the process is aborted with an error message. */
convert_formula_to_fo2(Formula,ConvertedFormula) :-
        copy_term(Formula,ConvertedFormula),
        term_variables(ConvertedFormula,[]), !.
convert_formula_to_fo2(Formula,ConvertedFormula) :-
        copy_term(Formula,ConvertedFormula),
        term_variables(ConvertedFormula,[x]), !.
convert_formula_to_fo2(Formula,ConvertedFormula) :-
        copy_term(Formula,ConvertedFormula),
        term_variables(ConvertedFormula,[x,y]), !.
convert_formula_to_fo2(-F1,-CF1) :- !,
        convert_formula_to_fo2(F1,CF1).
convert_formula_to_fo2(F1*F2,CF1*CF2) :- !,
        convert_formula_to_fo2(F1,CF1),
        convert_formula_to_fo2(F2,CF2).
convert_formula_to_fo2(F1+F2,CF1+CF2) :- !,
        convert_formula_to_fo2(F1,CF1),
        convert_formula_to_fo2(F2,CF2).
convert_formula_to_fo2(Formula,_ConvertedFormula) :- !,
        report_message(['Failed while attempting to use FO²-Solver!']),
        report_message(['Input formula contains more than two variable symbols:']),
        report_message([Formula]),
        report_message(['Aborting...']),
        abort.

write_formula(Stream, F1<=>F2) :- !,
        write_binary_formula(Stream, F1, '<=>', F2).
write_formula(Stream, F1=>F2) :- !,
        write_binary_formula(Stream, F1, '=>', F2).
write_formula(Stream, F1<=F2) :- !,
        write_binary_formula(Stream, F1, '<=', F2).
write_formula(Stream, F1*F2) :- !,
        write_binary_formula(Stream, F1, 'and', F2).
write_formula(Stream, F1+F2) :- !,
        write_binary_formula(Stream, F1, 'or', F2).
write_formula(Stream, -F) :- !,
        write(Stream, '(not '),
        write_formula(Stream, F),
        write(Stream, ' )').
write_formula(Stream, some(V,F)) :- !,
        write_quantified_formula(Stream,'exists',V,F).
write_formula(Stream, all(V,F)) :- !,
        write_quantified_formula(Stream,'forall',V,F).
write_formula(Stream, true) :- !,
        write_formula(Stream,all(x,(x=x))).
write_formula(Stream, false) :- !,
        write_formula(Stream,-true).
write_formula(Stream, (X=Y)) :- !,
        write(Stream, '(= '),
        write_fml_term(Stream, X),
        write(Stream, ' '),
        write_fml_term(Stream, Y),
        write(Stream, ')').
write_formula(Stream, F) :-
        F =.. [Pred], !,
        write(Stream, '('),
        write(Stream, Pred),
        write(Stream, ' '),
        write_fml_term(Stream, Pred), % no 0-ary predicates allowed
        write(Stream, ')').  % =>  p ->  p(p)
write_formula(Stream, F) :-
        F =.. [Pred,Arg], !,
        write(Stream, '('),
        write(Stream, Pred),
        write(Stream, ' '),
        write_fml_term(Stream, Arg),
        write(Stream, ')').
write_formula(Stream, F) :-
        F =.. [Pred,Arg1,Arg2], !,
        write(Stream, '('),
        write(Stream, Pred),
        write(Stream, ' '),
        write_fml_term(Stream, Arg1),
        write(Stream, ' '),
        write_fml_term(Stream, Arg2),
        write(Stream, ')').

write_binary_formula(Stream, F1, Symbol, F2) :-
        write(Stream, '('),
        write(Stream, Symbol),
        write(Stream, ' '),
        write_formula(Stream, F1),
        write(Stream, ' '),
        write_formula(Stream, F2),
        write(Stream, ')').

write_quantified_formula(Stream,Quantifier,V,F) :-
        is_list(V), V \= [], !,
        write(Stream, '('),
        write(Stream, Quantifier),
        write(Stream, ' ('),
        write_variable_list(Stream, V),
        write(Stream, ') '),
        write_formula(Stream, F),
        write(Stream, ')').
write_quantified_formula(Stream,Quantifier,V,F) :-
        not(is_list(V)), !,
        write_quantified_formula(Stream,Quantifier,[V],F).
write_quantified_formula(Stream,_Quantifier,[],F) :- !,
        write_formula(Stream,F).

write_variable_list(Stream,[Var|Vars]) :-
        write(Stream, '('),
        write(Stream, Var),
        write(Stream, ' V)'),
        write_variable_list(Stream,Vars).
write_variable_list(_Stream,[]).

write_fml_term(Stream,Term) :-
        var(Term), !,
        write_fml_variable(Stream,Term).
write_fml_term(Stream,Term) :-
        write(Stream,Term).

write_fml_variable(Stream,Var) :-
        write(Stream,'|var'),
        write(Stream,Var),
        write(Stream,'|').

writeDeclarations(Stream,Formulas) :-
        get_predicates(Formulas,Predicates),
        write_predicate_declarations(Stream,Predicates).

write_predicate_declarations(_Stream,[]).
write_predicate_declarations(Stream,[Predicate|Predicates]) :-
        write_predicate_declaration(Stream,Predicate),
        write_predicate_declarations(Stream,Predicates).

write_predicate_declaration(Stream,pred(Name,0)) :-
        write(Stream,'(declare-fun '),
        write(Stream,Name),
        write(Stream,' () Bool)\n').
write_predicate_declaration(Stream,pred(Name,1)) :-
        write(Stream,'(declare-fun '),
        write(Stream,Name),
        write(Stream,' (V) Bool)\n').
write_predicate_declaration(Stream,pred(Name,2)) :-
        write(Stream,'(declare-fun '),
        write(Stream,Name),
        write(Stream,' (V V) Bool)\n').

get_predicates(Formulas,Predicates) :-
        setof(Predicate,
              is_fml_predicate(Formulas,Predicate),
              Predicates).

is_fml_predicate([Formula|Formulas],Predicate) :- !,
        is_fml_predicate(Formula,Predicate);
        is_fml_predicate(Formulas,Predicate).
is_fml_predicate(Formula,Predicate) :-
        (Formula = (F1 <=> F2);
         Formula = (F1  => F2);
         Formula = (F1 <=  F2);
         Formula = (F1  *  F2);
         Formula = (F1  +  F2)), !,
        (is_fml_predicate(F1,Predicate);
         is_fml_predicate(F2,Predicate)).
is_fml_predicate(Formula,Predicate) :-
        (Formula = (-F);
         Formula = all(_,F);
         Formula = some(_,F)), !,
        is_fml_predicate(F,Predicate).
is_fml_predicate(Atom,pred(Symbol,Arity)) :- !,
        Atom =.. [Symbol|Args],
        length(Args,Arity).
