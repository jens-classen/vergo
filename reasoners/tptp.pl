/**

<module> TPTP

This module implements an interface to the 'TPTP' (Thousands of
Problems for Theorem Provers) language. The exported procedure
writeTPTPFile/3 allows to write a set of vergo formulas and a
conjecture to a specified file, which can then be processed by a
theorem prover.

@author  Jens Claßen
@license GPLv2

 **/

:- module(tptp, [writeTPTPFile/3]).

:- use_module('../logic/fol', [op(1130, xfy, <=>),
                               op(1110, xfy, <=),
                               op(1110, xfy, =>)]).
:- use_module('../lib/utils').

/* writeTPTPFile(+ListOfAxioms, +Conjecture, +FileName)
   Writes the formulas in ListOfAxioms and +Conjecture in TPTP
   syntax to file named FileName, to be solved by a theorem prover. */
writeTPTPFile(ListOfAxioms, Conjecture, FileName) :-
        set_prolog_flag(gc, false), % ensure consistent variable names
        open(FileName, write, Stream),
        writeTimeStamp(Stream),
        writeAxioms(Stream, ListOfAxioms, 0),
        writeConjecture(Stream, Conjecture, conjecture),
	close(Stream),
        set_prolog_flag(gc, true).

writeTimeStamp(Stream) :-
        local_time_and_date_as_string(TimeS),
        atom_string(TimeA,TimeS),
        write(Stream, '% Automatically generated TPTP problem file\n'),
        write(Stream, '% '),
        write(Stream, TimeA),
        write(Stream, '\n\n').

/* writeAxioms(+Stream, +ListOfAxioms, +N)
   Writes ListOfAxioms to Stream in TPTP syntax, naming
   axioms axiomN, axiom(N+1), axiom(N+2), ... */
writeAxioms(Stream, [], _) :-
        write(Stream, '\n').
writeAxioms(Stream, [Formula|Formulas], N) :-
        write(Stream, 'fof(axiom'),
        write(Stream, N),
        write(Stream, ', axiom, '),
        write_formula(Stream, Formula),
        write(Stream, ').\n'),
        N1 is N+1,
        writeAxioms(Stream, Formulas, N1).

writeConjecture(Stream, Conjecture, Name) :-
        write(Stream, 'fof('),
        write(Stream, Name),
        write(Stream, ', conjecture, '),
        write_formula(Stream, Conjecture),
        write(Stream, ').\n').

write_formula(Stream, F1<=>F2) :-
        write_binary_formula(Stream, F1, '<=>', F2).
write_formula(Stream, F1=>F2) :-
        write_binary_formula(Stream, F1, '=>', F2).
write_formula(Stream, F1<=F2) :-
        write_binary_formula(Stream, F1, '<=', F2).
write_formula(Stream, F1*F2) :-
        write_binary_formula(Stream, F1, '&', F2).
write_formula(Stream, F1+F2) :-
        write_binary_formula(Stream, F1, '|', F2).
write_formula(Stream, -F) :-
        write(Stream, '~( '),
        write_formula(Stream, F),
        write(Stream, ' )').
write_formula(Stream, some(V,F)) :-
        is_list(V), V \= [], !,
        write(Stream, '?'),
        write(Stream, V),
        write(Stream, ':'),
        write_formula(Stream, F).
write_formula(Stream, some(V,F)) :-
        var(V), !,
        write_formula(Stream, some([V],F)).
write_formula(Stream, some([],F)) :- !,
        write_formula(Stream, F).
write_formula(Stream, all(V,F)) :-
        is_list(V), V \= [], !,
        write(Stream, '!'),
        write(Stream, V),
        write(Stream, ':'),
        write_formula(Stream, F).
write_formula(Stream, all(V,F)) :-
        var(V), !,
        write_formula(Stream, all([V],F)).
write_formula(Stream, all([],F)) :- !,
        write_formula(Stream, F).
write_formula(Stream, true) :-
        write(Stream, '$true').
write_formula(Stream, false) :-
        write(Stream, '$false').
write_formula(Stream, F) :-
        writeq(Stream, F). % use (single) quotes where necessary

write_binary_formula(Stream, F1, Symbol, F2) :-
        write(Stream, '( '),
        write_formula(Stream, F1),
        write(Stream, ' '),
        write(Stream, Symbol),
        write(Stream, ' '),
        write_formula(Stream, F2),
        write(Stream, ' )').
