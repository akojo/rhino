%-*-Prolog-*-%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Theorem prover for predicate logic formulas
%
% Author: Atte Kojo
% Year:   2002
%
% Based on resolution algorithm for propositional logic
% formulas proposed by I.Bratko (Bratko: Prolog Programming
% for Artificial Intelligence, Addison-Wesley 1986,
% ss. 396).
%
% Enhanced with transformation rules for predicate logic
% formulas and unification algorithm. Also includes simple
% methods for reading input from a file.
%
% I have commented all predicates so that they include the
% suggested direction for arguments (or at least the
% direction I use)
%
% Written for GNU Prolog 1.2
% Should also work with any other ISO compatible Prolog
% interpreter/compiler
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Operators for predicate logic
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- op(100, fy, ~).
:- op(110, xfy, &).
:- op(120, xfy, v).
:- op(130, xfy, =>).
:- op(140, xfy, <=>).
:- op(150, xfy, forall).
:- op(150, xfy, exists).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Some useful predicates
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% ISO standard defines not as \+ (strange indeed; and very
% counter-intuitive)
not(Goal) :- \+ Goal.

% If an unknown goal is called, interpreter fails instead of
% throwing an exception (ISO predicate)
:- set_prolog_flag(unknown, fail).

% Catch errors caused by user writing bogus terms (catch is
% an ISO predicate)
prot_read(Term) :-
	catch(read(Term), Err, die(Err)).

% Print an error an halt the program
die(Error) :-
	write('User fumbled hopelessly: '), nl,
	tab(4), write(Error), nl, nl,
	write('Cannot continue, halting.'), nl,
	halt.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Main program for the theorem prover
%
% Reads a list of terms from a given file and tries to find
% a contradiction.
%
% The term to be proved must be preceded by term 'prove.'
% and it must be the last term in the file.
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

solve(Filename) :-
	catch(see(Filename), Err, die(Err)),
	prot_read(Term),
	write('Original formula(s):'), nl,
	read_program(init, Term), nl,
	print_clauses,
	write('Resolving set:'), nl,
	run, !.

% read_program(in, in)
%
% A state machine for reading program input

read_program(_, end_of_file) :- 
	!,
	die('No formula to prove.'), nl,
	halt.

read_program(_, constants) :-
	prot_read(Term),
	read_program(constants, Term).

read_program(_, given) :-
	prot_read(Term),
	read_program(given, Term).

read_program(_, prove) :-
	prot_read(Term),
	read_program(prove, Term).

read_program(init, Term) :-
	trans(~Term), !.

read_program(constants, Term) :-
	assertz(constant(Term)),
	prot_read(NewTerm),
	read_program(constants, NewTerm).

read_program(given, Term) :-
	trans(Term),
	write_clause(Term), nl,
	prot_read(NewTerm),
	read_program(given, NewTerm).

read_program(prove, Term) :-
	write_clause(Term), nl,
	trans(~Term), !.

% print_clauses
%
% A predicate to print out all clauses stored in the program
% database

print_clauses :-
	write('Clauses are:'), nl,
	findall(X, clause(X), Clauses),
	print_clauselist(Clauses), nl.

print_clauselist([]).

print_clauselist([Clause| Others]) :-
	write_step,
	write_clause(Clause), nl,
	print_clauselist(Others).

write_clause(Clause) :-
	write('{'),
	write(Clause),
	write('}').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Transformation algorithm
%
% Transforms a formula into a form suitable for the proving
% algorithm
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

trans(Formula) :-
	trans_prenex(Formula, NewFormula),
	trans_skolem(NewFormula, NewerFormula), !,
	trans_cnf(NewerFormula, Result),
	input_clauses(Result), !.

input_clauses(L & R) :-
	input_clauses(L),
	input_clauses(R).

input_clauses(X) :-
	assertz(clause(X)).

% trans_prenex(in, out)
%
% Applies translate as long as it takes to get the formula
% to prenex normal form

trans_prenex(Formula, Result) :-
	translate(Formula, NewFormula),
	(Formula == NewFormula, Result = Formula, !;
	    trans_prenex(NewFormula, Result)).

% translate(in, out)
%
% Perform recursively one round of transformations towards
% prenex normal form.
% 
% NOTE: translate doesn't get the formula right in one pass,
% thus it must be called consecutively to get it right.

translate(forall(X, Y), Result) :-
	translate(Y, NewY),
	transform(forall(X, NewY), Result).

translate(exists(X, Y), Result) :-
	translate(Y, NewY),
	transform(exists(X, NewY), Result).

translate(X <=> Y, Result) :-
	transform(X <=> Y, NewFormula),
	translate(NewFormula, Result).

translate(X => Y, Result) :-
	transform(X => Y, NewFormula),
	translate(NewFormula, Result).

translate(X v Y, Result) :-
	translate(X, NewX),
	translate(Y, NewY),
	transform(NewX v NewY, Result).

translate(X & Y, Result) :-
	translate(X, NewX),
	translate(Y, NewY),
	transform(NewX & NewY, Result).

translate(~X, Result) :-
	translate(X, NewX),
	transform(~NewX, Result).

translate(X,  Result) :-
	transform(X, Result). 

% transform(in, out)
%
% Rules for transforming predicate logic formulas into
% prenex normal form

transform(~forall(T, Y), exists(T, ~Y)) :- !.
transform(~exists(T, Y), forall(T, ~Y)) :- !.
transform(X v exists(T, Y), exists(NewT, X v Result)) :-
	rename(T, NewT, Y, Result), 
	incr_number, !.
transform(exists(T, X) v Y, exists(NewT, Result v Y)) :-
	rename(T, NewT, X, Result), 
	incr_number, !.
transform(X & exists(T, Y), exists(NewT, X & Result)) :-
	rename(T, NewT, Y, Result), 
	incr_number, !.
transform(exists(T, X) & Y, exists(NewT, Result & Y)) :-
	rename(T, NewT, X, Result), 
	incr_number, !.
transform(X v forall(T, Y), forall(NewT, X v Result)) :-
	rename(T, NewT, Y, Result), 
	incr_number, !.
transform(forall(T, X) v Y, forall(NewT, Result v Y)) :-
	rename(T, NewT, X, Result), 
	incr_number, !.
transform(X & forall(T, Y), forall(NewT, X & Result)) :-
	rename(T, NewT, Y, Result), 
	incr_number, !.
transform(forall(T, X) & Y, forall(NewT, Result & Y)) :-
	rename(T, NewT, X, Result), 
	incr_number, !.

transform(X <=> Y, (~X v Y) & (~Y v X)) :- !.
transform(X => Y, ~X v Y) :- !.
transform(~(~X), X) :- !.

% If all else fails, do nothing
transform(X, X) :- !.

% trans_skolem(in, out)
% skolem(in, out) 
% skolem_function(in, in, out)
%
% Generate skolem-functions and -constants for a formula
% that is in prenex normal form.
%
% The algorithm cheats because it doesn't generate any new
% constants but assumes that all constats are already
% distinct.

trans_skolem(Formula, Result) :-
	skolem(Formula, Result).

skolem(exists(_, X), Result) :-
	skolem(X, Result).

skolem(forall(T, X), Result) :-
	skolem_function(X, [T], Result).

skolem(X, X).

skolem_function(forall(T, X), AList, Result) :-
	skolem_function(X, [T| AList], Result).

skolem_function(exists(T, X), AList, Result) :-
	Func =.. [f| AList],
	substitute(T, Func, X, SubResult),
	skolem_function(SubResult, AList, Result).

skolem_function(X, _, X).

% trans_cnf(in, out)
%
% Transform formula into conjunctive normal form

trans_cnf(L & R, NewL & NewR) :-
	trans_cnf(L, NewL),
	trans_cnf(R, NewR).

trans_cnf(Formula, Result) :-
	transform_cnf(Formula, NewFormula), !,
	trans_cnf(NewFormula, Result).

trans_cnf(Formula, Formula).

% transform_cnf(in, out)
%
% Transformation rules for transforming a formula into cnf

transform_cnf(~(~X), X) :- !.

transform_cnf(~(X v Y), ~X & ~Y) :- !.
transform_cnf(~(X & Y), ~X v ~Y) :- !.

transform_cnf(X v Y & Z, (X v Y) & (X v Z)) :- !.
transform_cnf(X & Y v Z, (X v Z) & (Y v Z)) :- !.

transform_cnf(X v Y, X1 v Y) :-
	transform_cnf(X, X1), !.

transform_cnf(X v Y, X v Y1) :-
	transform_cnf(Y, Y1), !.

transform_cnf(~X, ~X1) :-
	transform_cnf(X, X1).

% rename(in, in, in, out)
%
% Renames all atoms matching T to something completely new

rename(T, NewT, Atom, NewAtom) :-
	atom(Atom),
	rename_atoms(T, NewT, [Atom], [NewAtom]).

rename(T, NewT, Formula, NewFormula) :-
	pure_predicate(Formula),
	Formula =.. [Op| Atoms],
	rename_atoms(T, NewT, Atoms, NewAtoms),
	NewFormula =.. [Op| NewAtoms].

rename(T, NewT, Left forall Right, NewLeft forall NewRight) :-
	rename(T, NewT, Left, NewLeft),
	rename(T, NewT, Right, NewRight).

rename(T, NewT, Left exists Right, NewLeft exists NewRight) :-
	rename(T, NewT, Left, NewLeft),
	rename(T, NewT, Right, NewRight).

rename(T, NewT, Left <=> Right, NewLeft <=> NewRight) :-
	rename(T, NewT, Left, NewLeft),
	rename(T, NewT, Right, NewRight).

rename(T, NewT, Left => Right, NewLeft => NewRight) :-
	rename(T, NewT, Left, NewLeft),
	rename(T, NewT, Right, NewRight).

rename(T, NewT, Left v Right, NewLeft v NewRight) :-
	rename(T, NewT, Left, NewLeft),
	rename(T, NewT, Right, NewRight).

rename(T, NewT, Left & Right, NewLeft & NewRight) :-
	rename(T, NewT, Left, NewLeft),
	rename(T, NewT, Right, NewRight).

rename(T, NewT, ~Formula, ~NewFormula) :-
	rename(T, NewT, Formula, NewFormula).

% rename_atoms(in, in, in, out)
%
% Renames an atom (or atoms) to something new

rename_atoms(T, T, [], []).

rename_atoms(T, NewAtom, [Atom| Others], [NewAtom| NewOthers]) :-
	T = Atom,
	name(Atom, L1),
	get_number(N),
	name(N, L2),
	append(L1, L2, List),
	name(NewAtom, List),
	rename_atoms(T, _, Others, NewOthers).

rename_atoms(T, NewT, [Atom| Others], [Atom| NewOthers]) :-
	rename_atoms(T, NewT, Others, NewOthers).

% get_number(out)
%
% Get the current index number for the new constants

get_number(Number) :-
	retract(a_number(Number)),
	assertz(a_number(Number)).

get_number(100) :-
	incr_number.

% incr_number
%
% Increases the running index for renaming constants

incr_number :-
	retract(a_number(OldNumber)), !,
	Number is OldNumber + 1,
	assertz(a_number(Number)).

incr_number :- 
	assertz(a_number(100)).

% substitute(in, in, in, out)
%
% Substitutes T for Func in predicate's arguments
% I.e p(x, y) -> p(x, f(x)). That is, in an input predicate,
% not a Prolog predicate.

substitute(T, Func, Left forall Right, Result) :-
	substitute(T, Func, Left, NewLeft),
	substitute(T, Func, Right, NewRight),
	Result = NewLeft forall NewRight.

substitute(T, Func, Left exists Right, Result) :-
	substitute(T, Func, Left, NewLeft),
	substitute(T, Func, Right, NewRight),
	Result = NewLeft exists NewRight.

substitute(T, Func, Left v Right, Result) :-
	substitute(T, Func, Left, NewLeft),
	substitute(T, Func, Right, NewRight),
	Result = NewLeft v NewRight.

substitute(T, Func, Left & Right, Result) :-
	substitute(T, Func, Left, NewLeft),
	substitute(T, Func, Right, NewRight),
	Result = NewLeft & NewRight.

substitute(T, Func, ~Formula, ~Result) :-
	substitute(T, Func, Formula, Result).

substitute(T, Func, Formula, Result) :-
	Formula =.. [Op| Atoms],
	substitute_atoms(T, Func, Atoms, NewAtoms),
	Result =.. [Op| NewAtoms].

% substitute_atoms(in, in, in, out)
%
% Substitute A for Func in a list containing atoms and
% possibly functions

substitute_atoms(_, _, [], []).

substitute_atoms(A, Func, [A| Rest], [Func| Result]) :-
	substitute_atoms(A, Func, Rest, Result).

substitute_atoms(A, Func, [B| Rest], [B| Result]) :-
	atom(B),
	substitute_atoms(A, Func, Rest, Result).

substitute_atoms(A, Func, [B| Rest], [NewB| Result]) :-
	predicate(B),
	substitute(A, Func, B, NewB),
	substitute_atoms(A, Func, Rest, Result).


% pure_predicate(in)
%
% Checks whether a given term is a predicate

pure_predicate(X) :-
	atomic(X).

pure_predicate(X) :- 
	X =.. [F| Args],
	not(operator(F)),
	pred_list(Args).

% pred_list(in)
%
% Checks that a given list contains only atoms or predicates

pred_list([]).

pred_list([H| T]) :-
	atomic(H),
	pred_list(T).

pred_list([H| T]) :-
	pure_predicate(H),
	pred_list(T).

% operator(in)
%
% Tells which atoms are actually logical operators

operator(forall).
operator(exists).
operator(<=>).
operator(=>).
operator(v).
operator(&).
operator(~).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Program interpreter for general pattern programs
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- op(800, xfx, --->).

run :-
	Cond ---> Action,
	test(Cond),
	execute(Action).

test([]).

test([First| Rest]) :-
	call(First),
	test(Rest).

execute([stop]) :- !, halt.

execute([]) :-
	run.

execute([First| Rest]) :-
	call(First),
	execute(Rest).

replace(A, B) :-
	retract(A), !,
	assertz(B).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Resolution algorithm
%
% Solves a set of clausules using resolution mehtod.
%
% Uses the interpreter above
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% These patterns for the above interpreter are the actual
% resolution algorithm. They manipulate the clauses using
% assertz and retract

% Tries to find to contradicting clauses
[clause(X1), clause(~X2)] --->
	[not(~_ = X1), % Make sure there are no negations in
		       % the first term. Unification
		       % algorith is really not good at
		       % these things.
	unify(X1, X2, MGU),
	tab(10),
	write_clause(X1),
	write(', '),
	write_clause(~X2), 
	write(', '),
	write_unifier(MGU), nl,
	write_step,
	write('{ }, Contradiction'), nl, stop].

% Removes a clause from database that is trivially true,
% i.e. contains both p and ~p (or two predicates that unify
% and one is negation of the other)
[clause(C), in(P1, C), in(~P2, C)] --->
	[not(~_ = P1),
	unify(P1, P2, _),
	retract(clause(C)),
	tab(10),
	write_clause(C), nl,
	write('Removed true clause.'), nl].

% Simplifies formula by removing multiple instances of same
% predicate (or proposition) form a clause
[clause(C), delete_term(~P1, C, C1), in(~P2, C1)] --->
	[unify(P1, P2, MGU),
	diff_substitute(MGU, C1, C1U),
	replace(clause(C), clause(C1U)),
	tab(10),
	write_clause(C), 
	write(', '),
	write_unifier(MGU), nl,
	write_step,
	write_clause(C1U), nl].

% As above
[clause(C), delete_term(P1, C, C1), in(P2, C1)] --->
	[unify(P1, P2, MGU),
	diff_substitute(MGU, C1, C1U),
	replace(clause(C), clause(C1U)),
	tab(10),
	write_clause(C), 
	write(', '),
	write_unifier(MGU), nl,
	write_step,
	write_clause(C1U), nl].

% Special case
% Resolves a one-term clause with another clause 
[clause(P1), clause(C), delete_term(~P2, C, C1), not(done(P1, C, P1))] --->
	[not(~_ = P1),
	unify(P1, P2, MGU),
	diff_substitute(MGU, C1, C1U),
	assertz(clause(C1U)), assertz(done(P1, C, P1)),
	tab(10),
	write_clause(P1),
	write(', '),
	write_clause(C), 
	write(', '),
	write_unifier(MGU), nl,
	write_step,
	write_clause(C1U), nl].

% As above, now with negations other way round
[clause(~P1), clause(C), delete_term(P2, C, C1), not(done(~P1, C, P1))] --->
	[not(~_ = P2),
	unify(P1, P2, MGU),
	diff_substitute(MGU, C1, C1U), 
	assertz(clause(C1U)), assertz(done(~P1, C, P1)),
	tab(10),
	write_clause(~P1),
	write(', '),
	write_clause(C), 
	write(', '),
	write_unifier(MGU), nl,
	write_step,
	write_clause(C1U), nl].

% General case
% Resolves to clauses with each other
[clause(C), delete_term(P1, C, NewC), clause(D), delete_term(~P2, D, NewD), not(done(NewC, NewD, P1))] --->
	[not(~_ = P1),
	unify(P1, P2, MGU),
	diff_substitute(MGU, NewC v NewD, CU),
	assertz(clause(CU)), assertz(done(NewC, NewD, P1)),
	tab(10),
	write_clause(C),
	write(', '),
	write_clause(D), 
	write(', '),
	write_unifier(MGU), nl,
	write_step,
	write_clause(CU), nl].

% If nothing above fits, we couldn't prove the set to be unsatisfiable 
[] ---> 
	[write('No solution found'), nl, stop].

% write_step
%
% Prints the current resolution step number to the screen

write_step :-
	retract(step(Step)), !,
	NewStep is Step + 1,
	write(NewStep),
	write('. '),
	assertz(step(NewStep)).

write_step :- 
	write('1. '),
	assertz(step(1)).

% in(in, in)
%
% Checks whether a predicate is in a clausule

in(X, X) :- predicate(X), !.

in(X, C) :-
	delete_term(X, C, _).

% delete_term(in, in, out)
%
% Deletes a predicate from a clausule

delete_term(X, X v Y, Y) :- predicate(X).

delete_term(X, Y v X, Y) :- predicate(X).

delete_term(X, Y v Z, Y v Z1) :-
	delete_term(X, Z, Z1).

delete_term(X, Y v Z, Y1 v Z) :-
	delete_term(X, Y, Y1).

% predicate(in)
%
% Accepts as predicates also negated predicates (e.g. ~p(x))

predicate(X) :-
	pure_predicate(X), !.

predicate(~X) :-
	pure_predicate(X), !.

% write_unifier(in)
%
% Writes a list of unifiers to the screen preceded by MGU
% (most general unifier)

write_unifier(U) :-
	write('MGU {'),
	write_ulist(U),
	write('}').

write_ulist([U]) :-
	write(U).

write_ulist([U| Tail]) :-
	write(U), write(', '),
	write_ulist(Tail).

write_ulist([]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Unification algorithm 
%
% Finds the most general unifier (MGU) for two predicates or
% fails if MGU is not found
%
% NOTE: Due to the above algorithm, unify is always called
% with two (possibly negated) predicates as arguments.
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Special cases: propositional logic
unify(X, X, []) :-
	atom(X).

unify(~X, ~X, []) :-
	atom(X).

unify(~X, ~Y, []) :-
	atom(X), !,
	atom(Y),
	fail.

unify(~X, Y, []) :-
	atom(X), !,
	atom(Y),
	fail.

unify(X, ~Y, []) :-
	atom(X), !,
	atom(Y),
	fail.

unify(X, Y, []) :-
	atom(X), !,
	atom(Y),
	fail.

% Real unification for predicate logic
unify(X, X, []) :- !.

unify(~X, ~Y, D) :-
	unify(X, Y, D).

unify(~X, Y, D) :-
	unify(X, Y, D).

unify(X, ~Y, D) :-
	unify(X, Y, D).

unify(X, Y, [D| Rest]) :-
	diff(X, Y, D),
	diff_substitute([D], X v Y, NewX v NewY), !,
	unify1(NewX, NewY, Rest, []).

% unify1(in, in, in, out)
%
% same as unify, but with circular unification prevention,
% i.e. if we go back to some previous form during
% unification, the formula is obviously not unifiable

unify1(X, X, [], _) :- !.

unify1(X, Y, [D| Rest], Done) :-
	diff(X, Y, D),
	diff_substitute([D], X v Y, NewX v NewY), !,
	not(member(NewX v NewY, Done)),
	unify1(NewX, NewY, Rest, [NewX v NewY| Done]).

% diff(in, in, out)
%
% Finds the difference set for two predicates

diff(X, Y, D) :-
	X =.. [Px| Ax],
	Y =.. [Py| Ay],
	Px == Py,
	diff_set(Ax, Ay, D), !.

% diff_set(in, in, out)
%
% Finds first difference in two lists

diff_set([], [], []) :- !.

diff_set([Hx| Rx], [Hy| Ry], Rd) :-
	Hx == Hy,
	diff_set(Rx, Ry, Rd).
diff_set([Hx|_], [Hy|_], Hx/Hy) :-
	atom(Hx),
	not(is_constant(Hx)),
	(atom(Hy); constant_term(Hy)),
	not(contains(Hy, Hx)), !.

diff_set([Hx|_], [Hy|_], Hy/Hx) :-
	atom(Hy),
	not(is_constant(Hy)),
	(atom(Hx); constant_term(Hx)),
	not(contains(Hx, Hy)), !.

diff_set([Hx|_], [Hy|_], D) :-
	diff(Hx, Hy, D).

constant_term(X) :-
	atom(X), !,
	is_constant(X).

constant_term(X) :-
	X =.. [_| Args], 
	constant_list(Args).

constant_list([]).

constant_list([L| Rest]) :-
	constant_term(L),
	constant_list(Rest).

is_constant(X) :-
	retract(constant(X)),
	assertz(constant(X)).

% contains
%
% Checks if a predicate contains a variable

contains(Pred, V) :-
	Pred =.. [_| Args],
	contains_list(Args, V).

contains_list([V|_], V) :-
	atom(V), !.

contains_list([H| Tail], V) :-
	atom(H),
	contains_list(Tail, V).

contains_list([H| Tail], V) :-
	contains(H, V), !;
	contains_list(Tail, V).

% diff_substitute
%
% Performs substitutions in a formula according to a
% difference set D

diff_substitute([], Formula, Formula).

diff_substitute([X/Y| Rest], Formula, Result) :-
	substitute(X, Y, Formula, NewFormula),
	diff_substitute(Rest, NewFormula, Result).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Predicates for compiling the program
%
% To be used with GNU Prolog's gplc
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- initialization(main).

main :-
	argument_list([Arg1| _]),
	solve(Arg1).
