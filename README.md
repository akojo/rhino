Rhino
=====

Rhino is a simple theorem prover for predicate logic formulas, or anything that
can be expressed as such.

Using Rhino
-----------

###Building Rhino

`make`

###Syntax

Rhino programs are Prolog programs that use a custom layout and operators
designed for expressing predicate logic formulas. A Rhino program consists of
three sections: constant definitions, givens and a provable formula, as follows:

```prolog
constants.
e.

given.
k(e,e).
forall(x, forall(y, forall(z, forall(u, k(x,y) & l(y,u,z) => k(c(u,x),z))))).
forall(x, l(e,x,c(x,e))).
forall(y, forall(u, forall(z, forall(x, l(y,u,z) => l(c(x,y),u,c(x,z)))))).

prove.
k(c(1, c(2, e)), c(2, c(1, e))).
```

Since Rhino programs are handled as Prolog terms, you need to use Prolog
syntactic conventions, i.e. use only lowercase atoms, or enclose atom names in
single quotes, and end all terms with a full stop.

####Constants

Since Rhino programs are Prolog programs, you need to tell the system which
terms are constants in a formula. All atoms not found in the constants list
will be handled as variables in formulas. The constants section is optional.

####Givens

This section contains all formulas that are assumed to hold. The givens section
is also optional.

####Prove

This section is the only mandatory one and must hold exactly one formula to be
proven.

####Operators

Rhino supports all logical operators and also universal and existential
quantifiers. The operators are, in precedence order (from lowest to highest):

* `forall`
  The universal quantifier. To use it as a prefix operator, as is customary in
  logical formulas, the quantifier must be written as `forall(var, <formula>)`.
  You can also use infix notation `var forall <formula>`. When printing
  formulas, Rhino uses infix notation.

* `exists`
  The existential quantifier. Is used as the `forall` quantifier.

* `<=>`
  Equivalence.

* `=>`
  Implication.

* `v`
  Disjunction.

* `&`
  Conjunction.

* `~`
  Negation.

###Proving formulas

To prove a formula, write the constants, givens and the provable formula to a
file and the invoke rhino:

```
./rhino <filename>
```

###Output

An example of Rhino's output while proving a simple formula (`(b => c) => (a =>
c)`), with one given fact (`a => b`) is shown below.

```
Original formula(s):
{a=>b}
{(b=>c)=>a=>c}

Clauses are:
1. {~a v b}
2. {~b v c}
3. {a}
4. {~c}

Resolving set:
          {a}, {~a v b}, MGU {}
5. {b}
          {b}, {~b v c}, MGU {}
6. {c}
          {c}, {~c}, MGU {}
7. { }, Contradiction
```

First Rhino prints the formulas it read from the input file, then it prints a
list of fact that were derived by transforming the original formulas into
discjuntive form.

After that, Rhino prints all the steps it uses when trying to prove the given
statement from the given facts. For each step, Rhino prints an indented line
showing which clauses it is resolving, and possibly Most General Unifier when
using predicates. Then it prints as the next step a new clause that was derived
from the clauses to be resolved.

Rhino continues resolving clauses until it can derive an empty clause, in which
case the statement to be proved has been successfully proven, or until it cannot
find any more resolvable clauses and states that there is no solution.
