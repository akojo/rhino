Rhino
=====

Rhino is a simple theorem prover for predicate logic formulas, or anything that
can be expressed as such.

Using Rhino
-----------

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

###Syntax

Since Rhino programs are handled as Prolog terms, you need to use Prolog
syntactic conventions, i.e. use only lowercase atom, or enclose atom names in
single quotes and end all terms with a full stop.

###Constants

Since Rhino programs are Prolog programs, you need to tell the system which
terms are constants in a formula. All atoms not found in the constants list
will be handled as variables in formulas. The constants section is optional.

###Givens

This section contains all formulas that are assumed to hold. The givens section
is also optional.

###Prove

This section is the only mandatory one and must hold exactly one formula to be
proven.

###Operators

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
