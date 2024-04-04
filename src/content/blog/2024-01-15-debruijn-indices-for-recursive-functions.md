---
title: De Bruijn indices for recursive functions
pubDatetime: 2024-01-15T12:00:00Z
modDatetime: 2024-01-15T12:00:00Z
description: Nameless representations for recursive functions
tags:
  - pl
---

$$
\gdef\fix{\text{fix}}
\gdef\step{\Rightarrow}
\gdef\subst#1#2#3{#1[#2\mapsto #3]}
\gdef\substt#1#2#3#4#5{#1[#2\mapsto #3, #4\mapsto #5]}
\gdef\upup{\Uparrow\Uparrow}
$$

# $$\lambda$$-calculus and operational semantics

_Operational semantics_ is a way to specify behaviors of programming languages by viewing each program as an abstract expression, which could "reduce" or "unfold" to other (simpler or not) abstract expressions via a series of transition steps.

For example, considering the very famous lambda calculus, with syntax for variables, abstractions, and applications:

$$
e\;\coloneqq\;x\;|\;\lambda x.~e\;|\;e_1~e_2
$$

Suppose for the sake of examples that we also have numbers and arithmetic operators in the lambda calculus. Just intuitively, we know that the expression $$(\lambda x.~x+1)~42$$ should reduce to $$43$$. When we see this function application syntax, we bind the argument $$42$$ to the variable $$x$$ introduced by the lambda, and when we evaluate the body $$x+1$$, we know that the $$42$$ should be substituted for $$x$$ in the body.

One way to rigorously define such operation is via a meta-procedure called _subtitution_. It is denoted as $$\subst{e_0}{x}{e'}$$ and is inductively defined on the grammar in the following way:

- If $$e_0$$ is the variable $$x$$, put $$e'$$ in place of it. If it's some different variable, leave it unchanged.
- If $$e_0$$ is some lambda form $$\lambda x.~e$$, then leave it unchanged. Otherwise, substitute the body and perform $$\alpha$$_-renaming_ if necessary.
- If $$e_0$$ is an application form $$e_1~e_2$$, then just substitue both subexpressions separately: $$(\subst{e_1}{x}{e'})(\subst{e_2}{x}{e'})$$.

The case of substituting lambdas can be tricky, as one might run into _variable captures_. The problem is solved by using _capture-free substitutions_. Details can be found in this [lecture note](https://www.cs.cornell.edu/courses/cs6110/2023sp/lectures/lec02.pdf).

There are various _reduction strategies_ that all involve substitution. For our purpose, we will stick to _call-by-value_ (CBV) semantics, which forces arguments to be fully evaluating before performing any substitution.

## Semantics for recursive functions

The classic way to encode recursive functions in lambda calculus is through fixed-point combinators. For example, see the [CBV Y-combinator](https://www.cs.cornell.edu/courses/cs6110/2023sp/lectures/lec05.pdf):

$$
Y \triangleq \lambda t.~(\lambda f.~t(\lambda z.~ffz))(\lambda f.~t(\lambda z.~ffz))
$$

Being a fixed-point combinator, it satisfies the equation that for any function $$F$$, $$F(YF)=YF$$. To define the recursive factorial function using the Y-combinator, for example, one needs to define a "pre-factorial" function first, and apply the combinator to that. However, while this is a perfectly valid way to represent recursion, it is not close to how we actually write programs in practice. An alternative is to use explicit recursion, by augmenting the syntax of the calculus with a new construct

$$
e~\coloneqq \;\dots\;|\;\fix~f~x.~e
$$

We also need a notion of _parallel substitution_, which extends the single substitution definition and substitutes multiple variables simultaneously. For example, the reduction rule for applying an argument to a fix-expression is defined as

$$
(\fix~f~x.~e)e' \step \substt{e}{f}{(\fix~f~x.~e)}{x}{e'}
$$

where in addition to substituting $$e'$$ for $$x$$, we also expand free occurrences of $$f$$ in $$e$$ to copies of the fix-expression itself.

# De Bruijn indices

Although explicitly variable names is essential for practical usage of programming languages, it introduces a lot of headache, as we previously hinted. For example, many metatheoretic results about lambda calculus (and its derivatives) are often framed with the caveat of "up to $$\alpha$$-equivalence". In the definition of substitution above, we also had a dubious _renaming_ operation, which needs to be able to come up with fresh variable names.

A common solution is to switch to a nameless representation of bound variables using _De Bruijn indices_. In such representation, there are no variable names, and bound variables are replaced by natural numbers which refer to how many levels of lambda binders out it refers to. For example, the expression $$\lambda x.~\lambda y.~x$$ is written as $$\lambda. ~\lambda.~1$$ in the nameless style.

Since there are no more variable names, the subtitution operation will need to take care of re-indexing the variables. See this [lecture note](https://www.cs.cornell.edu/courses/cs4110/2018fa/lectures/lecture15.pdf) for a detailed definition of how to do so.

One of the main advantages of De Bruijn indices is that $$\alpha$$-equivalence is not longer a concern at all. This makes it amenable for implementing proof assistants or other dependently typed languages. Yet another use case is in mechanized verification of programming language semantics in proof assistants like _Coq_ or _Agda_. In fact, this blog post is inspired by a problem I encountered when trying to formalize the semantics for a language for distributed systems in Coq.

# Nameless recursive functions
Say we want to formalize the operational semantics of a Turing-complete programming language in proof assistants. It will be nice to be able to combine De Bruijn indices and the explicit recursion we defined above. It turns out this is not so hard to do! The grammar is just ordinary nameless style lambda calculus:
$$
e\;\coloneqq\;x\;|\;\lambda.~e\;|\;e_1~e_2
$$

Although syntactically unchanged, the $$\lambda$$ case is semantically different. Now instead of binding one index, it binds *two* indices, one corresponding to the argument and one to the lambda itself. This is manifested in the new CBV semantics:

$$
\frac{e_1 \step e_1'}{e_1~e_2 \step e_1'~e_2}\quad
\frac{e_2 \step e_2'}{(\lambda.~e_1)~e_2 \step (\lambda.~e_1)~e_2'}\quad
\frac{\;}{(\lambda.~e)~v \step \substt{e}{0}{v}{1}{(\lambda.~e)}}
$$

A quick note for notation: $$[m\mapsto v_1,~m+1\mapsto v_2]$$ denotes the infinite parallel substitution that maps the indices $$n$$ to $$v_1$$, $$m+1$$ to $$v_2$$, and all other indices unchanged. Given an infinite parallel substitution $$\sigma$$, which is just a function from natural numbers to expressions, the "double up" operator $$\upup$$ applied to $$\sigma$$ yields a new substitution with the indices shifted up by two. For example, this can written as a fairly short inductive definition in languages like OCaml or Gallina:

```ocaml
let rec upup (sigma : nat -> expr) =
  function
  | 0 -> Var 0
  | S 0 -> Var 1
  | S (S n') -> sigma n'
```

We call it "double up" because it is nothing more than applying the conventional $$\Uparrow$$ twice.

Now, applying substitutions to expressions is very straightforward. Since this is CBV and not full reduction, we don't need to shift open indices:
$$
\begin{align*}
n[\sigma] &\triangleq \sigma(n)\\
(\lambda.~e)[\sigma] &\triangleq \lambda.~(e[\upup\sigma])\\
(e_1~e_2)[\sigma] &\triangleq (e_1[\sigma])~(e_2[\sigma])
\end{align*}
$$

For example, the OCaml recursive function `let rec f x = f x` can be expressed in our calculus as $$\lambda.~1 ~0$$. For a sanity check, let's try to $$\beta$$-reduce the expression with some argument:

$$
\begin{align*}
&(\lambda.~1 ~0)~v \\
\step &\substt{(1~0)}{0}{v}{1}{(\lambda.~1 ~0)}\\
= &(\substt{1}{0}{v}{1}{(\lambda.~1 ~0)})~(\substt{0}{0}{v}{1}{(\lambda.~1 ~0)})\\
= &(\lambda.~1 ~0)~v
\end{align*}
$$

Note that since introducing a binder increments the indices by $$2$$, the function $$\lambda f.~\lambda x.~(f~x)$$ (which is *not* recursive) in regular lambda calculus is represented as $$\lambda.~\lambda.~(2~0)$$ in our formulation.