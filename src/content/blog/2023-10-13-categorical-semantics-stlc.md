---
title: Categorical Semantics of Simply Typed Lambda Calculus
pubDatetime: 2023-10-13T11:12:00Z
description: The Curry-Howard-Lambek correspondence
tags:
  - category
  - pl
---
$$
\gdef\TUnit{\texttt{Unit}}
\gdef\fst{\texttt{fst}}
\gdef\snd{\texttt{snd}}
$$

# Introduction
Programs are complicated. How do we develop a better understanding of how they work? _Denotational semantics_ is the subarea of programming languages where people study the behaviors of programs by mapping them into some _semantic domain_ of mathematical objects.

The [_lambda calculus_](https://www.cs.cornell.edu/courses/cs6110/2023sp/lectures/lec02.pdf) is one of the simplest programming languages there is. Written in Backus-Naur form (BNF), it only has three kinds of expressions:

$$
e\;:=\;x\;|\;\lambda x.e\;|\;e_1\;e_2
$$

which stands for variable, function abstraction, and function application. Despite its simplicity, the lambda calculus is Turing-complete, and in particular can represent infinite loops. There has been interesting work in giving semantics to the lambda calculus via _domain theory_, but that's the topic for another day.

## Computational trilogy
We will focus our attention on [simply typed lambda calculus](https://en.wikipedia.org/wiki/Simply_typed_lambda_calculus)(STLC). STLC adds types to the (pure) lambda calculus. As a programming language, STLC is _strongly normalizing_, meaning that every well-typed term will eventually evaluate to a normal form. That shouldn't be discouraging, since STLC is closely connected to intuitionistic logic, via the _Curry-Howard correspondence_. It turns out that logic and type systems are both connected to _category theory_ via the so-called _Curry-Howard-Lambek_ correspondence.


The goal of this post is to explicitly spell out a categorical semantics of STLC. I was unable to find proofs for the following table taken from this [nlab page](https://ncatlab.org/nlab/show/computational+trilogy) on "computational trilogy", so I figured it will be a fun exercise to spell them out here.

| logic                | type theory             | category theory                   |
|:--------------------:|:-----------------------:|:---------------------------------:|
| propositions         | types                   | objects                           |
| proofs               | terms                   | /                                 |
| impl-intro           | $$\lambda$$ abstraction | counit from tensor-hom adjunction |
| impl-elim            | application             | unit from tensor-hom adjunction   |
| cut elimination      | $$\beta$$ reduction     | zigzag identities                 |
| identity elimination | $$\eta$$ conversion     | other zigzag                      |

# Categorical semantics

Some of the following definitions are adapted from Benjamin Pierce's _Basic Category for Computer Scientists_.

## The type theory

We define the grammar for types in STLC:

$$
A\;:=\;\TUnit\;|\;A\to B\;|\;A\;\times\;B
$$

And the grammar for terms:

$$
e\;:=\;\texttt{unit}\;|\;\lambda x:\tau.e\;|\;e_1\;e_2\;|\;(e_1,e_2)\;|\;\fst\;e\;|\;\snd\;e
$$

Here, $$\TUnit$$ is the type with one element $$\texttt{unit}$$. we also consider the following typing rules:

$$
\infer{Axiom}{\;}{\Gamma,x:A\vdash x:A}
\quad
\infer{Weaken}{\Gamma\vdash e:A}{\Gamma,y:B\vdash e:A}
\quad
\infer{Unit-I}{\;}{\Gamma\vdash\texttt{unit}:\TUnit}
$$

$$
\infer{Arrow-I}{\Gamma, x:A\vdash e:B}{\Gamma\vdash\lambda x:A. e:A\to B}
\quad
\infer{Arrow-E}{\Gamma\vdash f:A\to B \quad \Gamma\vdash e:A}{\Gamma\vdash f\;e:B}
$$

$$
\infer{Prod-I}{\Gamma\vdash e_1:A \quad \Gamma\vdash e_2:B}{\Gamma\vdash (e_1,e_2):A\times B}
\quad
\infer{Prod-E1}{\Gamma\vdash e:A\times B}{\Gamma\vdash \fst~e:A}
\quad
\infer{Prod-E2}{\Gamma\vdash e:A\times B}{\Gamma\vdash \snd~e:B}
$$

Here, the -I and -E refer to _introduction rules_ and _elimination rules_. Introduction rules describe how to produce terms of a certain type, whereas elimination rules corresponds to how to consume terms of a certain type. We call the syntax associated with them _introduction forms_ and _elimination forms_. For example, $$\lambda x: A.~e$$ and $$(e_1,e_2)$$ are introduction forms, whereas $$e_1~e_2$$, or say $$\fst~e$$, are elimination forms.


## A Cartesian-closed category

For the other piece of the translation, we fix any Cartesian-closed category (CCC) $$\mathbf{C}$$. Recall that a Cartesian-closed category is a category with finite products, such that for each object $$A$$, the _right product functor_ $$(-\times A):\mathbf{C}\to\mathbf{C}$$ has a right adjoint $$(-^A):\mathbf{C}\to\mathbf{C}$$ called the _exponential_.

The definition of adjunctions come with a unit natural transformation $$\epsilon_A:(-^A\times A)\to \text{Id}_\mathbf{C}$$ and a counit natural transformation $$\eta_A:\text{Id}_\mathbf{C}\to (-\times A)^A$$ such that the following "zigzag" equalities hold:

$$
\begin{equation}\mathcal{Id}_{(-\times A)}=\epsilon_A (-\times A)\circ (-\times A)\eta_A\end{equation}
$$

$$
\begin{equation}\mathcal{Id}_{(-^A)}=(-^A)\epsilon_A\circ \eta_A (-^A)\end{equation}
$$

Here $$\text{Id}_\mathbf{C}$$ is the identity functor on $$\mathbf{C}$$, and the caligraphic $$\mathcal{Id}$$ denotes identity natural transformations on the respective functors.

An alternative formulation of the unit equation is useful as follows. For each object $$B\in\mathbf{C}$$, the component $$\epsilon_{A,B}$$ of the unit $$\epsilon_A$$ has the universal property such that, for any $$C\in\mathbf{C}$$ and morphism $$f$$ from $$(\underline{C}\times A)$$ (the product functor applied to $$C$$) to $$B$$, there exists a unique morphism $$curry(f)$$ from $$C$$ to $$B^A$$ (the exponential functor applied to $$B$$) making the diagram commute:
<div align="center">
<!-- https://q.uiver.app/#q=WzAsMyxbMCwwLCJcXHVuZGVybGluZXtDfVxcdGltZXMgQSJdLFswLDIsIkJeQVxcdGltZXMgQSJdLFsyLDIsIkIiXSxbMSwyLCJcXGVwc2lsb25fe0EsQn0iLDJdLFswLDEsIlxcZXhpc3RzIVxcO2N1cnJ5KGYpXFx0aW1lcyBcXHRleHR7aWR9X0EiLDEseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJkYXNoZWQifX19XSxbMCwyLCJmIl1d -->
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsMyxbMCwwLCJcXHVuZGVybGluZXtDfVxcdGltZXMgQSJdLFswLDIsIkJeQVxcdGltZXMgQSJdLFsyLDIsIkIiXSxbMSwyLCJcXGVwc2lsb25fe0EsQn0iLDJdLFswLDEsIlxcZXhpc3RzIVxcO2N1cnJ5KGYpXFx0aW1lcyBcXHRleHR7aWR9X0EiLDEseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJkYXNoZWQifX19XSxbMCwyLCJmIl1d&embed" width="420" height="400" style="border-radius: 8px; border: none;"></iframe>
</div>

<!-- Dually, for each object $$C\in\mathbf{C}$$, the component $$\eta_{A,C}$$ of the counit has the universal property that for any $$B\in\mathbf{C}$$ and morphism $$g$$ from $$C$$ to $$\underline{B}^A$$, there exists a unique morphism $$uncurry(g)$$ such that $$(uncurry(g))^A\circ\eta_{A,C}=g$$ -->

## The translation
We are finally ready to define the semantic translation! The double brackets $$\llbracket \;\rrbracket $$ takes something from the type theory and maps it into the CCC we specified. On types, it is defined inductive on the syntax and maps each type to an object in the CCC. Again, the following translations are taken from Pierce's _Basic Category for Computer Scientists_:

$$
\begin{align*}
\llbracket \TUnit\rrbracket &\triangleq 1_\mathbf{C}\\
\llbracket A\times B\rrbracket &\triangleq \llbracket A\rrbracket  \times \llbracket B\rrbracket \\
\llbracket A\to B\rrbracket &\triangleq \llbracket B\rrbracket ^{\llbracket A\rrbracket }
\end{align*}
$$

The translation for the typing context is inductively defined on the number of variables: $$\llbracket \varnothing\rrbracket \triangleq 1_\mathbf{C}$$ and $$\llbracket \Gamma,x:A\rrbracket \triangleq \llbracket \Gamma\rrbracket \times \llbracket A\rrbracket $$.

Finally, we inductively define the translation on the typing derivations:

| Derivation                                           | Translation                                                                                     | Domain                            | Target                            |
|------------------------------------------------------|-------------------------------------------------------------------------------------------------|-----------------------------------|-----------------------------------|
| $$\llbracket \Gamma\vdash \texttt{unit}:\TUnit\rrbracket $$ | $$!_{\llbracket \Gamma\rrbracket }$$                                                                          | $$\llbracket \Gamma\rrbracket $$                | $$1_\mathbf{C}$$                  |
| $$\llbracket \Gamma,x:A\vdash x:A\rrbracket $$                     | $$\pi_2$$                                                                                       | $$\llbracket \Gamma\rrbracket \times\llbracket A\rrbracket $$ | $$\llbracket A\rrbracket $$                     |
| $$\llbracket \Gamma,y:B\vdash e:A\rrbracket $$                     | $$\llbracket \Gamma\vdash e:A\rrbracket \circ\pi_1$$                                                          | $$\llbracket \Gamma\rrbracket \times\llbracket A\rrbracket $$ | $$\llbracket B\rrbracket $$                     |
| $$\llbracket \Gamma\vdash \lambda x:A.e:A\to B\rrbracket $$        | $$curry(\llbracket \Gamma,x:A\vdash e:B\rrbracket )$$                                                         | $$\llbracket \Gamma\rrbracket $$                | $$\llbracket B\rrbracket ^{\llbracket A\rrbracket }$$         |
| $$\llbracket \Gamma\vdash e_1\;e_2:B\rrbracket $$                  | $$\epsilon_{A,B}\circ\langle\llbracket \Gamma\vdash e_1:A\to B\rrbracket ,\llbracket \Gamma\vdash e_2:A\rrbracket \rangle$$ | $$\llbracket \Gamma\rrbracket $$                | $$\llbracket B\rrbracket $$                     |
| $$\llbracket \Gamma\vdash (e_1,e_2):A\times B\rrbracket $$         | $$\langle\llbracket \Gamma\vdash e_1:A\rrbracket ,\llbracket \Gamma\vdash e_2:B\rrbracket \rangle$$                         | $$\llbracket \Gamma\rrbracket $$                | $$\llbracket A\rrbracket \times\llbracket B\rrbracket $$ |
| $$\llbracket \Gamma\vdash \fst\;e:A\rrbracket $$           | $$\pi_1\circ \llbracket \Gamma\vdash e:A\times B\rrbracket $$                                         | $$\llbracket \Gamma\rrbracket $$                | $$\llbracket A\rrbracket $$                     |
| $$\llbracket \Gamma\vdash \snd\;e:B\rrbracket $$           | $$\pi_2\circ \llbracket \Gamma\vdash e:A\times B\rrbracket $$                                         | $$\llbracket \Gamma\rrbracket $$                | $$\llbracket B\rrbracket $$                     |

For this particular formulation of STLC, it just so happens that for any fixed context, if a term is typeable then there is a unique typing rule that applies to it. This can be seen just from the fact that each term grammar branch appears in the conclusion of exactly one typing rule. Thus, we can be a little hand-wavy and define the translations on the term syntax directly.

# Semantics respects equivalence

## $$\eta$$-equivalence
The $$\eta$$-equivalence for function types says that for whatever types $$A,B$$, a function $$h:A\to B$$ should be considered "the same" as $$\lambda x:A.~(h~x)$$. Indeed, the latter seems to be just "$$h$$ with extra steps". It is an instance of a more general idea called _contextual equivalence_, or even more abstractly, _extensional equivalence_. In short, it means that things are identified by "extension", i.e. how they act from the outside perspective.

One might notice that $$\lambda x:A. (h\;x)$$ is an introduction form immediately wrapped around an elimination form, both for arrow types. In general, $$\eta$$-equivalences almost all look like this.

### $$\eta$$-equivalence for product types
This amounts to claiming that $$\semant{\Gamma\vdash (\fst~e, \snd~e): A\times B}=\semant{\Gamma \vdash e:A\times B}$$, which follows immediately from the universal property of the product:
<div align="center">
<!-- https://q.uiver.app/#q=WzAsNCxbMiwwLCJcXGxsYnJhY2tldCBcXEdhbW1hIFxccnJicmFja2V0Il0sWzIsMiwiXFxsbGJyYWNrZXQgQVxccnJicmFja2V0IFxcdGltZXMgXFxsbGJyYWNrZXQgQlxccnJicmFja2V0Il0sWzAsMiwiXFxsbGJyYWNrZXQgQVxccnJicmFja2V0Il0sWzQsMiwiXFxsbGJyYWNrZXQgQlxccnJicmFja2V0ICJdLFswLDEsImYiLDFdLFsxLDIsIlxccGlfMSJdLFsxLDMsIlxccGlfMiIsMl0sWzAsMiwiZ18xIiwyXSxbMCwzLCJnXzIiXV0= -->
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsNCxbMiwwLCJcXGxsYnJhY2tldCBcXEdhbW1hIFxccnJicmFja2V0Il0sWzIsMiwiXFxsbGJyYWNrZXQgQVxccnJicmFja2V0IFxcdGltZXMgXFxsbGJyYWNrZXQgQlxccnJicmFja2V0Il0sWzAsMiwiXFxsbGJyYWNrZXQgQVxccnJicmFja2V0Il0sWzQsMiwiXFxsbGJyYWNrZXQgQlxccnJicmFja2V0ICJdLFswLDEsImYiLDFdLFsxLDIsIlxccGlfMSJdLFsxLDMsIlxccGlfMiIsMl0sWzAsMiwiZ18xIiwyXSxbMCwzLCJnXzIiXV0==&embed" width="759" height="432" style="border-radius: 8px; border: none;"></iframe>
</div>

### $$\eta$$-equivalence for arrow types
Suppose $$\Gamma\vdash \lambda x:A.e\;x:A\to B$$. Then $$e$$ must be of type $$A\to B$$, but it doesn't have to be in normal form. The semantics of the typing derivations defined earlier tells us

$$
\begin{align*}
&\llbracket \Gamma\vdash \lambda x:A.e\;x:A\to B\rrbracket \\
=&curry(\llbracket \Gamma,x:A \vdash e\;x:B\rrbracket )\\
=&curry(\epsilon_{A,B}\circ \langle\llbracket \Gamma,x:A\vdash e:A\to B\rrbracket ,\llbracket \Gamma,x:A\vdash x:A\rrbracket \rangle)\\
=&curry(\epsilon_{A,B}\circ \langle\llbracket \Gamma,x:A\vdash e:A\to B\rrbracket ,\pi_2\rangle)\\
=&curry(\epsilon_{A,B}\circ \langle\llbracket \Gamma\vdash e:A\to B\rrbracket \circ\pi_1,\pi_2\rangle)
\end{align*}
$$

Tho a mouthful, $$\epsilon_{A,B}\circ\langle\llbracket \Gamma\vdash e:A\to B\rrbracket \circ\pi_1,\pi_2\rangle$$ is a morphism from $$\llbracket \Gamma\rrbracket \times \llbracket A\rrbracket $$ to $$\llbracket B\rrbracket $$. If we set $$C$$ to be $$\llbracket \Gamma\rrbracket $$, and $$f$$ as $$\epsilon_{A,B}\circ\langle\llbracket \Gamma\vdash e:A\to B\rrbracket \circ\pi_1,\pi_2\rangle$$, then the diagram for the unit equation becomes

<div align="center">
<!-- https://q.uiver.app/#q=WzAsMyxbMCwwLCJbXFwhW1xcR2FtbWFdXFwhXVxcdGltZXMgW1xcIVtBXVxcIV0iXSxbMCwyLCJbXFwhW0JdXFwhXV57W1xcIVtBXVxcIV19XFx0aW1lcyBbXFwhW0FdXFwhXSJdLFsyLDIsIltcXCFbQl1cXCFdIl0sWzEsMiwiXFxlcHNpbG9uX3tBLEJ9IiwyXSxbMCwxLCJnIiwxLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZGFzaGVkIn19fV0sWzAsMiwiZiJdXQ== -->
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsMyxbMCwwLCJbXFwhW1xcR2FtbWFdXFwhXVxcdGltZXMgW1xcIVtBXVxcIV0iXSxbMCwyLCJbXFwhW0JdXFwhXV57W1xcIVtBXVxcIV19XFx0aW1lcyBbXFwhW0FdXFwhXSJdLFsyLDIsIltcXCFbQl1cXCFdIl0sWzEsMiwiXFxlcHNpbG9uX3tBLEJ9IiwyXSxbMCwxLCJnIiwxLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZGFzaGVkIn19fV0sWzAsMiwiZiJdXQ==&embed" width="400" height="400" style="border-radius: 8px; border: none;"></iframe>
</div>

Where did the mystery $$g$$ come from? Well, since $$f$$ is of the form $$\epsilon_{A,B}$$ composed with _something_, we can just define $$g$$ to be the _something_, aka $$\langle\llbracket \Gamma\vdash e:A\to B\rrbracket \circ\pi_1,\pi_2\rangle$$, and the above diagram will trivially commute. But, note $$g$$ is actually equal to $$\llbracket \Gamma\vdash e:A\to B\rrbracket \times \text{id}_{\llbracket A\rrbracket }$$.

Finally, for the real kicker, we invoke the uniqueness of $$curry$$ in the universal property of $$\epsilon_A$$, so that $$\llbracket \Gamma\vdash e:A\to B\rrbracket =curry(\epsilon_{A,B}\circ \langle\llbracket \Gamma\vdash e:A\to B\rrbracket \circ\pi_1,\pi_2\rangle)$$. Thus,

$$
\llbracket \Gamma\vdash \lambda x:A.e\;x:A\to B\rrbracket =\llbracket \Gamma\vdash e:A\to B\rrbracket
$$

# Conclusion
This was mostly just an exercise for me to make sure that the categorical semantics of STLC is sensible. Indeed, we have verified parts of the analogy from the nlab "computational trilogy" table, that the semantic respects $$\beta$$ and $$\eta$$ equivalence. Actually, the proof came down exactly to the unit and counit equations, just as in the table.

Note that our version of STLC doesn't contain any "ground types" besides $$\TUnit$$. One can simply add more ground types like $$\texttt{Int}, \texttt{Bool}, \texttt{Number}$$, etc. The translation will then be incorporated to map each ground type to some designated object in our CCC, and the proof still works because it was defined inductively on the typing derivations. However, in this way the categorical semantics will not be able to enforce fine-grained equational constraints like `40 + 2 = 42` on the operational semantics.

# References
1. B. C. Pierce, Basic Category Theory for Computer Scientists. The MIT Press, 1991. doi: 10.7551/mitpress/1524.001.0001.
2. S. Mac Lane, Categories for the Working Mathematician, vol. 5. in Graduate Texts in Mathematics, vol. 5. New York, NY: Springer, 1978. doi: 10.1007/978-1-4757-4721-8.
3. https://ncatlab.org/nlab/show/computational+trilogy