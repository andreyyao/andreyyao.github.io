---
title: Everything about fixpoints
pubDatetime: 2024-11-28T12:00:00Z
modDatetime: 2024-11-28T12:00:00Z
description: A exhibition of fixpoints found in the Wild West of programming language theory and mathematics
tags:
  - category theory
  - topology
  - pl
---

$$
\gdef\sym{\operatorname{Sym}}
\gdef\alt{\;|\;}
$$

  What do Cantor's diagonal argument and the Y combinator have in common? It turns out that they, along with many other interesting mathematical results, are all closely related to the concept of fixpoints. Given a mapping from some object to itself, the elements that stay the same after applying the mapping are called the *fixpoints* of the mapping. There have been rich investigations of fixpoints in various settings by both mathematicians and programming language researchers. Today we will delve into some examples and theorems related to fixpoints. We will see that many of them share a common abstract structure, and that the framework of reasoning about fixpoints is powerful enough for many other interesting results to be reduced to it.

## We'll be countin' stars (fixpoints)

There are many results about counting the number of fixpoints.

### Orbits and fixpoints
Whenever I encounter a new mathematical concept, I always try to apply it to simple constructs like finite sets to try to gain some intuition. For example, for some finite set $X$ is there something interesting about the fixpoints of self-maps on $X$?

A natural setting of considering bijections on a set is via *group actions*. A group action of some group $G$ on $X$ is a (heterogenous) binary operation $\star$ satisfying $(gh)\star x=g\star (h\star x)$ for all $g,h\in G$ and $x\in X$. The set of all bijections on $X$ form the symmetric group $\sym(X)$. A group action can then also be viewed as a homomorphism $\varphi: G\to\sym(X)$. For example, $\sym(X)$ acts on $X$ in the obvious way.

For any $x\in X$, the *orbit* of $x$ under the group action is the set $\{g\star x \alt g\in G\}$. It is the set of elements reachable by multiplying by a group element. It is easy to verify that the set of orbits partition $X$, i.e. they are equivalence classes. For any $g\in G$, we can also consider the set of fixpoints under $g$, $X^g\triangleq \{x \alt g\star x = x\}$. Then, we have the following theorem:

**Theorem (Burnside's Lemma):**
$$\displaystyle\#\text{orbits} = \frac{1}{|G|}\sum_{g\in G}|X^g|$$

The theorem says that to figure out the number of orbits, it suffices to average out the number of fixpoints for each group element. Intuitive but also surprising when you think about it more!

## Fixpoint combinators
The (untyped) $\lambda$-calculus is a simple yet elegant formal system. Being a universal model of computation, it needs to be able to express recursion and nontermination.

The canonical example of nontermination in the $\lambda$-calculus is the $\omega$ combinator $(\lambda x.~xx)(\lambda x.~xx)$. It is the smallest example of a term that doesn't eventually reduce to a normal form, precisely because it stays fixed after each transition step. One could say it is a "fixpoint" with respect to the transition relation.

To represent recursion, something a little more complex then $\omega$ is needed. Enter the *fixpoint combinators*, which are terms $T$ satisfying that for every term $f$, $f(Tf)$ is $\beta$-equivalent to $Tf$. In other words, $Tf$ is a fixpoint of $f$. The most famous example is the Y combinator:

$$
Y \triangleq \lambda f.~(\lambda x.~f(xx))(\lambda x.~f(xx))
$$

Taking any term $f$, we can check that
$$
\begin{aligned}
Yf
&= (\lambda f.~(\lambda x.~f(xx))(\lambda x.~f(xx)))f\\
&\equiv_\beta (\lambda x.~f(xx))(\lambda x.~f(xx))\\
&\equiv_\beta f(\lambda x.~f(xx))(\lambda x.~f(xx))\\
&= f(Yf)
\end{aligned}
$$

implementing recursion using $Y$ is now possible with some extra steps. For example, to write the fibonacci function $\texttt{fib}$ which satisfies $\texttt{fib}(n+2)=\texttt{fib}(n)+\texttt{fib}(n+1)$, we can define an auxilliary function $\texttt{fib}'\triangleq \lambda f.~\lambda n.~\texttt{if}~n > 1~\texttt{then}~f (n-1) + f (n-2)~\texttt{else}~\dots$, and then define $\texttt{fib} \triangleq Y\texttt{fib}'$.

There are other fixpoint combinators out there. For example, this monstrosity $Y_k$ is a fixpoint combinator:
$$
L \triangleq \lambda 𝑎𝑏𝑐𝑑𝑒𝑓𝑔ℎ𝑖𝑗𝑘𝑙𝑚𝑛𝑜𝑝𝑞𝑠𝑡𝑢𝑣𝑤𝑥𝑦𝑧𝑟. (𝑟 (𝑡 ℎ 𝑖 𝑠 𝑖 𝑠 𝑎 𝑓 𝑖 𝑥 𝑒 𝑑 𝑝 𝑜 𝑖 𝑛 𝑡 𝑐 𝑜 𝑚 𝑏 𝑖 𝑛 𝑎 𝑡 𝑜 𝑟))
$$
$$
Y_k \triangleq L L L L L L L L L L L L L L L L L L L L L L L L L L
$$

## Fixpoints of monotone functions


# References
- https://www.cs.cornell.edu/courses/cs4110/2021fa/lectures/lecture16.pdf