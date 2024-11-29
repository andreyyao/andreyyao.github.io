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
$$

  What do Cantor's diagonal argument and the Y combinator from the $\lambda$-calculus have in common? It turns out that they, along with many other interesting mathematical results, are all closely related to the concepts of fixpoints. Given a mapping from some object to itself, the elements that stay the same after applying the mapping are called the *fixpoints* of the mapping. There have been rich investigations of fixpoints in various settings by both mathematicians and programming language researchers. Today we will delve into some examples and theorems related to fixpoints. We will see that many of them share a common abstract structure, and that the framework of reasoning about fixpoints is powerful enough for many other interesting results to be reduced to it.

## A simple example
Whenever I encounter a new mathematical concept, I always try to apply it to simple constructs like finite sets to try to gain some intuition. For example, for some finite set $X$ is there something interesting about the fixpoints of self-maps on $X$? For simplicity, we will only look at bijective self-maps on $X$. The set of all bijections on $X$ form a *group* called the symmetric group $\sym(X)$