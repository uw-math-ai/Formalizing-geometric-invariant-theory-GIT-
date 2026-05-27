# Propositions

## tensor_invariants_iso — Exercise 7.5.1 (a)

Let $G$ be a linearly reductive group acting on an affine $\mathbb{k}$-scheme $\text{Spec } A$.
Let $N$ be an $A^G$-module. Then the natural map $N \to (N \otimes_{A^G} A)^G$ is an isomorphism.

**Proof.**

Since $G$ is linearly reductive, there exists a Reynolds operator $R : A \to A^G$, which is
$A^G$-linear and satisfies $R|_{A^G} = \mathrm{id}$.

The natural map $\varphi : N \to (N \otimes_{A^G} A)^G$ is given by $n \mapsto n \otimes 1$.

We construct an inverse. 

Define

$$\psi : N \otimes_{A^G} A \to N, \qquad n \otimes f \mapsto R(f) \cdot n.$$

This is well-defined: for $\lambda \in A^G$,

$$\psi(n\lambda \otimes f) = R(f) \cdot n\lambda = R(\lambda f) \cdot n = \psi(n \otimes \lambda f),$$

using $A^G$-linearity of $R$. Since $R$ maps onto $A^G$ and $N$ is an $A^G$-module, $\psi$ lands in $N$.

We check the two compositions:

- $\psi \circ \varphi$ : $n \mapsto n \otimes 1 \mapsto R(1) \cdot n = n$. ✓
- $\varphi \circ \psi$ on $(N \otimes_{A^G} A)^G$ : take an invariant element $x = \sum_i n_i \otimes f_i$.
  Its image under $\psi$ is $m := \sum_i R(f_i) n_i$, and $\varphi(m) = m \otimes 1 = \sum_i n_i \otimes R(f_i)$.
  Since $x$ is $G$-invariant, averaging on the $A$-factor replaces each $f_i$ by $R(f_i)$,
  so $\sum_i n_i \otimes f_i = \sum_i n_i \otimes R(f_i) = \varphi(\psi(x))$. ✓

Thus $\varphi$ is an isomorphism. $\blacksquare$

---

## pi_surjective — Exercise 7.5.1 (b)

Let $G$ be a linearly reductive group acting on an affine $\mathbb{k}$-scheme $\text{Spec } A$.
Then $\pi : \text{Spec } A \to \text{Spec } A^G$ is surjective.

**Proof.**

Let $y \in \text{Spec } A^G$, corresponding to a prime $\mathfrak{p} \subset A^G$, and let
$\kappa(y) = (A^G)_\mathfrak{p} / \mathfrak{p}(A^G)_\mathfrak{p}$ be the residue field at $y$.

Apply part (a) to the $A^G$-module $N = \kappa(y)$. This gives an isomorphism

$$\kappa(y) \xrightarrow{\sim} (\kappa(y) \otimes_{A^G} A)^G.$$

In particular $(\kappa(y) \otimes_{A^G} A)^G \cong \kappa(y) \neq 0$, so $\kappa(y) \otimes_{A^G} A \neq 0$.

Since $\kappa(y) \otimes_{A^G} A \neq 0$, it has at least one prime ideal, say $\mathfrak{q}'$.

Pulling back along the ring map $A \to \kappa(y) \otimes_{A^G} A$ yields a prime $\mathfrak{q} \subset A$.

The composite $A^G \to A \to \kappa(y) \otimes_{A^G} A$ factors through $\kappa(y)$ and has kernel $\mathfrak{p}$,
so $\mathfrak{q} \cap A^G = \mathfrak{p}$, i.e. $\mathfrak{q}$ is a prime of $A$ lying over $y$.

Therefore $\pi$ is surjective. $\blacksquare$

*Remark.* This approach via (a) cleanly sidesteps the issue of verifying $\mathfrak{q} \cap A^G = \mathfrak{p}$
by hand: non-vanishing of $\kappa(y) \otimes_{A^G} A$ gives existence of a prime over $\mathfrak{p}$
without needing to track which prime of $A$ is chosen.

---

## V(I)_image_closed — Exercise 7.5.1 (c)

Let $G$ be a linearly reductive group acting on an affine $\mathbb{k}$-scheme $\text{Spec } A$.
If $I \subseteq A$ is a $G$-invariant ideal, then the image of $V(I)$ under $\pi$ is closed
and equals $V(I^G)$, where $I^G := I \cap A^G$.

**Proof.**

Since $G$ is linearly reductive, there exists a Reynolds operator $R : A \to A^G$,
which is $A^G$-linear and satisfies $R|_{A^G} = \mathrm{id}$.

**Step 1: $R(I) = I^G$.**

For any $f \in I$, since $I$ is $G$-invariant we have $g \cdot f \in I$ for all $g \in G$,
and therefore $R(f) \in I$. Since $R(f) \in A^G$ by definition, $R(I) \subseteq I \cap A^G = I^G$.

Conversely, for any $f \in I^G$ we have $R(f) = f$, so $f \in R(I)$.

Thus $R(I) = I^G$.

**Step 2: $(A/I)^G = A^G / I^G$.**

By Step 1, the Reynolds operator descends to a well-defined splitting of $A^G \to A/I$,
and its image is $I^G$, giving $(A/I)^G \cong A^G/I^G$.

**Step 3: $\pi(V(I)) = V(I^G)$.**

- **(⊆)** If $\mathfrak{q} \in V(I)$, i.e. $I \subseteq \mathfrak{q}$, then
  $I^G = I \cap A^G \subseteq \mathfrak{q} \cap A^G = \pi(\mathfrak{q})$,
  so $\pi(\mathfrak{q}) \in V(I^G)$.

- **(⊇)** Let $\mathfrak{p} \in V(I^G)$, so $I^G \subseteq \mathfrak{p}$.
  Apply part (b) to the quotient $A/I$, whose ring of invariants is $A^G/I^G$ by Step 2.
  The induced map $\pi_I : \text{Spec}(A/I) \to \text{Spec}(A^G/I^G)$ is surjective by (b).
  The prime $\mathfrak{p}/I^G \in \text{Spec}(A^G/I^G)$ therefore lifts to some
  $\bar{\mathfrak{q}} \in \text{Spec}(A/I)$, corresponding to a prime $\mathfrak{q} \supset I$ in $A$
  with $\mathfrak{q} \cap A^G = \mathfrak{p}$.
  Hence $\mathfrak{q} \in V(I)$ and $\pi(\mathfrak{q}) = \mathfrak{p}$, so $\mathfrak{p} \in \pi(V(I))$.

Therefore $\pi(V(I)) = V(I^G)$, which is closed in $\text{Spec } A^G$. $\blacksquare$