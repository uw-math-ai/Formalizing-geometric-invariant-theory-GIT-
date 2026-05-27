# Propositions

## tensor_invariants_iso — Exercise 7.5.1 (a)

Let $G$ be a linearly reductive group acting on an affine $\mathbb{k}$-scheme $\text{Spec } A$. Let $N$ be an $A^G$-module. Then the natural map $N \to (N \otimes_{A^G} A)^G$ is an isomorphism.

**Proof.**

Since $G$ is linearly reductive, there exists a Reynolds operator $R : A \to A^G$, which is $A^G$-linear and satisfies $R|_{A^G} = \mathrm{id}$.

The natural map $\varphi : N \to (N \otimes_{A^G} A)^G$ is given by $n \mapsto n \otimes 1$.

We construct an inverse.

Define

$$\psi : N \otimes_{A^G} A \to N, \qquad n \otimes f \mapsto R(f) \cdot n.$$

This is well-defined: for $\lambda \in A^G$,

$$\psi(n\lambda \otimes f) = R(f) \cdot n\lambda = R(\lambda f) \cdot n = \psi(n \otimes \lambda f),$$

using $A^G$-linearity of $R$. Since $R(f) \in A^G$ and $N$ is an $A^G$-module, $\psi$ lands in $N$.

We check the two compositions:

- $\psi \circ \varphi$ : $n \mapsto n \otimes 1 \mapsto R(1) \cdot n = n$, since $1 \in A^G$ and $R|_{A^G} = \mathrm{id}$. ✓

- $\varphi \circ \psi$ on $(N \otimes_{A^G} A)^G$ : take an invariant element $x = \sum_i n_i \otimes f_i$. Its image under $\psi$ is $m := \sum_i R(f_i)n_i$, and

$$\varphi(m) = \sum_i n_i \otimes R(f_i).$$

Since $x$ is $G$-invariant, applying the Reynolds operator on the $A$-factor replaces each $f_i$ by its invariant part $R(f_i)$ without changing the tensor, so

$$\sum_i n_i \otimes f_i = \sum_i n_i \otimes R(f_i) = \varphi(\psi(x)).$$

Thus $\varphi$ and $\psi$ are inverse maps, so

$$N \cong (N \otimes_{A^G} A)^G.$$

$\blacksquare$

---

## pi_surjective — Exercise 7.5.1 (b)

Let $G$ be a linearly reductive group acting on an affine $\mathbb{k}$-scheme $\text{Spec } A$. Then $\pi : \text{Spec } A \to \text{Spec } A^G$ is surjective.

**Proof.**

Let $y \in \text{Spec } A^G$, corresponding to a prime $\mathfrak{p} \subset A^G$, and let $\kappa(y) = (A^G)_\mathfrak{p}/\mathfrak{p}(A^G)_\mathfrak{p}$ be the residue field at $y$.

Apply part (a) to the $A^G$-module $N = \kappa(y)$. This gives an isomorphism

$$\kappa(y) \xrightarrow{\sim} (\kappa(y) \otimes_{A^G} A)^G.$$

In particular,

$$(\kappa(y) \otimes_{A^G} A)^G \cong \kappa(y) \neq 0,$$

so $\kappa(y) \otimes_{A^G} A \neq 0$.

Since $\kappa(y) \otimes_{A^G} A$ is a nonzero ring, it has at least one prime ideal, say $\mathfrak{q}'$. Pulling back along the ring map

$$A \to \kappa(y) \otimes_{A^G} A$$

yields a prime $\mathfrak{q} \subset A$.

The composite

$$A^G \to A \to \kappa(y) \otimes_{A^G} A$$

factors through $\kappa(y)$ and has kernel $\mathfrak{p}$, so

$$\mathfrak{q} \cap A^G = \mathfrak{p}.$$

Thus $\mathfrak{q}$ is a prime of $A$ lying over $y$. Since $y$ was arbitrary, $\pi$ is surjective. $\blacksquare$

---

## V(I)_image_closed — Exercise 7.5.1 (c)

Let $G$ be a linearly reductive group acting on an affine $\mathbb{k}$-scheme $\text{Spec } A$. If $I \subseteq A$ is a $G$-invariant ideal, then the image of $V(I)$ under $\pi$ is closed and equals $V(I^G)$, where $I^G := I \cap A^G$.

**Proof.**

Since $G$ is linearly reductive, there exists a Reynolds operator $R : A \to A^G$, which is $A^G$-linear and satisfies $R|_{A^G} = \mathrm{id}$.

**Step 1: $R(I) = I^G$.**

For any $f \in I$, since $I$ is $G$-invariant we have $g \cdot f \in I$ for all $g \in G$. Because the Reynolds operator preserves $G$-stable submodules, it follows that $R(f) \in I$. Since also $R(f) \in A^G$, we obtain

$$R(I) \subseteq I \cap A^G = I^G.$$

Conversely, for any $f \in I^G$ we have $f \in A^G$, so $R(f) = f$. Since $f \in I$, this gives $f \in R(I)$. Therefore

$$R(I) = I^G.$$

**Step 2: $(A/I)^G \cong A^G/I^G$.**

By Step 1, the Reynolds operator descends to the quotient $A/I$, and the invariant classes in $A/I$ are precisely those coming from invariant elements of $A$. The kernel is exactly $I^G$, so

$$(A/I)^G \cong A^G/I^G.$$

**Step 3: $\pi(V(I)) = V(I^G)$.**

- **($\subseteq$)** If $\mathfrak{q} \in V(I)$, i.e. $I \subseteq \mathfrak{q}$, then

$$I^G = I \cap A^G \subseteq \mathfrak{q} \cap A^G = \pi(\mathfrak{q}),$$

so $\pi(\mathfrak{q}) \in V(I^G)$. Hence

$$\pi(V(I)) \subseteq V(I^G).$$

- **($\supseteq$)** Let $\mathfrak{p} \in V(I^G)$, so $I^G \subseteq \mathfrak{p}$. Apply part (b) to the quotient $A/I$, whose ring of invariants is $A^G/I^G$ by Step 2. The induced map

$$\pi_I : \text{Spec}(A/I) \to \text{Spec}(A^G/I^G)$$

is surjective. The prime $\mathfrak{p}/I^G \in \text{Spec}(A^G/I^G)$ therefore lifts to some $\bar{\mathfrak{q}} \in \text{Spec}(A/I)$, corresponding to a prime $\mathfrak{q} \supseteq I$ in $A$ satisfying

$$\mathfrak{q} \cap A^G = \mathfrak{p}.$$

Hence $\mathfrak{q} \in V(I)$ and $\pi(\mathfrak{q}) = \mathfrak{p}$, so $\mathfrak{p} \in \pi(V(I))$.

Therefore

$$\pi(V(I)) = V(I^G),$$

which is closed in $\text{Spec } A^G$. $\blacksquare$
