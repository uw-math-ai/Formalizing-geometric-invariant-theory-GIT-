# Reynolds Operator Existence (Part 1)

This file proves that if a linearly reductive group acts on a finite-dimensional
k-module, then a Reynolds operator exists for any G-stable submodule.

We work in the setting of a representation ρ : G → GL(V), where V is a
finite-dimensional module over a field k.

First, we define a G-stable submodule: a submodule W ⊆ V is G-stable if it is
preserved by the group action.

We then define a linearly reductive group as one for which every G-stable
submodule of a finite-dimensional representation admits a G-stable complement.
That is, for any such W, there exists W' such that V = W ⊕ W' and W' is also
G-stable.

Next, we define a Reynolds operator onto a submodule W to be a k-linear map
R : V → V satisfying:
- R(v) ∈ W for all v,
- R acts as the identity on W,
- R commutes with the group action (i.e., R(ρ(g)v) = ρ(g)(R(v))).

Using the linear reductivity assumption, we construct a Reynolds operator by
projecting onto W along a G-stable complement W'. The projection map is shown
to satisfy all required properties, including G-equivariance.

This establishes the existence of a Reynolds operator for any G-stable
submodule of a finite-dimensional representation of a linearly reductive group.