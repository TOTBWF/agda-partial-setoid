Partial Setoids in Agda
=========================

A setoid is some set (or type, in the case of agda), equipped with an
equivalence relation. This is useful in agda, because it allows
us to use a much more interesting notions of equality than
definitional equality, and define things like quotients of types.

Partial Setoids are a generalization of this concept.
Instead of equipping our set/type with an equivalence relation,
we use a _partial_ equivalence relation (equivalence relation w/o reflexivity).

Whereas Setoids let us enrich a type with extra equalities, Partial Setoids
let us take away equalities, opening the door for things like subsets of types.

For example, we define a "subset" of a type as follows. Let `S` be a Partial Setoid
over some type `A` with a Partial Equivalence relationship `≈`. We say some `x : A`
is a member of `S` (or `x ∈ S`) if we can prove that `x ≈ x`.

This library implements Partial Setoids in agda, and proves some interesting properties
of otther structures using these definitions.
