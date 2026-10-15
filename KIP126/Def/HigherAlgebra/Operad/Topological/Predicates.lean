module

public import KIP126.Def.HigherAlgebra.Operad.Topological.Data
public import Mathlib.Topology.Homotopy.Contractible

@[expose] public section

namespace KIP126.HigherAlgebra.Operad.TopologicalOperad

universe v

/-- Freeness of the actual action of every finite permutation group: a
permutation fixing an operation must be the identity permutation. -/
def SigmaFree (O : TopologicalOperad.{v}) : Prop :=
  ∀ (I : FintypeCat.{0}) (e : I ≃ I) (x : O.Op I),
    O.relabel e x = x → e = Equiv.refl I

/-- The usual contractible, symmetric-group-free topological E∞ convention.
Contractibility is homotopy equivalence to a point, not mere uniqueness of
components or operations in Ho. This is a predicate on all of the actual
operad structure, including its nullary operations. See May, *What precisely
are E∞ ring spaces and E∞ ring spectra?*, Section 1, pp. 224–225:
https://math.uchicago.edu/~may/PAPERS/Final1.pdf. -/
structure IsEInfinity (O : TopologicalOperad.{v}) : Prop where
  contractible : ∀ (I : FintypeCat.{0}), ContractibleSpace (O.Op I)
  sigma_free : O.SigmaFree

/-- The optional reduced convention: exactly one nullary operation. The main
operad and E∞ definitions retain unital non-reduced operads as well. -/
def IsReduced (O : TopologicalOperad.{v}) : Prop :=
  Nonempty (O.Op (FintypeCat.of PEmpty)) ∧
    Subsingleton (O.Op (FintypeCat.of PEmpty))

end KIP126.HigherAlgebra.Operad.TopologicalOperad
