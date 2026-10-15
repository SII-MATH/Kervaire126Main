module

public import KIP126.Literature.Standard.Sphere.Algebra.Data
public import KIP126.Def.ClassicalAdams.SphereAlgebra.Proofs

@[expose] public section

namespace KIP126.Classical.Adams.Sphere.Internal

open KIP126.Algebra
noncomputable section
set_option maxRecDepth 10000

theorem actualE2Product_apply (p q : ℕ × ℕ) (x : ActualE2At p) (y : ActualE2At q) :
    actualE2Product p q x y =
      product standardFoundation.hf2 standardMilnorCooperations
        (s := p.1) (t := p.2) (s' := q.1) (t' := q.2) x y :=
  KIP126.Classical.Adams.Sphere.Algebra.actualE2Product_apply KIP126.Def.standardHF2AdamsContext p q x y

attribute [local irreducible]
  KIP126.Classical.Adams.Sphere.Algebra.ActualE2At
  KIP126.Classical.Adams.Sphere.Algebra.actualE2AtModule
  KIP126.Classical.Adams.Sphere.Algebra.actualE2Product

theorem actualE2_smul_mul (r : F2) (a b : GradedMonoid ActualE2At) :
    (r • a) * b = r • (a * b) :=
  KIP126.Classical.Adams.Sphere.Algebra.actualE2_smul_mul KIP126.Def.standardHF2AdamsContext r a b

theorem embed_injective (p : ℕ × ℕ) : Function.Injective (embed p) :=
  KIP126.Classical.Adams.Sphere.Algebra.embed_injective KIP126.Def.standardHF2AdamsContext p

theorem embed_product (p q : ℕ × ℕ) (x : ActualE2At p) (y : ActualE2At q) :
    embed (p + q) (actualE2Product p q x y) = embed p x * embed q y :=
  KIP126.Classical.Adams.Sphere.Algebra.embed_product KIP126.Def.standardHF2AdamsContext p q x y

theorem embed_unit : embed 0 actualE2Unit = (1 : ActualE2Total) :=
  KIP126.Classical.Adams.Sphere.Algebra.embed_unit KIP126.Def.standardHF2AdamsContext

end
end KIP126.Classical.Adams.Sphere.Internal
