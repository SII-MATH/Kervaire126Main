module

public import KIP126.Def.Synthetic.AdamsFiltration.Convergence.Data

@[expose] public section

/-! Detection on one synthetic Adams family. All indeterminacy is retained:
there must be a common infinite-cycle representative and equality only in
the associated graded of the actual νHF₂ tower filtration. -/
namespace KIP126.Synthetic.SpectralSequence
open CategoryTheory KIP126.SpectralSequence
open KIP126.StableHomotopy KIP126.Synthetic.Context
universe u v
variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  [HasFunctorialCofiber (C := Syn)]

/-- A finite-page class represents this E∞ class. Zero is allowed. -/
def HasInfinityRepresentative (A : SyntheticAdamsSS.{v}) (r : ℤ) (i : Tridegree)
    (x : A.Page r i) (e : (A.sequence.ssData i).eInfty) : Prop :=
  2 ≤ r ∧ ∃ z : (Subobject.underlying.obj ((A.sequence.ssData i).Z ⊤) : ModuleCat ℤ),
    (Subobject.ofLE _ _ ((A.sequence.ssData i).Z_anti le_top) ≫
      (A.sequence.ssData i).pageπ (↑(r - 2).toNat : WithTop ℕ)) z = x ∧
      (A.sequence.ssData i).pageπ ⊤ z = e

/-- Associated-graded detection, allowing a zero leading class. This weaker
relation is needed for the paper's C₅ convention (Remark 7.12). -/
def Detects {H : Syn} {unit : S_0_0 ⟶ H} {F : SyntheticAdamsFamily Syn} {X : Syn}
    (c : TowerConvergence unit F X) (i : Tridegree) (x : (F.obj X).E₂ i)
    (α : BiHom (i.2.1 - i.1) i.2.2 X) : Prop :=
  ∃ e : ((F.obj X).sequence.ssData i).eInfty,
    HasInfinityRepresentative (F.obj X) 2 i x e ∧
    ∃ a : (Subobject.underlying.obj
      ((towerFiltration unit X).F i.1 (i.2.1 - i.1, i.2.2)) : ModuleCat ℤ),
      ((towerFiltration unit X).F i.1 (i.2.1 - i.1, i.2.2)).arrow a = α ∧
      (c.identification i).hom e =
        (towerFiltration unit X).toAssociatedGraded i.1 (i.2.1 - i.1, i.2.2) a

/-- Exact filtration: detection together with nonzero associated-graded
class. Nonzero E₂ alone would not suffice. -/
def DetectsNonzero {H : Syn} {unit : S_0_0 ⟶ H} {F : SyntheticAdamsFamily Syn} {X : Syn}
    (c : TowerConvergence unit F X) (i : Tridegree) (x : (F.obj X).E₂ i)
    (α : BiHom (i.2.1 - i.1) i.2.2 X) : Prop :=
  Detects c i x α ∧
    ∃ e : ((F.obj X).sequence.ssData i).eInfty,
      HasInfinityRepresentative (F.obj X) 2 i x e ∧ e ≠ 0

/-- Filtration bounds for the actual homotopy class, including zero. -/
def FiltrationAtLeast {H : Syn} (unit : S_0_0 ⟶ H) {X : Syn}
    (s : ℤ) {m w : ℤ} (α : BiHom m w X) : Prop :=
  α ∈ towerFiltrationSubmodule unit X s (m, w)
end KIP126.Synthetic.SpectralSequence
