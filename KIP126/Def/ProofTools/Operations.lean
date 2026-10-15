module

public import KIP126.Def.ProofTools.Laws
import all KIP126.Def.ProofTools.ConvergenceOperations
import all KIP126.Def.ProofTools.DetectionOperations
import all KIP126.Def.ProofTools.GeneralizedMahowald.Filtration
import all KIP126.Def.ProofTools.GeneralizedMahowald.SphereLabels
import all KIP126.Def.ProofTools.GeneralizedMahowald.PageCalculus
import all KIP126.Def.ProofTools.GeneralizedMahowald.Coherence
import all KIP126.Def.ProofTools.StretchingRepresentatives
import all KIP126.Def.ProofTools.GeneralizedMahowald.BoundaryLambda

/-! Proven operations used by the paper proofs. These expose selected existing
implementations without adding inputs or proof obligations. -/
namespace KIP126.ProofTools.Operations

public alias rho_infty_injective := Internal.rho_infty_injective
public alias map_preserves_filtration := Internal.map_preserves_filtration
public alias filtration_representative_exists := Internal.filtration_representative_exists
public alias family_page_comp := Internal.family_page_comp
public alias family_infinity_representative_map := Internal.family_infinity_representative_map
public alias detects_reflect := Internal.detects_reflect
public alias finite_bottom_filtration := Internal.Mahowald.finite_bottom_filtration
public alias finite_infinity_zero_outside := Internal.Mahowald.finite_infinity_zero_outside
public alias detects_map := Internal.detects_map
public alias grade_natural := Internal.grade_natural
public alias filtration_iff_of_infinity_zero := Internal.Mahowald.filtration_iff_of_infinity_zero

public alias grade_difference := Internal.grade_difference
public alias initialProjection_eq_cycleLabel := Internal.Mahowald.initialProjection_eq_cycleLabel
public alias represents_zero_mem_boundary := Internal.Mahowald.represents_zero_mem_boundary
public alias boundaries_le_cycles := Internal.Mahowald.boundaries_le_cycles
public alias boundaries_one := Internal.Mahowald.boundaries_one
public alias finite_high_filtration_zero := Internal.Mahowald.finite_high_filtration_zero
public alias sphere_first_quotient_label := Internal.Mahowald.sphere_first_quotient_label
public alias sphere_finite_lambda_detects := Internal.Mahowald.sphere_finite_lambda_detects
public alias susp_invariance_add := Internal.Mahowald.susp_invariance_add
public alias inverse_associativity := Internal.Mahowald.inverse_associativity
public alias shift_hom_associativity := Internal.Mahowald.shift_hom_associativity

public alias next_filtration_of_infinity_injective := Internal.next_filtration_of_infinity_injective
open CategoryTheory KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
universe u v
public noncomputable def biSuspensionIso {Syn : Type u} [SyntheticCategory.{u,v} Syn]
    (q : ℤ) (Q : Syn) : (SyntheticCategory.biShift (1,-q)).obj Q ≅
      ((SyntheticCategory.biShift (0,-q)).obj Q)⟦(1 : ℤ)⟧ :=
  Internal.Mahowald.biSuspensionIso q Q

@[expose] public noncomputable def infinityGradedIso
    {Syn : Type u} [SyntheticCategory.{u,v} Syn]
    [KIP126.StableHomotopy.HasFunctorialCofiber (C := Syn)]
    {H : Syn} {unit : S_0_0 ⟶ H} {F : SyntheticAdamsFamily Syn}
    {P : SyntheticTowerPresentation unit F} {X : Syn}
    (c : SyntheticTowerConvergence P X) (p : ℤ × ℤ) (s : ℤ) :
    ((F.obj X).sequence.ssData (s,p.1+s,p.2)).eInfty ≅
      (P.filtration X).associatedGraded s p :=
  c.identification (s,p.1+s,p.2) ≪≫ eqToIso (by simp)
public theorem tower_extension_iff
    {Syn : Type u} [SyntheticCategory.{u,v} Syn]
    [KIP126.StableHomotopy.HasFunctorialCofiber (C := Syn)]
    {H : Syn} {unit : S_0_0 ⟶ H} {F : SyntheticAdamsFamily Syn}
    {P : SyntheticTowerPresentation unit F} {X Y : Syn} {g : X ⟶ Y}
    {cx : SyntheticTowerConvergence P X} {cy : SyntheticTowerConvergence P Y}
    (M : ConvergentMap F g cx.toConvergence cy.toConvergence)
    (p : ℤ × ℤ) (s n : ℤ)
    (x : ((F.obj X).sequence.ssData (s,p.1+s,p.2)).eInfty)
    (y : ((F.obj Y).sequence.ssData (s+n,p.1+(s+n),p.2)).eInfty) :
    TowerExtensionEquation M p s n x y ↔
      0 ≤ n ∧ ∃ (a : (Subobject.underlying.obj ((P.filtration X).F s p) : ModuleCat.{v} ℤ))
        (b : (Subobject.underlying.obj ((P.filtration Y).F (s+n) p) : ModuleCat.{v} ℤ)),
        ((P.filtration X).F s p).arrow a ≫ g = ((P.filtration Y).F (s+n) p).arrow b ∧
        (P.filtration X).toAssociatedGraded s p a = (infinityGradedIso cx p s).hom x ∧
        (P.filtration Y).toAssociatedGraded (s+n) p b = (infinityGradedIso cy p (s+n)).hom y :=
  Internal.tower_extension_iff M p s n x y

open KIP126.Kervaire.Route KIP126.Core.SpectralSequence KIP126.Literature
open KIP126.AdamsSynthetic.Standard
public theorem finite_target_label_iff (X : ClassicalObject) (q : ℕ) (hq : 0 < q)
    (s t : ℤ) (k : ℕ) (hk : k < q)
    (y : cycles model X ((q:ℤ)-t+(t-k)) (s,t))
    (e : ((model.family.quotient (model.nu.functor.obj (X.obj model.auxiliary)) q).sequence.ssData
      (s,t,t-k)).eInfty) :
    HasInfinityRepresentative _ 2 (s,t,t-k) (finiteTargetLabel model X q s t k y.val) e ↔
      KIP126.Literature.Standard.infinityFiniteWindow X q hq (s,t) (t-k) (by omega) e =
        subquotientClass (cycles model X ((q:ℤ)-t+(t-k)) (s,t))
          (boundaries model X (1+t-(t-k)) (s,t)) y := by
  exact Internal.Mahowald.finite_target_label_iff X q hq s t k hk y e

end KIP126.ProofTools.Operations
