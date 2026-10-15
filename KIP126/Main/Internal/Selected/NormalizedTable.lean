module
public import KIP126.Main.Conditions
public import KIP126.Def.Computation.Table

/-! A private change of presentation for the fixed Adams sequence. The
record is proved equal to the actual input; it only makes the known first
page and differential degree reducible in the finite calculations. -/
@[expose] section
namespace KIP126.Main.Internal.Selected.Normalized
open CategoryTheory CategoryTheory.Limits KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic.Standard (model)
open KIP126.Computation.Table
noncomputable section
set_option backward.isDefEq.respectTransparency false

private def pre (E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ×ℤ))
    (hr : E.r₀=2) (hd : E.diffDeg=fun r => (r,r-1)) :
    PreSS (ModuleCat.{v} ℤ) (ℤ×ℤ) where
  r₀ := 2
  ssData := E.ssData
  diffDeg := fun r => (r,r-1)
  d r p := by simpa only [hr,hd] using E.d r p

private theorem pre_eq (E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ×ℤ))
    (hr : E.r₀=2) (hd : E.diffDeg=fun r => (r,r-1)) : pre E hr hd=E.toPreSS := by
  rcases E with ⟨⟨r,data,degree,d⟩,hdd,hZ,hB⟩
  dsimp only at hr hd
  subst r
  subst degree
  rfl

private def normalize (E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ×ℤ))
    (hr : E.r₀=2) (hd : E.diffDeg=fun r => (r,r-1)) :
    KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ×ℤ) where
  toPreSS := pre E hr hd
  d_comp_d := by rw [pre_eq]; exact E.d_comp_d
  Z_succ := by rw [pre_eq]; exact E.Z_succ
  B_succ := by rw [pre_eq]; exact E.B_succ

private theorem normalize_eq (E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ×ℤ))
    (hr : E.r₀=2) (hd : E.diffDeg=fun r => (r,r-1)) : normalize E hr hd=E := by
  rcases E with ⟨⟨r,data,degree,d⟩,hdd,hZ,hB⟩
  dsimp only at hr hd
  subst r
  subst degree
  rfl

private def sequence (o : Raw.Spectrum) := normalize (KIP126.Computation.Table.sequence o)
  (model.classical.firstPage _) (funext (model.classical.differentialDegree _))

private theorem sequence_eq (o : Raw.Spectrum) : sequence o=KIP126.Computation.Table.sequence o :=
  normalize_eq _ _ _

private abbrev sphere := sequence .sphere

private abbrev Page (o : Raw.Spectrum) (s t : ℕ) := (sequence o).Page 2 (s,t)

private def basis (o : Raw.Spectrum) (s t i : ℕ) : Page o s t :=
  (eqToHom (congrArg (fun E : KIP126.Core.SpectralSequence (ModuleCat ℤ) (ℤ×ℤ) => E.Page 2 (s,t))
    (sequence_eq o).symm)) (KIP126.Computation.Table.basis o s t i)

private def decode (o : Raw.Spectrum) (s t : ℕ) (indices : List ℕ) : Option (Page o s t) :=
  if Raw.coordinatesValid Raw.degrees o s t indices then some ((indices.map (basis o s t)).sum) else none

private def BasisCorrect (d : Raw.Degree) : Prop :=
  ∃ e : Page d.spectrum d.s d.t ≃ₗ[ℤ] (Fin d.monomials.length →₀ ZMod 2),
    ∀ i, e.symm (Finsupp.single i 1)=basis d.spectrum d.s d.t i.val

private theorem basis_correct (d : Raw.Degree) (hd : d ∈ Raw.degrees) : BasisCorrect d := by
  have transport (E E' : KIP126.Core.SpectralSequence (ModuleCat ℤ) (ℤ×ℤ)) (h : E=E')
      (b : ℕ → E.Page 2 (d.s,d.t))
      (hb : ∃ e : E.Page 2 (d.s,d.t) ≃ₗ[ℤ] (Fin d.monomials.length →₀ ZMod 2),
        ∀ i, e.symm (Finsupp.single i 1)=b i.val) :
      ∃ e : E'.Page 2 (d.s,d.t) ≃ₗ[ℤ] (Fin d.monomials.length →₀ ZMod 2),
        ∀ i, e.symm (Finsupp.single i 1)=
          (eqToHom (congrArg (fun A => A.Page 2 (d.s,d.t)) h)) (b i.val) := by
    subst E'
    simpa only [eqToHom_refl,ModuleCat.id_apply] using hb
  exact transport _ _ (sequence_eq d.spectrum).symm
    (KIP126.Computation.Table.basis d.spectrum d.s d.t)
    (KIP126.Computation.Table.basis_correct d hd)

private def Statement (c : Raw.Claim) : Prop :=
  ∃ x, decode c.spectrum c.s c.t c.x=some x ∧
    match c.kind with
    | .reaches => ReachesPage (sequence c.spectrum) c.r (c.s,c.t) x
    | .boundaryBy => IsBoundaryBy (sequence c.spectrum) c.r (c.s,c.t) x
    | .equation => ∃ y, decode c.spectrum c.ts c.tt c.y=some y ∧
        HasDifferential (sequence c.spectrum) c.r (c.s,c.t) (c.ts,c.tt) x y
    | .refutation => ∃ y, decode c.spectrum c.ts c.tt c.y=some y ∧
        ¬ HasDifferential (sequence c.spectrum) c.r (c.s,c.t) (c.ts,c.tt) x y

private theorem result (c : Raw.Claim) (hc : c ∈ Raw.claims) : Statement c := by
  let stmt (E : KIP126.Core.SpectralSequence (ModuleCat ℤ) (ℤ×ℤ))
      (b : (s t i : ℕ) → E.Page 2 (s,t)) : Prop :=
    let dec (s t : ℕ) (indices : List ℕ) : Option (E.Page 2 (s,t)) :=
      if Raw.coordinatesValid Raw.degrees c.spectrum s t indices then some ((indices.map (b s t)).sum) else none
    ∃ x, dec c.s c.t c.x=some x ∧
      match c.kind with
      | .reaches => ReachesPage E c.r (c.s,c.t) x
      | .boundaryBy => IsBoundaryBy E c.r (c.s,c.t) x
      | .equation => ∃ y, dec c.ts c.tt c.y=some y ∧ HasDifferential E c.r (c.s,c.t) (c.ts,c.tt) x y
      | .refutation => ∃ y, dec c.ts c.tt c.y=some y ∧ ¬HasDifferential E c.r (c.s,c.t) (c.ts,c.tt) x y
  have transport (E E' : KIP126.Core.SpectralSequence (ModuleCat ℤ) (ℤ×ℤ)) (h : E=E')
      (b : (s t i : ℕ) → E.Page 2 (s,t)) (hb : stmt E b) :
      stmt E' (fun s t i => (eqToHom (congrArg (fun A => A.Page 2 (s,t)) h)) (b s t i)) := by
    subst E'
    simpa only [eqToHom_refl,ModuleCat.id_apply] using hb
  exact transport _ _ (sequence_eq c.spectrum).symm
    (KIP126.Computation.Table.basis c.spectrum) (KIP126.Computation.Table.result c hc)

end
end KIP126.Main.Internal.Selected.Normalized
