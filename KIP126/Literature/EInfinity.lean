module

public import KIP126.AdamsSynthetic

/-! Actual E₂ subquotients and synthetic E∞ formulae, adapted from
`ClassicalAdams/PageRepresentatives/Quotient` and `Synthetic/EInfty/Presentation`
at bbac1fc05843. The raw ambient object is not confused with E₂.
The paper's Z_c and B_b use raw index c-1 and b-1, respectively. -/

@[expose] section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace KIP126.Literature
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn]
  [HasFunctorialCofiber (C := Syn)] (D : Model C Syn)

public def cycleLabel (X : ClassicalObject) (n : WithTop ℕ) (p : Bidegree) :
    Subobject.underlying.obj (((D.classical.obj (X.obj D.auxiliary)).ssData p).Z n) ⟶
      (D.classical.obj (X.obj D.auxiliary)).Page 2 p :=
  let E := (D.classical.obj (X.obj D.auxiliary)).ssData p
  Subobject.ofLE (E.Z n) (E.Z 0) (E.Z_anti bot_le) ≫ E.pageπ 0 ≫
    eqToHom (by simp [E, Page, D.classical.firstPage])

public def boundaryLabel (X : ClassicalObject) (n : WithTop ℕ) (p : Bidegree) :
    Subobject.underlying.obj (((D.classical.obj (X.obj D.auxiliary)).ssData p).B n) ⟶
      (D.classical.obj (X.obj D.auxiliary)).Page 2 p :=
  let E := (D.classical.obj (X.obj D.auxiliary)).ssData p
  Subobject.ofLE (E.B n) (E.Z 0) ((E.B_le_Z n).trans (E.Z_anti bot_le)) ≫ E.pageπ 0 ≫
    eqToHom (by simp [E, Page, D.classical.firstPage])

public def cycles (X : ClassicalObject) (c : ℤ) (p : Bidegree) :=
  LinearMap.range (cycleLabel D X (↑(c-1).toNat) p).hom
public def boundaries (X : ClassicalObject) (b : ℤ) (p : Bidegree) :=
  LinearMap.range (boundaryLabel D X (↑(b-1).toNat) p).hom
public def permanentCycles (X : ClassicalObject) (p : Bidegree) :=
  LinearMap.range (cycleLabel D X ⊤ p).hom

private theorem cycleLabel_factor (X : ClassicalObject) (p : Bidegree)
    (a b : WithTop ℕ) (h : a ≤ b) :
    let E := (D.classical.obj (X.obj D.auxiliary)).ssData p
    Subobject.ofLE (E.Z b) (E.Z a) (E.Z_anti h) ≫ cycleLabel D X a p =
      cycleLabel D X b p := by
  dsimp [cycleLabel]
  simp only [← Category.assoc, Subobject.ofLE_comp_ofLE]

private theorem boundaryLabel_factor (X : ClassicalObject) (p : Bidegree)
    (a b : WithTop ℕ) (h : a ≤ b) :
    let E := (D.classical.obj (X.obj D.auxiliary)).ssData p
    Subobject.ofLE (E.B a) (E.B b) (E.B_mono h) ≫ boundaryLabel D X b p =
      boundaryLabel D X a p := by
  dsimp [boundaryLabel]
  simp only [← Category.assoc, Subobject.ofLE_comp_ofLE]

public theorem cycles_antitone (X : ClassicalObject) (p : Bidegree) :
    Antitone (fun c => cycles D X c p) := by
  intro a b hab x hx
  obtain ⟨z, rfl⟩ := hx
  have h : (↑(a-1).toNat : WithTop ℕ) ≤ ↑(b-1).toNat := by
    exact_mod_cast (show (a-1).toNat ≤ (b-1).toNat by omega)
  refine ⟨(Subobject.ofLE _ _ (((D.classical.obj (X.obj D.auxiliary)).ssData p).Z_anti h)) z, ?_⟩
  exact congrArg (fun f => f z) (cycleLabel_factor D X p _ _ h)

public theorem boundaries_monotone (X : ClassicalObject) (p : Bidegree) :
    Monotone (fun b => boundaries D X b p) := by
  intro a b hab x hx
  obtain ⟨z, rfl⟩ := hx
  have h : (↑(a-1).toNat : WithTop ℕ) ≤ ↑(b-1).toNat := by
    exact_mod_cast (show (a-1).toNat ≤ (b-1).toNat by omega)
  refine ⟨(Subobject.ofLE _ _ (((D.classical.obj (X.obj D.auxiliary)).ssData p).B_mono h)) z, ?_⟩
  exact congrArg (fun f => f z) (boundaryLabel_factor D X p _ _ h)

public theorem permanentCycles_le_cycles (X : ClassicalObject) (p : Bidegree) (c : ℤ) :
    permanentCycles D X p ≤ cycles D X c p := by
  rintro x ⟨z, rfl⟩
  refine ⟨(Subobject.ofLE _ _
    (((D.classical.obj (X.obj D.auxiliary)).ssData p).Z_anti le_top)) z, ?_⟩
  exact congrArg (fun f => f z) (cycleLabel_factor D X p _ ⊤ le_top)

universe a b

/-- The actual submodule quotient, uniformly over its scalar ring. -/
public abbrev E2Subquotient {R : Type a} [Ring R] {A : Type b}
    [AddCommGroup A] [Module R A] (Z B : Submodule R A) := Z ⧸ B.comap Z.subtype

public def subquotientClass {R : Type a} [Ring R] {A : Type b}
    [AddCommGroup A] [Module R A] (Z B : Submodule R A) : Z →ₗ[R] E2Subquotient Z B :=
  (B.comap Z.subtype).mkQ

public def subquotientMap {R : Type a} [Ring R] {A : Type b}
    [AddCommGroup A] [Module R A] {Z Z' B B' : Submodule R A}
    (hZ : Z ≤ Z') (hB : B ≤ B') : E2Subquotient Z B →ₗ[R] E2Subquotient Z' B' :=
  (B.comap Z.subtype).mapQ (B'.comap Z'.subtype)
    (Submodule.inclusion hZ) (fun _ hx => hB hx)

public theorem subquotientMap_surjective {R : Type a} [Ring R] {A : Type b}
    [AddCommGroup A] [Module R A] {Z B B' : Submodule R A} (hB : B ≤ B') :
    Function.Surjective (subquotientMap (le_rfl : Z ≤ Z) hB) := by
  intro y
  obtain ⟨x,rfl⟩ := Submodule.Quotient.mk_surjective _ y
  exact ⟨Submodule.Quotient.mk x, rfl⟩

public abbrev CycleQuotient (X : ClassicalObject) (c b : ℤ) (p : Bidegree) :=
  E2Subquotient (cycles D X c p) (boundaries D X b p)
public abbrev PermanentQuotient (X : ClassicalObject) (b : ℤ) (p : Bidegree) :=
  E2Subquotient (permanentCycles D X p) (boundaries D X b p)

public def quotientMap (X : ClassicalObject) {c c' b b' : ℤ}
    (hc : c' ≤ c) (hb : b ≤ b') (p : Bidegree) :
    CycleQuotient D X c b p →ₗ[ℤ] CycleQuotient D X c' b' p :=
  subquotientMap (cycles_antitone D X p hc) (boundaries_monotone D X p hb)

public def permanentQuotientMap (X : ClassicalObject) {b b' : ℤ}
    (hb : b ≤ b') (p : Bidegree) :
    PermanentQuotient D X b p →ₗ[ℤ] PermanentQuotient D X b' p :=
  subquotientMap (le_refl (permanentCycles D X p)) (boundaries_monotone D X p hb)

public def permanentToFinite (X : ClassicalObject) (c b : ℤ) (p : Bidegree) :
    PermanentQuotient D X b p →ₗ[ℤ] CycleQuotient D X c b p :=
  subquotientMap (permanentCycles_le_cycles D X p c) (le_refl (boundaries D X b p))

public theorem permanentQuotientMap_surjective (X : ClassicalObject) {b b' : ℤ}
    (hb : b ≤ b') (p : Bidegree) : Function.Surjective (permanentQuotientMap D X hb p) := by
  exact subquotientMap_surjective (Z := permanentCycles D X p) (boundaries_monotone D X p hb)

public def nuEInftyModel (X : ClassicalObject) (p : Bidegree) (w : ℤ) : ModuleCat.{v} ℤ :=
  if w ≤ p.2 then ModuleCat.of ℤ (PermanentQuotient D X (1+p.2-w) p)
  else ModuleCat.of ℤ PUnit.{v+1}

public def finiteEInftyModel (X : ClassicalObject) (q : ℕ) (p : Bidegree) (w : ℤ) : ModuleCat.{v} ℤ :=
  if 0 ≤ p.2-w ∧ p.2-w < q then ModuleCat.of ℤ (CycleQuotient D X (q-p.2+w) (1+p.2-w) p)
  else ModuleCat.of ℤ PUnit.{v+1}

public structure EInfinityPresentation where
  nu : ∀ (X : ClassicalObject) (p : Bidegree) (w : ℤ),
    ((D.family.nu D.nu (X.obj D.auxiliary)).sequence.ssData (p.1,p.2,w)).eInfty ≃+
      nuEInftyModel D X p w
  finite : ∀ (X : ClassicalObject) (q : ℕ) (_hq : 0 < q) (p : Bidegree) (w : ℤ),
    ((D.family.quotient (D.nu.functor.obj (X.obj D.auxiliary)) q).sequence.ssData (p.1,p.2,w)).eInfty ≃+
      finiteEInftyModel D X q p w

/-- Additive comparison is already ℤ-linear; this view retains the source
interface's linear form without choosing a second scalar action. -/
public def EInfinityPresentation.nuLinear (P : EInfinityPresentation D)
    (X : ClassicalObject) (p : Bidegree) (w : ℤ) :
    ((D.family.nu D.nu (X.obj D.auxiliary)).sequence.ssData (p.1,p.2,w)).eInfty ≃ₗ[ℤ]
      nuEInftyModel D X p w := (P.nu X p w).toIntLinearEquiv

public def EInfinityPresentation.finiteLinear (P : EInfinityPresentation D)
    (X : ClassicalObject) (q : ℕ) (hq : 0 < q) (p : Bidegree) (w : ℤ) :
    ((D.family.quotient (D.nu.functor.obj (X.obj D.auxiliary)) q).sequence.ssData (p.1,p.2,w)).eInfty ≃ₗ[ℤ]
      finiteEInftyModel D X q p w := (P.finite X q hq p w).toIntLinearEquiv

public def EInfinityPresentation.nuWindow (P : EInfinityPresentation D)
    (X : ClassicalObject) (p : Bidegree) (w : ℤ) (hw : w ≤ p.2) :
    ((D.family.nu D.nu (X.obj D.auxiliary)).sequence.ssData (p.1,p.2,w)).eInfty ≃+
      PermanentQuotient D X (1+p.2-w) p :=
  (P.nu X p w).trans (by unfold nuEInftyModel; rw [if_pos hw])

public def EInfinityPresentation.finiteWindow (P : EInfinityPresentation D)
    (X : ClassicalObject) (q : ℕ) (hq : 0 < q) (p : Bidegree) (w : ℤ)
    (hw : 0 ≤ p.2-w ∧ p.2-w < q) :
    ((D.family.quotient (D.nu.functor.obj (X.obj D.auxiliary)) q).sequence.ssData (p.1,p.2,w)).eInfty ≃+
      CycleQuotient D X (q-p.2+w) (1+p.2-w) p :=
  (P.finite X q hq p w).trans
    (by unfold finiteEInftyModel; rw [if_pos hw])

/-- The E∞ shift is determined by actual filtered homotopy transport and
the model's given convergence, using the established AdamsSynthetic interface. -/
public def infinityShift (K : ∀ k : ℕ, SyntheticESSShiftComparison D (0,-(k:ℤ)))
    (X : SyntheticObject) (k : ℕ) (p : Bidegree) (w : ℤ) :
    ((D.family.obj (X.obj D.nu D.auxiliary)).sequence.ssData (p.1,p.2,w)).eInfty ≅
      ((D.family.obj ((SyntheticObject.shift (0,-(k:ℤ)) X).obj D.nu D.auxiliary)).sequence.ssData
        (p.1,p.2,w-k)).eInfty :=
  eqToIso (by simp) ≪≫
    towerInfinityIso (D.convergence X) (D.convergence (.shift (0,-(k:ℤ)) X))
      ((K k).filtered X (p.2-p.1,w)) p.1 ≪≫ eqToIso (by simp [sub_eq_add_neg])

/-- Naturality concerns the shift fixed by the actual homotopy maps, so no
unrelated infinity-page automorphism can be selected. -/
public structure InfinityShiftCoordinates where
  comparison : ∀ k : ℕ, SyntheticESSShiftComparison D (0,-(k:ℤ))
  natural : ∀ (X Y : SyntheticObject) (f : X.obj D.nu D.auxiliary ⟶ Y.obj D.nu D.auxiliary)
    (k : ℕ) (p : Bidegree) (w : ℤ),
    (D.family.map f).eInftyMap (p.1,p.2,w) ≫ (infinityShift D comparison Y k p w).hom =
      (infinityShift D comparison X k p w).hom ≫
        (D.family.map ((SyntheticCategory.biShift (0,-(k:ℤ))).map f)).eInftyMap (p.1,p.2,w-k)

public def InfinityShiftCoordinates.shift (S : InfinityShiftCoordinates D) :=
  infinityShift D S.comparison

public def InfinityShiftCoordinates.lambdaMap (S : InfinityShiftCoordinates D)
    (X : SyntheticObject) (k : ℕ) (p : Bidegree) (w : ℤ) :
    ((D.family.obj (X.obj D.nu D.auxiliary)).sequence.ssData (p.1,p.2,w)).eInfty ⟶
      ((D.family.obj (X.obj D.nu D.auxiliary)).sequence.ssData (p.1,p.2,w-k)).eInfty := by
  by_cases hk : k=0
  · subst k
    exact eqToHom (by simp)
  · exact (S.shift D X k p w).hom ≫
      (D.family.map (lambdaPow k (X.obj D.nu D.auxiliary))).eInftyMap (p.1,p.2,w-k)

public theorem InfinityShiftCoordinates.lambdaMap_zero (S : InfinityShiftCoordinates D)
    (X : SyntheticObject) (p : Bidegree) (w : ℤ) :
    HEq (S.lambdaMap D X 0 p w)
      (𝟙 (((D.family.obj (X.obj D.nu D.auxiliary)).sequence.ssData (p.1,p.2,w)).eInfty)) := by
  simp only [lambdaMap, ↓reduceDIte]
  exact eqToHom_heq_id_dom _ _ (by simp)

public def InfinityShiftCoordinates.finiteLambdaMap (S : InfinityShiftCoordinates D)
    (X : ClassicalObject) (q k : ℕ) (hkq : k < q) (p : Bidegree) (w : ℤ) :
    ((D.family.quotient (D.nu.functor.obj (X.obj D.auxiliary)) (q-k)).sequence.ssData (p.1,p.2,w)).eInfty ⟶
      ((D.family.quotient (D.nu.functor.obj (X.obj D.auxiliary)) q).sequence.ssData (p.1,p.2,w-k)).eInfty := by
  by_cases hk : k=0
  · subst k
    exact eqToHom (by simp)
  · exact (S.shift D (.quotient (q-k) (.nu X)) k p w).hom ≫
      (D.family.map ((D.quotients.tower (D.nu.functor.obj (X.obj D.auxiliary))).triangle
        (Nat.pos_of_ne_zero hk) hkq).lambdaMap).eInftyMap (p.1,p.2,w-k)

public theorem InfinityShiftCoordinates.finiteLambdaMap_zero (S : InfinityShiftCoordinates D)
    (X : ClassicalObject) (q : ℕ) (hq : 0 < q) (p : Bidegree) (w : ℤ) :
    HEq (S.finiteLambdaMap D X q 0 hq p w)
      (𝟙 (((D.family.quotient (D.nu.functor.obj (X.obj D.auxiliary)) q).sequence.ssData (p.1,p.2,w)).eInfty)) := by
  simp only [finiteLambdaMap, ↓reduceDIte]
  apply (eqToHom_heq_id_cod _ _ (by simp)).trans
  have id_heq : ∀ {A B : ModuleCat.{v} ℤ}, A = B → HEq (𝟙 A) (𝟙 B) := by
    intro A B h
    subst B
    rfl
  exact id_heq (by simp)

/-- Weight comparison lowers from w₂ to w₁ by the actual λ power.
The old KIPBase weight-raising direction reverses the boundary inclusion. -/
public def InfinityShiftCoordinates.weightMap (S : InfinityShiftCoordinates D)
    (X : ClassicalObject) (s t w₁ w₂ : ℤ) (hw : w₁ ≤ w₂) :
    ((D.family.nu D.nu (X.obj D.auxiliary)).sequence.ssData (s,t,w₂)).eInfty ⟶
      ((D.family.nu D.nu (X.obj D.auxiliary)).sequence.ssData (s,t,w₁)).eInfty :=
  S.lambdaMap D (.nu X) (w₂-w₁).toNat (s,t) w₂ ≫ eqToHom (by
    have he : w₂ - ((w₂-w₁).toNat : ℤ) = w₁ := by
      rw [Int.toNat_of_nonneg (by omega)]; omega
    rw [he]; rfl)

private structure EInfinityCompatibility (P : EInfinityPresentation D) (S : InfinityShiftCoordinates D) : Prop where
  lambda_nu : ∀ (X : ClassicalObject) (k : ℕ) (p : Bidegree) (w : ℤ) (hw : w ≤ p.2)
      (x : ((D.family.nu D.nu (X.obj D.auxiliary)).sequence.ssData (p.1,p.2,w)).eInfty),
    P.nuWindow D X p (w-k) (by omega) (S.lambdaMap D (.nu X) k p w x) =
      permanentQuotientMap D X (by omega) p (P.nuWindow D X p w hw x)
  lambda_finite : ∀ (X : ClassicalObject) (q k : ℕ) (hkq : k < q)
      (p : Bidegree) (w : ℤ) (hw : 0 ≤ p.2-w ∧ p.2-w < (q-k : ℕ))
      (x : ((D.family.quotient (D.nu.functor.obj (X.obj D.auxiliary)) (q-k)).sequence.ssData (p.1,p.2,w)).eInfty),
    P.finiteWindow D X q (by omega) p (w-k) (by constructor <;> omega)
        (S.finiteLambdaMap D X q k hkq p w x) =
      quotientMap D X (by omega) (by omega) p
        (P.finiteWindow D X (q-k) (by omega) p w hw x)
  rho_finite : ∀ (X : ClassicalObject) (i j : ℕ) (hi : 0 < i) (hij : i ≤ j)
      (p : Bidegree) (w : ℤ) (hw : 0 ≤ p.2-w ∧ p.2-w < i)
      (x : ((D.family.quotient (D.nu.functor.obj (X.obj D.auxiliary)) j).sequence.ssData (p.1,p.2,w)).eInfty),
    P.finiteWindow D X i hi p w hw
        ((D.family.map ((D.quotients.tower (D.nu.functor.obj (X.obj D.auxiliary))).rho i j hij)).eInftyMap (p.1,p.2,w) x) =
      quotientMap D X (by omega) le_rfl p
        (P.finiteWindow D X j (by omega) p w (by constructor <;> omega) x)
  rho_nu : ∀ (X : ClassicalObject) (q : ℕ) (hq : 0 < q)
      (p : Bidegree) (w : ℤ) (hw : 0 ≤ p.2-w ∧ p.2-w < q)
      (x : ((D.family.nu D.nu (X.obj D.auxiliary)).sequence.ssData (p.1,p.2,w)).eInfty),
    P.finiteWindow D X q hq p w hw
        ((D.family.quotientProjection (D.nu.functor.obj (X.obj D.auxiliary)) q).eInftyMap (p.1,p.2,w) x) =
      permanentToFinite D X (q-p.2+w) (1+p.2-w) p
        (P.nuWindow D X p w (by omega) x)
  nu_labels : ∀ (X : ClassicalObject) (s t w : ℤ) (hw : w ≤ t)
      (x : (D.classical.obj (X.obj D.auxiliary)).Page 2 (s,t))
      (z : ((D.family.nu D.nu (X.obj D.auxiliary)).sequence.ssData (s,t,w)).eInfty),
    HasInfinityRepresentative _ 2 (s,t,w) (nuWeightLabel D X s t w hw x) z ↔
      ∃ hx : x ∈ permanentCycles D X (s,t),
        P.nuWindow D X (s,t) w hw z = subquotientClass (permanentCycles D X (s,t)) (boundaries D X (1+t-w) (s,t)) ⟨x,hx⟩
  finite_labels : ∀ (X : ClassicalObject) (q : ℕ) (hq : 0 < q)
      (s t w : ℤ) (hw : 0 ≤ t-w ∧ t-w < q)
      (x : (D.classical.obj (X.obj D.auxiliary)).Page 2 (s,t))
      (z : ((D.family.quotient (D.nu.functor.obj (X.obj D.auxiliary)) q).sequence.ssData (s,t,w)).eInfty),
    HasInfinityRepresentative _ 2 (s,t,w)
      ((D.family.quotientProjection (D.nu.functor.obj (X.obj D.auxiliary)) q).pageMap 2 (s,t,w)
        (nuWeightLabel D X s t w (by omega) x)) z ↔
      ∃ hx : x ∈ cycles D X (q-t+w) (s,t),
        P.finiteWindow D X q hq (s,t) w hw z = subquotientClass (cycles D X (q-t+w) (s,t)) (boundaries D X (1+t-w) (s,t)) ⟨x,hx⟩

/-- Surjectivity is derived from the actual quotient formula and λ equation. -/
private theorem EInfinityCompatibility.lambda_epi {P : EInfinityPresentation D}
    {S : InfinityShiftCoordinates D} (R : EInfinityCompatibility D P S)
    (X : ClassicalObject) (k : ℕ) (p : Bidegree) (w : ℤ) (hw : w ≤ p.2) :
    Epi (S.lambdaMap D (.nu X) k p w) := by
  apply (ModuleCat.epi_iff_surjective _).mpr
  intro y
  obtain ⟨z,hz⟩ := permanentQuotientMap_surjective D X
    (show 1+p.2-w ≤ 1+p.2-(w-k) by omega) p
    (P.nuWindow D X p (w-k) (by omega) y)
  refine ⟨(P.nuWindow D X p w hw).symm z, ?_⟩
  apply (P.nuWindow D X p (w-k) (by omega)).injective
  rw [R.lambda_nu X k p w hw]
  simpa only [AddEquiv.apply_symm_apply] using hz

private theorem EInfinityCompatibility.weight_epi {P : EInfinityPresentation D}
    {S : InfinityShiftCoordinates D} (R : EInfinityCompatibility D P S)
    (X : ClassicalObject) (s t w₁ w₂ : ℤ) (hw : w₁ ≤ w₂) (ht : w₂ ≤ t) :
    Epi (S.weightMap D X s t w₁ w₂ hw) := by
  letI := R.lambda_epi D X (w₂-w₁).toNat (s,t) w₂ ht
  unfold InfinityShiftCoordinates.weightMap
  infer_instance

end
end KIP126.Literature
