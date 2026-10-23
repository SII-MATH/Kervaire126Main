module

import KIP126.ProofTools.Language
import KIP126.AdamsComputation.Standard
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! Numerical targets from AimPaper Section 6, on the fixed Standard model.

All declarations in this file are private. The two classical d3 conclusions
are obtained from registered literature inputs and the actual E2 archive;
this does not supply their synthetic extension proofs. The remaining target
propositions below are definitions, with no assertion of their truth.
-/

@[expose] section
namespace KIP126.ProofTools.Paper.NumericalExamples
open CategoryTheory KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.StableHomotopy KIP126.AdamsSynthetic KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard (model Spectrum)
open KIP126.Computation KIP126.Computation.Standard
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

private def regradeMonomial {s t s' t' : ℕ} (hs : s = s') (ht : t = t')
    (a : SourceMonomial archive.generators s t) : SourceMonomial archive.generators s' t' :=
  hs ▸ ht ▸ a

private def h0Word : SourceMonomial archive.generators 1 1 :=
  regradeMonomial rfl rfl (.generator (archive.atomIndex .h0))

private def pIndex : Fin archive.generators.count := ⟨26, by decide⟩
private def d0Index : Fin archive.generators.count := ⟨8, by decide⟩

private theorem p_record : archive.generators.record pIndex = ("p",4,37) := by rfl
private theorem d0_record : archive.generators.record d0Index = ("d_0",4,18) := by rfl

private def pWord : SourceMonomial archive.generators 4 37 :=
  regradeMonomial rfl rfl (.generator pIndex)
private def d0Word : SourceMonomial archive.generators 4 18 :=
  regradeMonomial rfl rfl (.generator d0Index)

/-- The actual archived class p, rather than a freely selected E2 target. -/
private def p : model.classical.sphere.Page 2 (4,37) :=
  comparison 4 37 (by decide) (pWord.value sourceData sourceGenerator)

/-- The actual archived class d0, with its fixed original generator address. -/
private def d0 : model.classical.sphere.Page 2 (4,18) :=
  comparison 4 18 (by decide) (d0Word.value sourceData sourceGenerator)

private def h0p : model.classical.sphere.Page 2 (5,38) := product h0 p
private def h0d0 : model.classical.sphere.Page 2 (5,19) := product h0 d0

private theorem h0Word_value :
    h0Word.value sourceData sourceGenerator = sourceData.atom .h0 :=
  sourceAtom_agrees .h0

private theorem h0p_word :
    archive.basisMonomial 5 38 ⟨0,by decide⟩ = .mul h0Word pWord := by rfl

private theorem h0d0_word :
    archive.basisMonomial 5 19 ⟨0,by decide⟩ = .mul h0Word d0Word := by rfl

private theorem h0p_basis :
    (coordinates 5 38 (by decide)).symm (Finsupp.single ⟨0,by decide⟩ 1) = h0p := by
  rw [coordinates_basis,h0p_word]
  change comparison 5 38 _
    (sourceData.product 1 1 4 37 (h0Word.value sourceData sourceGenerator)
      (pWord.value sourceData sourceGenerator)) = h0p
  have h := comparison_product 1 1 4 37 (by decide)
    (h0Word.value sourceData sourceGenerator) (pWord.value sourceData sourceGenerator)
  rw [h0Word_value,comparison_h0] at h
  exact h

private theorem h0d0_basis :
    (coordinates 5 19 (by decide)).symm (Finsupp.single ⟨0,by decide⟩ 1) = h0d0 := by
  rw [coordinates_basis,h0d0_word]
  change comparison 5 19 _
    (sourceData.product 1 1 4 18 (h0Word.value sourceData sourceGenerator)
      (d0Word.value sourceData sourceGenerator)) = h0d0
  have h := comparison_product 1 1 4 18 (by decide)
    (h0Word.value sourceData sourceGenerator) (d0Word.value sourceData sourceGenerator)
  rw [h0Word_value,comparison_h0] at h
  exact h

private theorem one_coordinate_cases (x : Fin 1 →₀ ZMod 2) :
    x = 0 ∨ x = Finsupp.single 0 1 := by
  have h : x 0 = 0 ∨ x 0 = 1 :=
    (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (x 0)
  rcases h with h | h
  · left
    apply Finsupp.ext
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    simpa only [hi,Finsupp.zero_apply] using h
  · right
    apply Finsupp.ext
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    simpa only [hi,Finsupp.single_eq_same] using h

private theorem one_coordinate_label_cases
    {A : Type} [AddCommGroup A] [Module ℤ A] {n : ℕ} (hn : n = 1)
    (e : A ≃ₗ[ℤ] (Fin n →₀ ZMod 2))
    (a : A) (ha : e.symm (Finsupp.single ⟨0,by omega⟩ 1) = a) (x : A) :
    x = 0 ∨ x = a := by
  subst n
  rcases one_coordinate_cases (e x) with h | h
  · exact Or.inl (e.injective (h.trans e.map_zero.symm))
  · right
    apply e.injective
    exact h.trans ((e.apply_symm_apply _).symm.trans (congrArg e ha))

private theorem h0p_label_cases (x : model.classical.sphere.Page 2 (5,38)) :
    x = 0 ∨ x = h0p :=
  one_coordinate_label_cases rfl (coordinates 5 38 (by decide)) h0p h0p_basis x

private theorem h0d0_label_cases (x : model.classical.sphere.Page 2 (5,19)) :
    x = 0 ∨ x = h0d0 :=
  one_coordinate_label_cases rfl (coordinates 5 19 (by decide)) h0d0 h0d0_basis x

private theorem nonzero_differential_target_label_ne_zero
    {E : KIP126.Core.SpectralSequence (ModuleCat ℤ) (ℤ × ℤ)}
    {r : ℤ} {u v : ℤ × ℤ} {x : E.Page 2 u} {y : E.Page 2 v}
    (h : HasNonzeroDifferential E r u v x y) : y ≠ 0 := by
  obtain ⟨yr,hy,hyr⟩ := h.target_survives
  intro hy0
  subst y
  exact hyr (hy.unique (RepresentsOnPage.zero hy.1))

/-- The exact classical conclusion of AimPaper Example 6.7. The source is
the product of the two specified Standard Hopf classes; the target is the
actual archived product h0p. This proof uses the independent literature d3,
not the still unproved full nu-extension in Example 6.24. -/
private theorem paper6_7_classical_d3 :
    HasNonzeroDifferential model.classical.sphere 3 (2,36) (5,38)
      (KIP126.Literature.Standard.hiProduct 2 5) h0p := by
  obtain ⟨y,hy⟩ := KIP126.Literature.Standard.mahowald_tangora_h2_h5_d3
  rcases h0p_label_cases y with hz | he
  · exact False.elim (nonzero_differential_target_label_ne_zero hy hz)
  · simpa only [he] using hy

/-- The actual nonzero differential which rules out the erroneous zero
conclusion in Example 6.8 and Remarks 6.6, 6.9 and 6.10. -/
private theorem paper6_8_classical_d3 :
    HasNonzeroDifferential model.classical.sphere 3 (2,17) (5,19)
      (KIP126.Literature.Standard.hiProduct 0 4) h0d0 := by
  obtain ⟨y,hy⟩ := KIP126.Literature.Standard.iwx_h0_h4_d3
  rcases h0d0_label_cases y with hz | he
  · exact False.elim (nonzero_differential_target_label_ne_zero hy hz)
  · simpa only [he] using hy

private theorem paper6_8_not_vanishing :
    ¬ DifferentialVanishesOn model.classical.sphere 3 (2,17)
      (KIP126.Literature.Standard.hiProduct 0 4) :=
  paper6_8_classical_d3.not_all_zero

private theorem paper6_8_not_zero :
    ¬ DifferentialAt model .sphere 3 (2,17) (5,19)
      (KIP126.Literature.Standard.hiProduct 0 4) 0 := by
  rintro ⟨_,hzero⟩
  change HasDifferential model.classical.sphere 3 (2,17) (5,19)
    (KIP126.Literature.Standard.hiProduct 0 4) 0 at hzero
  obtain ⟨hdeg,xr,yr,hx,_,hd,hyne⟩ := paper6_8_classical_d3
  obtain ⟨hdeg0,xr0,yr0,hx0,hy0,hd0⟩ := hzero
  have hxx : xr = xr0 := hx.unique hx0
  have hyy : yr = yr0 := hd.symm.trans (by simpa only [hxx] using hd0)
  exact hyne (hyy.trans (hy0.unique (RepresentsOnPage.zero hy0.1)))

private def h0h4Square : model.classical.sphere.Page 2 (3,33) :=
  product h0 (model.standardClasses.standardHiSquare 4)

private def h0h3Square : model.classical.sphere.Page 2 (3,17) :=
  product h0 (model.standardClasses.standardHiSquare 3)

/-- The actual comparison of three iterated suspensions with the 3-sphere. -/
private def tripleSphereShiftIso :
    ((ClassicalObject.shift 1 (.shift 1 (.shift 1 .sphere))).obj model.auxiliary) ≅
      ((ClassicalObject.shift 3 .sphere).obj model.auxiliary) :=
  (shiftFunctor Spectrum (1:ℤ)).mapIso
    (((shiftFunctorAdd' Spectrum (1:ℤ) 1 2 (by decide)).app
      (SphereSpectrum (C := Spectrum))).symm) ≪≫
    ((shiftFunctorAdd' Spectrum (2:ℤ) 1 3 (by decide)).app
      (SphereSpectrum (C := Spectrum))).symm

/-- A fixed label condition for h0 h4² on the actual 3-sphere. Every
intermediate class is forced to be an actual classical suspension of the
specified archived product; the final map is the fixed shift comparison. -/
private def IsSphereThreeH0H4Square
    (x : Ambient model (.shift 3 .sphere) (3,36)) : Prop :=
  ∃ (x1 : Ambient model (.shift 1 .sphere) (3,34))
    (x2 : Ambient model (.shift 1 (.shift 1 .sphere)) (3,35))
    (x3 : Ambient model (.shift 1 (.shift 1 (.shift 1 .sphere))) (3,36)),
    (model.classicalSuspension .sphere).DesuspendsClass 3 34 x1 h0h4Square ∧
    (model.classicalSuspension (.shift 1 .sphere)).DesuspendsClass 3 35 x2 x1 ∧
    (model.classicalSuspension (.shift 1 (.shift 1 .sphere))).DesuspendsClass
      3 36 x3 x2 ∧
    (model.classical.map tripleSphereShiftIso.hom).pageMap 2 (3,36) x3 = x

/-- Complete finite nu-extension target in Example 6.19. This is a target
definition, not a proof or an additional premise for another theorem. -/
private def Paper6_19FiniteNuExtensionStatement : Prop :=
  ∃ x : Ambient model (.shift 3 .sphere) (3,36),
    IsSphereThreeH0H4Square x ∧
    ReachesPage (model.classical.obj ((ClassicalObject.shift 3 .sphere).obj
      model.auxiliary)) 3 (3,36) x ∧
    FiniteExtension model (.shift 3 .sphere) .sphere model.auxiliary.nuMap
      3 2 3 36 x h0p

/-- Complete full-space nu-extension target in Example 6.24. The
InfiniteExtension predicate requires one actual full source and its actual
normalized-map image with both specified detections; no collection of
unrelated finite quotient witnesses is substituted. -/
private def Paper6_24InfiniteNuExtensionStatement : Prop :=
  ∃ x : Ambient model (.shift 3 .sphere) (3,36),
    IsSphereThreeH0H4Square x ∧
    InfiniteExtension model (.shift 3 .sphere) .sphere model.auxiliary.nuMap
      2 3 36 x h0p

private def Paper6_7ClassicalStatement : Prop :=
  DifferentialAt model .sphere 3 (2,36) (5,38)
    (KIP126.Literature.Standard.hiProduct 2 5) h0p

private theorem paper6_7_classical : Paper6_7ClassicalStatement :=
  ⟨by decide,paper6_7_classical_d3.toHasDifferential⟩

/-- The extension-equation portion of the warning, including the shorter
essential extension and the two actual full-space length-two witnesses.
Normalization calibration and the maximal-image-choice explanation are not
asserted by this definition. Only exclusion of the zero d3 is proved above. -/
private def Paper6_8CrossingWarningStatement : Prop :=
  let f : SphereSpectrum (C := Spectrum) ⟶ SphereSpectrum := 2 • 𝟙 _
  DifferentialAt model .sphere 2 (1,16) (3,17) h4 h0h3Square ∧
  FiniteExtension model .sphere .sphere f 2 1 1 16 h4
    (KIP126.Literature.Standard.hiProduct 0 4) ∧
  InfiniteExtension model .sphere .sphere f 2 3 17 h0h3Square 0 ∧
  (∃ W : InfiniteExtensionWitness model .sphere .sphere f 1 4 18 d0 h0d0,
    W.Essential) ∧
  InfiniteExtension model .sphere .sphere f 2 3 17 h0h3Square h0d0 ∧
  ¬ DifferentialAt model .sphere 3 (2,17) (5,19)
    (KIP126.Literature.Standard.hiProduct 0 4) 0

/-- The paper's page-two differential no-crossing check is vacuous. This
does not identify it with any stronger synthetic crossing predicate. -/
private theorem paper6_19_classical_d2_no_crossing :
    NoCrossingOn model .nuCofiber 2 2 (3,37) := by
  refine ⟨by decide,by decide,?_⟩
  rintro ⟨a,b,ha,hab,_⟩
  omega

/-- The original E2 top-cell extension has no crossing for the same
page-index reason; its actual existence and fixed labels remain separate. -/
private theorem paper6_19_top_page_two_no_crossing :
    FiniteNoCrossing model .nuCofiber (.shift 1 (.shift 3 .sphere))
      model.auxiliary.nuRouteTriangle.h 2 0 3 37 := by
  rintro ⟨a,b,ha,hab,_⟩
  omega

end
end KIP126.ProofTools.Paper.NumericalExamples
end
