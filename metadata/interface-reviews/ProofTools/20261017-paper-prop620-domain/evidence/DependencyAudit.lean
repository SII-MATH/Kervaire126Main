module
import Lean

public import KIP126.ProofTools.Language
import all KIP126.ProofTools.ConvergenceOperations
import all KIP126.ProofTools.StretchingRepresentatives

/-! The naturality part of AimPaper Proposition 6.20, on the domain of
Definition 5.4. The printed essentiality equivalence requires a separate
statement review and is not asserted by this file. -/

@[expose] section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace KIP126.ProofTools.Paper
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Core.SpectralSequence.FinitePageCalculus
open KIP126.Kervaire.Route KIP126.AdamsSynthetic.Standard
open KIP126.ProofTools.Internal
noncomputable section

private theorem extension_square_map
    (A B A' B' : SyntheticObject)
    (g : A.obj model.nu model.auxiliary ⟶ B.obj model.nu model.auxiliary)
    (g' : A'.obj model.nu model.auxiliary ⟶ B'.obj model.nu model.auxiliary)
    (ra : A.obj model.nu model.auxiliary ⟶ A'.obj model.nu model.auxiliary)
    (rb : B.obj model.nu model.auxiliary ⟶ B'.obj model.nu model.auxiliary)
    (hsquare : ra ≫ g' = g ≫ rb) (p : ℤ × ℤ) (s n : ℤ)
    (x : ((model.family.obj (A.obj model.nu model.auxiliary)).sequence.ssData
      (s,p.1+s,p.2)).eInfty)
    (y : ((model.family.obj (B.obj model.nu model.auxiliary)).sequence.ssData
      (s+n,p.1+(s+n),p.2)).eInfty)
    (h : TowerExtensionEquation (model.convergentMap A B g) p s n x y) :
    TowerExtensionEquation (model.convergentMap A' B' g') p s n
      ((model.family.functor.map ra).eInftyMap (s,p.1+s,p.2) x)
      ((model.family.functor.map rb).eInftyMap (s+n,p.1+(s+n),p.2) y) := by
  obtain ⟨hn,a,b,hab,ha,hb⟩ :=
    (tower_extension_iff (model.convergentMap A B g) p s n x y).mp h
  let a' := ((model.convergentMap A A' ra).filteredMap.compat s p).choose a
  let b' := ((model.convergentMap B B' rb).filteredMap.compat (s+n) p).choose b
  have ha' : ((model.syntheticTower.filtration (A'.obj model.nu model.auxiliary)).F s p).arrow a' =
      ((model.syntheticTower.filtration (A.obj model.nu model.auxiliary)).F s p).arrow a ≫ ra := by
    have hh := ConcreteCategory.congr_hom
      ((model.convergentMap A A' ra).filteredMap.compat s p).choose_spec a
    change _ = (model.convergentMap A A' ra).filteredMap.map p
      (((model.syntheticTower.filtration (A.obj model.nu model.auxiliary)).F s p).arrow a) at hh
    exact hh.trans (ConcreteCategory.congr_hom
      ((model.convergentMap A A' ra).filteredMap_map p) _)
  have hb' : ((model.syntheticTower.filtration (B'.obj model.nu model.auxiliary)).F (s+n) p).arrow b' =
      ((model.syntheticTower.filtration (B.obj model.nu model.auxiliary)).F (s+n) p).arrow b ≫ rb := by
    have hh := ConcreteCategory.congr_hom
      ((model.convergentMap B B' rb).filteredMap.compat (s+n) p).choose_spec b
    change _ = (model.convergentMap B B' rb).filteredMap.map p
      (((model.syntheticTower.filtration (B.obj model.nu model.auxiliary)).F (s+n) p).arrow b) at hh
    exact hh.trans (ConcreteCategory.congr_hom
      ((model.convergentMap B B' rb).filteredMap_map p) _)
  apply (tower_extension_iff (model.convergentMap A' B' g') p s n _ _).mpr
  refine ⟨hn,a',b',?_,?_,?_⟩
  · rw [ha',hb',Category.assoc,hsquare,← Category.assoc,hab]
  · have hh := representative_grade_naturality
      (model.convergentMap A A' ra) p s a a' ha'.symm
    rw [ha] at hh
    have hc := (infinityGradedIso (model.convergence A) p s).toLinearEquiv.symm_apply_apply x
    change (infinityGradedIso (model.convergence A) p s).inv
      ((infinityGradedIso (model.convergence A) p s).hom x) = x at hc
    rw [hc] at hh
    exact ((infinityGradedIso (model.convergence A') p s).toLinearEquiv.apply_symm_apply _).symm.trans
      (congrArg (infinityGradedIso (model.convergence A') p s).hom hh)
  · have hh := representative_grade_naturality
      (model.convergentMap B B' rb) p (s+n) b b' hb'.symm
    rw [hb] at hh
    have hc := (infinityGradedIso (model.convergence B) p (s+n)).toLinearEquiv.symm_apply_apply y
    change (infinityGradedIso (model.convergence B) p (s+n)).inv
      ((infinityGradedIso (model.convergence B) p (s+n)).hom y) = y at hc
    rw [hc] at hh
    exact ((infinityGradedIso (model.convergence B') p (s+n)).toLinearEquiv.apply_symm_apply _).symm.trans
      (congrArg (infinityGradedIso (model.convergence B') p (s+n)).hom hh)

/-- Finite page extensions descend along the actual quotient reduction,
provided the target page belongs to the defining length range. This is the
naturality assertion of Proposition 6.20 on the domain of Definition 5.4. -/
public theorem finiteExtension_descends
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (rEarlier rLater : ℕ) (n s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model Y (s+n,t+n))
    (hr : 2 ≤ rEarlier) (hle : rEarlier ≤ rLater)
    (hnUpper : n ≤ (rEarlier : ℤ) - 2 + normalizedExponent model.classicalTower f)
    (h : FiniteExtension model X Y f rLater n s t x y) :
    FiniteExtension model X Y f rEarlier n s t x y := by
  obtain ⟨W⟩ := h
  let ra := (model.quotients.tower
    ((extensionSourceObject model X Y f).obj model.nu model.auxiliary)).rho
      (rEarlier-1) (rLater-1) (Nat.sub_le_sub_right hle 1)
  let rb := (model.quotients.tower (model.nu.functor.obj (Y.obj model.auxiliary))).rho
    (rEarlier-1) (rLater-1) (Nat.sub_le_sub_right hle 1)
  refine ⟨{
    page_ge_two := hr
    length_lower := W.length_lower
    length_upper := hnUpper
    source_cycle := reaches_earlier (by omega) (by omega) W.source_cycle
    target_cycle := reaches_earlier (by omega) (by omega) W.target_cycle
    source := (model.family.functor.map ra).eInftyMap
      (s,(t-s)+s,t+normalizedExponent model.classicalTower f) W.source
    target := (model.family.functor.map rb).eInftyMap
      (s+n,(t-s)+(s+n),t+normalizedExponent model.classicalTower f) W.target
    source_rep := ?_
    target_rep := ?_
    equation := ?_ }⟩
  · have hh := family_infinity_representative_map ra _ _ W.source W.source_rep
    rw [finite_source_rho] at hh
    exact hh
  · have hh := family_infinity_representative_map rb _ _ W.target W.target_rep
    rw [finite_target_rho] at hh
    exact hh
  · exact extension_square_map
      (.quotient (rLater-1) (extensionSourceObject model X Y f))
      (.quotient (rLater-1) (.nu Y))
      (.quotient (rEarlier-1) (extensionSourceObject model X Y f))
      (.quotient (rEarlier-1) (.nu Y))
      (finiteExtensionMap model X Y f (rLater-1))
      (finiteExtensionMap model X Y f (rEarlier-1)) ra rb
      ((model.quotients.natural (model.normalizedMap X Y f).map).rho_naturality
        (Nat.sub_le_sub_right hle 1))
      (t-s,t+normalizedExponent model.classicalTower f) s n W.source W.target W.equation

end
end KIP126.ProofTools.Paper

open Lean Elab Command in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let root := `KIP126.ProofTools.Paper.finiteExtension_descends
  let mut pending := #[root]
  let mut seen : NameSet := {}
  let mut project : Array String := #[]
  let mut holes : Array String := #[]
  let mut main : Array String := #[]
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    let userName := (privateToUserName? name).getD name
    unless userName.toString.startsWith "KIP126." do continue
    let some info := env.find? name | throwError "Missing dependency {name}"
    project := project.push userName.toString
    let body := info.value? (allowOpaque := true)
    if info.type.hasSorry || body.any (·.hasSorry) then
      holes := holes.push userName.toString
    if userName.toString.startsWith "KIP126.Main." then
      main := main.push userName.toString
    pending := pending ++ info.type.getUsedConstants
    if let some value := body then pending := pending ++ value.getUsedConstants
  let axioms ← collectAxioms root
  let data := Json.mkObj [
    ("root", toJson root.toString),
    ("project_constant_count", toJson project.size),
    ("project_constants", toJson project),
    ("direct_sorry_dependencies", toJson holes),
    ("main_dependencies", toJson main),
    ("axioms", toJson (axioms.map Name.toString))]
  liftIO <| IO.FS.writeFile "metadata/interface-reviews/ProofTools/20261017-paper-prop620-domain/evidence/dependency-audit.json" (data.pretty ++ "\n")
  logInfo m!"Actual project closure: {project.size} constants, {holes.size} existing direct holes, {main.size} Main dependencies"
