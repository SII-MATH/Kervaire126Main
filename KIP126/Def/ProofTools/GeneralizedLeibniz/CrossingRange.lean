module
import all KIP126.Def.ProofTools.GeneralizedLeibniz.Filtration
import all KIP126.Def.ProofTools.StretchingRepresentatives

/-! Source-filtration bounds for the finite crossing comparison in AimPaper
Proposition `prop:cross-f-Er`. The finite E∞ window bounds the source displacement;
at page two it rules out all higher-source essential extensions. -/
@[expose] section
namespace KIP126.ProofTools.Internal.Leibniz
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.AdamsSynthetic.Standard
noncomputable section
set_option backward.isDefEq.respectTransparency false

private theorem finite_extension_zero_source_not_essential (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary) (q : ℕ)
    (p : ℤ × ℤ) (u d : ℤ) (hd : 0 ≤ d)
    (y : ((model.family.obj ((SyntheticObject.quotient q (.nu Y)).obj model.nu model.auxiliary)).sequence.ssData
      (u+d,p.1+(u+d),p.2)).eInfty) :
    ¬ TowerEssentialExtension (model.convergentMap
      (.quotient q (extensionSourceObject model X Y f)) (.quotient q (.nu Y))
      (finiteExtensionMap model X Y f q)) p u d 0 y := by
  intro he
  have hrel : TowerExtensionEquation (model.convergentMap
      (.quotient q (extensionSourceObject model X Y f)) (.quotient q (.nu Y))
      (finiteExtensionMap model X Y f q)) p u d 0 y := he.1
  have hzero : TowerExtensionEquation (model.convergentMap
      (.quotient q (extensionSourceObject model X Y f)) (.quotient q (.nu Y))
      (finiteExtensionMap model X Y f q)) p u d 0 0 := by
    apply (tower_extension_iff _ _ _ _ _ _).mpr
    refine ⟨hd,0,0,?_,?_,?_⟩ <;> simp
  exact ((tower_essential_iff_no_zero _ _ _ _ _ _ hrel).mp he) hzero

private theorem finite_crossing_source_bound (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary) (q : ℕ) (hq : 0 < q)
    (s t u v : ℤ) (huv : u ≤ v)
    (x : ((model.family.obj ((SyntheticObject.quotient q (extensionSourceObject model X Y f)).obj model.nu model.auxiliary)).sequence.ssData
      (u,(t-s)+u,t+normalizedExponent model.classicalTower f)).eInfty)
    (y : ((model.family.obj ((SyntheticObject.quotient q (.nu Y)).obj model.nu model.auxiliary)).sequence.ssData
      (u+(v-u),(t-s)+(u+(v-u)),t+normalizedExponent model.classicalTower f)).eInfty)
    (he : TowerEssentialExtension (model.convergentMap
      (.quotient q (extensionSourceObject model X Y f)) (.quotient q (.nu Y))
      (finiteExtensionMap model X Y f q))
      (t-s,t+normalizedExponent model.classicalTower f) u (v-u) x y) : u-s < q := by
  by_contra hqle
  have hz := shifted_quotient_eInfty_zero X q hq (normalizedExponent model.classicalTower f)
    u ((t-s)+u) (t+normalizedExponent model.classicalTower f) (by omega)
  have hsub := ModuleCat.isZero_iff_subsingleton.mp hz
  have hx : x = 0 := @Subsingleton.elim _ hsub _ _
  subst x
  exact finite_extension_zero_source_not_essential X Y f q
    (t-s,t+normalizedExponent model.classicalTower f) u (v-u) (by omega) y he

private theorem page_two_tower_no_crossing (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary) (s t n : ℤ) :
    TowerNoCrossing (model.convergentMap
      (.quotient 1 (extensionSourceObject model X Y f)) (.quotient 1 (.nu Y))
      (finiteExtensionMap model X Y f 1))
      (t-s,t+normalizedExponent model.classicalTower f) s n := by
  intro u v hsu huv hvs x y he
  have hh := finite_crossing_source_bound X Y f 1 (by omega) s t u v huv x y he
  omega
end
end KIP126.ProofTools.Internal.Leibniz
