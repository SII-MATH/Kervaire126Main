module

public import KIP126.Def.SpectralSequence.Basic.Proofs

@[expose] public section

/-!
# Categories of nested-subobject spectral sequences
-/

namespace KIP126.SpectralSequence

open CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The category of pre-spectral sequences. -/
instance {ι : Type w} [AddCommGroup ι] [DecidableEq ι] :
    Category.{max w v} (PreSS C ι) where
  Hom E E' := PreSSMorphism E E'
  id E := {
    toSSDataMorphism := SSDataMorphism.id E.ssData
    r₀_eq := rfl
    diffDeg_eq := rfl
    comm_d := PreSSMorphism.id_comm_d E }
  comp f g := {
    toSSDataMorphism := f.toSSDataMorphism.comp g.toSSDataMorphism
    r₀_eq := f.r₀_eq.trans g.r₀_eq
    diffDeg_eq := f.diffDeg_eq.trans g.diffDeg_eq
    comm_d := PreSSMorphism.comp_comm_d f g }
  id_comp f := PreSSMorphism.ext (funext fun k => Category.id_comp (f.φ k))
  comp_id f := PreSSMorphism.ext (funext fun k => Category.comp_id (f.φ k))
  assoc f g h :=
    PreSSMorphism.ext (funext fun k => Category.assoc (f.φ k) (g.φ k) (h.φ k))

/-- The category of nested-subobject spectral sequences. -/
instance {ι : Type w} [AddCommGroup ι] [DecidableEq ι] :
    Category.{max w v} (SpectralSequence C ι) where
  Hom E E' := SpectralSequenceMorphism E E'
  id E := {
    φ := (SSDataMorphism.id E.ssData).φ
    preserves_Z := (SSDataMorphism.id E.ssData).preserves_Z
    preserves_B := (SSDataMorphism.id E.ssData).preserves_B
    r₀_eq := rfl
    diffDeg_eq := rfl
    comm_d := PreSSMorphism.id_comm_d E.toPreSS }
  comp f g := {
    φ := (f.toSSDataMorphism.comp g.toSSDataMorphism).φ
    preserves_Z := (f.toSSDataMorphism.comp g.toSSDataMorphism).preserves_Z
    preserves_B := (f.toSSDataMorphism.comp g.toSSDataMorphism).preserves_B
    r₀_eq := f.r₀_eq.trans g.r₀_eq
    diffDeg_eq := f.diffDeg_eq.trans g.diffDeg_eq
    comm_d := PreSSMorphism.comp_comm_d f.toPreSSMorphism g.toPreSSMorphism }
  id_comp f := SpectralSequenceMorphism.ext
    (funext fun k => Category.id_comp (f.φ k))
  comp_id f := SpectralSequenceMorphism.ext
    (funext fun k => Category.comp_id (f.φ k))
  assoc f g h := SpectralSequenceMorphism.ext
    (funext fun k => Category.assoc (f.φ k) (g.φ k) (h.φ k))

end KIP126.SpectralSequence
