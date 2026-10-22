module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.Pushout.Proofs
import Mathlib.Topology.Category.TopCat.Limits.Products
import Mathlib.Topology.Homotopy.Basic

@[expose] section

namespace KIP126.Topology.SequentialColimit

open CategoryTheory CategoryTheory.Limits
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- The disjoint union of the actual spaces in a sequence. -/
def telescopeVertices (F : ℕ ⥤ TopCat.{u}) : TopCat.{u} := TopCat.of (Σ n, F.obj n)

/-- Both ends of all the actual stage cylinders. -/
def telescopeEnds (F : ℕ ⥤ TopCat.{u}) : TopCat.{u} :=
  TopCat.of (telescopeVertices F ⊕ telescopeVertices F)

/-- The disjoint family of actual stage cylinders, with its product topology. -/
def telescopeCylinders (F : ℕ ⥤ TopCat.{u}) : TopCat.{u} :=
  TopCat.of (I × telescopeVertices F)

/-- The bottom of a stage cylinder attaches to that stage, and its top
to the next stage through the actual transition map. -/
def telescopeAttachingMap (F : ℕ ⥤ TopCat.{u}) : telescopeEnds F ⟶ telescopeVertices F :=
  TopCat.ofHom ⟨Sum.elim id (fun x => ⟨x.1 + 1,F.map (homOfLE (Nat.le_succ x.1)) x.2⟩),
    continuous_id.sumElim (continuous_sigma (fun n =>
      (@continuous_sigmaMk ℕ (fun k => (F.obj k : Type u)) (fun k => (F.obj k).str) (n+1)).comp (F.map (homOfLE (Nat.le_succ n))).hom.continuous))⟩

/-- The actual endpoint inclusion into the disjoint family of cylinders. -/
def telescopeEndpointMap (F : ℕ ⥤ TopCat.{u}) : telescopeEnds F ⟶ telescopeCylinders F :=
  TopCat.ofHom ⟨Sum.elim (fun x => (0,x)) (fun x => (1,x)),
    (continuous_const.prodMk continuous_id).sumElim (continuous_const.prodMk continuous_id)⟩

/-- The actual mapping telescope, defined by the topological pushout
which attaches every stage cylinder at its two prescribed ends. -/
noncomputable def telescope (F : ℕ ⥤ TopCat.{u}) : TopCat.{u} :=
  pushout (telescopeAttachingMap F) (telescopeEndpointMap F)

/-- Inclusion of all the stage vertices in the actual telescope. -/
noncomputable def telescopeVertexInclusion (F : ℕ ⥤ TopCat.{u}) : telescopeVertices F ⟶ telescope F :=
  pushout.inl _ _

/-- Inclusion of all the actual stage cylinders in the telescope. -/
noncomputable def telescopeCylinderInclusion (F : ℕ ⥤ TopCat.{u}) : telescopeCylinders F ⟶ telescope F :=
  pushout.inr _ _

/-- The actual inclusion of one stage in the mapping telescope. -/
noncomputable def telescopeStageInclusion (F : ℕ ⥤ TopCat.{u}) (n : ℕ) : F.obj n ⟶ telescope F :=
  TopCat.ofHom (X := F.obj n) (Y := telescopeVertices F) ⟨fun x => (⟨n,x⟩ : Σ k, F.obj k),
    @continuous_sigmaMk ℕ (fun k => (F.obj k : Type u)) (fun k => (F.obj k).str) n⟩ ≫ telescopeVertexInclusion F

/-- A stage cylinder retains its entire interval parameter in the telescope. -/
noncomputable def telescopeStageCylinder (F : ℕ ⥤ TopCat.{u}) (n : ℕ) : C(I × F.obj n,telescope F) :=
  (telescopeCylinderInclusion F).hom.comp
    ⟨fun z => (z.1,⟨n,z.2⟩),continuous_fst.prodMk (continuous_sigmaMk.comp continuous_snd)⟩

end KIP126.Topology.SequentialColimit
