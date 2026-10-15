module

public import KIP126.Def.Topology.SimplicialRealization.Pullback.Finite.Data
public import KIP126.Def.Topology.SimplicialRealization.Pullback.Identification.Proofs

@[expose] public section

namespace KIP126.Topology.SimplicialRealization
open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open scoped MonoidalCategory
universe u
set_option backward.isDefEq.respectTransparency false

@[simp] theorem finitePullbackHomeomorph_fst {X Y Z : SSet.{u}} [Y.Finite]
    (f : X ⟶ Z) (g : Y ⟶ Z) (x : |pullback f g|) :
    (finitePullbackHomeomorph f g x).val.1 = SSet.toTop.map (pullback.fst f g) x :=
  pullbackRealizationHomeomorph_fst f g _ _ _ x

@[simp] theorem finitePullbackHomeomorph_snd {X Y Z : SSet.{u}} [Y.Finite]
    (f : X ⟶ Z) (g : Y ⟶ Z) (x : |pullback f g|) :
    (finitePullbackHomeomorph f g x).val.2 = SSet.toTop.map (pullback.snd f g) x :=
  pullbackRealizationHomeomorph_snd f g _ _ _ x

end KIP126.Topology.SimplicialRealization
