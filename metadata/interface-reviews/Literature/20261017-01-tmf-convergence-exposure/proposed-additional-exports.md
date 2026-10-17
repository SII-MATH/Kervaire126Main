# 供人类选择的精确新增公开签名（未经批准）

JSON附件 SHA-256: `733e172b916e6e70adedb8d31e91e25d365a957b34c3b480bdbf170b329525a1`

原754导出保持；以下19项为唯一拟议附加范围，总数773。全部 universe parameters 为空。不能据本附件自动改变接口锁。

## KIP126.Literature.Standard.tmf_convergence._proof_1

type_fingerprint: `9307461684277026747`；universes: `[]`；capture kind: `generated`。

```lean
∀ (m : ℤ),
  Eq.{1}
    (CategoryTheory.CategoryStruct.comp.{0, 1}
      (ModuleCat.ofHom.{0, 0}
        (AddMonoidHom.toIntLinearMap.{0, 0}
          (KIP126.StableHomotopy.inducedMap.{1, 0} (CategoryTheory.Iso.hom.{0, 1} KIP126.Literature.Standard.tmfIso)
            m)))
      (ModuleCat.ofHom.{0, 0}
        (AddMonoidHom.toIntLinearMap.{0, 0}
          (KIP126.StableHomotopy.inducedMap.{1, 0} (CategoryTheory.Iso.inv.{0, 1} KIP126.Literature.Standard.tmfIso)
            m))))
    (CategoryTheory.CategoryStruct.id.{0, 1}
      (KIP126.AdamsSynthetic.AbstractAdamsTower.homotopy.{1, 0} KIP126.Literature.Standard.tmf m))
```

## KIP126.Literature.Standard.tmf_convergence._proof_2

type_fingerprint: `3266357727409569513`；universes: `[]`；capture kind: `generated`。

```lean
∀ (m : ℤ),
  Eq.{1}
    (CategoryTheory.CategoryStruct.comp.{0, 1}
      (ModuleCat.ofHom.{0, 0}
        (AddMonoidHom.toIntLinearMap.{0, 0}
          (KIP126.StableHomotopy.inducedMap.{1, 0} (CategoryTheory.Iso.inv.{0, 1} KIP126.Literature.Standard.tmfIso)
            m)))
      (ModuleCat.ofHom.{0, 0}
        (AddMonoidHom.toIntLinearMap.{0, 0}
          (KIP126.StableHomotopy.inducedMap.{1, 0} (CategoryTheory.Iso.hom.{0, 1} KIP126.Literature.Standard.tmfIso)
            m))))
    (CategoryTheory.CategoryStruct.id.{0, 1}
      (KIP126.AdamsSynthetic.AbstractAdamsTower.homotopy.{1, 0}
        (KIP126.Kervaire.Route.AuxiliaryData.detector.{1, 0}
          (KIP126.Kervaire.Route.ModelData.auxiliary.{1, 0, 1}
            (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1} KIP126.AdamsSynthetic.Standard.model)))
        m))
```

## KIP126.Literature.Standard.tmf_convergence._proof_3

type_fingerprint: `10580754988500988908`；universes: `[]`；capture kind: `generated`。

```lean
∀ (p : Prod.{0, 0} ℤ ℤ),
  Eq.{1}
    (CategoryTheory.CategoryStruct.comp.{0, 1}
      (KIP126.Core.SpectralSequence.SpectralSequenceMorphism.eInftyMap.{1, 0, 0}
        (KIP126.Classical.Adams.ClassicalAdamsFamily.map.{1, 0}
          (KIP126.Kervaire.Route.ModelData.classical.{1, 0, 1}
            (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1} KIP126.AdamsSynthetic.Standard.model))
          (CategoryTheory.Iso.hom.{0, 1} KIP126.Literature.Standard.tmfIso))
        p)
      (KIP126.Core.SpectralSequence.SpectralSequenceMorphism.eInftyMap.{1, 0, 0}
        (KIP126.Classical.Adams.ClassicalAdamsFamily.map.{1, 0}
          (KIP126.Kervaire.Route.ModelData.classical.{1, 0, 1}
            (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1} KIP126.AdamsSynthetic.Standard.model))
          (CategoryTheory.Iso.inv.{0, 1} KIP126.Literature.Standard.tmfIso))
        p))
    (CategoryTheory.CategoryStruct.id.{0, 1}
      (KIP126.Core.SpectralSequence.SSData.eInfty.{1, 0}
        (KIP126.Core.SpectralSequence.PreSS.ssData.{1, 0, 0}
          (KIP126.Core.SpectralSequence.toPreSS.{1, 0, 0}
            (KIP126.Classical.Adams.ClassicalAdamsFamily.obj.{1, 0}
              (KIP126.Kervaire.Route.ModelData.classical.{1, 0, 1}
                (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1} KIP126.AdamsSynthetic.Standard.model))
              KIP126.Literature.Standard.tmf))
          p)))
```

## KIP126.Literature.Standard.tmf_convergence._proof_4

type_fingerprint: `10172549857467399601`；universes: `[]`；capture kind: `generated`。

```lean
∀ (p : Prod.{0, 0} ℤ ℤ),
  Eq.{1}
    (CategoryTheory.CategoryStruct.comp.{0, 1}
      (KIP126.Core.SpectralSequence.SpectralSequenceMorphism.eInftyMap.{1, 0, 0}
        (KIP126.Classical.Adams.ClassicalAdamsFamily.map.{1, 0}
          (KIP126.Kervaire.Route.ModelData.classical.{1, 0, 1}
            (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1} KIP126.AdamsSynthetic.Standard.model))
          (CategoryTheory.Iso.inv.{0, 1} KIP126.Literature.Standard.tmfIso))
        p)
      (KIP126.Core.SpectralSequence.SpectralSequenceMorphism.eInftyMap.{1, 0, 0}
        (KIP126.Classical.Adams.ClassicalAdamsFamily.map.{1, 0}
          (KIP126.Kervaire.Route.ModelData.classical.{1, 0, 1}
            (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1} KIP126.AdamsSynthetic.Standard.model))
          (CategoryTheory.Iso.hom.{0, 1} KIP126.Literature.Standard.tmfIso))
        p))
    (CategoryTheory.CategoryStruct.id.{0, 1}
      (KIP126.Core.SpectralSequence.SSData.eInfty.{1, 0}
        (KIP126.Core.SpectralSequence.PreSS.ssData.{1, 0, 0}
          (KIP126.Core.SpectralSequence.toPreSS.{1, 0, 0}
            (KIP126.Classical.Adams.ClassicalAdamsFamily.obj.{1, 0}
              (KIP126.Kervaire.Route.ModelData.classical.{1, 0, 1}
                (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1} KIP126.AdamsSynthetic.Standard.model))
              (KIP126.Kervaire.Route.AuxiliaryData.detector.{1, 0}
                (KIP126.Kervaire.Route.ModelData.auxiliary.{1, 0, 1}
                  (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1} KIP126.AdamsSynthetic.Standard.model)))))
          p)))
```

## KIP126.Literature.Standard.tmf_convergence._proof_5

type_fingerprint: `6959415456206603119`；universes: `[]`；capture kind: `generated`。

```lean
∀ {X Y : KIP126.AdamsSynthetic.Standard.Spectrum} (f : Quiver.Hom.{0, 1} X Y) (s m : ℤ)
  (x : KIP126.StableHomotopy.HomotopyGroup.{1, 0} m X),
  Membership.mem.{0, 0}
      (KIP126.AdamsSynthetic.AbstractAdamsTower.filtrationSubmodule.{1, 0}
        (KIP126.AdamsSynthetic.ClassicalTowerPresentation.tower.{1, 0}
          (KIP126.Kervaire.Route.ModelData.classicalTower.{1, 0, 1}
            (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1} KIP126.AdamsSynthetic.Standard.model))
          X)
        s m)
      x →
    Membership.mem.{0, 0}
      (KIP126.AdamsSynthetic.AbstractAdamsTower.filtrationSubmodule.{1, 0}
        (KIP126.AdamsSynthetic.ClassicalTowerPresentation.tower.{1, 0}
          (KIP126.Kervaire.Route.ModelData.classicalTower.{1, 0, 1}
            (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1} KIP126.AdamsSynthetic.Standard.model))
          Y)
        s m)
      (CategoryTheory.CategoryStruct.comp.{0, 1} x f)
```

## KIP126.Literature.Standard.tmf_convergence._proof_6

type_fingerprint: `5327665652499015184`；universes: `[]`；capture kind: `generated`。

```lean
(∀ {X Y : KIP126.AdamsSynthetic.Standard.Spectrum} (f : Quiver.Hom.{0, 1} X Y) (s m : ℤ)
    (x : KIP126.StableHomotopy.HomotopyGroup.{1, 0} m X),
    Membership.mem.{0, 0}
        (KIP126.AdamsSynthetic.AbstractAdamsTower.filtrationSubmodule.{1, 0}
          (KIP126.AdamsSynthetic.ClassicalTowerPresentation.tower.{1, 0}
            (KIP126.Kervaire.Route.ModelData.classicalTower.{1, 0, 1}
              (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1} KIP126.AdamsSynthetic.Standard.model))
            X)
          s m)
        x →
      Membership.mem.{0, 0}
        (KIP126.AdamsSynthetic.AbstractAdamsTower.filtrationSubmodule.{1, 0}
          (KIP126.AdamsSynthetic.ClassicalTowerPresentation.tower.{1, 0}
            (KIP126.Kervaire.Route.ModelData.classicalTower.{1, 0, 1}
              (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1} KIP126.AdamsSynthetic.Standard.model))
            Y)
          s m)
        (CategoryTheory.CategoryStruct.comp.{0, 1} x f)) →
  ∀ {X Y : KIP126.AdamsSynthetic.Standard.Spectrum} (e : CategoryTheory.Iso.{0, 1} X Y) (s m : ℤ)
    (x : ↑(KIP126.AdamsSynthetic.AbstractAdamsTower.homotopy.{1, 0} X m)),
    Membership.mem.{0, 0}
        ((ModuleCat.subobjectModule.{0, 0} (KIP126.AdamsSynthetic.AbstractAdamsTower.homotopy.{1, 0} Y m))
          (KIP126.Core.SpectralSequence.Filtration.F.{1, 0, 0}
            (KIP126.AdamsSynthetic.AbstractAdamsTower.filtration.{1, 0}
              (KIP126.AdamsSynthetic.ClassicalTowerPresentation.tower.{1, 0}
                (KIP126.Kervaire.Route.ModelData.classicalTower.{1, 0, 1}
                  (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1} KIP126.AdamsSynthetic.Standard.model))
                Y))
            s m))
        (CategoryTheory.CategoryStruct.comp.{0, 1} x (CategoryTheory.Iso.hom.{0, 1} e)) ↔
      Membership.mem.{0, 0}
        ((ModuleCat.subobjectModule.{0, 0} (KIP126.AdamsSynthetic.AbstractAdamsTower.homotopy.{1, 0} X m))
          (KIP126.Core.SpectralSequence.Filtration.F.{1, 0, 0}
            (KIP126.AdamsSynthetic.AbstractAdamsTower.filtration.{1, 0}
              (KIP126.AdamsSynthetic.ClassicalTowerPresentation.tower.{1, 0}
                (KIP126.Kervaire.Route.ModelData.classicalTower.{1, 0, 1}
                  (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1} KIP126.AdamsSynthetic.Standard.model))
                X))
            s m))
        x
```

## KIP126.Literature.Standard.tmf_convergence._proof_7

type_fingerprint: `14718596544751197205`；universes: `[]`；capture kind: `generated`。

```lean
∀ {R : Type} [inst : Ring.{0} R], RingHomInvPair.{0, 0} (RingHom.id.{0} R) (RingHom.id.{0} R)
```

## KIP126.Literature.Standard.tmf_convergence._proof_8

type_fingerprint: `9125403165499682175`；universes: `[]`；capture kind: `generated`。

```lean
∀ {R : Type} [inst : Ring.{0} R] {M : ModuleCat.{0, 0} R} (B Z : CategoryTheory.Subobject.{0, 1} M) (h : LE.le.{1} B Z),
  CategoryTheory.Limits.HasColimit.{0, 0, 0, 1}
    (CategoryTheory.Limits.parallelPair.{0, 1} (CategoryTheory.Subobject.ofLE.{0, 1} B Z h) 0)
```

## KIP126.Literature.Standard.tmf_convergence._proof_9

type_fingerprint: `10166773359036421582`；universes: `[]`；capture kind: `generated`。

```lean
∀ {R : Type} [inst : Ring.{0} R] {M N : ModuleCat.{0, 0} R} (B Z : CategoryTheory.Subobject.{0, 1} M)
  (B' Z' : CategoryTheory.Subobject.{0, 1} N) (h : LE.le.{1} B Z) (h' : LE.le.{1} B' Z')
  (e : LinearEquiv.{0, 0, 0, 0} (RingHom.id.{0} R) ↑M ↑N),
  (∀ (x : ↑M),
      Membership.mem.{0, 0} ((ModuleCat.subobjectModule.{0, 0} N) B') (e x) ↔
        Membership.mem.{0, 0} ((ModuleCat.subobjectModule.{0, 0} M) B) x) →
    (∀ (x : ↑M),
        Membership.mem.{0, 0} ((ModuleCat.subobjectModule.{0, 0} N) Z') (e x) ↔
          Membership.mem.{0, 0} ((ModuleCat.subobjectModule.{0, 0} M) Z) x) →
      ∃ q,
        ∀ (a : ↑(CategoryTheory.Functor.obj.{1, 0, 1, 1} CategoryTheory.Subobject.underlying.{0, 1} Z)),
          ∃ b,
            Eq.{1} ((CategoryTheory.ConcreteCategory.hom.{0, 0, 1, 0} (CategoryTheory.Subobject.arrow.{0, 1} Z')) b)
                (e ((CategoryTheory.ConcreteCategory.hom.{0, 0, 1, 0} (CategoryTheory.Subobject.arrow.{0, 1} Z)) a)) ∧
              Eq.{1}
                ((CategoryTheory.ConcreteCategory.hom.{0, 0, 1, 0} (CategoryTheory.Iso.hom.{0, 1} q))
                  ((CategoryTheory.ConcreteCategory.hom.{0, 0, 1, 0}
                      (CategoryTheory.Limits.cokernel.π.{0, 1} (CategoryTheory.Subobject.ofLE.{0, 1} B Z h)))
                    a))
                ((CategoryTheory.ConcreteCategory.hom.{0, 0, 1, 0}
                    (CategoryTheory.Limits.cokernel.π.{0, 1} (CategoryTheory.Subobject.ofLE.{0, 1} B' Z' h')))
                  b)
```

## KIP126.Literature.Standard.tmf_convergence._proof_10

type_fingerprint: `10765865559627188234`；universes: `[]`；capture kind: `generated`。

```lean
∀ (s m : ℤ),
  LE.le.{1}
    (KIP126.Core.SpectralSequence.Filtration.F.{1, 0, 0}
      (KIP126.AdamsSynthetic.AbstractAdamsTower.filtration.{1, 0}
        (KIP126.AdamsSynthetic.ClassicalTowerPresentation.tower.{1, 0}
          (KIP126.Kervaire.Route.ModelData.classicalTower.{1, 0, 1}
            (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1} KIP126.AdamsSynthetic.Standard.model))
          KIP126.Literature.Standard.tmf))
      (HAdd.hAdd.{0, 0, 0} s 1) m)
    (KIP126.Core.SpectralSequence.Filtration.F.{1, 0, 0}
      (KIP126.AdamsSynthetic.AbstractAdamsTower.filtration.{1, 0}
        (KIP126.AdamsSynthetic.ClassicalTowerPresentation.tower.{1, 0}
          (KIP126.Kervaire.Route.ModelData.classicalTower.{1, 0, 1}
            (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1} KIP126.AdamsSynthetic.Standard.model))
          KIP126.Literature.Standard.tmf))
      s m)
```

## KIP126.Literature.Standard.tmf_convergence._proof_11

type_fingerprint: `8652705843332259721`；universes: `[]`；capture kind: `generated`。

```lean
∀ (s m : ℤ),
  CategoryTheory.Limits.HasColimit.{0, 0, 0, 1}
    (CategoryTheory.Limits.parallelPair.{0, 1}
      (CategoryTheory.Subobject.ofLE.{0, 1}
        (KIP126.Core.SpectralSequence.Filtration.F.{1, 0, 0}
          (KIP126.AdamsSynthetic.AbstractAdamsTower.filtration.{1, 0}
            (KIP126.AdamsSynthetic.ClassicalTowerPresentation.tower.{1, 0}
              (KIP126.Kervaire.Route.ModelData.classicalTower.{1, 0, 1}
                (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1} KIP126.AdamsSynthetic.Standard.model))
              KIP126.Literature.Standard.tmf))
          (HAdd.hAdd.{0, 0, 0} s 1) m)
        (KIP126.Core.SpectralSequence.Filtration.F.{1, 0, 0}
          (KIP126.AdamsSynthetic.AbstractAdamsTower.filtration.{1, 0}
            (KIP126.AdamsSynthetic.ClassicalTowerPresentation.tower.{1, 0}
              (KIP126.Kervaire.Route.ModelData.classicalTower.{1, 0, 1}
                (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1} KIP126.AdamsSynthetic.Standard.model))
              KIP126.Literature.Standard.tmf))
          s m)
        (KIP126.Literature.Standard.tmf_convergence._proof_10 s m))
      0)
```

## KIP126.Literature.Standard.tmf_convergence._proof_12

type_fingerprint: `2623149362275174052`；universes: `[]`；capture kind: `generated`。

```lean
∀ (s m : ℤ),
  LE.le.{1}
    (KIP126.Core.SpectralSequence.Filtration.F.{1, 0, 0}
      (KIP126.AdamsSynthetic.AbstractAdamsTower.filtration.{1, 0}
        (KIP126.AdamsSynthetic.ClassicalTowerPresentation.tower.{1, 0}
          (KIP126.Kervaire.Route.ModelData.classicalTower.{1, 0, 1}
            (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1} KIP126.AdamsSynthetic.Standard.model))
          (KIP126.Kervaire.Route.AuxiliaryData.detector.{1, 0}
            (KIP126.Kervaire.Route.ModelData.auxiliary.{1, 0, 1}
              (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1} KIP126.AdamsSynthetic.Standard.model)))))
      (HAdd.hAdd.{0, 0, 0} s 1) m)
    (KIP126.Core.SpectralSequence.Filtration.F.{1, 0, 0}
      (KIP126.AdamsSynthetic.AbstractAdamsTower.filtration.{1, 0}
        (KIP126.AdamsSynthetic.ClassicalTowerPresentation.tower.{1, 0}
          (KIP126.Kervaire.Route.ModelData.classicalTower.{1, 0, 1}
            (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1} KIP126.AdamsSynthetic.Standard.model))
          (KIP126.Kervaire.Route.AuxiliaryData.detector.{1, 0}
            (KIP126.Kervaire.Route.ModelData.auxiliary.{1, 0, 1}
              (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1} KIP126.AdamsSynthetic.Standard.model)))))
      s m)
```

## KIP126.Literature.Standard.tmf_convergence._proof_13

type_fingerprint: `10215788166765288462`；universes: `[]`；capture kind: `generated`。

```lean
∀ (s m : ℤ),
  CategoryTheory.Limits.HasColimit.{0, 0, 0, 1}
    (CategoryTheory.Limits.parallelPair.{0, 1}
      (CategoryTheory.Subobject.ofLE.{0, 1}
        (KIP126.Core.SpectralSequence.Filtration.F.{1, 0, 0}
          (KIP126.AdamsSynthetic.AbstractAdamsTower.filtration.{1, 0}
            (KIP126.AdamsSynthetic.ClassicalTowerPresentation.tower.{1, 0}
              (KIP126.Kervaire.Route.ModelData.classicalTower.{1, 0, 1}
                (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1} KIP126.AdamsSynthetic.Standard.model))
              (KIP126.Kervaire.Route.AuxiliaryData.detector.{1, 0}
                (KIP126.Kervaire.Route.ModelData.auxiliary.{1, 0, 1}
                  (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1} KIP126.AdamsSynthetic.Standard.model)))))
          (HAdd.hAdd.{0, 0, 0} s 1) m)
        (KIP126.Core.SpectralSequence.Filtration.F.{1, 0, 0}
          (KIP126.AdamsSynthetic.AbstractAdamsTower.filtration.{1, 0}
            (KIP126.AdamsSynthetic.ClassicalTowerPresentation.tower.{1, 0}
              (KIP126.Kervaire.Route.ModelData.classicalTower.{1, 0, 1}
                (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1} KIP126.AdamsSynthetic.Standard.model))
              (KIP126.Kervaire.Route.AuxiliaryData.detector.{1, 0}
                (KIP126.Kervaire.Route.ModelData.auxiliary.{1, 0, 1}
                  (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1} KIP126.AdamsSynthetic.Standard.model)))))
          s m)
        (KIP126.Literature.Standard.tmf_convergence._proof_12 s m))
      0)
```

## KIP126.Literature.Standard.tmf_convergence._proof_14

type_fingerprint: `16698574928565675964`；universes: `[]`；capture kind: `generated`。

```lean
RingHomInvPair.{0, 0} (RingHom.id.{0} ℤ) (RingHom.id.{0} ℤ)
```

## KIP126.Literature.Standard.tmf_convergence._proof_15

type_fingerprint: `199771240247710024`；universes: `[]`；capture kind: `generated`。

```lean
(∀ {X Y : KIP126.AdamsSynthetic.Standard.Spectrum} (e : CategoryTheory.Iso.{0, 1} X Y) (s m : ℤ)
    (x : ↑(KIP126.AdamsSynthetic.AbstractAdamsTower.homotopy.{1, 0} X m)),
    Membership.mem.{0, 0}
        ((ModuleCat.subobjectModule.{0, 0} (KIP126.AdamsSynthetic.AbstractAdamsTower.homotopy.{1, 0} Y m))
          (KIP126.Core.SpectralSequence.Filtration.F.{1, 0, 0}
            (KIP126.AdamsSynthetic.AbstractAdamsTower.filtration.{1, 0}
              (KIP126.AdamsSynthetic.ClassicalTowerPresentation.tower.{1, 0}
                (KIP126.Kervaire.Route.ModelData.classicalTower.{1, 0, 1}
                  (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1} KIP126.AdamsSynthetic.Standard.model))
                Y))
            s m))
        (CategoryTheory.CategoryStruct.comp.{0, 1} x (CategoryTheory.Iso.hom.{0, 1} e)) ↔
      Membership.mem.{0, 0}
        ((ModuleCat.subobjectModule.{0, 0} (KIP126.AdamsSynthetic.AbstractAdamsTower.homotopy.{1, 0} X m))
          (KIP126.Core.SpectralSequence.Filtration.F.{1, 0, 0}
            (KIP126.AdamsSynthetic.AbstractAdamsTower.filtration.{1, 0}
              (KIP126.AdamsSynthetic.ClassicalTowerPresentation.tower.{1, 0}
                (KIP126.Kervaire.Route.ModelData.classicalTower.{1, 0, 1}
                  (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1} KIP126.AdamsSynthetic.Standard.model))
                X))
            s m))
        x) →
  (∀ {R : Type} [inst : Ring.{0} R] {M N : ModuleCat.{0, 0} R} (B Z : CategoryTheory.Subobject.{0, 1} M)
      (B' Z' : CategoryTheory.Subobject.{0, 1} N) (h : LE.le.{1} B Z) (h' : LE.le.{1} B' Z')
      (e : LinearEquiv.{0, 0, 0, 0} (RingHom.id.{0} R) ↑M ↑N),
      (∀ (x : ↑M),
          Membership.mem.{0, 0} ((ModuleCat.subobjectModule.{0, 0} N) B') (e x) ↔
            Membership.mem.{0, 0} ((ModuleCat.subobjectModule.{0, 0} M) B) x) →
        (∀ (x : ↑M),
            Membership.mem.{0, 0} ((ModuleCat.subobjectModule.{0, 0} N) Z') (e x) ↔
              Membership.mem.{0, 0} ((ModuleCat.subobjectModule.{0, 0} M) Z) x) →
          ∃ q,
            ∀ (a : ↑(CategoryTheory.Functor.obj.{1, 0, 1, 1} CategoryTheory.Subobject.underlying.{0, 1} Z)),
              ∃ b,
                Eq.{1} ((CategoryTheory.ConcreteCategory.hom.{0, 0, 1, 0} (CategoryTheory.Subobject.arrow.{0, 1} Z')) b)
                    (e
                      ((CategoryTheory.ConcreteCategory.hom.{0, 0, 1, 0} (CategoryTheory.Subobject.arrow.{0, 1} Z))
                        a)) ∧
                  Eq.{1}
                    ((CategoryTheory.ConcreteCategory.hom.{0, 0, 1, 0} (CategoryTheory.Iso.hom.{0, 1} q))
                      ((CategoryTheory.ConcreteCategory.hom.{0, 0, 1, 0}
                          (CategoryTheory.Limits.cokernel.π.{0, 1} (CategoryTheory.Subobject.ofLE.{0, 1} B Z h)))
                        a))
                    ((CategoryTheory.ConcreteCategory.hom.{0, 0, 1, 0}
                        (CategoryTheory.Limits.cokernel.π.{0, 1} (CategoryTheory.Subobject.ofLE.{0, 1} B' Z' h')))
                      b)) →
    ∀ (s m : ℤ),
      ∃ q,
        ∀
          (a :
            ↑(CategoryTheory.Functor.obj.{1, 0, 1, 1} CategoryTheory.Subobject.underlying.{0, 1}
                (KIP126.Core.SpectralSequence.Filtration.F.{1, 0, 0}
                  (KIP126.AdamsSynthetic.AbstractAdamsTower.filtration.{1, 0}
                    (KIP126.AdamsSynthetic.ClassicalTowerPresentation.tower.{1, 0}
                      (KIP126.Kervaire.Route.ModelData.classicalTower.{1, 0, 1}
                        (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1} KIP126.AdamsSynthetic.Standard.model))
                      KIP126.Literature.Standard.tmf))
                  s m))),
          ∃ b,
            Eq.{1}
                ((CategoryTheory.ConcreteCategory.hom.{0, 0, 1, 0}
                    (CategoryTheory.Subobject.arrow.{0, 1}
                      (KIP126.Core.SpectralSequence.Filtration.F.{1, 0, 0}
                        (KIP126.AdamsSynthetic.AbstractAdamsTower.filtration.{1, 0}
                          (KIP126.AdamsSynthetic.ClassicalTowerPresentation.tower.{1, 0}
                            (KIP126.Kervaire.Route.ModelData.classicalTower.{1, 0, 1}
                              (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1} KIP126.AdamsSynthetic.Standard.model))
                            (KIP126.Kervaire.Route.AuxiliaryData.detector.{1, 0}
                              (KIP126.Kervaire.Route.ModelData.auxiliary.{1, 0, 1}
                                (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1}
                                  KIP126.AdamsSynthetic.Standard.model)))))
                        s m)))
                  b)
                ((CategoryTheory.Iso.toLinearEquiv.{0, 0}
                    (CategoryTheory.Iso.mk.{0, 1}
                      (ModuleCat.ofHom.{0, 0}
                        (AddMonoidHom.toIntLinearMap.{0, 0}
                          (KIP126.StableHomotopy.inducedMap.{1, 0}
                            (CategoryTheory.Iso.hom.{0, 1} KIP126.Literature.Standard.tmfIso) m)))
                      (ModuleCat.ofHom.{0, 0}
                        (AddMonoidHom.toIntLinearMap.{0, 0}
                          (KIP126.StableHomotopy.inducedMap.{1, 0}
                            (CategoryTheory.Iso.inv.{0, 1} KIP126.Literature.Standard.tmfIso) m)))
                      (KIP126.Literature.Standard.tmf_convergence._proof_1 m)
                      (KIP126.Literature.Standard.tmf_convergence._proof_2 m)))
                  ((CategoryTheory.ConcreteCategory.hom.{0, 0, 1, 0}
                      (CategoryTheory.Subobject.arrow.{0, 1}
                        (KIP126.Core.SpectralSequence.Filtration.F.{1, 0, 0}
                          (KIP126.AdamsSynthetic.AbstractAdamsTower.filtration.{1, 0}
                            (KIP126.AdamsSynthetic.ClassicalTowerPresentation.tower.{1, 0}
                              (KIP126.Kervaire.Route.ModelData.classicalTower.{1, 0, 1}
                                (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1}
                                  KIP126.AdamsSynthetic.Standard.model))
                              KIP126.Literature.Standard.tmf))
                          s m)))
                    a)) ∧
              Eq.{1}
                ((CategoryTheory.ConcreteCategory.hom.{0, 0, 1, 0} (CategoryTheory.Iso.hom.{0, 1} q))
                  ((CategoryTheory.ConcreteCategory.hom.{0, 0, 1, 0}
                      (CategoryTheory.Limits.cokernel.π.{0, 1}
                        (CategoryTheory.Subobject.ofLE.{0, 1}
                          (KIP126.Core.SpectralSequence.Filtration.F.{1, 0, 0}
                            (KIP126.AdamsSynthetic.AbstractAdamsTower.filtration.{1, 0}
                              (KIP126.AdamsSynthetic.ClassicalTowerPresentation.tower.{1, 0}
                                (KIP126.Kervaire.Route.ModelData.classicalTower.{1, 0, 1}
                                  (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1}
                                    KIP126.AdamsSynthetic.Standard.model))
                                KIP126.Literature.Standard.tmf))
                            (HAdd.hAdd.{0, 0, 0} s 1) m)
                          (KIP126.Core.SpectralSequence.Filtration.F.{1, 0, 0}
                            (KIP126.AdamsSynthetic.AbstractAdamsTower.filtration.{1, 0}
                              (KIP126.AdamsSynthetic.ClassicalTowerPresentation.tower.{1, 0}
                                (KIP126.Kervaire.Route.ModelData.classicalTower.{1, 0, 1}
                                  (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1}
                                    KIP126.AdamsSynthetic.Standard.model))
                                KIP126.Literature.Standard.tmf))
                            s m)
                          (KIP126.Literature.Standard.tmf_convergence._proof_10 s m))))
                    a))
                ((CategoryTheory.ConcreteCategory.hom.{0, 0, 1, 0}
                    (CategoryTheory.Limits.cokernel.π.{0, 1}
                      (CategoryTheory.Subobject.ofLE.{0, 1}
                        (KIP126.Core.SpectralSequence.Filtration.F.{1, 0, 0}
                          (KIP126.AdamsSynthetic.AbstractAdamsTower.filtration.{1, 0}
                            (KIP126.AdamsSynthetic.ClassicalTowerPresentation.tower.{1, 0}
                              (KIP126.Kervaire.Route.ModelData.classicalTower.{1, 0, 1}
                                (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1}
                                  KIP126.AdamsSynthetic.Standard.model))
                              (KIP126.Kervaire.Route.AuxiliaryData.detector.{1, 0}
                                (KIP126.Kervaire.Route.ModelData.auxiliary.{1, 0, 1}
                                  (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1}
                                    KIP126.AdamsSynthetic.Standard.model)))))
                          (HAdd.hAdd.{0, 0, 0} s 1) m)
                        (KIP126.Core.SpectralSequence.Filtration.F.{1, 0, 0}
                          (KIP126.AdamsSynthetic.AbstractAdamsTower.filtration.{1, 0}
                            (KIP126.AdamsSynthetic.ClassicalTowerPresentation.tower.{1, 0}
                              (KIP126.Kervaire.Route.ModelData.classicalTower.{1, 0, 1}
                                (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1}
                                  KIP126.AdamsSynthetic.Standard.model))
                              (KIP126.Kervaire.Route.AuxiliaryData.detector.{1, 0}
                                (KIP126.Kervaire.Route.ModelData.auxiliary.{1, 0, 1}
                                  (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1}
                                    KIP126.AdamsSynthetic.Standard.model)))))
                          s m)
                        (KIP126.Literature.Standard.tmf_convergence._proof_12 s m))))
                  b)
```

## KIP126.Literature.Standard.tmf_convergence._proof_16

type_fingerprint: `5066765771609085539`；universes: `[]`；capture kind: `generated`。

```lean
Eq.{1}
  (KIP126.Core.SpectralSequence.PreSS.r₀.{1, 0, 0}
    (KIP126.Core.SpectralSequence.toPreSS.{1, 0, 0}
      (CategoryTheory.Functor.obj.{0, 0, 1, 1}
        (KIP126.Classical.Adams.ClassicalAdamsFamily.functor.{1, 0}
          (KIP126.Kervaire.Route.ModelData.classical.{1, 0, 1}
            (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1} KIP126.AdamsSynthetic.Standard.model)))
        KIP126.Literature.Standard.tmf)))
  2
```

## KIP126.Literature.Standard.tmf_convergence._proof_17

type_fingerprint: `12807507390798102435`；universes: `[]`；capture kind: `generated`。

```lean
∀ (r : ℤ),
  Eq.{1}
    (KIP126.Core.SpectralSequence.PreSS.diffDeg.{1, 0, 0}
      (KIP126.Core.SpectralSequence.toPreSS.{1, 0, 0}
        (CategoryTheory.Functor.obj.{0, 0, 1, 1}
          (KIP126.Classical.Adams.ClassicalAdamsFamily.functor.{1, 0}
            (KIP126.Kervaire.Route.ModelData.classical.{1, 0, 1}
              (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1} KIP126.AdamsSynthetic.Standard.model)))
          KIP126.Literature.Standard.tmf))
      r)
    (Prod.mk.{0, 0} r (HSub.hSub.{0, 0, 0} r 1))
```

## KIP126.Literature.Standard.tmf_convergence._proof_18

type_fingerprint: `8897409890030837039`；universes: `[]`；capture kind: `generated`。

```lean
(∀ (s m : ℤ),
    ∃ q,
      ∀
        (b :
          ↑(CategoryTheory.Functor.obj.{1, 0, 1, 1} CategoryTheory.Subobject.underlying.{0, 1}
              (KIP126.Core.SpectralSequence.Filtration.F.{1, 0, 0}
                (KIP126.AdamsSynthetic.AbstractAdamsTower.filtration.{1, 0}
                  (KIP126.AdamsSynthetic.ClassicalTowerPresentation.tower.{1, 0}
                    (KIP126.Kervaire.Route.ModelData.classicalTower.{1, 0, 1}
                      (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1} KIP126.AdamsSynthetic.Standard.model))
                    KIP126.Literature.Standard.tmf))
                s m))),
        ∃ b',
          Eq.{1}
              ((CategoryTheory.ConcreteCategory.hom.{0, 0, 1, 0}
                  (CategoryTheory.Subobject.arrow.{0, 1}
                    (KIP126.Core.SpectralSequence.Filtration.F.{1, 0, 0}
                      (KIP126.AdamsSynthetic.AbstractAdamsTower.filtration.{1, 0}
                        (KIP126.AdamsSynthetic.ClassicalTowerPresentation.tower.{1, 0}
                          (KIP126.Kervaire.Route.ModelData.classicalTower.{1, 0, 1}
                            (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1} KIP126.AdamsSynthetic.Standard.model))
                          (KIP126.Kervaire.Route.AuxiliaryData.detector.{1, 0}
                            (KIP126.Kervaire.Route.ModelData.auxiliary.{1, 0, 1}
                              (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1}
                                KIP126.AdamsSynthetic.Standard.model)))))
                      s m)))
                b')
              (CategoryTheory.CategoryStruct.comp.{0, 1}
                ((CategoryTheory.ConcreteCategory.hom.{0, 0, 1, 0}
                    (CategoryTheory.Subobject.arrow.{0, 1}
                      (KIP126.Core.SpectralSequence.Filtration.F.{1, 0, 0}
                        (KIP126.AdamsSynthetic.AbstractAdamsTower.filtration.{1, 0}
                          (KIP126.AdamsSynthetic.ClassicalTowerPresentation.tower.{1, 0}
                            (KIP126.Kervaire.Route.ModelData.classicalTower.{1, 0, 1}
                              (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1} KIP126.AdamsSynthetic.Standard.model))
                            KIP126.Literature.Standard.tmf))
                        s m)))
                  b)
                (CategoryTheory.Iso.hom.{0, 1} KIP126.Literature.Standard.tmfIso)) ∧
            Eq.{1}
              ((CategoryTheory.ConcreteCategory.hom.{0, 0, 1, 0} (CategoryTheory.Iso.hom.{0, 1} q))
                ((CategoryTheory.ConcreteCategory.hom.{0, 0, 1, 0}
                    (KIP126.Core.SpectralSequence.Filtration.toAssociatedGraded.{1, 0, 0}
                      (KIP126.AdamsSynthetic.AbstractAdamsTower.filtration.{1, 0}
                        (KIP126.AdamsSynthetic.ClassicalTowerPresentation.tower.{1, 0}
                          (KIP126.Kervaire.Route.ModelData.classicalTower.{1, 0, 1}
                            (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1} KIP126.AdamsSynthetic.Standard.model))
                          KIP126.Literature.Standard.tmf))
                      s m))
                  b))
              ((CategoryTheory.ConcreteCategory.hom.{0, 0, 1, 0}
                  (KIP126.Core.SpectralSequence.Filtration.toAssociatedGraded.{1, 0, 0}
                    (KIP126.AdamsSynthetic.AbstractAdamsTower.filtration.{1, 0}
                      (KIP126.AdamsSynthetic.ClassicalTowerPresentation.tower.{1, 0}
                        (KIP126.Kervaire.Route.ModelData.classicalTower.{1, 0, 1}
                          (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1} KIP126.AdamsSynthetic.Standard.model))
                        (KIP126.Kervaire.Route.AuxiliaryData.detector.{1, 0}
                          (KIP126.Kervaire.Route.ModelData.auxiliary.{1, 0, 1}
                            (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1} KIP126.AdamsSynthetic.Standard.model)))))
                    s m))
                b')) →
  ∀ (p : Prod.{0, 0} ℤ ℤ),
    ∃ q,
      ∀
        (b :
          ↑(CategoryTheory.Functor.obj.{1, 0, 1, 1} CategoryTheory.Subobject.underlying.{0, 1}
              (KIP126.Core.SpectralSequence.Filtration.F.{1, 0, 0}
                (KIP126.AdamsSynthetic.AbstractAdamsTower.filtration.{1, 0}
                  (KIP126.AdamsSynthetic.ClassicalTowerPresentation.tower.{1, 0}
                    (KIP126.Kervaire.Route.ModelData.classicalTower.{1, 0, 1}
                      (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1} KIP126.AdamsSynthetic.Standard.model))
                    KIP126.Literature.Standard.tmf))
                p.1 (HSub.hSub.{0, 0, 0} p.2 p.1)))),
        ∃ b',
          Eq.{1}
              ((CategoryTheory.ConcreteCategory.hom.{0, 0, 1, 0}
                  (CategoryTheory.Subobject.arrow.{0, 1}
                    (KIP126.Core.SpectralSequence.Filtration.F.{1, 0, 0}
                      (KIP126.AdamsSynthetic.AbstractAdamsTower.filtration.{1, 0}
                        (KIP126.AdamsSynthetic.ClassicalTowerPresentation.tower.{1, 0}
                          (KIP126.Kervaire.Route.ModelData.classicalTower.{1, 0, 1}
                            (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1} KIP126.AdamsSynthetic.Standard.model))
                          (KIP126.Kervaire.Route.AuxiliaryData.detector.{1, 0}
                            (KIP126.Kervaire.Route.ModelData.auxiliary.{1, 0, 1}
                              (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1}
                                KIP126.AdamsSynthetic.Standard.model)))))
                      p.1 (HSub.hSub.{0, 0, 0} p.2 p.1))))
                b')
              (CategoryTheory.CategoryStruct.comp.{0, 1}
                ((CategoryTheory.ConcreteCategory.hom.{0, 0, 1, 0}
                    (CategoryTheory.Subobject.arrow.{0, 1}
                      (KIP126.Core.SpectralSequence.Filtration.F.{1, 0, 0}
                        (KIP126.AdamsSynthetic.AbstractAdamsTower.filtration.{1, 0}
                          (KIP126.AdamsSynthetic.ClassicalTowerPresentation.tower.{1, 0}
                            (KIP126.Kervaire.Route.ModelData.classicalTower.{1, 0, 1}
                              (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1} KIP126.AdamsSynthetic.Standard.model))
                            KIP126.Literature.Standard.tmf))
                        p.1 (HSub.hSub.{0, 0, 0} p.2 p.1))))
                  b)
                (CategoryTheory.Iso.hom.{0, 1} KIP126.Literature.Standard.tmfIso)) ∧
            Eq.{1}
              ((CategoryTheory.ConcreteCategory.hom.{0, 0, 1, 0} (CategoryTheory.Iso.hom.{0, 1} q))
                ((CategoryTheory.ConcreteCategory.hom.{0, 0, 1, 0}
                    (KIP126.Core.SpectralSequence.Filtration.toAssociatedGraded.{1, 0, 0}
                      (KIP126.AdamsSynthetic.AbstractAdamsTower.filtration.{1, 0}
                        (KIP126.AdamsSynthetic.ClassicalTowerPresentation.tower.{1, 0}
                          (KIP126.Kervaire.Route.ModelData.classicalTower.{1, 0, 1}
                            (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1} KIP126.AdamsSynthetic.Standard.model))
                          KIP126.Literature.Standard.tmf))
                      p.1 (HSub.hSub.{0, 0, 0} p.2 p.1)))
                  b))
              ((CategoryTheory.ConcreteCategory.hom.{0, 0, 1, 0}
                  (KIP126.Core.SpectralSequence.Filtration.toAssociatedGraded.{1, 0, 0}
                    (KIP126.AdamsSynthetic.AbstractAdamsTower.filtration.{1, 0}
                      (KIP126.AdamsSynthetic.ClassicalTowerPresentation.tower.{1, 0}
                        (KIP126.Kervaire.Route.ModelData.classicalTower.{1, 0, 1}
                          (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1} KIP126.AdamsSynthetic.Standard.model))
                        (KIP126.Kervaire.Route.AuxiliaryData.detector.{1, 0}
                          (KIP126.Kervaire.Route.ModelData.auxiliary.{1, 0, 1}
                            (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1} KIP126.AdamsSynthetic.Standard.model)))))
                    p.1 (HSub.hSub.{0, 0, 0} p.2 p.1)))
                b')
```

## KIP126.Literature.Standard.tmf_convergence._proof_19

type_fingerprint: `5711257927081125987`；universes: `[]`；capture kind: `generated`。

```lean
∀
  (gr :
    ∀ (s m : ℤ),
      ∃ q,
        ∀
          (b :
            ↑(CategoryTheory.Functor.obj.{1, 0, 1, 1} CategoryTheory.Subobject.underlying.{0, 1}
                (KIP126.Core.SpectralSequence.Filtration.F.{1, 0, 0}
                  (KIP126.AdamsSynthetic.AbstractAdamsTower.filtration.{1, 0}
                    (KIP126.AdamsSynthetic.ClassicalTowerPresentation.tower.{1, 0}
                      (KIP126.Kervaire.Route.ModelData.classicalTower.{1, 0, 1}
                        (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1} KIP126.AdamsSynthetic.Standard.model))
                      KIP126.Literature.Standard.tmf))
                  s m))),
          ∃ b',
            Eq.{1}
                ((CategoryTheory.ConcreteCategory.hom.{0, 0, 1, 0}
                    (CategoryTheory.Subobject.arrow.{0, 1}
                      (KIP126.Core.SpectralSequence.Filtration.F.{1, 0, 0}
                        (KIP126.AdamsSynthetic.AbstractAdamsTower.filtration.{1, 0}
                          (KIP126.AdamsSynthetic.ClassicalTowerPresentation.tower.{1, 0}
                            (KIP126.Kervaire.Route.ModelData.classicalTower.{1, 0, 1}
                              (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1} KIP126.AdamsSynthetic.Standard.model))
                            (KIP126.Kervaire.Route.AuxiliaryData.detector.{1, 0}
                              (KIP126.Kervaire.Route.ModelData.auxiliary.{1, 0, 1}
                                (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1}
                                  KIP126.AdamsSynthetic.Standard.model)))))
                        s m)))
                  b')
                (CategoryTheory.CategoryStruct.comp.{0, 1}
                  ((CategoryTheory.ConcreteCategory.hom.{0, 0, 1, 0}
                      (CategoryTheory.Subobject.arrow.{0, 1}
                        (KIP126.Core.SpectralSequence.Filtration.F.{1, 0, 0}
                          (KIP126.AdamsSynthetic.AbstractAdamsTower.filtration.{1, 0}
                            (KIP126.AdamsSynthetic.ClassicalTowerPresentation.tower.{1, 0}
                              (KIP126.Kervaire.Route.ModelData.classicalTower.{1, 0, 1}
                                (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1}
                                  KIP126.AdamsSynthetic.Standard.model))
                              KIP126.Literature.Standard.tmf))
                          s m)))
                    b)
                  (CategoryTheory.Iso.hom.{0, 1} KIP126.Literature.Standard.tmfIso)) ∧
              Eq.{1}
                ((CategoryTheory.ConcreteCategory.hom.{0, 0, 1, 0} (CategoryTheory.Iso.hom.{0, 1} q))
                  ((CategoryTheory.ConcreteCategory.hom.{0, 0, 1, 0}
                      (KIP126.Core.SpectralSequence.Filtration.toAssociatedGraded.{1, 0, 0}
                        (KIP126.AdamsSynthetic.AbstractAdamsTower.filtration.{1, 0}
                          (KIP126.AdamsSynthetic.ClassicalTowerPresentation.tower.{1, 0}
                            (KIP126.Kervaire.Route.ModelData.classicalTower.{1, 0, 1}
                              (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1} KIP126.AdamsSynthetic.Standard.model))
                            KIP126.Literature.Standard.tmf))
                        s m))
                    b))
                ((CategoryTheory.ConcreteCategory.hom.{0, 0, 1, 0}
                    (KIP126.Core.SpectralSequence.Filtration.toAssociatedGraded.{1, 0, 0}
                      (KIP126.AdamsSynthetic.AbstractAdamsTower.filtration.{1, 0}
                        (KIP126.AdamsSynthetic.ClassicalTowerPresentation.tower.{1, 0}
                          (KIP126.Kervaire.Route.ModelData.classicalTower.{1, 0, 1}
                            (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1} KIP126.AdamsSynthetic.Standard.model))
                          (KIP126.Kervaire.Route.AuxiliaryData.detector.{1, 0}
                            (KIP126.Kervaire.Route.ModelData.auxiliary.{1, 0, 1}
                              (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1}
                                KIP126.AdamsSynthetic.Standard.model)))))
                      s m))
                  b'))
  (p : Prod.{0, 0} ℤ ℤ)
  (a :
    KIP126.StableHomotopy.HomotopyGroup.{1, 0} (HSub.hSub.{0, 0, 0} p.2 p.1)
      (KIP126.AdamsSynthetic.AbstractAdamsTower.stageAt.{1, 0}
        (KIP126.AdamsSynthetic.ClassicalTowerPresentation.tower.{1, 0}
          (KIP126.Kervaire.Route.ModelData.classicalTower.{1, 0, 1}
            (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1} KIP126.AdamsSynthetic.Standard.model))
          KIP126.Literature.Standard.tmf)
        p.1))
  (z :
    ↑(CategoryTheory.Functor.obj.{1, 0, 1, 1} CategoryTheory.Subobject.underlying.{0, 1}
        (KIP126.Core.SpectralSequence.SSData.Z.{1, 0}
          (KIP126.Core.SpectralSequence.PreSS.ssData.{1, 0, 0}
            (KIP126.Core.SpectralSequence.toPreSS.{1, 0, 0}
              (KIP126.Classical.Adams.ClassicalAdamsFamily.obj.{1, 0}
                (KIP126.Kervaire.Route.ModelData.classical.{1, 0, 1}
                  (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1} KIP126.AdamsSynthetic.Standard.model))
                KIP126.Literature.Standard.tmf))
            p)
          Top.top.{0}))),
  Eq.{1}
      (KIP126.AdamsSynthetic.TowerSequencePresentation.infiniteRepresentativeE1.{1, 0}
        (KIP126.AdamsSynthetic.ClassicalTowerPresentation.sequence.{1, 0}
          (KIP126.Kervaire.Route.ModelData.classicalTower.{1, 0, 1}
            (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1} KIP126.AdamsSynthetic.Standard.model))
          KIP126.Literature.Standard.tmf)
        p z)
      ((KIP126.AdamsSynthetic.AbstractAdamsTower.layerMap.{1, 0}
          (KIP126.AdamsSynthetic.ClassicalTowerPresentation.tower.{1, 0}
            (KIP126.Kervaire.Route.ModelData.classicalTower.{1, 0, 1}
              (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1} KIP126.AdamsSynthetic.Standard.model))
            KIP126.Literature.Standard.tmf)
          p)
        a) →
    ∀
      (b :
        ↑(CategoryTheory.Functor.obj.{1, 0, 1, 1} CategoryTheory.Subobject.underlying.{0, 1}
            (KIP126.Core.SpectralSequence.Filtration.F.{1, 0, 0}
              (KIP126.AdamsSynthetic.AbstractAdamsTower.filtration.{1, 0}
                (KIP126.AdamsSynthetic.ClassicalTowerPresentation.tower.{1, 0}
                  (KIP126.Kervaire.Route.ModelData.classicalTower.{1, 0, 1}
                    (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1} KIP126.AdamsSynthetic.Standard.model))
                  KIP126.Literature.Standard.tmf))
              p.1 (HSub.hSub.{0, 0, 0} p.2 p.1)))),
      Eq.{1}
          ((CategoryTheory.ConcreteCategory.hom.{0, 0, 1, 0}
              (CategoryTheory.Subobject.arrow.{0, 1}
                (KIP126.Core.SpectralSequence.Filtration.F.{1, 0, 0}
                  (KIP126.AdamsSynthetic.AbstractAdamsTower.filtration.{1, 0}
                    (KIP126.AdamsSynthetic.ClassicalTowerPresentation.tower.{1, 0}
                      (KIP126.Kervaire.Route.ModelData.classicalTower.{1, 0, 1}
                        (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1} KIP126.AdamsSynthetic.Standard.model))
                      KIP126.Literature.Standard.tmf))
                  p.1 (HSub.hSub.{0, 0, 0} p.2 p.1))))
            b)
          (CategoryTheory.CategoryStruct.comp.{0, 1} a
            (KIP126.AdamsSynthetic.AbstractAdamsTower.projection.{1, 0}
              (KIP126.AdamsSynthetic.ClassicalTowerPresentation.tower.{1, 0}
                (KIP126.Kervaire.Route.ModelData.classicalTower.{1, 0, 1}
                  (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1} KIP126.AdamsSynthetic.Standard.model))
                KIP126.Literature.Standard.tmf)
              p.1)) →
        Eq.{1}
          ((CategoryTheory.ConcreteCategory.hom.{0, 0, 1, 0}
              (CategoryTheory.Iso.hom.{0, 1}
                (CategoryTheory.Iso.trans.{0, 1}
                  (CategoryTheory.Iso.mk.{0, 1}
                    (KIP126.Core.SpectralSequence.SpectralSequenceMorphism.eInftyMap.{1, 0, 0}
                      (KIP126.Classical.Adams.ClassicalAdamsFamily.map.{1, 0}
                        (KIP126.Kervaire.Route.ModelData.classical.{1, 0, 1}
                          (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1} KIP126.AdamsSynthetic.Standard.model))
                        (CategoryTheory.Iso.hom.{0, 1} KIP126.Literature.Standard.tmfIso))
                      p)
                    (KIP126.Core.SpectralSequence.SpectralSequenceMorphism.eInftyMap.{1, 0, 0}
                      (KIP126.Classical.Adams.ClassicalAdamsFamily.map.{1, 0}
                        (KIP126.Kervaire.Route.ModelData.classical.{1, 0, 1}
                          (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1} KIP126.AdamsSynthetic.Standard.model))
                        (CategoryTheory.Iso.inv.{0, 1} KIP126.Literature.Standard.tmfIso))
                      p)
                    (KIP126.Literature.Standard.tmf_convergence._proof_3 p)
                    (KIP126.Literature.Standard.tmf_convergence._proof_4 p))
                  (CategoryTheory.Iso.trans.{0, 1}
                    (KIP126.AdamsSynthetic.ClassicalTowerConvergence.identification.{1, 0}
                      (KIP126.Kervaire.Route.ModelData.classicalConvergence.{1, 0, 1}
                        (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1} KIP126.AdamsSynthetic.Standard.model)
                        KIP126.Kervaire.Route.ClassicalObject.detector)
                      p)
                    (CategoryTheory.Iso.symm.{0, 1}
                      (Exists.choose.{1} (KIP126.Literature.Standard.tmf_convergence._proof_18 gr p)))))))
            ((CategoryTheory.ConcreteCategory.hom.{0, 0, 1, 0}
                (KIP126.Core.SpectralSequence.SSData.pageπ.{1, 0}
                  (KIP126.Core.SpectralSequence.PreSS.ssData.{1, 0, 0}
                    (KIP126.Core.SpectralSequence.toPreSS.{1, 0, 0}
                      (KIP126.Classical.Adams.ClassicalAdamsFamily.obj.{1, 0}
                        (KIP126.Kervaire.Route.ModelData.classical.{1, 0, 1}
                          (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1} KIP126.AdamsSynthetic.Standard.model))
                        KIP126.Literature.Standard.tmf))
                    p)
                  Top.top.{0}))
              z))
          ((CategoryTheory.ConcreteCategory.hom.{0, 0, 1, 0}
              (KIP126.Core.SpectralSequence.Filtration.toAssociatedGraded.{1, 0, 0}
                (KIP126.AdamsSynthetic.AbstractAdamsTower.filtration.{1, 0}
                  (KIP126.AdamsSynthetic.ClassicalTowerPresentation.tower.{1, 0}
                    (KIP126.Kervaire.Route.ModelData.classicalTower.{1, 0, 1}
                      (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1} KIP126.AdamsSynthetic.Standard.model))
                    KIP126.Literature.Standard.tmf))
                p.1 (HSub.hSub.{0, 0, 0} p.2 p.1)))
            b)
```
