---
issue_id: "20261016T1625-ordinary-sphere-separation"
responsibility_module: "AdamsSynthetic"
targets:
  - "KIP126.AdamsSynthetic.Standard.synthetic_homotopy_separated"
  - "KIP126.AdamsSynthetic.Standard.classical_sphere_separated"
baseline_commit: "bef90640c4594af4db32c86837f9d95340d1e171"
worktree: "/tmp/kip-adams-synthetic-20261016T1625"
candidate_source_commit: "a484b981fad612eabe2bc7a01b54e049e9a01ce4"
api_file_and_sha256: "metadata/adams-synthetic-api.json: 2fb1b8af37f2e926d72c3e6e8bceb13ec37c5574325f9511d92bb9676e8f20e2"
source_file_and_sha256:
  - "KIP126/AdamsSynthetic/Standard/Separation.lean: ba0da5ea44e3ca3aa11e075646bd85424047bdfb4997d7812c2dcf38d386bd1b"
  - "KIP126/AdamsSynthetic/Standard/ClassicalSupport.lean 基线: 2c9071240744a828db75601a8bdc66b124dfd64f8735b9569d3c1825c36b189d"
reporter_agent: "/root/separation_reporter"
independent_of_discoverer_and_implementer: true
evidence_level: "意图中的真实 ordinary/HF₂ synthetic 对象上的完整数学反例论证；在当前 Lean 未完成构造和实际识别边界上为条件性证据；没有无项目待补依赖的 Lean 反例"
status: approved-interface-change
human_decision: "2026-10-17，本聊天用户：同意以上提案，修改原接口。具体范围见文末本轮批准记录。"
---

# 接口调整人审报告

## 请求人类决定的具体问题

**当前 universal 分离性与已锁定的普通球/真实 HF₂ synthetic 语义不能同时按预期实现。** 本报告独立核对的见证位于 `X = .sphere`、`(m,w) = (3,3)`：普通稳定球的非零 3 阶类经过同一个 ν 保持非零，而在真实 νHF₂ 系数的每个塔层中均可提升。问题与 Milnor 坐标或某一页的计算无关。

同一问题也直接涉及 `Standard.classical_sphere_separated`：它在普通球的 `m=3` 已有同样见证，甚至不需要 ν/recovery 这部分依赖。报告已独立复核这个第二目标，未把发现者的结论作为前提。

需要人类决定的范围是这一个 universal 生产者接口及其实际调用域，**不是**更改六模块职责或默许用完备化球替换当前普通球。可审查的具体范围如下。

1. 是否保留当前普通 `sourceRecognition`、ν 和 λ recovery 的对象关联，并批准将本报告第“方案及精确差异”节的候选 A（有限 λ 商域）作为替代签名开展证明和调用域适配？这是明确缩小结论适用域的接口变更；候选尚未补证，不能因本报告而登记为完成。AdamsSynthetic 仍承担有限商和所需实际特例的生产者证明，不把缺口转交 Main/ProofTools。
2. 若必须保留原定理对原闭包的一字不改的零结论，则需要说明拟采用的真实数学解释如何绕过下述见证。单纯加强内部技术引理不够；不能删除普通球识别、把普通球重命名为完备化球，或改为不加性的替代张量。
3. 若选择完整的完备化路线，需要单独提出精确的新对象、普通源到完备化源比较、ν 的定义域以及 λ recovery 的接口方案。本报告**不请求也不授权**恢复历史 `CompletionModel`/`HF2AdamsContext` 公理背景；这些大范围修改尚无可批准的完整补丁方案。
4. 是否批准将经典目标按候选 C 改为 ordinary 球上的奇挠结论，或批准添加明确排除奇挠的元素条件？degree 125 的实际下游零结论须由 AdamsSynthetic 继续提供有适用条件的证明，不自动转为 Main 的新增假设。

本报告仅形成待审记录。没有改生产源码、接口锁、契约、待补清单或其他模块。等待、agent 认同和其他问题的批准均不是本问题的授权。

## 原接口、背景与问题成因

### 完整声明及宇宙

源码 `KIP126/AdamsSynthetic/Standard/Separation.lean:20`：

```lean
public theorem synthetic_homotopy_separated (X : SyntheticObject) :
    KIP126.AdamsSynthetic.HomotopySeparated model.syntheticTower
      (X.obj model.nu model.auxiliary) := by
  sorry
```

基线 `obligations-baseline.json` 与 API 锁给出的完整 elaborated 类型如下；它没有隐藏的完备性、2-locality、双次数范围或元素条件。宇宙参数列表为空，固定对象宇宙为 1，Hom 宇宙为 0。

```lean
∀ (X : KIP126.Kervaire.Route.SyntheticObject),
  KIP126.AdamsSynthetic.HomotopySeparated.{1, 0}
    (KIP126.Kervaire.Route.ModelData.syntheticTower.{1, 0, 1}
      (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1}
        KIP126.AdamsSynthetic.Standard.model))
    (KIP126.Kervaire.Route.SyntheticObject.obj.{1, 0, 1}
      (KIP126.Kervaire.Route.ModelData.nu.{1, 0, 1}
        (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1}
          KIP126.AdamsSynthetic.Standard.model))
      (KIP126.Kervaire.Route.ModelData.auxiliary.{1, 0, 1}
        (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1}
          KIP126.AdamsSynthetic.Standard.model))
      X)
```

所用谓词的全部参数和定义为（沿用文件中的普通 namespace/open）：

```lean
universe u v
variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  [HasFunctorialCofiber (C := Syn)] {H : Syn} {unit : S_0_0 ⟶ H}
  {F : SyntheticAdamsFamily Syn}

public def FiltrationAtLeast (P : SyntheticTowerPresentation unit F) {X : Syn}
    (s : ℤ) {m w : ℤ} (a : BiHom m w X) : Prop :=
  a ∈ P.filtrationSubmodule X s (m,w)

public def HomotopySeparated (P : SyntheticTowerPresentation unit F) (X : Syn) : Prop :=
  ∀ (m w : ℤ) (a : BiHom m w X),
    (∀ s : ℕ, FiltrationAtLeast P s a) → a = 0
```

`P.filtrationSubmodule X s (m,w)` 恰为后合成实际 `(P.tower X).projection s` 的整数线性映射之像；不是任意指定滤过。自然数 `s` 强制转换为整数；`stageAt s = stage s.toNat`，因此这里确实穷尽所有非负实际塔层，负指标的常值延拓不影响见证。

### 同源的第二个完整接口

`Standard/ClassicalSupport.lean` 基线第 30 行（其他 worker 补前两个独立声明后，当前第 79 行）的原声明为：

```lean
public theorem classical_sphere_separated (m : ℤ)
    (a : HomotopyGroup (C := Spectrum) m SphereSpectrum)
    (ha : ∀ s : ℕ,
      a ∈ (model.classicalTower.tower SphereSpectrum).filtrationSubmodule s m) :
    a = 0 := by
  sorry
```

基线锁的完整 elaborated 类型（宇宙参数列表同样为空）为：

```lean
∀ (m : ℤ)
  (a : KIP126.StableHomotopy.HomotopyGroup.{1, 0}
    m KIP126.StableHomotopy.SphereSpectrum.{1, 0}),
  (∀ (s : ℕ),
      Membership.mem.{0, 0}
        (KIP126.AdamsSynthetic.AbstractAdamsTower.filtrationSubmodule.{1, 0}
          (KIP126.AdamsSynthetic.ClassicalTowerPresentation.tower.{1, 0}
            (KIP126.Kervaire.Route.ModelData.classicalTower.{1, 0, 1}
              (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1}
                KIP126.AdamsSynthetic.Standard.model))
            KIP126.StableHomotopy.SphereSpectrum.{1, 0})
          (↑s) m)
        a) →
    Eq.{1} a 0
```

它也没有 `HomotopyTwoLocal`、完备性或排除奇挠前提。其同文件私有 adapter `classical_sphere_separated_of_residual_acyclic` 则明确假设 natural products、`oneSubShift` 是同构以及塔步在该同伦度数的核有限。此 adapter 是正确的**有前提**路线，不能从它的存在推断那些残余条件对普通球满足；尤其不得由已争议的零结论回推其前提，再循环应用 adapter。

### 固定对象和来源

`SyntheticObject` 的构造子为 `.sphere`、`.nu X`、`.shift p X`、`.quotient n X`。`.sphere.obj nu auxiliary` 定义就是 `S_0_0`。`BiHom m w X = Smn m w ⟶ X`，`Smn m w = biShift (m,w) S_0_0`。辅助 detector、ν cofiber 或其识别都不参与本见证。

`Standard.sourceRecognition : ClassicalSourceRecognition Spectrum coefficients` 是待构造的**普通**稳定源识别。实际 `SourceRecognition` 包含 `SourceCategory.{0} ≌ Spectrum`、普通 source sphere 同构、整数稳定同伦及实际 cubical addition 的比较。`Internal/Source/Prespectrum.lean` 明示源未完备化；`Internal/Source/Sphere.lean` 中 source sphere 从离散两点空间迭代实际 reduced suspension 构成。当前 `ClassicalHF2LocalizedSource sourceRecognition` 是另一个范畴；`localizedSphere_classicalIso` 仅是**谱序列**对象同构，并不是普通球与完备化球在 `Spectrum` 中同构。

本接口由 `bbac1fc...` 的 coherent model 字段恢复。任务限定的 a48 源本身也有 `AdamsComparison.homotopySeparated` 字段，而不是该字段的构造证明：

```lean
structure AdamsComparison extends AdamsComparisonData H Syn where
  ...
  homotopySeparated : HomotopySeparated toAdamsComparisonData
  ...
```

a48 的 `KIP126/Def/AdamsSynthetic/Comparison/Predicates.lean:82` 将其说明为 selected complete objects 上的 Hausdorff convergence。a48 的实际 `SourceComparison Q H` 则从 `CompletedSpectrum` 等价到经典范畴，球是 `Q.localization.obj Prespectrum.sphere` 的像。另一个直接源 `a48:KIP126/Main/AdamsSynthetic/SphereConvergence.lean:3716` 的 `standardSphereSeparated` 明确针对 2-completed sphere，证明直接调用 `standardSphereApplicability.strongly_convergent.separated`。这既没有证明当前普通球分离性，也没有构造所需 universal synthetic 分离性。

迁移分类应分别为：a48 coherent 字段 **源中仍未证**；a48 completed-sphere 推导到当前 ordinary-sphere 目标 **不适用/需人审适配**。不能把输入字段或强收敛假设计作已迁入证明。

成因是**普通对象与完备化适用域错配**，并伴随尚未完成的实际背景识别。它不只是“目前找不到证明”。对真实对象语义，下节给出明确失败见证；对当前裸 Lean 记录，本报告不声称已形式证明 `False`。

## 真实前提与对象核对

| 前提或对象条件 | 是否满足 | 证据及仍依赖的待补责任 |
| --- | --- | --- |
| 目标允许 `X=.sphere` | 是，定义性 | `Configuration.lean` 的闭包及 `.obj`；不需 auxiliary 性质 |
| 目标允许 `m=w=3` | 是 | 全部 `m w : ℤ`；无 Chow degree 或正滤过排除条款 |
| 经典球是 ordinary 稳定球 | 锁定语义是；实际 Lean 比较未完成 | `Standard.sourceRecognition` 直接 sorry；源 sphere 的定义没有 completion |
| ordinary π₃ 球含非零 3 阶类 | 实际普通球上是；项目中未形式化 | π₃S=ℤ/24，取生成元的 8 倍；外部作者资料及对象识别边界见下节 |
| 同一个 ν 保持非零类 | 由 recovery 数据可推导 | `LambdaRecovery.nuRealizationIso : N.functor ⋙ R.realization ≅ 𝟭 C` 使 ν faithful；`Standard.recovery`、`Standard.nu` 尚待构造 |
| ν 加性、球/悬移关联 | 记录确实要求 | `NuFunctorData.additive`、`unitIso`、`suspensionIso`；三次悬移给 ν(S³)≅S^(3,3)；使用同一 biShift 比较 |
| 系数就是同一 HF₂ 的 ν 像 | 是，接口固定 | `nuCoefficientUnit = nu.unitIso.inv ≫ nu.functor.map coefficients.unit`；`syntheticTower` 以该单位为参数 |
| `2·id_HF₂=0` | 真正 HF₂ 上是；裸记录未编码该结论 | 真正 Eilenberg–MacLane 谱的端自映射/环特征 2；`ModTwoCoefficients` 只列同伦群，不能在任意抽象背景中直接推出 |
| νHF₂⊗T_s 被 2 杀死 | 真实 synthetic 张量上是；裸父记录未编码张量加性 | ν 加性加上实际张量加性；不能从 `Preadditive + MonoidalCategory` 自动假定 `MonoidalPreadditive` |
| 每层是上述系数 smash 同一 stage | 接口精确规定；实际塔尚待构造 | `AbstractAdamsTower.layerIso s : cofib(step_s) ≅ νHF₂ ⊗ stage s`；不使用替代塔 |
| 实际 cofiber 序列 Hom 正合 | 真实 triangulated 背景上是 | `HasFunctorialCofiber.cofib_distinguished`，以及 `exactness.syntheticTriangulated`；实际实例待构造 |
| 反例需要 E₂、Milnor、检测或分离性自身 | 否 | 提升证明只用同一塔的 cofiber 层；不调用目标、其下游或相关分离性未证责任 |

特别说明：Whitehead 判定等价不意味着任何诱导所有 π 为零的映射都是零。此处的 `2 id_HF₂=0` 应由真正 HF₂ 的 Eilenberg–MacLane/t-structure 或特征 2 环结构证明，不能以“其诱导同伦映射全零”一笔带过。

## 独立证据与复现

### 数学见证

普通稳定球的 π₃ 是 ℤ/24。选择生成元 β，令 `α=8β : S³→S`，则 `α≠0` 且 `3α=0`。作者资料 [N. P. Strickland, *An introduction to the category of spectra*, §2.3](https://strickland1.org/research/stableintro.pdf) 记录该群；本报告不把它冒充已存在的项目 Lean 定理。

另外独立核对作者教材 [A. Hatcher, *Algebraic Topology*, §4.J，p.474](https://pi.math.cornell.edu/~hatcher/AT/ATch4.4.pdf)：那里讨论 `π₇(S⁴)→π₈(S⁵)` 的像为 ℤ/24，Hopf 类悬移生成该群；结合该节 p.473 的 suspension stable range，得到相同 ordinary 第三稳定群。没有使用项目 Literature 中的待补声明作计算依据。

HF₂ 的 `2 id=0` 也可不用环结构作一项完整数学推导。[J. Lurie, *Higher Algebra*, Proposition 1.4.3.6(3)，p.151](https://www.math.ias.edu/~lurie/papers/HA.pdf) 将实际谱范畴标准 t-structure 的 heart 与 Ab 等价。真正 HF₂ 位于该 full heart 并对应 ℤ/2，因此其度零端自映射群等同 `Hom_Ab(ℤ/2,ℤ/2)`；加性的 full inclusion 将零 doubling 的恒等同态送为 `2 id_HF₂=0`。这是对**特定 heart 对象**的证明，不是一般“零 π 映射即零映射”的错误推论。此 t-structure/heart 识别尚未在当前固定源的 Lean 实现下补齐，故仍保留报告的条件性等级。

同一个 ν 的恢复同构给 ν 的 faithful 性：若 νf=νg，施加 realization，再用自然同构 `realization ∘ ν ≅ id` 的自然性消去两端同构，即得 f=g。ν 的加性将 ν0 识别为 0。因此 να 非零，且仍被 3 杀死。

将 `NuFunctorData.suspensionIso` 使用三次，并使用 ν 的同一个 `unitIso` 和实际 shift/biShift 复合比较，得到 `e : ν(S³) ≅ Smn 3 3`。定义

`a := e.inv ≫ ν(α) ≫ nu.unitIso.hom : BiHom 3 3 S_0_0`。

则 `a≠0`、`3·a=0`。这没有把 spectral-sequence 层面的 `family.nuSphereIso nu` 当成对象识别；后者仅由 `family.functor.mapIso nu.unitIso` 导出，真正对象关联来自 `unitIso`。Pstrągowski 的 [*Synthetic spectra and the cellular motivic category*](https://arxiv.org/pdf/1803.01804)，Theorem 4.37/4.40 的普通 λ（文献记 τ）反演恢复，以及 Definition 4.6 附近的球约定，与这组固定接口的预期语义一致；它没有将普通 νS 改成 2-completed sphere。

现在固定**目标中同一个** `T := model.syntheticTower.tower S_0_0`。记

`f_s : T.stage (s+1) → T.stage s`，`j_s : T.stage s → cofib(f_s)`。

实际系数 HF₂ 的 doubling 为零；ν 和实际张量加性给 νHF₂⊗T_s 的 doubling 为零。由 `T.layerIso s`，`2 id_cofib(f_s)=0`，所以 `2 j_s=0`。将正合函子 `Hom(T_s,-)` 用于该 distinguished triangle，`2 id_T_s` 落在后合成 `j_s` 的核中，因此存在

`q_s : T_s → T_(s+1)`，满足 `q_s ≫ f_s = 2 id_T_s`。

取 `b₀ := a ≫ T.zeroIso.inv`，递归定义

`b_(s+1) := 2 · (b_s ≫ q_s)`。

由 preadditivity 归纳得 `3 b_s=0`，并且

`b_(s+1) ≫ f_s = 4 b_s = b_s`。

最后一个等号恰使用 `3 b_s=0`。利用塔的 `map_comp` 与同一个 `zeroIso`，每个自然数 s 都满足 `b_s ≫ T.projection s = a`。所以 `∀ s : ℕ, FiltrationAtLeast model.syntheticTower s a`，而 `a≠0`。原 universal 分离性在真实普通球的 `(3,3)` 处失败。

这个构造比“任何 lift 自动仍为 3-torsion”的说法更强且准确：所选 lift 通过 `q_s` 和标量 2 明确修正，确实保持 3-torsion。它不需要 ν exact、ν strong monoidal 或 classical/synthetic 塔之间的比较。

### 经典接口的独立特化

直接取 `T := model.classicalTower.tower (SphereSpectrum : Spectrum)`，`a := α : HomotopyGroup 3 SphereSpectrum`。接口将 `cofib(f_s)` 认同为 `coefficients.object ⊗ T_s`。实际 ordinary HF₂ smash 加性给每层 doubling 为零；同一 `q_s` 和 `b_s` 递归因此证明 α 属于经典塔每个非负滤过级。由于 α≠0，`classical_sphere_separated 3 α` 在意图中的 ordinary 对象上失败。

此特化删去了全部 synthetic 类别、ν faithful、ν suspension、λ recovery 的依赖。仍需要实际 ordinary π₃、真正 HF₂ 的特征 2、实际张量与 cofiber 正合，以及尚未完成的 ordinary `sourceRecognition`/经典塔构造。不能把它称为当前 Lean 中已无待补依赖的反例。

### 证据等级及依赖审计

* **对意图中的实际普通/HF₂ synthetic 对象：完整数学反例论证。** 用的是实际普通球上的类、实际 ν、实际系数 smash cofiber 塔；没有改用平凡范畴或自由抽象滤过。
* **对当前 Lean 实现：条件性证据。** `Spectrum`、`SyntheticSpectrum`、两类结构、cofiber 实例、`coefficients`、`nu`、`recovery`、`syntheticTower` 和 `sourceRecognition` 尚为直接待补构造。实际 π₃ 计算、特征 2 和 synthetic 张量加性尚未在该固定实现下补齐。仅按裸记录类型，前两项附加事实也不是现有字段的自动结论。
* **不是**已检查的无 `sorryAx` Lean 反例，不是有限计算推出拓扑事实，也不是从未证目标或不一致环境推出 `False`。没有运行针对这些待补常量的反证程序。
* `Standard.finite_map_separation` 仅推出 `IsOddTorsionMap`，`adams_filtration_bounded` 明确保留 `HomotopyTwoLocal` 等条件。它们与此处的奇素数无限滤过见证相容，没有被用来制造矛盾。
* `SyntheticTowerConvergence` 只认同 associated graded；它不保证滤过 Hausdorff，也不排除一个在所有滤过级中的类。不能以其存在为本问题的内部证明。
* `sourceClassical_inverts_hf2`、`localizedSphere_classicalIso` 只处理谱序列，不能消去被普通 realization 检出的 α。本论证不依赖这些待补比较。

### 同目录复现与实际结果

独立报告员重新读了原接口、谓词、实际源定义、ν/recovery、塔层、a48 coherent 字段、a48 完备化源比较及 completed-sphere 分离推导。随后才阅读发现者材料核对；没有参与候选发现或实现。

在工作树运行：

```sh
python3 /inspire/hdd/global_user/czxs25250150/Kervaire126Main/metadata/interface-reviews/AdamsSynthetic/20261016T1625-ordinary-sphere-separation/reproduce.py
```

`reproduce.py` 只读仓库和 `git show`，只写本问题目录；不调用 Lean/Lake、不写 `.lake`。实际退出码为 0；`reproduction-result.json` 记录 `lean_or_lake_executed=false`、`formal_counterexample_proved=false`。有限标量检查仅验证 `4^s·8=8 (mod 24)` 对 `s=0,…,16`，其结果全为 8；此项只是检查上文算术，没有证明任何谱、塔或拓扑事实。

附件：

* `exact-declarations.json`：API 锁及 session 基线中的两个完整目标、谓词和关键依赖类型。
* `input-sha256.json`、`source-excerpts.txt`：独立读取时的源码快照和行号。
* `baseline-separation-source.txt`：两个分离性目标所在文件的完整 session 基线源与哈希。
* `a48-source-excerpts.txt`：直接 `git show a484…:path` 得到的实际源、哈希和行号，包含 `KIP126/Main/AdamsSynthetic/SphereConvergence.lean`；不是当前 BHS 补包的代用品。
* `downstream-callers.txt`：当前源码直接调用位置。
* `reproduction-result.json`：只读复现的实际结果与限制。
* `external-mathematical-sources.md`：独立外部来源的作者链接、精确位置及使用边界。

`Standard/Separation.lean`、原始 Background/Recognition/Recovery 等文件与 session 基线哈希相符。`Internal/Source/Prespectrum.lean` 已有本 session 其他 worker 的新增私有支持引理和一个 import，`Standard/ClassicalSupport.lean` 已补另外两个独立声明，`Standard/Filtration.lean` 已补 `homologyShift`/`homology_exact`，因此全体快照的 `session_baseline_hashes_all_match=false`。已独立查看这些 diff：ordinary 源和两个分离性目标的完整签名、其直接 sorry 均未改变；`finite_map_separation` 和 boundedness 的适用条件也未改变。本报告不依赖新增支持引理，不影响这些独立补证，没有覆盖或回退其他 worker 的修改。

## 方案及精确差异

### 先评估保留原接口的内部方案

在保留普通源、同一个 ν/recovery 和真实加性 synthetic 张量的前提下，原 universal 结论不能由内部证明修复：见证已经位于 `.sphere` 中，任意满足所锁定 cofiber 层条件的真实塔都受上述提升论证约束。换一套谱页、补 associated-graded comparison 或选择另一个 canonical presentation 均不消除它。

以下操作不构成保留接口的修复：偷换 `S_0_0` 为完备化球；削弱 `HomotopySeparated` 的定义但保持名字；把源对普通球的识别改成对完备化球；令 ν 杀掉 α 同时保留 `nuRealizationIso`；使用缺张量加性字段来挑选并非真实 synthetic 谱的模型；用待补定理直接关闭目标。

仍有不改现有公共接口即可先做的工程/数学工作：完成独立 Milnor 和源构造；内部研究有限 λ 商上的直接分离性、特定未截断调用域和对象识别。研究过程中不得把原 universal 声明当作已证明引理。

### 候选 A：把 universal 生产者缩到明确有限 λ 商

原签名为上文完整类型。使用现有记号的新候选完整源码签名是：

```lean
public theorem synthetic_homotopy_separated (X : SyntheticObject) (n : ℕ) :
    KIP126.AdamsSynthetic.HomotopySeparated model.syntheticTower
      (KIP126.Synthetic.Context.XModLambdaN
        (X.obj model.nu model.auxiliary) n)
```

差异：同一名字增加 `n : ℕ`，目标从任意选定 X 的对象改成**同一个对象的实际 λⁿ cofiber**。不增加结果包、模型参数或外部证明假设；同一塔、ν、auxiliary 和宇宙保持。`n=0` 的 cofiber 为零对象，应由现有 cofiber 结构证明；正 n 的范围是有限 λ 商。该候选删除了对原未截断 `.sphere`/`.nu X` 的保证，所以不再包含本报告 `(3,3)` 的原球见证。

这是一份**待证明的候选签名**，本报告没有证明其对整个嵌套 SyntheticObject 闭包都成立。实施前须实际构造 Cλ/有限商对象和其 νHF₂ 塔，完成分离性证明，再用普通导入复验；若失败，仍保留待审，不能增公理或假设补洞。对于商后再 shift 的调用，要用实际 shift/cofiber 同构转运，不能只依靠对象名字。

未截断调用需要 AdamsSynthetic 在其真实度数/对象条件下另外给出准确结论，并明确证明条件在每个调用处成立；不能把原 universal 责任直接作为 Main/ProofTools 的新前提。涉及别的模块源码适配还需要对具体范围的批准。

### 候选 B：普通对象上保留“排除奇挠”的元素条件

可供进一步研究的另一个精确签名是：

```lean
public theorem synthetic_homotopy_separated
    (X : SyntheticObject) (m w : ℤ)
    (a : KIP126.Synthetic.Context.BiHom m w
      (X.obj model.nu model.auxiliary))
    (h_no_odd : ∀ (n : ℕ), Odd n → n • a = 0 → a = 0)
    (ha : ∀ s : ℕ,
      KIP126.AdamsSynthetic.FiltrationAtLeast model.syntheticTower s a) :
    a = 0
```

它保留原对象，增加每个元素无奇挠的真实条件，将全对象的分离性改成逐元素结论。α 不满足 `h_no_odd`（取 n=3），因此能排除已知见证。但**排除这一见证并不证明此新签名**：还要独立证明当前选定闭包上的无限滤过类必为奇挠，核对 detector/tmf 的真实适用条件，排除其他 completion/limit 问题。本报告没有确认该条件单独充分，不建议直接实施或让下游无依据补出它。

只给所有对象统一加 `w>m` 也不是精确修复：闭包含任意双移位，`.shift (0,100) .sphere` 将同一个非零奇挠类移到 `(3,103)`，仍可对该目标的真实 HF₂ 塔逐层提升。限制区域必须跟踪具体对象及 shift，不能仅用全局双次数不等式。

### 完备化方向的边界

可以保留普通源作为独立对象，另构造真正 HF₂ 完备/局部 synthetic 路线，再在经证明适用的对象上陈述分离性。但普通 recovery 与完成后的 recovery 的对象范畴不能静默相同；HF₂-local、derived 2-complete、νHF₂-local/hypercomplete 和 Adams 完备也不能无条件混用。本报告未提供覆盖这些全部边界的精确签名改动，因此不以这一方向申请笼统授权。

### 候选 C：经典 ordinary 球的精确弱化

对 `classical_sphere_separated`，保留原参数和实际滤过前提，把结论精确改为：

```lean
public theorem classical_sphere_separated (m : ℤ)
    (a : HomotopyGroup (C := Spectrum) m SphereSpectrum)
    (ha : ∀ s : ℕ,
      a ∈ (model.classicalTower.tower SphereSpectrum).filtrationSubmodule s m) :
    KIP126.AdamsSynthetic.IsOddTorsionMap a
```

`IsOddTorsionMap a` 的现有完整定义是 `∃ n : ℕ, Odd n ∧ 0 < n ∧ n • a = 0`，包括零。这比原 `a=0` 严格弱，普通见证 α 正好满足新结论。它不改对象、塔、量词、宇宙或增加结果包；同名定理的语义发生变化，必须明确批准。若需要名称表达更准确，可另行批准重命名/导出变化；本报告不自行执行。

数学上该结论可研究从同模块现有 `finite_map_separation` 推导：源 `Sphere m` 和目标球在 `IsFiniteSpectrum` 闭包内，`ha` 的实际 projection lift 正是 `MapAdamsFiltration`，负级由 stage zero 延拓处理。因此它与已锁定普通有限谱定理一致。但 `finite_map_separation` 自身仍是登记的直接待补，推导成功也必须如实保留该传递依赖，不能宣称奇挠判定已经无待补证明。

若人类仍需经典目标的零结论，可明确批准在原签名 `ha` 后增加以下元素条件，再由奇挠结论消去：

```lean
(h_no_odd : ∀ n : ℕ, Odd n → 0 < n → n • a = 0 → a = 0)
```

这是增加前提而非原接口的内部补证。特别是 Main 的 degree 125 调用，必须由原责任模块实际证明该元素条件或更精确局部定理；不允许让 Main 无来源承担一个新增基础责任。

## 下游影响

`downstream-callers.txt` 找到下列直接依赖。它们是需要重新审查适用域的调用，不代表每个特例结论都已被本报告推翻。

| 文件与位置 | 模块 | 依赖用途与影响 |
| --- | --- | --- |
| `ProofTools/GeneralizedMahowald/Filtration.lean:61,103` | ProofTools | 有限/shifted finite 商的高滤过消失；可研究候选 A 的实际转运 |
| `ProofTools/GeneralizedMahowald/HSource.lean:33` | ProofTools | 首商检测唯一性；有限 λ 商域可独立重建 |
| `ProofTools/GeneralizedMahowald/MayCorrection.lean:114` | ProofTools | 特定商目标的 correction；需按 B 的真实定义核对 |
| `ProofTools/GeneralizedMahowald/SphereMayCorrection.lean:56` | ProofTools | shifted finite 目标；需要实际 cofiber/shift 比较 |
| `ProofTools/GeneralizedMahowald/OctahedralPullback.lean:236` | ProofTools | 特定目标 B 的 pullback 消失；不能继续借 universal 定理关闭 |
| `Main/Internal/Theta/RealizationKernel.lean:124` | Main | 通用选定对象上的核为零步骤；需要更精确实际条件 |
| `Main/Internal/Choice/LambdaInjectivity.lean:97` | Main | 从 E∞ 注入推出 homotopy 注入；依赖无无限滤过核 |
| `Main/Internal/High125/Filtration.lean:76` | Main | `.sphere` 的 `(125,130)` 特例；本反例在 `(3,3)`，尚未推翻该局部结论 |
| `Main/Internal/LowEta.lean:75` | Main | `.sphere` 的 `(1,3)` 特例；同样需独立实际区域证明 |
| `Main/Internal/High125/Filtration.lean:126` | Main | 直接用 `classical_sphere_separated 125 a` 关闭经典 26 滤过消失；需要该度数的真实奇挠/完备性条件，不能借 universal 零结论 |

API 变更后必须经批准定向更新 `metadata/adams-synthetic-api.json`、对应 `adams-synthetic-contracts.json` 的 `synthetic-homotopy-separation`/`filtration-separation`/`adams-synthetic-main-proof-consumption` 记录、`adams-synthetic-sources.json` 和两个直接责任的 `proof-obligations.json` 行；保留原始来源和本报告，不能批量刷新六模块锁或为掩盖失败放宽检查。

`Tests/AdamsSynthetic/Interface.lean` 对完整类型、宇宙、导出和传递公理有实际检查，必须保留。届时需由协调者单一构建进程验证普通公共消费、AdamsSyntheticChecks、ArchitectureChecks、现有 Integration/Trust 审计、`python3 scripts/check-source-inventory.py` 和完整 `lake build`。本报告员没有运行这些构建；报告不修改生产文件，因此没有把只读核验当成构建验证。

分离性依赖的逻辑链应做定向传递审计。保留现有编译不意味着该链已数学完成；改签名也不能只改检查而不修实际调用。

## 阻塞范围与继续项

应暂停的是 `Standard.synthetic_homotopy_separated` 和 `Standard.classical_sphere_separated` 作为**无条件 universal 零结论**的补证，以及任何依赖它们在争议对象/区域上有效的候选证明。两者仍是登记中的 AdamsSynthetic 待补责任，不能据此报告直接责任已消除。源中的同名假设字段也不能迁为证明。

对上述调用的适用域尚未逐项证明，故记录其传递依赖风险；不能宣称整个 ProofTools/Main 命题为假，也不能接手这些模块。对具体有限商或固定局部区域，可以独立寻找真实证明并由原协调者安排审核。

本 session 可继续且协调者已经安排的独立项包括：ordinary prespectrum/源 HF₂ 的实际支持构造；同一系数单位的 canonical tower/完整谱页适配；Milnor cobar 的独立 `d²=0` 与 cohomology；有限 λ 商塔及其结构比较；不使用本分离性声明的 ν/λ recovery 泛型推导。HF₂ localization 与 ordinary source 的比较也可继续，只须保持对象区分。

同文件 `Standard.classical_page_negative` 与 `Standard.sphere_page_filtration_zero` 只用实际 cofiber 页/系数消失事实，不消费分离接口；比较 worker 对这两项的迁移和验证可以继续，它们不在人审阻塞闭包内。

没有理由冻结整个 AdamsSynthetic。不会等待其他 session 的未补接口，也不把 SpectralSequence 等模块的责任迁入本模块。

## 人类审核记录

尚无人类对本报告的具体方案和范围作出决定。`status=pending-human-review`，`human_decision=null`。


## 本轮批准记录（2026-10-17）

用户在本聊天阅览七份报告摘要后明确回复：

> 同意以上提案，修改原接口

本报告获准范围：

- 候选 A：synthetic_homotopy_separated 限于同一选定对象的有限 λⁿ 商，增加 n : ℕ。
- 候选 C：classical_sphere_separated 结论改为 IsOddTorsionMap；不批准恢复无条件零结论。

该批准不是新增公理、额外待补责任、任意 Main 公共前提或未列明接口变更的授权。原文中的“尚未批准”保留为历史阶段记录；实现及实际验证另记，批准不表示证明已经完成。
