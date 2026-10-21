---
issue_id: SpectralSequence-low-page-compatibility-20261021
title: 谱序列起始页以前的微分约定尚未接到全页比较与退化目标
summary: 已核实正页比较与低页要求之间的精确差项；优先继续在固定 Adams 系统的既有构造责任内证明低页零性。若改为加强 tower presentation 或调整泛型有效页语义，须另获本报告范围的人审批准；当前不阻断其他补证。
responsibility_module: SpectralSequence
targets:
  - KIP126.Core.SpectralSequence.DegeneratesAt
  - KIP126.Core.SpectralSequence.PreSSMorphism
  - KIP126.Core.SpectralSequence.SpectralSequenceMorphism
  - KIP126.AdamsSynthetic.TowerSequencePresentation
  - KIP126.AdamsSynthetic.Standard.classical_canonicalIso
  - KIP126.Literature.Standard.degeneration
baseline_commit: ca41f040fade95a25a94ff4a1b1eaf0682c3c82a
worktree: /inspire/hdd/global_user/czxs25250150/ops/tmp/main-followup-20261019
reporter_agent: /root/low_page_interface
independent_of_discoverer_and_implementer: true
evidence_level: 独立源码与完整前提复核；三次既有实际 Lean 检查的源码及日志哈希复核；另给泛型对象的数学模型说明，未声称固定模型反例
status: pending-human-review
human_decision: null
---

# 接口调整人审报告

## 请求人类决定的具体问题

当前两项公共目标分别要求全部整数页的谱序列同构、从任意整数 `N` 起的退化；所用 tower presentation 与正页比较只约束 `r ≥ 2`。报告确认了这个范围差，**没有推翻当前固定数学对象上的目标**，也没有证明必须修改公共接口。

保留现有接口的首选方案是：在既有固定 `classical`、`family`、`classicalTower`、`syntheticTower` 的构造责任内完成所选系统的低页零性，再接上已核验的正页桥。继续此内部补证无需新批准。本报告不请求暂停该路线或其他正常补证。

若决定采用接口调整，请明确批准下文 **B（加强指定的 tower presentation）** 或 **C（泛型态射与退化只讨论有效页）** 的具体范围。二者是不同数学约定，不能以更新锁指纹代替选择与验证。当前没有对 B、C 的人类授权；报告本身没有应用任何一种方案。

## 原接口、背景与问题成因

### 固定的两个完整目标

在 `KIP126.AdamsSynthetic.Standard` 中，`Spectrum : Type`、它的稳定同伦范畴与 cofiber 实例、`coefficients`、`classical` 是已经选定的对象；实际实例由同文件的注册责任提供，并非本报告可替换的参数。完整目标为：

```lean
public def classical_canonicalIso (X : Spectrum) :
    classical.obj X ≅ canonicalAdamsSequence X := by
  sorry
```

同一文件固定了：

```lean
@[no_expose] public def canonicalAdamsTower (X : Spectrum) :
    AbstractAdamsTower coefficients.unit X :=
  Internal.Source.canonicalTower coefficients.unit X

@[no_expose] public def canonicalAdamsSequence (X : Spectrum) :
    KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) (ℤ × ℤ) :=
  Internal.Source.canonicalSequence coefficients.unit X
```

这里 `≅` 是实际 `SpectralSequence` 范畴中的同构，要求同一 ambient、所有有限及无限 cycles/boundaries 的映射和**全部整数页**微分相容；不能只用 E₂ 线性同构或只用正页 `PagewiseIso` 代替。

在 `KIP126.Literature.Standard` 中，`model : Model Spectrum SyntheticSpectrum` 已固定，完整目标为：

```lean
public theorem degeneration :
  ∀ (X : ClassicalObject) (N : ℤ),
    DegeneratesAt (model.classical.obj (X.obj model.auxiliary)) N →
    DegeneratesAt
      (model.family.nu model.nu (X.obj model.auxiliary)).sequence N := by
  sorry
```

`X` 是按 `model.auxiliary` 解释的同一个经典对象；synthetic 一侧是该对象经指定 `model.nu` 后的指定 `model.family`，没有另选等维谱页。`N` 无 `2 ≤ N` 前提。

### 泛型接口的完整范围

以下公共声明的上下文为：

```lean
universe u v w
variable {C : Type u} [Category.{v} C] [Abelian C]
  {ι : Type w} [AddCommGroup ι] [DecidableEq ι]

public def DegeneratesAt
    (E : SpectralSequence C ι) (N : ℤ) : Prop :=
  ∀ (r : ℤ), N ≤ r → ∀ (k : ι), E.d r k = 0
```

`PreSS.Page E r k = (E.ssData k).page ↑(r-E.r₀).toNat`。因此 `r < E.r₀` 时得到索引 `0` 的商页，通常并非零对象。`SpectralSequence` 的 `d_comp_d` 对所有 `r` 成立，但 `Z_succ`、`B_succ` **只在 `E.r₀ ≤ r` 时**约束微分的核与像。平方为零不能推出低页微分为零。

`SpectralSequenceMorphism` 完整字段为 ambient map `φ`、在全部 `WithTop ℕ` 上保 cycles 的 `preserves_Z`、保 boundaries 的 `preserves_B`、`r₀_eq`、`diffDeg_eq`，以及：

```lean
comm_d : ∀ (r : ℤ) (k : ι),
  let f : SSDataMorphism ι E.ssData E'.ssData :=
    { φ := φ, preserves_Z := preserves_Z, preserves_B := preserves_B }
  f.pageMapAt (E := E.toPreSS) (E' := E'.toPreSS) r₀_eq r k ≫
      E'.d r k =
    E.d r k ≫
      f.pageMapAt (E := E.toPreSS) (E' := E'.toPreSS)
        r₀_eq r (k + E.diffDeg r) ≫ eqToHom (by rw [diffDeg_eq])
```

`PreSSMorphism` 继承 `SSDataMorphism`，同样给出 `r₀_eq`、`diffDeg_eq` 和无起始页前提的上述 `comm_d`。这些完整源码及 `SpectralSequence` 全部约束见[逐行摘录](evidence/source-excerpts.txt)。

### Tower 数据只约束正页

完整参数上下文是：

```lean
universe u v
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)] {H : C}
  (unit : SphereSpectrum ⟶ H)
```

`TowerSequencePresentation unit T D d` 的完整对象及前提是：`X : C`，`T : AbstractAdamsTower unit X`，`D : (ℤ × ℤ) → SSData (ModuleCat.{v} ℤ)`，以及

```lean
d : ∀ (r : ℤ) (p : ℤ × ℤ),
  (D p).page (↑(r-2).toNat : WithTop ℕ) ⟶
    (D (p+(r,r-1))).page (↑(r-2).toNat : WithTop ℕ)
```

它的四组完整字段为：每个 `p` 上到实际 `T.cycles 2` 的 `ambient` 同构；每个自然数 `n` 上的 `cycles` 和 `boundaries` 当且仅当；以及**带 `(hr : 2 ≤ r)`** 的 `differential`，后者对任意源 cycle、实际 tower lift `a`、目标 cycle 的完整 connecting/layer 等式给出指定 `d r p` 的值。`differential` 完整签名较长，已在[摘录](evidence/source-excerpts.txt)逐字保留，不省略它的两个代表等式。

`ClassicalTowerPresentation.sequence X` 正是对同一个 `(classical.obj X).ssData` 和 `normalizedDifferential (classical.obj X) ...` 的上述 presentation。`SyntheticTowerPresentation.sequence X w` 对同一个 synthetic tower、同一 fixed-weight 微分也使用这个 presentation。它们没有低页零性字段。

另一方面，实际 canonical 实现为：

```lean
private noncomputable def towerD
    (T : AbstractAdamsTower unit X) (r : ℤ) (p : ℤ × ℤ) :
    (towerSSData T p).page (↑(r-2).toNat : WithTop ℕ) ⟶
      (towerSSData T (p+(r,r-1))).page
        (↑(r-2).toNat : WithTop ℕ) :=
  if hr : 2 ≤ r then (towerDifferential_exists T r hr p).choose else 0
```

所以 canonical 一侧低页确实定义为零；任意满足现有 presentation 的另一侧，并未仅凭该 presentation 获得同一结论。

这是**起始页以前的约定尚未桥接到强接口要求**。它不是已确认的 AimPaper 假命题，也不是已经证明的固定模型反例；目前也无法仅凭源码缺少字段断言实际低页事实绝不可能由其他真实构造证明。

## 真实前提与对象核对

| 前提或对象条件 | 是否满足 | 证据及仍依赖的待补责任 |
| --- | --- | --- |
| 经典与 synthetic 起始页均为 2 | 是，接口直接提供 | `ClassicalAdamsFamily.firstPage`、`SyntheticAdamsFamily.firstPage`。 |
| 经典微分次数为 `(r,r-1)`、synthetic 次数为 `(r,r-1,0)` | 是，接口直接提供 | 两 family 的 `differentialDegree`；没有限制到 `r ≥ 2`，但次数公式不蕴含微分零性。 |
| 比较的是同一个 `classical.obj X` 与同一 coefficient-unit 的 canonical sequence | 是 | 实际实例化探针使用 `classicalTower.sequence X`、`classicalTower.tower X`、`canonicalTower coefficients.unit X`；未使用 `classical_canonicalIso`。 |
| 任意两个同一 unit、同一 `X` 的 abstract towers 可比较 | 已有实际 Lean 检查 | stage 同构、实际 cofiber map 的 IsIso、全部 finite/infinite Z/B、正反 quotient map；generic 结果只含三基础公理。 |
| 该 presentation 的正页微分与 canonical 微分相容 | 已有实际 Lean 检查 | 对任意 `r ≥ 2`、任意 source representative/lift；实际 fixed 对象桥仍依赖五个已登记上游责任。 |
| `classical` 所选实现的 `r < 2` 微分零性 | 尚未提供 | 不能从 `firstPage=2`、`d²=0` 或 presentation 的正页公式直接读取。 |
| 经典退化可传至 synthetic 的任意权重、全部 `r ≥ 2` | 条件性完整证明已实际检查 | 调用同一 `model` 的 `inversion_differential`、`free_component`、`free_inversion`、`above_diagonal`。 |
| 原 `N` 可以小于 2 | 是 | 原公共目标及 `DegeneratesAt` 中 `N : ℤ` 无额外前提。 |
| synthetic 所选实现的 `N ≤ r < 2` 微分零性 | 尚未提供 | 已有精确 iff，证明这恰是原退化结论相对正页结果所剩部分。 |
| 已有完整固定模型反例 | 否 | 本报告没有构造完整模型，更没有替换 `model` 或从待补事实推出矛盾。 |

## 独立证据与复现

本报告员未参与发现或实现上述证明，独立阅读了原结构、两个目标、canonical 实现、已有证明全文及实际日志。没有运行新的 Lean、没有写 `.lake/build/`；以下是**核验既有实际执行证据**，不是声称本报告员重新执行过它们。

这些实际探针读取本轮 η/ν 补证前的已成功编译输入：Background 源哈希为 `0bf990cb42552b79289537ad90e762a59bec02e52f5ada53dee201e89af96f34`，Literature/Standard 为 `fb25dc2185804f5475e379d50fd1afa39e2c3154ab064ea7aa3aaecc559cbd0a`。本报告写入时，协调者已整合 η/ν 同接口证明，当前两源分别为 `d663cb50…87dba`、`a1c0f66c…a5729`，canonical cache 正在重编。本报告未把旧缓存探针冒认为当前新源码的全量编译结果。被讨论的 `classical`、`classicalTower`、退化目标签名及其对象关联没有在 η/ν 补证中改动；新构建的最终结论另由协调者记录。附件 [tower 实际编译输入记录](evidence/TowerComparison-worker-result.json)区分这两种输入。

[源码和日志清单](evidence/checked-source-manifest.json)记录当前接口源码/三个接口锁哈希，以及以下每份附件的 SHA-256。三次运行均核对 `exit_code = 0`、源码哈希与实际 `.lean` 一致、日志哈希一致；每份附件小于 1 MB。

报告格式检查：只读复用原仓库已有的 `/inspire/hdd/global_user/czxs25250150/Kervaire126Main/.lake/blueprint-env/bin/python`，在本工作树实际运行原 `scripts/interface-proposals.py validate`，exit 0，输出 `Validated 25 interface reports.`。另核对了本报告全部附件链接、SHA/大小、无空人审批准。[准确检查记录](evidence/metadata-validation.json)保留了先前默认 Python 缺少 hgraph、工作树内无 blueprint-env 的环境失败，以及原始 `read_reports` 元数据检查的实际通过；这些早期失败未冒认通过。没有安装环境或修改验证脚本；完整网站渲染不在本次静态审查范围。

1. [TowerComparison.lean](evidence/TowerComparison.lean)、[实际运行记录](evidence/TowerComparison-run.json)、[日志](evidence/TowerComparison.log)：`lake env lean <原记录中的 TowerComparison.lean 绝对路径>`，无 `-o`，7.682 秒，exit 0。完整 stage/cofiber/SSData/正页桥；打印的六个 generic 根均只含 `propext`、`Classical.choice`、`Quot.sound`。
2. [TowerComparisonActual.lean](evidence/TowerComparisonActual.lean)、[实际运行记录](evidence/TowerComparisonActual-run.json)、[日志](evidence/TowerComparisonActual.log)：同样 `lake env lean <原记录中的 TowerComparisonActual.lean 绝对路径>`，无 `-o`，8.048 秒，exit 0。实例化到实际 `classicalTower` 和 canonical tower。其完整直接待补闭包为 `classical`、`classicalTower`、`coefficients`、`spectrumCategory`、`spectrumCofiber`；未使用所欲证明的 `classical_canonicalIso`。
3. [DegenerationRange.lean](evidence/DegenerationRange.lean)、[实际记录](evidence/DegenerationRange-result.json)、[日志](evidence/DegenerationRange.log)：`lake env lean -j4 <原记录中的 DegenerationRange.lean 路径>`，无 `-o`，exit 0。证明全部 `r ≥ 2`、额外条件 `2 ≤ N` 的完整版本，以及：

```lean
-- 在原经典退化前提 hD 下，保持同一个固定对象：
DegeneratesAt syntheticSequence N ↔
  ∀ (r : ℤ), N ≤ r → r < 2 → ∀ (p : Tridegree),
    syntheticSequence.d r p = 0
```

这里 `syntheticSequence` 仅是正文中 `(model.family.nu model.nu (X.obj model.auxiliary)).sequence` 的排版缩写，附件为全式。该证明用到仍未补的项目上游，打印有 `sorryAx`；它没有新增洞，没有用 `degeneration`、Main、E₂/后续 Adams 计算或 BHS 结果包。不能据此宣称最终无未证依赖。

### 泛型范围差的数学模型说明

下面仅说明为什么不能从泛型谱序列公理推出所有低页微分为零，**不是当前 `classical`、`family` 或完整 `Model` 的反例**，也没有声称已 Lean 形式化此模型。

取 `ModuleCat ℤ`、双次数、`r₀=2`、`diffDeg r=(r,r-1)`。只在 `p=(0,0)` 和 `q=(1,0)` 令 ambient 为 `ℤ`，其余为零；全部有限/无限 `Z=V`、`B=0`，故所有这些商页都为 `V`。令全部 `r ≥ 2` 微分为零。在 `r=1` 可令 `p→q` 的微分为 `id_ℤ`，其余低页微分为零。此低页微分平方为零；正页的核像条件均满足。将唯一的 `d₁` 再改为零，得到另一个完全相同正页/Z/B 的泛型谱序列。

二者有相同的 `firstPage`、次数、所有 Z/B、所有正页微分，却不能用可逆页映射满足该 `d₁` 的交换方块：一边为可逆映射，另一边为零。零低页版本满足 `DegeneratesAt _ 1`，非零版本不满足。因此 `Page r` 在起始页之前复用索引 0 不能充当“低页对象为零”或“低页微分为零”的证明。

此模型未满足/建立与实际 coefficient tower、完整 stable category/family、固定 `model`、文献比较数据的全部联系。不得把它升级为两个实际公共目标的反例或已证明不可证明性结论。

## 方案及精确差异

### A．保持全部公共接口，在既有实际构造中补低页事实（首选继续项）

不改变任何原签名，不新增公共声明、假设、公理或待补条目。继续构造指定的两个 family，并在模块内部真正证明：

```lean
-- 仅展示内部证明义务，不提议新增 public 接口或登记新洞：
∀ (X : Spectrum) (r : ℤ), r < 2 →
  ∀ p : ℤ × ℤ, (classical.obj X).d r p = 0

∀ (X : ClassicalObject) (r : ℤ), r < 2 → ∀ p : Tridegree,
  (model.family.nu model.nu (X.obj model.auxiliary)).sequence.d r p = 0
```

若来自实际生产者，可将这些私有证明与本轮正页桥结合，保持两个原公共目标完全不变。现有 canonical producer 的低页定义已是零；尚缺到另一侧所选 family 的真实识别，不能把 generic presentation 当成该识别本身。当前无法保证实际 family 构造的剩余自然性/函子律已经完成；这部分原有责任不会因本报告而消失。

### B．加强 `TowerSequencePresentation`，统一要求指定低页为零

保留 `DegeneratesAt`、两个 `comm_d` 和两个目标的原语义；在上面给出的完整原 `TowerSequencePresentation` 四组字段后，增加第五个字段：

```lean
  differential_before_first : ∀ (r : ℤ), r < 2 →
    ∀ p : ℤ × ℤ, d r p = 0
```

原/新差异恰为这个新字段，所有既有参数、`ambient/cycles/boundaries/differential` 保留原样。此候选加强 presentation：旧实例不一定是新实例；低页零性证明由该 presentation 的实际构造者承担。`classicalTower.sequence` 及 `syntheticTower.sequence` 继续关联原来的 fixed objects。经典低页零性可由 normalized differential 的可逆传输得出；synthetic 侧对每个固定权重同理。这不允许只给新字段填 `sorry` 再宣称两项整体已解决。

责任实质属于 AdamsSynthetic 的 tower presentation 生产者。若批准，需要协调 AdamsSynthetic、泛型接口锁/测试与调用方，不能仅在 SpectralSequence 报告目录改写一个锁绕过检查。canonical presentation 的新增字段可由现有 `if ... else 0` 定义证明，但其他构造者仍需逐一验证。

### C．泛型约定改为只约束有效页

这是更广的替代方案，与 B 不混同。完整原 `PreSSMorphism`/`SpectralSequenceMorphism` 的其余字段全部不动，仅将上述完整 `comm_d` 签名中的

```lean
comm_d : ∀ (r : ℤ) (k : ι), <上文逐字给出的交换等式>
```

分别改为以下准确字段签名（其余结构字段和全部参数/实例均原样保留）：

```lean
-- PreSSMorphism E E'：
comm_d : ∀ (r : ℤ) (hr : E.r₀ ≤ r) (k : ι),
  toSSDataMorphism.pageMapAt r₀_eq r k ≫ E'.d r k =
    E.d r k ≫ toSSDataMorphism.pageMapAt r₀_eq r (k + E.diffDeg r) ≫
      eqToHom (by rw [diffDeg_eq])

-- SpectralSequenceMorphism E E'：
comm_d : ∀ (r : ℤ) (hr : E.r₀ ≤ r) (k : ι),
  let f : SSDataMorphism ι E.ssData E'.ssData :=
    { φ := φ, preserves_Z := preserves_Z, preserves_B := preserves_B }
  f.pageMapAt (E := E.toPreSS) (E' := E'.toPreSS) r₀_eq r k ≫
      E'.d r k =
    E.d r k ≫ f.pageMapAt (E := E.toPreSS) (E' := E'.toPreSS)
      r₀_eq r (k + E.diffDeg r) ≫ eqToHom (by rw [diffDeg_eq])
```

`hr` 不出现在等式内。对 `DegeneratesAt` 的完整候选则是：

```lean
public def DegeneratesAt
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (E : SpectralSequence C ι) (N : ℤ) : Prop :=
  ∀ (r : ℤ), N ≤ r → E.r₀ ≤ r → ∀ (k : ι), E.d r k = 0
```

在 `N ≥ E.r₀` 时退化命题等价；在 `N < E.r₀` 时新命题更弱。态射条件也更弱，会扩大允许的态射集合，改变整个 `SpectralSequence` 范畴和相关公开引理的语义，必须同步调整 `pageMap_comm_d`、态射的 identity/composition、类别结构和每个调用位置，不能只改变两个目标的证明。所有 ambient 和有限/无限 Z/B 要求仍保留，不能用较弱的 `PagewiseIso` 替代完整对象比较。

现有 `PagewiseIso.comm_d`、Literature 的私有 `FromFirstMorphism.comm_d` 已采用有效页前提，说明项目里并存两种范围；这只支持问题定位，不等于已获全局改变的授权。

### 不作为默认修复的方案

给 `classical_canonicalIso` 增加低页零性的调用方假设、给 `degeneration` 增加 `2 ≤ N`、改选 unrelated 的零 family、从 `classical_canonicalIso` 自身反推所需低页事实，都不能当作保留原接口的补证。前两者会改变公共目标并把证明责任交给下游；后两者改变固定对象或形成循环。本报告不提出默认实施它们。

## 下游影响

| 方案/声明 | 责任与受影响调用方 | 记录与验证范围 |
| --- | --- | --- |
| A：仅内部真实补证 | AdamsSynthetic 的实际 family/tower 生产者；Literature 的 `degeneration`。 | 保留所有公开类型/宇宙/对象/导出；仅据实际 proof 更新待补状态和真实公理依赖，普通导入检查、全部既有测试及完整构建。 |
| B：新增 presentation 字段 | `TowerSequencePresentation` 及所有构造者；`ClassicalTowerPresentation.sequence`、`SyntheticTowerPresentation.sequence`、canonical presentation。 | AdamsSynthetic API 的结构/构造器/新字段、两标准 tower 生产者与 pending 依赖必须重新核对；不得新增未获准洞。泛型 SpectralSequence 的原声明不变。 |
| C：有效页语义 | `PreSSMorphism`、`SpectralSequenceMorphism`、其 category/identity/comp、`pageMap_comm_d` 和 `DegeneratesAt`；上游比较/后续计算中的调用须补真实页范围。 | SpectralSequence API 首先变化；八模块消费、Architecture/Integration/Trust 必须完整重跑。不能声称只影响一个实现文件。 |
| `classical_canonicalIso` 的现有依赖链 | `classicalSphere_sourceIso`、`nonzeroSurvival_source_iff`、`canonicalE2ClassOfCycle` 的后续识别与 `Tests.AdamsSynthetic.Structural`。 | A/B 保留这条完整 ambient+∞ 比较的原语义；C 改变其所在范畴对低页的要求，需要明确审阅。 |
| `degeneration` 的现有记录 | `Literature.Rigidity` 的私有旧结果字段、Literature Blueprint 条目及对应 hgraph 绑定。 | A/B 陈述不变；C 的原字面签名虽可不变，其 `DegeneratesAt` 语义会改变，必须明确同步说明。 |

这是形式化起始页约定与证明桥接问题，目前没有核实相对 AimPaper 的新数学修正；故没有写入或另建平行 `corrections.yaml` 修正条目，也没有改 Blueprint 绑定。若人审决定涉及论文数学陈述，须另按现有唯一修正源规则处理。

## 阻塞范围与继续项

本报告精确定位当前两条路线的剩余缺口：`classical_canonicalIso` 的低页微分相容；`degeneration` 在 `N ≤ r < 2` 的低页零性。两个公共原目标继续保留待补，正页私有结果不计为公共目标关闭。

这不是“已有固定对象反例导致整个依赖闭包应暂停”的判定。已有上游接口仍按仓库规则消费；本轮 η/ν 非零永久存活、其他 E₂ 坐标桥接、cofiber 标定、HF₂ unit-kernel 与有限 lift 一致性等独立工作可继续。报告不把无批准视为必须停工，不修改公共接口、锁文件、生产数学源码、现有待补登记或构建缓存。

## 人类审核记录

尚未收到针对本报告方案、目标和范围的明确人类决定。`human_decision: null`。本报告员意见、协调者派发任务、其他提案的批准或用户要求继续补证，都不构成 B/C 的接口变更授权。
