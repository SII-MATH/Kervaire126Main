---
issue_id: AdamsSynthetic-20261019-paper-complete-fixed-background
title: 统一论文固定对象的完备背景与一次性 λ 反演比较
summary: 用户已明确将跨模块完成背景迁移延期至 issue #31；普通源、完成模型与配套合成比较留待后续。当前只将既有已证代表元定理绑定原文节点，不实施本提案的接口迁移。
responsibility_module: AdamsSynthetic
targets:
  - KIP126.AdamsSynthetic.Standard.Spectrum
  - KIP126.AdamsSynthetic.Standard.SyntheticSpectrum
  - KIP126.AdamsSynthetic.Standard.sourceRecognition
  - KIP126.AdamsSynthetic.ClassicalSourceRecognition
  - KIP126.AdamsSynthetic.Standard.recovery
  - KIP126.AdamsSynthetic.Standard.auxiliary
  - KIP126.AdamsSynthetic.Standard.classicalTower
  - KIP126.AdamsSynthetic.Standard.syntheticTower
  - KIP126.Literature.LambdaInversionAdamsComparison
baseline_commit: ef01dcfd904b51fe2288f0dc3e1eed074591967f
worktree: /inspire/hdd/global_user/czxs25250150/ops/tmp/prooftools-main-proofs-20261019
reporter_agent: /root/convergence_reporter
independent_of_discoverer_and_implementer: true
evidence_level: 独立源码与完整类型约束审查、公开主来源核对；没有完成范畴迁移证明或新实例构造，也没有完整模型反例
status: pending-human-review
human_decision: null
tracking_issue: https://github.com/SII-MATH/Kervaire126Main/issues/31
implementation_status: deferred-by-user
---

# 论文完备固定背景：范围与实施顺序提案

## 请求人类决定的具体问题

**当前已按用户明确要求延期实施，后续统一跟踪于 [issue #31](https://github.com/SII-MATH/Kervaire126Main/issues/31)。** 本轮只调整原文节点的已有形式化绑定，不进行本提案的跨模块对象、公共接口或锁变更。

**建议把论文使用的对象及适用范围在上游固定一次，保留普通来源供几何与整数稳定同伦使用。** 这会影响多项对象关联，不只是2.20和5.14。需审核的新增范围是：拆开普通谱识别与完成谱识别；统一选用完成球、完成的 Hopf cofiber、完成 tmf；配套核实合成范畴、张量单位、ν和λ恢复；构造一次适用性及实际塔比较，再给固定论文系统提供无需额外背景binder的推论。

**已有2.20三个自然前提、5.14的R/hcomp局部修改及其条件证明授权继续有效，不重复请求。** 本次待决定的是跨模块固定对象迁移。用户“把2完备谱这个条件直接组装进我们的固定对象”的方向意见及“继续”授权开展本项研究，尚不等于批准以下精确源识别/单位/恢复变更。建议按下面两阶段审核：先确定分层与数学构造范围；配套完成合成背景的具体实现、确切公开名及变更清单可审核后再实施，不凭本报告直接改锁。

不申请新增公理或sorry来替代构造，不把5.14目标结果填入Model，不把全部上游未完成责任或全部经典ESS构造纳入本次迁移目标。

## 原接口、背景与问题成因

原文已把完成性当作范围约定：[AimPaper §2](https://arxiv.org/html/2412.10879v1#S2)指定全篇对象为2-completed、connective、finite type；本地 `AimPaper/main.tex:138` 指定完成球，`:791` 的λ反演使用完成谱惯例。当前固定背景的类型却受到普通来源识别约束。

```lean
-- KIP126.AdamsSynthetic.Standard；固定实例的原始公开类型
public def Spectrum : Type 1 := by sorry
public def SyntheticSpectrum : Type 1 := by sorry
public def sourceRecognition : ClassicalSourceRecognition Spectrum coefficients := by sorry
public def recovery : LambdaRecovery nu := by sorry
```

这不是可随意改注释的空白：`ClassicalSourceRecognition C H`展开为普通 `Source.SourceRecognition C H`。对 `universe u v`、`C : Type u`、`[StableHomotopyCategory.{u,v} C]`、`H : ModTwoCoefficients C`，其字段包括

```lean
equivalence : SourceCategory.{0} ≌ C
sphereIso : equivalence.functor.obj (sourceLocalization.obj Prespectrum.sphere) ≅ SphereSpectrum
homotopy : ∀ (X : Prespectrum.{0}) (d : ℤ),
  HomotopyGroup d (equivalence.functor.obj (sourceLocalization.obj X)) ≃
    Prespectrum.StableHomotopy X d
```

还有相同源对象上的实际悬挂/解悬挂自然性、零与加法、球正生成元、HF₂对象/π₀坐标及单位兼容。**完整原字段与相关声明见[精确源码摘录](evidence/original-interface-excerpts.md)**，宇宙、实例、原固定参数不省略成任意比较包。它要求普通球的整数稳定同伦，不能在维持此识别时再声称该球本身已完成；普通球π₀与完成球π₀也有不同语义。现有背景虽有登记sorry，这些类型约束仍不能当作不存在。

已核对[2026-10-17普通球分离性原批准](../20261016T1625-ordinary-sphere-separation/report.md)：当时明确保留ordinary语义，只批准有限λ商分离性及普通球上的odd-torsion结论，未批准完成路线。本次提案保留其普通来源侧和有效结论，不撤回原批准。普通球奇挠导致未分离的见证不是AimPaper完成范围中的反例；新背景研究也不表示所有既有证明错误。

`Source.lean:142–179`已经定义同一HF₂各整数移位的上同调等价类及其**范畴局部化**；`Internal/Source/Completion.lean:24–27`明确尚未把它识别成反射完成范畴或论文完成模型。`Standard/Source.lean:237`的

```lean
public def localizedSphere_classicalIso : localizedSphereSequence ≅ classical.sphere
```

是Adams**谱序列**同构，不是完成球与普通球的谱同构，也不提供同伦滤过的完备性。分类是固定对象/来源范围未统一及构造比较缺口，不是已证所有定理错误，亦不是原文数学反例。

## 真实前提与对象核对

| 项目 | 已确认事实与边界 |
| --- | --- |
| 经典对象 | `ClassicalObject`闭包为sphere、实际ν cofiber、detector及任意整数shift。基本对象可connective；全部shift闭包只能要求bounded below，不能把整个ambient稳定范畴限制成connective。 |
| 完成性与有限性 | 应在实际完成来源和同一HF₂塔证明基本对象finite mod-2 type。`IsFiniteSpectrum`是球/shift/有限cofiber生成闭包，**不同于**finite type；tmf不可因finite type而冒充有限cell对象。 |
| 合成环境 | 现 `LambdaRecovery N` 完整签名为 `localization : LambdaLocalization Syn`、`equivalence : LambdaInvertibleObjects Syn ≌ C`、`nuLocalization : N.functor ⋙ localization.reflector ≅ equivalence.inverse`。其对象和单位必须与C同步。 |
| 来源中的λ恢复 | Pstrągowski完整Syn的λ/τ反演恢复普通Sp，并为ν左逆：[Theorem1.3、4.37及Proposition4.40](https://arxiv.org/pdf/1803.01804v3)。故只换经典codomain、保留完整Syn的原恢复不能算迁移证明。 |
| 2.20条件 | 对全部选定X、全部d须得同一实际滤过的canonical `CompletionWitness`、有限自然数层商及分离性；由有界下、完成、finite mod-2 type及实际Adams收敛理论在上游证明，不让每条下游重新证明。 |
| 5.14比较 | R与hcomp同样适合固定构造一次；但hcomp是系数/张量/塔/ZB/E₂兼容事实，**不是2-complete本身的逻辑推论**。已有条件定理保留同一a与a≫f、零类及边界类。 |
| 几何 | 真实framing与整数稳定同伦的Pontryagin–Thom来源保留普通语义；完成球到几何的桥仍归Literature既有Browder责任，不能用改名使其自动成立。 |

BHS区分强收敛的完备/Hausdorff及grade同构，其A.1保留nilpotent completeness和strong convergence条件；不能把E∞≅gr当作这些条件已经实现。[BHS Definition9.17、TheoremA.1](https://arxiv.org/pdf/1910.14116v3)

## 方案及精确差异

### 先评估保留原接口

可继续保持普通固定系统并在其**完成对象**上应用现有条件定理；但只在原 `SphereSpectrum` 上加“complete”性质不能修复普通源识别冲突。单独保留局部binder也不能给用户期望的“论文固定背景自动满足范围”接口。推荐保留泛型 `Model C Syn`及已证泛型证明，在其旁边真实构造论文完成实例；不在泛型Model塞结论型字段。

### 候选的核心数学接口

以下是**完整数学类型规格**，不是宣称可直接编译的Lean补丁；名称为拟议名。取普通稳定对称张量范畴O、完成稳定对称张量范畴C₂及配套合成范畴S₂，分别在明确的对象/态射宇宙中；迁移选用的固定实例仍须满足当前`{1,0}`接口或另报确切宇宙变化。新对象层要求：

1. **普通识别保留。** 将原固定识别移到
   `ordinarySourceRecognition : ClassicalSourceRecognition O HF₂_O`，保留其全部普通球、整数同伦及单位字段；原 `ClassicalSource` 定义不变。
2. **实际完成来源。** 构造精确局部化 `L₂ : O ⥤ C₂`、全忠实包含 `i : C₂ ⥤ O`、`L₂ ⊣ i`、单位 `q : Id_O ⟶ L₂⋙i`，并证明i的本质像为选定数学意义的2-complete对象。证明其与论文有界下范围的完成一致。C₂的单位为`L₂(S_O)`、张量为`L₂(iX⊗iY)`，保留实际系数等价`L₂(HF₂_O)≅HF₂_C₂`、单位、shift和cofiber兼容；不假定普通张量自动保持完成。
3. **完成识别。** 设Q为从普通源出发、对应所选完成等价类的实际局部化。拟议
   `completedSourceRecognition`提供 `E₂ : Source₂ ≌ C₂`及自然同构
   `Q ⋙ E₂.functor ≅ ordinarySourceRecognition.equivalence.functor ⋙ L₂`，连同同一完成球、HF₂、单位、悬挂/cofiber的实际识别。若复用现有 `ClassicalHF2LocalizedSource`，须先证明其上同调等价类与此完成模型匹配，不能默认。普通同伦通过q映入完成同伦；**不再要求**完成对象的同伦等于每个原普通谱的整数同伦。
4. **基本对象范围。** `S₂^cl=L₂ S_O`、`Cν₂=L₂(cofib ν_O)`、`tmf₂=L₂ tmf_O`及其单位/η/ν取同一实际源映射的像。证明三个基本对象connective、每个次数HF₂同调有限；对整数移位闭包证明bounded below及同样有限型。C₂的ambient不限制finite type或connective，不把tmf加入有限cell生成定义。
5. **配套合成与恢复。** 构造实际S₂、`ν₂:C₂⥤S₂`、bigraded shifts及λ，使其满足当前`NuFunctorData`、`LambdaRecovery`及`StructuralExactness`的**全部原字段**，特别
   `LambdaInvertibleObjects S₂ ≌ C₂`、`λ⁻¹ν₂≅Id_C₂`、`ν₂(S₂^cl)≅1_S₂`。完成合成环境/限制的选择、局部化单位、tensor及λ商比较均须核实，不能将完整Syn的旧实例原封不动重用。本报告尚未选定或证明这种S₂构造，也不宣称“在Syn加complete谓词”已经足够。

在以上对象、实际HF₂单位及塔构造完成后，拟议上游交付是**证明定理**而非新增未经构造的假设字段：

```text
D₂ : Model C₂ S₂                          -- 实际完成的论文实例
selected_adams_scope :
  ∀ X : ClassicalObject, ∀ d : ℤ,
    Nonempty (CompletionWitness (actualTower D₂ X).filtration d)
    ∧ (∀ n : ℕ, Finite (π_d(X₂) / Fⁿπ_d(X₂)))
    ∧ (∀ a : π_d(X₂), (∀ n : ℕ, a ∈ Fⁿπ_d(X₂)) → a=0)
R₂ : RealizationCoordinates D₂
hcomp₂ : LambdaInversionAdamsComparison D₂ R₂
```

hcomp₂由Literature在实际完成语境构造；其完整字段沿用[已有5.14提案](../../Literature/20261019-lambda-inversion-adams-comparison/report.md)与实际定义，不重复列字段或另造Detects结果包。`selected_adams_scope`是需要证明的自然范围后果；不能以一个带该字段却未构造的wrapper宣布完成。BHS所需residual tower的nilpotent completeness也仍须证明，不由此三行条件默默替换。

随后ProofTools可新增固定实例推论，分别将已证2.20、5.14中的D替为D₂，保持各自**其余原始对象、映射、类、前提及结论逐字不变**，由上游固定交付消去三个范围binder或R/hcomp。泛型条件定理保留，固定推论不再要求调用者重复供应这些固定数据。具体公开名需列入获批清单，不能擅自覆盖原泛型名。代表元版的数学依据已有AimPaper Proposition2.5(1)；当前ESS formal correspondence边界单列保留，本提案不要求重新构建全部经典ESS，也不把表达形式差异算作论文修正。

### 仍待确定，不能当成已完成补丁的部分

必须先明确2-completion的全ambient精确定义及它与当前HF₂上同调局部化的适用范围；选定并证明配套S₂/单位/recovery；确定普通源与完成源公开声明的改名/迁移映射；构造hcomp₂的系数及实际tower比较。不得把HF₂ nilpotent、Moore(2) completion、HF₂ localisation在所有无界对象上无条件等同。这些是研究/实施前置边界，尚无已证迁移，不新增sorry代替它们。

## 下游影响与实施顺序

| 模块/实际声明 | 需处理的范围 |
| --- | --- |
| **AdamsSynthetic** `Standard.Spectrum/SyntheticSpectrum`、`sourceRecognition`、source tensor/cofiber recognition、`recovery/nu/coefficients/auxiliary`、双塔及canonical comparisons | 普通源识别保留另名；论文Standard对象语义迁到完成实例。`Standard/Source.localizedSphere_classicalIso`保留为谱序列比较，完成来源识别另证。`IsFiniteSpectrum`、`Standard.FiniteSpectrum`随新单位成为完成球有限cell闭包；原有限映射/odd-torsion/有理无环条件逐项核对，不改成finite type。 |
| **Literature** `BHSObjectApplicability`、BHS适用性、`Standard.tmf/tmfIso/tmfUnit/tmf_convergence`、R₂/hcomp₂、`Geometry.browder_iff` | 在完成对象及其实际单位上重新识别来源；保留BHS适用性证明与普通几何到完成检测的既有桥接责任。不得整体把待补打包成新公理。 |
| **E2Computation**独立基底/维数/乘法与`Computation.Standard`实际页比较 | 独立Ext数据通常不变；与新`D₂.classical`实际E₂、hᵢ及其乘积的比较须重接并证明单位/标准类标定，仍不得依赖ProofTools。 |
| **ProofTools / AdamsCalculations / Main**泛型引理及固定Standard调用 | 泛型证明尽量直接复用；固定背景改变的实际类型、标签、ν cofiber及比较调用需重核。新增固定2.20/5.14推论不反复搬移责任；不能据本提案宣布此前已证定理数学错误或无条件迁移完成。 |
| **Geometry**两项公开几何推论 | 其真实流形目标及无本地洞结构保留；通过Literature.Browder连到完成球。不能把普通framed存在性直接改成完成谱定义。 |

建议顺序为：**先**列齐ordinary/completed source与配套Syn/recovery精确签名及证明构造；**再**完成基本对象、真实单位与双塔来源比较和统一范围定理；**随后**由Literature构造固定hcomp、ProofTools提供固定推论；**最后**按上表逐层迁移实际页/标准类和调用，统一更新获准模块接口锁、既有责任及测试。每步保留原未完成边界，不把新增producer sorry当作替换原洞。

对应记录为 `interface/baselines/{adams-synthetic,literature,e2-computation,proof-tools,adams-calculations,main,geometry}-api.json` 中实际受影响的类型/宇宙/依赖/导出，以及 `proof-obligations.json`。只更新真实变化，不盲刷全部锁。检查应覆盖 `Tests/AdamsSynthetic/{Structural,Background,System,Filtration}.lean`、Literature/E2/ProofTools消费测试、`Tests.Architecture`、`Tests.Integration`、`Tests.Trust`及既有全部覆盖。Blueprint按八章实际public归属同步背景与引用；相对AimPaper的修正仍仅在根`corrections.yaml`维护。本报告不另建论文修正版。

## 独立证据与复现

独立读取上述完整源码及现有局部提案，并实际通过web打开/查找三份主来源；摘要与定位见[主来源核对](evidence/primary-source-check.md)。[读取清单](evidence/read-manifest.json)保留基线及相关文件SHA-256；[小型原接口摘录](evidence/original-interface-excerpts.md)保留关键完整字段。可复核命令为在本worktree运行 `sed -n '29,100p' KIP126/AdamsSynthetic/Internal/Source/Recognition.lean`、`sed -n '140,181p' KIP126/AdamsSynthetic/Source.lean`及`sed -n '228,251p' KIP126/AdamsSynthetic/Standard/Source.lean`，对应输出已核对。

证据等级为独立对象/签名/来源审查，不是完整模型反例、已证范畴迁移或编译证书。本轮没有运行Lean或全量检查，只写本指定目录。没有从普通源的既有sorry导出False来否定模型，也没有调用Main目标反向构造背景。已有2.20/5.14条件证明的独立审计仍有效，但不证明Standard范围定理或hcomp₂已经构造；它们的证据保留在各自原报告，不大规模复制。

## 阻塞范围与继续项

等待精确批准/构造的是**固定对象跨模块语义迁移**。已有泛型证明、已获准局部binder方案及不依赖本迁移的补证可继续；无需因本提案冻结所有模块。研究配套完成Syn、普通/完成源比较和责任清单在当前“继续”授权内可以进行。工程实施、锁变更、网页状态同步及完整构建应在具体范围获准、实际构造后由协调者安排，不能以范围提案本身消除待补。

## 人类审核记录

本轮方向意见的真实用户原话，由协调者在本session派工转发：

> 这确实不需要从论文背景推出，论文默认讨论的范围就是满足这些条件的对象吧。

随后针对hcomp：“这个是不是同理。”继而：“这个问题会不会影响其他条目啊，感觉应该把2完备谱这个条件直接组装进我们的固定对象啊。”后续指令为：“继续”。

记录为研究与提案授权；尚未收到针对本报告精确普通/完成源拆分、配套合成背景、跨模块固定对象迁移清单的明确决定。故 `status=pending-human-review`、`human_decision=null`。现有2.20/5.14局部修改授权保持，不因本报告重复征询或撤回；本报告也不扩大成对所有上游缺口、全部ESS构造的批准。


### 后续决定：延期迁移并统一原文绑定

2026-10-19，当前session用户明确指示：

> 这个是一个大改动，改了这个接口以后下游多个文件都要改，因此，先把这项改动挂到 issue，我们后面再改。现在，先把我们已经完成形式化的对象绑定到灰色节点，不再单独设改写的自然语言版本。因为结论是一样的，我们只是补全了论文当中默认的背景而已

已据此创建 [issue #31](https://github.com/SII-MATH/Kervaire126Main/issues/31)。该决定批准本轮将已有证明直接绑定 `paper:2.20` 与 `paper:5.14`、取消两个独立改写节点，保留原文及背景/实际Standard未完成范围；它明确推迟本报告的跨模块迁移，未批准立即修改固定对象公共语义。因此接口提案仍为 `pending-human-review`，`human_decision` 仍为空，具体迁移由后续issue推进。
