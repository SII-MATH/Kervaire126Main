---
issue_id: AdamsSynthetic-20261019-paper-complete-fixed-background
title: 统一论文固定对象的完备背景与一次性 λ 反演比较
summary: 用户已批准含整族非零字段的标准类结构及结构版主定理迁移，并确定论文 Standard 最终采用完成系统、普通来源保留独立入口。本轮实施可由已有公共输入推出的修改；完成背景落实精确规格与责任地图，实际完成范畴、配套合成模型及来源和塔比较仍归上游，issue #31 尚未解决。
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
  - KIP126.Classical.Adams.StandardSphereClasses
  - KIP126.AdamsSynthetic.Standard.standardClasses
  - KIP126.Computation.Standard.h6_exhaustive
  - KIP126.Main.h6_sq_permanent
baseline_commit: ef01dcfd904b51fe2288f0dc3e1eed074591967f
worktree: /inspire/hdd/global_user/czxs25250150/ops/tmp/prooftools-main-proofs-20261019
reporter_agent: /root/convergence_reporter
independent_of_discoverer_and_implementer: true
evidence_level: 独立源码与完整类型约束审查、公开主来源核对；没有完成范畴迁移证明或新实例构造，也没有完整模型反例
status: partially-approved
human_decision: "2026-10-21，本聊天用户确认采用含整族 hi_ne_zero 的结构版并授权按有界计划实施；论文 Standard 最终采用完成系统，普通来源保留独立入口。本轮完成背景工作限于精确规格、责任地图及可由现有公共输入导出的迁移，不授权新建底层谱或合成模型、完成理论、cobar/resolution 工具，亦不以新增公理或待补责任替代缺失构造。具体范围见文末后续决定。"
tracking_issue: https://github.com/SII-MATH/Kervaire126Main/issues/31
implementation_status: bounded-interface-implemented-and-validated-foundations-deferred
---

# 论文完备固定背景：范围与实施顺序提案

## 当前范围

**2026-10-21 获批的有界接口改动已实现并通过完整验证。** 本轮把标准类整族非零性纳入结构，并将唯一对外主定理统一为该结构上的直接平方陈述；同时在本报告明确完成背景的精确规格和上游责任。当前尚未构造完成范畴、配套合成模型或实际来源比较，不能据此把现有 `Standard` 宣布为已完成迁移。具体授权、下游范围和验证边界见文末。以下原报告及其历史审核记录保留，描述的是当时的提案与决定，不代替本次实际实施结果。

## 2026-10-19 原提案问题（历史）

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

### 后续决定：结构版主定理与有界实施

2026-10-21，用户明确纠正主定理方案，确认的是把非零性放进整族标准类规格的结构版，并要求：

> 好，就按这个结构版，把公共接口改动、证明责任和下游影响清单重新统一一遍，明确本轮完成哪些、哪些留给上游，先别改代码。

在范围统一后，用户授权：

> 好，就按照这个计划，行动

此前用户还同意论文使用的 `Standard` 最终代表完成系统，普通来源保留在独立入口；同时明确不把本次工作扩大为 Milnor cobar/resolution 工具、具体谱或 synthetic 谱模型、完成理论及全部底层来源识别的建设。本次批准限于以下可审阅范围，不表示上文全部候选构造已经实现或被证明。

| 本轮公共接口与消费者 | 授权改动及证明责任 | 当前实施边界 |
| --- | --- | --- |
| `KIP126.Classical.Adams.StandardSphereClasses` | 在既有 `hi` 上增加 `hi_ne_zero : ∀ i : ℕ, hi i ≠ 0`，不把维数或唯一性写进标准类定义。 | 构造者须提供证明；不得添加公理或新的来源待补项来填该字段。 |
| `AdamsSynthetic.Standard.standardClasses` | 从既有 Milnor 类的非零性及实际 E₂ 线性等价证明固定整族非零，补齐结构构造。 | 继续继承 `sphereE2_milnorEquiv` 原已登记的构造责任；该推导不证明此等价的实际来源、第一微分或乘法兼容已经完成。 |
| `KIP126.Computation.Standard.h6_exhaustive` | 由既有独立 E₂ 坐标证明实际 `(1,64)` 页中每个元素为零或固定 `h₆`；供任意符合新规格的结构族识别其第六类。 | 归属 E2Computation，不调用 ProofTools 或后续 Adams 计算，不以额外标准类公理替代坐标证明。 |
| `KIP126.Main.h6_sq_permanent` | 保留这一个对外主定理名称，接收同一实际球 E₂ 上的 `StandardSphereClasses`，结论直接陈述其第六类与自身的实际乘积在 `(2,128)` 非零存活；既有指定类证明转为私有并复用。 | 不另增逐元素版或公开指定类版；Main 保持无直接证明洞。 |
| Geometry、Main 其余调用及公共消费测试 | 原固定调用显式传入 `model.standardClasses`；同步真实受影响的接口锁、待补清单状态与必要的 Blueprint 陈述和绑定。 | Geometry 保持无本地证明洞；Blueprint 阅读顺序调整留待后续，不在本轮重排。 |

完成背景的本轮交付是精确规格与责任地图；上文核心数学规格继续保留。其尚未具备的生产者按下表归属上游，不能改为由下游调用者提供结果包，也不能靠重新打包或重命名消除责任。

| 固定对象／公共接口 | 完整上游责任及本轮处理 |
| --- | --- |
| `Standard.Spectrum`、`spectrumCategory`、`spectrumCofiber`、`coefficients` | 实际完成范畴 `C₂`、`L₂ ⊣ i`、全忠实包含、本质像的完成性，以及球、HF₂、单位、张量、shift/cofiber 的实际识别尚未构造。本轮不改变现有普通来源所约束的对象语义。 |
| `ClassicalSourceRecognition`、`Standard.sourceRecognition` 及 source tensor/cofiber/derived smash recognition | 原完整普通源等价、整数稳定同伦及单位标定保留；独立普通入口和完成入口的精确公开命名仍待实际构造确定。完成识别须提供同一来源局部化与 `L₂` 的自然比较，不能原封不动继承普通整数同伦等价。 |
| `Standard.SyntheticSpectrum`、`nu`、`recovery`、`exactness` | 配套 `Syn₂` 的选择与构造尚未完成。必须提供当前 `NuFunctorData`、`LambdaRecovery`、`StructuralExactness` 的全部字段，尤其同一实际 λ 可逆子范畴与 `C₂` 的等价、ν 的单位比较及恢复同构；本轮不削弱这些接口。 |
| `Standard.auxiliary`、`classical`、`family`、双塔、`comparison` 及实际 E₂ 标定 | 完成球、完成的实际 ν cofiber、完成 tmf、源映射及其双塔比较仍须在同一模型上构造。独立 Ext/E₂ 计算可复用，但完成实例上的实际页、标准类及乘法比较仍须证明。 |
| `Literature.BHSObjectApplicability` 及固定适用性 | 同一实际 HF₂ 塔的 residual nilpotent completeness、滤过完备性、分离性和 associated graded 比较仍须分别提供；有限滤过商还须在相同塔、相同选定对象及每个整数次数证明。不能由 `E∞ ≅ gr` 或现有范畴局部化自动推出。 |
| `Literature.LambdaInversionAdamsComparison`、固定 `RealizationCoordinates` 及 ProofTools 固定推论 | 实际 target、各权移位 target、塔与层映射、代表及 ambient 坐标、零／边界标签和 E₂ 标定的相容性仍归上游。完成性本身不产生这些数据；现有 2.20／5.14 条件定理保留，待实际生产者完成后再消去固定背景参数。普通几何到完成球检测的 Browder 桥仍归 Literature。 |

实质来源缺口有两处。首先，现有 `sourceRecognition` 的完整类型固定了普通源等价和整数稳定同伦标定，因此不能仅改 `Spectrum` 的说明便宣称完成化。其次，现有 `LambdaRecovery` 恢复的是同一个实际合成范畴的 λ 可逆子范畴，不能固定旧合成背景而仅替换经典范畴。现有 `localizedSphere_classicalIso` 是依赖既有 `sourceClassical_inverts_hf2` 待证项的谱序列同构，不是完成反射子、完成球同伦识别或滤过完备性证据。

因此，即使把普通源和完成源责任合并到同一个记录、使 `sorry` 数量不变，也会增加独立数学构造责任；本轮不作这种替换。完成范畴在全部 ambient 上的精确定义、与当前 HF₂ 上同调局部化的一致范围、配套 `Syn₂`、实际单位与 λ 商的比较均仍待上游确定。不能无条件混同 HF₂ nilpotent completion、Moore(2) completion 和现有局部化。

本次实施基于 `f17969a0c7839f7d47d550d5e8f8a0a0aa2ffe91`，工作树为 `/inspire/hdd/global_user/czxs25250150/ops/tmp/adams-complete-main-statement-20261021`。本补记记录获准范围及源码／完整类型的复核；原报告的 baseline、独立 reporter、来源证据和历史状态均予保留，不把旧证据冒充对本次 Lean 修改的独立编译核验。**本轮有界接口改动已实现并通过完整验证。** 三份接口锁与编译捕获一致：AdamsSynthetic 增加非零字段和必要生成证明，E2Computation 只增加 `h6_exhaustive`，Main 只改变唯一主定理的结构参数；其他五份 API、所有既有宇宙参数和公理依赖保持不变。完整捕获包含 23,852 项项目声明，原有 214 项待补责任精确保留，没有新增项目公理或失败占位。默认 `lake build` 通过全部 3609 项任务，Main、Geometry 无本地证明洞的审计与精确 Main／ProofTools 边界均通过；源码清单、49 项 Blueprint 测试和 7 项元数据测试通过。34 项既有诊断标签指纹经独立 kernel 表达式核对后迁移，未改变证明责任，方法见 `docs/metadata-baselines.md`。这些是本次实现与核验结果，不改写原报告的独立证据等级；`status=partially-approved` 不表示完成背景已经实现，[issue #31](https://github.com/SII-MATH/Kervaire126Main/issues/31) 仍保留上述上游边界，Blueprint 阅读顺序调整也仍留待后续。
