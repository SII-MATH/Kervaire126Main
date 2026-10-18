---
title: Computation 的公开封装与导出边界
archived_from: local-history/metadata/interface-reviews/Computation/20261017-exposure-01/report.md
archived_sha256: 04767132a7152b4046212426775df74b75d51bdc37e6f36c23ff11afa0aeb514
summary: "历史 Computation 封装提案；报告记录保持原接口的内部路线已通过验收。旧接口修改方案未实施且无批准记录。"
issue_id: 20261017-exposure-01
responsibility_module: Computation
targets: [generators, atomIndex, basisCount, basisMonomial, sourceComponent, sourceProduct, sourceUnit, sourceAtom, sourceGenerator, detectorComponent, detectorV2Sixteen, detectorBetaGFour]
baseline_commit: bef90640c4594af4db32c86837f9d95340d1e171
worktree: /tmp/kip-computation-20261017
candidate_source_commit: a484b981fad612eabe2bc7a01b54e049e9a01ce4
reporter_agent: /root/interface_reporter
independent_of_discoverer_and_implementer: true
evidence_level: Lean-4.32.2-source-review-and-isolated-formal-reproductions
status: pending-human-review
human_decision: null
---

# 接口调整人审报告

> 最终技术验收状态：当前 Standard `20aef905…` 的 fresh Computation 根构建、841 项原 git 锁完整类型全文/指纹/宇宙及精确公共导出、12091 声明 actual capture 均已通过并独立核对来源绑定；正式默认完整 `lake build` 亦已实际通过（3102 jobs），原 Main 两个证明及原预算保持。32 项直接责任消除、56 项保留，其中已消除项15项无项目待补依赖、17项仍有传递待补。basisCount 的 `[irreducible]` 默认Meta展开变化已披露。no_expose/privateInPublic 提案未实施，无需为已保持原接口的内部路线实施旧接口调整。本报告仍 `pending-human-review` / `human_decision=null`，没有人类批准记录。下文早期“尚待验证”与失败记录均为各自历史阶段，不代表当前验收状态。


## 请求人类决定的具体问题

目前不建议批准改变公开声明的 expose 属性：独立最小实验证明存在保留 expose 的内部实现路线，实际项目适配尚未验证。若这两种路线在实际对象上最终失败且协调者仍希望采用 no_expose，应由人类明确决定：是否仅允许本文列明的 12 个 Computation.Standard 声明取消普通 import 下定义体公开展开，同时保持名称、完整类型、宇宙、对象、前提及职责不变。该候选尚未获授权；本报告也不证明其必要性。若保留 expose 的内部方案通过项目验证，则不需要接口调整。

## 原接口、背景与问题成因

基线源文件 SHA-256：5cbbce723fdedb65daed9a10738ac11a03c5d39fb139fc9038fd0b97a0ea8d9c。
本次独立取样候选快照 SHA-256：6dbbbf37a9c65c216882c16ed94d9ee93ff8121f2de1ae3a366e949c1c2f7fdb。协调者持续写源码，报告所述候选以同目录 candidate-Standard.lean.txt 为准，不声明其为最终文件。

基线 12 个声明位于 `module` 文件的 `@[expose] section` 中，均为 `public noncomputable def`，构造体原为 `by sorry`。目的为完整源档案和分次坐标商代数、其原子及生成元，以及 tmf detector 坐标的指定类提供固定公开对象；与真实 Adams 对象的识别另外由 comparison 系列承担。原文完整文件见 baseline-Standard.lean.txt；完整 elaborated 类型、宇宙和已登记消费者见 interfaces.json。这里没有将历史 sorry 解释为真实构造。

本次迁移将实际生成元、基目录、商代数及 detector 数据放入私有实现；public exposed 定义体在导出上下文中直接引用 private 名称会受到 Lean module 可见性检查。添加 no_expose 能改变 elaboration 上下文，但也取消普通 import 的公开展开。该问题属于实现封装和公开归约行为的约定错配，不是假命题、漏数学前提、几何反例或计算表反例。公共完整类型哈希不记录所有这种行为差异，因此冻结脚本通过不能代替接口授权。

### 12 项完整原签名和候选差异

以下所有名称位于 `namespace KIP126.Computation.Standard`，宇宙参数列表均为空；原声明均继承 section 的 expose。每项候选仅在原声明前增加 `@[no_expose]`，完整类型逐字不变。原体 `by sorry` 被实际构造替换属于本 session 正常补构造；争议只在显式改变 expose。

原声明（完整 kernel 类型）：

```lean
@[expose] public noncomputable def atomIndex :
  KIP126.Computation.Atom → Fin KIP126.Computation.Standard.generators.count := by sorry
```

候选签名：

```lean
@[no_expose] public noncomputable def atomIndex :
  KIP126.Computation.Atom → Fin KIP126.Computation.Standard.generators.count := <迁移构造体>
```

原声明（完整 kernel 类型）：

```lean
@[expose] public noncomputable def basisCount :
  ℕ → ℕ → ℕ := by sorry
```

候选签名：

```lean
@[no_expose] public noncomputable def basisCount :
  ℕ → ℕ → ℕ := <迁移构造体>
```

原声明（完整 kernel 类型）：

```lean
@[expose] public noncomputable def basisMonomial :
  (s t : ℕ) →
  Fin (KIP126.Computation.Standard.basisCount s t) →
    KIP126.Computation.SourceMonomial KIP126.Computation.Standard.generators s t := by sorry
```

候选签名：

```lean
@[no_expose] public noncomputable def basisMonomial :
  (s t : ℕ) →
  Fin (KIP126.Computation.Standard.basisCount s t) →
    KIP126.Computation.SourceMonomial KIP126.Computation.Standard.generators s t := <迁移构造体>
```

原声明（完整 kernel 类型）：

```lean
@[expose] public noncomputable def detectorBetaGFour :
  ↑(KIP126.Computation.Standard.detectorComponent 19 114) := by sorry
```

候选签名：

```lean
@[no_expose] public noncomputable def detectorBetaGFour :
  ↑(KIP126.Computation.Standard.detectorComponent 19 114) := <迁移构造体>
```

原声明（完整 kernel 类型）：

```lean
@[expose] public noncomputable def detectorComponent :
  ℕ → ℕ → ModuleCat.{0, 0} (ZMod 2) := by sorry
```

候选签名：

```lean
@[no_expose] public noncomputable def detectorComponent :
  ℕ → ℕ → ModuleCat.{0, 0} (ZMod 2) := <迁移构造体>
```

原声明（完整 kernel 类型）：

```lean
@[expose] public noncomputable def detectorV2Sixteen :
  ↑(KIP126.Computation.Standard.detectorComponent 16 112) := by sorry
```

候选签名：

```lean
@[no_expose] public noncomputable def detectorV2Sixteen :
  ↑(KIP126.Computation.Standard.detectorComponent 16 112) := <迁移构造体>
```

原声明（完整 kernel 类型）：

```lean
@[expose] public noncomputable def generators :
  KIP126.Computation.GeneratorCatalogue := by sorry
```

候选签名：

```lean
@[no_expose] public noncomputable def generators :
  KIP126.Computation.GeneratorCatalogue := <迁移构造体>
```

原声明（完整 kernel 类型）：

```lean
@[expose] public noncomputable def sourceAtom :
  (a : KIP126.Computation.Atom) → ↑(KIP126.Computation.Standard.sourceComponent a.degree.1 a.degree.2) := by sorry
```

候选签名：

```lean
@[no_expose] public noncomputable def sourceAtom :
  (a : KIP126.Computation.Atom) → ↑(KIP126.Computation.Standard.sourceComponent a.degree.1 a.degree.2) := <迁移构造体>
```

原声明（完整 kernel 类型）：

```lean
@[expose] public noncomputable def sourceComponent :
  ℕ → ℕ → ModuleCat.{0, 0} (ZMod 2) := by sorry
```

候选签名：

```lean
@[no_expose] public noncomputable def sourceComponent :
  ℕ → ℕ → ModuleCat.{0, 0} (ZMod 2) := <迁移构造体>
```

原声明（完整 kernel 类型）：

```lean
@[expose] public noncomputable def sourceGenerator :
  (i : Fin KIP126.Computation.Standard.archive.generators.count) →
  ↑(KIP126.Computation.ProgramData.component.{0} KIP126.Computation.Standard.sourceData
      (KIP126.Computation.Standard.archive.generators.degree i).1
      (KIP126.Computation.Standard.archive.generators.degree i).2) := by sorry
```

候选签名：

```lean
@[no_expose] public noncomputable def sourceGenerator :
  (i : Fin KIP126.Computation.Standard.archive.generators.count) →
  ↑(KIP126.Computation.ProgramData.component.{0} KIP126.Computation.Standard.sourceData
      (KIP126.Computation.Standard.archive.generators.degree i).1
      (KIP126.Computation.Standard.archive.generators.degree i).2) := <迁移构造体>
```

原声明（完整 kernel 类型）：

```lean
@[expose] public noncomputable def sourceProduct :
  (s t s' t' : ℕ) →
  LinearMap.{0, 0, 0, 0} (RingHom.id.{0} (ZMod 2)) (↑(KIP126.Computation.Standard.sourceComponent s t))
    (LinearMap.{0, 0, 0, 0} (RingHom.id.{0} (ZMod 2)) ↑(KIP126.Computation.Standard.sourceComponent s' t')
      ↑(KIP126.Computation.Standard.sourceComponent (HAdd.hAdd.{0, 0, 0} s s') (HAdd.hAdd.{0, 0, 0} t t'))) := by sorry
```

候选签名：

```lean
@[no_expose] public noncomputable def sourceProduct :
  (s t s' t' : ℕ) →
  LinearMap.{0, 0, 0, 0} (RingHom.id.{0} (ZMod 2)) (↑(KIP126.Computation.Standard.sourceComponent s t))
    (LinearMap.{0, 0, 0, 0} (RingHom.id.{0} (ZMod 2)) ↑(KIP126.Computation.Standard.sourceComponent s' t')
      ↑(KIP126.Computation.Standard.sourceComponent (HAdd.hAdd.{0, 0, 0} s s') (HAdd.hAdd.{0, 0, 0} t t'))) := <迁移构造体>
```

原声明（完整 kernel 类型）：

```lean
@[expose] public noncomputable def sourceUnit :
  ↑(KIP126.Computation.Standard.sourceComponent 0 0) := by sorry
```

候选签名：

```lean
@[no_expose] public noncomputable def sourceUnit :
  ↑(KIP126.Computation.Standard.sourceComponent 0 0) := <迁移构造体>
```

对 12 项都没有增删数学前提、没有改变结论的命题强弱，且候选目标仍指定相同名下对象。但是公开定义的可展开行为变弱；dependent 类型及普通 import 消费者的 `rfl`、`decide`、`change`、计算归约可能因此受影响。不能把“同名同类型”提升成已证“所有公开语义保持”。

## 真实前提与对象核对

| 条件 | 核对结果 | 证据与局限 |
| --- | --- | --- |
| 工具链固定 v4.32.2 | 满足 | README、lean-toolchain、已安装对应源码及该版本二进制实验 |
| 公共名称、完整类型、宇宙 | 提议保持 | 12 项冻结类型见 interfaces.json，全部无宇宙参数；并非最终候选编译比对 |
| helpers 私有 | 满足候选组织 | Internal.GeneratorCatalogue、Internal.SphereQuotient 默认私有；Standard.DetectorCoordinates 默认私有 |
| 完整目录及有效范围 | 分开核查 | sourceCoordinates、comparison 明示 t≤261；源商额外令 t>261 的单项式为零。expose 争议不能改变范围 |
| 固定球面 E₂ 对应 | 仍未完成 | comparison、comparison_product、comparison_unit、comparison_h0…h6 等候选仍有 sorry；无权把坐标商定义当几何识别 |
| detector 固定对象 | 仍未完成 | detectorComparison、detector_v2_agrees、detector_beta_agrees 的真实比较仍待证；(16,112)及(19,114)坐标类不能直接充当 tmf 页类 |
| 标准原子分次 | 有专门责任 | atom_record、sourceAtom_agrees 处理目录标定，sourceAtom 用 eqToHom 运输；可见性方案不得移除运输 |
| 外部计算假设 | 未引入 | 本报告两份最小实验不导入任何项目数学结果，无 sorry/axiom/假设 |

## 独立证据与复现

我未参与候选发现或实现；独立阅读 protocol、AGENTS、README、冻结 API/契约、基线源、取样候选及 Lean 实现。所有写入仅在本 review_dir，未修改项目源码、接口锁或任何工作树记录，未运行 Lake。

Lean 源码证据（安装路径 `/root/.elan/toolchains/leanprover--lean4---v4.32.2/src/lean/`）：

- `Lean/Elab/MutualDef.lean` 1343–1391：expose section 决定 wouldBeExposed；no_expose 优先使定义体进入 withoutExporting；随后移除属性语法。故这不是无作用的文档属性。
- `Lean/Elab/BuiltinTerm.lean` 465–485：private_decl% 在导出上下文中 privately elaborates，创建私有辅助定义并返回常量；不能简单等同于 AST 内联。
- `Lean/Meta/Tactic/Delta.lean` 13–29：deltaExpand 可按名称谓词递归展开定义体，默认不展开 opaque/theorem。

最小实际实验：在本目录以该版本二进制直接调用，完全独立于项目 Lake 状态。

```sh
LEAN=/root/.elan/toolchains/leanprover--lean4---v4.32.2/bin/lean
$LEAN -o Inline.olean Inline.lean
LEAN_PATH=. $LEAN Consumer.lean
$LEAN -o PrivateDecl.olean PrivateDecl.lean
LEAN_PATH=. $LEAN PrivateConsumer.lean
```

受限执行环境第一次启动 Lean 返回 `error: failed to locate application`；随后使用获准的隔离只读运行环境成功启动，未更换工具链。Inline.lean 编译退出 0；Consumer.lean 退出 1，唯独预期的 `hidden = 37 := rfl` 失败，并明确提示 `hidden` 定义未 exposed；同文件 `visible = 37 := rfl` 与 dependent.val 的等式通过。PrivateDecl.lean 使用 private Alias 和 privateValue，而 exposed dependent 中用带公共 Fin visible 类型的 let result，编译退出 0；PrivateConsumer 的第一轮普通 import 类型消费编译退出 0并打印 `dependent : Fin visible`。第二轮增加 `visible = 37 := rfl`、`dependent.val = 0 := rfl` 后退出 1；前者明确提示 `visible._private_1` 未 exposed，后者同样无法归约。因此 typed private_decl% 能保持公开类型消费和原 expose 标记，但私有辅助常量的实际值不会在普通 import 下展开。最终 PrivateConsumer.lean 保留这两条预期失败作为证据。实验源码为权威最小复现；linter 对命题 def 的提示不影响结论。

证据等级为 Lean 实际隔离编译及源码核对；不依赖 sorryAx、项目待补责任、目标本身或不一致环境。本报告没有完整的实际 12 项修复编译证据，也没有数学反例。未从未找到反例推出任何数学正确性。

## 方案及精确差异

优先方案 A：保持原 expose，用私有上下文 elaboration，但在 private_decl% 内给最终 result 明确写完整公共返回类型：

```lean
-- 示例，未经实际 12 项验证，不是已应用补丁
public noncomputable def atomIndex (a : Atom) : Fin generators.count :=
  private_decl% (let result : Fin generators.count := Internal.Archive.atomIndex a; result)
```

关键是辅助定义的实际类型不能泄露 private generators 等可定义相等但不可公开解析的别名。所有依赖返回类型均逐项作同样核对；须检查 kernel expression 而非仅 pretty print。最小 private Alias 实验支持此机制，但不证明实际大数据和所有 dependent 转换已通过。public body 仍 expose，不过它可包含私有辅助常量；这种封装不自动承诺普通 import 能把新数据归约为 literal。基线也是未实现的 def，而非 public abbrev；应由公共消费与精确 type 验证确定所需接口。此方案不增加公开 helper、不改数学条件、不转交责任。独立测试确认它不提供普通 import 下透过私有辅助常量到 literal 的归约；这与 B 的展开能力不同。基线构造体本为 sorry，不能把基线未提供的数值计算行为误当已承诺行为，但仍须以项目契约确定要求。

备选方案 B：保留 expose，在私有 elaborator 中 elaborates 私有实现后，递归展开该实现的私有定义，把公开 body 变为只引用公开常量及 literal 的表达式。Inline.lean 的局部 elaborator 已实测这种机制。实际实现必须限制展开目标、审核未展开 private opaque/theorem、终止性、巨量 AST/内存与构建时间，并核验最终公开 body 无不允许的私有数据常量。源数据庞大，不能凭 toy 就承诺性能。另可由私有语法宏直接展开原始 literal 结构，或者在原公开定义中直接写 literal/let 结构；都会避免新公开 helper，但需谨慎处理数据重复和证明字段。以上均是报告内候选，不是实施授权或既成修复。

最后备选 C：仅对列明 12 项采用 no_expose。精确差异见上文；名称/类型/对象关联不变，普通 import 的定义体展开能力下降。需要本报告具体范围的人类批准后才可实施。增加 public helper、绕过冻结检查、引入额外公理或给下游增加结果包均不建议。

## 依赖审计与下游影响

取样候选中直接数据定义依赖本模块私有目录、商代数及 detector 构造。sourceAtom 还通过 atom_record 对齐分次；sourceGenerator 与 sourceData/archive 的 definitional equality 必须实际检查。有限数据构造没有自动证明 sourceCoordinates 的 spanning/independence，亦不证明 comparison；后者及 detectorComparison 的待补依赖必须继续登记。未发现可见性最小实验中的循环或未证数学依赖。对实际 12 项的最终 proof-body/transitive audit 仍由最终构建和 trust capture 完成，不能引用本报告作完整无 sorry 审计。

interfaces.json 保存基线已登记的精确 type_consumers：generators→atomIndex/atom_record/basisMonomial；basisCount→basisMonomial；sourceComponent→sourceAtom/sourceProduct/sourceUnit；sourceGenerator→sourceAtom_agrees/sourceBasis_values/coordinates_basis/comparison_symm_coordinates_basis；detectorComponent→detectorComparison/两指定类/两比较标定/detector_d3；detectorV2Sixteen与detectorBetaGFour→对应标定及detector_d3。这里 type_consumers 不穷尽 body 消费。

另独立源码搜索定位 Computation/Basis.lean、Table/Values.lean、Table/Relations.lean、Table/ThetaRelations.lean、Table/Internal/SourceExpression.lean 的 Standard 对象引用。Standard 内 archive、sourceData、coordinates、全部通过 comparison 使用这些构造的实际球面声明及 detector 族属于需回归检查范围。ProofTools/Main 可通过公开 Computation 名称继续调用类型级接口；未证明它们不使用展开，因此需保留现有公共消费和集成测试。

责任仍为 Computation；无上游责任转移。若 C 获批，应对 computation-api.json 所不覆盖的可见性契约、computation-contracts.json 的普通公共消费含义、computation-sources.json 的实现来源及 proof-obligations.json 的真实构造状态同步记录；不得以刷新锁掩盖未授权变化。A/B 不需要改接口锁，但同样要同步真实完成责任、来源和哈希。测试需覆盖普通 import、完整 dependent 类型、实际公开计算归约需求，并运行 ComputationChecks、ArchitectureChecks、Integration/Trust、check-source-inventory.py 与完整 lake build；由协调者唯一构建进程执行。本报告没有运行这些项目检查。

## 阻塞范围与继续项

受争议阻塞的是“以 no_expose 作为最终结果合并并宣称接口完全不变”及依赖这种合并的最终交付。此处不是可信数学反例，不应冻结整个 Computation 或把全部比较声明判假。

可立即继续：A 的逐项适配与普通公共消费验证；B 的实际规模可行性试验；私有目录和有限商证书的验证；与 expose 无关的维数、关系、存活、Cν、tmf 迁移研究；固定球面/ detector 比较的真正证明工作。采用 A/B 若实际成功可继续正常串行整合，无需为普通补构造再次请求人类授权。仍未完成的比较责任必须保留。

协调者后续告知实际 GeneratorCatalogue 的 generators/atomIndex typed private_decl% 前缀试验已通过；这是协调者提供的附加进展，不作为报告员独立实际项目验证。协调者拟恢复原 expose 并逐项验证 12 个声明，这属于保留接口内部方案的正常补构造；本报告无权把其尚未完成的验证记为成功。

## 人类审核记录

尚无。human_decision 为 null；协调者、其他 agent 的意见、继续实验或等待均不构成批准。


## 后续独立复核：typed 封装实际项目与完整内联

协调者于后续任务给定 Standard SHA-256 `4a6dead54a61be3ed215e0a2606ff0746701daacde792f63be652ab660e3eeae`。报告员实际读取该文件并独立计算得到同值；当时未保存完整快照，后续协调者继续修改源码；本目录 `candidate-typed-Standard.lean.txt` 保存稍后实际取样版本，SHA 及研究补丁基线见 inline-patch-baseline.txt。12 个目标均已移除 no_expose，保持原 expose section，并用 typed `private_decl% (let result : 完整公共返回类型 := 实现; result)` 封装。报告员独立读取 standard-build-3.log，文件内 Standard 错误仅位于 316、345、365 三处零关系/actual-page 转换，无 12 项数据声明错误；该次整体 Standard 构建仍失败，不能记录为整个模块通过。原日志副本见 standard-build-3.log.txt。由此，原“必须用 no_expose 才能编译这些数据”的理由已被实际类型检查否定，保留接口的内部路线已取得真实项目进展。报告继续 pending-human-review，不意味着要求先人审才能继续不变接口补构造。

额外的独立最小实现 PrivateElab.lean 使用 **私有 import Lean、本地 syntax、local term_elab 属性及 private meta def**，不新增 public helper，也不增加 public import。该文件及 PrivateElabConsumer.lean 均实测编译退出 0；普通 import 后 visible=37 与 dependent.val=0 的 rfl 均成功。非 local 的 term_elab 属性要求 elaborator 为 public（已经实际失败），故 local 属性是必要细节。InlineNoHelper.lean 另验证 run_tac 可以达到同样 literal 展开，但需 public meta import；为避免扩展导出，不建议使用该版本。它们只是隔离证据，不是项目已应用代码。

研究补丁 inline-candidate.patch 对 inline-patch-baseline.txt 中实际记录的后续取样 SHA 增加私有 metaprogram 支持，并将恰好 12 处 private_decl% 替换为 inline_private%，保留 typed result 和所有声明/属性。补丁只在本报告目录展示，未应用源码；新增源码为数百字节量级，补丁文件几 KB，准确字节数以文件为准。Lean 源码依赖及 source-inventory 是否允许额外 import Lean 仍须协调者核验，不能因是 metaprogram 就跳过架构检查。

**必要性评估：目前没有足够理由实施完整内联。** 基线 12 个构造体原为 sorry，不提供数据 literal 归约；冻结类型及已读契约要求固定对象、完整数据、普通调用和真实比较，没有发现明确要求将所有数据经普通 import 化为 literal 的单独条款。typed 封装保留原 expose 标记与公开类型消费。完整内联可提供更强计算展开，但没有证明它是当前责任的必要条件，也没有证明 typed 封装违反原接口。若特定公开消费者确实必须归约目录计数/单项式，应先给出该消费者及必要归约范围，再只内联所需族，而非为属性形式一致而展开整份档案。

**体积与性能评估：** 实际私有 GeneratorCatalogue.lean 为 2,219,722 字节，SphereQuotient.lean 为 7,777,872 字节，两者合计 9,997,594 字节；typed Standard 为 36,630 字节。公开 sourceComponent/sourceProduct/sourceUnit/sourceAtom/sourceGenerator 的内部展开可能在类型与值中反复插入同一 relation 数据、同构实例及分次子模；basisCount/basisMonomial 会重复展开基目录。公开 generators 的引用可以保留共享，但私有 Internal.generators 或局部 component 的引用也可能触发重复目录。**不能把新增源码数百字节理解为新增 olean/AST 数百字节，也不能把 10MB 文本线性等同实际 AST 字节。** 未运行实际全量内联，尚无内存、olean、耗时或 AST 节点数的测量。私有 theorem/opaque 默认不会被 deltaExpand 展开，返回表达式仍可能包含此类常量；证明字段及其私有类型必须再次审计。若要求无任何 private 常量的完全 AST，则本补丁不满足该更强要求，需要逐项处理这些项，不能擅自 allowOpaque 展开所有证明。

建议继续 typed 封装完成当前迁移，保留完整内联为有实际消费者需求时的定向优化/内部实现备选；本报告不扩大写入或发布权限。


## 后续独立复核：18 个额外公共导出（修正前述封装结论）

**这一节修正前文“typed private_decl% helpers 私有”的不充分判断：body 私有不等于名称真私有，也不等于导出集合保持。** 12 项 typed 封装虽通过完整目标类型检查且保留 expose，却为每项生成可公开引用的 `<公开声明>._private_1` 名称。因此该版本不能宣称完全符合冻结的公共导出接口。此前 toy 只检查类型消费和 literal 归约，未检查名称导出，这是已明确补齐的证据范围。

报告员未参与本疑点发现或实现；直接重新解析冻结 computation-api.json 与 `.lake/computation-standard-capture.json` 并做集合比较，结果见 independent-export-audit.json。capture SHA-256 为 `b63283d58655282dd2fd8a52e5a4c883658766cdff127c8546ca3d88bac2611e`，API SHA-256 为 `3f9348f006570a1836ec733ba075ca043cdfd156a6042a4b8bb021eda27612fe`。183 个已捕获目标的 type_fingerprint 与 universe 列表均匹配；从导入环境捕获的全部 Computation exports 相对冻结的整个 Computation exports 多出恰好 18 名：

- `KIP126.Computation.Standard.X.eq_1`
- `KIP126.Computation.Standard.atom.eq_1`
- `KIP126.Computation.Standard.atomIndex._private_1`
- `KIP126.Computation.Standard.basisCount._private_1`
- `KIP126.Computation.Standard.basisMonomial._private_1`
- `KIP126.Computation.Standard.comparison.congr_simp`
- `KIP126.Computation.Standard.correction.eq_1`
- `KIP126.Computation.Standard.detectorBetaGFour._private_1`
- `KIP126.Computation.Standard.detectorComponent._private_1`
- `KIP126.Computation.Standard.detectorV2Sixteen._private_1`
- `KIP126.Computation.Standard.generators._private_1`
- `KIP126.Computation.Standard.h5Square.eq_1`
- `KIP126.Computation.Standard.product.eq_1`
- `KIP126.Computation.Standard.sourceAtom._private_1`
- `KIP126.Computation.Standard.sourceComponent._private_1`
- `KIP126.Computation.Standard.sourceGenerator._private_1`
- `KIP126.Computation.Standard.sourceProduct._private_1`
- `KIP126.Computation.Standard.sourceUnit._private_1`

Standard 归属导出与历史 Standard 归属比较会显示 19 项，因为另有 coordinates.congr_simp；但该名称已存在于冻结的全 Computation exports，因此本次真正超出全锁的是 18 项。不能混淆这两种集合边界，也不能用部分 Standard 导入 capture 声称检查了整个 Computation 的所有缺失名称；其尚未导入的其他文件声明不在本次完整性证据范围。

### 两类成因与证据等级

1. **12 个 `._private_1` 名称：独立形式复现确认普通导入可见。** Lean/Elab/BuiltinTerm.lean 的 private_decl% 先 `mkAuxDeclName _private`，再 `withoutExporting` 调 mkAuxDefinitionFor。Lean/CoreM.lean 149 附近的 mkAuxDeclName 仅用名称生成器给出唯一名；Lean/Meta/Closure.lean 447 附近的 mkAuxDefinitionFor 只推断类型并按所给 name 建定义。它们不会把名称自动变成真正 `_private.<module>.0.…`。Lean/PrivateName.lean 32 的 isPrivateName 只认 `_private` 前缀，字符串后缀 `_private_1` 不满足。独立 AuxVisibility.lean 普通 import 前述 PrivateDecl 后，`#check visible._private_1` 打印 Nat、`#check dependent._private_1` 打印 Fin visible，`#eval Lean.isPrivateName` 返回 false；该文件实际退出 0。因此不是仅仅捕获脚本宽松识别造成的假阳性，而是普通消费者能新增引用这些名称。

2. **5 个 `.eq_1` 和 comparison.congr_simp：源码机制与实际 capture 证据。** Lean/Meta/Tactic/Simp/SimpTheorems.lean 的 mkSimpEntryOfDeclToUnfold 会查询 getEqnsFor?；Lean/Elab/PreDefinition/Eqns.lean 的 getEqnsFor?/mkEqns 通过 realizeConst 和 addDecl 生成公开父定义名下方程。Lean/Meta/CongrTheorems.lean 对 congr_simp 注册 reserved-name action，按公开父名生成并 realize congruence theorem。取样 Standard 在 325、354、374 等新证明中使用 `simpa [atom, h5Square/X/correction, product,…]`，与实际多出的方程名对应。这说明一般生成路径和候选触发位置；没有单独以删除某一行后重编实现一一因果隔离。额外 EqnsVisibility.lean 的极简 simp toy 未观察到 eq_1（before/after 都 false），因此本报告不把该 toy 当方程生成的形式复现。已确认的是实际 capture 中这些额外名称以及 Lean 的生成机制，具体最小触发过程仍由后续定向项目验证解决。

这两类均为封装/导出实现问题，不是数学反例或遗漏几何前提；不改变原 183 个目标类型不等于已保持导出冻结。方程/同余定理虽然逻辑上只是已有定义的后果，仍属于新增公共名称，不能因其“自动生成”自行改锁接纳。

### 保持接口的内部修复方向（未由报告员实施）

优先修复 12 个辅助名：本地 term elaborator 在私有 elaboration 上下文生成辅助名后，使用 `mkPrivateName` 将其转换为真正 private 名称，再以该名称调用 mkAuxDefinitionFor；继续保留完整公共返回类型的 typed let result，避免再次泄露私有别名。保留非计算性标记、级别参数、闭包捕获和类型适配；生成真正 private helper 后复核普通 import 不能 #check 用户原始别名，捕获 exports 不含该名，183 项类型/宇宙仍匹配，并审计无新 sorry/公理/责任。此路线是内部实现修复，无需接口调整授权；尚未被本报告员在实际 12 项上验证成功。不能仅使捕获脚本忽略 `_private_1` 后缀来修复，它已经被实测可公开引用。

方程/同余名方面，避免新证明请求公开定义的懒生成方程，改为定向 delta、显式等式、exact 或已有已锁定定理；务必实测每种 tactic 是否仍触发生成。单纯从 simp 改成 rw 不能一般保证无额外导出，因为 rw 同样可能解析公开方程名或请求 equation theorem。使用局部 simp 配置禁用 congrConsts 仅是候选方向，不能未经确认大范围改变全局选项。保留既有已锁定的 coordinates.congr_simp，不删除已有覆盖、不新增 public 桥接引理。候选证明的数学内容、上游 comparison 待补和本模块责任都不应转移。

如果两条内部路线成功，原接口、属性及全导出集合均能保持，不存在必须请求人类扩展公共接口的已证理由。若协调者最终希望接纳这 18 名为新增导出，则必须另形成精确方案并由人类批准；本报告不批准，也不预设将其纳入允许范围。原 12 项 no_expose 的人审备选不包含这 18 项新增导出，更不能授权改锁。

### 下游、阻塞与继续项

暂停把带 18 个新增导出的 Standard artifact 用作最终合格依赖，并重新捕获修复后的 Standard；依赖该 artifact 的 Dimensions 重编可由协调者按实际状态暂停。既有私有数据、有限关系证明与其他不依赖该导出候选的研究可继续。普通消费者应检验：原 183 项名/完整类型/宇宙可用；辅助名不新增公开入口；全 Computation 普通根导入的 exports 与锁严格匹配。最终仍须进行本模块及 Architecture/Integration/Trust 与完整 lake build，不能以此部分 capture 代替。

本轮仅追加报告及同目录证据，未实现修复、未改源码或锁、未运行 Lake，也未代协调者重启 Dimensions 构建。状态继续 pending-human-review，human_decision=null。


## 后续独立复核：真正私有辅助名与 backward.privateInPublic

这一节再次收紧前文“mkPrivateName + typed result 即可修复”的可行性表述：它只是研究方向，不能记为已可用修复。协调者新提供的 geometry-worker toy 显示，真正 private 辅助声明在默认规则下不会导出，public exposed body 因而无法引用它。报告员独立读 Lean 实现，确认这并非仅普通消费者 literal 计算的问题。

Lean/AddDecl.lean 136–143 在声明的所有 top-level 名称均满足 isPrivateName 时作如下选择：默认 `backward.privateInPublic=false`，令 exportedInfo?=none，不导出该私有声明；若该兼容选项为 true，则 exportedInfo?=some info，导出完整 ConstantInfo。Lean/ResolveName.lean 105–110 的选项默认值为 false，描述为“Export private declarations, allowing for arbitrary access … while code is being ported to the module system”。名字解析亦因该选项放行 exporting 上下文对私有名的访问。故该选项实质改变私有导出/名称解析边界，不是辅助名拼写控制，也不是仅消除无害警告。

报告员在本 review_dir 独立复现：FlagToy.lean 的本地 elaborator 用真正 mkPrivateName，并仅在 mkAuxDefinitionFor 时 `Lean.withOptions (…privateInPublic.set · true)`。保留 public count_eq : count=2 := rfl 的第一轮仍失败，Lean 指出公开证明所需归约的定义必须 exposed；同内容保存在 FlagPublicProof.lean。随后把该证明改成 private（最终 FlagToy.lean）后编译退出 0。普通 import 的 FlagConsumer.lean 枚举 `env.setExporting true`，实际看到两个 `_private.FlagToy.0.TruePrivateToy.…._implementation_1` 辅助常量且 isPrivateName=true；公开 count/entry 的类型消费可用，但 `count=2 := rfl` 仍失败（最终 consumer 退出 1，唯一错误为此预期失败）。不能把这个 toy 的失败归咎于额外 noncomputable 示例：最终已将那个示例标为 noncomputable，诊断只剩该 rfl。

证据说明：局部开启选项确实把真正私有 helper 的完整信息加入 ordinary-import 可见的导出环境；helper 所依赖的既有私有 catalogue 却未自动获得相同导出处理，因此仍不保证完整展开。若 export 审计仅过滤 isPrivateName，此时可能恰好看不到新增“公共名称”，但这不足以证明原私有边界保持。这里没有证明 Lean 内核可靠性失效，也没有发现新增数学公理；被放宽的是 module 系统的私有导出和访问边界。不能将“不增加逻辑公理”解释为符合用户冻结要求。

**当前判断：不建议、也未授权在生产实现中启用 backward.privateInPublic。** 用户明确禁止“放宽检查掩盖缺口”，而这项兼容开关的官方本地定义及实际环境证据都显示它允许原默认禁止的私有导出/访问；用它让暴露定义引用 private helper 恰好触及这条限制。报告员不会自行批准例外。是否存在用户愿意明确批准的更窄边界方案须另给具体范围，本报告 human_decision 仍为空。

无须这项开关的备选仍为已实测 `local inline_private%`：私有 import Lean、local syntax、@[local term_elab …] private meta def，在 withoutExporting 中 elaborates 原私有实现，再 deltaExpand 私有定义成公开 body 表达式。报告员已将 PrivateElab.lean/PrivateElabConsumer.lean 与研究补丁位置发送 geometry_worker，建议对完整 Standard 作实际验证。若需控制体积，可研究在同一公开 body 内用 let-bound DAG 共享重复数据/类型及表达式，而非新增公共 helper 或开启私有导出兼容开关；此 let-DAG 优化未实现/未验证，尤其 dependent let 的类型关联和私有 theorem/opaque 残留仍须逐项审计。

协调者亦告知另一 worker 已找到避免新方程导出的实际证明改写；报告员未参与实现，也未将该转述作为自己完整构建证据。仍需最终普通 root import 的全导出集合、类型/宇宙及 proof-body 审计。

本轮只写同目录报告与隔离 toy 证据；无生产源码/接口锁/选项变更，无 Lake 调用。仅本问题的导出合格交付受阻，其他不相关迁移及无开关的内部方案可继续。status=pending-human-review，human_decision=null。


## 最新技术进展：正常内核检查的 local command 直接定义路线

本节记录一条新的 **保留接口的内部实现路线**，不删除或批准前文 no_expose 备选，也不改变本报告 pending-human-review/human_decision=null。报告员未参与该路线实现或发现；本轮独立阅读实际候选、audit tail、Count/Component 源与日志、auditor/direct-definition/review.md、counterexample/direct-definition/report.md 和真实错误输入日志，并对照锁定 Lean 源码。独立读取文件的绝对路径、SHA-256 和取样字节数见 direct-definition-evidence-manifest.json；完整候选取样保存为 direct-definition-candidate.snapshot.lean.txt，关键日志副本保存在本目录。没有重复运行昂贵内联、运行 Lake 或修改生产源码。

### 实际实现和信任边界

候选使用本地 command `inline_definition% public noncomputable def <原目标> : <原完整类型> := <原私有实现>`，实现声明为 private meta，属性为 local command_elab。它按当前 namespace 与原 identifier 组成原公共名字，不添加公开数学 helper。

实际流程为：使用 elabType elaborates 指定公共类型并完成 synthesis；在私有上下文独立 elaborates 原私有 value；对 private 常量的 **实际已存储定义体和证明体** 做 δ 展开（allowOpaque=true）；拒绝 type/value 中仍残留 private 名称或直接 sorry term；将值包装为 `mkExpectedTypeHint value type`；先 `Meta.checkWithKernel`，再显式要求 debug.skipKernelTC=false，调用正常 `Lean.addDecl (.defnDecl {safety:=.safe,…}) (forceExpose:=true)`；最后标记原本的 noncomputable 状态。

独立核对 Lean/Meta/AppBuilder.lean：mkExpectedTypeHintCore 只是构造 `@id expectedType value`，它不提供 cast 或放过类型不符。Lean/Meta/Check.lean 377 附近的 checkWithKernel 会实例化 metavariable 后直接调用 Kernel.check；正常 AddDecl 仍进行声明级检查。forceExpose 控制导出时保留已检查定义体，而不是跳过内核。safe 声明仍拒绝 unsafe 依赖。这里不使用 backward.privateInPublic、no_expose 或 skipKernelTC，也未调用 unchecked/addDeclWithoutChecking。展开既有 checked theorem 的实际 proof term 是替换证明体，不是重新假设其结论；但必须保留实际证明依赖审计，不能从 allowOpaque 本身推出无 sorry 或无循环。

本命令 levelParams=[] 只覆盖本任务 12 个冻结宇宙列表为空的单态目标；不是一个已证明适用于任意宇宙的框架。regular 0 是内部归约优先级提示，不改变数学类型和值。候选还保留原生成支持 sourceProduct._proof_1 的精确声明；这不是允许随意添加新支持名，最终仍按全锁捕获。

### 已观察到的实际正向结果

- **Count 三目标（真实项目数据）：** check-direct.log 实际显示 generators、basisCount、basisMonomial exposed=true，三者 collectAxioms 均为空，Standard 公开名恰为这三项。它们值仍引用同一 Internal.Archive 原实现并展开，没有另造满足表的模型。
- **所有 s,t 的计数对象相同：** Count-direct-equality.lean 直接构造 `∀ s t, originalArchiveCount s t = newPublicCount s t`，证明体为以原 lhs 构成的 lambda/Eq.refl；通过正常 addDecl 的真实 kernel 检查。check-direct-equality-final.log 显示 COUNT_EQUALITY_KERNEL、axioms=[]。这是无限自然数范围的定义相同证据，不是有限点穷举，也不是只凭 Meta.isDefEq 的返回值；它不证明 archive 基线性无关或真实球面 comparison。
- **Component 四目标（真实项目商）：** Component.direct-check.log 显示 generators/sourceComponent/sourceProduct/sourceUnit 的精确公开集合，并显示本地 elaborator 的依赖仅 propext、Classical.choice、Quot.sound。实际 candidate 按同一 Internal.SphereCoordinates 商及齐次分量/乘法/单位展开；无新几何模型选择。counterexample 报告核对这四项内核、暴露体及私有残留检查通过。报告员独立读取实际源和日志，但没有重跑它们；应将报告审读与本轮亲自执行区分。
- **隔离正向玩具：** positive.log 显示 count/entry 精确导出，count 无公理，entry 仅基础 propext/Quot.sound。这只覆盖有限数组与 dependent Fin 例子，不覆盖全部 12 项巨大数据或实际 Adams 对象。

### 真正内核拒绝的负例

本轮独立阅读了负例源/实际日志，并与命令代码一致性核对。DirectWrongType 试图把 Bool 的 true 放入 Nat，wrong-type.log 明确由 kernel 在 `id true` 处以 argument type Bool / expected Nat 拒绝。DirectUnsafe 使用真正公开 unsafe 输入，unsafe.log 明确由 kernel 报 `invalid declaration, it uses unsafe declaration 'DirectPublicUnsafe'`。目标后续 unknown 是被拒绝的后果，不能把失败结果当已安装声明。这两项证明所测 command 路径没有凭 expected-type hint 或 safety 字段越过真实 kernel，并不构成整个 project trust audit 的替代品。

### 完整 Standard 当前仍未验收

取样时 Standard.direct-kernel-audit.log 为 **0 字节**，direct-audit-result.json 尚不存在。完整 Standard.direct-kernel-candidate.lean 正在验证；报告员不从已通过的 Count3/Component4 推出全部 12 项、全部 183 目标或最终普通消费者已通过。

实际 audit tail 计划逐项比对 183 个冻结完整类型指纹及宇宙；检查 12 个 data body exposed、无 sorry、无 private 常量并仅有基础逻辑公理；比较当前本地公共名与全 Computation exports；核验两个 elaborator 真私有及其 trust。该 tail 设计有意义，但日志未完成时只能记为 **待运行结果**。定义模块内环境审计也仍不能代替编译后普通 root import 消费、Integration/Trust 和完整 lake build。

另取样完整候选把六个 Mathlib `import` 写成了 `public import`。183 项 Computation 类型和 Computation 名称导出集合并不单独覆盖第三方 import/reexport 边界；协调者应核对这是否仅是使公开体依赖可见所需的原外部公共闭包，或需要恢复既有 import 形式。这里不预先宣布其为接口违例，也不把它默认为已获授权的额外公共依赖调整。

### sourceAtom_agrees 的元层算法与内核证据

候选把原 Meta.rfl/自动 defeq 路线换成 `kernel_checked% (Eq.refl (sourceData.atom a))`。该 local term elaborator 要求 skipKernelTC=false、拒直接 sorry，以 `@id expectedType term` 约束真实目标并调用 Kernel.check。只有 kernel 接受 RHS 的 Eq.refl 是原完整目标类型时才构成证明；不是用反射算法的成功/失败直接替换数学推理。Meta.rfl 慢或 Meta 算法未能发现定义相同，不能据此判定对象不同、产生数学反例或要求改接口。完整候选目前仍在运行，故本报告未认领 sourceAtom_agrees 的最终 kernel 成功。

### 人审与继续范围

若上述内部路线在真实完整候选和普通消费者上验证通过，且确实保持原完整名、类型、前提、对象、标准类、宇宙、expose 及公共导出集合，则实施属于已授权的 Computation 内部补构造/补证明，**无需为了采用正常内核检查的实现方式另求人审改变接口**。agent 的技术审查不替代最终验证，也不授予任何接口调整权限。

原 no_expose 方案仍仅为未批准备选，前文 18 名额外导出和 privateInPublic 放宽边界不能被当作这条路线的允许副作用。仍需保留 sourceCoordinates 的真正基证书、comparison/product/unit/标准类标定、detectorComparison 等实际对象待补；有限坐标定义通过不等于当前固定 Adams 对象计算已完成。

可继续完整 12 项及普通公共消费/全锁导出验证和无争议的独立迁移；本问题最终封装验收尚未完成，不能继续使用旧 18 导出版本作为接口合格成果。未经明确批准不改 API 锁、不新增公理或责任。status=pending-human-review，human_decision=null。


## 最终 root / 841 项公共接口阶段验收（完整 trust / full build 尚待）

报告员本轮独立实际计算的最终源 SHA-256：

| 文件 | SHA-256 |
| --- | --- |
| Standard.lean | f56a0b03e79db1d49904e58577e47849e7e17ad4cb0957ac217570131cff660d |
| Table/Values.lean | 133064fbcf98096bcd4183f02aaf81d0d231b9e9d9568708f07462d78292bf66 |
| Table/Internal/SourceExpression.lean | 97b47598e8a478041e712f2b03b95e04d46f430507e74411caec5b5df285e0fe |

上述三值均与 `public-pass-before-capture-optimization/capture-inputs-before.json` 的原 capture 输入吻合。报告员独立读正式 computation-export-fixed-root-build.log 和 computation-final-root-build.log，两者均结束于 Built KIP126.Computation / Build completed successfully (2760 jobs)。日志副本保存本报告目录。这里是 **Computation 模块根构建**，不是默认完整 lake build/Trust/六模块全部验收。

报告员不只转述通过布尔值：重新解析冻结 computation-api.json 的 declarations+generated_declarations 与保存的 ordinary public root capture；841 个精确名称均匹配，841 个完整 type_fingerprint 及 universes 均匹配，exports 也是 841 对 841 且 added/missing 均为空。独立重算见 independent-final-root-841-audit.json；原捕获副本 final-public-841-capture.json 的 SHA-256 为 c9f4e79a78e36e73ad655ddb24b2f11df5fd0b3c89c2a3f5a3e99825a753c5eb。final-public-841-result.json 记录实际 Lean capture exit_code=0、inputs_unchanged=true；scope 原文明确 trust capture incomplete，故本报告没有把公开 capture 成功冒充传递信任审计完成。

### 与原问题相关的结果

保留 expose 的本地私有 direct-definition elaborator 及正常 safe addDecl / 内核检查已用于实际正式根构建；12 个直接构造无需 no_expose 或 privateInPublic。最终源不包含这两个兼容路径；同一 frozen 841 公共接口的名称、完整类型、宇宙和 exports 已有正式 root 证据。普通消费者不再依赖前述新增 `._private_1` 名称，也没有通过更新接口锁接纳额外出口。

原源码声明计数 123→124 并不等于增加接口：新增显式源命令恰是 **原已冻结 generated 声明** sourceProduct._proof_1，指纹 11175341723205241885、空宇宙，仍在同一个841集合。报告员独立查原API确认该条目原本已存在；auditor 已用未改 source commands scanner 对原git基线核对。不能把它误写为“原源码命令数未变”，也不能因生成支持如今显式写出就盲刷 API 的 named/generated 历史分类。

两轮后续额外 lazy exports 均保留失败 capture，而非悄然删除证据。报告员重新对它们的 exports 与同一全锁比较，结果见 independent-two-failed-export-rounds.json；这些 capture 自身进程 exit0 仅说明成功产出 JSON，不说明接口集合合格。最终 Values 使用 private 显式原定义等式与定向运输避免生成额外公开方程，完整 root/841 再验收通过。失败轮来源位于本 session 独占 run 子目录，报告没有改写全局记录。

### 已确认与仍未确认

现在不能再以“项目适配尚未验证”描述本内部路线：**实际 Computation root + 普通公共根导入841精确接口这一范围已经验证。** 这同时解决了本议题早期封装导致的公共名泄漏验收，不要求人类批准原 no_expose 方案。它不等于人类批准任何接口变化；因为本阶段结果保持原接口，采用内部补构造属于原有授权。

完整 body/trust 捕获（含全部私有 metaprogram 和传递待补）、默认完整 lake build、Architecture/Integration/Trust 等后续验收仍未在本次材料中完成，需等待协调者真实新证据。比较到 actual sphere、sourceCoordinates 与 detector 标定等数学待补继续如实保留，不能凭841接口相同或根构建成功宣称全部计算责任已证明。

前文 no_expose 备选、privateInPublic 风险、18新增导出及失败toy均保留作历史原因与替代方案证据；这些未获人类批准方案没有被本报告批准、也无需实施。原初状态仍 pending-human-review，human_decision=null。只写本 issue 目录，没有修改共享主源码、接口锁或全局索引。


## 收尾前实际捕获复核（full build 尚在运行）

本轮报告员独立读取 capture-provenance.json、final-captures 两份实际 JSON 及其 Lean 输入、执行结果、verified-completions.json 与原88项 task-interface-snapshot。未复跑 Lake、未写其他成员记录。复算结果保存 independent-final-capture-audit.json。

实际 trust/body capture 共 **12091 个声明**，public capture 共 **841 个声明及841精确公共导出**。最终归档四文件和 capture execution 两份结果的 SHA-256 均与 provenance 匹配；public 全名称、完整类型指纹、宇宙列表及导出集合与原冻结 API 再次全部相同。两个本地 Standard elaborator 及 Values kernel_checked elaborator 在 actual capture 中都是真私有名称，direct_sorry=false，依赖仅基础 propext/Classical.choice/Quot.sound。原12个数据构造的 actual 依赖同样没有 sorryAx：目录四项无公理，商/坐标构造仅基础逻辑三项。因此，先前“完整数据封装 actual trust 尚未捕获”的阶段状态已有真实新证据；这不等于 Tests.Trust 或整个项目无待补。

verified-completions 的 **32项直接责任消除、56项直接责任保留** 与原88项目标精确分割（无交叠、无丢失）；32项中记录的 actual row 均与 final actual capture 逐字一致，均无 direct_sorry 或 synthetic_sorry。报告员没有仅凭32这个数字确认全部最终数学依赖已闭合：其中若干关系、基值、平方结论仍经原 comparison/sourceCoordinates 等含 sorryAx 的传递待补。带传递 sorryAx 的已消除直接责任名单已独立写入 evidence JSON，不能把“直接责任已消除”称为“无项目未证依赖”。12项数据构造的本次封装问题与这批仍登记的真实对象比较责任必须分开报告。

当前 no_expose 提案仍未获批准且没有实施；privateInPublic 也未成为生产路线。保留原完整 public841 的安全内核内部实现已有根构建、完整 public capture 及实际 body/dependency capture 支撑，故没有要求人类批准取消 expose 的现实技术必要性。原方案、失败证据及讨论继续保留，不能把技术替代路线的成功伪装成人类对旧方案的批准。

**正式完整 full build 此时仍在运行。** 本报告不提前宣布 Tests.Trust、Architecture/Integration 全部或默认 lake build 已通过；待协调者提供后续实际完成结果，再独立绑定最终源码/输入与日志补齐这部分。status=pending-human-review，human_decision=null；没有新增公共接口调整，也没有扩大实施或发布权限。


## 当前真实阶段：完整构建失败与 basisCount 的 elaborator 归约属性

本轮报告员独立读取 full-build-attempt-01 的源快照、正式完整日志及结果，当前 Standard、性能修复差异、local consumer 实验源/结果、auditor/basis-count-reducibility-review.md、Tests.Computation.Interface 和锁定 Lean 机制源码。未运行 Lean/Lake、未改生产或任何其他记录。独立摘要见 independent-reducibility-stage-audit.json。

### 首轮完整构建确实失败

full-build-attempt-01/full-build-result.json 实际 exit_code=1，inputs_unchanged=true，resource_stops=[]。完整日志的数学源码错误仅 Main/Internal/Theta/ZeroDegree 的200000 heartbeats 与 Main/Internal/NuNinth/Frames 的1600000 heartbeats 用尽，均为 deterministic timeout at whnf/tactic execution；最终 build failed。因此不能将根Computation通过或public/trust capture完成写成首次全量通过。该轮日志同时实际显示 **Computation trust audit: 5642 declarations; 56 individually registered pending proofs/constructions; no project axioms**，这项内部审计通过也不能消除整个构建失败。

先前的 native ReducibilityHints height 候选虽经正常 kernel 检查，但未解决原两consumer proof的超时，未整合。失败源码、日志和绑定旧f56的captures均保存在 full-build-attempt-01，继续作为历史证据。

### 新改动的精确性质

报告员实际计算当前 Standard SHA-256 为 `20aef9056c2650ba7e645ba8119d6f665651cabe97327a65b68bc8c98342e726`。与full-build-attempt-01中f56 Standard逐字diff仅新增注释与同文件正常 `attribute [irreducible] basisCount`，原目标名/完整类型、数据定义体、safe状态、forceExpose和所有证明文本未替换。没有改Main源码/预算或测试名单。

独立核对 Lean/ReducibilityAttrs.lean 16–32：普通def的semireducible在TransparencyMode.default可展开；irreducible仅在all展开。Lean/Meta/GetUnfoldableConst.lean 的 canUnfoldDefault 对default检查isIrreducible，对all允许。Lean/Declaration.lean明确这种attribute控制elaborator的simp/rfl/dsimp展开，**不影响kernel**，与constant ReducibilityHints不同。正常 ReducibilityAttrs.validate 会检查本文件定义、合法原状态与attribute作用域；当前使用attribute，未启用allowUnsafeReducibility或绕过validate的底层setter。

因此此次改变不能写成“所有可观察行为保持”：默认 Meta.isDefEq/whnf 的自动展开策略确实改变，可能影响某些自动化/rfl消费者；应在交付中如实披露。它不把定义改为opaque、不取消expose，不改变checked value或kernel定义相等；显式delta和all透明仍能展开原同一有限目录。它也不属于此前privateInPublic的私有导出放行或no_expose的body隐藏。

### 冻结边界与证据限度

独立读取Tests.Computation.Interface，其实际锁定完整kernel类型、宇宙、精确公共导出、传递公理依赖；没有锁定basisCount的默认reducibility状态。AGENTS仍冻结数学语义/对象关联/标准类和职责，不能只凭脚本没检查就放行实质对象修改；但这次仅正常同文件elaborator策略，原同数据定义未动。按当前证据，此为保留数学接口的内部性能策略，**没有证据表明它必须取得no_expose式的接口调整授权**；这不是报告员批准任何接口变更，也不能解除必须验证原全部消费者和检查的要求。若后续需修改Main证明、预算、完整类型/对象/导出，则必须按真实新增差异重新判断，不得继续泛称性能属性。

### 性能诊断与当前未决

报告员独立比对 local basisCount probes 与 original Main proof副本，仅增加local irreducible属性（准确diff保存在证据JSON），完整proof与原heartbeat预算保持。baseline8-results.jsonl 实际报告 ZeroDegree.basisCount exit0 /1.62s、Frames.basisCount exit0 /2.88s。这是具体consumer诊断证据，不是生产同文件global属性传播后的全量验收。irreducible-evidence另保存type_hash和value_hash前后相同的实际小probe，但hash摘要也不替代fresh kernel/interface/trust捕获。

**当前唯一Lake进程仍在重新验证root/维数，新的public841、actual12091/32+56和完整build尚未完成。** 先前所有f56捕获/32直接责任结果仅代表其历史源绑定，不能冒作当前20ae最终证据。等待协调者提供fresh provenance、实际capture与fullbuild完成日志后再更新最终阶段。本问题保留接口内部路线仍可继续正常核验；no_expose和privateInPublic没有实施，原no_expose提案未获人审批准。

status=pending-human-review，human_decision=null。报告员仅更新独占issue报告及证据，没有授予实现/发布权限或改写任何其他成员记录。


## 最终独立验收：当前20ae实现全部既定工程检查通过

本节为当前最终状态，替代前文最新阶段尚在等待fresh/root/full结果的表述，并保留全部原始失败、候选和证据等级。报告员独立读取正式结果与原始日志、fresh provenance/归档capture、auditor full-type实际输出及执行文件、verified-completions、最终源文件；未重跑Lean/Lake或改写其他成员记录。复算全部结论见 independent-final-20ae-validation.json。

### 来源绑定和完整类型

实际 Standard SHA-256 仍为 `20aef9056c2650ba7e645ba8119d6f665651cabe97327a65b68bc8c98342e726`，同时匹配fresh capture-provenance与正式full-build-result的inputs_before。归档public/trust JSON及两份capture Lean源四个SHA全部匹配provenance，两个实际capture执行结果SHA亦匹配。因而当前结论不再借用旧f56阶段证据冒充20ae。

auditor/full-type-capture/execution.json 实际exit0，source/provenance/build inputs均声明unchanged；报告员另独立重算执行source、provenance及输出文件SHA，全部匹配其绑定值。更进一步，直接 `git show bef90640…:metadata/computation-api.json` 取原冻结数据，而不是仅信任已经更新证明状态的工作树API；独立对比实际full-types.json的 **841项full_type全文、type_fingerprint、universes**，逐项零差异，名称集合也精确相同。ordinary root public capture exports与同一原git锁的841精确集合相同。actual full-type输出确认basisCount当前状态为 `[irreducible]`。

fresh actual capture仍为12091条，verified-completions的32个actual row逐字匹配；32项直接责任消除和56项保留未改变。已消除项中 **15项没有项目待补依赖，17项仍经sorryAx传递依赖已登记待补**。这不是12091条全部无待补，也不是球面/detector几何比较已完成；相关比较、坐标基责任仍保留。

### 正式root与默认完整构建

`computation-basis-count-performance-build-result.json` 实际exit0，1162.400054秒，inputs_unchanged=true、resource_stops=[]，正式目标为KIP126.Computation。这包含生产global属性传播后的维数/下游重编，不再只是local probe。

`full-build-result.json` 实际exit0，173.904678秒，targets=[]（默认完整构建），inputs_unchanged=true、resource_stops=[]；full-build.log 最终明确 `Build completed successfully (3102 jobs)`。日志实际显示原 ZeroDegree 2.1秒、Frames 3.2秒完成。报告员又将这两个生产Main文件逐字与原git基线比较，均完全相同，因此这里既非改Main证明，也非抬高原200000/1600000预算后的通过。

正式full日志还包括 Tests.Computation.Consumers、Tests.Computation.Interface、Tests.Integration、Tests.Architecture、Tests.Trust及所有既有模块内部审计。Tests.Trust实际报告19 consumer declarations、无local axioms或sorry；Computation.InternalAudit实际报告5642 declarations、56已单独登记待补、无project axioms。其他模块内部审计也随默认构建通过，保留其自身登记待补。完整日志中的预期#check_failure“Unknown identifier”是info级边界测试输出，不是构建error，不能据字符串误判失败。最终source-inventory日志实际报告475项目文件、27 consumer/audit文件覆盖以及依赖/私有import边界验证通过。

### 本问题最终技术结论与人审状态

expose/body/额外导出问题已通过保留原接口的内部实现及fresh正式验收解决；不存在因这项已解决封装问题而必须实施no_expose的理由。normal kernel safe addDecl、真正私有本地elaborator和显式原定义Eq proof没有引入新公理、额外前提、结果包或责任转移。basisCount irreducible是已披露的默认elaborator策略改变，原kernel值/定义相等/公开body及完整类型保持，并已在原全部消费者和预算下实际验证。这项判断不等于任何agent授予接口修改权限。

原no_expose备选、privateInPublic研究及全部失败数据仍留在本报告和各独占run目录；旧提案未经人类批准且未实施，不因最终技术验收通过而记录为“获准”。status仍严格 `pending-human-review`，human_decision=null；没有可填写的人类批准原话或出处。若人类之后审阅原提案，当前建议为保留接口内部路线已完成，无需执行旧接口调整。

本问题不再阻塞当前Computation迁移成果的工程交付；后续数学目标仅按仍登记的56项及其他模块传递责任继续，不能把本轮工程成功扩大为所有固定对象计算已证明。无提交、推送或发布授权由本报告产生；报告员本轮仍只写指定issue目录，未动源码、接口锁、全局索引或Lake状态。
