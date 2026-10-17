---
issue_id: "AdamsSynthetic-20261017-struct-generated-proof-exports"
responsibility_module: "AdamsSynthetic"
targets:
  - "KIP126.AdamsSynthetic.Standard.graded_compose"
  - "KIP126.AdamsSynthetic.Standard.graded_compose_homogeneous"
baseline_commit: "bef90640c4594af4db32c86837f9d95340d1e171"
worktree: "/tmp/kip-adams-synthetic-20261017-struct"
candidate_source_commit: null
api_file_and_sha256: "metadata/adams-synthetic-api.json; original baseline 2fb1b8af37f2e926d72c3e6e8bceb13ec37c5574325f9511d92bb9676e8f20e2; status-sync intermediate snapshot 968635388977aaaa24e957c12225447b03587197e1ffe227a3e40a65efdcdbda; final position-refreshed record c29c08f33689aa99c8576a700b03f61ae7b616efe18ebf491f5a2ac0713235cf"
source_file_and_sha256: "KIP126/AdamsSynthetic/Standard/Operations.lean; final 63bb1c57b1bc949af0553c8baebc6e4ef95090be38594e0a83b26e9f837ad1d0"
reporter_agent: "/root/generated_export_reporter"
independent_of_discoverer_and_implementer: true
evidence_level: "独立 Lean 最小复现、最终源码与研究候选裸 Lean 重放、普通消费者捕获独立全量比对；未证明无接口变化的所有实现均不可能"
status: approved-interface-change
human_decision: "2026-10-17，本聊天用户：同意以上提案，修改原接口。具体范围见文末本轮批准记录。"
---

# 接口调整人审报告

## 请求人类决定的具体问题

**本轮已经保留全部冻结接口交付可完成部分，不需要放开任何导出才能继续验证。** 最终源码已完成 `graded_module`、`graded_lambda_smul`，这两项不受本报告阻塞；`graded_compose` 与 `graded_compose_homogeneous` 保留原有两处 `sorry`，没有新增责任。报告员独立比对最终普通公共导入捕获：1825 → 1825，名称增删、完整类型、类型指纹、宇宙及逻辑公理集合变化均为空；见 [最终比较](evidence/final-public-interface-comparison.json)。这只是接口及本地证明状态结论，不代替协调者的最终全仓构建。

剩余具体问题：若后续继续合入复合的数学候选，是否允许**仅将 `graded_compose` 的定义体改为不向普通导入公开**，即在它原有完整签名前加 `@[no_expose]`？该备选保留数学类型、对象、两侧线性性、齐次公式和责任归属，要求继续保留原 `graded_compose._proof_1` 的精确冻结类型。它会改变普通消费者的定义展开能力，故必须人审。玩具对照已经核实这种语义变化；实际项目的完整候选、原辅助名保留及所有调用方尚未完成验证，**此项仍是待验证备选，不能直接实施**。

安全默认是继续保持当前冻结，寻找内部证明方案。报告不请求笼统允许新增 generated declarations，也不将已观察到的 11 项前缀新增当成数学上最小或必需集合。另一可精确描述但不建议接受的历史方案，是原样接受已留档研究候选的 11 项前缀新增和原 `_proof_1` 改型；它并不保留原辅助接口，而且尚未完成全模块导出枚举，不能据本报告直接批准该候选合入。

## 原接口、背景与问题成因

本次来源与责任由任务限定为抽象 Adams/synthetic 系统中的结构证明。固定基线的 `Operations.lean` SHA-256 为 `4e7e9e1916bbef4c18abba0510448a11b6b2a0b688e4db87c098d9afe8b24bd2`；只读参考 a48 为 `a484b981fad612eabe2bc7a01b54e049e9a01ce4`。报告员独立执行 `git grep`，a48 中没有 `GradedLambdaEnrichment`、`TotalWeightHom`、`weightHomLambda` 或这四个目标的对应声明，未发现可直接迁移的完整证明。当前候选应登记为本轮结构构造，不是 a48 原证明迁入。

`SyntheticSpectrum : Type 1` 和 `syntheticCategory : SyntheticCategory.{1,0} SyntheticSpectrum` 是当前 Standard 背景中的固定对象；这些声明没有额外宇宙参数。`WeightHom.{1,0} X Y w` 是从 `(biShift (0,w)).obj X` 到 `Y` 的实际态射，`TotalWeightHom.{1,0} X Y` 是这些 Hom 的整数分次直和。λ 降低源权重一；复合先取 `g : Y → Z` 再取 `f : X → Y`，齐次权重为 `a+b`。不是在每个未分次 Hom 上另选多项式作用。

原数学声明完整源码签名如下；所有隐式类别实例均由上述固定 `syntheticCategory` 取得，局部模实例在签名中显式列出。完整冻结呈现、宇宙和依赖另见 [原签名证据](evidence/original-signatures.json)。

```lean
@[implicit_reducible] public def graded_module :
    ∀ X Y : SyntheticSpectrum,
      Module (Polynomial ℤ) (TotalWeightHom X Y) := by sorry

public theorem graded_lambda_smul :
    ∀ (X Y : SyntheticSpectrum) (w : ℤ) (f : WeightHom X Y w),
    letI := graded_module X Y
    (Polynomial.X : Polynomial ℤ) • weightHomInclusion w f =
      weightHomInclusion (w-1) (weightHomLambda f) := by sorry

public def graded_compose : ∀ X Y Z : SyntheticSpectrum,
    letI := graded_module X Y
    letI := graded_module Y Z
    letI := graded_module X Z
    TotalWeightHom Y Z →ₗ[Polynomial ℤ]
      TotalWeightHom X Y →ₗ[Polynomial ℤ] TotalWeightHom X Z := by sorry

public theorem graded_compose_homogeneous :
    ∀ (X Y Z : SyntheticSpectrum) (a b : ℤ)
      (f : WeightHom X Y a) (g : WeightHom Y Z b),
    graded_compose X Y Z (weightHomInclusion b g) (weightHomInclusion a f) =
      weightHomInclusion (a+b) (weightHomComp f g) := by sorry
```

文件在 `module` 与 `@[expose] section` 下，故公开定义的定义体也参与普通导入接口。契约 `obligation-zlambda-enrichment` / `support-enrichment` 将结构与实际移位、实际 λ 及实际复合相联。元数据把自动辅助声明归为非独立数学承诺，但当前 API 锁和用户指令仍冻结其名称、类型和导出；不能仅因它们由 elaborator 产生而自动豁免。

原已导出生成支持是：

```lean
-- universe parameters: []
KIP126.AdamsSynthetic.Standard.graded_compose._proof_1 :
  ∀ (X Z : KIP126.AdamsSynthetic.Standard.SyntheticSpectrum),
    SMulCommClass.{0,0,0} (Polynomial.{0} ℤ) (Polynomial.{0} ℤ)
      (KIP126.AdamsSynthetic.TotalWeightHom.{1,0} X Z)
```

此呈现隐藏的标量作用实例精确来自 `graded_module X Z`。其冻结类型指纹为 `13301073175485286128`，完全展开实例参数的原 kernel 类型见 [原始 kernel 类型](evidence/original-proof1-raw-kernel-type.txt)。简单另写 `letI` 签名即使数学等价也可能保留 `let` 节点，从而不保留冻结指纹；报告员的 [签名对照](evidence/OriginalHelperSignature.log) 实测为 `1034105542232245081`。因此本报告不承诺一个未验证的显式重声明就能保型。

问题来自暴露的公开数据值中的新证明字段：Lean 4.32.2 在 elaboration 和 `Meta.abstractNestedProofs` 阶段产生公开 `_proof_*`，广义 `simp` 还可按需生成 `eq_1` / `congr_simp`。最初数学候选的四个数学签名保持不变，但原辅助名被另一证明占用，并增加公开辅助名。**这是实现产生的导出不相容；没有证据表明原分次数学命题为假、漏前提或固定对象约定错误。** 同样，没有证明所有保留原接口的构造路线都不可行。

## 真实前提与对象核对

| 前提或对象条件 | 是否满足 | 证据及仍依赖的待补责任 |
| --- | --- | --- |
| 固定 `SyntheticSpectrum`、`syntheticCategory`、宇宙 `{1,0}` | 类型层面保持 | 原锁与最终普通消费者逐项相等；固定背景本身仍是登记上游责任。 |
| 多项式作用位于总分次 Hom，λ 的权移为 `w-1` | 保持 | 最终两个直接证明的独立重放无直接 `sorry`，`graded_lambda_smul` 指纹 `10082347246846211589` 不变。 |
| 复合确为实际移位复合，先 `g` 后 `f`，权重 `a+b` | 研究候选保持；最终尚待补 | 候选按直和双加性扩张，齐次公式经过 kernel；最终没有把候选错误计作已合入。 |
| 移位加性、结合律及 λ 中心性 | 候选按现有结构调用 | 原候选消费 `exactness.shiftAdditive`、`quotients.coherence`；没有新增调用方假设或结果包。 |
| 本轮排除具体谱模型、Milnor/cobar 与具体模型比较 | 保持 | 研究候选直接路径在抽象预加性、移位、λ 和多项式构造中；未接手被排除的实现。 |
| 生成支持和真实私有边界 | 最终保持；研究候选不保持 | 最终 1825 个导出精确匹配；`privateInPublic` 对照证明可造成实际私有名公开可访问。 |
| 原 `_proof_1` 的完整类型 | 最终保持 | 独立最终重放指纹 `13301073175485286128`；保留原复合 `sorry` 自动保留原生成支持，没有手改锁。 |

## 独立证据与复现

报告员未参与原候选发现或实现。独立读取了用户任务、AGENTS、协议、API/契约/来源/待补登记、当前及留档源码、Lean 实现，并运行以下对照和重放；没有修改生产源码、锁文件、检查或全局记录。

1. **最终生产源码重放。** `FinalProductionReplay63.lean` 仅复制 SHA `63bb1c57…` 的实际源码，增加 `import Lean` 和诊断，不改任何证明体。裸 Lean 不传 `-o`，exit 0。五个有关导出中，`graded_module`、`graded_lambda_smul` 无直接 `sorry`，`graded_compose`、`graded_compose_homogeneous` 仍有直接 `sorry`，原 `_proof_1` 无直接 `sorry`。完整命令、环境、输出见 [重放记录](evidence/final63-replay-results.json)、[捕获](evidence/FinalProductionReplay63.json)。随后独立重算最终 root 普通消费捕获，1825 全量精确匹配。
2. **研究候选重放。** 留档源 `run/graded/compose-research-candidate.lean.txt` SHA `2c3887f1ca5a2b2bceb48c0bc2a0173c0a957f89bb1f2392871ed8fab49e93e0`。报告员只替换末尾诊断、没有改数学代码，裸 Lean exit 0，四个目标均无直接 `sorry`。在 `graded_module` / `graded_compose` 前缀及另两目标的诊断范围内有 16 项，较原相关 5 项新增 11 项、改型 1 项；这不是全模块导出枚举。完整显式类型及原始 kernel 表达式见 [独立捕获](evidence/ComposeCandidateReplay.json) 和 [差异](evidence/compose-candidate-diff-complete.json)。
3. **历史 c3 全量差异独立重算。** SHA `c3eb9589b2ec77bb1953855f70ca7fe6c3f5e598bf7931b7253a3b77d8b10104` 曾产生全模块 1825 → 1856，31 个新增、0 个删除、1 个既有类型变化。其中 27 个归属 Operations，4 个归属 Background。完整证据见 [历史差异](evidence/c3-export-diff.json)。该候选已经被拒绝，不能把 27 或 31 称为当前两项必需的最小授权集合。Background 的相关生成声明及最终 module 证明触发的 lazy 声明已在实现中消去。
4. **`privateInPublic` 实际可访问性。** `ProducerDisabled.lean` 不开选项公开引用私有证明，exit 1，错误为私有声明不能在公开处使用；`ProducerEnabled.lean` 开启后 exit 0 并警告公开访问私有声明。普通 `public import` 的 `OrdinaryConsumer.lean` 自己不开选项；用户别名 `#check_failure` 成功，但通过完整 `_private.ProducerEnabled.0.ReporterEnabled.privateProof` 名称可正常 elaboration。对照使用 `Term.withoutErrToSorry` 且断言结果不含 `sorry`，同时确认该名在 exporting environment 中。不开选项的 Plain 私有证明在普通环境缺失。三份成功对照 exit 0；见 [结果](evidence/privacy-results.json) 与 [消费者日志](evidence/OrdinaryConsumer.log)。因此不能以 `isPrivateName` 过滤后的表面名单未变，宣称真实私有边界未变。
5. **自动嵌套证明。** 开启 `backward.proofsInPublic true` 后，非原子证明 `Eq.trans (Eq.refl 1) (Eq.refl 1)` 仍生成公开 `complexBox._proof_1`，原子 `Eq.refl 1` 不生成。`NestedExtraction.lean` exit 0；见 [日志](evidence/NestedExtraction.log)。结合本机固定版本 `Lean/Meta/AbstractNestedProofs.lean` 第 40–111 行和 `Lean/Elab/SyntheticMVars.lean` 第 458 行起，只能得出所用开关不全面关闭抽取，不能得出原目标无法以不同内部构造实现。
6. **`no_expose` 语义。** `ProducerExposure.lean` 与普通 `ExposureConsumer.lean` 均 exit 0。公开类型相同；exposed 值可 `rfl`，no_expose 值在普通消费方无法 `rfl` 展开，但已给出的公开计算定理可用，私有证明未导出。见 [结果](evidence/exposure-results.json)。这是 Lean 语义的最小复现，不是实际 `graded_compose` 完整项目候选验证。

可在本目录执行：

```sh
python3 evidence/reproduce.py --toys-only
python3 evidence/reproduce.py
```

脚本只在证据目录生成玩具模块产物；完整运行读取记录在 `replay-results.json` 的固定 `LEAN_PATH`，重放不传输出标志，不写项目 `.lake`。生产重放、候选重放、选项实验分别记录真实 exit code；没有把初次沙箱启动失败、语法修正前的实验或吞错产生的 `sorry` 当成成功证据。

依赖审计：报告员重新遍历已有 kernel capture 的全部项目闭包，并独立阅读候选证明体。c3 四目标的闭包没有返回目标的依赖环，没有通过 `gradedEnrichment` 或派生结合律倒推目标，没有调用争议分离性、Milnor、实现模型或结果包作为捷径。模块/λ 两项在 c3 中保留 7 个登记直接上游待补：`Spectrum`、`SyntheticSpectrum`、`spectrumCategory`、`syntheticCategory`、`nu`、`recovery`、`exactness`；复合另依赖 `syntheticCofiber`、`quotients`。这些是 c3 的传递依赖记录，不能套称最终更简 λ 构造的精确闭包。最终捕获仍含 `sorryAx`，所以本地直接完成不表示所有背景已证明。详见 [依赖审计](evidence/dependency-audit.json)。模块系统把若干导入的定理/非暴露声明显示为 `axiomInfo` 视图；本报告按实际 `collectAxioms` 与直接 `sorry` 登记判断信任，不把视图种类误报为新增数学公理。未发现利用不一致环境或 `False.elim` 的证据，也没有在此证明抽象背景整体一致。

## 方案及精确差异

### A. 保持原接口的内部方案——当前采用

先将 λ 的总 Hom 加性映射改为公共数据组合器 `DirectSum.toAddMonoid`、`Preadditive.leftComp`、`AddMonoidHom.comp` 的组合，再以 `Polynomial.eval₂RingHom'` 和 `Module.compHom` 给出多项式模。证明辅助保持真实私有；公开数据中不再引入新的复杂证明字段。最终 `graded_module` / `graded_lambda_smul` 已用此路径完成；λ 齐次计算使用精确改写以避免 lazy equation / congruence 支持被导出。

复合双线性候选仍需新证明字段，目前没有已验证的完整、保留全部导出且保持 expose 的实现。可以继续研究公共双加性/线性数据组合器，以及把 λ 相容证明放入真正私有的证明环境；不得把现有失败提升为无解结论。本轮将原复合二项保留为待补，这是原责任的延续，不是给下游添加新前提。原 `_proof_1` 保留原型的办法在当前分支已实际验证：不合入改型候选，保持原公开复合声明及其类型 elaboration。

### B. 已观察候选的精确漂移——不能直接当批准集

研究候选中原 `_proof_1` 被改为以下**不同**命题，宇宙参数仍为 `[]`，指纹变为 `6764674208015818020`：

```lean
∀ (X Y Z : KIP126.AdamsSynthetic.Standard.SyntheticSpectrum)
  (b : ℤ) (g : KIP126.AdamsSynthetic.WeightHom.{1,0} Y Z b) (a : ℤ),
  (KIP126.AdamsSynthetic.weightHomInclusion.{1,0} (a+b))
    (KIP126.AdamsSynthetic.weightHomComp.{1,0} (0 : KIP126.AdamsSynthetic.WeightHom.{1,0} X Y a) g) = 0
```

这是齐次复合保零，原来是总 Hom 上两个多项式标量作用可交换；两者前提、量词和结论不同。主数学声明类型没变，仍不能默许这项已冻结导出的改型。精确原/候选全类型及隐式实例在 [差异 JSON](evidence/compose-candidate-diff-complete.json) 中逐项保留。

候选在已枚举前缀范围内新增如下 11 名，全部为无额外宇宙参数的生成支持：

| `KIP126.AdamsSynthetic.Standard.graded_compose.` 后缀 | 类型指纹 |
| --- | --- |
| `_proof_2` | `15278113679731647993` |
| `_proof_3` | `11333382591365444844` |
| `_proof_4` | `6875382576527178117` |
| `_proof_5` | `13924055376003879316` |
| `_proof_6` | `1519847942565273603` |
| `_proof_7` | `7468560993772528295` |
| `_proof_8` | `16392846838704083923` |
| `_proof_9` | `12003571349092450339` |
| `_proof_10` | `13301073175485286128` |
| `_proof_11` | `6071241059108734780` |
| `eq_1` | `5331259268022784308` |

其中 `_proof_10` 才具有原 `_proof_1` 的类型指纹；把它移到新编号不等于保留原名称。不能只删新增集合中的 `eq_1` 或改检查过滤器就认为已修复。若以后选择保持 expose 并增加支持声明，必须先得到保留原 `_proof_1` 精确类型的完整候选，再全量枚举其真实新名及完整类型，形成可独立审核的最小实际差异；本报告没有提供这一尚未实现的候选，也没有请求批准它。

### C. 仅改变 `graded_compose` 的定义体公开性——待人审备选

原签名为上文 `public def graded_compose : ...`，位于 expose section。候选仅变为：

```lean
@[no_expose] public def graded_compose : ∀ X Y Z : SyntheticSpectrum,
    letI := graded_module X Y
    letI := graded_module Y Z
    letI := graded_module X Z
    TotalWeightHom Y Z →ₗ[Polynomial ℤ]
      TotalWeightHom X Y →ₗ[Polynomial ℤ] TotalWeightHom X Z :=
  -- 使用经过核验的实际复合构造；完整实现仍需在项目中验证。
  ...
```

这里 `...` 是方案说明占位，不是可合入代码或新增 `sorry`。数学前提、结论强弱、分次、固定对象和责任归属均应保持；唯一拟允许的接口语义差异是**普通导入不再得到 `graded_compose` 的定义体及其定义性计算**。`graded_module` 的 expose / implicit-reducible 属性和其他公开声明不在授权范围内。普通使用必须依赖已经提供的齐次公式与线性结构；其证明仍由 AdamsSynthetic 负责，不能要求下游补双线性或添加新假设。

实际应用前必须证明：原 `_proof_1` 仍以原名称、完整 kernel 类型和宇宙导出；不新增其他导出；复合和齐次公式均消除直接 `sorry`；泛型结合律/单位律、普通消费及信任审计通过。若任一条件做不到，需要另报精确差异，不能把本方案当授权继续改型。玩具对照不能保证这些项目条件，所以当前尚无可直接实施的完整补丁。

### D. `privateInPublic` / 放宽过滤——不建议

选项的 Lean 描述明说导出 private 声明、允许任意访问；`Lean/AddDecl.lean` 第 136 行起对私有声明启用真实导出。独立对照证明这不是单纯隐藏名称的实现技巧。保持 `_private` 拼写并让 API 检查跳过它们，会改变真实消费边界。该方法不是保留接口的内部证明方案；本轮最终未启用此选项，也没有修改检查。

## 下游影响

| 声明、调用方或记录 | 影响与责任 |
| --- | --- |
| `graded_module`、`graded_lambda_smul` | 已在冻结接口下直接完成；不得因复合争议回退，也不需要本报告批准。 |
| `graded_compose`、`graded_compose_homogeneous` | 本报告准确受阻范围；实际候选仍由 AdamsSynthetic 完成，原二项待补保留。 |
| `gradedEnrichment`，`graded_associative`、`graded_left_unit`、`graded_right_unit` | 结构装配及派生调用仍可使用原登记上游接口，但其复合传递责任不能被标为已关闭；no_expose 方案须复验这些调用。 |
| `GradedLambdaEnrichment.compose_lambda_left/right`，`Tests.AdamsSynthetic.Structural` | 数学消费类型应保持；可能依赖计算的消费须用原有公式核验，不默认给下游加前提。 |
| 其他五模块及固定 Main 目标 | 无需改变名称、类型、前提、职责或主目标。未发现源码直接展开 Standard 复合的跨模块调用；全仓消费仍由现有集成测试核验。 |
| `metadata/adams-synthetic-api.json` | 当前不改；若将来批准具体新增支持或公开性语义，须先锁定准确差异，不得批量刷新六模块掩盖变化。 |
| `metadata/adams-synthetic-contracts.json` / `*-sources.json` / `proof-obligations.json` | 当前只按实际两项完成同步；保留复合二项及上游背景未证责任。若批准 no_expose，应明确记录公开性决定、来源及计算定理责任，不能删除历史证据。 |
| `Tests.AdamsSynthetic.Interface`、Internal/Trust、Architecture、Integration | 原检查保留。现有 Interface 排除私有名，因此如使用兼容导出选项仅靠它不能证明真实私有边界；本轮没有使用此选项。 |

后续任何获准实施均需普通 `KIP126.AdamsSynthetic` 消费、精确类型/宇宙/信任/导出比对、现有 AdamsSynthetic/Architecture/Integration/Trust 检查、`python3 scripts/check-source-inventory.py` 和完整 `lake build`；本报告员没有修改这些检查。默认本轮分支的全构建由协调者串行执行，报告不会将正在进行的构建写为已通过。

## 阻塞范围与继续项

当前只暂停将已知导出漂移的 `graded_compose`、`graded_compose_homogeneous` 候选合入。其数学命题没有被推翻；安全分支仍保留原登记上游入口，不能把未合入候选算作直接责任完成。

`graded_module`、`graded_lambda_smul`、两个 E∞ 相容性及本 session 其余已在冻结接口下完成的结构证明、来源/责任更新、公共消费、库存和全构建都可以继续。最终源码与普通消费已避免本报告所述漂移，因此本报告不阻塞这些独立成果的验证或本轮无提交/无推送交付。具体谱模型、Milnor/cobar 与历史分离性问题不因本报告重新进入本轮范围。

## 人类审核记录

尚无人类对本报告的具体方案作出明确决定。`status: pending-human-review`，`human_decision: null`。协调者采用保留冻结的安全分支、agent 建议、其他报告获批或等待均不构成本报告中方案 C 或新增支持声明的人类授权。未经明确批准，本报告备选代码只作审阅展示；实施须由协调者后续安排。


## 本轮批准记录（2026-10-17）

用户在本聊天阅览七份报告摘要后明确回复：

> 同意以上提案，修改原接口

本报告获准范围：

- 方案 C：仅 graded_compose 使用 no_expose；原 _proof_1 名称/完整类型/宇宙必须保留；不得新增其他导出。

该批准不是新增公理、额外待补责任、任意 Main 公共前提或未列明接口变更的授权。原文中的“尚未批准”保留为历史阶段记录；实现及实际验证另记，批准不表示证明已经完成。
