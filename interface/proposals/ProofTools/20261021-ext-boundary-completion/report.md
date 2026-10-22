---
issue_id: ProofTools-20261021-ext-boundary-completion
title: 完成有限层满射合成的经典 Ext 连接同态比较
summary: 已按 2026-10-22 授权建立支撑 5.49 的最小上游接口，完成其无本地证明洞的 Ext 输出证明及 Blueprint 绑定。既有接口与原 199 项待补记录保持不变，精确新增五项上游构造或比较责任；完整 lake build 与 49 项 Blueprint 测试通过，不宣称上游基础或全信任链闭合。
responsibility_module: ProofTools
targets:
  - KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary
  - KIP126.ProofTools.Standard.FiniteLayerSurjectivityMahowaldLeibnizStatement
  - sem:ProofTools:cprime
baseline_commit: fa6c729fe2f1b251ef6ead8838a0fbbb0975f8aa
reporter_agent: /root/ext_interface_report
latest_reviewer_agent: /root/ext_authorization_scope
latest_review_date: '2026-10-22'
independent_of_discoverer_and_implementer: true
evidence_level: 独立源码、公开锁与许可待补核对；现有接口及新增私有群短正合证明的 Lean kernel 探针通过，实际局部证明体闭包已核验；不是 Ext 身份、反例或不可证明性证据
status: approved-implemented-and-validated-before-publication
human_decision: '2026-10-22 用户明确回复：“是的我同意,注意对上游接口做尽可能小的改动,也不要去形式化上游接口的上游接口,只需要建立足以支撑我们 5.49 结论的上游接口就行”。批准最小跨模块接口扩展，保留既有接口，止于足够支撑 5.49 的上游边界；必要源构造及文献比较可精确登记为上游待补责任，5.49 的本地证明须完整。尚未验收未实施的具体签名或数量。'
---

# 有限层满射合成的 Ext 边界比较

## 人审结论与当前执行范围

本报告不请求重新批准 Blueprint 5.34、5.47、5.48、5.50 的公开包装与绑定。用户已授权这些工作，它们不受本问题阻塞。

2026-10-21 原请求为：**是否允许在 AdamsSynthetic 与 Literature 两个上游模块中补实际同调余模、其 Ext 及与当前第一商操作的比较构造和证明，以完成 Blueprint `sem:ProofTools:cprime` 的既有经典 Ext 陈述？** 用户于 2026-10-22 已明确批准，并限定为建立足够支撑 5.49 的最小上游接口，不再向这些接口的上游递归形式化；该模块边界授权不再阻塞实施。

当前授权严格限定为选定 `Standard.model` 的 `ClassicalObject` 对象族、同一实际 `TriangleData`、同一实际同调短正合列及分次 `(s,t) → (s+1,t+1)`；保留所有现有公开声明的名称、类型、前提、对象关联及导出，另增完成上述识别所需的最小源对象、文献比较与公共消费接口。**不将比较等式或结果包变成 5.49 调用者的额外前提，也不将经典 Ext 陈述改写成仅以第一商操作为输出的较弱替代。**

原建议要求新增接口全部来自构造或完整证明，承诺不新增公理或待补责任；这是当时的推荐实施方案，不是用户此次要求继续完成全部上游基础的授权。最新人审将实施边界收窄到必要接口：允许将其确需的固定源构造及文献比较精确登记为 `pending-construction`／`pending-proof`，保留来源、完整数学条件、对象关联及传递信任边界，既有已登记责任可直接调用。不得以此新增与 5.49 无关的责任、任意公理或把整个合成结论登记为上游假设。**ProofTools 的 5.49 本地推导须无证明洞；依赖上游待补接口不表示全信任链闭合。**

这是已获准的模块边界扩展，尚不是已完成候选签名的验收。本报告保留数学目标与待实现接口草案的区别，不把未定义名称列为现有可调用接口。具体新公开类型和待补责任仍须按实际实施独立核对、捕获及登记；本次授权本身不证明 5.49 已完成，也不确认任何尚未实施的接口数量。

## 原接口、背景与问题成因

当前 Blueprint 原始目标、数学前提、结论和证明只维护在 [ProofTools.tex 的 `cprime` 条目](../../../../blueprint/chapters/ProofTools.tex#L2107)，不在本报告另立一份修正版。该条目不是 AimPaper 的编号原命题，而是有限商、Bockstein 比较和有限修正的项目推导。

问题是**尚未构造目标表示与证明比较**，不是已发现假命题、漏掉数学假设或发现现有合成证明实现错误。现有结果已完整证明其实际归一化商操作版本；它没有同时构造另一个由实际同调短正合列定义的 Ext 连接同态。

固定背景为 `Standard.model : Model Spectrum SyntheticSpectrum`；kernel 实际宇宙为 `{1,0,1}`，两个下游公开定义本身无自由宇宙参数。`ClassicalObject` 仅由 sphere、实际 ν-cofiber、选定 detector 及整数移位构成；不要求对所有谱泛化。`TriangleData` 保存这三个对象、实际 `f,g,h` 及其 distinguishedness，不是三张任意线性映射。

这个对象范围不是本次为便于补证而收窄。独立逐字比较确认：[ProofTools 章首第 1–7 行](../../../../blueprint/chapters/ProofTools.tex#L1) 中“composition theorem 使用固定 Standard model、经典对象属于选定族”的约定在基线 `fa6c729fe2f1b251ef6ead8838a0fbbb0975f8aa` 已存在，当前前七行完全相同。因此所需比较应覆盖这个族中任意实际 `TriangleData`，不必额外泛化所有谱；也不能只证明某一个数值三角或把 5.52／底层群 SES 当作整个 5.49。对照结果记录在新增 [补证元数据](evidence/homology-ses-review.json) 中，正文量词未改。

现有第一商操作的完整公开类型为：

```lean
public def cofiberFirstQuotientBoundary
    (T : TriangleData model.auxiliary)
    (hef : normalizedExponent model.classicalTower T.f = 1)
    (s t : ℤ) (x : Ambient model T.X (s,t)) :
    Ambient model T.Y (s+1,t+1)
```

其值由实际归一化 `T.f` 在 `Q₁` 上的映射，经固定 `model.firstQuotient` 及悬挂/weight 等式运输得到。这里 `e(f)=1` 表示正 Adams 滤过，不能读成滤过恰好一；它也不是普通 `E₂(f)`。

完整合成命题的公开类型为：

```lean
public def FiniteLayerSurjectivityMahowaldLeibnizStatement
    (T : TriangleData model.auxiliary)
    (hef : normalizedExponent model.classicalTower T.f = 1)
    (heg : normalizedExponent model.classicalTower T.g = 0)
    (heh : normalizedExponent model.classicalTower T.h = 0) : Prop
```

完整定义体、其调用的 `MahowaldLeibnizFiniteLayerSurjectivity`、泛宇宙/实例/上下文见 [逐字源码快照](evidence/existing-signatures.lean.txt)；编译后类型见 [kernel 输出](evidence/boundary-interfaces.log)。定义体逐一保留：

- 同一归一化三角的 `NormalizedTriangleCompatible`；
- `R,K : ℕ` 且 `2 ≤ R, 2 ≤ K`，所有 `s,t : ℤ` 和实际 `x,z,v`；
- `x,z` 的输入 cycle 资格，两条真正的 Adams 微分；第一条的目标包含实际 `h` 页映射及同一 tower 的 desuspension；
- **每个** `1 ≤ j < K` 上的 cycle-qualified 满射条件和 `B_(R+j−1)`，包括最后一层；
- 输出是 `y = cofiberFirstQuotientBoundary T hef s t x` 的实际 cycle 资格及指定 `d_(R+K−1)`，不要求 `y ≠ 0`、输出存活或目标永久。

它的完整内部证明是 [Corollaries.lean:541 的 `finite_layer_surj_statement`](../../../../KIP126/ProofTools/MahowaldLeibniz/Corollaries.lean#L541)，现在已由 `Standard.finiteLayerSurjectivityMahowaldLeibniz` 公开包装并绑定在 Blueprint `sem:ProofTools:cprime-model`。原报告员与本次更新复核者均未参与这些证明的发现或实现。

## 2026-10-21：真实前提与对象核对

| 条件或对象 | 独立核对结果 | 证据与限制 |
| --- | --- | --- |
| 固定模型及对象族 | 已明确 | `System.lean` 的 `ModelData`，`Configuration.lean` 的 `ClassicalObject`/`TriangleData`；没有额外一般谱任务。 |
| 实际 normalized triangle | 已有定义及真实兼容性前提 | `Literature/Triangles.lean:70–108` 从三条归一化映射定义三角；兼容性是 distinguishedness。 |
| 同一第一商与实际 Adams E₂ | 已有 | `FirstQuotientComparison` 是 `BiHom(t−s,t+a,Q₁Σ^(0,a)νX) ≃ₗ[ℤ] E₂^(s,t)(X)`；它不是一般余模 Ext 比较。 |
| 实际有限商横行及其符号 | 已证明上游接口可调用 | `normalized_finite_quotient_horizontal_row` 保留同一映射及字面负号；取 `q=1` 可给实际第一商三角。 |
| 度数逐项的同调短正合性 | 已在 ProofTools 内部证明底层群版本 | 从同一 `T` 的 `e_f=1` 导出 `ZeroOnModTwoHomology`，再证明 `HomologyShortExact model.coefficients (Triangle.mk T.f T.g T.h).rotate`；逐度保留实际 `g_*` 单射、`g_*/h_*` 正合和 `h_*` 满射。不含 Steenrod coaction，也未把原未旋转三角误代为短正合列。见下述新增独立核验。 |
| 一般 `H_*X` 的实际 Steenrod 余模及映射 | 当前未找到已构造/已登记接口 | 全库源码检索及完整 `ModelData` 字段核对；不能以单纯关键词缺失代替此结构核对。 |
| 这些余模的实际派生 Ext 与 Adams E₂ 的自然比较 | 当前未找到 | `sphereE2_milnorEquiv`、`milnorCoordinates` 等只针对 sphere；ν-cofiber 和 detector 不由这份 sphere 比较自动覆盖。 |
| 同一同调 SES 的 Ext δ 与实际归一化 Q₁ 映射相等 | 尚未证明 | 不包含在 BHS A.1/A.11 当前接口中；那些接口控制有限 lift/Bockstein/Adams 微分。 |

AimPaper 的 [synthetic 背景段落约第 791 行](../../../../AimPaper/main.tex#L791) 明确把模 λ 的特殊纤维联系到 dual Steenrod algebra comodules 的派生范畴。这说明正确的数学比较路线，但**正文引用不等于项目已形式化该范畴或此等价**。当前已登记有限 Bockstein 比较也没有悄悄提供这一完整识别。

## 独立证据与复现

本报告实际执行并通过：

```text
lake env lean -o /tmp/ext-boundary-interfaces.olean \
  interface/proposals/ProofTools/20261021-ext-boundary-completion/evidence/BoundaryInterfaces.lean
```

退出码为 0。探针使用普通公开导入，仅输出已存在接口的展开类型和公理列表，未创建新证明、公理或生产构建结果。[探针源码](evidence/BoundaryInterfaces.lean) 与 [294 行日志](evidence/boundary-interfaces.log) 同目录提供；日志的公理检查说明固定背景仍继承登记的 `sorryAx`，不能把接口成功打印当作全依赖链已经完成。

[源码哈希与登记责任摘录](evidence/source-review.json) 记录本次核对的 16 个文件。源类型核对包括 `ModelData`/`Model` 的**全部字段**，不只是名称检索；也逐一读取了 `HomologyShortExact`、`FirstQuotientComparison`、`E2Comparison`、normalized triangle 和有限商横行的完整结论。全库关于 comodule/coaction/Ext connecting 的检索只有现有 sphere Milnor 实现及本次目标的说明，没有现成一般对象表示。

既有 `sourceRecognition`、`classical_canonicalIso`、sphere Milnor 坐标/比较、first-quotient shift 等责任仍按原许可表存在，可按仓库规则调用。它们的类型都没有把一般 `H_*X` 变成余模或给出这条 SES 的 Ext δ。当前 `bhs_bockstein` 的登记也只是其已有有限 lift/微分含义。**没有发现可直接调用、类型已经准确覆盖本桥接而只需补本地组合的登记目标。**

证据局限：本报告没有构造缺失余模与派生比较，没有证明它们不能由更深入的上游构造导出，也没有给出实际谱或 `Standard.model` 反例。结论严格是“现有已检查表示不足以完成当前直接绑定”，不是逻辑不可证明性。尤其不能把尚未找到桥接写成已证伪，也不能给 5.49 留 `sorry` 后称满足“只有证伪可留洞”。

依赖审查：本探针不调用原文 5.10 的错误 iff、旧 GL/MH law、5.49 自身或新合成包装来证明边界识别；没有从未证目标或不一致假设导出 `False`。本报告中的接口缺口判定依据类型内容与源码范围，不是调用带 `sorryAx` 的结果导出的数学否定。

### 2026-10-21：同一旋转三角的底层群短正合补证

本次新增独立复核者为 `/root/ext_ses_report_update`，未参与候选发现或实现；原报告者 `/root/ext_interface_report` 的原始探针和证据快照保持不变。复核对象是新增生产文件 [HomologySES.lean](../../../../KIP126/ProofTools/ExtBoundaryComparison/HomologySES.lean)，SHA-256 为 `d9e0b3d402301d5581ac9373ecaf26b147df2e96b044882a4541cd3d83ebf61d`。该文件使用 `module`，所有数学声明均为私有。其完成根的完整源类型为：

```lean
private theorem positive_normalized_rotated_homology_short_exact
    (T : TriangleData model.auxiliary)
    (hf : normalizedExponent model.classicalTower T.f = 1) :
    HomologyShortExact model.coefficients
      (Triangle.mk T.f T.g T.h).rotate
```

命名空间为 `KIP126.ProofTools.Internal.ExtBoundaryComparison.HomologySES`；固定对象仍是原 `Standard.model`，kernel 无自由宇宙参数。`T.distinguished` 是原三角数据的字段；除此以外只有显示的 `hf`，没有增加 `H_*f=0`、短正合性、`e_g/e_h` 或 normalized synthetic compatibility 作为调用者前提。内部先由已登记 `factorization_filtration_iff` 得到长度一的同调零因子分解，从而证明同一实际 `f` 在同一 HF₂ 同调上为零；再将同一实际 distinguished triangle 与 HF₂ 张量，通过标准 tensor--suspension 同构转到旋转后的 `Y → Z → ΣX`。单射性和中间正合性来自该张量三角的长正合列；满射性用其旋转第三箭头 `-Σ(HF₂ ⊗ f)` 为零。负号在证明中显式保留，并非借“模二所以符号无关”跳过。

独立执行以下两项检查均退出 0：

```text
lake env lean -o /tmp/ext-ses-report-independent.olean \
  KIP126/ProofTools/ExtBoundaryComparison/HomologySES.lean
lake env lean -o /tmp/ext-ses-report-probe.olean \
  interface/proposals/ProofTools/20261021-ext-boundary-completion/evidence/HomologySESReview.lean
```

[实际生产模块探针](evidence/HomologySESReview.lean) 以 `import all` 读取实际私有证明体，逐项核验三根类型与宇宙、私有性，以及 6／5／12 个本文件声明的真实证明闭包；无本地公理、直接 `sorry` 或 synthetic sorry，也没有调用其他 ProofTools 结论，故不使用 5.49、合成包装或旧错误 crossing iff 自证。实际输出见 [核验日志](evidence/homology-ses-review.log)，源哈希和执行结果见 [补证元数据](evidence/homology-ses-review.json)。

**这份 2026-10-21 证据的边界没有改变。** 这些根仍继承固定 HF₂、classical tower、closed tensor background、`factorization_filtration_iff` 等已登记上游构造／比较责任，kernel 公理列表仍含 `sorryAx`；当次只证明本地组装步骤没有新增证明洞。群短正合性已完成，但实际 Steenrod 余模结构、这些同一群与映射的余模短正合提升、E₂/Ext 自然比较和 Q₁ 操作等于该 SES 的 Ext δ 在当次核验时均未完成。该核验不证明全信任链闭合、5.49 已证明或已证伪；上游扩展授权来自后述 2026-10-22 用户决定，不来自这份 kernel 检查。

## 方案及精确差异

### A．保留现有接口，建立必要上游识别接口（已获范围授权）

现有 `cofiberFirstQuotientBoundary`、`MahowaldLeibnizFiniteLayerSurjectivity`、`FiniteLayerSurjectivityMahowaldLeibnizStatement` 的签名和定义保持不变。当前 ProofTools 内部证明继续通过公开包装提供；它只证明它实际陈述的命题。

所需上游接口的数学内容按职责分列如下。实现止于支撑本目标的边界，不要求继续形式化这些接口的上游：

1. **AdamsSynthetic**：为同一固定 `coefficients`／选定经典源提供各 `ClassicalObject` 的实际 graded Steenrod 余模、实际映射与悬挂，以及真实 cobar/derived Ext 和到当前 Adams E₂ 的自然比较接口。可只覆盖本项目对象闭包和所需实际序列；必要的源构造或识别可按本次授权精确登记为上游待补责任，不要求先补覆盖所有 synthetic objects 的全局范畴等价。不能把一个新任意线性同构直接称为 source recognition，也不能以任意类型族代替实际余模的 Ext。
2. **Literature**：提供实际第一商／特殊纤维的文献比较接口，将同一归一化 `Q₁` 三角识别为来自该**同一实际同调 SES** 的派生三角，并将其边界识别为相应 Ext δ。比较必须保留 `g,h`、悬挂、weight、符号和 `(1,1)` 分次。可选等价路线是实际 Adams/cobar 短正合复形的连接同态比较，但接口仍须保留该复形计算这些同调余模 Ext 的源关联；文献识别的待补证明单列登记，不向更深层基础扩张任务。
3. **ProofTools**：直接调用已登记的上游边界比较接口，完整证明其与现有有限层满射合成的组合，得到原 `cprime` 条目的经典 Ext 结论并直接绑定；不在本地新增 `sorry`。

待实际类型建立后，核心新定理的**数学目标**精确为：对原 `T,hef,heg,heh,hT,s,t,x`，设 `ε_X, ε_Y` 是已构造、自然且源对象一致的实际 `E₂ ↔ Ext` 比较，则

```text
ε_Y(s+1,t+1)(cofiberFirstQuotientBoundary T hef s t x)
  = δExt(the actual SES of g and h)(ε_X(s,t)(x)).
```

这里 `δExt` 必须由该 SES 在实际余模/派生范畴中构造，不能由左侧定义。该等式的所有对象来自固定源；`ε` 和 `δExt` 不成为合成定理调用者额外提交的参数。本段记录原提案时的精确数学目标，**不是当时已经存在或编译过的 Lean 签名**；2026-10-22 新实施的实际声明见后述实施说明。

这一路线不降低 5.49 的结论、不加新数学前提、不改变现有对象关联；所需最小跨模块接口扩展已于 2026-10-22 获准。原建议“新接口全部来自构造或完整证明、不接受新许可洞”的实施深度按最新人审收窄：仅必要固定源构造与文献比较允许精确登记上游待补责任；无需在本任务中完成其更深层基础。该例外不延伸到 ProofTools 的 5.49 本地证明，也不许可任意未约束的 Ext 替代品。

### B．只公开现有 Q₁ 合成（可继续，但不是完成 5.49）

用户已授权的公开包装现已完成，准确证明 `FiniteLayerSurjectivityMahowaldLeibnizStatement`；同一旋转三角的底层群 SES 也已有内部证明。两者都是完成经典 Ext 版的实质数学步骤，但均不能直接绑定为当前 Ext 陈述的完整证明，不能把 Blueprint 的 `∂_(g,h)` 改名解释为定义出来的第一商操作，以此宣称比较完成。

### 不采纳的捷径

- 新增 `hExt : ∂Q = δExt` 作为 5.49 调用者前提：转移了本应完成的比较责任，改变公开数学命题。
- 由同一核像/长正合性推出两个连接态相等：仅 exactness 不唯一确定连接态，更不识别实际同调余模的扩张类。
- 把 sphere Milnor 比较无条件用于 ν-cofiber/detector：超出完整类型的对象范围。
- 以 `def δExt := cofiberFirstQuotientBoundary` 代替派生构造：循环命名，没有证明与同一 SES 的关联。
- 将整个 5.49、带有 Surj／两条微分的合成结果或无源关联的一般 Ext 比较登记为新 `sorry`：仍不在授权范围内。2026-10-22 批准的例外只涵盖本目标必要、完整陈述并精确登记的上游源构造与文献比较责任；不得冒充已完成的局部证明。

## 下游影响

| 范围 | 影响 |
| --- | --- |
| 既有 ProofTools 三个公开定义及其普通消费者 | 保持类型、前提、语义和对象关联；不要求重接现有调用。 |
| Blueprint `sem:ProofTools:cprime` | 在源对象、真实 Ext 边界及比较接口建立并完成本地推导后直接绑定；范围已获准不等于条目已经完成，也不代表上游传递待补消失。 |
| Blueprint `sem:ProofTools:cprime-model` | 已证固定模型命题已有公开证明绑定；不冒充经典 Ext 比较证明。 |
| Blueprint 5.34/5.47/5.48/5.50、最后层比较、ν 数值补证 | 不受影响，继续按已有授权实施。PDF/NC 版采用指定第一商操作，不另声称本 Ext 识别。 |
| AdamsSynthetic、Literature 的 public 锁与消费者 | 按最小授权实施后登记新增对象／比较接口；完整类型、宇宙、公理依赖、实际待补状态及导出集合需重新捕获与检查，既有接口不改。 |
| E2Computation 独立计算数据、AdamsCalculations、Main、Geometry | 本方案不迁移其责任或修改现有接口。后续经典 Ext 版可供调用，但本报告不宣称现有调用已需要它。 |
| 待补清单与信任检查 | 现有上游许可责任保持；本次必要源构造及文献比较的新增待补逐项按实际状态登记，ProofTools 的 5.49 本地证明不新增洞。不通过重刷锁隐瞒新增责任，明确传递信任边界。 |

实施后的验证包括实际普通公共消费、对象/次数/自然性及边界方块核对、接口锁/待补责任审计、`python3 scripts/check-source-inventory.py`、`lake build` 和 Blueprint 原生同步。该计划不新增网页门禁，不把网页颜色当编译证据。

## 实施范围与未完成边界

截至本次授权回写，**5.49 从实际 Q₁ 输出到经典 Ext 连接态输出的完整形式化与直接绑定**仍是实施目标，不能因获得授权而标为完成。已证明的核心、两判据、PDF/NC 合成或其公开包装不受影响。当前没有该 Ext 比较的反例，不能把该范围标成“已证伪，因此可留洞”。

2026-10-21 未获跨模块授权时，工作限于保留接口的内部证明路线与精确表示需求整理；当时不能擅自修改 AdamsSynthetic/Literature 或新增上游待补责任。2026-10-22 用户已改变这一授权状态：现在可实施上述最小接口并登记必要责任，不再等待同一范围的重复批准；也不扩展到其上游基础或其他数学模块。

此前已在保接口范围内补齐底层群 SES 并核验。该私有辅助结论不新增公共接口，不单独生成 Blueprint 绑定；它的完成情况与本次新授权分别记录，不相互冒充。

## 人类审核记录

**2026-10-22，用户明确回复：**

> 是的我同意,注意对上游接口做尽可能小的改动,也不要去形式化上游接口的上游接口,只需要建立足以支撑我们 5.49 结论的上游接口就行

本次决定明确批准本报告请求的 AdamsSynthetic／Literature 最小范围扩展，并将实施深度限定为支撑 5.49 的必要上游接口。既有接口保持不变；可精确登记必要源构造／文献比较的上游待补责任，直接调用后完成 5.49 无本地证明洞的推导，不再递归形式化这些接口的上游。来源、数学对象和比较方块不得弱化，新增接口的真实信任依赖仍须展示。

这一决定取代原建议方案中“本任务先完成全部新上游构造和证明、绝不新增上游待补责任”的实施深度要求，不改变报告保留的历史核验结论、原 5.49 数学陈述或证据等级。授权回写不表示任何具体候选已经实施、编译或验收，也不确认未实施接口的数量。此前针对其他条目的授权仍不自动扩展到本次最小范围之外。

## 2026-10-22：最小接口实施与独立源码复核

本节由 `/root/ext_authorization_scope` 独立复核协调者新写的 `Standard.Ext`、`Literature.Standard.ExtBoundary` 和 ProofTools 合成包装，并阅读另一 agent 实现的内部 Milnor 余模／派生 Ext 源码；复核者未参与这些 Lean 实现。这里的证据等级为**实际完整源码、已有源文件差异和已完成上游构建日志阅读**，尚未对新的本地合成证明独立运行 kernel 探针，不能将源码阅读写成完整构建或全信任链核验。

### 实际源对象与连接同态

- [SteenrodComodules.lean](../../../../KIP126/AdamsSynthetic/Internal/SteenrodComodules.lean#L24) 明确使用 `MvPolynomial ℕ (ZMod 2)`、Milnor 次数和余乘法、余单位，定义具有有限齐次分解、真实余作用及保次数余模映射的范畴；定义中没有 Adams 页或 synthetic 商。`IntExt` 使用 mathlib 在拟同构处局部化的 `SmallShiftedHom`，对所有整数上同调次数定义；非负次数与 mathlib `Ext` 定义相同，并未把负数通过 `Int.toNat` 改成零次 Ext。[`IntExt.sesBoundary`](../../../../KIP126/AdamsSynthetic/Internal/SteenrodComodules.lean#L195) 是与**所给同一短正合列的 `ShortExact.extClass`** 的派生复合，定义不调用 Q₁ 操作。
- [Standard/Ext.lean](../../../../KIP126/AdamsSynthetic/Standard/Ext.lean#L60) 的 `HomologyComoduleSource` 把各度余模与同一 `ModTwoHomology coefficients` 及实际谱映射相连；它还固定同一 HF₂ 的乘法／单位、Milnor cooperation、Kunneth 外乘积及由插入单位诱导的谱余作用。其上游待构造责任因此带有实际数学源约束，不是任意类型族或任意向量空间同构。
- [实际 `ClassicalExt` 与 Adams 坐标](../../../../KIP126/AdamsSynthetic/Standard/Ext.lean#L116) 使用同一同调余模和同一悬挂球面的派生 Ext；`AdamsExtComparison` 的完整类型保留实际映射自然性及 classical suspension/desuspension 的关系。[`cofiberHomologyShortComplex`](../../../../KIP126/AdamsSynthetic/Standard/Ext.lean#L155) 的两箭头是 `homologyComodule.map T.g` 与 `homologyComodule.map T.h`，零复合来自同一 `T.distinguished`。[`cofiberExtBoundary`](../../../../KIP126/AdamsSynthetic/Standard/Ext.lean#L172) 将该短正合列的真实派生连接态运回固定 E₂ 坐标；没有用左侧 Q₁ 操作来定义它。
- [Literature 的比较定理](../../../../KIP126/Literature/Standard/ExtBoundary.lean#L24) 保留同一 `T`、三个实际规范化指数、`NormalizedTriangleCompatible`、同一旋转同调短正合性、任意 `s,t : ℤ` 和实际输入类；左侧写出原第一商操作，右侧为上述独立派生定义。其类型没有 `R,K`、Surj、两条 Adams 微分或合成结论，也没有让下游调用者另交一个比较等式。来源定位为 BHS Theorem 9.12(5)、Corollary 9.13 及 Pstrągowski Lemma 4.29、Theorem 4.54、Lemma 4.56；固定源的这一比较本身如实保留为上游文献证明责任。

### 精确的新增上游待补边界

截至本次源码复核，新增源文件共有以下 **5 个直接 `sorry` 责任**，恰为本次批准的最小上游边界；内部 Milnor 余模／派生 Ext 文件和 ProofTools 新合成包装源码均没有直接 `sorry` 或新增 `axiom`。

| 稳定源声明名 | 源模块 | 登记类别 | 完整责任的数学范围 |
| --- | --- | --- | --- |
| `KIP126.AdamsSynthetic.Standard.canonicalComoduleAbelian`（private） | `KIP126.AdamsSynthetic.Standard.Ext` | `pending-construction` | 实际 graded Milnor 余模范畴的 abelian 结构，且其底层 preadditive 结构等于已经构造的那个结构。 |
| `KIP126.AdamsSynthetic.Standard.canonicalHomologyComoduleSource`（private） | `KIP126.AdamsSynthetic.Standard.Ext` | `pending-construction` | 同一 HF₂ 同调、实际谱映射、乘法／单位、Milnor cooperation、Kunneth 及谱余作用的源识别，全部约束保留在 `HomologyComoduleSource` 类型中。 |
| `KIP126.AdamsSynthetic.Standard.canonicalAdamsExtComparison`（private） | `KIP126.AdamsSynthetic.Standard.Ext` | `pending-construction` | 选定对象族在全部整数 `(s,t)` 的 Adams E₂／真实派生 Ext 加法同构，带实际映射自然性和规定的悬挂比较。 |
| `KIP126.AdamsSynthetic.Standard.cofiberHomologyShortComplex_shortExact` | `KIP126.AdamsSynthetic.Standard.Ext` | `pending-proof` | 将同一旋转三角已知的逐度 HF₂ 同调短正合性提升为上述实际余模短复形的短正合性；不包含合成推导。 |
| `KIP126.Literature.Standard.firstQuotient_ext_boundary` | `KIP126.Literature.Standard.ExtBoundary` | `pending-proof` | 同一实际规范化三角的 Q₁ 操作与同一同调余模短正合列 Ext 连接态的文献比较；不包含任何有限层合成假设。 |

此前已登记的 **199 项**构造／证明责任应原样保留，以上五项作为明确增量登记，不移除、重分类或改写旧责任以抵消新数量。正式接口与待补清单需在当前源状态下重新捕获并核验；本节的五项是按实际完整源声明和直接 `sorry` 核对的责任范围，不是仅凭类型名称或网页颜色作出的判断。上游四项加一项的边界不转入 ProofTools 的本地证明责任，也不能据此宣称这些上游基础已完成。

### 5.49 本地推导与 Blueprint 对应

[`finiteLayerSurjectivityMahowaldLeibnizExt`](../../../../KIP126/ProofTools/ExtBoundaryComparison.lean#L345) 的类型保留原 `T`、规范化指数、兼容性、`R,K ≥ 2`、全部整数次数、实际 `x,z,v`、两个 cycle 资格、两条实际 differential 和全部有限层 Surj 条件。结论为

```text
∃ hH : HomologyShortExact coefficients (Triangle.mk T.f T.g T.h).rotate,
  the actual class cofiberExtBoundary T hH s t x has the prescribed
  cycle qualification and d_(R+K-1) with target v.
```

这里的 `∃ hH` 在**结论中**，不是新增调用者输入。证明体先由既有 `positive_normalized_rotated_homology_short_exact T hf` 构造同一实际 `hH`，再调用已有完整固定模型满射合成和新增上游 `firstQuotient_ext_boundary`，最后以该等式改写输出；源码没有额外结果包、比较等式假设或本地证明洞。

原 `cofiberFirstQuotientBoundary`、`MahowaldLeibnizFiniteLayerSurjectivity`、`FiniteLayerSurjectivityMahowaldLeibnizStatement` 及 [5.52 的既有公开包装](../../../../KIP126/ProofTools/BlueprintTheorems.lean#L693) 的签名和定义保持不变。本次源码采用新增对象／比较与新增 Ext 输出定理，未将 5.52 原 Q₁ 结论改名成 Ext 版本；所有既有公开类型的最终捕获对照仍属实施验证步骤。

Blueprint 的数学对象和依赖分别落在：

- AdamsSynthetic 的 [`sem:AdamsSynthetic:coefficient-ext`](../../../../blueprint/chapters/AdamsSynthetic.tex#L260) 与 [`sem:AdamsSynthetic:homology-ext-boundary`](../../../../blueprint/chapters/AdamsSynthetic.tex#L324)，说明实际余模、派生 Ext、同一 SES 连接态及其上游待补责任。
- Literature 的 [`sem:Literature:first-quotient-ext-boundary`](../../../../blueprint/chapters/Literature.tex#L860)，陈述同一规范化三角的比较及精确文献来源，绑定本模块比较定理；数学证明说明不冒充其底层源实现。
- ProofTools 的 [`sem:ProofTools:cprime`](../../../../blueprint/chapters/ProofTools.tex#L2107)，保留原 Ext 合成数学命题，新增绑定 `finiteLayerSurjectivityMahowaldLeibnizExt`，证明通过上述原生数学条目引用连接上游；注释明确继承的五项上游责任。绑定源码已经写入不表示最终接口锁捕获、完整构建和原生导出已经通过。

### 本次已查证据与尚待验证

协调者的上游目标构建日志 `/tmp/minimal-ext-target-build.log`（本地证据）显示 `KIP126.AdamsSynthetic.Standard.Ext`、`KIP126.Literature.Standard.ExtBoundary` 已构建，并以 `Build completed successfully (2768 jobs)` 结束；日志同时如实显示上述上游 `sorry`。协调者另报告 `/tmp/StandardExt-final.log` 的单文件复核退出 0。本复核没有以这些结果证明新合成定理已经编译：回写时协调者仍在运行 `/tmp/ext-549-proof-build.log` 所记录的 ProofTools 目标构建，尚未给出其终态。

本节不宣称已通过新的本地合成 kernel 审计、全部公共接口锁／待补清单对照、全量 `lake build`、Blueprint 检查或网页同步；这些步骤仍须以实际结果补记。状态因此保持 `approved-interface-change`，不升级为已实施并验证。原有历史证据和 199 项待补记录不由这次源码实施说明替换。

## 2026-10-22：实施验证结果

本节由实施协调者 `/root` 记录实际命令结果，区别于上一节的独立源码复核。上节描述的是其回写时尚未完成的验证状态；现在已完成以下检查。

- `lake build KIP126.ProofTools.ExtBoundaryComparison` 成功，3347 个构建任务。最终普通公共导入探针 [ExtComposition.lean](evidence/ExtComposition.lean) 与 [kernel 输出](evidence/ext-composition.log) 核验真实对象、边界定义、比较定理与完整 5.49 类型；公理输出如实包含继承的 `sorryAx`。
- 全仓信任捕获覆盖 25306 个项目声明。原 199 项待补的名称、源模块、类型、证明体指纹及类别逐项不变；新增恰为上表的五项，没有新增项目公理或 synthetic elaboration sorry。待补总数为 204，其中新增三项构造、两项证明，ProofTools 仍仅有原 crossing iff 一项直接责任。
- 新增显式公开声明为 AdamsSynthetic 十一项、Literature 一项和 ProofTools 的 Ext 输出定理一项，另有 Lean 自动生成的必要导出。按编译捕获更新三个模块的接口锁；更新前 AdamsSynthetic 的 1787 项、Literature 的 841 项和 ProofTools 的 346 项完整导出，其名称、类型指纹、宇宙参数与公理列表全部逐行保持。
- 完整 `lake build` 成功，3716 个构建任务。AdamsSynthetic、Literature、ProofTools、Main 及消费者信任审计全部通过；ProofTools 的新本地证明没有新增洞，34 项 Main 依赖边界保持，Main 没有本地待补。
- `python3 scripts/check-source-inventory.py` 成功：617 个项目源文件与 35 个消费者／审计文件全部覆盖；49 项 Blueprint 测试全部成功，`git diff --check` 通过。

Blueprint 的悬挂公式已按独立源码复核精确写为实际 Adams 页悬挂后使用悬挂谱的 E₂／Ext 坐标，即调用既有 `suspendedE2ExtEquiv` 的完整标定关系；没有新增另一套 Ext 内部悬挂接口。5.49 及对应上游节点都明确保留五项传递待补边界。原生导出成功，243 个数学条目；Playwright 实际检查 5.49 和三个新增上游条目的公式与 Proof 面板，没有公式错误或运行时异常，并人工查看了 5.49 截图。第五模块的原生局部状态为 54 项 `lean_ok`、9 项 `empty`、1 项 `sorry`，其中 5.49 为 `lean_ok`；这些网站状态不代替上述编译检查或五项上游责任的证明。

本次止于获准的最小上游接口，没有继续构造这些接口的上游基础，也没有将比较等式、短正合性或结果包加为 5.49 调用者前提。`lake-manifest.json` 保持不变；独立的 `meeting/2026-10-13.yaml` 用户改动保持原字节。没有执行提交、推送或远程合并。
