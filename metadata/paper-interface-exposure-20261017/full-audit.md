# AimPaper 公共接口核对现状

AimPaper/main.tex 的全部未注释 theorem/lemma/definition/corollary/proposition/fact 环境；112.tex 仅含图，没有这些环境。别名不重复计数。

按论文出现次数计数；定理 1.4 与 7.1 是同一结论的两次出现。

本表按原审计逐条更新，公共名称均与当前六模块 API 锁交叉核对。具体声明、源位置及论文原文见 [full-audit.json](full-audit.json)，本轮证明与验证见 [report.md](report.md)。

| 状态 | 数量 |
| --- | ---: |
| 原有公共主干对应 | 24 |
| 本轮补齐并公开 | 7 |
| 部分对应／条件或范围不同 | 9 |
| 相关内部步骤，尚未补齐 | 3 |
| 用户暂缓 | 1 |
| 未见对应公共结果 | 11 |
| 当前形式化终点之外 | 2 |
| 合计 | **57** |

公共对应合计 **31** 项。这个数字不表示 31 项论文一般范围的全部内容均已完成无待补证明。

- 公共对应不等于论文一般范围的全部覆盖，也不等于已消除既有上游待补责任。
- 原有公共 24 项只表示所选模型的公共主干；3.6 等受 ClassicalObject 范围限制，3.17 的任意 lift 比较仅模 λ-torsion，6.11 保留指数二条件，6.1 仍有登记直接待补。
- 本轮新增七项局部证明完成，但仍可能依赖已登记上游待补；2.10 的代表版本不补齐定义 2.1 的一般 ESS 构造。
- 未见公共结果表示未找到对应公共陈述，不表示数学上不能由其他结果推出。

## 原有公共主干对应（24）

| 论文条目 | 当前对应与限制 | 公共名称 |
| --- | --- | --- |
| 定理 1.4 | 与定理 7.1 是同一目标；接口还保留共同 Z∞ 代表及非零 E∞ 像。 | `KIP126.Main.h6_sq_permanent` |
| 命题 3.1 | 保留完整 HF2 同调短正合与同一 ν 余纤维三角的双向条件，范围为该模型的经典范畴。 | `KIP126.Literature.Standard.nu_cofiber`<br>`KIP126.Literature.NuCofiberCriterion` |
| 定理 3.6 | 以坐标、free-λ 范围和微分刚性拆分公开；对象范围是项目 ClassicalObject 闭包，非所有任意外部谱。 | `KIP126.Literature.Standard.nuPage_e2`<br>`KIP126.Literature.Standard.free_component`<br>`KIP126.Literature.Standard.free_e2`<br>`KIP126.Literature.Standard.free_lambda`<br>`KIP126.Literature.Standard.free_differential`<br>`KIP126.Literature.Standard.bhs_differentials` |
| 定理 3.8 | 首商与经典标签、有限 lift 和 Bockstein 微分的公共对应；保留所选对象及实际比较条件。 | `KIP126.Literature.Standard.bhs_finite_lift`<br>`KIP126.Literature.Standard.bhs_bockstein`<br>`KIP126.Literature.Standard.bhs_differentials` |
| 命题 3.11 | 所选 ClassicalObject 上实际 cycle/boundary 商的 E∞ 公式和标签。 | `KIP126.Literature.Standard.eInfinity_nu`<br>`KIP126.Literature.Standard.eInfinity_nu_labels` |
| 命题 3.12 | 有限 λ 商的 E∞ 窗口公式及有效范围公开。 | `KIP126.Literature.Standard.eInfinity_finite`<br>`KIP126.Literature.Standard.eInfinity_finite_labels` |
| 命题 3.16 | 同一经典映射和实际 tower filtration bound 给出 λ^k 分解。 | `KIP126.Literature.Standard.lift`<br>`KIP126.Literature.SyntheticFullLift`<br>`KIP126.Literature.SyntheticLiftComparison` |
| 命题 3.17 | 保留正 filtration 与完整短正合，给出同一 connecting arrow 的分解及三角性；任意 full lift 的比较只模 λ-torsion。 | `KIP126.Literature.Standard.triangle_lift`<br>`KIP126.Literature.SyntheticTriangleLiftComparison` |
| 定义 4.14 | 经典微分 crossing 的论文方向和有效页范围已公开；与 Moss crossing 分开。 | `KIP126.ProofTools.HasCrossingOn`<br>`KIP126.ProofTools.NoCrossingOn` |
| 定义 5.4 | 有限/无限页 extension 与实际 normalized map、cycle 标签、次数及见证关联。 | `KIP126.Kervaire.Route.FiniteExtension`<br>`KIP126.Kervaire.Route.FiniteExtensionWitness`<br>`KIP126.Kervaire.Route.InfiniteExtension`<br>`KIP126.Kervaire.Route.InfiniteExtensionWitness` |
| 定义 5.9 | 有限/无限 extension crossing 语言公开。 | `KIP126.ProofTools.FiniteHasCrossing`<br>`KIP126.ProofTools.FiniteNoCrossing`<br>`KIP126.ProofTools.InfiniteHasCrossing`<br>`KIP126.ProofTools.InfiniteNoCrossing` |
| 定理 6.1 | 公共命题与可调用定理均有；保留无交叉、次数和页范围，当前 API 标记有直接待补证明。 | `KIP126.ProofTools.GeneralizedLeibnizLaw`<br>`KIP126.ProofTools.Standard.generalizedLeibniz` |
| 引理 6.11 | May pushpull 图及 signed boundary 的结构化公共交付；去符号仍保留指数二条件。 | `KIP126.Literature.Standard.may_pushpull`<br>`KIP126.Literature.Standard.may_signed_boundary`<br>`KIP126.Literature.Route.MayPushpullData` |
| 定理 7.1 | 与 1.4 相同公共结论；按出现次数计两条。 | `KIP126.Main.h6_sq_permanent` |
| 定理 7.3 | Literature 固定 θ5 的 BX 判据；Main 任意 ThetaChoice 版本含所有自然数 r，r=0 单独处理。 | `KIP126.Literature.Standard.bx_finite`<br>`KIP126.Literature.Standard.bx_untruncated`<br>`KIP126.Main.any_choice_criterion` |
| Fact 7.6 | 四条 Fact 条件分拆公开：W 有限存活、T 的 cycle 和允许 incoming、U 存活、高滤过限制。 | `KIP126.Computation.Standard.w_to_e6`<br>`KIP126.Computation.Standard.t_permanent_cycle`<br>`KIP126.Computation.Standard.t_only_incoming`<br>`KIP126.Computation.Standard.u_permanent`<br>`KIP126.Computation.Standard.high_e5` |
| 命题 7.8 | 标准 h6 平方非零存活/D12 二分及 C3/C4/C5 等价公开。 | `KIP126.Main.h6_square_differential_dichotomy_and_criterion` |
| 命题 7.9 | C3 推出非 C5 的公共结论。 | `KIP126.Main.eta_extension_excluded_of_d6_vanishes` |
| 引理 7.10 | C4 的存在选择与所有 θ5 选择的检测条件等价。 | `KIP126.Main.theta5_square_nonzero_detection_choice_equivalence` |
| 引理 7.11 | C5 的存在选择与所有 U 代表的检测条件等价。 | `KIP126.Main.eta_extension_detection_choice_equivalence` |
| Fact 7.13 | V 的 E12 存活、无 incoming 与指定非零 d2 公开。 | `KIP126.Computation.Standard.v_to_e12`<br>`KIP126.Computation.Standard.v_not_hit`<br>`KIP126.Computation.Standard.d2_x125_8` |
| Fact 7.15 | Y 的 E5 存活及排除 incoming 公开。 | `KIP126.Computation.Standard.y_to_e5`<br>`KIP126.Computation.Standard.y_not_hit` |
| Fact 7.19 | X 的 E6 存活及排除 incoming 公开。 | `KIP126.Computation.Standard.x_to_e6`<br>`KIP126.Computation.Standard.x_not_hit` |
| Fact 7.21 | P=h6Md0 与 Q=h5x91,11 的非零永久存活公开。 | `KIP126.Computation.Standard.p_permanent`<br>`KIP126.Computation.Standard.q_permanent` |

## 本轮补齐并公开（7）

| 论文条目 | 当前对应与限制 | 公共名称 |
| --- | --- | --- |
| 命题 2.10 | 已公开任意滤过阿贝尔群的完整代表等价式及三个分款，另有同一 synthetic map 的 E∞ 包装；不据此宣称一般经典 f-ESS 构造（定义 2.1）也已补齐。 | `KIP126.ProofTools.Paper.filtered_extension_noCrossingRange_iff`<br>`KIP126.ProofTools.Paper.filtered_extension_noCrossing_iff`<br>`KIP126.ProofTools.Paper.filtered_zero_extension_noCrossing_iff`<br>`KIP126.ProofTools.Paper.filtered_extension_noCrossing_of_filtration_bound` |
| 命题 4.2 | 同一实际 λ、ρ 的有限与无限商版本：排除正长度 essential 扩张、实际 d₀ 方程及无 crossing。 | `KIP126.ProofTools.Paper.lambda_rho_extension_collapse_finite`<br>`KIP126.ProofTools.Paper.lambda_rho_extension_collapse_infinite` |
| 命题 4.6 | 两种微分长度范围，有限与绝对 δ-extension 的全部四个分支。 | `KIP126.ProofTools.Paper.syntheticDeltaExtension_prop46_above_absolute`<br>`KIP126.ProofTools.Paper.syntheticDeltaExtension_prop46_below_absolute`<br>`KIP126.ProofTools.Paper.syntheticDeltaExtension_prop46_above_finite`<br>`KIP126.ProofTools.Paper.syntheticDeltaExtension_prop46_below_finite` |
| 推论 4.10 | 完整有效权重、a=n 零端点及源靶超出 strip 的消失情形。 | `KIP126.ProofTools.Paper.syntheticDeltaExtension_absolute`<br>`KIP126.ProofTools.Paper.syntheticDeltaExtension_finite`<br>`KIP126.ProofTools.Paper.syntheticDeltaSource_vanishes`<br>`KIP126.ProofTools.Paper.syntheticDeltaFiniteTarget_vanishes` |
| 命题 4.16 | 2≤page≤r 全范围内经典 crossing 与实际 δ ESS crossing 的双向等价。 | `KIP126.ProofTools.Paper.classical_crossing_iff_delta_crossing` |
| 引理 7.14 | 已公开同一 Q11 类、Q9 像、每个 U 代表的两个修正关系及精确 h₀ 消灭关系。 | `KIP126.Main.Paper.lemma_x1239` |
| 引理 7.20 | 已公开同一 Q9 中两个规定类的非零检测及规范化 ν 的精确方程，量词为存在代表。 | `KIP126.Main.Paper.lemma_nuext125` |

## 部分对应／条件或范围不同（9）

| 论文条目 | 当前对应与限制 | 公共名称 |
| --- | --- | --- |
| 定义 2.1 | 有同一 filtered map 的 ESS 构造，但要求源、靶滤过 IsBounded；没有正文任意经典 f 的专门 ESS 入口及其完整 abutment 对应。 | `KIP126.Core.SpectralSequence.FilteredMapExtension.sequence`<br>`KIP126.Core.SpectralSequence.FilteredMapExtension.differentialRelation_iff` |
| 定义 2.3 | 扩张与 essential 的公共语言已具备；与实际 ESS 微分的桥接保留 boundedness/projectivity，ConvergentMap 专用于 synthetic family。 | `KIP126.Core.SpectralSequence.FilteredMapExtension.Relation`<br>`KIP126.Core.SpectralSequence.FilteredMapExtension.Essential`<br>`KIP126.AdamsSynthetic.ConvergentMap.ExtensionEquation`<br>`KIP126.AdamsSynthetic.ConvergentMap.EssentialExtension` |
| 命题 2.5 | 代表存在性、同长度目标不定性及高滤过修正有公共部件；未见全文各项的公共总定理，尤其不同长度 m>n 的分支及 essential 较短微分见证。 | `KIP126.AdamsSynthetic.ConvergentMap.extensionEquation_iff`<br>`KIP126.Core.SpectralSequence.FilteredMapExtension.mem_indeterminacy_iff`<br>`KIP126.Core.SpectralSequence.FilteredMapExtension.Relation.mem_targetCoset_iff`<br>`KIP126.Core.SpectralSequence.FilteredMapExtension.essential_iff` |
| 定义 2.7 | 本轮已公开任意滤过阈值的代表语言 FilteredNoCrossingRange、ExtensionNoCrossingRange；与一般经典 f-ESS 的 DifferentialDatum／HasCrossingAt 及其比较尚未统一形成完整公共桥接，因此仍列部分对应。 | `KIP126.Core.SpectralSequence.FilteredMapTransport.NoCrossing`<br>`KIP126.ProofTools.Paper.FilteredNoCrossingRange`<br>`KIP126.ProofTools.Paper.ExtensionNoCrossingRange` |
| 定义 3.2 | 双分次球有公共对象；Smn 以 biShift 的单位定义。正文任意整数 w 的 Σ^(s-w)ν(S^w) 对应不是一个直接导出的统一等式/同构定理。 | `KIP126.Synthetic.Context.Smn`<br>`KIP126.Literature.nuSphereOne`<br>`KIP126.Literature.nuSphereTwo`<br>`KIP126.Literature.nuSphereThree` |
| 定义 3.3 | λ 自然变换是 SyntheticCategory.lam 字段，商对象公开；正文由 ν 的比较映射得到 λ、及 X/λ≃(S/λ)∧X 的整段语义未以完整公共比较定理交付。 | `KIP126.Synthetic.Context.SyntheticCategory`<br>`KIP126.Synthetic.Context.lambdaPow`<br>`KIP126.Synthetic.Context.XModLambda`<br>`KIP126.Synthetic.Context.XModLambdaN` |
| 命题 3.20 | 可构造 normalized triangle，且可获得 normalized first-arrow 的 cofiber 比较；没有仅由指数和等于一即推出指定三个 normalized arrows 形成 distinguished triangle 的一般公共定理。NormalizedTriangleCompatible 是命题/条件，不能算已交付该结论。 | `KIP126.Literature.Standard.normalizedTriangle`<br>`KIP126.Literature.NormalizedTriangleCompatible`<br>`KIP126.Literature.Standard.normalized_cofiber` |
| 定理 6.12 | 存在公共 Mahowald 定理，但比正文另显式要求 NormalizedTriangleCompatible 及指定 suspendedX 与 x 的 DesuspendsClass。不能在缺少 3.20 一般桥接时算作同前提的完整覆盖；该 theorem 当前还有直接待补。 | `KIP126.ProofTools.GeneralizedMahowaldLaw`<br>`KIP126.ProofTools.Standard.generalizedMahowald` |
| 推论 6.23 | 当前接口只给有限后页，源靶需满足后页 cycle 条件；排除同一早期有限商中非零且不 lift 的所有短扩张，比论文仅排除 essential crossings 更强。正文 r=∞ 的形式也未由此交付。 | `KIP126.ProofTools.FinitePageExtensionStretchingLaw`<br>`KIP126.ProofTools.FiniteExtensionNonliftableCrossing`<br>`KIP126.ProofTools.Standard.finitePageExtensionStretching` |

## 相关内部步骤，尚未补齐（3）

| 论文条目 | 当前对应与限制 | 公共名称 |
| --- | --- | --- |
| 命题 5.10 | 尚缺一般长度下同时除 λ 的源与映像提升；抽象滤过群证据只反驳现有中间推理，不是固定对象反例。 | — |
| 引理 7.16 | 原 Toda 成员非零已有证明；仍缺保持 Toda 关系的 F11 成员与完整不确定性控制，以完成规定检测。 | — |
| 推论 7.18 | 仍缺对任意 Y 检测代表证明 h₀ 消去代表差，不能取消额外 λ 因子。 | — |

## 用户暂缓（1）

| 论文条目 | 当前对应与限制 | 公共名称 |
| --- | --- | --- |
| 命题 6.20 | 用户决定暂时保持不变；页长度域及目标关联问题保留在独立报告，候选修正未接入公共接口。 | — |

## 未见对应公共结果（11）

| 论文条目 | 当前对应与限制 | 公共名称 |
| --- | --- | --- |
| 定理 1.3 | Browder 的几何存在性与 h_j 平方存活的双向定理没有公共接口；Literature 的 theta5 检测结果不能代替该定理。 | — |
| 推论 1.5 | Adams 2-line 所有永久存活元素的完整分类未见公共结论。标准类、个别微分与 h6 平方存活不能代替穷尽分类。 | — |
| 推论 2.6 | 未见 AF(f)=k 推出该 f-ESS 全部 i<k 微分为零的公共定理；action_filtration 是相关支撑而非同一结论。 | — |
| 定理 2.12 | 一般同伦交换正方形的扩张追踪定理未见公共接口；GL/MH 的特定 quotient square 不能替代该一般定理。 | — |
| 推论 2.15 | 交换正方形的无交叉推论未见公共接口。 | — |
| 推论 2.16 | 从同源两边扩张推出第三边扩张的三角图推论未见公共接口。 | — |
| 推论 2.17 | 连续两边扩张与无交叉推出复合扩张的推论未见公共接口。 | — |
| 推论 2.18 | 由 p、q 的首个 ESS 微分诱导 f-ESS 到 g-ESS 态射的公共定理未见；FilteredMapTransport 处理的是已有 filtered-map 同构的输运。 | — |
| 推论 2.19 | g∘f=0 推出 f 扩张目标在 g-ESS 中为永久 cycle 的公共定理未见。 | — |
| 命题 2.20 | 同伦群正合推出全部 g-ESS 永久 cycle 是 f-ESS boundaries 的公共定理未见。 | — |
| 命题 5.14 | 未见 E∞ 页上的 normalized f-extension 下降为经典 f-ESS 扩张的公共定理；两侧现有 extension 定义本身不提供该桥接。 | — |

## 当前形式化终点之外（2）

| 论文条目 | 当前对应与限制 | 公共名称 |
| --- | --- | --- |
| 定理 1.1 | 126 维有 Kervaire 不变量一的带标架流形；当前终点仅为标准 h6 平方非零永久存活。 | — |
| 推论 1.2 | 全部维数分类；没有流形存在性及仅这些维数的公共命题。 | — |
