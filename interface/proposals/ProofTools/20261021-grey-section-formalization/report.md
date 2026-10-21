---
issue_id: ProofTools-20261021-grey-section-formalization
title: 第五模块数学规则及实际数值构造的最小公共包装
summary: 已实施获批十三根与七处数学绑定：A6＋B的p/h0p/6.7定理3＋C3＋D1。完整乘二条目及d0/h0d0另由方案E获批实施；B中局部6.8定理仍未单独公开。既有公共类型及许可洞不变，不做程序算法形式化。
responsibility_module: ProofTools
targets:
  - paper:6.5
  - sem:ProofTools:ss-leibniz-specialization
  - sem:ProofTools:ss-cutoff-square-specialization
  - sem:ProofTools:ss-mahowald-specialization
  - paper:6.8
  - paper:6.19
  - paper:6.24
  - paper:6.7
baseline_commit: f17969a0c7839f7d47d550d5e8f8a0a0aa2ffe91
reporter_agent: /root/grey_interface_report
independent_of_discoverer_and_implementer: true
evidence_level: 独立核对完整目标、固定对象及公共候选；十三根与后续方案 E 已实施，最终全库构建、接口及页面核验通过；本报告不声称既有上游待补已消除。
status: partially-approved
human_decision: "2026-10-21，本对话用户对精确十三根及七处绑定的询问回复：‘批准最小 13 项并绑定’。仅授权本报告推荐13根、必需导出、ProofTools入口／基线增量及7个数学条目绑定；不包含B可选3根、已有类型修改、新公理／证明洞、程序正确性或后续乘二数学结论的新增公共名字。"
---

# 接口审查报告

## 已批准范围与当前结果

用户批准的**最小十三根组合及七处数学绑定已经实施并通过最终核验**；人审原话与边界见末尾记录。后续独立方案 E 的 `d0,h0d0,paper6_8_complete_crossing_warning` 也已另获批准、实施，完整 `paper:6.8` 已直接绑定。两次批准合计 16 个命名根，不包含单独的局部 `paper6_8_classical_d3`。下文 A／B／C／D 的完整候选和其他选择保留为历史审阅依据；其中“十三根范围”指第一次批准当时的精确边界，不是当前数学缺口或等待批准的任务。方案 A 的六个精确声明及其四处绑定如下。完整、可检查的原始候选源码见 [public-wrappers.lean](evidence/public-wrappers.lean)，逐字签名另见 [candidate-signatures.md](evidence/candidate-signatures.md)；生产实施采用下文的十三根精确整包。

| 拟议完整公共名称 | 种类 | 对应数学条目 |
| --- | --- | --- |
| `KIP126.ProofTools.Standard.QuotientBoundaryCutoffStatement` | 命题定义 | cutoff 两个定理的完整结论类型；不单独冒充其他条目的绑定 |
| `KIP126.ProofTools.Standard.cutoffLeibnizSquare` | 定理 | `paper:6.5` |
| `KIP126.ProofTools.Standard.ssCutoffSquareAtLevel` | 定理 | `sem:ProofTools:ss-cutoff-square-specialization` |
| `KIP126.ProofTools.Standard.ssLeibnizAtLevelZero` | 定理 | `sem:ProofTools:ss-leibniz-specialization` |
| `KIP126.ProofTools.Standard.FiniteMahowaldZeroInputStatement` | 命题定义 | Mahowald 特化的完整结论类型；不另外绑定成结论 |
| `KIP126.ProofTools.Standard.ssMahowaldZeroInputLevels` | 定理 | `sem:ProofTools:ss-mahowald-specialization` |

方案 A 的原提案范围是六个新根声明、它们必需且如实生成的导出项、ProofTools 入口与相应接口基线的增量，以及四处直接 Blueprint 绑定。方案 B 的另外六个历史候选、C 的三根和 D 的一根、各自精确成品与数值绑定范围在后文保留；实际批准与实施子集以本节十三根清单及后续方案 E 的交叉记录为准。**不包含**修改现有公共类型、删减前提、改变对象关联、增添公理或 `sorry`、扩大许可证明洞、修改其他模块接口、声明程序正确，或把数值例子弱化成条件定理。

本次任务最初选中的四节有 16 个空绑定条目，完整快照保存在 [targets-at-review-start.json](evidence/targets-at-review-start.json)。协调者随后转达用户收窄范围：仅继续数学命题与证明，不继续程序内部数据结构、递归证书或算法正确性形式化。因此，本方案不为三个程序数据定义和两个程序 soundness 猜想提出公共接口；原有文档及其猜想状态保留。`ml-ss-scope`、`ss-level-implications`、`ss-soundness-boundary` 是来源／逻辑边界说明，不应为了消除灰色而伪造一个数学结论绑定。

## 已实施并核验的十三根组合（第一次批准的范围）

精确整包为 [public-minimal-package.lean](evidence/public-minimal-package.lean)。本报告员独立实际执行无 `-o` 的单文件检查，**exit 0**，完整日志为 [public-minimal-package.log](evidence/public-minimal-package.log)。整包恰好声明下列 13 根，未声明 B 的可选 `d0,h0d0,paper6_8_classical_d3`；实际执行的 13 项 `#check` 与 `#print axioms` 均成功。检查没有修改生产接口或锁。

以下每个名字的完整前缀均为 **`KIP126.ProofTools.Standard.`**：

| 公共根 | 方案 | 获准后的用途 |
| --- | --- | --- |
| `QuotientBoundaryCutoffStatement` | A | cutoff 的完整命题类型；支持定义，不额外绑定成结论 |
| `cutoffLeibnizSquare` | A | `paper:6.5` |
| `ssCutoffSquareAtLevel` | A | `sem:ProofTools:ss-cutoff-square-specialization` |
| `ssLeibnizAtLevelZero` | A | `sem:ProofTools:ss-leibniz-specialization` |
| `FiniteMahowaldZeroInputStatement` | A | 完整 MH 特化命题类型；支持定义 |
| `ssMahowaldZeroInputLevels` | A | `sem:ProofTools:ss-mahowald-specialization` |
| `p` | B 必需子集 | 固定 actual archived 数学标签 |
| `h0p` | B 必需子集 | 指定实际乘积；C/D 公开目标使用同一个标签 |
| `paper6_7_classical_d3` | B 必需子集 | `paper:6.7` 的确定目标经典微分结论 |
| `IsSphereThreeH0H4Square` | C | 固定实际 S³ 源的完整 suspension 关系；支持谓词 |
| `paper6_19_finite_nu_extension` | C | `paper:6.19` 的完整有限 ν 扩展结论 |
| `paper6_24_infinite_nu_extension` | C | `paper:6.24` 的完整无限 ν 扩展结论 |
| `paper6_19_actual_cofiber_d2` | D | `paper:6.19` 的 actual suspension、q/i 页映射、d₂ 与 permanence 存在结论 |

计数为 **A6＋B 必需子集3＋C3＋D1＝13 根**，其中五个是供陈述使用的定义／数学标签，八个是定理。可直接覆盖的原灰色数学条目恰为七个：`paper:6.5`、`paper:6.7`、`paper:6.19`、`paper:6.24` 与三个 SS 数学特化。`paper:6.19` 正文确有有限扩展和 actual cofiber 数据两个结论，因此由 C、D 两个 theorem 分别绑定；不是给同一结论堆绑辅助引理。五个支持定义不冒充额外结论绑定。

**公开依赖闭合已经实际检查。**C 需要 B 的 `p,h0p`，D 需要这两个标签及 C 的 source predicate；B 的 6.7 theorem 已用同一个 `h0p`。所有其他公开类型均沿用已有锁定上游接口。可选三根不被这 13 根的公开类型依赖；已完成的 private 数值事实可照常在证明体使用，不因此产生新的 caller 假设。整包仅调用既有注册上游责任及本轮完成的私有证明，没有为了闭合加入新公理或许可洞。

**第一次十三根批准当时未覆盖的条目：**当时 `paper:6.8` 的完整 warning 尚需严格零像／maximal、两个不同实际 lift 及同一实际 normalized map、stem/weight 下的 crossing 比较，因此十三根包没有为它申请绑定。后续这些数学事实已全部补齐，并由用户另行批准的 [方案 E](../20261021-doubling-complete-warning/report.md) 三根完整实施，`paper:6.8` 现已直接绑定；不是仅用局部非零 d₃ 使整个 warning 变绿。来源／工作边界说明及用户排除的程序内部算法条目维持原文与状态。

这份十三根清单固定了第一次批准的授权范围：ProofTools 的这 13 根与其必需真实生成导出、公共入口／锁的如实增量及上述七处数学条目的直接绑定。下文保留 A/B/C/D 的历史候选差异；B 中 `d0,h0d0` 后来由方案 E 单独获批，局部 `paper6_8_classical_d3` 仍未单独公开，不能把后续批准倒算为十三根批准时的一部分。

## 原接口、背景与问题成因

### 审查起点的完整公共接口（历史基线）

审查起点的 `KIP126.ProofTools` 入口及 `interface/baselines/proof-tools-api.json` 当时不包含上述六个名称。该历史接口基线有 121 个显式声明、95 个生成声明、216 个导出记录。此次不是修改其中某个错误签名，而是在现有完整证明工具之外，为 Blueprint 实际陈述的特化结论提供直接、同模块、可公开消费的名字。

已存在的公共定理是：

```lean
KIP126.ProofTools.Standard.generalizedLeibnizAtLevel
KIP126.ProofTools.Standard.generalizedMahowaldAtLevel
KIP126.ProofTools.Standard.FiniteMahowaldAtLevelStatement
KIP126.ProofTools.Paper.extensionSquare
```

它们的完整源码声明、所需记号和定义体见 [existing-signatures-source-snapshot.md](evidence/existing-signatures-source-snapshot.md)。其中：

- `generalizedLeibnizAtLevel` 在固定 `Standard.model` 中，显式量化 `X,Y,f,page,level,r,m,l,s,t`、四个实际 E₂ 标签、`2≤page≤r`、`e(f)≤m≤page−2+e(f)`、`e(f)≤l`、两个永久标签、实际 Adams 微分、有限与无限扩展，以及实际源边与底边 crossing 条件。
- `generalizedMahowaldAtLevel (T) (he) : FiniteMahowaldAtLevelStatement T he` 的完整命题定义量化同一个实际归一化三角、兼容比较、`n₁,m₁,k,i,j`、`0<n₁`、`j<n₁`、四个经典标签、所有实际 E∞ 检测、三条实际扩展及同权重的 no-crossing 条件；结论包含共同代表 `a,b,c`、所有检测、限制与带负号像等式、改进的 cycle 资格和有限输出关系。
- `Paper.extensionSquare` 是经典四边形定理，保留 cutoff `0<κ≤b+L−M`、底边阈值 no-crossing 和右边长度 `κ−1` 的无 crossing 零扩展。它不能仅凭名字直接充当实际 synthetic quotient-boundary 方块的全部类型与比较。

### 为什么仍需要独立方案

现有公共接口足以在**内部**证明这些数学特化。新文件 `KIP126/ProofTools/SyntheticProgramRules.lean` 正是保留公共接口的实现方案：所有新证明与中间命题均为私有。私有证明可以完成数学工作，但仓库规则不允许把 Blueprint 绑定到私有名字，也不允许把只在证明中调用的一般定理或背景谓词绑定成正文特化结论。

因此，先完成私有证明，再提出六个最小包装，而不是预先改锁或改变原定理。此报告员没有参与私有证明实现；对候选的独立工作限于完整类型展开、对象和前提核对，以及仅位于报告 evidence 中的公开包装可行性检查。

## 真实前提与对象核对

### 1. `paper:6.5` 和 SS cutoff 方块

实际固定模型中，令 `A=Σ^{0,e(f)}νX`、`B=νY`，`F` 为同一个实际归一化映射。对任意自然数 `q`，四个顶点严格是

\[
Q_qA,\quad Q_qB,\quad \Sigma^{1,-q}A,\quad \Sigma^{1,-q}B.
\]

四条边分别是实际 `Q_qF`、两个实际绝对边界和实际 `Σ^{1,−q}F`，不是任意另选的同次数线性映射。边界展开为

```lean
XModLambdaN.proj A q ≫ (Internal.Mahowald.biSuspensionIso q A).inv
```

其中 `A` 是实际 synthetic 对象；公开候选完整写出相应参数，不导出私有 `absoluteBoundary`。

固定同一 stem/weight `p=(a,w)`。四个实际 E∞ 标签在三分次 `(s,a+s,w)`、`(s+M,a+s+M,w)`、`(s+b,a+s+b,w)`、`(s+b+L,a+s+b+L,w)`。完整输入为：

1. `M,b,L≥0`、`0<κ≤b+L−M`；
2. 顶边长度 `M`、左边长度 `b`、底边长度 `L` 的三个实际扩展等式；
3. 顶边或左边无 essential crossing；
4. 底边没有从更高源滤过开始、目标位于 `[s+M+κ,s+b+L]` 的 essential crossing；
5. **同一个右边**长度 `κ−1`、从 `η` 到零的扩展，并且该零扩展无 crossing。

结论严格是右边长度 `D=b+L−M`、从 `η` 到原来指定 `ω` 的扩展，末端 degree transport 显式保留。

这里 essential crossing 以实际 ESS 的完整 shorter-image 不定性定义。候选把私有 `TowerNoCrossing` 与 `EssentialNoCrossingRange` 全部展开为 `∀u v ... ∀source target, ¬TowerEssentialExtension ...`，没有增加公共技术谓词。没有用现有较强的 `ExtensionNoCrossingRange`（要求每条扩展的目标本身为零）替代这个较弱的 essential-crossing 条件。

`ssCutoffSquareAtLevel` 仅取 `q=page+level−1`、`page≥2`；保留所有以上输入与完整输出。指数恒等式及 `D≥2`、`0≤k+M−e<q` 已在私有 `cutoff_boundary_exponents` 证明，属于 classical decoder 的算术步骤，**不能**凭这些算式宣称任意四个标签就是所需 boundary-comparison 标签。该条目的数学输出仍是方块扩展；指定经典微分的解释仍须其正文明确列出的检测比较。

### 2. SS Leibniz 特化

候选固定 `Standard.model`，从原公共定理取 `level=0`，原其余参数对应为 `r=b,m=M,l=L`。完整目标是

\[
d_{b+L-M}(y)=v.
\]

没有删除 `u,v` 的永久资格、`d_bx=u`、`LevelFiniteExtension ... page 0 ... x y`、实际无限扩展、源边 no-crossing 二选一或底边 no-crossing。有限输入商恰为 `Q_{page−1}`，权重恰为 `t+e(f)`。普通页扩展可通过现有 `finiteExtensionAtLevelZero` 提供这一有限输入，但不会因此自动提供 crossing 或永久资格。

这是一条完整数学规则的特化，不是“程序所有成功分支满足这些前提”的证明。本方案不增加后一断言。

### 3. SS Mahowald 特化

候选只把一般完整命题中的两个**输入层**取为 `i=j=0`。仍量化同一个兼容归一化三角及全部比较同构与其 inclusion 方块；保留同一个源标签、同一个最高层目标、三条实际扩展以及源边实际 no-crossing 二选一。

其参数精确变为

\[
A=n_1+k,\quad B=m_1+1,\quad N=A+B=r,\quad
K=k,\quad J=A,\quad Q=N-k,
\]

并保留原命题的全部存在见证 `a,b,c`、六项对应检测、`rho` 等式、带负号的实际像等式、源的 cycle 改进和输出 `LevelFiniteExtension ... (Q+1) k ...`。因此，输出层仍为 `k=l−e(h)`，没有把非零输出层除掉，也没有把 `B_{k+1}`、`B_{r′}` 或 shorter-image 不定性去掉。

这里没有采用“有限层满射”或 PDF 条件代替实际前提。现有 `FiniteLayerSurjectivityMahowaldLeibnizStatement` 与 `MahowaldLeibnizFiniteLayerSurjectivity` 均保持原名、原类型、原对象关联。

## 独立证据与复现

审查起点、原始灰色条目和输入 SHA-256 在 [inputs-at-review-start.json](evidence/inputs-at-review-start.json)。公开包装草稿及其实际检查见 [public-wrappers.lean](evidence/public-wrappers.lean)。

本报告独立核对了四条数学规则的完整 Blueprint 正文、现有公共锁、对应定义体和私有实现的全部结论类型。它没有把网页绿色或接口类型指纹当作数学证明。

独立执行 `lake env lean interface/proposals/ProofTools/20261021-grey-section-formalization/evidence/public-wrappers.lean`，**exit 0**，六项 `#check` 与六项 `#print axioms` 全部成功；完整输出为 [public-wrappers.log](evidence/public-wrappers.log)。该检查实际验证了展开后的 cutoff 命题与私有目标、完整 Mahowald 特化命题与私有目标的定义等同，包含实际 boundary 选择；不是只做名称搜索。六个声明都固定使用当前模型，没有新引入的宇宙参数；六项结果均如实报告现有传递 `sorryAx`。

默认受限环境运行 `lake env lean` 曾因 Lake 安装定位失败而退出；在同一固定 v4.32.2 工具链的许可执行环境重试后成功。首份公开草稿仅 `import all` 私有证明模块，Lean 如实拒绝其公开类型使用私有导入的既有公共名；补充 `public import GeneralizedLeibnizAtLevel`、`public import GeneralizedMahowald.FiniteLevelAssembly` 后通过。这是公开可消费性所需的正常 import 声明，没有增添数学前提或新依赖版本。没有升级工具链、改变依赖或写 `.olean`。

候选只通过 `import all KIP126.ProofTools.SyntheticProgramRules` 在证明体调用已构造的私有结果；公开类型通过既有上游的普通 `public import` 消费，没有导入生产总 facade、修改生产公共入口或写接口锁。两个 public proposition 定义本身不是新增公理；四个 theorem 都有完整证明包装，没有新增许可证明洞。

### 传递依赖与循环审计边界

现有公共锁明确记录 `generalizedLeibnizAtLevel`、`generalizedMahowaldAtLevel` 与其命题定义含传递 `sorryAx`。这来自现有上游构造／比较责任，不能据私有证明完成就声称整个数学基础已无未证依赖。原 `Paper.extensionSquare` 的锁中只有基础逻辑公理；实际 Standard 版本则沿用固定模型的上游构造。

新 wrappers 的直接证明依赖依次是私有 cutoff 证明、原公共任意层 Leibniz、原公共双输入层 Mahowald。后两条没有反过来依赖新 wrapper；私有 cutoff 证明从实际收敛代表和有限滤过修正构造推出右边等式，不调用程序 soundness 猜想，也不假设自身结论。未见本方案引入循环、相关新 `sorry` 或以矛盾消去的路径。完整递归责任清单与全量 `lake build` 已由协调者统一整合并通过最终核验，实际结果见末尾；上述独立单文件证据与后续全量构建证据分别记录。

## 方案及精确差异

### 首先评估的保留原接口方案（历史备选，未采用）

审查时首先评估保持六个结果私有、仅供模块内部审计引用的方案；这样可在不改接口的情况下完成数学补证，但四个 Blueprint 数学条目无法直接绑定这些私有名。用户随后批准并实施了上述公共包装，因此这不是当前待执行方案。来源／工作边界说明继续不伪造数学结论绑定。

### 最小公共方案 A（四个数学规则）

- **原签名：**六个完整公共名称在基线均不存在；原有一般定理完整签名不变，见前述快照。
- **候选签名：**[public-wrappers.lean](evidence/public-wrappers.lean) 中恰好六个 `public` 根声明，无另加公开 crossing、边界、算术引理或代表辅助声明。
- **定义变化：**只加入完整 cutoff 命题类型和完整 `i=j=0` Mahowald 命题类型；定义没有提供事实真假。
- **前提和结论强弱：**Leibniz 与 Mahowald 分别是原定理的 `k=0` 与 `i=j=0` 特化，未弱化前提或扩大结论。cutoff 维持原文建议的阈值范围条件及右边零扩展，实际 quotient 与比较在类型中固定。
- **对象关联：**全部使用当前 `Standard.model`；归一化映射、quotient、实际边界、指定标签、共同代表保持一致，没有换成独立矩阵、自由 ESS 或存在某个目标。
- **替代方案：**不增加公共名，接受私有补证而暂不直接绑定；或把完整命题体直接摊入四个 public theorem，减少两个命题定义。后者显著复制 cutoff/Mahowald 类型且降低可读性，数学强弱不变；不是本次首选。

算法成功条件、程序状态不变量、recursive certificates、两个 soundness 猜想不在方案 A 中，不能作为其隐式输入或输出。

### 最小公共方案 B（四个固定数学标签与两个已证数值结论）

数值私有证明随后完成。本报告员独立读完其完整源码，展开 E₂ 唯一非零目标标定，并独立构造、检查了 [public-numerical-wrappers.lean](evidence/public-numerical-wrappers.lean)。此次没有参与生产数值证明实现。完整私有源码及 SHA-256 见 [numerical-private-source-snapshot.md](evidence/numerical-private-source-snapshot.md)。

| 拟议完整公共名称 | 精确类型／数学内容 | 绑定范围 |
| --- | --- | --- |
| `KIP126.ProofTools.Standard.p` | `model.classical.sphere.Page 2 (4,37)`；固定 archive 第 26 号、记录为 `("p",4,37)` 的 generator 经现有实际 E₂ comparison 的像 | 数学标签；不把标签本身当成某个例子结论 |
| `KIP126.ProofTools.Standard.d0` | `model.classical.sphere.Page 2 (4,18)`；固定 archive 第 8 号、记录为 `("d_0",4,18)` 的 generator 经同一 comparison 的像 | 数学标签 |
| `KIP126.ProofTools.Standard.h0p` | `model.classical.sphere.Page 2 (5,38)`，定义为实际 `product h0 p` | 数学标签 |
| `KIP126.ProofTools.Standard.h0d0` | `model.classical.sphere.Page 2 (5,19)`，定义为实际 `product h0 d0` | 数学标签 |
| `KIP126.ProofTools.Standard.paper6_7_classical_d3` | 下列完整非零微分命题 | 可绑定 `paper:6.7` 的确定目标经典微分结论；不把其原文 synthetic 证明路径也宣称完成 |
| `KIP126.ProofTools.Standard.paper6_8_classical_d3` | 下列完整非零微分命题 | 只记 `paper:6.8` 的局部已证事实；**不绑定整个 crossing warning** |

两个新 theorem 的完整签名为：

```lean
public theorem paper6_7_classical_d3 :
    HasNonzeroDifferential model.classical.sphere 3 (2,36) (5,38)
      (KIP126.Literature.Standard.hiProduct 2 5) h0p

public theorem paper6_8_classical_d3 :
    HasNonzeroDifferential model.classical.sphere 3 (2,17) (5,19)
      (KIP126.Literature.Standard.hiProduct 0 4) h0d0
```

**原签名：**上述六个公共名字在基线均不存在，私有对应及原 Literature 存在性定理的完整签名见证据。**候选精确差异：**只把两个指定 generator 的实际标签、它们与指定标准 `h0` 的实际乘积，以及已经证明的两条确定目标非零 `d₃` 公开；不增添任何新假设。`HasNonzeroDifferential` 比单独的微分等式多断言目标页类非零，该额外断言正来自现有 Literature 输入及实际 E₂ 标定，不是凭 target E₂ 标签非零推出的。

`p,d0` 采用仓库已有的 `@[no_expose] public def` 封装方式：公开类型为实际指定 E₂ 页，定义体调用该固定 private construction；其完整选取公式与第 26／8 号记录在证据快照中，并在独立检查中分别以 `rfl` 核对。这样不把 `pIndex`、`d0Index`、`regradeMonomial`、字表达、坐标唯一性或 Gaussian 算法变成公共接口。`h0p,h0d0` 则公开定义为同一实际乘法。两条 theorem 的 `change` 实际通过了公开标签与原私有确定目标的定义等同性检查。

独立执行：

```sh
lake env lean interface/proposals/ProofTools/20261021-grey-section-formalization/evidence/public-numerical-wrappers.lean
```

**结果：exit 0**；完整输出为 [public-numerical-wrappers.log](evidence/public-numerical-wrappers.log)。该无 `-o` 文件还实际检查：两个 generator 的名字／次数记录；`paper6_7_classical_d3` 推出原 `DifferentialAt` 结论；`paper6_8_classical_d3` 借实际页代表唯一性排除目标零。后两个只是 evidence 内的 `example`，因此无需再增加重复的 `paper6_7_classical` 或 `paper6_8_not_zero` 公共根。六项 `#check` 与 `#print axioms` 也全部成功，均继承已登记上游的 `sorryAx`，没有把源坐标和文献责任误写为已消除。

证明路径是：现有 `coordinates_basis`、`sourceAtom_agrees`、`comparison_product`、`comparison_h0` 把目标唯一基向量识别为实际 `h0p`／`h0d0`；`Fin 1 →₀ ZMod 2` 中非零向量唯一；两个已登记 Literature 输入给出实际**非零页目标**，因此目标不可能是 E₂ 零向量，必为已标定者。没有调用 `paper:6.19`、`paper:6.24`、待证明的无限 `ν` 扩展、程序正确性或新数值结论本身。

**方案 B 的明确范围：**另外六个公共根及其必需生成导出、ProofTools 公共入口与锁的如实增量；`paper:6.7` 的确定目标经典结论可直接绑定。这套独立证明不冒充原文的正向 Leibniz 证明路径：完整 `ν` 无限扩展由下文 C 完成，原文实际 no-crossing 比较仍属该正向路径的独立事项。完整 `paper:6.8` 的后续补证及绑定见方案 E，不能仅用方案 B 的局部经典微分冒充完整 warning。`paper:6.19`、`paper:6.24` 的完整扩展不在方案 B 范围，而由方案 C 提供。

方案 A 与 B 合计十二个新公共根，加上 C 与 D 共十六个。各方案均不改变已存在公共声明，不增加公理或许可证明洞，也不申请把 numerical worker 的所有私有声明批量公开。接口锁必须保留原 121 个显式根与原导出记录的类型／归属，增补项的实际生成导出由实施后的正常检查捕获。

### 最小公共方案 C（真实 S³ 源谓词与两个完整 ν 扩展）

最终私有构造已稳定在源 SHA-256 `246233e95d6a60bf99b56c60416110382f0ebc6e7de72de409a7a961862f1559`，完整源码为 [nu-private-source-snapshot.md](evidence/nu-private-source-snapshot.md)。本报告员独立核对最终三根公开候选 [public-nu-wrappers.lean](evidence/public-nu-wrappers.lean)，实际执行无 `-o` 的单文件 Lean 检查，**exit 0**；完整输出见 [public-nu-wrappers.log](evidence/public-nu-wrappers.log)。因此，现在完成的是两条完整数值扩展结论，不再把它们的实际 full lift 或输出本身列作未完成。

| 拟议完整公共名称 | 种类及精确内容 | 数学绑定范围 |
| --- | --- | --- |
| `KIP126.ProofTools.Standard.IsSphereThreeH0H4Square` | 对实际 `S³` 页类的固定来源谓词，完整三次经典 suspension 与最后的实际 shift comparison 全部内联 | 固定数学标签条件，不另冒充扩展结论 |
| `KIP126.ProofTools.Standard.paper6_19_finite_nu_extension` | 下列完整存在性／有限扩展定理，无新前提 | `paper:6.19` 的有限 ν 扩展结论及源到 E₃ 的资格 |
| `KIP126.ProofTools.Standard.paper6_24_infinite_nu_extension` | 下列完整存在性／无限扩展定理，无新前提 | `paper:6.24` 的指定源、指定目标的无限 ν 扩展结论 |

两个 theorem 直接展开完整类型，避免再增加两个仅包装目标的 public Statement 定义：

```lean
public theorem paper6_19_finite_nu_extension :
    ∃ x : Ambient model (.shift 3 .sphere) (3,36),
      IsSphereThreeH0H4Square x ∧
      ReachesPage (model.classical.obj ((ClassicalObject.shift 3 .sphere).obj
        model.auxiliary)) 3 (3,36) x ∧
      FiniteExtension model (.shift 3 .sphere) .sphere model.auxiliary.nuMap
        3 2 3 36 x h0p

public theorem paper6_24_infinite_nu_extension :
    ∃ x : Ambient model (.shift 3 .sphere) (3,36),
      IsSphereThreeH0H4Square x ∧
      InfiniteExtension model (.shift 3 .sphere) .sphere model.auxiliary.nuMap
        2 3 36 x h0p
```

**原签名：**上述三个公共名字在原基线均不存在；现有 private `Paper6_19FiniteNuExtensionStatement`、`Paper6_24InfiniteNuExtensionStatement` 的完整定义在数值源快照，原来的上游 `FiniteExtension`／`InfiniteExtension` 完整定义与 witness 类型见 [existing-extension-predicates.md](evidence/existing-extension-predicates.md)。它们不被改写。

**固定源的完整含义。**新谓词不是 `∃x` 后给它任意起名。它从指定标准球页类 `product h0 (model.standardClasses.standardHiSquare 4)` 出发，依次要求实际页类

- `x1 ∈ E₂^(3,34)(ΣS⁰)` 在实际 `classicalSuspension .sphere` 下 desuspend 到该指定乘积；
- `x2 ∈ E₂^(3,35)(ΣΣS⁰)` 在下一次实际 suspension 下 desuspend 到 `x1`；
- `x3 ∈ E₂^(3,36)(ΣΣΣS⁰)` 在第三次实际 suspension 下 desuspend 到 `x2`；
- `x` 等于固定 `ΣΣΣS⁰ ≅ Σ³S⁰` 的实际 classical page map 作用于 `x3`。

最后的 comparison 精确为 `shiftFunctor Spectrum 1` 对 `shiftFunctorAdd' 1 1 2` 逆同构的作用，再与 `shiftFunctorAdd' 2 1 3` 的逆同构复合；完整方向、所有对象与 `by decide` 参数在候选定义体内联，不另公开技术 helper。检查文件包含 `∀x, publicPredicate x ↔ privateCompletePredicate x` 的 `rfl` 证明，实际验证两者定义相同。

**有限资格与零。**`ReachesPage ... 3 ... x` 允许其页类为零；没有擅自加强为非零永久存活。原 `FiniteExtensionWitness` 同时保留实际 `Q₂` 源／目标、原始检测、同一个归一化有限映射与实际扩展等式。目标恰为 B 中固定的 actual `h0p`，不是只存在某个同次数类。

**无限资格与同一个全代表。**现有 `InfiniteExtension` 是完整 `InfiniteExtensionWitness` 的 `Nonempty`：包含两个实际永久资格、实际 full-space E∞ 标签及原标签检测、同一个实际 normalized `ν` 映射的 ESS 方程。这里确实先构造一个实际源 `a` 与目标 `β`，满足指定首商检测和严格等式 `a·F=λβ`，然后包装为该完整谓词；不把各有限层上独立选取的见证集合当成一个全代表。有限定理通过同一全见证的有限商限制取得，保留源的固定 suspension 关联和指定目标。

**依赖方向必须保留。**这是一条完成扩展结论的替代数学证明路线：已登记的经典 `d₂(h₅)=h₀h₄²`、B 所标定的独立文献 `d₃(h₂h₅)=h₀p`、实际归一化 ν 在首商上的作用，以及 quotient-boundary 的自然性，给出 full ν-extension，再限制出 finite ν-extension。源码 `target_h2h5_boundary` 明确消费 `paper6_7_classical_d3.toHasDifferential`。所以实际方向是 **独立文献 d₃ → full ν-extension → finite ν-extension**；不能再把这套新证明描述成不依赖该 d₃ 的原文 “Cν d₂／Mahowald → ν-extension → Leibniz → d₃” 正向证明。Lean 本身没有循环，Blueprint 的 proof 依赖也应保留这个真实方向。

原文 `Cν` 上 `d₂(h₀h₄²[4])=h₀p[0]` 及相应页映射数据不包含在 C 的候选根中，不能因为 C 的扩展输出已经另证便自动记作完成；下文 D 随后以另一条实际构造补出了存在性 d₂ 及指定页映射。`paper:6.19` 若直接绑定这条完整扩展结论，原文输入计算仍作为原文路线说明保留其范围，不混成该 theorem 已证明的额外断言。

**最小公开依赖。**C 的公开类型需要 B 的固定 `p,h0p` 两个标签。可以批准 B+C；也可只批准 B 的标签子集 `{p,h0p}` 再批准 C，而保留 B 的两个 d₃ 定理私有。C 的证明仍可合法调用已完成的 private 数值结果，不能把“未公开某个已证结果”误写成数学新假设。候选单文件在开头重现 B 作为检查上下文，以便无 `-o` 核验；这不表示 C 又申请六个重复声明，C 的新增根严格只有上述三个。

**证据等级与局限。**本报告实际检查三条 C 根的完整类型、定义等同、固定对象、原有 witness 语义及三项 `#print axioms`，均如实继承现有 `sorryAx`。另有独立 proof-auditor 的 [配套日志](evidence/nu-proof-auditor-visible-sites.log)：其 root kernel／递归检查通过，列出 34 个 **当前 import 环境可见证明体中直接含未证的上游 sites**。该 34 不是完整许可洞闭包数；普通跨模块 import 不恢复所有不透明上游证明体，`collectAxioms` 的 `sorryAx` 摘要也不能还原其全部来源。Literature d₃、source-basis 与乘法比较等已登记输入仍被真实调用，不能因未出现在 visible 列表就视为已消除。完整许可责任总账继续由各模块 InternalAudit 与统一 `lake build` 核验；本报告不把上述日志或单文件检查替代全量审计。

随后 proof-auditor 实际补跑了同源最终 ν 源码、显式 `import all` 五个上游模块 InternalAudit 的闭包检查（仍无 `-o`），exit 0；新日志为 [nu-proof-auditor-full-closure.log](evidence/nu-proof-auditor-full-closure.log)。在该更完整 import 环境中，full／finite 两根分别遍历 9561／9590 个项目及边界依赖，均列出 **71 个已登记上游直接 sorry 位置**，包含先前被不透明导入遮蔽的 `mahowald_tangora_h2_h5_d3`、`sourceBasis_values`、`comparison_product` 等。该日志由独立 proof-auditor 运行，不冒充本报告员再次执行了完整依赖遍历；本报告员另独立把两份 71 项清单逐个与当前冻结 `proof-obligations.json` 核对，均无未登记项，结果为 [nu-full-closure-baseline-membership.json](evidence/nu-full-closure-baseline-membership.json)。34 是先前有限可见环境的历史结果，71 是新增完整上游导入环境下的结果，二者不是数学前提变化或责任消失。

### 最小公共方案 D（一个实际 cofiber d₂ 存在定理）

最终源 `KIP126/ProofTools/Paper/NuCofiberNumericalDifferential.lean` 稳定在 SHA-256 `3707286d9661901be6876a00fb86153d87166eeafea7acc39196357e39a33f37`，快照为 [cofiber-private-source-snapshot.md](evidence/cofiber-private-source-snapshot.md)。本报告员独立展开最终根及私有 `bottomH0P` 定义后，构造了最小的**一个**新公共根：

```lean
public theorem KIP126.ProofTools.Standard.paper6_19_actual_cofiber_d2 :
    ∃ x : Ambient model (.shift 3 .sphere) (3,36),
      IsSphereThreeH0H4Square x ∧
      x ∈ permanentCycles model (.shift 3 .sphere) (3,36) ∧
      ∃ uTop : Ambient model (.shift 1 (.shift 3 .sphere)) (3,37),
        (model.classicalSuspension (.shift 3 .sphere)).DesuspendsClass 3 37 uTop x ∧
        ∃ xbar : Ambient model .nuCofiber (3,37),
          (model.classical.map model.auxiliary.nuRouteTriangle.h).pageMap 2 (3,37) xbar = uTop ∧
          DifferentialAt model .nuCofiber 2 (3,37) (5,38) xbar
            ((model.classical.map model.auxiliary.nuRouteTriangle.g).pageMap 2 (5,38) h0p) ∧
          IsPermanent model .nuCofiber (5,38)
            ((model.classical.map model.auxiliary.nuRouteTriangle.g).pageMap 2 (5,38) h0p)
```

完整精确源码为 [public-cofiber-wrappers.lean](evidence/public-cofiber-wrappers.lean)，上面的完整类型采用候选文件中的同一 Standard-model 记号。原公共名字不存在；原 private 最终类型和固定底标签定义完整保存在源快照。候选只把

```lean
(model.classical.map model.auxiliary.nuRouteTriangle.g).pageMap 2 (5,38) h0p
```

内联两次作为同一实际底标签，不增加一个公开技术 helper 或任意独立选取的底类。公开 theorem 证明体直接 `exact` 私有最终根，实际检查通过完整类型的定义等同。

**全部固定关联：**`x` 满足 C 的真实三次经典 suspension 源谓词，且本身属于实际源的 permanent-cycle 子空间；`uTop` 再经实际 `classicalSuspension (S³)` desuspend 到该同一个 `x`；`xbar` 在实际 `Cν` 的次数 `(3,37)`，其实际 `q_E₂` 像就是同一个 `uTop`。微分目标是实际 `i_E₂(h0p)`，其永久资格也是对这个相同实际页类断言，而不是另选某个同次数检测。没有把实际页映射换成独立矩阵，也没有把 suspension 标签当自由变量。

**量词及强弱：**结论存在某个同时满足这些条件的 `x,uTop,xbar`。它不声称每个预先选择的 AH lift 都具有该微分，不断言 `xbar` 唯一。`DifferentialAt` 是实际指定值的微分等式，允许零；该根未额外证明 `i_E₂(h0p)≠0`、`HasNonzeroDifferential` 或底边长度零扩展 essential，报告不会把它写成这些更强结论。原 Blueprint 当前列出的 actual q/i 页映射、d₂ 等式和 permanence 与这里分别对应，不为未出现的 nonzero 条件人为追加新的接口前提。

**证明方向：**这个 cofiber 类由 C 背后的独立 full ν 代表、实际三角与 λ-cofiber 的共同 lift 构造得到。随后实际 quotient-boundary 比较解码为 `d₂`，并保留同一个 top-cell、bottom-cell 标签；符号经过实际负号图与页二特征二校准。它是 **独立球 d₃ → full ν 关系 → actual cofiber d₂** 的推导，不是重新运行 secondary Steenrod algebra 的独立计算，也不能作为不依赖该球 d₃ 的原文输入重新证明该 d₃。

**已执行检查：**

```sh
lake env lean interface/proposals/ProofTools/20261021-grey-section-formalization/evidence/public-cofiber-wrappers.lean
```

无 `-o`，**exit 0**；完整打印类型与公理依赖见 [public-cofiber-wrappers.log](evidence/public-cofiber-wrappers.log)。固定模型无新 universe 或 caller 参数，保留现有传递 `sorryAx`。配套独立 proof-auditor 对同源根及关键 helper 的全上游导入检查见 [cofiber-proof-auditor-full-closure.log](evidence/cofiber-proof-auditor-full-closure.log)：公共候选对应最终根遍历 9635 个项目及边界依赖、75 个已登记直接未证上游位置，未添加本地证明洞。本报告员另独立把日志的 75 项及两个 helper 清单与冻结基线核对，均无未登记项，记录在 [cofiber-check-result.json](evidence/cofiber-check-result.json)。完整责任审计仍遵守前述 C 中对 import 环境及全量构建的限制。

**公开范围及替代方案：**只增这一 theorem、相应如实生成的导出及其公共入口／锁项，并在 `paper:6.19` 对应的实际 cofiber 数据结论上绑定。D 的公开类型只需要 B 的 `p,h0p` 与 C 的 `IsSphereThreeH0H4Square`；不要求把 C 的两条 theorem 也公开，私有已证结果仍可正常调用。候选单文件复制 B/C 上下文只是为了无 `-o` 核验，D 新增名单严格只有此一根。若不批准该新增，可继续保留私有完整证明而不加绑定；不会通过删减 source/suspension/top/bottom 关联缩小目标。

### 聚合 `paper:6.8` 的零目标边界核对（历史疑点，已由方案 E 闭合）

另独立核对了原文实际措辞，完整原段及行号在 [doubling-zero-source-snapshot.md](evidence/doubling-zero-source-snapshot.md)：

- 原 Remark 6.9（`Example Leibnizno` 后第一个 remark）陈述 essential 短扩展对两条 length-two extension 的 crossing，其中目标标签分别为 `0` 和 `h₀d₀`；再比较忽略 crossing 所导致的两个经典输出。此段的 extension 结论应按原 ESS 标签与完整不定性读取，不应额外要求所有代表像都严格为零。
- 原 Remark 6.10（`rem:chuaerror`）则**明确提升到实际 full synthetic homotopy 等式**：存在 `[h₀h₃²] ∈ π_(14,17) S^(0,0)`，其 `[h₀]` 乘积在 `π_(14,18) S^(0,0)` 中严格等于零；又列另一 lift 的非零像，并称第一个 lift 为 Chua 定义下的 maximal `[h₀]` extension。这不是只有目标 E∞ 类或某一 associated grade 为零的措辞。
- 更早 Example `extonEn` 的第 (4) 项（原文 `main.tex:1421–1431`）也明确写同一个实际乘积等于零，给出的具体理由是 `π_(14,18) S^(0,0) ≅ Z/2`，生成元为 `[λh₀d₀]`，并可由更高 Adams 滤过的 `[λd₀]` 经 `[h₀]` 命中，从而校正原 source lift 使实际像为零。这一具体群与校正事实足以解释原文的额外断言，不能把它从来源中删掉。

这项来源核对在十三根批准阶段明确了必须补证的区别：完整 ESS 的目标标签 `0/v`、essential 短扩展和错误零输出的否定，并不自行证明 Remark 6.10 的实际严格零像；**目标标签为零本身仍不等于实际像为零**。后续方案 E 已通过具体 full-space 桥接与 source 校正构造严格零像见证，并证明同一像对每个有限 λ 幂可除；另构造第二个实际非零 `λβ` 像及同一 weight 的 essential crossing。这些已证事实现包含于完整公开定理。

这里保留的是原文语义与历史补证责任的精确区分，没有人为把 Remark 6.9 的标签结论加强成所有 full 像为零，也没有把 Remark 6.10 的 full 等式降为标签等式。上述核对本身未修改生产数学、未增添假设；后续补证与绑定由独立方案 E 完成。B 的两个经典 d₃ 是当时的候选事实，其中仅 6.7 根纳入十三根批准；6.8 的局部 d₃ 现作为完整 warning 的一部分公开，不另立局部公共根。

## 数值例子的已完成结论与保留边界

四个原文数值条目的完整固定对象、标签、次数、输入与结论保存在目标快照，不能用附加假设的泛型特化取代它们。

| 条目 | 要证明的原目标 | 当前已完成结论与真实范围 |
| --- | --- | --- |
| `paper:6.8` | 乘二例子的实际三条输入、`d₁(d₀)=h₀d₀` essential crossing、两种全代表以及省略 crossing 所致的错误零结论 | Literature 的某非零目标已通过 E₂ `(5,19)` 唯一基底标定为 `h₀d₀`；后续完整乘二无限关系、同权 essential crossing、长关系 inessential、两个不同实际全代表及严格零/maximal 全部已由方案 E 另行证明、获批并直接绑定。逻辑上仍不把单个非零 d₃ 当作这些全部事实的证明。 |
| `paper:6.19` | 固定实际 S³ 源在 E₃ 的资格与确定目标 `h₀p` 的长度二有限 ν 扩展；原文另列 Cν d₂ 和有限边输入作为论证路线 | **有限扩展完整结论已由 C 证明；指定 actual q/i 页映射、actual cofiber d₂ 与底标签 permanence 已由 D 另行构造并独立检查**。源是构造出的 AH lift，不是任意预选者；当前根未宣称非零／essential，也没有重跑 secondary Steenrod 独立计算。 |
| `paper:6.24` | 同一确定实际 S³ 源与目标 `h₀p` 的全 synthetic 无限 ν 扩展 | **完整无限扩展与指定源／像检测已由 C 证明并独立检查**，实际同一全代表与严格 λ 等式均保留。原文由 finite extension 经 no-crossing／stretching 的具体路线仍与此替代证明分开说明。 |
| `paper:6.7` | 确定目标的经典 `d₃(h₂h₅)=h₀p`；原文用指定 `ν` 扩展和 Leibniz 推导 | Literature 已有 `mahowald_tangora_h2_h5_d3` 给某个非零目标；E₂ `(5,38)` 唯一基底及乘法比较允许把目标识别为 `h₀p`。该目标标定与确定目标微分已私有证明，并由方案 B 的独立公开草稿复核，但不能因此称原文依赖 `paper:6.24` 与实际 no-crossing 的 Leibniz 论证也完成。 |

独立读到的 Literature 两条完整类型均为 `∃y, HasNonzeroDifferential ... y`，完整签名在证据快照。E₂ 已有 `sourceGenerator`、`sourceAtom_agrees`、`comparison_product`、`comparison_h0`、`coordinates_basis` 等公共桥接；因此“原 Literature 类型没有目标名字”本身**不是**不能标定目标的证明。该标定现在已完成并由本报告的方案 B 独立检查通过。它们仍继承既有 E₂ 比较与文献输入的未证责任。

历史候选 A 不自动包含数值声明，B 提供四个标签与两条经典结论供选择，C 包含真实源谓词与两个完整 ν 扩展，D 包含完整 actual cofiber d₂ 存在定理。最终采用的十三根子集及后续 E 已完成、获批和实施；完整 warning 不再是剩余缺口。6.19 类型未断言的非零／essential 强结论及原文独立正向证明路线仍不额外承诺，也未通过新增公理、许可洞或条件版 theorem 冒充完成。

## 下游影响

| 范围 | 已实施动作及保留责任 |
| --- | --- |
| `KIP126/ProofTools/` | 由协调者增加小型 public 包装文件，分别沿用私有 `SyntheticProgramRules`、已完成数值证明、`NuNumericalExtensions` 与 `NuCofiberNumericalDifferential`；不接手 Literature/E₂ 或下游计算责任。 |
| `KIP126/ProofTools.lean` | 公开导入包装模块，保证普通公共消费者可用；不公开 `import all` 或内部辅助声明。 |
| `interface/baselines/proof-tools-api.json` | 仅登记第一次批准的 A6＋B 子集3＋C3＋D1，以及后续 E3 和它们的真实生成导出、类型、宇宙及传递公理依赖；原216条完整记录逐项不变，未登记 B 的局部6.8根。 |
| `interface/baselines/proof-obligations.json` | 不新增公理／许可洞；只有证明体导致已有审计摘要确需更新时由协调者同步真实结果，不借此掩盖数值缺口。 |
| `blueprint/chapters/ProofTools.tex` | 方案 A 的四个数学结论各直接绑定上表 theorem；两个支持型 public proposition 不另挂到说明节点。方案 B 对 6.7 确定目标经典结论给直接绑定，C 对 6.19/6.24 的完整扩展结论、D 对 6.19 的 actual cofiber 数据结论分别给直接绑定；各自原文论证路径保持清楚。6.8 完整 warning 已由另行获批的 E 定理直接绑定。三条纯说明和本轮排除的算法猜想保持原本地位。 |
| 测试与审计 | 检查普通导入消费、获准声明归属唯一、完整导出、固定对象及接口差异；运行既有 `python3 scripts/check-source-inventory.py` 与 `lake build`。不删覆盖，不升级工具链，不共写他人的构建进度。 |

现有公共调用方无需改参数；Main、AdamsCalculations、Geometry 等下游不因这些增补取得新的假设义务。生产修改严格按两次明确批准的范围完成，未实施未批准的局部6.8根。

## 阻塞范围与继续项

**本次已经批准的实施范围：**上文实际核验的最小十三根组合与七个数学条目绑定，以及相应入口／锁的如实增量。B 的局部 `paper6_8_classical_d3` 仍不单独公开；`d0,h0d0` 及完整乘二定理后来已在独立方案 E 中明确获批，见交叉记录。

**可以继续：**保接口私有证明、已完成数值目标、完整 ν 扩展与 actual cofiber d₂ 的审计、原文独立正向路线、现有上游接口的直接调用、独立 proof/type 审计和已有构建检查。私有完成不自动变成公共绑定。

**范围边界：**`paper:6.8` 的严格零像／maximal、两个不同实际 lift 及同一 weight 的 crossing 已随后全部补齐并由方案 E 提供完整公开定理。原文不借用已知目标 d₃ 的独立正向论证、以及 6.19 未额外断言的底标签非零／essential 强结论，不在本次实际结论之外追加承诺。6.19/6.24 的扩展与 full 代表已由 C 完成，actual cofiber d₂ 与固定 cell map 数据已由 D 完成，不再把它们本身列作缺口。程序内部算法形式化已按本轮范围排除；两个既有 soundness 猜想保持未证，不据此暂停其他数学补证。

## 人类审核记录

2026-10-21，用户对本报告顶部最小十三根及七个条目绑定的明确询问回复：“批准最小 13 项并绑定”。因此，方案 A 六根、B 的 `p,h0p,paper6_7_classical_d3` 三根、C 三根、D 一根及其必要入口／基线增量已获批准、实施并通过最终核验。B 的另外三根不在这一次授权内；随后 `d0,h0d0` 和完整 warning 已由方案 E 另行明确获批，局部 `paper6_8_classical_d3` 未单独公开；既有类型、公理及许可洞保持原边界。最终实施与验证结果如下。


### 实施核验结果（十三根阶段与后续 E 分开记录）

生产文件为 `KIP126/ProofTools/StandardSpecializations.lean`，13 根签名及证明与批准整包一致，单文件检查和 `lake build KIP126.ProofTools` 已通过。公共入口已添加这一个文件，七处数学条目已按本报告的绑定表写入；五个支持定义未被额外绑成结论。

十三根阶段从实际已编译入口重新采集：旧 216 项导出全部保留，所有旧类型指纹及宇宙参数不变；新增恰为批准的 13 根及它们的 30 项编译器自动生成子声明，共 259 项。每个新增导出均是这 13 根之一或其真实生成子项，没有其他新增公开根。接口基线已同步为134个命名声明、125个编译器生成项；原有216条记录（包括类型、宇宙与公理依赖）逐条保持相等。全部既有214项许可责任及其他保护输入均未变。


十三根阶段的接口计数保留为历史实施证据；包含后续 E 的最终全量结果统一如下，不再将乘二正文视为待检查。新数学文件均经独立审计，仍继承既有注册上游责任。

修复了本地 dependency audit 的一个普通导入可见性问题：仅在实际定义源模块属于 ProofTools 时展开证明体，上游交由各自 InternalAudit；保留本地缺失依赖和本地 proof gap 的拒绝。独立探针证实原缺失 helper 属于上游 Literature，已经有完整证明；改动遵循现有 Main 边界模式。全库检查重新通过；临时负向探针把原有未完成 crossing iff 放入已完成根后，仍准确报错拒绝。没有修改许可清单、改数学接口前提或跳过缺失本地证明。

乘二完整 warning 的额外三根另见 [方案 E](../20261021-doubling-complete-warning/report.md)，其授权与实施不倒算进第一次十三根批准范围。

2026-10-21 后续交叉记录：用户另行批准方案 E 的 `d0,h0d0,paper6_8_complete_crossing_warning`，详见 [独立方案 E](../20261021-doubling-complete-warning/report.md)。最终接口为137个命名声明、131个真实编译器生成项，共268项导出；相对原216项，新增16个获批根和36个生成项。原216条完整接口记录逐条不变，许可责任仍214项且文件内容未变。

### 最终联合核验结果（十三根＋方案 E，2026-10-21）

两次授权合计 **16 个命名根＋36 个真实编译器生成项**，ProofTools 当前接口为 **137 个命名声明＋131 个生成项＝268 项导出**。原 216 条完整接口记录（类型、宇宙、公理依赖及导出关联）逐条不变，全部 214 项许可责任及其文件内容不变。`paper:6.8` 现直接绑定完整 `paper6_8_complete_crossing_warning`；相关输入、同权 crossing、长关系 inessential、第二实际非零像与实际严格零/maximal 均已完成。

协调者执行最终检查；本报告员只读核对了相应日志，不把这次文档回写称为自己重新执行构建：

- `lake build`：**成功，3618 jobs**。本地日志 `/tmp/grey-formalization-20261021/final-complete-build.log`。ProofTools audit 为 5708 declarations、1 项原有登记 pending、无 project axioms；Main audit 为 1921 declarations、0 项本地 pending。
- Source inventory：**592 project files、35 consumer/audit files**，模块依赖及 private-import 边界通过；日志 `final-inventory.log` 位于同一临时证据目录。
- Blueprint：**49 项测试通过**；原生导出 **241 个数学条目、9875 个 Lean declarations、1919 个 warnings**。日志分别为同目录 `final-all-blueprint-tests.log` 与 `final-blueprint-build.log`，warnings 按原生输出保留。
- 浏览器预览与真实卡片核验：`page_errors=[]`、`math_errors=0`；`paper:6.8` 与 `paper:6.19` 的实际卡片均为 `lean ok`，分别显示 1／2 个绑定。证据为同目录 `blueprint-final-preview.json`、`final-cards.json`；当前页面统计为 128 个 lean 条目，不沿用早期脚本抓到的旧统计。网页状态仍不替代 Lean 信任审计。
- 接口提案校验：**26 份报告通过**。没有通过改锁放宽前提、新增许可洞或修改已批准数学候选使检查通过。

以上 `/tmp` 路径为本地构建证据位置，未冒充随报告发布的附件。数学候选、独立 kernel／闭包审计与准确前提证据继续保留于两份提案各自的 `evidence/`，本次仅更新报告当前状态。

