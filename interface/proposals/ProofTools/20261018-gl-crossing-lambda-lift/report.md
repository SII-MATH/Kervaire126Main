---
title: GL 的 crossing 条件与 λ 提升
archived_from: local-history/metadata/interface-reviews/ProofTools/20261018-gl-crossing-lambda-lift/report.md
archived_sha256: aa0615b25912ffbd880434ec5aad960c968f4bcefc9d9a9501cba51c084f40cd
summary: "一般谱上的 GL crossing 与 λ 提升条件有数学反例；报告未声称固定模型 Lean 反例，候选条件需另行审核。"
issue_id: "ProofTools-20261018-gl-crossing-lambda-lift"
responsibility_module: "ProofTools"
targets:
  - "AimPaper Proposition prop:cross-f-Er (general finite crossing equivalence)"
  - "AimPaper Theorem thm:e73f481e (general-spectrum GL statement)"
  - "KIP126.ProofTools.Standard.generalizedLeibniz: GL1/GL2 geometric subgoals"
baseline_commit: "18113d44df596c43d4fb7aab2aaf7ca9e0c52c48"
worktree: "/inspire/hdd/global_user/czxs25250150/Kervaire126Main"
candidate_source_commit: "uncommitted candidate; input snapshots and SHA-256 manifest attached"
api_file_and_sha256: "metadata/proof-tools-api.json b22076575c6abdb44300a9e1959eb35d73bdd200767ea1f87a5098210ed30a7f"
source_file_and_sha256: "KIP126/ProofTools/GeneralizedLeibniz.lean 660fd29e307a53b89b0478452d6faaaae56529417a61686293f41ac7666f0e3d"
reporter_agent: "/root/crossing_interface_report"
independent_of_discoverer_and_implementer: true
evidence_level: "general-spectrum mathematical counterexample, independently enumerated finite coefficients; not a fixed-model Lean counterexample"
status: pending-human-review
human_decision: null
---

# 接口调整人审报告

## 请求人类决定的具体问题

**核验结论：AimPaper 的一般 Proposition 5.10（`prop:cross-f-Er`）在原 Definition 5.9 的条件下失败。它把较大 λ 商中的实际 crossing 提升为较小商的零层扩张；下面的例子中，该较小扩张不存在。后续独立核验的第二个例子还满足原 Theorem 6.1 的全部前提而否定结论，因此一般谱上的 GL 原陈述也失败。两例均未识别为当前固定 `Standard.model` 的对象，不能称为固定 Lean GL 反例。**

请决定后续目标范围：

1. **方案 A：保持全部公共接口不变。** 保留 GL 两个待补，停止使用已失败的一般 crossing 等价作为通用中间引理；继续证明固定对象闭包上的特殊结果，或寻找不依赖这条等价的固定对象 GL 证明。当前证据不能排除此方案；但原一般谱版本已不能在原条件下继续求证。
2. **方案 B：批准本报告第“方案及精确差异”节给出的 GL 专用充分条件版本。** 保留四个现有 crossing 谓词的语义，在 GL 的原 no-crossing 条件上增加同一有限商、同一 synthetic weight 的实际 ESS no-crossing 条件。结论、对象、页数、源靶标签保持不变；`LeftEdge` 等内部证明责任仍由 ProofTools 完成。修改范围仅限 GL 及新增的两个 GL 专用公开谓词、相应记录和测试。

方案 B 是**待审修改建议**，并未实施，也未声称已经证明该修正版。人类可只批准 A，或明确批准 B 的精确范围。不能将“继续补证明”解释为改变公开前提的授权。

本报告依据当前 `AGENTS.md`、指定 protocol 和 template 制作。报告员未参与候选发现、生产实现；已独立读取定义和来源，重新推导谱识别，并另写独立穷举程序。仅在本目录写入文件。

## 原接口、背景与问题成因

### 冻结声明与职责

完整原声明（包括泛型宇宙、实例、Law 全部前提、两个 crossing 定义、witness 所有字段及 essential 语义）见同目录 [original-interface.md](original-interface.md)，由本次读取的源码逐字摘录；[source-manifest.json](evidence/source-manifest.json) 和 `evidence/snapshots/` 保留输入身份。

公共证明入口为：

```lean
public theorem KIP126.ProofTools.Standard.generalizedLeibniz
    (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary) :
    GeneralizedLeibnizLaw model X Y f
```

这里的 `model` 固定为 `KIP126.AdamsSynthetic.Standard.model`；该定理没有自由的模型、范畴或宇宙参数。泛型 `GeneralizedLeibnizLaw`、witness 和 crossing 的定义另外具有 `u v w`、`C`、`Syn`、相应范畴与 functorial-cofiber 实例，以及同一个 `D : Model C Syn`。不能把“定义适用于任意 D”混同于“此公共定理证明了任意 D”。

`ClassicalObject` 实际只包含 `.sphere`、`.nuCofiber`、`.detector` 及整数 `.shift`。没有一般直和或任意 Eilenberg–Mac Lane 谱构造子；固定 detector 也不能任意替换。所有 maps、convergence、E∞、filtration、λ 商和 normalized map 必须是这个 model 指定的实际对象。

GL 在原 finite extension 和 infinite extension、经典微分以及周期/页数条件下，推出 `d_(r+l-m)(y)=yInfinity`。当前两个 `sorry`（`GeneralizedLeibniz.lean:171,304`）都仍需要：

* 从经典微分得到指定有限/无限 witness 之间的 `LeftEdge`；
* 从原经典/有限 no-crossing 条件得到实际方块上边/左边的 no-crossing；
* 从原无限 no-crossing 得到乘 λ、移位后的实际底边 no-crossing。

方块引理、右边存活及反向微分读取已分别完成，不等于上述几何输入已完成。GL 的 type/body fingerprint 与两项本地待补的审计仍在；未因本例更改。

### 论文目标和缺失步骤

AimPaper 输入 SHA-256 为 `828ee5a5aa06e1f390b036a043230ed417446fa7be11a4e27eecc4a565135c4b`。相关定位：

* §2 开头（约第 254 行）：2-complete、connective、finite-type 谱；
* §4 开头及脚注（第 999 行）：synthetic ESS 使用有限谱，或 synthetic Adams 谱序列强收敛的谱；
* Definition 5.4，`def:6c076a33`（1303）：零层 `(f,E_R)` 扩张及实际 ESS essential 性；
* Definition 5.9，`def:41d51149`（1437）：较小商 crossing；
* Proposition 5.10，`prop:cross-f-Er`（1515）：两种 crossing 等价；
* Theorem 6.1，`thm:e73f481e`（1606）：GL，其证明在 1646 行应用上述转换。

写 `q=R-1`、原扩张长度 `N`、源位移 `a>0`、靶位移 `b≥0`、`e=e(f)`。原论文 crossing 要求较小商 `Q_(q-a)` 中一个长度 `N-a-b` 的 essential 扩张，并要求其经典靶不属于 **`B_(1+N-b-e)`**。当前 `FiniteHasCrossing` 正确保留这个较大边界指数，未误写成 `B_(1+N-a-b-e)`。

论文从较大商的等式

\[
\hat f_q(\lambda^a x')=\lambda^{N-b-e}y'
\]

直接断言存在较小商的扩张

\[
\hat f_{q-a}(x')=\lambda^{N-a-b-e}y'',\qquad
y''\equiv y'\pmod {B_{1+N-b-e}}.
\]

交换方块只保证两边乘 λ 后相同。除 λ 后，`f` 的像可能多出低滤过的 λ-torsion；必须能用**源端**修正去消掉它，才能得到所需扩张。单独存在源原像、靶原像或正确的靶边界商均不提供这种同步修正。

现有私有 `normalized_finite_source_image_division` 只保证较小像的底层滤过；`finite_crossing_of_lifted_witness` 正确地**以已有较小 witness 为前提**，再推出 essential 性、边界排除和 `FiniteHasCrossing`。这两项已证结果与本例一致，不应删除或改写成无条件提升。

问题分类：第一例是论文一般转换命题的数学反例，第二例进一步反驳一般谱 GL 原陈述；当前固定对象补证路线存在缺口。不是已发现的 Lean 归一化实现错误。究竟需要修正一般命题的前提、crossing 定义，还是绕开该命题，属于方案选择。固定模型 GL 是否为真仍未决。

## 真实前提与对象核对

令 `E=H(Z₂)` 为完成的整数 Eilenberg–Mac Lane 谱，`T=H(Z/4)`，`j:E→T` 为模 4 商映射。取

\[
X=E_x\oplus E_v,\quad Y=T_t\oplus E_z\oplus E_y,\qquad
f(x,v)=(j(x),2x,4v).
\]

| 条件 | 核验结果 | 证据及限制 |
| --- | --- | --- |
| 经典谱 2-complete、connective、mod-2 finite type | 满足 | E、T 及其有限直和均满足；不把 finite type 误当 finite spectrum |
| 经典 Adams 收敛与完整输入 | 满足 | HZ 的单 h₀ 塔、HZ/4 两塔及唯一 d₂；May–Milgram Lemma 3、4 |
| synthetic 强收敛 | 满足，需独立论证 | 下节使用 BHS A.13、A.14、A.16、A.17；不只引用论文脚注或经典强收敛 |
| e(f) 和 normalized map | e=0，`fhat=νf` | j 在 mod-2 H₀ 非零；不任意选择正归一化 lift |
| 同一商、同一 weight、实际 maps | 满足 | q=3,w=1 的较大商；q=2,w=2 和 q=1,w=3 的小商；具体矩阵由 νf 得到 |
| 原扩张的有效页数和长度 | 满足 | R=4,N=2,s=t=1；0≤2≤R−2 |
| 原源靶 cycle 条件 | 满足 | `h₀v` 与 `h₀³y` 在自由 E 分量，均永久循环 |
| 原扩张非零、essential | 满足 | 全部同 grade 代表的 y 坐标均为 4 mod 8，零靶不在目标 coset |
| 较大商 crossing 非零、essential | 满足 | source `λh₀²x`，target `λ²h₀³z`；全体高源修正不能消去其 z 坐标 |
| 所有 Definition 5.9 候选 | 已穷尽 | (a,b) 只有 (1,0)、(1,1)、(2,0)；见下表 |
| 本例位于固定 `ClassicalObject` 闭包 | **未满足/未识别** | 不能据此实例化固定公共 GL 或宣称 Lean 固定模型矛盾 |
| 完整 GL 的额外经典微分与无限扩张前提 | 第一例未提供；第二例全部核对 | 见下文“完整 GL 的第二个反例”，其结论独立于只反驳中间命题的推断 |

## 独立证据与复现

### 独立来源及强收敛检查

[May–Milgram, *The Bockstein and the Adams Spectral Sequences*, p.129, Lemma 3(ii),(iii), Lemma 4](https://math.uchicago.edu/~may/PAPERS/34.pdf) 给出：`E₂(E)=F₂[h₀]`，所有类永久；`E₂(T)=F₂[h₀]{t,u}`，`|t|=(0,0)`、`|u|=(0,1)`，且 `d₂(h₀^k u)=h₀^(k+2)t`。完成不改变这些 mod-2 Adams 数据。报告员查看了原 PDF 图像，核实条件为 `r≥2`，不是 OCR 误读的 `r>2`。原 PDF 与 p.129 图像已存证。

强收敛额外核对如下，**这是由所引定理和本例页结构推出的结论**：

* E、T 的经典 HF₂ Adams 完成及收敛已知。BHS Proposition A.13、A.16 将完备性与强收敛传到 `νE`、`νT`。
* 每个正整数 q，BHS Lemma A.14 直接给出 `Q_qνZ` 的 νHF₂-nilpotent completeness。Corollary A.11 把固定 stem/weight 的谱页限制在有限 filtration strip；本例每个三次数的 E₂ 还是有限维 F₂ 空间。因此后页下降子群满足 Mittag–Leffler，`lim¹_r E_r=0`。Theorem A.17 的 synthetic 版本给出强收敛。
* 有限直和及所用 shifts 保留这些性质。于是“有限 synthetic 谱或强收敛”的脚注条件确实满足。

定位见 [BHS, arXiv:1910.14116v3, Appendix A, printed pp.73–76](https://arxiv.org/pdf/1910.14116v3)。`evidence/bhs-convergence-pages.txt` 与同目录原 PDF 可复查。这里没有由经典收敛直接跳到 synthetic 收敛，也没有靠 E∞ 表 alone 排除隐藏的无限滤过项。

### 实际 synthetic 群、滤过及映射

以下推导可独立于候选程序阅读。

1. 对 `νE`，BHS rigidity 与强收敛给出 stem −1 群为零。第一 λ 商是 Ext；在 stem 0，λ 的长正合列给出
   \[
   0\to\pi_{0,w+1}\nu E\xrightarrow\lambda\pi_{0,w}\nu E
      \to\mathbb F_2\to0\quad(w\ge0).
   \]
   这里左侧单射因 Ext 的 stem 1 消失，右侧满射因 stem −1 消失。`π_(0,0)νE=Z₂` 由 [Pstrągowski, Corollary 4.12、Proposition 4.57](https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/synthetic2.pdf) 的比较和 λ 长正合列确定。因此 `π_(0,w)νE` 可识别为 `2^w Z₂`；以各 weight 的生成元计，λ 作用乘 2。BHS Corollary A.19 把 Adams 滤过识别为此 λ-image 滤过，故 `F_(w+j)=2^j Z₂`。
2. 对 `νT`，在 w≥1、stem 0，BHS 的无限 window 只剩 filtration w 的 `h₀^w t`。所有更高 filtration 的 `λ^j h₀^(w+j)t`（j≥1）都已被上述 d₂ 杀掉。因此强收敛给出 `π_(0,w)νT=Z/2`，`F_w=Z/2`、`F_(w+1)=0`；stem −1 同样为零。λ 在相邻正 weight 间作用为零，因为它保留 Adams filtration。
3. 对 λ^q cofiber 的长正合列，由 stem −1 消失得
   \[
   \pi_{0,w}Q_q\nu E=\mathbb Z/2^q,
   \quad F_{w+j}=2^j(\mathbb Z/2^q),\qquad
   \pi_{0,w}Q_q\nu T=\mathbb Z/2,
   \quad F_w=\mathbb Z/2, F_{w+1}=0.
   \]
   滤过也由有限 window 与强收敛核对。q=1 直接为第一商 Ext。可能的正 stem Tor 类不进入所用 stem 0 群。
4. `νj` 在底层 Ext 上把 `h₀^w` 送到非零 `h₀^w t`，故其实际群映射为 mod 2。ν 保留有限 biproduct 及加法，λ 商也保留有限和，所以在任意 w≥1 的上述坐标中实际 `f_q` 是
   \[
   (a,c)\longmapsto(a\bmod2,,2a\bmod2^q,,4c\bmod2^q).
   \]
   该矩阵不是独立选择的抽象 map。由小商 (q,w)=(2,2) 到大商 (3,1) 的 λ，源的两坐标乘 2，靶的 T 坐标归零、其余两坐标乘 2。

此推导不需要把某个任意选择的 `hat4` 宣称为指定 scalar map；因此归一化 lift 的 λ-torsion 选择不成为本例的额外未证前提。所有输入来自早于争议命题的独立比较与初等 Adams 计算，没有调用 GL、MH2、`prop:cross-f-Er` 或其下游结论。

### 原扩张与较大商 crossing

取 `R=4,q=3,N=2,s=t=1,e=0`。原非零扩张为

\[
d_2^{f,E_4}(h_0v)=h_0^3y.
\]

在 weight 1，实际源 `(0,1)∈(Z/8)^2` 映到 `(0,0,4)`。同源 grade 的全部代表为 `(2a,1+2c)`；其 y 坐标始终为 4 mod 8，不能把像推到 filtration 4。完整目标 coset 有 `(0,0,1)` 与 `(0,1,1)` 两个 grade，均非零。因此 essential 不是只凭某个靶非零宣称。

同一商和 weight 中，源 `(2,0)` 在 filtration 2，像 `(0,4,0)` 在 filtration 3，给出

\[
d_1^{\hat f_3}(\lambda h_0^2x)=\lambda^2h_0^3z.
\]

所有同源 grade 的代表为 `(2+4a,4c)`，z 坐标始终 4 mod 8，完整齐次靶歧义为零。因此这是原扩张的 essential synthetic crossing（a=1,b=0）。

除 λ 后的小商是 q=2、weight 2。所有与 `h₀²x` 源 grade 相同的代表有奇数 x 坐标，像的 T 坐标始终为 1；它们的像不能在 filtration 3。允许靶改为模 `B₃` 同余的另一个标签也无用：根本不存在该源的一次正长度扩张。

### 全部小商 crossing 的排除

| a,b | 小页／q／weight | 长度 | 所有可能 essential 靶及为何失败 |
| --- | --- | --- | --- |
| 1,0 | 3／2／2 | 1 | 要像进入 filtration 3，x 必须偶数；这使 `(x mod2,2x,4v)` 在 Z/2⊕Z/4⊕Z/4 中整个为零，无 essential 扩张 |
| 1,1 | 3／2／2 | 0 | 唯一非零靶为 `h₀²t`（可来自两个不同源 grade），属于被排除的 `B₂` |
| 2,0 | 2／1／3 | 0 | 唯一非零靶为 `h₀³t`，属于 `B₂⊆B₃`，同样被排除 |

底 weight 的靶标签分母为 B₁=0，故不能加自由 E 分量而仍代表同一个 E∞ 靶。程序枚举了所有源线性组合及全部实际代表，未遗漏 v 分量或 inessential 修正。

所以，原 `(f,E₄)` 扩张满足 Definition 5.9 的 no-crossing，而对应较大商实际 ESS 有 crossing。**一般 Proposition 5.10 的等价本身失败，不只它所给出的某种选代表算法失败。**

同一个例子在未截断自由坐标 Z₂ 中也保留现象：对小源零层的正长度 1，x 偶数时像自动再高一层，所有扩张 inessential；两种长度 0 的靶仍为上述被排除的 T 类。不过本报告的可执行完整穷举只覆盖有限商；无限版本的这一判断是 2-adic 数学推导，不是有限枚举或固定模型证书。

### 实际复跑与证据等级

从仓库根目录运行：

```sh
python3 local-history/metadata/interface-reviews/ProofTools/20261018-gl-crossing-lambda-lift/evidence/independent_check.py
python3 local-history/metadata/interface-reviews/ProofTools/20261018-gl-crossing-lambda-lift/evidence/snapshots/local-history/proof-sessions/gl-2026-10-18/kernel-obstruction/check_hz4_crossing.py
```

两条均已实际退出 0。输出保存为 `independent-result.json` 与 `discoverer-script-rerun.json`。独立脚本分别遍历 64、64、16、16、4 个源代表，另外枚举齐次靶歧义并检查完整 affine coset；逐项验证它与“无零靶”的 essential 判据相同。所有三个小商位置的 `paper_crossings` 均为空；四个指定小源代表的像均为 `(1,2,0)`；全部 16 个 λ 方块坐标相容。

Lean 有限算术验证的确切命令和结果单列在 [validation.json](evidence/validation.json)。它只导入 Mathlib 并验证有限整数余数公式，**不证明谱识别，不实例化项目 model，也不证明完整反例**。不能把该 Lean 检查通过升级为“Lean 已反驳固定 GL”。

仅审查目录有写入；没有生产代码改动，故本报告没有运行项目全量构建，也不引用早前全量构建来验证本反例。后续生产修改仍必须执行仓库规定的 inventory 和 `lake build`。

### 完整 GL 的第二个反例：全部前提，而非只否定中间命题

此例由协调者追加，报告员随后独立核对了三个实际边、全部页数和 crossing 候选；不把第一例对 Proposition 5.10 的反驳直接推论为 GL 失败。

仍令 `E=H(Z₂)`、`T=H(Z/4)`，取实际 cofiber triangle

\[
E\xrightarrow4E\xrightarrow jT\xrightarrow\delta\Sigma E.
\]

改取

\[
X=T_a\oplus E_x,\quad Y=\Sigma E_w\oplus T_b\oplus E_z,
\qquad f(a,x)=(\delta a,jx,2x).
\]

两份 T 的底类记 `t_a,t_b`，顶类记 `u_a,u_b`，满足
`d₂(u_a)=h₀²t_a`、`d₂(u_b)=h₀²t_b`。`w` 是 ΣE 的单位类，位于 (0,1)。所有谱及 ν/有限商满足前文同样的强收敛条件。f 的 mod-2 同调非零，故 e(f)=0，normalized map 是同一个 νf。

固定参数与标签：

\[
\mathrm{page}=r=2,\quad m=0,\ l=2,\ s=0,\ t=1,
\quad x=u_a,\ y=w,\ x_\infty=h_0^2t_a,\ y_\infty=h_0^4z.
\]

| 原 GL 的全部前提 | 独立核验 |
| --- | --- |
| `2≤page≤r` | 2≤2≤2 |
| `e≤m≤page−2+e`、`l≥e` | 0≤0≤0、2≥0 |
| x、y 次数 | 均 (0,1)，分别在 T_a 顶塔及 ΣE 塔 |
| x∞、y∞ 次数 | (2,2)、(4,4)，精确等于原声明的两组公式 |
| `x∈Z_(r−1)`、`y∈Z_(r−1−m+e)` | 所需均为 Z₁=E₂；y 还是永久类 |
| x∞、y∞∈Z∞ | h₀²t_a 是边界但仍是共同永久 cycle；h₀⁴z 在自由 E 分量永久且不是边界 |
| `d_r(x)=x∞` | 已知 d₂(u_a)=h₀²t_a |
| finite extension | `d₀^(f,E₂)(u_a)=w`，由实际 Q₁νδ 的非零 Ext map 给出 |
| infinite extension | `d₂^(f,E∞)(h₀²t_a)=h₀⁴z`，由下述同一个 νf 的实际代表给出 |
| source no-crossing 的 disjunction | 经典 d₂ 在 E₂ 页没有 crossing：0<a≤page−2=0 无解 |
| infinite extension 的原 no-crossing | 所有三种 (a,b) 位置均核对排除，见下 |

**有限边的 δ 不是任选映射。** 模 2 同调中，4=0，所以 cofiber 的 connecting map δ 将 T 的顶分量映到 ΣE 的底分量。其实际 Adams E₂ map 把 `u_a` 送到 `w`；由第一商比较 `π_(1,1)(Q₁νZ)=Ext^(0,1)(Z)` 的自然性，同一个 `Q₁νδ` 给出所需长度 0 扩张。其他分量对此源均为零。

**无限边使用同一个 map 和同一 weight 2。** 此 stem 0 的实际源群是 `Z/2⊕Z₂`，靶的 ΣE 分量是 `π_(-1,1)νE=0`，其余为 `Z/2⊕Z₂`。所以

\[
\nu f(\alpha,c)=(0,c\bmod2,2c).
\]

取实际源 `(α,c)=(1,2)`，其 leading class 在 filtration 2 为 `h₀²t_a`，附加的自由源项是 `λh₀³x`，位于更高 filtration 3。像为 `(0,0,4)`，由 `λ²h₀⁴z` 检测于 filtration 4。故长度 2 的无限扩张确实存在。原扩张 **inessential**：同源 grade 的 `(1,0)` 有零像。但 Theorem 6.1、当前 `GeneralizedLeibnizLaw`、`InfiniteExtensionWitness` 均不要求原扩张 essential，不能额外排除这个合法前提实例。

这里 x∞ 虽然在经典 E∞ 上为零，却在 E₂ 及 νT 的 weight 2、filtration 2 上非零。AimPaper 明确规定 `B∞⊂Z∞`；当前 `IsPermanentCycle`（`SpectralSequence/Computation/State/Predicates.lean:51`）也明确允许其 E∞ 像为零。因此没有把“非零永久存活”偷换为“共同永久 cycle”。四个经典标签全都在各自 E₂ 上非零。

原无限 no-crossing 的 base 为 (2,2)，长度 l=2、e=0，因此 a,b 只可能为：

* (1,0)：native weight 3、长度 1。源自由坐标 c 若奇数，T_b 的底分量阻止像进入 filtration 4；c 若偶数，2c 被 4 整除，像已进入 filtration 5，所以长度 1 的靶为零，没有 essential 扩张。源 T_a 坐标对像恒为零。
* (1,1)：native weight 3、长度 0。唯一非零 leading 靶是 `h₀³t_b`，位于应排除的 B₂。
* (2,0)：native weight 4、长度 0。唯一非零 leading 靶是 `h₀⁴t_b`，位于 B₂⊆B₃。

所有 source linear combinations 均被这两个坐标分析覆盖；ΣE 在该 stem 的 E₂ 及 E∞ 皆零，不产生遗漏的候选。因此原 `InfiniteNoCrossing` 成立。

GL 结论却要求

\[
d_4(w)=h_0^4z.
\]

Y 的经典 Adams 序列按三个直和分量分裂；ΣE 的 w 为永久循环，其 d₄ 为零，而自由 E_z 分量的 `h₀⁴z` 非零且不属于 B₃。故该结论为假。这个独立完整实例证明：**AimPaper Theorem 6.1 按所读原声明，在一般谱范围内也不成立。**

`evidence/gl_assumption_check.py` 已退出 0，输出存为 `gl-assumption-result.json`。该独立程序检查全部所需坐标/filtration/coset 和参数；对 Z₂ 的检验只用 mod 8 精度，所有相关 grade 判断由这些低位完全决定。它同时检出实际同 weight crossing：filtration 3 的 `λh₀³x` essential 地映到 filtration 4 的 `λ²h₀⁴z`，而原零层 crossing 谓词漏掉它。δ 的谱识别、收敛及经典 d₄ 结论是上述独立数学证明，并非该程序形式化内容。

**仍不构成固定 Lean model 反例。** 本例新增 T、HZ 及有限和，当前 `ClassicalObject` 未包含或识别这些对象。不能据此给固定 `Standard.generalizedLeibniz` 填入 `False.elim`，也不能由这个数学报告声称当前形式化环境已矛盾。

## 方案及精确差异

### 方案 A：优先评估保留原接口

仍可尝试：

* 在固定 `.sphere/.nuCofiber/.detector/shift` 及实际 maps 中证明足够的特殊消 torsion/crossing 结果。两个反例均不属于该闭包，不能断言这个方向不可能。
* 为固定 GL 构造绕开通用 crossing 等价的证明，使用固定对象的特殊结构；第二例已满足一般 GL 全部数据，故不能把这些额外前提 alone 当作普遍修复。
* 继续内部 `LeftEdge` 标签/shift 匹配，完成以实际 ESS no-crossing 为输入的私有 GL 方块组装；这不改公共接口。

目前未发现可调用的上游接口保证同步 source/image 提升；这是一项已核对的接口检索结论，**不是**“整个固定理论不可能蕴含它”的模型论证明。不能把失败的一般提升命题新增到 Literature 或把它作为调用者的新结果包，借此转移 ProofTools 责任。

### 方案 B：保留旧 crossing 定义，新增 GL 专用几何充分条件

以下是**报告内拟议代码，未编译、未实施、未批准**。使用与 `Language.lean` 相同的泛型上下文 `u v w,C,Syn,D,X,Y,f`，不导出私有 `TowerNoCrossing`、`absoluteBoundary` 或方块 helper。

```lean
public def LeibnizFiniteNoCrossing
    (page : ℕ) (m s t : ℤ) : Prop :=
  ∀ u v : ℤ, s < u → u ≤ v → v ≤ s + m →
    ∀ x y, ¬ TowerEssentialExtension
      (D.convergentMap
        (.quotient (page - 1) (extensionSourceObject D X Y f))
        (.quotient (page - 1) (.nu Y))
        (finiteExtensionMap D X Y f (page - 1)))
      (t - s, t + normalizedExponent D.classicalTower f)
      u (v - u) x y

public def LeibnizBottomNoCrossing
    (page : ℕ) (r l s t : ℤ) : Prop :=
  ∀ u v : ℤ, s + r < u → u ≤ v → v ≤ s + r + l →
    ∀ x y, ¬ TowerEssentialExtension
      (D.convergentMap
        (.shift (1, -((page - 1 : ℕ) : ℤ))
          (extensionSourceObject D X Y f))
        (.shift (1, -((page - 1 : ℕ) : ℤ)) (.nu Y))
        ((SyntheticCategory.biShift (1, -((page - 1 : ℕ) : ℤ))).map
          (D.normalizedMap X Y f).map))
      (t - s, t + normalizedExponent D.classicalTower f)
      u (v - u) x y
```

原 Law 的最后两项几何前提是：

```lean
(NoCrossingOn D X r page (s,t) ∨
  FiniteNoCrossing D X Y f page m s t) →
InfiniteNoCrossing D X Y f l (s+r) (t+r-1) →
```

本方案 B 精确改为：

```lean
(NoCrossingOn D X r page (s,t) ∨
  (FiniteNoCrossing D X Y f page m s t ∧
   LeibnizFiniteNoCrossing D X Y f page m s t)) →
(InfiniteNoCrossing D X Y f l (s+r) (t+r-1) ∧
 LeibnizBottomNoCrossing D X Y f page r l s t) →
```

原 Law 的其他量词、页数/长度、cycle/permanent、微分、finite/infinite witness 以及结论全部不变。公共 theorem 名称和表面结论仍可写 `GeneralizedLeibnizLaw model X Y f`，但其语义因 Law 正文改变而实质变弱，必须人审。新增两个 public 名称也是接口变化。

这版前提**逻辑上加强原前提**：显式保留旧谓词并增加 conjunction，结论不变；无须假称新旧谓词等价。较大商 crossing 的反例显示新增 finite 条件不能在一般谱上仅由旧 `FiniteNoCrossing` 推出。尚未证明修正版对固定 model 的适用范围严格小于原版。

若人类希望删除旧谓词、只保留两个实际 ESS 前提，那是另一种可讨论的简化版本；**不包含在本方案 B 的批准范围内**，因为尚未证明其与原条件的全局逻辑强弱关系，尤其底边多了 λ 层。

底边的 weight 不能省略：若去掉最后 `(1,−(page−1))` shift，其 weight 是 `t+e+page−1`，等于原无限源 weight `(t+r−1)+e` 减去 `k=r−page`。它是传播后的同 weight crossing 检查。以原零层 `InfiniteNoCrossing` 替代这个实际条件，会重新引入本次失败的除 λ 步骤。

这些条件正好匹配已证 `gl_witness_square_high_filtration` 和 `gl_witness_square_detects` 的实际假设。经典 `NoCrossingOn` 分支的转换已有证明。但 **`LeftEdge` 仍须内部证明**；不能把指定 witness 匹配、整个方块结果包或结论本身加成假设来宣称完成。新增条件在本方案中的责任是实际几何 no-crossing 假设，其数学验证需要后续应用提供；报告将此适用性收缩明示给人类，不把它伪装成原 GL 的补证。

## 下游影响

| 项目 | 精确影响 |
| --- | --- |
| `Standard.generalizedLeibniz` / `GeneralizedLeibnizLaw` | 方案 A 不改；方案 B 改 Law 的两项前提与 theorem 证明组装，保留所有其他内容 |
| 四个原 crossing 谓词 | 两方案均保留原名称、类型、语义及导出；全局改定义会影响 MH2 和 Main，非建议默认修复 |
| 现有生产调用者 | 当前 `KIP126/` 没有实际应用 `generalizedLeibniz`；`Tests/ProofTools/Consumers.lean:17` 只整体消费 Law |
| `GeneralizedMahowaldLaw` / MH2 | 不调用 GL，仍使用旧 `FiniteNoCrossing`；本报告不修改它的前提或接手其证明；是否另有类似一般转换缺口应另行审查 |
| Main | `Main/InternalAudit.lean:372` 明确禁止 GL/MH2 依赖；Main 使用的 zero-layer νCofiber 结果及原 finite crossing 排空论证不变 |
| 已证私有辅助 | 保留有条件的 crossing 后果、source division、边界判断、方块和右边读取；不能把它们的编译状态改报为无条件提升完成 |
| `metadata/proof-tools-api.json` | B 获准后登记新增谓词及重捕获 GL；Law 正文语义变化可能不改变其 `…→Prop` 类型指纹，不能以锁不报错当作未改接口 |
| `metadata/proof-obligations.json:321` | GL 两洞未闭合前保留 pending；完成后再按实际 type/body 更新；Main 精确边界保留 |
| `ProofTools/InternalAudit.lean:154` | 当前只允许 GL 与 MH2 两个直接待补声明；只有 GL 真正无直接洞才调整，继续递归反循环检查 |
| Blueprint / hgraph / MEMO | 如改为 B，正式绑定条目必须陈述新充分条件；不能保留原论文正文、只在注释说改了。修正版与原一般命题应清楚区分；相应更新 `paper/ProofTools.tex` 的 GL 条目、`ed88d4e1610a` 附件、MEMO 的目标修正范围 |
| 测试 | B 获准后增加按精确前提逐项应用 GL 的普通导入测试；保留 interface、private 隐藏、Main 边界、Trust 审计。运行 inventory、`lake build`，必要时同步 Blueprint 精确绑定测试 |

下游影响部分另经只读 explorer `/root/crossing_interface_report/impact_audit` 检索；报告员也核对了实际 Law、witness、Main forbidden 列表和方块签名。没有通过变更宽入口、模型或责任边界避开问题。

## 循环、未证及矛盾依赖审计

* 有限程序和 Lean 算术证据不导入项目模型，不引用 `sorryAx`、GL 或 MH2；它们只验证列明的有限坐标关系。
* 谱识别的数学证据使用 May–Milgram、Pstrągowski、BHS 的上述比较/收敛，不使用一般 crossing 转换、GL、Mahowald 或其后续 Adams 计算。因此没有以争议结论证明自身反例的循环。
* 当前项目允许上游构造/文献有待补；本报告没有把这些待补自动当作已经实现的 HZ 对象证明。没有构造当前 model 的矛盾，也没有从 `False` 反推结论。
* GL 本地两个 `sorry` 仍属同一公开 theorem，MH2 仍独立 pending。Main 的局部无 GL/MH2 依赖边界不代表全部上游都无待补；本例不改变这一区分。
* Wu 的跨层版本及其对 LWX crossing 的转述存在不同边界指数/essential 说明。附存的 `wu-comparison.md` 可供后续研究；本报告的反例和方案均不以 Wu 的转述正确为前提。

## 阻塞范围与继续项

**确实不能继续当作已成立一般定理使用的目标**：从任意实际较大商 essential crossing 无条件构造 Definition 5.9 所需较小商 witness；由此推出的一般有限 no-crossing 转换；未截断的相同无条件除 λ 方案；原 Theorem 6.1 对一般谱且保持原前提的求证目标。不能将这些目标注册为新公理或上游债务以跳过。

**没有被本例逻辑否定的目标**：固定对象 GL 原接口、经典 differential-to-boundary 转换、`LeftEdge` 代表/shift 匹配、方块及右边读取、Main 当前路线。协调者已安排 `left_edge` 与其两个子任务继续独立匹配工作；本报告不接手或修改其文件。

因此，两处 GL `sorry` 仍未消除；它们不能通过本次失败的一般提升引理闭合。选择 A 后仍可在固定对象的特殊结构或适用于该闭包的另一证明路线中继续；选择 B 需明确人类授权后方可实施，且仍须完成剩余内部证明。

## 人类审核记录

尚无本报告方案的明确人类决定。`human_decision: null`。协调者或其他 agent 的数学同意、已有不同问题的批准、等待和沉默，均不计作本方案授权。


## 2026-10-19：当前泛型 5.10 的完整模型与同一 detector 自映射复核

本段由独立报告员 `/root/interface_reporter` 追加，未参与候选发现或实现。工作区为 `/inspire/hdd/global_user/czxs25250150/ops/tmp/prooftools-main-proofs-20261019`，起始提交 `0e940a5108088ad73a19415721060012a8aad779`；当前含其他 worker 的未提交补证。本轮读取当前规则及指定 protocol/template，只写本报告，不改源码、锁、corrections、旧 GL/MH 报告或人审记录；按用户安排不运行全量检查。

**结论：下述有限矩阵可由实际谱及完整的数学 Model 实现，构成当前任意 D 版本 5.10 的数学反例。** 模型采用 HF₂-local 谱与 hypercomplete HF₂-synthetic 谱，单位、ν、λ-localization 和实际塔整套相容。尚无 Lean `Model` 值或 Lean 否定证书，不能称为 kernel 已验证的完整反例，也不能称为固定 tmf `Standard.model` 的反例。

新涉及的 5.10 接口处置仍为 **`status=pending-human-review`、`human_decision=null`**。旧 GL/MH 删除授权不覆盖这条不同声明；本段不推测新授权，不改变文件头的原待审状态。

### 当前完整声明及真实前提

本报告原来的普通谱例子曾不能装入固定对象闭包。本轮目标后来公开为泛型 D；当前完整上下文、签名如下：

```lean
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn]
  [HasFunctorialCofiber (C := Syn)] (D : Model C Syn)
public theorem finiteCrossing_iff_syntheticCrossing (X Y : ClassicalObject)
    (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary)
    (r : ℕ) (n s t : ℤ)
    (x : Ambient D X (s,t)) (y : Ambient D Y (s+n,t+n))
    (he : FiniteExtension D X Y f r n s t x y) :
    FiniteHasCrossing D X Y f r n s t ↔
      ∃ a b : ℤ, s < a ∧ a ≤ b ∧ b ≤ s+n ∧
        ∃ (source : ((D.family.obj
          ((SyntheticObject.quotient (r-1) (extensionSourceObject D X Y f)).obj
            D.nu D.auxiliary)).sequence.ssData
          (a,(t-s)+a,t+normalizedExponent D.classicalTower f)).eInfty)
          (target : ((D.family.obj
          ((SyntheticObject.quotient (r-1) (.nu Y)).obj D.nu D.auxiliary)).sequence.ssData
          (a+(b-a),(t-s)+(a+(b-a)),t+normalizedExponent D.classicalTower f)).eInfty),
          target ≠ 0 ∧ TowerExtensionEquation
            (D.convergentMap (.quotient (r-1) (extensionSourceObject D X Y f))
              (.quotient (r-1) (.nu Y)) (finiteExtensionMap D X Y f (r-1)))
            (t-s,t+normalizedExponent D.classicalTower f) a (b-a) source target
```

没有隐含 `D=Standard.model`，原 he 不要求非零或 essential。`AuxiliaryData.detector : C` 没有 tmf 条件；因此可以在某一合法 generic D 内把 `.detector` 选为下述 M，**不需要新增 ClassicalObject 直和构造子**。这不是把固定 Standard detector 私自换掉。

左侧 `FiniteHasCrossing`：自然数 i,j，`0<i≤r−2`、`j≤n−i−e(f)`；同一 f 在 page r−i、length n−i−j、source `(s+i,t+i)` 上的真实 `FiniteExtensionWitness`；W.Essential 且指定经典靶不在 B_(1+n−j−e(f))。Witness 的全部字段含 page/length 界、指定标签的 cycle、同一实际 map 上的 E∞ source/target、两个标签代表比较及实际 equation。右侧则在同一大商 Q_(r−1)、固定 stem/weight，要求更高 source filtration 的非零靶 equation。右侧没有 essential 前提，但本例右侧也 essential；仅加 essential 不能修复。

### 完整 Model 的实际实现，而非只指定有限矩阵

取 H=HF₂，C=Ho(Sp_H)，tensor 为 H-localized smash，单位 S₂∧。取 Syn=Ho(hypercomplete Syn_H)，tensor 与单位也取 hypercompletion 后的版本。[Pstrągowski §5.1 Remark 5.5、Propositions 5.6–5.7](https://arxiv.org/html/1803.01804v3#S5.SS1) 提供这套 completed tensor、ν 的 locality 及 λ-invertible recovery：ν(S₂∧) 正是此 Syn 的单位，λ-inversion 恢复同一个 C。不能把 whole-Syn 的普通单位 νS 与 C 的完备单位混用。

令 E=Hℤ₂、T=H(ℤ/4)、M=E⊕T⊕E，`auxiliary.detector=M`、`detectorUnit=0`，其余 etaMap/nuMap 取真实 Hopf 映射，ν-cofiber 为在同一 C 中取的完备 Cν。零 detectorUnit 合法且未参与本计算。

报告员逐项读取 `System.lean` 以及 Context、Configuration、Tower、Detection、Comparisons、Recovery、Compatibility、Normalized、Sphere 和 witness 定义，核对 Model 的全部字段如下：

| 字段/实例 | 实际数学实现及核对 |
| --- | --- |
| StableHomotopyCategory、SyntheticCategory、HasFunctorialCofiber | 上述两个稳定范畴的同伦范畴；实际加法、双移位、tensor、三角和 λ。选定实际 cofiber 及方块填充满足两个结构箭头方程；当前 cofiber class 没有额外严格复合律要求。 |
| coefficients | C 中 H、π₀=F₂、其余 π=0；完备球谱到 H 的真实单位。 |
| classical、classicalTower、classicalSuspension | 实际 H coefficient tower、exact-couple 谱序列及同一塔的悬挂。TowerSequencePresentation 的 ambient/cycles/boundaries/differential 由该 exact couple 生产，不自由指定 d₂。 |
| nu、nuExactTriangle | usual ν 限制到 H-local 对象，取相容的单位、加法、悬挂比较；完整 homology short-exact 三角由 [Pstrągowski Lemma 4.23](https://arxiv.org/html/1803.01804v3#S4.SS2) 保持，没有把 ν 当任意 exact functor。 |
| recovery、exactness | 上述 hypercomplete λ-invertible recovery；同一双移位和 realization 的 exactness。 |
| auxiliary | M 是唯一 detector 对象，两份 E 分量独立；Hopf η、ν 与 ν-cofiber 真实，未用其他任选谱替换球谱。 |
| sphereAlgebra、standardClasses | S₂∧ 的真实 Adams Ext、F₂、乘法/单位、标准 hᵢ；Model 没有额外非零/永久结论字段。 |
| family、syntheticTower | 同一 νH coefficient tower 及其真实 synthetic Adams family；所有 weight 使用指定塔的 weight shift。 |
| comparison、firstQuotient | 实际 νE₂、Cλ/Ext 与 λ 自然比较；[Pstrągowski 4.56–4.58](https://arxiv.org/html/1803.01804v3#S4.SS6)、[BHS A.8](https://arxiv.org/html/1910.14116v3#A1.SS1) 识别同一谱页/代表，不另选标签或滤过。 |
| quotients | 同一实际 λⁿ cofiber 系统、ρ/λ/δ 三角及其自然性。 |
| normalizedMap（对全部 selected maps） | e=0 取 νf，带零移位比较；e=1 时第一 residual factorization 蕴含 H_*f=0，Pstrągowski 4.57 在 t=w=0 的精确列给 νf 的 λ-lift。对所有这种 map 选 lift 满足原 factorization；不只构造本例 map。 |
| classicalConvergence、convergence | 下文给所有选定对象及任意有限迭代 quotient/shift 的 canonical 强收敛；不省略全闭包。 |
| comparisonCompatible（两字段） | Canonical tower→associated-grade 比较对每个实际 map 自然，且 first quotient 检测由实际 reduction 诱导。 |
| sphereDetectionCompatible（两字段） | 同一球谱的实际 Cλ reduction 及实际 λ^k 检测；零 leading term 意味更高 filtration，仍在原范围。 |
| multiplicationCompatible、sphereProductCommutative | 同一 complete 球谱、multiplicative coefficient tower 与 composition product 的 canonical 检测比较；双分次球谱 coherence 采用 topological Koszul sign，没有换另一 E₂ 乘法或 abutment。 |

**任意迭代商/移位的收敛。** 经典生成谱 S₂∧、完备 Cν、M 均 bounded below、H-nilpotent complete 且 mod-2 finite type，整数移位保留这些性质。经典 Adams 各双次数有限，ML 成立；[BHS A.13、A.16–A.17](https://arxiv.org/html/1910.14116v3#A1.SS1) 给 νX 的 νH-nilpotent completeness 与强收敛。

对 local A，νH⊗A 是 νH-module，因而 local；actual Adams residual 由它与 A 的 fiber 得到，也 local。所以 whole-Syn 中这条塔已位于 hypercomplete 子范畴，completed tensor 不改变该塔或其 filtration。经典 H-local 塔同理。νH-nilpotent completeness 等价 `lim_s I^s⊗A=0`；各 I^s⊗− 及 inverse limit 保有限 exact diagrams，故该性质对有限 cofiber 与双移位封闭，覆盖任意有限次 λ 商与移位。[BHS A.14](https://arxiv.org/html/1910.14116v3#A1.SS1) 也直接给第一层有限商。

每个这样的对象是有限移位 νX 的有限 cone 构造。固定三次数的 coefficient/cobar 项有限维：生成谱的 mod-2 homology finite type，Steenrod cobar 在固定内部次数的贡献有限；固定 Adams 层及有限 cone/shift 保留有限性。于是每个 E₂ 三次数有限，后页只可能有限次发生非零进出微分，ML 障碍消失；BHS A.17 给整个有限构造闭包的 canonical 强收敛。这足以供应当前 Model 要求的 associated-grade identification 及同一代表的 canonical 方程，而不要求全范畴每个对象都强收敛。其对 map/乘法的相容来自同一真实 tower，未假定 5.10 或 GL/MH。

这是一套完整**数学模型**实现；没有提交 Lean Model 定义或 kernel 否定证明。把这套范畴构造形式化仍是未交付工程，不能用仓库上游 sorry 的任选结果代替。

### 实际群及地图的独立识别

报告员本次重新读取 [May–Milgram，Lemma 3(ii),(iii)、Lemma 4，p.129](https://math.uchicago.edu/~may/PAPERS/34.pdf)：Hℤ 有 h₀ 塔；T 有底 θ、顶 u 两塔，`d₂(h₀^k u)=h₀^(k+2)θ`；有限和分解。Hℤ→Hℤ₂ 的 mod-2 等价保留这些输入。

由 Cλ 长正合列、nonnegative-Chow 比较与上述 d₂/收敛，在 w≥1，π_(0,w)νE=ℤ₂，其 generator 吸收 realization 子群 2^wℤ₂，λ 在这些坐标为乘2；π_(0,w)νT=ℤ/2，λ 从正 weight w+1 到 w 为零；二者 π_(-1,w)=0。T 的 native 类为 h₀^wθ，F^w 是全群，F^(w+1)=0。w≥2 时此类虽为经典边界，在该 native synthetic weight 仍非零。

因此对 q≥1：

\[
G_{q,w}=\pi_{0,w}Q_q\nu M=\mathbb Z/2^q\oplus\mathbb Z/2\oplus\mathbb Z/2^q,
\quad F^wG=G,\quad
F^{w+j}G=2^j\mathbb Z/2^q\oplus0\oplus2^j\mathbb Z/2^q\quad(j\ge1).
\]

取同一个 self-map `f(x,t,z)=(0,jx,2x)`，j:E→T 为模4商映射。其 H₀(−;F₂) 的 j 分量非零，故不通过第一 residual stage，e(f)=0，normalized map 为带零移位识别的 νf。νj 在每个 native h₀ 底层非零，自然性给所有 q,w 的实际 map `f_(q,w)(x,t,z)=(0,x mod2,2x mod2^q)`。实际 λ:Q_(q−1)@weight(w+1)→Q_q@weight w 是 `(x,t,z)↦(2x,0,2z)`，方块交换。这些 map 没有独立任选；λ-kernel 中的 T 分量正是除 λ 的障碍。

### 全部真实前提和 crossing

| 条件 | 独立核验 |
| --- | --- |
| D、X、Y | 上述完整 generic 模型，X=Y=.detector=M；不主张等于 Standard.model。 |
| 参数范围 | r=4、q=3、n=2、s=t=1、e=0，合法 0≤2≤r−2；stem/weight=(0,1)。 |
| 原始 x、y | 分别为 `(1,1)`、`(3,3)` 的零标签；source reaches page4、target reaches page2。 |
| 原 he | source=target=0、所有实际 homotopy lifts=0，满足全部界、cycle、代表与 equation；接口允许 inessential 原输入。 |
| RHS 的整数 a,b | a=2、b=3，1<2≤3≤3。 |
| RHS source/target | 在 G_(3,1) 取 α=(2,0,0)∈F²∖F³，β=fα=(0,0,4)∈F³∖F⁴；canonical E∞ grades 位于 `(2,2,1)`、`(3,3,1)`，实际代表给 length1 equation，target≠0。 |
| RHS 全部靶歧义 | 同源 grade 的四个实际代表均映到 β，零靶不在完整 coset；故也 essential。 |

LHS 自然数 i,j 恰为三对，native source filtration/weight 为 1+i：

| i,j | q′、weight、length | 排除全部实际源/靶 |
| --- | --- | --- |
| 1,0 | 2、2、1 | 像在 F³ 强迫 x 偶，继而 2x=0 mod4，像整体零，无 essential extension。 |
| 1,1 | 2、2、0 | 唯一非零 target grade 是 h₀²θ，属于被排除的 B₂。 |
| 2,0 | 1、3、0 | 唯一非零 target grade 是 h₀³θ，属于 B₂⊆B₃，违反 B₃ 排除。 |

零 source grade 有零实际代表，故不能产生 essential extension；另外两分量在 f 的 kernel。length0 的 native target 分母 B₁=0，不能偷偷加自由 E 标签仍保持同一 grade；其他经典边界标签若 E∞ grade 零，也不 essential。这覆盖全部原始 E₂ 线性组合、实际代表及整个靶 coset。因此 RHS 真、LHS 假；成因为大商乘 λ 消掉 T 阻挡，而小商 native source 无法同步消去它，不是实现笔误或单纯缺证明。

### 本轮独立复现及证据局限

报告员重跑 `/tmp/crossing-proof-20261019/check_crossing.py`，exit0；又独立运行以下全源grade/全代表/coset枚举，不调用发现者的 Python 函数：

```sh
python3 - <<'PY'
from itertools import product
for i,j in ((1,0),(1,1),(2,0)):
 q,w,L=3-i,1+i,2-i-j
 G=list(product(range(2**q),range(2),range(2**q)))
 F=lambda a,k: k<=0 or (a[0]%(2**k)==0 and a[1]==0 and a[2]%(2**k)==0)
 gr=lambda a,k:(a[0]//2**k%2,a[1] if k==0 else 0,a[2]//2**k%2)
 mp=lambda a:(0,a[0]%2,2*a[0]%(2**q))
 fibers={z:set() for z in product(range(2),repeat=3)}
 for a in G:
  if F(mp(a),L): fibers[gr(a,0)].add(gr(mp(a),L))
 essential={s:ys for s,ys in fibers.items() if ys and (0,0,0) not in ys}
 assert all(ys=={(0,1,0)} for ys in essential.values())
 assert not essential or (L==0 and w>=2 and 1+2-j>=2)
 print(i,j,len(G),len(essential),'allowed targets after boundary=[]')
G=list(product(range(8),range(2),range(8)))
reps=[a for a in G if F(a,1) and gr(a,1)==(1,0,0)]
ys={(0,a[0]%2,(2*a[0])%8) for a in reps}
assert ys=={(0,0,4)}
print('RHS source representatives=',len(reps),'images=',ys)
PY
```

实际 exit0：三窗口枚举32、32、8个实际代表，essential source fibers 为0、4、4，边界排除后全部为空；RHS四个同源代表的像集合恰为 `{(0,0,4)}`。这是有限算术证据；全模型/谱识别由上面的独立数学构造承担，没有生成 Lean 完整模型证书。本轮只做必要局部计算，不运行全量 checks。

### 依赖审计、精确待决方案及非阻塞任务

独立证据顺序为 May–Milgram 的经典输入 → Pstrągowski 的真实 complete/synthetic 比较 → BHS 的塔/有限窗口/收敛 → 实际群与自然 map → 全 crossing 排除。没有调用 GL、MH、5.10、5.14、2.20、AdamsCalculations、Main 或相关 sorry 得到的结论；没有用不一致导出 False。Model 的所有字段在数学上逐项实现；Lean 实现和 kernel 运输仍未完成，不能省略这个证据边界。

先尝试保留原接口的内部方案：上述实际模型满足全部字段与真实前提后，任意-D 全称等价不能被正确证明。把 detector 默认为 tmf、忽略合法零 he、悄悄补 essential 或把 D 设成 Standard 都改变语义；本例 RHS 已 essential。仅该反例不推翻固定 Standard 版本，后者也未在此获证。

最小精确待审方案：撤销公共 theorem `KIP126.ProofTools.Paper.finiteCrossing_iff_syntheticCrossing`，即上述完整原签名对应候选签名为**无声明**；保留旧 `FiniteHasCrossing` 定义、反例及现有正确带层/有条件除 λ 工具。这是删除错误接口，不能记作证明原命题。若改用同商 actual crossing 或补 λ-kernel 同步条件，须另给完整可审准确签名和证明；本段没有准备好并批准该新 theorem。收窄为 Standard.model 是另一个仍未证明的候选，不能默认实施。

受影响范围为这一 theorem 的源码/导出、ProofTools API锁、对应待补登记、internal audit 精确许可洞集合、原声明消费者、Blueprint `paper:5.10` 与原生 Blueprint 测试；实施时保留其他 trust 覆盖与 Main 禁用边界。相对 AimPaper 的修正只由协调者维护于 `corrections.yaml`，本报告不平行保存修正版。其他模块公共接口、工具链和依赖锁均不在本方案内。

准确阻塞项为任意-D 5.10 的全称补证及其真实依赖闭包。5.14、2.20、Main 补证、灰色节点真实对应、actual level 工具及 λ-kernel 条件下的局部证明可继续；不能因这项反例自动宣称那些不同目标也为假。用户要求先补证、暂缓全量检查保持；无需重复确认旧 GL/MH 已批准范围。

### 本次源码身份与人审记录

以下为 dirty worktree 中读取快照，不冒称已提交或全量构建验证：

| 文件 | SHA-256 |
| --- | --- |
| `KIP126/ProofTools/Paper/OriginalStatements.lean` | `ac4eb11d31ef053edcaa8553eba5b959fd2349fcd092b8d1341b3f13a04da7cc` |
| `KIP126/ProofTools/Language.lean` | `50164249c50b08c58a5357e1aec2ea6035dd8043474e71b69082b56eed9cd7ee` |
| `KIP126/AdamsSynthetic/System.lean` | `2278a0714ba8f204e0d6e6f3f1e2bba838ec71adedade2916955ae58c39fffa4` |
| `KIP126/AdamsSynthetic/Configuration.lean` | `aca9ba1263dfecd248440a667461265fd7b0149430a74b5fdc342cd5cc47f1e1` |
| `KIP126/AdamsSynthetic/Compatibility.lean` | `69abbf22400a8b26f2189dc08a30e34185e590fee8ab64717e6cf42589ed97a3` |
| `/tmp/crossing-proof-20261019/check_crossing.py` | `6497ccf45c5d0848af7933c934e906b9a01f30c27cf570555de9490603433b32` |

新5.10处置请求的人类决定：**null**。本轮没有收到对此具体声明删除/改型的明确决定；历史其他批准或 agent 的数学意见不作为本项授权。实施交协调者安排。


## 2026-10-19 审查 PDF 交付与投递记录

协调者本次明确转达用户要求：制作解释原命题、完整全局条件、真实谱反例、全部 crossing 排除及修正版的具体 PDF，并发给 `project-math-assistant`。授权只涵盖本次审查材料制作/外发；**没有批准修改本条原文、公共声明或待补登记**。本报告保持 `pending-human-review`、`human_decision: null`，发送或agent数学核验不替代人审。

本地一次性交付为 `local-history/reports/20261019-prop510-review/Prop5.10-review-2026-10-19.pdf`（10页A4桌面），SHA-256 `b104aa87b322464c3b2cb79727f6fb5f66e795c238ecf733126fecbca39436eb`。同目录归档原生LaTeX、原签名/现有替代完整签名、有限脚本及JSON、source hashes、编译日志、QA/预览和发送回查。目录按仓库规则被Git忽略，其本地路径不是dashboard已托管附件；实际PDF附在下述飞书消息中。

PDF完整写出已证 `finiteLambdaDivision` 的实际小商 target-kernel no-crossing（含初始行）、保留同一个大商源及像的四项结论、固定Standard模型范围，以及它与旧iff不等价。另加入同一M的加强例 `f*(a,θ,c)=(4c,ja,2a)`：原he `h₀c→h₀³a` 非零essential，16个同源代表的完整target coset不含0；RHS四个代表与全部三个小商排除保持。加强例由本报告员提出，再经 `/root/independent_review` 独立核对完整前提并实际复跑枚举后纳入，不以提出者自检冒充独审。证据仍是谱级数学反例＋有限计算，无Lean完整Model或否定证书，非固定tmf detector反例。

最终PDF QA：missing-glyph=0、overfull=0、undefined=0；目视抽样最终页1、2、6、7、9、10，数学公式、反例、表格和完整接口附录正常。没有运行全仓检查；本报告员没有改数学源码、接口锁、待补或corrections。

投递通过user身份搜索唯一精确同名群：`project-math-assistant`，chat_id `oc_0757f47818759dc02c05b8dd370aa649`。首次user发送被飞书 `230027 user_unauthorized` 拒绝，未生成消息；随后只读确认当前应用bot已在同一群且可发言，以 **飞书CLI应用bot** 上传同一PDF并成功发送一条带附件post。没有重复发送失败的user请求。

- message_id：`om_x100b62682b77f880ce3610b758c7c9c`。
- [实际审查PDF消息](https://applink.feishu.cn/client/chat/open?openChatId=oc_0757f47818759dc02c05b8dd370aa649&position=1521)。
- 正文：“Prop5.10 原命题／反例／修正版提案，供审核；尚未授权改原文／接口。”另附10页A4及非Lean完整Model证书的说明。
- identity：`bot`；sender：`飞书 CLI`。
- 只读回查确认正文、文件名和消息附件；附件区资源key与上传key不同，进一步下载消息对应资源，SHA-256与本地PDF完全一致。证据见同目录 `delivery.json`、`message-readback.json`、`attachment-hash-verification.json`。

本次原5.10 theorem与待补责任保留；后续删除或改写须取得针对本项的明确人类决定，再由协调者实施。外发成功不改变人审状态。
