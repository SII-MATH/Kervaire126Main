# 6.20 固定原目标版本：第二轮证明探索

## 范围与结论等级

基线 `aad718722aa01dfce361f40645fc776037d1078f`。本轮只写本报告及 `WangBzeroProof.lean`，生产源码、接口、锁、待补清单不改。协议与上轮相同；共享工作区的其他变更由协调者管理。

新消息为群内 guozhen 的“一般的 b，可以推 b=0”。本轮实际尝试了固定原 `y`、`b=0`、保留非 liftable 源的完整 iff，重点核验能否改变代表来保持目标。没有找到该必要方向的证明；反而得到一个具体的 **HZ/16 实际谱候选及其完整系数计算路线**。下文严格区分：

- 整数/有限模数计算：9 条 Lean lemma 已实际检查通过，无 `sorryAx`。
- 实际谱到这些有限群的识别：给出三角、连接映射、约化与滤过的兼容推演；其中 HZ 的 HF₂-Adams 计算及 synthetic 对应尚未在当前 Lean 对象库构造，须独立审核，故本交付仍标 **条件性实际谱候选**。
- 当前 `ClassicalObject` 只有 sphere、nuCofiber、detector 与 shifts，没有下面的 HZ/16 对象。因此本文件不是现有固定 Lean 模型中的形式化反例，也不许可用它直接修改任何冻结接口。

## 为什么继续采用固定目标也有实质障碍

早页非本质性确实给出较高源实际类映到原目标余类；但这个实际类的首项可以 lift，而用来消去其映像低阶项的后续源可以不 lift。后续非 liftable 源首先命中的是被消去的低阶目标，而不一定是原目标。改变后续代表时若要重新命中原目标，可能必须加回那个较低 filtration 的 liftable 首项。

以下候选恰好实现这个机制；它比一般 filtered 方块更具体，因为使用实际 Eilenberg–Mac Lane 谱及其标准连接映射。这里不把分次上 `b=0` 的必然性当成存在固定目标非 liftable 源的证明。

## 谱、映射与参数

记 `E=Hℤ₂^∧`，`M=E/16`，取标准 distinguished triangle

\[
E\xrightarrow{16}E\longrightarrow M\xrightarrow{\delta}\Sigma E.
\]

令

\[
X=\Sigma E_x\oplus\Sigma E_u\oplus M,
\qquad
Y=\Sigma E_z\oplus\Sigma E_y.
\]

定义实际谱映射（各矩阵项均为 E-module 映射，因而也是谱映射）

\[
f(x)=8y,\qquad f(u)=2z,\qquad
f|_M=(\delta,2\delta).
\]

这些谱 connective、2-complete、mod-2 finite type。记两个悬挂 E 源的 Ext 首类为 `x,u`，M 的顶类为 `v∈Ext^{0,1}`、底类为 `w∈Ext^{0,0}`，两个靶首类为 `z,y₀`。取

\[
(s,t)=(0,1),\quad n=3,\quad r'=5,\quad r=7,\quad
y=h_0^3y_0\in Ext^{3,4}(Y).
\]

`δ` 在 mod-2 同调上非零，故 `AF(f)=0`、`e(f)=0`。合法域满足 `0≤3≤5−2`。这里的同一个原目标始终是 `h₀³y₀`，不把 `z` 改名为 `y`。

## HZ 输入及其需要的核验

所需标准 HF₂-Adams 输入为

\[
H^*(E;\mathbf F_2)=A//E(Sq^1),\qquad
Ext_A(H^*E,\mathbf F_2)=\mathbf F_2[h_0],\quad |h_0|=(1,1).
\]

此处 change-of-rings 是对 HF₂-Adams 的实际 Steenrod 模计算，不是把 HZ-module 的 2-adic filtration 未经识别当成 HF₂-Adams filtration。由单条 stem-0 tower、`π₀E=ℤ₂`、乘 2 在同调上为零以及塔强收敛，得到 Adams filtration 恰为 `2^aℤ₂`。没有其他 stem 的 Ext 类可贡献到本计算。

此实际 ASS 输入有直接一手来源：[J. P. May 与 R. J. Milgram, *The Bockstein and the Adams Spectral Sequences*, Proc. AMS 83(1), 1981](https://math.uchicago.edu/~may/PAPERS/34.pdf)，印刷页 129 的 Lemma 3(ii)(iii) 分别给出 `HZ/2^r` 两条 h₀ spike 及 `d_r`、HZ 的单条 spike 和 `E₂=E∞`；Lemma 4 给出楔和的直和。协调者本轮已读取该三页原文；因此 `HZ/16` 的 `d₄` 有实际谱依据，不仅是一般 filtered-complex 类比。该来源不替代下文 synthetic δ/ρ/f 的兼容核验。

依 AimPaper Theorem 4.1/rigidity（`main.tex:799–807`）及 λ-Bockstein 对应（`:814–823`），相应 synthetic 图为 `h₀,λ` tower，`λh₀=2`；固定 weight `w≥0` 的

\[
\pi_{0,w}(\nu E)=h_0^w\mathbf Z_2,
\qquad
F^a\pi_{0,w}=2^{\max(a-w,0)}h_0^w\mathbf Z_2.
\]

其他 stem 的 synthetic homotopy 为零。这个结论需连同强收敛/hidden 2-extension 一并核验：tower 的 `λh₀=2` 来自原 2 的 h₀ 检测，而非任选一个乘法结构。本报告没有在当前 Lean 标准对象中构造 E 或这个识别。

## 归一化三角逐项核对

对 `16:E→E`：mod-2 同调映射为零，`AF(16)=4>0`，故 `e(16)=1`。由同调长正合列，`E→M` 在 mod-2 同调上注入且非零，`δ:M→ΣE` 满射且非零，因而它们的 `e` 都是 0。于是 `e(16)+e(ι)+e(δ)=1`。

AimPaper `not:fhat`（`:946–964`）及其后归一化三角（`:966–971`）适用，给出

\[
\Sigma^{0,1}\nu E\xrightarrow{\widehat{16}}\nu E
\longrightarrow\nu M\xrightarrow{\nu\delta}\Sigma^{1,1}\nu E.
\]

在所需固定 weight 的 homotopy 上，`λ·widehat{16}=16`，`λ` 是自由 Z₂ tower 间的单射，故此处 `widehat{16}=16/λ=λ³h₀⁴`。不必假设在所有 synthetic 映射群中有全局唯一除法。

重要的是整条归一化三角的兼容，而不是仅有某个没有指定箭头的 `νM≅cofib(widehat{16})` 同构：连接就是 `νδ`，没有额外 λ，因为 `e(δ)=0`，且 `νΣE≅Σ^{1,1}νE`。

仓库相关上游声明位于 `Literature/Triangles.lean`、`Literature/Standard.lean:1324`。当前这些声明只对已选 `ClassicalObject` 工作；本候选不能把未在库内表示的 E/M 偷换进去调用。

## 有限 λ 商、δ 与 ρ 的兼容识别

写 `Q_q(T)=T/λ^q`。在 `νE` 的 weight 0 和 weight 1 上，λ^q 作用按上述基底都是乘 `2^q`，且单射。因此

\[
\pi_{0,0}Q_q(\nu E)=\mathbf Z/2^q,
\qquad \pi_{0,1}Q_q(\nu E)=h_0\mathbf Z/2^q,
\]

这些有限商仍没有 stem 1 的额外贡献（长正合列中的相关核为零）。`Q_q` 是 cofiber/tensor 构造，在稳定范畴保持 distinguished triangle。将上一节三角作用 `Q_q`，固定 stem 1、weight 1 的连接正合列给出

\[
\pi_{1,1}Q_q(\nu M)
\xrightarrow[\text{injective}]{\nu\delta}
\pi_{1,1}Q_q(\Sigma^{1,1}\nu E)=\mathbf Z/2^q
\xrightarrow{8}
h_0\mathbf Z/2^q.
\]

最后系数是 **8**：`widehat{16}(1)=8h₀`。故连接像是

\[
K_q:=\ker(8:\mathbf Z/2^q\to\mathbf Z/2^q).
\]

特别 `K₄=2ℤ/16`、`K₆=8ℤ/64`。这个 K 坐标直接由指定 `νδ` 取得，非另选的抽象群同构。

商约化 `ρ:Q₆→Q₄` 与整条三角及 `νδ` 自然交换，因此这些坐标里的 ρ 就是模 16 约化；`K₆→K₄` 像为 `8ℤ/16`。在两个悬挂 E 分量也是通常约化。

## Adams 滤过兼容与全部非 liftable 首项

M 的实际 HF₂-Adams 图应由三角/Bockstein 算得

\[
Ext(M)=\mathbf F_2[h_0]\{w,v\},\quad |w|=(0,0),\ |v|=(0,1),
\qquad d_4(v)=h_0^4w.
\]

`d₄` 也可以由上节 `widehat{16}=λ³h₀⁴` 的 λ-Bockstein 直接读出；不借用 6.20。有限商的 `λ^a h₀^a v` 在 weight 1 的存活条件是 `a+3≥q`，对应 K 坐标中 `2^a` 的实际类。δ 在其关联分次上发送 `h₀^a v↦h₀^a`，因而这不是仅保持群的同构，而是把 δ 的 HF₂-Adams filtration 与 K 中的 2-adic valuation 对齐。

也可直接使用 AimPaper finite E∞ 描述（`:842–869`）：它给出 `λ^a h₀^a v∈E∞(Q_qνM)` iff `h₀^a v∈Z_{q−a}`，对于 `d₄` 正是 `q−a<4`。原文 `x′∈Z_{r′−1−a}\setminus Z_{r−1−a}` 在这里等价于

\[
1\le a\le3,\quad a+3\ge4,\quad a+3<6,
\]

即 **a=1 或 2**，且首项包含非零 v 分量。a=3 的所有源首项都已可 lift。x、u 两条永久 tower 在每个 a 都可 lift；给非 liftable 首项加入它们，不能取消 v 分量。

本节要求的准确 Ext/δ 计算仍交独立审核，尤其需排除额外 Steenrod-module Ext 和任何未记录的同度类；不能凭裸有限群就认定滤过兼容。

## 实际 f 的矩阵及 essentiality 计算

在 `π₁,₁` 上，两个源悬挂 E 分量、两个靶悬挂 E 分量坐标都是 `ℤ/2^q`，M 坐标 `v∈K_q` 由上述连接定义。ν 保持有限双积及加法，故指定 f 的有限商映射是

\[
(x,u,v)\longmapsto (z,y_0)=(2u+v,\ 8x+2v).
\]

它与 ρ 自然交换，因为每项均来自实际 νf。目标 `λ³h₀³y₀` 对应 `(0,8)`。

**晚页 r=7。** q=6 时 v 坐标必为 8 的倍数。所有源 F¹ 元素的 x 坐标为偶数，所以其 y₀ 坐标 `8x+2v` 都是 16 的倍数。原源 x 的像是 `(0,8)`，在目标 F³/F⁴ 中非零；且任何高源修正都不能改变这个非零 y₀ 首项。因此原 extension essential。这里同时使用整个目标不定性，并非只检查 y≠0。

**早页 r′=5。** q=4 时 `(x,u,v)=(0,−2,4)` 是合法高源实际类，映到 `(0,8)`。其源首项在 AF1，是 `h₀u`，可以 lift 到晚页。于是早页原目标属于较短 ESS 像，原 extension inessential。

**为何没有到同一个 y 的非 liftable 短方程。** 对 a=1、2，非 liftable 首项的 v 系数分别为 `2^a·odd`。同一 filtration 的 u 项在 z 坐标只贡献 `2^{a+1}` 的倍数，x 项不贡献 z；更高源修正同样不能取消 v 的 z 首项。因此 f 像的 z 坐标分别为 `2 mod 4` 或 `4 mod 8`（乘任意奇单位），不能达到目标 AF3，更不能命中仅有 y₀ 分量的指定原目标。a=3 没有非 liftable 首项。至此排除了全部 `0<a≤n−e=3` 的候选。

在先前早页短方程中，`−2u` 的 z 首项 `−4z` 由 `4v` 的 `4z+8y₀` 消去；这个非 liftable v 首先命中 z，即原迭代的较低目标，而非同一个 y。这正是迭代不能保持固定目标的机制。

## 实际检查及交付界限

`WangBzeroProof.lean` 包含 9 条 private lemma：K₄/K₆ 核条件、早消去式、晚高源 y 坐标的整除性及不能命中 8、a=1/2 非 liftable z 首项不能消失、非 liftable 的窗口范围、合法长度。

已实际运行（没有 `-o`，不写生产 `.olean`）：

```sh
lake env lean metadata/interface-reviews/ProofTools/20261017-paper-prop620-domain/evidence/WangBzeroProof.lean
```

沙箱启动不可用，按协调者允许使用 `require_escalated`；最终 exit code **0**。全部 `#print axioms` 至多 `[propext, Classical.choice, Quot.sound]`，没有 `sorryAx`，没有新增公理。它们是纯整数/模数计算，**没有证明上述实际谱到有限模型的识别**。

实际未完成责任不是一条凭空可调用的新上游假设：需要独立核实 HZ 的实际 HF₂-Adams/ν tower 输入，以及 16 归一化三角对 δ、ρ、f、滤过的上述兼容；本报告提供逐项推导供审核。若这些识别核实成立，候选反驳的是“早页 inessential ⇒存在非 liftable 首项命中固定原 y”的新增必要方向。它不反驳合法域自然性，也不是现有固定 Lean `ClassicalObject` 中的形式化反例。未经进一步核验，不应对外宣称已推翻实际谱定理。
