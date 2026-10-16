# 原论文备忘

记录原论文阅读与形式化过程中发现的问题、反例及修正方向。条目注明版本、原文位置和验证状态。

## 2026-10-16：广义 Mahowald trick 的降层障碍

**对象与出处。** 沿用原文的约定：素数为 2，所有谱均为 2 完备的 connective finite-type 谱。讨论 Lin–Wang–Xu, *On the Last Kervaire Invariant Problem*, [arXiv:2412.10879v2](https://arxiv.org/html/2412.10879v2) 的 Theorem 6.12。仓库原文见 [AimPaper/main.tex](AimPaper/main.tex)，标签 `thm:158d451a`；相关定义为 Notation 2.2、Definition 5.4、Remark 5.7。

### 反例

旋转同伦元素 $\nu:S^3\to S^0$ 的余纤维三角：

$$
X=S^0\xrightarrow{f=j}Y=C\nu\xrightarrow{g=p}Z=S^4
\xrightarrow{h=-\Sigma\nu}\Sigma X=S^1.
$$

取

$$
(e(f),e(g),e(h))=(0,0,1),\qquad
(n,m,l,s,t)=(1,0,2,1,16).
$$

于是 $(n_1,m_1,l_1)=(1,0,1)$，$r=r'=3$。令

$$
x=b=d_2(h_4)=h_0h_3^2\ne0\in E_2^{3,17}(S^0),
\qquad \bar x=y=\bar y=0.
$$

其中 $\bar x\in E_2^{1,16}(S^4)$、$y\in E_2^{4,18}(C\nu)$、$\bar y\in E_2^{4,18}(S^4)$，而 $h$ 的目标为 $\Sigma b\in E_2^{3,18}(S^1)$。所有 cycle 条件成立，四项前提分别为：

1. $h$-延拓的目标 $\lambda\Sigma b$ 位于 $Z_1/B_2$，因 $b\in B_2$ 而为零，故 $d_2^{\hat h_2}(0)=\lambda\Sigma b=0$。
2. $d_3(0)=0$。
3. 采用 Adams 微分的 no-crossing 分支。按 Definition 4.14，唯一可能的 crossing 是从 $E_2^{2,17}(S^4)\cong\operatorname{Ext}_{\mathcal A}^{2,13}(\mathbb F_2,\mathbb F_2)=0$ 出发的 $d_2$，故不存在。
4. $d_0^{p,E_2}(0)=0$。

### 结论不成立

原结论要求存在 $y'\equiv0\pmod{B_3}$，使 $d_1^{j,E_3}(b)=y'$。但余纤维的 Ext 长正合序列包含

$$
\underbrace{\operatorname{Ext}_{\mathcal A}^{2,17}
(\Sigma^4\mathbb F_2,\mathbb F_2)}_{
\operatorname{Ext}_{\mathcal A}^{2,13}(\mathbb F_2,\mathbb F_2)=0}
\longrightarrow E_2^{3,17}(S^0)
\xrightarrow{j_2}E_2^{3,17}(C\nu).
$$

故 $j_2(b)\ne0$。在 $\nu(-)/\lambda^2$ 的底权上，synthetic $E_\infty$ 为 $Z_2/B_1=Z_2$，于是 $d_0^{\hat j_2}(b)=j_2(b)\ne0$。因此 $b$ 不在所需 $d_1$ 的定义域中，与目标如何修正无关。

Definition 5.4 明确取源的 $k=0$ 层，即源只模 $B_1=0$；不能将这个源改读成经典 $E_3=Z_2/B_2$ 中的零类。故此例直接适用于原文明示的定义。

### 修正方向与验证状态

建议在原四项之外增加候选条件 **（5）源已属于所需延拓微分的定义域**：令 $Q=n+m+e(h)$、$F=\hat f_Q$，要求 $x\in Z_Q(X)$，且其底层 synthetic 标签 $x_0\in{}^F Z_{n-1}$。本例 $n=1$ 时，这恰要求 $j_2(b)=0$。

条件（5）排除此反例；它是否足以恢复一般情形的完整目标同余，仍需证明。另一方向是保留 $l_1$ 层延拓，将降层单列为引理。可对照 [Wu, arXiv:2606.02779v2](https://arxiv.org/pdf/2606.02779v2) 的 Theorem 4.23 与 Remark 4.25；后者的降层另要求 $f_2(x)=0$ 及边界商条件。

形式化反证为 [StatementReview.lean](KIP126/Def/ProofTools/GeneralizedMahowald/StatementReview.lean) 中的私有定理 `rotated_nu_generalized_mahowald_law_false`；前提与非零性分别见同目录 `RotatedNuPremises.lean`、`BottomNuInjection.lean`。反证调用既有登记的上游接口，不调用待证 MH2 或 GL。代码已收入提交 `b4b439f`；公共接口未修改，MH2 的原始 `sorry` 保留。Main 当前使用的实例为 $l_1=0$，本反例为 $l_1=1$。

### 发现思路

补写 MH2 时，证明推进到带层关系

$$
d_n^{\hat f_r}(\lambda^{l_1}x)=\lambda^{r'-1}y.
$$

原证明末尾直接消去 $\lambda^{l_1}$。检查这一步时，注意到商映射

$$
\lambda:Z_2^{3,17}/B_1^{3,17}\longrightarrow Z_2^{3,17}/B_2^{3,17}
$$

杀掉非零的 $b=d_2(h_4)$。于是取 $l_1=1$，让 $h$-前提只看见 $b\bmod B_2=0$；再选旋转的 $\nu$ 三角，使底映射在 $b$ 上单射。取其余标签为零后，前提成立，而结论的指定源被最低延拓微分阻挡。问题定位在原文证明末尾的 “by dividing $\lambda^{l_1}$” 步骤（本地 `main.tex` 第 1913 行）。
