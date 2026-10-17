# 王老师对命题 6.20 修正的独立核验

核验日期：2026-10-17。基线：`aad718722aa01dfce361f40645fc776037d1078f`。
任务：独立核验首段增加 `n ≤ r′−2+e(f)`、第二段将 `y′` 换成原 `y`。核验者未参与本轮候选实现，只写本文件，不修改论文、生产 Lean、接口锁、责任清单或历史报告。按 `AGENTS.md` 及 `/root/.agents/skills/kip-upstream-session/references/protocol.md` 执行。

## 结论

1. **首段范围修正通过陈述核验。** 加上 `n ≤ r′−2+e(f)` 恰好补足定义 5.4 的早页长度上界。连同 `2 ≤ r′ < r`、原扩张和原定义中已有的 `e(f) ≤ n`，早页扩张处于合法域。该结论不需要修改 `f`、`x`、`y`、长度或固定模型。
2. **第二段不能只作 `y′ → y` 文本替换而保留现有的 `b ≥ 0` 公式。** 当 `b > 0` 时，短扩张的目标与原 `y` 处于不同的双分次；直接替换后的公式不是同一齐次分量上的方程。只有 `b = 0` 时，这项分次障碍消失。
3. **把 `b` 同时限定为零能否保留完整 iff，目前未决。** 本次没有证明，也没有实际谱对象反例。原文迭代最后明确得到 `b > 0` 和另一个目标 `y′`，不能把这段证明直接当作固定原 `y`、非 liftable 源版本的证明。
4. 所以可以接受第一项，第二项宜解释为对**直接命中原目标的判据**的提示；在完整 crossing/迭代公式中仍需确认作者希望如何处理 `b` 和变化后的目标。不能据此把完整 6.20 记为已完成。

## 原文与完整条件

源为 `AimPaper/main.tex:1981–1993`（`prop:dec738d3`）。保留同一 `f : X → Y`、同一 `s,t,n`，原扩张的条件为：

\[
x\in Z_{r-1}^{s,t}(X),\quad
y\in Z_{r-1-n+e(f)}^{s+n,t+n}(Y),\quad
e(f)\le n\le r-2+e(f),\quad
d_n^{f,E_r}(x)=y.
\]

首段修正后的早页域为

\[
2\le r'<r,\qquad n\le r'-2+e(f).
\]

第二段原先还要求晚页原扩张 essential，并量化

\[
0<a'\le n-e(f),\qquad
x'\in Z_{r'-1-a'}^{s+a',t+a'}(X)
\setminus Z_{r-1-a'}^{s+a',t+a'}(X).
\]

印刷公式为

\[
d_{n-a'-b}^{\hat f_{r'-1}}(\lambda^{a'}x')
=\lambda^{n-b-e(f)}y',\qquad b\ge0.
\]

其 `y′` 没有在该段单独量化和定型。若按前面 crossing 的定义补齐，`AimPaper/main.tex:1437–1440` 给出的条件是：

\[
0\le b\le n-a'-e(f),\qquad
y'\in Z_{r'-1-n+b+e(f)}^{s+n-b,t+n-b}(Y)
\setminus B_{1+n-b-e(f)}^{s+n-b,t+n-b}(Y),
\]

并且所称 crossing 是 essential 扩张。`a′ ≤ n−e(f) ≤ r′−2` 也保证其较小商页合法。单写 `b ≥ 0` 没有显式保证 differential 长度和 λ 指数合法；这些范围不能在 formal statement 中靠读者猜测。这里列出的是前文 crossing 的完整条件，不声称它们已经证明原第二段 iff。

## 分次证据：为什么一般不能令 y′ = y

论文 `:806` 明确规定 `λ` 的三分次是 `(0,0,−1)`，因此乘 λ 不改变 Adams filtration 或内部次数。原 `y` 的双分次是 `(s+n,t+n)`。

另一方面，源 `λ^{a′}x′` 的双分次是 `(s+a′,t+a′)`；ESS 的 `d_m` 把这两个分量都增加 `m`（`:270`，及 `:1290–1293`）。令 `m=n−a′−b`，目标必须位于

\[
(s+a'+m,t+a'+m)=(s+n-b,t+n-b).
\]

这正是前面 crossing 定义明确写出的 `y′` 分次。直接用 `y` 替代后，右端仍在 `(s+n,t+n)`，不能通过乘 `λ^{n-b-e(f)}` 把它变成 `(s+n-b,t+n-b)`。相等需要 `b=0`；不能把不同分次的零元也不经同一分量的识别而直接代入 Lean 齐次方程。

同一问题也反映在 weight：固定归一化源的 weight 为 `t+e(f)`。合法 `y′` 的右端 weight 是 `(t+n−b)−(n−b−e(f))=t+e(f)`；换成原 `y` 后成为 `t+b+e(f)`。因此 `b>0` 时三个指标都不匹配，而非记号名称上的争议。

生产 Lean 对此保持严格定型：`KIP126/AdamsSynthetic/Extension.lean:124–138` 的 `TowerExtensionEquation` 和 `TowerEssentialExtension` 将源定在 `(s,p.1+s,p.2)`，靶定在 `(s+n,p.1+s+n,p.2)`。取 `p=(t−s,t+e(f))`，短源 `s+a′` 和长度 `n−a′−b` 必须用靶分量 `(s+n−b,t+n−b,t+e(f))`，没有任何公共 regrade 允许无证明地改成原目标分量。

这些公共定义的宇宙保持源码中的 `Syn : Type u`、hom 宇宙 `v`、`SyntheticCategory.{u,v}` 与 `HasFunctorialCofiber`；`F,P,g,cx,cy` 仍为同一映射及 convergence。有限页的外层结构保持 `C : Type u`、`Syn : Type w`、公共 hom 宇宙 `v`、两个稳定/合成范畴实例及同一 `D : Model C Syn`。此次核验没有实例替换、退化模型或新对象关联。

## 原证明的目标确实在迭代段变化

`:2006–2013` 的第一步写的是

\[
d_{n-a}^{\hat f_{r'-1}}(\lambda^a x')
=\lambda^{n-e(f)}y.
\]

这里确实是**同一个 y**，也正是 `b=0` 的形式。因此王老师的意见对这一步具有直接对应。

但 `:2060–2066` 随后处理的情况不同：源在约化像中，却在晚页支持一个**严格更短的 essential extension**。正文要求继续迭代，最终写出 `b>0` 及 `λ^{n-b-e(f)}y′`。缩短后的目标 filtration 已降低，前面的分次核对迫使它换成另一分次的目标。不能在没有新论证的情况下断言这段迭代保持原 `y`。

目前还需要证明：若限定同一 `y`、`b=0`，能否始终选到满足所写经典 `Z` 差集的非 liftable 源；以及这种源的存在是否充分推出原早页扩张 inessential。原文的初始直接目标判据和最终 nonliftable-crossing 判据不能直接混为一个断言。

## 可依赖内容与证明状态

生产 `FiniteExtensionWitness` 的 `length_upper`（`ExtensionWitnesses.lean:26`）直接要求 `n ≤ r−2+e(f)`，不借任何上游证明就能判定域条件。`PageExtensions.lean:22–32` 把扩张与 essential 关联到同一个 witness、实际商映射及同一 source/target。

生产 `Extension.lean:105–113` 已有同一方程前提下的 `essential_iff_no_zero_target`；`SpectralSequence/Consumer/Extension.lean` 中 `Relation`、`TargetCoset`、`Essential` 真实定义保留指定目标的同次不定性。历史证据 `IndependentChecks.lean` 通过实际方程加减给出 `¬ Essential x y ↔ Relation 0 y`，这是固定目标的精确判据；它未证明经典非 liftable 源条件。本轮检查了该证明体，但未重新运行其 kernel 检查，也不把历史日志当作本轮新验证。

本轮未构造或核验完整 6.20 候选，没有需要声称已消除的本地责任；也没有新增公理、`sorry`、上游待补或对终极目标的调用。完整降页自然性在标准模型中仍会依赖已登记的模型/比较/收敛上游责任，不能把泛型的分次算术核对当成这些实际对象的构造证明。

## 实际检查、哈希和局限

实际执行：读取仓库规则与 protocol；读取完整 6.20 及证明、定义 5.4、crossing 定义和对应公式、λ 分次约定；读取上述生产 Lean 的真实声明及依赖入口；读取现有精确目标证据证明体；`git rev-parse HEAD`；`git diff HEAD --` 检查所列论文/接口/生产文件（结果无差异）；`sha256sum` 固定以下输入。

| 文件 | SHA-256 |
| --- | --- |
| `AGENTS.md` | `d5698d8dc344a07d7e3483b47b8284ef9a3188869273534dc7d8a0b90d82dce2` |
| `AimPaper/main.tex` | `828ee5a5aa06e1f390b036a043230ed417446fa7be11a4e27eecc4a565135c4b` |
| `KIP126/AdamsSynthetic/Extension.lean` | `23f48a534f4761af2b6994a0a10237fdf3efb6d5749c83251cbeb84b06d3c652` |
| `KIP126/AdamsSynthetic/ExtensionWitnesses.lean` | `2864cf03dae40fc24ad69f16026499e9b15a03b82a3ecddab0414c3b82d8a0ea` |
| `KIP126/AdamsSynthetic/ExtensionLabels.lean` | `12f363acefef0b05aab6c55222b62a740bcc7952d2586050bb985986bc49e87b` |
| `KIP126/AdamsSynthetic/PageExtensions.lean` | `902c670ec9234a2ac1e04f47e4bf844cf38485eebd84109f58395789d3fa89a4` |
| `metadata/proof-tools-api.json` | `364f271cba9f80d4452dac3a0e4370d5a556c60aaa18b76ad48a65e9ae384968` |
| `metadata/adams-synthetic-api.json` | `272bde79ba9a1e734ea462bcf5744831333d2f42ade891fb6f7c64402e78554b` |
| `metadata/proof-obligations.json` | `be2c30804b01991af0731aeaa0619b1738ccf93f0ac76c4271b4945844dd2aad` |

没有运行构建或修改构建状态：本任务是只读独立核验，未获协调者本轮构建写入调度；本文件是唯一交付写入。没有改接口、批准调整、发送飞书或作出论文定理为假的结论。

可继续项：首段按合法域完成独立候选核验；第二段先确定“同一 y 的直接判据（无 b）”还是“迭代后的不同目标 crossing（保留 b）”这一精确陈述，再分别核验完整双向证明。
