# Proposition 6.20：王老师建议的证明 worker 核验

任务基线为 `aad718722aa01dfce361f40645fc776037d1078f`。本 worker 只读生产文件；本报告及同目录 `WangCorrectionWorker.lean` 是唯一交付。没有改论文、公共接口、接口锁或待补清单。已读仓库 `AGENTS.md` 及 `/root/.agents/skills/kip-upstream-session/references/protocol.md`。

## 本次结论

1. 第一段增加 `n ≤ r′−2+e(f)` 正好修复 Definition 5.4 的适用范围；已有合法域下降候选可用，不需要改动 extension 定义。
2. **第二段不能在保留任意 `b≥0` 时直接把 `y′` 替成原来的 `y`。** 当 `b>0` 时，这个替换不符合论文规定的三重分次。若固定同一个 `y`，式子必须同步取 `b=0`，改成
   \[
   d_{n-a'}^{\hat f_{r'-1}}(\lambda^{a'}x')
     =\lambda^{n-e(f)}y.
   \]
3. `b=0` 只修复分次，并不证明包含“非 liftable 源”的完整 iff。该方向尚未完成，不能将它公开登记为已证的 Proposition 6.20。

## 来源与分次计算

已从头读取 `AimPaper/main.tex:1981–2075`，Definition 5.4（`:1301`）、ESS 定义（`:270–319`）、Remark 5.6（`:1386`）、Definition 5.9（`:1437`）及其 crossing 解释（`:1515–1536`）。

论文 `:806` 明确规定：经典 `Ext^{s,t}` 的初始 synthetic 三重分次是 `(s,t,t)`；`λ` 的三重分次是 `(0,0,−1)`。ESS 的 `d_m` 将前两项增加 `m`，保持 synthetic weight。

令 `e=e(f)`。第二段源 `λ^{a′}x′` 的实际源分次，在归一化 `e` 移位后是

\[
(s+a',\ t+a',\ t+e).
\]

因此 `d_{n-a′-b}` 的靶必须位于

\[
(s+n-b,\ t+n-b,\ t+e).
\]

若 `y′` 具有 Definition 5.9 规定的经典分次 `(s+n−b,t+n−b)`，则

\[
|\lambda^{n-b-e}y'|
=(s+n-b,t+n-b,(t+n-b)-(n-b-e))
=(s+n-b,t+n-b,t+e),
\]

完全匹配。这也说明原证明迭代末尾的 `y′` 可以是较低 filtration 的新目标。

但原 `y` 的经典分次固定为 `(s+n,t+n)`，因而

\[
|\lambda^{n-b-e}y|
=(s+n,t+n,t+b+e).
\]

它与所需靶分次相等当且仅当 `b=0`。这一判断是三重分次的整数恒等式，不借用目标命题、不依赖标准模型的待构造字段。

同目录 `WangCorrectionWorker.lean` 逐条表达上述算术：

- `fixed_y_degree_iff`：字面替换成固定 `y` 的三重分次匹配 iff `b=0`；
- `crossing_yprime_degree`：采用 Definition 5.9 的 `y′` 分次时全部坐标匹配；
- `crossing_length_range`：较短 extension 的合法下界等价于 `b≤n−a′−e`；
- `fixed_y_bzero_degree`：`b=0` 时的固定目标公式匹配。

这些辅助声明均为 private，仅是证据。没有构造任何所谓实际谱反例。

## 自顶向下的证明拆分及尚未完成步骤

在给定同一实际模型、同一个 `f,x,y` 及晚页 essential extension 的条件下：

1. 合法域中的自然性给出早页 extension。这一段已有 `ReviewedExtensionDescent.lean` 的候选证明；本次未更换任何模型或定义。
2. 早页 inessential 的精确含义，是**原目标** `λ^{n−e}y` 在早页 ESS 的较短微分像中。既有 `IndependentChecks.lean` 已证明同一 equation 下的零源/同目标判据，而论文 Proposition 2.2 给出较高源命中同一目标的表述。
3. 若找到的较高源已经不在晚页约化像中，就直接得到 `b=0` 的非 liftable 源。
4. **未完成情形**：这个源的首项可以 lift 到晚页，但其晚页映射可能首先在比原 `y` 更低的 filtration 检出一个新目标 `z`。为使早页原短方程存在，这个 `z` 必须在早页被进一步修正消去。沿此迭代提取的非 liftable 源命中的首先是 `z`，其分次为 `(s+n−b,t+n−b)`，通常正是论文末尾的 `y′`，`b>0`。

因此原文迭代没有给出“最终非 liftable 源仍命中同一个 `y`”的证明。把最后的 `y′` 改成 `y` 并令 `b=0` 后，必须另外证明可以保持原目标的非 liftability 提取引理；本 worker 没有该引理，也没有识别到实际谱对象中的反例。一般 filtered 方块的首项消去并不能自动提供这个引理，不能据此替换实际谱模型。

相反，只要已经有 `a′>0` 的短 equation 命中同一个原目标，原目标就是早页的较短 ESS 像，故推出早页 extension inessential。这个充分方向不需要非 liftability。尚未证明的是带指定非 liftable 源的必要方向。

## `b` 范围与 essentiality

- 原命题只写 `b≥0`。若保留一般 crossing 式，应补全 `0≤b≤n−a′−e(f)`，以保证归一化长度下界以及除去 `λ^{a′}` 后的幂指数非负；Definition 5.9 本来就有这个范围。
- 原命题末式未写 essential，而证明最后称它为 crossing。Definition 5.9 的 crossing 包含 essential 及非零/非边界条件。若最终目标是一般 crossing 判据，需要明确采用这些条件；不能将存在一个平凡 equation 当成存在 essential crossing。
- 若另行采用固定 `y` 且 `b=0` 的短 equation 版本，充分性是原目标属于较短像；是否把短 equation 强制为 essential、以及能否同时保持非 liftability，仍需核对完整必要方向。
- 本报告不建议通过添加一个“固定目标提取引理”作为未证假设或结果包来宣称完整命题完成。

## 实际验证与依赖

首次执行

```sh
lake env lean metadata/interface-reviews/ProofTools/20261017-paper-prop620-domain/evidence/WangCorrectionWorker.lean
```

以及显式工具链路径的同命令，均在沙箱启动阶段报 `could not detect the configuration of the Lake installation`；直接 Lean 启动也报 `failed to locate application`。这些返回未执行 Lean，不记为类型检查通过。随后按协调者安排，以 `require_escalated` 执行上述只读 Lean 检查，实际 **exit code 0**。四条 `#print axioms` 全部仅为 `[propext, Classical.choice, Quot.sound]`，不含 `sorryAx`。本次没有运行会写 `.lake/build/` 的命令，没有生成生产 `.olean`。

四个候选证明都是纯整数算术，不调用 `model`、Prop. 6.20、stretching、Main 最终目标，也没有 `sorry` 或新增公理。四个算术 lemma 通过，仅核验分次，不代表完整 iff 完成。

输入 SHA-256：

```text
828ee5a5aa06e1f390b036a043230ed417446fa7be11a4e27eecc4a565135c4b  AimPaper/main.tex
2864cf03dae40fc24ad69f16026499e9b15a03b82a3ecddab0414c3b82d8a0ea  KIP126/AdamsSynthetic/ExtensionWitnesses.lean
23f48a534f4761af2b6994a0a10237fdf3efb6d5749c83251cbeb84b06d3c652  KIP126/AdamsSynthetic/Extension.lean
```
