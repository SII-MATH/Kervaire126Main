# 独立核验记录

审查者：`/root/mh_interface_review`，2026-10-18；未参与候选发现或实现。独占报告及本目录；生产代码只读，未启动共享构建。

## 完整前提与固定对象核对

| 条件 | 独立核对结论 | 限制／责任 |
| --- | --- | --- |
| 同一个 `Standard.model`、实际经典三角 T、三个 normalized lifts | 候选固定这些对象；`Literature/Triangles.lean:97` 定义三条实际 map | generic law 适用任意 D，当前候选尚只承诺标准模型；不混为同一范围 |
| e_f,e_g,e_h 非负、和为1、实际 distinguished compatibility | 已保留；非负性来自 Nat exponent | 指数和不能单独替代 compatibility |
| x̄、ȳ、x、y 的真实 Adams 双次数和 cycle 条件 | 与旧 law、研究全文逐项一致，x 初始条件扩展为 Z_(n₁−j) | 必须沿固定 suspension 关联到指定 x，不能任选 E₂同构 |
| a 的三个检测 | 候选全部由同一实际 a 给出 | 两个孤立 ESS 页面方程不足以提供它；同步仍待证 |
| b 的两个检测 | 同一实际 Q_B 代表 | g 的商是 B=m₁+j+1，不能机械沿用原零层商 |
| 可见层与商长 | A−K=n₁−j>0，N−J=m₁+1>0，N=r+i | j<n₁ 是指定 x 反射的充分界；不宣称必要最小界 |
| δa 与 g_Bb 实际相等 | 两者目标都是 Q_B 顶层 B−1、同一双次数、同一标签 | 需 finite separation 与 E∞窗口；不是任意滤过群中自动的结论 |
| c 的两条像方程与标签 | signed tensor May 源码给同一个 c 的两式 | tensor-to-quotient comparisons 待完；非新 Lean theorem |
| ordinary Adams 推论 | 必须用同一个 α、β=f_Aα 与连接自然性 | `generalizedLeibnizAtLevel` 另有完整 `InfiniteExtension` 输入，不是一般有限—有限 GL |
| 完整／经典提升 | 仿射族相交与连接障碍消除是准确条件 | 源永久仅给某个完整首项代表，不保证保留目标；需要 source/target filtration reflection |
| source/target 非零、essentiality、目标永久 | 候选没有偷加这些结论 | 指定实际目标首项来自完整 ν才支持指定 y 永久；有限 ESS商式不足 |

## 一般算术与最小例

代入 n=n₁+e_f、m=m₁+e_g、l=k+e_h 和 e_f+e_g+e_h=1：

- r=n₁+m₁+k+1，A+B=r+i；A−i=n₁+k−j>0，A−K=n₁−j>0。
- B−j=N−J=m₁+1，N−K=r−k=n+m+e_h，J−K=n₁。
- δ 的目标指数 i+r−A−1=m₁+j=B−1；这是 g_Bb 的同一最高可见层。
- a 的 weight 为 t−i，δa 的 unshifted-Z weight 为 t−i+A。
- b 的 weight 为 t+l+n−1−j，加 e_g 等于 t−i+A。
- c 的 weight 为 t+e_h−1−i，加 e_f 等于 t−i−e_g；λ^A b 的 weight 也是 t−i−e_g。

最小强商例 n₁=1,m₁=0,k=1,i=j=0：A=2,B=1,N=3,K=1,J=2,Q=2。Q_3 保留目标层2，投影到 Q_2 后该层不可见。这是不能用弱投影替代强商目标的指标例，不声称该参数下构造了非零实际目标。

复现命令：

```sh
python3 interface-proposals/ProofTools/20261018-mh-finite-level-target/evidence/check-indices.txt
```

实际输出：55296 组 MH 参数、23256 组 finite–finite GL 参数，各核对3个 weight，所有断言通过。一般代数已逐式写出；有限盒只防笔误。脚本不搜索实际谱，不验证 homotopy 或 crossing，也不是反例搜索或新 Lean 证明。

## 源码及传递依赖

- `KIP126/Literature/Triangles.lean:97`：U=Σ^(0,e_f)νX，V=νY，W=Σ^(0,−e_g)νZ；normalizedConnecting 使用实际悬挂比较。
- `KIP126/ProofTools/GeneralizedMahowald/Geometry.lean:208`：May tensor common lift，两条实际式子的负号。调用 `may_pushpull` 与 tensor shift/exactness；没有调用旧 MH 或用 False 消去来证明新目标。
- `KIP126/Literature/Standard.lean:1786` 起：上述 May shift/exactness/pushpull 均保留 sorry、在待补基线登记。
- `KIP126/ProofTools/GeneralizedMahowald/Filtration.lean`：finite_top_detection_unique → finite_high_filtration_zero → `AdamsSynthetic.Standard.synthetic_homotopy_separated` 与 finite E∞比较。`AdamsSynthetic/Standard/Separation.lean` 明确是基础上游待补。
- `KIP126/Literature/Standard.lean:1140` 起：λ/ρ 的有限比较及 `eInfinity_rho_nu` 保留上游待补。仅关联分次公式不等于实际过滤反射已经无条件完成。
- `KIP126/ProofTools/GeneralizedLeibniz/Boundary.lean`：finite δ 是完整 boundary 后接投影；nu_projection_infinity_injective 使用 `eInfinity_rho_nu`。
- `KIP126/ProofTools/GeneralizedLeibniz/WeightedReverse.lean`：weighted reverse boundary 的已有实际 λ原像路线，可服务一般 finite–finite 解码；不能把该文件存在当作完整新方框定理已交付。
- `KIP126/ProofTools/GeneralizedLeibnizAtLevel.lean:26`：原公开类型含 `hInfinity : InfiniteExtension ...`，故底边要求强于一般 finite–finite 输入。
- `StatementReview.lean`、`RotatedNuPremises.lean`、`BottomNuInjection.lean`：旧 law 的实际对象反证。完整参数与限制在主报告；本次源码核验并非新内核构建。审查未调用旧 law 获得矛盾来证明候选。
- `KIP126/ProofTools/InternalAudit.lean` 对已完成工具（含 May tensor、weighted reverse、level GL、division）已有 transitive 禁用本地待补边界；未来候选应继续沿用，不能只看文件 imports。

群研究全文与历史笔记的一致支持不替代上述独立核查。官方历史大数据和 C++ 重放未在本轮运行；其计数、GL2412568 三个合法修正及未定系数均只作为已归档研究状态引用。

## 已确认／未决

已确认：数学参数、weight、可见层、强商必要范围、代表级输出与分层组织均与实际源码／研究材料相容；负号、边界分母、零目标语义必须保留。

未决：准确可 elaboration 的公共 Lean 类型；tensor-to-quotient 完整比较；最实用且充分的 actual no-crossing 同步谓词；一般有限—有限 ordinary 解码；经典仿射提升及实际调用证书；全部上游固定对象与文献待补。未发现新的实际谱反例，亦未把有限算术通过写作这些命题已证。
