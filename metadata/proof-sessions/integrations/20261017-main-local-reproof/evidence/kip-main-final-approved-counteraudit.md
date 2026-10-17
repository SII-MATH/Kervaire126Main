# Main 最终获批 high125 路线独立反例审查

审查者 `/root/independent_math_audit`；2026-10-17。基线HEAD为 `2c703812db7edb830b995c53e9fe648747a66429`，读取当前WIP。遵守AGENTS.md与 `/root/.agents/skills/kip-upstream-session/references/protocol.md`。本审查未参与本次Source/Injectivity候选实现。只读生产、候选与规则；唯一写入为本/tmp报告；未运行Lean、Lake、构建或修改源码/metadata/锁。

## 结论

已读取获批patch及实际应用后的生产文件。未找到满足最终完整前提的反例，未见恢复错误高类唯一性、把任意b偷当2-primary、换对象、用旧争议接口导出False或循环依赖。三个实际消费者均真实构造同一个输入元素的h2，不增加Main公共前提。

这是一份独立源码/数学scope审查通过的报告，不是全项目无未证依赖证明，也不是本审查重新执行的Lean构建。加强后的 `tmf_high125_nonzero` 仍是原Literature直接待补责任，获批改变结论不等于已补证明；完整build、trust与精确导出由协调者统一执行。

## 实际读取的文件指纹

| 文件 | SHA256 |
|---|---|
| Main/Internal/High125/Source.lean | 4f4c668cfe4c38e94f143dfc398a56874210456ee3b2b1bcb004b556e16f99ef |
| Main/Internal/High125/Injectivity.lean | 4a9caa06a62b22e51d1603e9cabd849841641e886cf158fa0cab01b84e08f9ac |
| Main/Internal/High125/Filtration.lean | a449d7e6e9141cd470b9588824cb1b6aed7de3816f0808e3d023dc040da15dd0 |
| Main/ChoiceIndependence.lean | bc1b0be9951572cc61f198cbd874eb66e656739aeda6bf10ee16d9c39ed34df0 |
| Main/DifferentialCriterion.lean | a1a54deb14187d34947fbe458057de602e0f653bc84fb7b6334c75d1c1d3a4d1 |
| Main/Internal/Theta/OrderTwo.lean | aaa2cb95bf3a4b57c2f2d36695658b6783d03fa82c2d5f04c15614339b27db74 |

另完整读取 `/tmp/kip-high125-after-nonodd-approval.patch`；应用后的Source/Injectivity与其数学改动一致，Source头注释已准确记录获批非奇挠来源。

## 获批上游接口及对象身份

当前 `KIP126/Literature/Standard.lean`：

```lean
public theorem tmf_high125_nonzero :
  ¬ IsOddTorsionMap (high125 ≫ tmfUnit) := by
  sorry
```

保留同名、同一个 ordinary `Spectrum : Type 1`、Hom宇宙0、固定 `high125 : HomotopyGroup 125 SphereSpectrum`、固定tmf及其实际algebra unit；没有替换为2-completed球或另一个抽象image。`IsOddTorsionMap f` 是存在正奇数n杀f，包含零。因此新结论确实蕴含旧非零结论，但严格更强。其对象/单位实际识别仍由原Literature责任承担，本审查不把该sorry作为文献已形式证明。

高源仍为同一个 `κ̄⁴w`：`high125 := ((κ̄κ̄)(κ̄κ̄))w`，先前固定对象定义未动。`tmfUnit ≫ tmfIso.hom = auxiliary.detectorUnit` 保留同一unit比较。最终证明只要求此指定像非odd；没有断言tmf全π125是2-primary或分离，也没有要求高源本身2-primary。

## 最终完整下游目标及前提核对

生产 `detector_injective_filtration15` 的当前完整局部类型：

```lean
theorem detector_injective_filtration15
  (a : BiHom 125 130 (S_0_0 : SyntheticSpectrum))
  (ha : FiltrationAtLeast model.syntheticTower 15 a)
  (h2 : a + a = 0)
  (hz : a ≫ detectorMap = 0) : a = 0
```

此处是Main模块默认私有声明；没有把h2新增到Main公共论文结论。`detectorMap` 是现有同一 `nu.unitIso.inv ≫ nu.functor.map auxiliary.detectorUnit`。a为实际同一synthetic球映射，ha为该tower projection像，h2是同一a在实际预加性群中的倍增为零。

主动检查的边界：a=0兼容；普通odd球无限滤过见证不满足h2，不能套用本目标；任意λ-torsion类若在F26尾中，联合两条新桥确实被排除。高类lift b允许有odd ambiguity和λ-torsion ambiguity，最终代码没有未经证明排除这些。

## Source：先证明classical非零永久存活，无循环

`source_high_detected` 只调用指定κ̄/w的检测、三次实际乘法检测及同一E₂标签校准，得到固定high125的25滤过代表。没有依赖detector注入或Main主目标。

`high_nonzero_survival` 取该同一Z∞代表，假设其E∞ image为零，则actual associated graded quotient使固定high125落F26。`classical_filtration26_odd_torsion` 从已经保留的有限页尾零逐级提升，最后只调用修正后的ordinary球奇挠separation，得到high125为odd。

`odd_postcompose` 将同一个正奇数消去关系沿实际tmfUnit后合成；这与获批指定像非odd矛盾。因此得到classical NS。这里没有使用synthetic weight130 E∞非零，也没有用错误unrestricted F26零、highsource2-primary或π125全群无奇挠。可能的晚incoming differential（例如此前担心的d23）会导致上述E∞零分支，因同一源像非odd而被正确排除。

`high125_detector_nonzero` 旧辅助已删除；其职责没有被换成一个任意同标签元素非零的假断言。

## Filtration：真实scope与依赖

已再次核对生产合并后的两条桥及收口：

* `synthetic_filtration26_infinite` 只从(125,130)F26推所有实际非负滤过，没有偷推出零。
* `classical_filtration26_odd_torsion` 只给ordinaryπ125F26的odd结论，不断言全群F26零。
* `sphere_infinite_filtration_lambda_torsion_zero` 以前提“同一sphere元素无限滤过且有限λ幂挠”给零。实现从actual cofiber边界构造有限BHS lifts，用fullSS同一个E₂代表的Z∞性质和selected永久lift杀boundary；Prüfer裸模没有这些实际lift约束，不能作为符合全部前提的反例。
* `infinite_realization_odd` 只对无限synthetic滤过给actual realization odd。它先对非odd realization取真正classical exact filtration和NS检测，再以prescribedlift在共同权比较；有限λkernel与classical NS在任意λ降权保持synthetic∞非零相冲突。没有倒推classical NS。
* `sphere_infinite_two_torsion_zero` 结合actual realization的odd与2-torsion排除非零，再selected realization kernel给有限λ挠，调用第一桥。最终 `synthetic_filtration26_zero a ha h2` 只对同一满足h2的a成立。

已在此前独立桥审计中读取actualδ/TR3/no-return传递链，本轮生产桥的数学内容对应此前审过的两个完整/tmp候选。两桥不调用Source或Injectivity，也互不成环；上游Choice/LambdaInjectivity不反向导入High125。

## Injectivity：差只作odd处理，不要求错误唯一性

已删除旧 `high_exhaustion : a=0 ∨ a=λ²⁰b`。新证明不再将同一leading class强升为实际元素相等。

先由已独立取得的classical highNS和source_high_detected，用原selected prescribedlift得到b0：其首商为指定highClass，actual realization恰为固定high125。通过nuZero、unitIso的同一实际map转成sphere lift b；`realize_lift`与`realize_lambda`保留该对象等式。

将a从F15升到F25，`theta_detection_step`分两支：

1. 非零grade支：a与λ²⁰b具有相同E∞检测，仅推出差d=a−λ²⁰b在F26。新代码对d**没有**调用需要h2的F26零，也没有声称d阶二或b2-primary；只用尾推无限滤过和 `infinite_realization_odd` 得R(d) odd。hz经actual nu/recovery自然性及tmfIso把R(a)的tmf像化为零，R(λ²⁰b)=high125，故同一个R(d)的tmf像为 `−(high125≫tmfUnit)`。odd_postcompose和odd_neg给获批指定像odd，与新source结论矛盾。这里的False.elim是有明确分支前提的正常反证，不是利用旧错误接口的全局矛盾。
2. 零grade支：a∈F26。此时只对actual a应用 `synthetic_filtration26_zero a h26 h2`，h2恰为定理真实前提。没有给任意高类lift补出阶二。

因此新source“像非odd”而非“源2-primary”确实已足以关闭该局部证明；原六元素滤过群illustration的high像是三阶，恰好违反新增获批前提，已不构成反例。

## 三处实际消费者的h2确实已构造

逐源码读取：

1. `Main/ChoiceIndependence.lean:129` 的a是两个实际 `Standard.eta * theta²` 的差，使用 `eta_product_difference_order_two 124 128` 给同一个差的h2。theta仍任意ThetaChoice，未加2-primary或order-two公共前提。
2. `Main/DifferentialCriterion.lean:22` 的a是固定BX代表的实际η平方乘积，使用 `eta_product_order_two 124 128 (sphereProduct bxTheta5 bxTheta5)`。
3. 同文件:32同一对象和h2用于selected_forward。

`eta_order_two` 来自同一个 `Standard.toda_h0_eta` 的实际零乘积与 `Standard.toda_lambda_h0` 的λh0=2；`lambda_h0_map_zero_iff`明确处理同一shift/naturality，取identity functor得η+η=0。左η乘法的加性给任意其右因子乘积倍增零；差的h2为两个实际零倍增等式的群运算。因此上述h2不需要任意theta或任意b阶二。

还读取 `Literature/BX.etaThetaSquare` 和 `Selected/Assembly` 的bxEtaSquare，确认两个DifferentialCriterion消费者的actual目标正是这个η乘积，而非仅同次数的替代元素。

## 对62-stem b路线的交叉检查

生产无旧无前提 `two_torsion_62_70` 或 `theta_degree_order_two`。唯一conditioned调用为 `stem62_exponent_two α hprimary`。`first_quotient_order_two_lift` 真实构造odd倍n·b0：2^34R(b0)无限classical滤过经sphere奇挠结论得到odd n消去，故R(n b0)为2-primary；odd n保持同一F₂首商标签。之后actual weight71 kernel独立给b阶二。

这与本轮high125的prescribedlift b是不同度数/用途的局部变量；最终high125证明没有把62-stem b的阶二或primary结论误用到(125,150)lift。

## 传递待补、实际验证与局限

本轮生产目标文件没有新增sorry/axiom。仍依赖原有待构造背景、actual sphere/ν/recovery与quotients/towers、finiteλ商separation、finite_map_separation、ν∞标签及BHS finite/permanent lifts、selected realization kernel/prescribedlift、计算表实际对象识别、κ̄/w检测与乘法检测，以及刚获批加强但未完成的tmf指定像非odd责任。这些是项目数学责任，不是基础逻辑公理；获批接口与局部构建通过不能消除它们。

验证实际为：只读完整Source/Injectivity、完整已合并Filtration桥、三个消费者、有关实际对象定义及b构造；rg核旧错误helpers和调用已消失；sha256sum固定审查快照。没有重跑Lean或Lake、没有重新获取kernel传递axiom图。因当前WIP并发变化，后续生产哈希变化需协调者定向复核；应以统一完整build/trust及接口锁审计为最终工程证据。

证据等级：独立源码与完整真实前提的数学反例审查；未发现新反例，不表示项目所有上游接口已数学完成。没有把抽象滤过模当固定谱反例，也没有把现有sorry环境当反例证据。
