# Main 重证路线的独立反例与前提审计

审查者 `/root/independent_math_audit`；2026-10-17。基线 HEAD `2c703812db7edb830b995c53e9fe648747a66429`，实际工作区为其他 worker 并发修改的 WIP。遵守 AGENTS.md 和 `/root/.agents/skills/kip-upstream-session/references/protocol.md`。本轮只读生产与 metadata；本文件为唯一写入物；不运行 Lake、不写共享构建缓存。

## 结论

本轮未找到 LowEta `(1,3)` 消失或标准具体 high125 结论的新数学反例；未找到 ordinary π125 的具体非零奇挠见证。没有据此认定无条件全称 `π125 F26=0` 或 synthetic `(125,130) F26=0` 已成立。两项仍不能只由 E∞ 尾零和修正后的有限商/奇挠接口推出。

LowEta 已改成消费者实际需要的有限商唯一性；本轮读到的新证明保留真实对象和原有上游待补，避开未证普通 π1 奇挠排除。选定 b 的奇数倍构造在数学上成立，不需要 π62 群有限性，不需要对任意 synthetic 类断言阶二；关键 λ-realization-kernel 引理必须由实际 cofiber/permanent-lift 路线独立重证。

本轮没有新的已核实反例需另开接口人审。对原报告中两个任意62-stem阶二的反例不重复；实现中若恢复它们、恢复未截断 universal separation 或借其已有矛盾证 False，仍不合法。

## 本轮独立读取的目标、对象与实际前提

### LowEta

原 `KIP126/Main/Internal/LowEta.lean`：

```lean
theorem sphere_one_three_zero
  (z : BiHom 1 3 (S_0_0 : SyntheticSpectrum)) : z = 0
```

固定 `SyntheticSpectrum : Type 1`、Hom 宇宙0、同一 `model`、普通 ν sphere、同一 λ 与实际 νHF₂ Adams tower；没有隐藏2-complete、2-local或元素条件。原证明只得到 `∀ s : ℕ, FiltrationAtLeast model.syntheticTower s z`，再用已撤回的未截断 separation 关目标。

审查过程中 worker 把原过度使用的 helper 删除，实际新声明为：

```lean
sphere_one_three_infinite_filtration z : ∀ j : ℕ, FiltrationAtLeast ... j z
sphere_one_three_finite_quotient_zero z n : quotientClass n z = 0
eta_finite_quotient_eq_of_first_quotient_eq n x y
  (h : quotientClass 1 x = quotientClass 1 y) : quotientClass n x = quotientClass n y
eta_source_iso_fixed_in_finite_quotient n eta a :
  quotientClass n (a.hom ≫ eta) = quotientClass n eta
```

最后一条中的 a 是实际源球 `Smn 1 2` 的自同构。新代码先用低维 E₂ 与 infinity 比较得到无限滤过，再沿实际 `XModLambdaN.incl` 的 `model.convergentMap` 映射到外层有限 λ 商，最后调用修正后的 `.sphere n` separation。eta 差通过实际 λ-cofiber exactness 分成 `lambdaMultiply 1 b`；`quotientClass n b=0` 给出所需有限商等式。n=0 也在同一 actual cofiber 定义下处理，没有换对象。

独立读取未见把有限商相等强升成未截断相等；消费者的修改仍由相应 worker 负责验证。本审查未运行 Lean，worker 报告其文件单独检查通过，不能冒充本审查自己的编译结果。

真实数学目标本身应可由 ordinary π1=Z/2、λ LES 和 η 首商标签证明：`G_(1,2) ≅ π1 S = Z/2`，η 首商非零映到 `Ext^(1,2)=F2`，相应核给 `G_(1,3)=0`。但项目尚无已登记的 ordinary π1 无奇挠/群计算公共定理；这只是一个真实数学证明方向，不是已有 Lean 上游可直接调用的事实。不能用待证 eta 唯一性反推它，亦不能从 E∞=0 本身排除无限滤过奇挠。有限商路线正好不需要新增该责任。

### High125

`KIP126/Main/Internal/High125/Filtration.lean` 原两个完整私有模块内部目标：

```lean
theorem synthetic_filtration26_zero
  (a : BiHom 125 130 (S_0_0 : SyntheticSpectrum))
  (ha : FiltrationAtLeast model.syntheticTower 26 a) : a = 0

theorem classical_filtration26_zero
  (a : HomotopyGroup (C := Spectrum) 125 SphereSpectrum)
  (ha : a ∈ (model.classicalTower.tower SphereSpectrum).filtrationSubmodule 26 125) :
  a = 0
```

两者量化所有 a，不限标准 high125、不限2-primary、没有排除奇挠前提。有限页计算和 sphereVanishing 能逐级把 F26 推到所有滤过，但合规结论分别只有：每个实际有限λ商中的像为零，以及 classical `IsOddTorsionMap a`。没有合法理由仅凭这些结论关闭 `a=0`。

标准具体对象在 `Literature/Standard.lean` 是：

```lean
high125 := classicalSphereProduct
  (classicalSphereProduct (classicalSphereProduct kappaBar kappaBar)
    (classicalSphereProduct kappaBar kappaBar)) wClass
```

其中 kappaBar∈π20S、wClass∈π45S；二者固定为 Literature 的选定普通源类，定义及实际识别仍有原有未补责任。`source_high_detected` 从两个实际 detection 与乘法 detection 推出其25滤过标签，保留原始同一高次乘积，未换为任意同标签代表。

`tmf_high125_nonzero : high125 ≫ tmfUnit ≠ 0` 只说明实际源乘积的 detector 像非零。`high125_detector_nonzero` 通过同一个 `tmfIso` 与 `tmfUnit_agrees` 运输这一结论，依赖方向正常。它本身不蕴含任意被相同 E∞ 类检测的元素均非零，更不蕴含 ordinary π125 的所有奇挠为零。

原 `high_nonzero_survival` 证明：若该 E∞ image为零，则标准high125落F26，再从general `classical_filtration26_zero`推出它为零，与tmf像非零矛盾。这条链的缺口正是generalF26零；不能在重证F26时回调 high_nonzero_survival，形成循环。

原 `detector_injective_filtration15` 同样量化任意a∈syntheticF15。若 ordinary π125 存在被tmf杀死的奇挠，该普通类会产生无限滤过 synthetic 核见证；本轮未找到该度数的具体类，故不声称这是已完成反例，但也不能默认排除。更小的实际元素如 `λ^k η · (bxTheta5²)` 因固定 BX θ 阶二及双线性自身被2杀，可作为精确重证对象，避免不必要全称。

## 文献核查的实际范围及有效的具体对象事实

本轮打开原文并实际读取：

1. Isaksen–Wang–Xu, *Stable homotopy groups of spheres: from dimension 0 to 90*, Publ. Math. IHÉS137 (2023), DOI10.1007/s10240-023-00139-1，https://www.numdam.org/item/10.1007/s10240-023-00139-1.pdf 。读取Table1，核对PDF第8页：ordinary π60=Z/4；62行有3-primary项。全文第7页也给普通π1=Z/2。由实际普通球π60计算，可证明任何κ∈π20S的κ³被4杀；经实际球乘法结合律，high125=κ⁴w亦被4杀。这排除了标准具体high125自身为非零奇挠的可能，但**该π60计算未在当前项目已有接口中形式化**，不能增加一个sorry作为补证。
2. Wang–Xu, *The triviality of the 61-stem in the stable homotopy groups of spheres*, Annals186 (2017), https://annals.math.princeton.edu/wp-content/uploads/annals-v186-n2-p03-p.pdf ，读取PDF第5页Prop1.12。它的实际证明使用κ̄⁴{w}在π125tmf的非零像。本轮确认与Literature的具体乘积来源一致，不把该文的prime2约定静默变成ordinaryπ125全群计算。
3. Ravenel作者官网原书 https://www.sas.rochester.edu/mth/sites/doug-ravenel/mybooks/ravenel.pdf 与作者数字第三版 https://www.sas.rochester.edu/mth/sites/doug-ravenel/mybooks/ravenel3rd.pdf 。读取并截图旧版A3.4、检查新版A3.2：3-primary表只列至stem108，不能据无125行断言π125无3-primary。5-primary表虽涵盖125且未列它，这不足以排除3-primary，亦不构成ordinary全群证明。本轮没有找到满足high125全称F26前提的实际非零奇挠类。

这些文献只是本轮反例/真性审查的证据，不是项目新增证明责任的授权，也不是 Lean proof term。

## 选定 b 的奇数倍路线：独立核验

目标是存在 `b : BiHom 62 70 S_0_0`，保持实际 atom.b 的 first-quotient/detection 标签，且 `b+b=0`，而非断言每个 b 阶二。

Literature worker 的具体构造如下，本审查逐步核对其真实前提：

1. 由原有实际永久循环 lift 得 b0，令 α=realizeSphere b0。
2. `sphereAlgebra.scalar` 提供同一classicalE₂的ZMod2模，后续页与E∞为其subquotient，所以倍增为零。associated-graded comparison 于是使倍增把 actual Adams F_s 提升到 F_(s+1)。从F0迭代N次得2^Nα∈F_N。
3. 62-stem在s≥34满足真实 `SphereVanishingLine` 的不等式 `62 < 2s−3`，故足够大滤过起每个associated grade为零；2^34α因此处所有滤过。用修正后的classical_sphere_separated得正奇数n杀2^34α。
4. 令b=n•b0；交换nsmul得2^34(realize b)=0，同一个 realization b 满足新的2-primary前提。n奇使首商F₂标签保持不变，因此仍是所需atom.b检测类，不改变E₂标准类选择。
5. 由条件stem62_exponent_two得realize(2b)=0。实际`λh0=2`及realization反演λ给realize(h0·b)=0。若独立证明的`lambda_kills_realization_kernel_62_71`成立，则λ(h0·b)=0，即2b=0。

这一路线不需要finite(π62S)，不假设任意b2-primary，也不靠选择一个未关联的抽象群分量。原有 producer 依赖包括finite_map_separation、sphereVanishing、conditioned stem62、realization及actual quotient comparisons，仍应在元数据保留。

循环禁区：weight71 kernel lemma 不能调用选定b阶二、此前任意b阶二或受其影响的下游结论。`Theta/OrderTwo.lean` 中原helper使用通用未截断separation的证明尚需替换；在它完成前，上述只是有明确依赖的候选构造，不是已交付完整Lean证明。

## λ-kernel 重证中实际 Bockstein 比较的核查

独立读取 `Literature/BHS.lean`、`AdamsSynthetic/Quotients.lean` 并与worker沟通：

* `BocksteinDifferential` 量化的是存在某个有限商lift a，并非对任意lift直接给δ公式。不过q=1时rho_id使该a唯一，可合法把d2关系绑定到指定首商类。
* `bocksteinArrow` 的δ来自实际 `LambdaRhoDeltaTriangle`；它**不定义性等于** `XModLambdaN.proj 1` 后合成悬移的 `incl 1`。只用rfl替换是对象关联错误。
* `LambdaQuotientSystem.restriction` 固定actual chosen cofiberMap；triangle有distinguished、lambda_quotient、rho_quotient。可通过实际TR3比较或其零核判定，证明给定类上两种boundary关系一致。
* worker明确报告采用完整TR3构造，比较自映射固定incl，再用有限商no-return使该自映射在所需sphere maps上恒等，故落实比较。no-return自身依赖public finite_high_filtration_zero、ESSshift及ν infinity window，属于修正后的有限商适用域。

该方案未用通用未截断separation回填。完整候选仍需worker实际Lean检查；本审查没有执行其/tmp候选，也没有证明所有regrading/signs已闭合。若只需要d2=0，符号通常不影响零判定，但必须真正完成map比较，不能用“都是Bockstein”跳过。

## 依赖、False 与验证审计

读取当前Main源码时尚见旧调用残留在High125/Filtration、Choice/LambdaInjectivity、Theta/RealizationKernel，worker正在替换；本报告不将WIP残留称为最终实现。

所见 `False.elim (high125_detector_nonzero hzero)` 是在假设detector像为零的分支中以已来源的具体乘积非零引出矛盾，这种常规反证本身合法。应审查产生hzero的实际元素等式是否经过失效F26零/循环链，不能把所有False.elim一概标成作弊，也不能用原错误公共接口产生的全局矛盾随意关闭新目标。

本轮数学检查未调用待反驳目标、其下游结论或False；外部低茎/乘积事实依赖原始文献。运输至当前Lean固定背景仍依赖原有待构造Spectrum、SyntheticSpectrum、同一ν/realization、sourceRecognition及actualHF₂ synthetic比较。基础逻辑公理与这些项目责任不同；未把sorryAx环境导出的任何命题作为反例。

证据等级：LowEta真性与标准high125的4-torsion为文献支持数学论证、Lean运输条件性；High125全称F26零为未决，无实际反例；选定b为有显式已登记依赖的数学构造路线；λ-kernel TR3为待完成编译的实际实现路线。未找到反例不代表接口正确。

实际验证：只读git状态、rg、sed/cat、生产完整声明与结构字段检查；本轮web实际打开并读原文/截图。没有运行lake、Lean、freeze、清缓存或修改生产/metadata。用户的全build/push/cache须由协调者在真正闭合与统一检查后执行，本报告不声称已完成。

## 后续源码复核：选定 b 构造

收到worker消息后，本审查额外读取了实际 `KIP126/Main/Internal/Theta/OrderTwo.lean:21–224`。现在该文件已经删除无前提任意b阶二，实际代码为 `classical_infinity_double` → `classical_doubling_filtration` → `classical_stem62_tail_step` → `classical_stem62_odd_multiple_primary` → `two_torsion_62_70_of_realization_primary` → `first_quotient_order_two_lift`。逐步核对与上述数学路线相符，最终返回同一 first-quotient label 与阶二等式。没有把假设hprimary省略或从conditioned theorem循环取得。worker报告arith/core及显式kernel参数隔离检查均exit0；本审查仍未自行编译。唯一局部外部依赖关键是原签名weight71 kernel lemma的合法重证。

## High125 专项后续：现有实际接口与最小候选（未实施）

协调者随后要求单独判断：actual `a : BiHom 125 130 S_0_0` 满足 `a+a=0`、F15及detector(a)=0时，是否能在现有接口下证明a=0，尤其是否存在计算数据绕开high_nonzero_survival。本轮再次只读检索并与final_change_audit交叉沟通。

### 精确检索结果

* `Computation/Table/Syntax.lean` 的 `Raw.Spectrum` 只有 `.sphere | .nuCofiber`。`Claim.spectrum`、degree、result/Statement全部经该枚举绑定；原始计算表没有tmf对象，因而没有tmf(25,150)/π125的直接结果。
* `Computation/Standard.lean:360–371` 的 `detectorComponent` 是抽象E₂坐标族，`detectorComparison` 给其到actual detector E₂的线性等价。它没有125-stem维数、基底、单位像或存活公理。唯一对应标签是`detectorV2Sixteen`、`detectorBetaGFour`；`detector_d3` 只有(16,112)到(19,114)，与所需(25,150)没有已登记乘法/非零绑定。
* Literature现有high125源事实仅具体乘积的detector像非零；没有κ̄、w、high125的2-power阶、π60指数或π125tmf奇挠排除定理。`tmf_convergence` 的完整类型仅 `ClassicalTowerConvergence`，定义中只有associated-graded identification及同一代表的canonical compatibility，**没有separated/complete字段**。
* `finite_map_separation` 要求源和靶都是finite spectrum。sphere125有限不够；tmf不是有限谱，`tmf_finiteModTwoType`不提供`IsFiniteSpectrum tmf`。因此不能把sphere奇挠separation搬到π125tmf。
* 新 `eta_order_two` 从实际 `toda_h0_eta=0` 与λh0=2导出，足以让实际η乘积及其选择差被2杀；此处不需要普通π1新定理。但这不能单独把high125的tmf非零像识别为非odd。

### 最小滤过群反模型说明缺口

取G=(Z/2)·a ⊕ (Z/3)·h，F_s=G（s≤25），F_s=(Z/3)·h（s≥26），detector为到Z/3的投影。令high=a+h。

则a非零、2a=0、a∈F15、detector(a)=0；high的detector像h非零。F25/F26是一维F₂，high与a具有同一非零永久associated grade；所有s≥26的associated grade为零，所有无限滤过元素恰是odd torsion。尽管如此a仍不为零。即使另加“classical highClass非零永久存活”，该illustration仍成立。

这里是**有限计算证据＋抽象滤过群反模型**，只检查这些局部代数输入的推理力度；没有构造完整KIP126 Model，没有实际谱对象识别，不能声称反驳固定接口。本轮用Python枚举G的6元素检查上述倍数、odd判定、源和像：全部断言通过。未利用任何项目sorry或False。

### 两个足够的新增数学候选及比较

候选A（更小、直接对准缺口）：

```lean
¬ KIP126.AdamsSynthetic.IsOddTorsionMap
    (KIP126.Literature.Standard.high125 ≫ KIP126.Literature.Standard.tmfUnit)
```

合适新名称例如 `tmf_high125_not_odd_torsion`。它严格强于当前非零像，却不要求high125本身无odd分量，不要求tmf整个π125是2-primary，也不要求tmf完整分离性。

候选B（较强、普通低茎计算有来源）：

```lean
∃ n : ℕ, (2^n : ℕ) • KIP126.Literature.Standard.high125 = 0
```

现有 `tmf_high125_nonzero` 加候选B推出候选A：加性后合成保留2-primary；一个同时被2幂和正奇数杀死的元素必为零。反向不成立：源可有被detector杀死的odd分量。

真实数学上B可由ordinaryπ60=Z/4推出：high125=κ̄³·(κ̄w)，故4high125=0。本专项本轮再次打开IWX2023原文Table1的60行以及Wang–Xu2017 Prop1.12，前者全群60行是4且odd/v1其余列空，后者给实际κ̄⁴w的tmf像非零。**这些源结果尚未在项目现有接口形式化，不能通过添加sorry实施B**。

### 候选A如何消除High125分支缺口

以下是有明确局部依赖的重证路线，不宣称已编译：

1. classical highClass若E∞为零，`source_high_detected`令实际high125∈F26。classical尾页零推到所有滤过；修正后的sphere separation给source high125 odd；后合成tmfUnit仍odd，与候选A矛盾。故先合法获得high_nonzero_survival，未循环使用synthetic detector注入。
2. 用该NS及`source_high_detected`调用既有`selected_realization_prescribed_lift`，得到首商标签highClass、realization恰为固定high125的b，再取λ²⁰b到weight130。
3. actual a的F25非零分支给a与λ²⁰b同associated grade，差d∈syntheticF26。若已建立同一actual realization的滤过比较，则realize d∈classicalF26，尾推无限滤过，sphere separation给realize d odd。由detector(a)=0，后合成可推出固定high125的tmf像odd，违反候选A。此处不必先证明d=0或b2-primary。
4. 零grade分支a∈syntheticF26。在同一realization滤过比较下，realize a既odd又被2杀，故为零。`selected_realization_kernel`给a有限λ幂挠；a的synthetic尾零给无限滤过，若独立完成“无限滤过且有限λ幂挠⇒零”的actual cofiber引理，即a=0。

不能跳过的额外边界：当前rg未发现独立public一般`realization_preserves_filtration`。`selected_filtration_lambda`只比较syntheticF与λ可除性；`selected_realization_detection`只对已知NS及指定首商lift给classical检测。这两者不能单独被当作任意元素R保持Adams滤过的已证定理。协调者拟用nonodd exact filtration、实际prescribedlift与finite quotient比较重建该桥；需要真实完成。候选A消除源像odd缺口，但不魔法般完成此桥或λ挠分离性。

本报告没有申请或实施新的public声明、待补责任、参数或sorry。若需要A/B，须由独立报告员给出精确接口人审范围；保持现有数学对象和责任归属。

## 两条新桥的独立候选审查（2026-10-17 后续）

本审查未参与以下两个候选的实现。按协调者新派发，完整读取并主动尝试反驳：

* `/tmp/kip-main-infinite-lambda-kernel.lean`，SHA256 `9d749e787aac8f4df9f0a9bf1292d6899e7f6a9c2fc17b75af79a87df08dc11e`。
* `/tmp/kip-high125-bridge.lean`，SHA256 `d5d756491978f33f245adc95d1b31a88a6b5fe9ab79f0403c91c27ee7a2525f9`。
* 被调用的新实际δ比较所在 `Main/Internal/Choice/LambdaInjectivity.lean` 当时SHA256 `b81366348b59acc32aa35f203a231d522c13819421bcd74d59a8b7c3fd5b7813`。

协调者报告两文件各已独立Lean exit0；本审查没有重跑Lean或Lake，因此下面是完整源码和传递调用的独立数学审查，不冒充重新取得的kernel axiom graph。

### 桥1：无限滤过且有限λ幂挠 ⇒ 零

末尾完整目标：

```lean
private theorem sphere_infinite_filtration_lambda_torsion_zero
  (m w : ℤ) (a : BiHom m w (S_0_0 : SyntheticSpectrum))
  (ha : ∀ s : ℕ, FiltrationAtLeast model.syntheticTower s a)
  (ht : ∃ k : ℕ, lambdaMultiply k a = 0) : a = 0
```

范围是同一固定synthetic球、所有整数m,w；元素同时满足真实tower无限滤过和真实λ有限幂挠。它不是恢复未截断全对象separation。原非零odd球类的realization非零，因realization反演λ而不可能满足ht，故不能重用旧odd见证反驳它。

独立核对的关键步骤：

1. 无限滤过沿同一actual quotient inclusion映到每个有限λ商；修正后 `.nu X n` separation给每个quotientClass n a=0。先在νX及nuZero中证明，再由相同unitIso搬回sphere，保持对象和实际maps。
2. 对λa=0的基步，实际λ cofiber Hom正合得到c∈π_(m+1,w)Cλ，其boundary等于悬移后的a。每个有限商像为零，经已证明的实际 `lambda_zero_shift_delta_evaluation` 使c在每条实际λ–ρ–δ triangle的δ像为零；正合性得到所有有限λⁿ lift。
3. actual `firstQuotient`把同一个c识别为同一个E₂类x。`bhs_finite_lift`说明这个固定x reaches every finite page，允许零和boundary。不是随n任意更换E₂类。
4. `route_common_cycle_of_finite_cycles` 没有非法交换 `∀n ∃z` 与 `∃z ∀n`。取一个初始代表z0。第n个代表zn与z0的差落在初始边界B0；SSData精确有 `B0 ≤ B∞ ≤ Z∞ ≤ Zn`。因此z0本身已经在每个Zn里。`Z_top_greatest`把其生成子模放入Z∞，给共同actual无限cycle代表。无需有限性、Mittag–Leffler或选择一个兼容inverse-limit序列。
5. 既有 `selected_permanent_lift X` 对这个共同cycle给actual untruncated lift z，使c恰为incl z。因actual incl≫proj=0，同一个c的boundary为零，故a=0。这里使用permanent cycle，不需要把它升格为nonzeroSurvival，也没有忽略它可能为incoming boundary。
6. 对有限λᵏ挠的归纳，只对λ^(k−1)a应用上述λ一步基步；所有有限商像零在预合成λ下保持。`lambda_multiply_compose` 明确处理实际shift coherence和HEq，没有混淆权w−k−1与w−(k+1)。k=0由λ⁰同构直接给零；负m,w与n=0没有额外前提缺失。

实际δ比较传递链亦独立读取：`lambda_zero_shift_delta_evaluation` → actual functoriality/nuZero iso → `lambda_first_quotient_delta_evaluation` → TR3填充c固定incl → `lambda_quotient_maps_equal_on_spheres` → `lambda_boundary_no_return` → ν infinity window、ESSshift、finite_high_filtration_zero。该链使用修正后的有限商分离性；没有回调此新桥、High125 detector注入、任意b阶二或已撤回sphere分离性。

### 为什么Prüfer λ模不是这条桥的反例

裸模中令λ=2作用于Q₂/Z₂，确有非零元素同时λ无限可除且被有限λ幂杀死；仅“所有有限商像零”不足以排除它。此前若用这种模说明一般inverse-limit缺口，必须保留其证据等级。

它不能同时满足本候选用到的actual firstQuotient、finiteBHS/fullSS和selected永久lift约束。具体说，取非零a∈kerλ，cofiber边界正合给c，其boundary是a。无限可除可让c向所有有限λⁿ商提升。若又把这些有限提升通过同一个firstQuotient/BHS绑定到同一个E₂类，则fullSS的共同cycle步骤给它永久cycle。`selected_permanent_lift`随即要求c是actual untruncated incl像，而正合性要求该incl像boundary为零，与a非零冲突。故此Prüfer实现必在这些绑定中至少失败一项，特别不能同时保留actual永久lift。

这个解释不是利用环境矛盾作反例，而是逐条指出裸Prüfer模不满足候选全部真实前提/固定对象比较。当前没有把Prüfer模识别为本项目选定sphere或selectedClassicalObject的构造，因此它只属抽象模警示，不能反驳该桥。

### 桥2：sphere无限synthetic滤过 ⇒ actual realization为odd

末尾完整目标：

```lean
private theorem infinite_realization_odd {m w : ℤ}
  (a : BiHom m w (S_0_0 : SyntheticSpectrum))
  (ha : ∀ q : ℕ, FiltrationAtLeast model.syntheticTower q a) :
  IsOddTorsionMap (Standard.realizeSphere m w a)
```

真实ordinary realization，未增加2-primary、有限λ挠或2-complete条件。原ordinary odd球见证满足该结论；它允许a本身非零，故也没有恢复错误零结论。

独立核对的反证链：

1. 假设实际α=realizeSphere a不是odd。源Sphere m和靶ordinarySphere均有限，合法调用已有 `finite_filtration_of_not_odd` 得α的精确actual classical滤过；`nonzeroClassicalDetection_of_exact` 经实际convergence给非零classicalE∞及同一α的检测。没有把synthetic∞非零误用为classical∞非零。
2. `selected_realization_prescribed_lift` 只在刚刚得到的NS类x上应用，给同一x的球lift b，且R b恰为同一个α。unitIso/nuZero与realization source iso的运输在 `prescribed_sphere_lift`、`realize_lift`中明确完成。
3. 降λ到共同权v=min(w,t)，a0、b0具有完全相同source/target和相同realization。实际map_sub给R(a0−b0)=0，`selected_realization_kernel .sphere`给有限N杀这个差。它没有假设a本身λ挠。
4. 因λ作用保持每个actual filtration，λ^N a0仍无限滤过，等式给λ^(kb+N)b也无限滤过。
5. 对真正NS x，`sphere_infinity_nonzero_of_survival`通过同一ν-unit map与 `eInfinity_nu_labels` 的actual permanent-quotient公式证明其任意有限λ降权的synthetic∞代表非零：若为零，x落入某有限boundaries子模，与classical NS矛盾。这个方向严格由已取得classical NS推synthetic非零。
6. actual `sphereDetectionCompatible.homotopy_lambda`又给同一λ^(kb+N)b的检测；无限滤过使其在检测级的下一级，故associated grade零，与上条非零矛盾。s可负时使用自然数(s+1).toNat及antitone正确覆盖；所有λ指数ka,kb,N为非负自然数，min保证降权合法。

这条桥没有使用桥1；两桥之间不成循环。它也不直接断言任意syntheticF_s在realization后仍classicalF_s，只证明无限滤过的odd结论，scope更小。

### 保留的依赖与审计结果

两候选没有新增sorry、axiom或用户假设。内部False目标 `sphere_detected_survival_not_infinite` 仅用于上述明确NS与同一元素无限滤过的局部矛盾，未调用旧假接口导出False。实际读取的被调用纯操作包括 `isCycle_iff_reaches`、firstQuotient线性同构、actual triangle正合性、SSData的B/Z极限律、sphere/ν标签搬运、Choice纯滤过difference检测搬运和λ shift coherence。

仍有上游producer依赖：固定Spectrum/SyntheticSpectrum和实例、ν/recovery、actualquotients和tower/convergence、有限λ商分离性、ESSshift、ν∞标签模型、BHS finite lift、selected永久lift；第二条另依赖finite_map_separation经nonodd exactfiltration、selectedrealization prescribedlift、selectedrealization kernel和sphereDetectionCompatible。它们是已有登记责任，不因局部Lean通过而变成无待补定理。

本轮未找到满足这两条完整前提及对象绑定的反例，未见依赖目标自身或High125待修复结论的循环。结论等级：独立源码与数学接口审查通过；协调者报告Lean已通过，本审查未独立执行kernel编译或全量axiom扫描。生产整合后应由协调者执行项目完整build/trust检查并复核私有导出及依赖，不以本scratch代替统一验证。
