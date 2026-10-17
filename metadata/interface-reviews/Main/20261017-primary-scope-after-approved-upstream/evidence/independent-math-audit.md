# 已批准接口候选的独立数学审查

审查者：/root/independent_math_audit；日期：2026-10-17。只读生产文件；本报告是唯一写入物；未运行 Lake 或写共享构建缓存。基线 HEAD 为 `2c703812db7edb830b995c53e9fe648747a66429`。审查按 `/root/.agents/skills/kip-upstream-session/references/protocol.md`；已读 AGENTS.md 和技能正文。其他 worker 并发改生产文件，以下区分基线与已观察的新候选。

## 结论

三个已批准的新接口未找到满足新真实前提的反例；这不表示有限商分离性已经证明。经典奇挠结论的新证明直接依赖既有 `finite_map_separation` 未证责任。新增同元素 2-primary 前提正确排除了普通 π₆₂ 的三阶反例。

但两个下游任意 synthetic 类阶二结论在同一个 ordinary sphere / 真实 HF₂ synthetic 语义中仍为假：`Main.Internal.Choice.theta_degree_order_two` 的任意 `BiHom 62 64 S_0_0`，以及 `Main.Internal.Theta.two_torsion_62_70` 的任意 `BiHom 62 70 S_0_0`。本报告给出这些真实数学对象上的完整三阶反例推导；运输到目前尚未构造完成的 Lean 固定背景仍是条件性的，没有不含项目待补依赖的 Lean 反例。

协调者已收到通知，已安排独立报告员 `/root/main_interface_report`。用户批准上游候选不是允许新增 Main 待补、篡改任意元素量词或增加下游公开假设的授权。

## 完整目标及固定对象

1. `KIP126/AdamsSynthetic/Standard/Separation.lean:20` 观察到的新签名：

```lean
public theorem synthetic_homotopy_separated (X : SyntheticObject) (n : ℕ) :
    HomotopySeparated model.syntheticTower
      (XModLambdaN (X.obj model.nu model.auxiliary) n)
```

所有对象均是固定 `SyntheticSpectrum : Type 1`、Hom 宇宙 0；没有隐藏的模型量词。`HomotopySeparated P Z` 定义为 `∀ m w : ℤ, ∀ a : BiHom m w Z, (∀ s : ℕ, FiltrationAtLeast P s a) → a = 0`。滤过由同一实际 tower projection 的像给出。`XModLambdaN Z n` 定义为同一 `lambdaPow n Z` 的选定 cofiber，不能以另一个抽象有限商替代。

`SyntheticObject` 在 `Configuration.lean:44` 只有 `.sphere`、`.nu (X : ClassicalObject)`、`.shift p X`、`.quotient n X`。特别是 `.nu` 的参数是 ClassicalObject，不允许任意 synthetic 对象再 ν；所谓嵌套来自 shift 和 quotient 的有限语法树。

2. `Standard/ClassicalSupport.lean:66` 观察到的新签名：

```lean
public theorem classical_sphere_separated (m : ℤ)
  (a : HomotopyGroup (C := Spectrum) m SphereSpectrum)
  (ha : ∀ s : ℕ,
    a ∈ (model.classicalTower.tower SphereSpectrum).filtrationSubmodule s m) :
  IsOddTorsionMap a
```

`IsOddTorsionMap a := ∃ n : ℕ, Odd n ∧ 0 < n ∧ n • a = 0`，包含零。普通球与其所有整数悬移均在有限谱闭包。

3. `Literature/Standard.lean:184` 的批准候选（独立读取时该 worker 尚未应用）：

```lean
public theorem stem62_exponent_two :
  ∀ a : HomotopyGroup (C := Spectrum) 62 SphereSpectrum,
    (∃ n : ℕ, (2 ^ n : ℕ) • a = 0) → a + a = 0
```

固定同一个 integral π₆₂；不能把“mod-2 Adams 可检测”与“该元素是 2-primary”混用。sourceRecognition 规定普通源球、同伦、加法；未用完备化球替换。

## 三个新候选的边界与前提核对

### 有限 λ 商

* n=0：`lambdaPow 0 Z` 是 `biShift_zero.hom.app Z`，实际同构；其 distinguished cofiber 是零对象。所以该边界与任意 s,m,w 的分离性相容。这是从既有 cofiber/triangulated 结构得出的数学边界检查，未运行 Lean 编译。
* `.quotient 0 X` 内层即为零，再取外层有限商仍零。
* 对有限嵌套 shift/quotient，没有找到普通奇挠见证仍在有限外商保留的反例。真实 HF₂ synthetic 中奇挠部分上 λ 是同构，故外层有限 cofiber 消去本报告使用的奇挠类。
* 此观察只排除一个反例家族，不证明整个嵌套闭包的分离性。需要构造实际 Cλ 对象、层和塔；不能仅从 E∞ 模型或有限窗口无非零页推出分离性。
* 调用对象必须精确：若目标为 `XModLambdaN (νY) q`，应使用新接口参数 `(.nu Y) q`。使用 `(.quotient q (.nu Y)) q` 得到的是二重商，不能靠类型转换当同一个对象。商后 shift 需要实际 shift/cofiber 同构及滤过自然性，不是给 n 填数字即可。

### 经典奇挠

观察到的新证明对 `finite_map_separation` 提交 `IsFiniteSpectrum.shift m sphere`、`sphere` 和 a，然后取 `ha s.toNat`。负滤过延拓通过 `stageAt s = stage s.toNat`，因此所有整数 s 的 MapAdamsFiltration 与自然数前提相容。

这是与既有 finite-map separation 一致的直接推导；其直接 sorry 在 `Standard/Filtration.lean:36–38`，所以新 theorem 不是已完成 foundational separation。m=0 的普通 π₀=ℤ 没有非零奇挠，m<0 的球群为零，m>0 的普通有限群奇挠都与结论相容。没有利用这些未形式化群识别冒充 Lean 证明。

### π₆₂ 同元素 2-primary

n=0 只允许 a=0。对完整群 `(ℤ/2)^4 ⊕ ℤ/3`，若 `2^n a=0`，在三阶因子上 `2^n` 可逆，因此三阶分量为零，其余部分确被2杀死。原来的非零三阶类不满足新前提。

选定 `theta5` 的阶二仍须由其真实选择/来源证明；`theta5_detection` 只约束 mod-2 检测类，不能排除给代表加上奇挠的不定性。不能仅传一个新增 sorry 证明 theta5 2-primary，也不能以 theta5_order_two 反过来证明所需前提再调用 exponent_two，形成循环。

## 下游任意元素阶二的完整数学反例

### 本轮独立核对的原始来源

* Isaksen–Wang–Xu, *Stable homotopy groups of spheres: from dimension 0 to 90*, Publ. Math. IHÉS 137 (2023), DOI 10.1007/s10240-023-00139-1，https://www.numdam.org/item/10.1007/s10240-023-00139-1.pdf 。本轮 web 打开全文，并 screenshot 核对 PDF 第8页 Table1 的 62 行为 `2^4 | 3 | 空`。因此 ordinary π₆₂ 中存在非零三阶类 α。
* Pstrągowski, *Synthetic spectra and the cellular motivic category*, https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/synthetic2.pdf 。本轮 web 打开并读取 Prop.4.57（PDF第79页）、Cor.4.38、Prop.4.40、Theorem4.58，而非只引用旧报告或回忆。其含义：ν fully faithful、τ反演恢复同一谱；ν 对象的 τ-长正合列两端为 E_*E comodule Ext。以下反例是据此自行推导。

### 量词内的具体构造

取 ordinary 稳定球的 `0 ≠ α ∈ π₆₂ S` 且 `3α=0`。同一个 ν 的单位和悬移比较把 ν α 运输成 `a₆₂ ∈ G₆₂ := [S^(62,62),S^(0,0)]`；ν 的 faithful 性及加性保证非零和阶3（也可使用真实 fully faithful ν 的同伦群加法识别）。

对每个整数 w，令 `G_w := [S^(62,w), S^(0,0)]`。Pstrągowski Prop.4.57 取 X=Y=S、E=HF₂，给出

```
A_w → G_(w+1) --λ--> G_w → B_w,
```

其中 A_w 与 B_w 是 HF₂_*HF₂ comodules 的 Ext 群。因此 `2 A_w = 0 = 2 B_w`，λ 的核和余核均被2杀死。这里是同一 synthetic sphere 和同一实际 λ，不是替代群模型。

群论步骤完整如下。假设 `0 ≠ b ∈ G_w` 且 `3b=0`。其在 B_w 中的像同时被2和3杀死，故为0。正合性给 x∈G_(w+1) 且 λx=b。设 k=3x，则 k∈kerλ，故2k=0。取 x'=-2x，则

```
λx' = -2b = b,
3x' = -2(3x) = -2k = 0.
```

由于 b≠0，x'≠0。这同时证明 λ 在3-torsion子群上的满射；若两个3-torsion lift有同一像，差同时被2和3杀死，故相同。因此该子群上的 lift 唯一。

从 w=62 迭代2次得 `a₆₄ ∈ BiHom 62 64 S_0_0`，迭代8次得 `a₇₀ ∈ BiHom 62 70 S_0_0`，二者都非零且阶3。阶3非零元素不可能满足 `a+a=0`，否则2a=3a=0由Bézout即a=0。

realization 反演 λ，且上述选择的自然 source isomorphism 与 `realization_lambda` 保持同一个 ordinary α；所以两个 realization α 均不是2-primary。它们精确满足两个下游私有引理的全部前提，因为引理只量化该双次数的任意类，没有检测、2-primary 或规范选择条件。

### 精确受影响目标

* `KIP126/Main/Internal/Choice/OrderTwo.lean:45`：
  `theta_degree_order_two (theta : BiHom 62 64 S_0_0) : theta+theta=0`。
* `KIP126/Main/Internal/Theta/OrderTwo.lean:50`：
  `two_torsion_62_70 (b : BiHom 62 70 S_0_0) : b+b=0`。

这两个结论本身在上述语义下失败，不能只为新 exponent_two 调用寻找一个普遍成立的 2-primary 证明。仅把“同一个 ν/recovery 存在”当成该前提也不成立。

## 其他受影响调用与可合法适配范围

* ProofTools/GeneralizedMahowald 的有限商调用可研究实际对象转运；它们属于批准的有限商适配候选，没有被本报告反驳。需要保持 shift/cofiber 同构和实际滤过。
* Main/Internal/Choice/LambdaInjectivity.lean 的通用 `selected_homotopyMap_injective_of_eInfty` 从 E∞ 注入断言任意选定对象的 homotopy 注入；缩小后的 separation 不再支持其证明。进一步的真实反例方向是 sphere 上 f=3id：实际 mod-2 E∞ 上它是恒等，而普通奇挠 homotopy 核非零。本报告没有在当前项目形式化 E∞ 对3id作用的同一塔自然性，因此该项明确标为条件性数学疑点，不把它列为已形式化反例。
* Main/Internal/Theta/RealizationKernel.lean 的 `selected_homotopyMap_kernel_zero_from_f9` 同样通用，不能恢复原 unrestricted separation 或留一个新 sorry。
* Main/Internal/LowEta.lean `sphere_one_three_zero` 是 (1,3) 特例；未被上面的62-stem见证反驳，仍需真实局部消失证明。
* Main/Internal/High125/Filtration.lean 的 `.sphere` (125,130) 及普通 π₁₂₅ 26滤过零结论均未被本次见证直接反驳。新经典结论只能给奇挠；从奇挠到零还缺独立排除条件。没有本轮原始来源支持该度数的奇挠消失，故不能声称可完成、也不声称已假。

批准范围内可以更换上游签名、保持旧责任的未完成状态、对真实有限商证明作适配、对经典奇挠结论直接调用已登记 finite-map producer。不能合法伪装完成的操作包括：给 Main 新增未授权 sorry/axiom、把两个任意类引理当原样数学可证、给公开消费者悄加 2-primary 或 no-odd 假设、把固定 ordinary sphere 换成2完备球、以“用户批准接口”替代 θ₅ 的真实选择证明。

## 依赖审计及证据等级

* 反例未调用 `synthetic_homotopy_separated`、`classical_sphere_separated`、`stem62_exponent_two`、两个 Main 阶二结论或其下游。未使用 False.elim 或现存 sorry 导出矛盾。
* 真实对象数学反例依赖上述 IWX 计算、Pstrągowski 的 ν 与 λ 长正合列，以及显式群论；拓扑计算未在本项目形式化。
* 运输至 Lean 常量依赖尚未构造的 `Spectrum`、`SyntheticSpectrum`、category/cofiber 实例、`sourceRecognition`、`nu`、`recovery`、exactness 和实际 HF₂ synthetic 识别。特别是项目现有裸抽象记录不足以自动推出 Prop.4.57 的实际比较，不能把来源定理当成已在当前记录中有的字段。
* 证据等级：对真实 ordinary/HF₂ synthetic 对象为文献支持的完整数学反例；对项目 Lean 固定常量为条件性反例；没有形式化反例，没有用替代抽象模型冒充固定对象反例。
* 未找到新三个候选反例不证明其正确；有限商完整 producer 和 θ₅ 选择仍有责任。

## 复现步骤与实际结果

只读命令：`git rev-parse HEAD`；`rg -n 'synthetic_homotopy_separated|classical_sphere_separated|stem62_exponent_two' KIP126`；读取上述完整生产文件、相关定义和两个原接口报告；`git diff --` 精确观察 worker 已改的签名。实际 HEAD 与派发相符，新 separation 与 classical 签名已出现，Literature exponent_two 当时仍为旧无前提签名。没有运行 Lake，故本报告不宣称任何新签名或反例已经编译。

web 实际操作：打开两篇原论文，IWX PDF pageno7 screenshot，Pstrągowski find/open Prop4.57、Cor4.38、Prop4.40 与Theorem4.58。原文数学结果与上述推导相容。可按以上公式自行复核群论，无有限数值穷举或计算程序代替对象识别。
