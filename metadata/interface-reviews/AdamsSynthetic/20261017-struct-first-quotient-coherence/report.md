---
issue_id: AdamsSynthetic-20261017-struct-first-quotient-coherence
responsibility_module: AdamsSynthetic
targets:
  - KIP126.AdamsSynthetic.Standard.firstQuotient_positive_shift
  - KIP126.AdamsSynthetic.Standard.firstQuotient_suspension
baseline_commit: bef90640c4594af4db32c86837f9d95340d1e171
worktree: /tmp/kip-adams-synthetic-20261017-struct
candidate_source_commit: a484b981fad612eabe2bc7a01b54e049e9a01ce4
api_file_and_sha256: "metadata/adams-synthetic-api.json: 2fb1b8af37f2e926d72c3e6e8bceb13ec37c5574325f9511d92bb9676e8f20e2"
source_file_and_sha256: "KIP126/AdamsSynthetic/Standard/FirstQuotientCompatibility.lean: 02b1951901c4263d46b4bfcbe38e1080ade1afd24258a509ab1a2eecbb518f3d"
reporter_agent: /root/quotient_interface_reporter
independent_of_discoverer_and_implementer: true
evidence_level: "独立源码/契约核验；抽象分裂余纤维的有限穷举；只读 Lean 依赖审计；固定对象刚性有传递待补的条件性证明路线；无固定 Standard 反例"
status: pending-human-review
human_decision: null
---

# 接口调整人审报告

> 本文初版形成时的状态与证据保留为历史记录。本轮后续已补完两项 ClassicalSupport 直接证明，并完成 sphere-source 的任意 δ inclusion rigidity 局部证明；最新范围、依赖及验证见文末“本轮后续进展”。审核状态及接口保留建议未改变。

## 请求人类决定的具体问题

**独立结论：两个固定 Standard 声明仍是未完成的证明责任；现有证据不足以认定它们为假，也不足以认定必须改变接口。建议保留原签名、对象关联和 AdamsSynthetic 责任。** 本报告未参与候选的发现或实现；独立阅读了声明、固定模型、比较、检测、商、悬挂、调用方和传递依赖，并重新运行了证据。

本报告列出的可选决定是：

1. **方案 A（建议）：保留原接口。** 继续在 AdamsSynthetic 内建立所选首商比较的权移位/悬挂相容性和实际商的球映射刚性。常规的保接口补证明已有授权，无须因本报告再次等待批准。
2. 只有人类明确决定收缩原来的“任意满足 inclusion square 的 ε”语义时，才考虑下文精确的 **方案 B：改成存在一个相容 ε**。它削弱任意性保证，同时增加 ε 存在性的生产者责任，改变调用方式；本报告不建议现在实施，未证明它是必要修复，也不视为已获授权。若选择 B，请明确是否仅改变这两个声明及其契约/测试、是否允许协调者另派 ProofTools 所有者修改直接消费者。

本报告不请求新增模型假设、结果包、公理、下游待补责任或恢复已排除的基础模型/具体识别路线。人类对其他问题的决定不适用于本报告。

## 原接口、背景与问题成因

两项责任在 `KIP126/AdamsSynthetic/Standard/FirstQuotientCompatibility.lean`，由 `KIP126.AdamsSynthetic.Standard` 导出，均属于 AdamsSynthetic。它们服务于 MH2 中同一经典类在正权移位与经典/合成悬挂之后的**实际同伦类等式**。

契约 `first-quotient-shift-suspension-compatibility` 明确锁定 `Standard.model`、正权移位 `(0,1)`、既有 `DesuspendsClass` 和固定 `nu.suspensionIso`；`source_locators` 为空。源文件与待补记录均说明：这两项是 2026-10-16 单独授权新增的待证兼容性，不是从 a484b981 迁来的已证定理。只读查看该历史提交的首商和 finite-Bockstein 数据文件，也只得到比较族、球特化及 `a=0` 的 transport，没有这两项当前目标的证明。原论文范围仅是上下文，不能冒充本签名的来源证明。

完整原接口如下。该节没有隐式的泛型 `Model`、额外宇宙参数或额外实例参数；API 的 `universes` 为 `[]`。对象及实例均固定：`Spectrum : Type 1`、`SyntheticSpectrum : Type 1`、hom universe `0`，使用 `Standard.spectrumCategory`、`syntheticCategory`、`spectrumCofiber` 和 `syntheticCofiber`。下面的 namespace/open/option 是原文件上下文；没有省略数学前提。

```lean
namespace KIP126.AdamsSynthetic.Standard
open CategoryTheory
open KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Synthetic.SpectralSequence KIP126.Kervaire.Route
noncomputable section
set_option backward.isDefEq.respectTransparency false

public theorem firstQuotient_positive_shift
    (X : ClassicalObject) (s t : ℤ)
    (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t))
    (ε : XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) 1 ≅
      (SyntheticCategory.biShift (0,1)).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) 1))
    (hε : XModLambdaN.incl _ 1 ≫ ε.hom =
      (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl _ 1)) :
    homotopyRegrade (by simp) (by simp)
      (shiftHomotopyClass (0,1) (t-s,t)
        (homotopyRegrade rfl (by simp) ((model.firstQuotient X 0 s t).symm x) ≫
          XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1)) ≫ ε.inv =
        (model.firstQuotient X 1 s t).symm x := by
  sorry

public theorem firstQuotient_suspension
    (X : ClassicalObject) (s t : ℤ)
    (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t))
    (sx : (model.classical.obj ((ClassicalObject.shift 1 X).obj model.auxiliary)).Page 2 (s,t+1))
    (ε : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) 1 ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) 1))
    (hε : XModLambdaN.incl _ 1 ≫ ε.hom =
      (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ 1))
    (hsx : (model.classicalSuspension X).DesuspendsClass s (t+1) sx (by simpa using x)) :
    (homotopyRegrade (w' := t+1) rfl (by simp)
        ((model.firstQuotient (.shift 1 X) 0 s (t+1)).symm sx) ≫
      XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1) ≫
      XModLambdaN.map (model.nu.suspensionIso (X.obj model.auxiliary)).hom 1 ≫ ε.hom =
    homotopyRegrade (by simp; omega) (by simp)
      (shiftHomotopyClass (1,1) (t-s,t)
        (homotopyRegrade rfl (by simp) ((model.firstQuotient X 0 s t).symm x) ≫
          XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1)) := by
  sorry

end
end KIP126.AdamsSynthetic.Standard
```

问题有两个不同部分。

- `FirstQuotientComparison A N aux` 在 `Compatibility.lean:71` 只是
  `∀ (X : ClassicalObject) (a s t : ℤ), BiHom (t-s) (t+a) (XModLambdaN (biShift (0,a) (N X)) 1) ≃ₗ[ℤ] A(X).Page 2 (s,t)`。
  该类型没有把不同 `a`、`X` 与 `.shift 1 X` 的分量连接起来。但这不自动构成漏前提：当前两项 theorem 本来就是为**所选固定比较的构造**证明这些相容性，未要求从任意比较族的类型直接推出。
- `hε` 只规定实际 inclusion square，却要求对所有这样的 ε 给相同等式。一般余纤维范畴中，这确实需要额外的“在相关球映射上刚性”论证；固定 Standard 范畴可能具备这种刚性。独立核验发现，本仓库已经有不依赖这两项目标的条件性刚性论证，详见下文。

目前分类如下：**未确认假命题；未确认漏前提；未发现目标中的符号、次数或对象约定错配；未交付错误实现；已确认现有两个 `sorry` 及比较构造尚不足以当作完成的证明。** 把“比较族没把自然性存成字段”直接判为接口错误，会混淆定义的数据边界与需要另证的性质。

## 真实前提与对象核对

| 前提或对象条件 | 是否满足 | 独立核对与待补依赖 |
| --- | --- | --- |
| 固定 `model`，而非任意可替换背景 | 是，声明本身固定 | `Standard/Background.lean:124` 显式组装，`model.firstQuotient` 就是 `Standard.firstQuotient`；组装没有独立存在假设。 |
| `X` 的真实范围 | 已核对 | `Configuration.lean:28–40` 仅 sphere、ν-map 的实际 cofiber、detector 及整数 shift；不包含任意分裂直和闭包。抽象例子尚未嵌入此范围。 |
| 经典类/分次 | 是，原声明完整保留 | 正权移位保持 `(s,t)`，目标 BiHom 权重 `t+1`；悬挂是 `(.shift 1 X,s,t+1)`，stem 增加 1，使用实际 `(1,1)` shift。 |
| 商对象 | 是 | `XModLambdaN V 1` 定义为同一个 `lambdaPow 1 V` 的所选 cofiber；`incl`、`proj`、`map` 是该构造的实际映射。 |
| 任意 ε 的 inclusion square | 是，真实而不冗余的前提 | 两项都只显式要求 inclusion square；不能自行附加 projection/representative/coherence 假设。 |
| 悬挂类关系 `hsx` | 是 | `Suspension.lean:60` 的关系含实际 E₁-cycle 代表、真实 page projection 和同一 classical tower 的 layer desuspension；不是可任取的线性同构。 |
| 固定 `nu.suspensionIso` | 是 | `Context.lean:204` 是同一 `NuFunctorData` 的字段；没有存储与 `firstQuotient` 的兼容性。必须由固定构造来证明，不能更换为另一 iso。 |
| 比较族的权移位/悬挂相容性 | 尚未证明 | `Standard.firstQuotient` 仍为 deferred construction。`E2Comparison` 的 `nu_natural` 只管同一 `a` 的映射；`nu_lambda` 管既定 λ 操作，均不等于这两个标签方块。 |
| 模型中已有的首商约束 | 已核对，不能忽略 | `ComparisonCompatible.first_quotient` 要求 inverse label 被实际 quotient page image 检测；任意独立扭转比较族未必满足它，因而不能作为完整 Model 反例。 |
| 同检测能否直接给同伦类相等 | 一般不能 | `Detection.lean:251` 实际结论为差落在 `s+1` filtration；单次提高 filtration 不等于落在全部 filtration。有限窗口与分离合用才可能消去。 |
| 固定对象的 ε 刚性 | 条件性支持，非完成 | 现有 NoReturn/QuotientShift 证明对整个 `ClassicalObject` 范围成立，但含文献窗口、ESS shift、synthetic separation 等未补传递责任；不能反向导入 AdamsSynthetic。 |

## 独立证据与复现

### 1. 任意 ε 的准确刚性要求

令 `V = model.nu.functor.obj (X.obj model.auxiliary)`，`F = biShift δ`，`Qδ = XModLambdaN (F.obj V) 1`，`Rδ = F.obj (XModLambdaN V 1)`，`jδ = F.map (XModLambdaN.incl V 1)`。给定 `ε₀ : Qδ ≅ Rδ` 满足 inclusion square。任何 `α : Rδ ≅ Rδ` 满足 `jδ ≫ α.hom = jδ` 时，`ε₀ ≪≫ α` 也满足同一前提。

对正权移位，记已经 shift 的左侧类为 `c : Smn (t-s) (t+1) ⟶ Rδ`、右侧 inverse label 为 `b`。原目标对 ε₀ 和 `ε₀ ≪≫ α` 同时成立，会给出

```text
c ≫ ε₀.inv = b,
c ≫ α.inv ≫ ε₀.inv = b,
从而 c ≫ α.inv = c。
```

对悬挂，记不含 ε 的左侧类为 `a`、右侧 shift 类为 `c`，同样得到 `a ≫ ε₀.hom = c` 与 `a ≫ ε₀.hom ≫ α.hom = c`，因此 `c ≫ α.hom = c`。这只是从原量词推得必要条件；未假设 α 在固定范畴中非平凡。

### 2. 分裂余纤维的有限证据及其限制

独立编写并运行 [inclusion_stabilizer.py](evidence/inclusion_stabilizer.py)。在 `F₂³ = B ⊕ D` 中穷举全部 512 个矩阵：可逆者 168 个，固定 `B` inclusion 者 24 个，其中 20 个移动 `e₁`；同时固定 inclusion 和 projection 者仍有 4 个。明确的 involution 是

```text
α(b,d₀,d₁) = (b+d₀,d₀,d₁),  α(e₁) = e₀+e₁ ≠ e₁。
```

该例可作为 `Dᵇ(F₂-Vect)` 内零映射 `D[-1] → B` 的 split-cofiber 局部模型。它说明泛型 categorical cancellation 不成立，**也说明单独再添 projection square 并不自动修复问题**。该模型没有识别为固定 Standard 的 λ 商，没有其 Adams tower、ν、检测、固定 comparison 或对象闭包见证，所以证据等级仅为“抽象局部模型的有限穷举”，不是完整数学/Lean 的固定对象反例，也不能据此冻结整个模块。

实际结果记录在 [finite-result.json](evidence/finite-result.json)：`PASS`，上述计数全部通过断言。复现命令：

```sh
python3 /inspire/hdd/global_user/czxs25250150/Kervaire126Main/metadata/interface-reviews/AdamsSynthetic/20261017-struct-first-quotient-coherence/evidence/inclusion_stabilizer.py
```

### 3. 固定对象上的现有条件性刚性路线

独立查看消费者时发现：

- `ProofTools/GeneralizedMahowald/NoReturn.lean:66` 的 `quotient_nu_maps_equal_on_spheres`：对于任意所选 `X,Y` 和正有限商长度，同 inclusion 的两个商映射在全部 BiHom 上作用相同。
- `QuotientShift.lean:60` 的 `shifted_quotient_sphere_congruence`：把该结果运输到任意实际 bigraded shift；它足以处理原目标中不同 inclusion-compatible ε 的歧义，**一旦基准 ε 的标签相容性已经建立**。

其数学步骤是：映射之差由 cofiber exactness 因子分解经 connecting map；固定 ν 的负权移位源类先被迫进入较高 filtration；有限 λ 商的窗口和 `synthetic_homotopy_separated` 再消去其像。该步骤适用于 `.nuCofiber`、`.detector` 及其 shifts，不局限于 sphere，因此局部抽象例子不能反驳固定对象的刚性。

这是一条有实际 Lean 实现的**条件性**路线。用 [CacheDependencyAudit.lean](evidence/CacheDependencyAudit.lean) 对上述两个 proof root 的项目常量闭包进行了只读审计；Lean v4.32.2 返回码 `0`。两者均实际输出：

```text
positive_target_in_closure = false
suspension_target_in_closure = false
axioms = [propext, sorryAx, Classical.choice, Quot.sound]
```

闭包明确含：`Literature.Standard.eInfinity_nu`、`eInfinity_finite`、`AdamsSynthetic.Standard.synthetic_homotopy_separated`、`essShift`、`shift_filtered`、`shift_ambient_eq`、`shift_page`、`shift_representative_iff`，以及固定背景的待补构造。这些是依赖审计所得，不是把编译成功称为无未证依赖。完整 [审计日志](evidence/cache-dependency-audit.log)、[简表](evidence/cache-audit-summary.json)、[确切命令及 LEAN_PATH](evidence/cache-audit-command.txt) 均已保存。读取了主工作区已有编译缓存，28 个所核 source/metadata 文件与研究 worktree 的对应源码 SHA 均匹配；没有重建全部缓存，不能据此声称所有传递缓存已做干净构建验证。可用 [复现脚本](evidence/reproduce_cache_audit.py) 重新执行：

```sh
python3 /inspire/hdd/global_user/czxs25250150/Kervaire126Main/metadata/interface-reviews/AdamsSynthetic/20261017-struct-first-quotient-coherence/evidence/reproduce_cache_audit.py
```

此路线没有在常量闭包内调用本报告的两个目标，未发现这两个目标的循环。它仍不能直接搬作 AdamsSynthetic 的实现：AdamsSynthetic 反向导入 ProofTools 或 Literature 会违反模块依赖方向/责任边界；其窗口、分离和比较构造的未证责任也不能被忽略。可学习其私有证明分解，再从本模块可用的真实上游边界建立相应结构性质；不能把文献结果改挂为新的 AdamsSynthetic 公理或向下游索要证明包。

另一个较窄的 sphere 方案是：歧义因子所属 `Hom(ΣΣ^(0,-1)νS,νS/λ)` 经 fixed unit/shift/quotient transport 化为 `BiHom(1,-1)`；首商比较把它关联到 `E₂(-2,-1)`，负 filtration vanishing 可令其为零。该 reduction 尚需实际 coherence 证明；`firstQuotient` 和 `classical_page_negative` 本身也未补，故同样只有条件性。对 `.nuCofiber`、`.detector`，仅 sphere 源的 `FirstQuotientComparison` 不能直接给带 `νX` 源的映射群比较；上述有限窗口法避免了这一步的过强要求。

### 4. 循环、未证与矛盾依赖结论

有限计算仅依赖 Python 标准库和显式有限矩阵，不调用任何项目待补、公理或目标。固定对象的条件性刚性审计如上，含 `sorryAx` 及登记待补，不能充当最终无假设的证明，也不能用于从不一致推出反例。未发现当前两项目标互相调用或被上述刚性 proof root 调回。首商族扭转的形式自由只是对其**裸类型**的观察：若不同时满足 `ComparisonCompatible.first_quotient`、球检测等全模型条件，就没有完整 Model 反例。

所有输入指纹、完整原接口、完整目标 metadata 记录、当前定义节选和 a484b981 的原始文件内容分别保存在 [input-sha256.json](evidence/input-sha256.json)、[original-interface.lean.txt](evidence/original-interface.lean.txt)、[metadata-excerpts.json](evidence/metadata-excerpts.json)、[source-excerpts.txt](evidence/source-excerpts.txt)。本报告没有新增或消去项目待补责任。

## 方案及精确差异

### 方案 A：保持原接口（建议）

没有名称、类型、前提、结论、对象关联、导出或责任变化。先完成两类私有步骤：

1. 对指定 `Standard.firstQuotient` 的实际构造，证明一个结构上选定的 quotient/shift 比较下的标签方块；悬挂方块必须使用现有 `DesuspendsClass` 的实际代表与固定 `nu.suspensionIso`。不能把想证的方块作为新 Model 字段后宣称完成。
2. 在现有模块边界内建立相关球映射上的 ε 独立性。所需是诱导作用唯一，不要求证明整个 cofiber iso 唯一。已有固定对象的 no-return 方法表明这一方向有具体数学支撑，但传递责任仍须照实保留。

第一步也可以在实现尚待构造的比较族时，把所有 `a` 分量从一个 coherent 的基础分量与实际 transport 构造出来，再证明与 `model.comparisonCompatible.first_quotient` 等既有约束一致。这属于保类型构造方案，不能在不核对固定对象身份和全部现有检测约束的情况下自由更换比较族。

当前不能声称仅用 `E2Comparison.nu_natural`、`nu_lambda` 或 `Detects` 已完成这两步。也没有证据表明这两步在固定模型上不可能，因此没有依据把附加前提当默认修复。

### 方案 B：存在一个 ε（仅供明确决定语义收缩时比较）

以下给出准确候选签名（使用上文相同 namespace/open/固定实例上下文），保留所有固定对象、分次、实际 map 和悬挂类前提。变化严格限定为：原来的函数参数 `ε`、`hε` 移入结论中的 `∃ ε, inclusion-square ∧ label-equation`；悬挂的 `hsx` 保持为输入参数。这些只是报告内的拟议签名，没有应用、引入新待补或声称编译。

```lean
public theorem firstQuotient_positive_shift
    (X : ClassicalObject) (s t : ℤ)
    (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t)) :
    ∃ ε : XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) 1 ≅
      (SyntheticCategory.biShift (0,1)).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) 1),
    (XModLambdaN.incl _ 1 ≫ ε.hom =
      (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl _ 1)) ∧
    (homotopyRegrade (by simp) (by simp)
      (shiftHomotopyClass (0,1) (t-s,t)
        (homotopyRegrade rfl (by simp) ((model.firstQuotient X 0 s t).symm x) ≫
          XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1)) ≫ ε.inv =
        (model.firstQuotient X 1 s t).symm x)

public theorem firstQuotient_suspension
    (X : ClassicalObject) (s t : ℤ)
    (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t))
    (sx : (model.classical.obj ((ClassicalObject.shift 1 X).obj model.auxiliary)).Page 2 (s,t+1))
    (hsx : (model.classicalSuspension X).DesuspendsClass s (t+1) sx (by simpa using x)) :
    ∃ ε : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) 1 ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) 1),
    (XModLambdaN.incl _ 1 ≫ ε.hom =
      (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ 1)) ∧
    ((homotopyRegrade (w' := t+1) rfl (by simp)
        ((model.firstQuotient (.shift 1 X) 0 s (t+1)).symm sx) ≫
      XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1) ≫
      XModLambdaN.map (model.nu.suspensionIso (X.obj model.auxiliary)).hom 1 ≫ ε.hom =
    homotopyRegrade (by simp; omega) (by simp)
      (shiftHomotopyClass (1,1) (t-s,t)
        (homotopyRegrade rfl (by simp) ((model.firstQuotient X 0 s t).symm x) ≫
          XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1)))
```

正权移位由

```text
∀ X s t x, ∀ ε, inclusionSquare ε → positiveLabelEquation X s t x ε
```

改为

```text
∀ X s t x, ∃ ε, inclusionSquare ε ∧ positiveLabelEquation X s t x ε。
```

悬挂由

```text
∀ X s t x sx, ∀ ε, inclusionSquare ε → DesuspendsClass x sx → suspensionLabelEquation x sx ε
```

改为

```text
∀ X s t x sx, DesuspendsClass x sx → ∃ ε, inclusionSquare ε ∧ suspensionLabelEquation x sx ε。
```

B 去掉任意 ε 的刚性保证，并增加生产者交付 ε 的存在性。它不证明两个接口原先为假，也不免除固定比较的标签相容性；ε 甚至可随类变化，因而弱于选定一个全局自然的 canonical quotient-shift comparison。当前原签名本身只条件性讨论给定 ε，不保证 ε 存在，所以纯逻辑上不能在不额外证明实际 ε 存在的情况下称其单向蕴含 B；固定模型已有 exact-shift triangle 构造给出了这条结构存在性路线。

B 的证明责任仍全部在 AdamsSynthetic。下游应消费生产者交付的 ε，不能被迫另证刚性或提供兼容性包。`QuotientShift` 中处理不同有限商 restriction 的兼容性还要保持；不能因为第一层标签只获存在就默默沿用任意 ε 的私有帮助引理。已有 `quotient_shift_exists` 的完整 triangle square 也不能仅凭“一般 cofiber map 唯一”来消除此核对，有限 shear 证据已经否定那个泛型理由。

另一种候选是在 AdamsSynthetic 新增全局 canonical quotient-shift comparison 并仅对它陈述两项定理。这比 B 更强地固定对象关联，但增加公共声明和新的构造/自然性责任；现阶段没有现成、无歧义的已登记 canonical 定义可精确引用，因此本报告没有将它提交为可立即实施的签名方案。单独增加 projection square、为下游补一个 `hcoherent` 前提，或把两目标写成 Model 字段，均不作为默认修复。

## 下游影响

| 对象/记录 | 方案 A | 方案 B 的实际影响及所有者 |
| --- | --- | --- |
| `Standard.FirstQuotientCompatibility` 两声明 | 名称/类型/责任保持 | AdamsSynthetic 修改两个完整签名及证明；必须另获明确授权。 |
| `Standard.firstQuotient`、`ModelData.firstQuotient`、`ComparisonCompatible.first_quotient` | 仍需同一个比较构造；不加字段 | B 本身不更改这些；仍须完成实际标签兼容性，不能把它们判为已完成。 |
| `ProofTools/GeneralizedMahowald/HSource.lean:109` 的 `positive_first_desuspend`，及其 finite-source 链 | 正常消费既有上游责任 | 原先为任意 ε；需由 ProofTools 所有者改为消费生产者 witness，并核对 `:244` 附近为 q 商选择的 ε 与第一层限制相容。 |
| `ProofTools/GeneralizedMahowald/SuspensionTarget.lean:30` 的 `suspension_first_unshift`、`:58` 的 finite-target 链 | 同上 | 原先为任意 ε；需由 ProofTools 所有者调整 `:129` 附近 witness 的选择及后续 restriction transport。 |
| GeneralizedMahowald 的公开 law、Main 的 MH2/主结果依赖 | 传递待补保持可见 | 不得声称 B 立即证明相同下游结论；先完成调用方修改及审计。没有自动授权修改其公共接口。 |
| `metadata/adams-synthetic-api.json` | 无锁变化 | 两类型指纹 `13497849682890837448`、`15839982846520915617` 和 exports 捕获需按批准后真实声明更新；禁止先改锁绕过。 |
| `metadata/adams-synthetic-contracts.json` / `-sources.json` | 保留 pending 与真实来源 | 修改对应 capability、任意 ε 的语义、来源和状态，不虚构迁移证明。 |
| `metadata/proof-obligations.json` | 两条原 pending 保留 | 更新真实完整类型/理由；不添加下游补证包；证明前不能移除 pending。 |
| `metadata/module-path-migration.json`、ProofTools 来源/契约的既有相关记录 | 当前历史事实不改 | 协调者核对其中“新兼容性义务”和消费者说明；只更新真实受影响记录，保留历史授权原话。 |
| `Tests/AdamsSynthetic/Structural.lean:168,189` | 原普通消费测试继续 | 两个当前精确调用例需改 witness 形式；同时保留冻结接口、普通导入和可见性边界覆盖。 |
| `Tests/AdamsSynthetic/Interface.lean`、`InternalAudit.lean`、`Tests/ProofTools/*`、`Tests.Integration`、`Tests.Architecture`、`Tests.Trust` | 保持已有覆盖 | 协调者整合后跑源码清单、接口/信任/消费者审计与完整 `lake build`；不删除覆盖来令测试通过。 |

本报告员未修改任何生产源码、接口锁、来源记录、待补清单或共享构建状态。已存在的并行编辑（如 `Standard/Filtration.lean`）未回退。没有 push/pull/发布，因此没有触发新的 Release 缓存同步动作。

## 阻塞范围与继续项

**实际未完成目标**恰为这两个原始 proof responsibility，以及“它们已经无直接/传递缺口完成”的交付断言。其依赖的固定比较构造与真实代表相容性尚未完成；没有得到固定 Standard 反例，故不能因本报告把全部 AdamsSynthetic 冻结，或把任意 ε 的调用一律宣布无效。原规则允许正常消费已登记上游待证接口，仍须报告其未证依赖。

**需人类明确决定才可实施的范围**仅为 B 或任何公开类型/语义/责任调整；本报告仍为 `pending-human-review`、`human_decision: null`。A 中正常保接口补证不因等待本报告决定而暂停。

可继续的独立工作：graded/filtration 的纯结构引理、convergence/map transport 的保接口证明、quotient 的函子性/coherence 私有推导、固定背景组装中不依赖争议标签等式的 transport、来源与实际依赖审计。可以继续在 AdamsSynthetic 内寻找基准标签方块与球作用刚性；不要为避开困难转到本 session 已排除的 Prespectrum/HF₂/完备化、Steenrod/Milnor/cobar 或具体识别/原始计算证书路线。

本报告的验证限于指纹/源码及 metadata 核对、有限穷举和实际只读 Lean 缓存依赖审计。未运行全局 `lake build` 或更新项目记录；这些共享动作由协调者在整合阶段统一执行。

## 本轮后续进展（2026-10-17，初版之后追加）

本节只更新本轮证明进展，不覆写初版证据或更改前述接口建议。进展发生在研究工作树 `/tmp/kip-adams-synthetic-20261017-struct`；报告存放于主工作区不表示主工作区生产源码已同步。追加前的完整报告已原样保存为 [report-before-followup.md](evidence/followup-20261017/report-before-followup.md)。初版 `SHA256SUMS` 中 `report.md` 的指纹对应这个历史快照；追加后报告及新增证据的指纹另列于 [本轮校验清单](evidence/followup-20261017/SHA256SUMS)，原证据文件未改。

### 两项 ClassicalSupport 直接责任已消除

独立重新阅读当前 `ClassicalSupport.lean`，其 SHA-256 为 `c576f2e00939f5638d37f19d3a8d89cf67bcb7cceb3870e1cd864068e08e4fd3`；快照见 [ClassicalSupport.lean.txt](evidence/followup-20261017/ClassicalSupport.lean.txt)。`classical_page_negative` 和 `sphere_page_filtration_zero` 已有实际证明体，不能再把它们列为本轮未完成的直接责任。

- `classical_page_negative` 用 `s<0` 得到相邻整数 stages 均索引到自然数 0，同一 tower transition 因而为同构，真实 cofiber layer 为零；同一 `classicalTower.sequence.ambient` 把 first-page homotopy 识别为谱序列 ambient，再由 cycle subobject 和 page quotient 推出每个整数 `r` 的 page 都为 subsingleton。
- `sphere_page_filtration_zero` 通过同一 tower 的 `layerIso 0`、`zeroIso` 和右 unit iso 识别系数对象，应用真实的系数同伦消失，再用相同的 ambient/subquotient 步骤。没有借用 sphere separation、ESSShift 或两个首商兼容性目标。

已查看并保存 worker 的 [裸 Lean 验证记录](evidence/followup-20261017/worker-classical-support-validation.json) 及另一审计员的 [kernel 对比](evidence/followup-20261017/independent-classical-support-kernel-comparison.json)：两项 `direct_sorry=false`，完整类型、type fingerprint、universes 与冻结基线全等，未发现未登记直接责任。该审计的 [实际日志](evidence/followup-20261017/independent-classical-support-final-kernel.log) 仍有未改动的 `classical_sphere_separated` warning；不能把这个 warning 误记为上述两项仍有直接 `sorry`。整个固定背景仍有传递待补，kernel 列表通过 `model` 数据装配保守包含 24 项，不能把这两项局部完成扩大为整个背景完成。报告员本次独立阅读证明并核对已有 kernel 证据，没有再次运行该生产文件的完整 kernel 捕获。

### Sphere-source 的任意 δ inclusion rigidity 已有检查通过的局部证明

独立阅读并保存 [Rigidity.lean](evidence/followup-20261017/Rigidity.lean)，随后用锁定 Lean v4.32.2 对该证据快照重新运行无输出文件的 bare Lean；[报告员实际日志](evidence/followup-20261017/reporter-rigidity-check.log) 返回码为 `0`，[调用记录](evidence/followup-20261017/reporter-rigidity-command.txt) 记录只读缓存路径。没有运行 Lake 或写入 `.lake`。这确认研究辅助证明本身通过检查；其导入的固定背景仍有登记待补，因此仍不是无传递缺口的闭合模型证明。

本轮已实现初版中尚待实际 coherence 的 sphere 路线：

1. 对任意目标 `Y : ClassicalObject`，由同一首商比较、实际零移位商函子 transport 及现已补完的 `classical_page_negative` 得到

   ```lean
   w - m < 0 →
     Subsingleton (BiHom m w
       (XModLambdaN (model.nu.functor.obj (Y.obj model.auxiliary)) 1))
   ```

2. 固定 `nu.unitIso` 和 bigraded shift 对象同构将 νSphere 的 suspended λ-boundary 识别为 `Smn 1 (-1)`；对应 filtration `-2`，故该源到任意所选首商的 Hom 为 subsingleton。
3. 对两映射之差使用 cofiber triangle 的 `yoneda_exact₃`。边界 Hom 消失因此给出**实际映射相等**，比只要求诱导 BiHom 作用相同更强。
4. 新的 `lambda_boundary_shift_iso` 用实际对象级 bigraded shift 同构和整数次数等式交换边界与任意 `δ : ℤ × ℤ`，随后以 full faithfulness 运输 Hom 消失。这里没有 ESS 页面/滤过 shift 比较。

准确覆盖范围是：对于任意目标 `Y : ClassicalObject`、任意 δ，以下源/目标之间的映射由它们与 inclusion 的复合唯一确定：

```lean
XModLambdaN ((SyntheticCategory.biShift δ).obj
    (model.nu.functor.obj (SphereSpectrum (C := Spectrum)))) 1 ⟶
  (SyntheticCategory.biShift δ).obj
    (XModLambdaN (model.nu.functor.obj (Y.obj model.auxiliary)) 1)
```

特别地，目标也取 `.sphere` 时，原两项接口在 `X=.sphere` 的任意两份 inclusion-compatible ε **相等**；覆盖 `(0,1)`、`(1,1)`，并且对所有 δ 成立。一般 split-cofiber 的局部有限模型因此不能作为该固定特例的反例。

这条新路线不使用 `synthetic_homotopy_separated`、`eInfinity_nu`、`eInfinity_finite`、ESSShift 或任何下游 ProofTools/Literature 结果，也不调用两个首商兼容性目标。其 `#print axioms` 仍实际输出 `[propext, sorryAx, Classical.choice, Quot.sound]`：`Rigidity.lean` 本身无 `sorry` body，`sorryAx` 来自 firstQuotient、ν、商函子性、范畴等既有固定背景构造。不能把这些传递责任说成已完成，也不能把该局部辅助证明登记为已完成的原公共目标。

### 尚未完成的范围与审核状态

两项公共 `firstQuotient_positive_shift`、`firstQuotient_suspension` 的严格标签等式仍未完成。即使 `X=.sphere` 上 ε 唯一，也还需要所选 `Standard.firstQuotient` 的跨权移位和经典/合成悬挂 normalization，唯一性本身不构造那个标签方块。

对一般源 `X`，新直接消去法所需的

```lean
Subsingleton
  (((SyntheticCategory.biShift (0,-1)).obj
      (model.nu.functor.obj (X.obj model.auxiliary)))⟦(1 : ℤ)⟧ ⟶
    XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) 1)
```

仍未建立；任意 `BiHom` 的负 filtration 消失只涉及 sphere 源，不能直接替换此处的任意 `νX` 源。初版中依赖窗口/分离的现有下游条件性论证仍可作为背景证据，但不能反向导入 AdamsSynthetic。因此不能把 sphere-source 新成果推广到全部 νCν/detector 及 shifts，也不能据此消除原两个公共直接责任。

本轮进展加强“优先保留原接口”的建议，没有授权或实施方案 B。`status` 仍为 `pending-human-review`，`human_decision` 仍为 `null`；可以继续一般源刚性研究与严格标签 normalization 等保接口工作。本报告员只追加报告和独占目录的证据，没有改生产源码、接口锁、共享记录或原始历史证据。

## 人类审核记录

