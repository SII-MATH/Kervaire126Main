# High125 获批接口后的生产适配交付

## 授权与范围

协调者在本轮明确转发用户决定：同名 `KIP126.Literature.Standard.tmf_high125_nonzero` 的结论加强为同一指定像的 `¬ IsOddTorsionMap`；维持原待补责任数量，继续完成 Main、完整 build 及后续提交/推送/Release 缓存。上游接口、锁、metadata 和共享构建均由 root 单独管理。

本 worker 只修改独占 `KIP126/Main/Internal/High125/Source.lean` 与 `Injectivity.lean`。冻结的 `Filtration.lean` 未再改动。遵守 `/root/.agents/skills/kip-upstream-session/references/protocol.md`；未新增 sorry、公理、责任或 Main 公共前提。

## 稳定生产源码

| 文件 | SHA-256 |
| --- | --- |
| Filtration.lean（本轮未改） | `a449d7e6e9141cd470b9588824cb1b6aed7de3816f0808e3d023dc040da15dd0` |
| Source.lean | `4f4c668cfe4c38e94f143dfc398a56874210456ee3b2b1bcb004b556e16f99ef` |
| Injectivity.lean | `4a9caa06a62b22e51d1603e9cabd849841641e886cf158fa0cab01b84e08f9ac` |

应用前 Source/Injectivity 哈希分别为 `183e7a9bf4ea394a526c83986d0b0318e971737e738a872e3d4731f80b87a82a`、`1f61501126f5079475a2c25ac897e6b296de322cb518495d4a4a1b698078b0ff`，与已交付局部补丁基线相符。先执行 `git apply --check` 成功，再应用 `/tmp/kip-high125-after-nonodd-approval.patch`。随后仅修正 Source 头注释，准确记录获批的同一实际 tmf 像的非奇挠源结论。

## 实际数学适配

Source 增加默认私有 `odd_postcompose`、`odd_neg`，分别证明实际映射的奇挠在后复合、取负下保留。`source_high_detected` 和 `high_nonzero_survival` 的完整类型保持不变。

`high_nonzero_survival` 不再使用错误的 ordinary F26=0。若高类的经典 E∞ 类为零，指定 high125 落入 F26；已完成的 `classical_filtration26_odd_torsion` 将它识别为奇挠，其指定 tmf 像也为奇挠，与获批上游结论矛盾。因此取得同一高类的真实非零永久存活。

Injectivity 删除旧 `high_exhaustion` 的任意检测代表唯一性路径；无用的 `high125_detector_nonzero` 也从 Source 删除。最终默认私有 helper 精确为：

```lean
detector_injective_filtration15
  (a : BiHom 125 130 S)
  (ha : FiltrationAtLeast model.syntheticTower 15 a)
  (h2 : a+a=0)
  (hz : a ≫ detectorMap=0) : a=0
```

F26 分支直接调用已完成的真实阶二尾部零结论。F25 高类分支取指定 classical high125 的原 prescribed lift b；a 与 λ20b 的差落在 F26，因此其 realization 是奇挠。后复合实际 tmfUnit，利用 a 的 detector 像零及 b 的指定 realization，推出指定 high125 的 tmf 像也是奇挠，与获批结论矛盾。

不要求 a=b，不要求 b 或指定 high125 本身已证明为2-primary，不将任意普通或 synthetic 元素当作没有奇挠。三个真正消费者由 root 负责同步，均能用本轮已证明的 η-product / η-product difference 阶二事实提供 h2，最终 Main 公共接口不变。

## 验证与边界

- 生产 `git diff --check -- Source.lean Injectivity.lean`：通过。
- 搜索 Main：旧 `high_exhaustion`、`high125_detector_nonzero`、`classical_filtration26_zero`、`high_detected_choice_unique` 已无实际引用或声明。
- 完整数学主体已在 `/tmp/kip-high125-conditional.lean` 以显式 `hImageNonodd` 独立验证，实际退出码0。生产适配将该参数精确替换为同名获批上游事实；没有额外生产前提。
- 原始验证日志 `/tmp/kip-high125-conditional-validation.log` SHA-256 `124d6e550106a3879ac11d5d4bd30effa19a29c72af3bd7aa1aa3322521b8f3b`；机器记录 `/tmp/kip-high125-conditional-validation.json`；条件源码 SHA-256 `c0d7176185edf348511c9c6dde00f4198aacd938e6428a9b534b25d72a8e3475`。
- 冻结的生产 Filtration 已由协调者共享 Lake 构建通过，共2766 jobs。此前完整桥、η阶二、finite λ kernel 的验证及来源记录见 `/tmp/kip-main-reproof-high125.md`。
- Source/Injectivity 的分文件公共消费、完整 Main 与完整项目构建由 root 统一运行；本 worker 没有运行会写共享 `.lake/build/` 的 Lake build。最终是否整项目通过以 root 的本轮日志为准。

真实传递依赖仍保留：固定范畴/对象与模型构造、finite_map_separation、有限 λ 商 separation、BHS finite/permanent/prescribed lifts 与 realization kernel、实际计算数据，以及现有同名 tmf 高125像非奇挠 Literature 责任。局部适配完成不等于这些上游待补责任已证明。
