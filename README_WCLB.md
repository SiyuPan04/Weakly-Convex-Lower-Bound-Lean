# 弱凸优化下界的 Lean 形式化

本工程的主要形式化库为 `WCLB`（Weakly Convex Lower Bound），稿件固定快照为 `wclb_snapshot/main.tex`。原始文件及其引用图源保持原样；逐字节 SHA256 对照记录在 `wclb_snapshot/provenance.json`。

**新稿全部 22 个正式陈述已有对应的 Lean 定义或证明，包括 `WCLB.main : WCLB.Model.MainTheorem` 和精确对数维数随机旋转归约 `WCLB.randomized_reduction`。全工程构建、覆盖检查和传递公理审计均已通过。可用 `python scripts/check_wclb.py` 复现；运行检查后生成 `verification_wclb.json` 验证回执。**

主定理给出显式通用常数 `c₀=1/512`、`c=2⁻²⁹`，在原稿的小精度条件和 gap 指数范围内，对所有 `ν∈[0,1)` 证明实际 oracle complexity 下界。函数类、完整 Fréchet 次微分 oracle、Hausdorff Borel 可测结构、真实 Moreau envelope 梯度及算法模型均复用已经证明的定义。

## 新稿与既有工程的关系

- `WC/` 保留既有数学库及证明，原稿与旧稿中相同的 coupled construction 直接复用这些定理。
- `WCLB/Model.lean`、`WCLB/Main.lean` 精确编码新稿主定理；`WCLB/UniformFamily.lean` 用新稿指定半径的真实 WCLB 函数族填满所有构造前提，再复用 WC 库中已经证明的缩放归约。
- `WCLB/Construction.lean` 验证新稿的 `5M/N` gap、显式 source 半径以及 `1/(10√N)` 的未缩放终端 Moreau 梯度下界。
- `WCLB/Radial.lean` 和 `WCLB/RadialOracle.lean` 单独验证新稿指定的半径 `R=2¹⁸(M+√(MN))`、原稿 max 函数公式、实际径向驻点下界与完整外部 oracle。
- `WCLB/Concentration.lean`、`WCLB/AdaptiveConcentration.lean`、`WCLB/Budget.lean` 和 `WCLB/RandomizedReduction.lean` 证明新稿明确要求的对数维数界。结论使用真实 Haar 旋转与 private seed 的联合概率，并同时涵盖所有查询及任意未查询的 Borel 输出。

完整次微分、鲁棒局部性和径向函数自身的 Moreau 梯度都使用实际解析对象；没有用选定次梯度或未证明的 certificate 字段代替它们。新稿终端命题采用已证明的更强 source-mixture 估计完成，原稿证明内部的二进制分组常数不是未证明的前提。

## 环境与复现

Lean `4.32.0`；mathlib 固定于 `11d11a11a667a8fa8ea19d9456fe059f683e308f`。

```powershell
lake exe cache get
lake build WCLB
python scripts/check_wclb.py
lake env lean scripts/check_wclb_coverage.lean
```

`check_wclb.py` 是最终的新稿完整性与公理检查入口。`scripts/check_wclb_coverage.lean` 核对逐项覆盖清单中的真实声明，并打印关键证明的传递公理。最终可接受的公理依赖仅为通常的 `propext`、`Classical.choice`、`Quot.sound`。

`check_wclb_coverage.lean` 已通过：94 个真实声明检查和 17 个关键结果的传递公理报告，均只含上述标准三项公理。主定理、实际 C1–C4、规定半径、完整 prefix oracle 与精确对数维数结论都在检查范围内。

`wclb_coverage.json` 与 `WCLB_COVERAGE.md` 覆盖注释剥离后新稿中的全部 22 个正式陈述。新稿有独立的验证入口与回执；旧稿验证回执不作为新稿完成证据。

原稿终端命题中“点属于终端子空间”和“隐藏坐标足够小”两种情形，均由 `WCLB.terminal_stationarity` 明确给出；子空间成员的外部坐标为零也有独立证明。
