# 弱凸优化一阶 oracle 下界的 Lean 形式化

本工程对应 Jiajin Li 和 Siyu Pan 的论文 *Optimal Oracle Complexity for Weakly Convex Optimization*，以 **2026 年 11 月 12 日版 `WC.pdf`** 为准。[逐项对照表](WCLB_COVERAGE.md)列出论文的 24 个编号陈述及其 Lean 入口；[`wclb_snapshot/`](wclb_snapshot/) 保存的是较早版本的 TeX 稿。

## 主定理

[定理 2 的 Lean 声明](WCLB/Model.lean)和[证明 `WCLB.main`](WCLB/Main.lean)给出以下下界。设 $G,\rho,\Delta,\varepsilon>0$，若

```math
\varepsilon \le \frac{1}{512}\min\left\lbrace G,\sqrt{\rho\Delta}\right\rbrace,
\qquad
\Delta \le \frac{G^2}{\rho}\exp\left(\frac{G^2}{200\varepsilon^2}\right),
```

则对每个 $\nu\in[0,1)$，

```math
\mathcal T_{\varepsilon,\nu}\bigl(\mathcal A_{\mathrm{rand}},\mathcal F(G,\rho,\Delta)\bigr)
\ge \frac{\rho G^2\Delta}{2^{29}\varepsilon^4}.
```

成功概率的门槛是 $1-\nu$。每次查询返回函数值和**整个 Fréchet 次微分集合**。算法可根据私有随机种子和已收到的回复给出任意 Borel 可测输出；该点不必被查询。成功判据是该点处 Moreau 包络的梯度范数不超过 $\varepsilon$。对于固定的正参数 $G,\rho,\Delta$，[`WCLB.main_for_sufficiently_small`](WCLB/Main.lean) 还给出了对所有 $\nu$ 同时有效的精度阈值，对应论文定理 1。

## 按论文查找证明

- **未缩放构造（条件 1，第 7 页）。** [`WCLB.construction_satisfies_conditions`](WCLB/Verification.lean)验证 C1–C4：正则性、完整 oracle 的局部性、终端梯度下界及初始函数值差距。
- **隐藏坐标与终端区域（第 13–18 页）。** [`WCLB/Certificates.lean`](WCLB/Certificates.lean) 给出活动权重的刻画、Fact 1、最大化点的位移约束与引理 9(i) 的距离界。引理 9(ii) 的严格半径界见[`source_radius_lt_three`](WCLB/Construction.lean)，引理 9(iii) 对每个次梯度的范数界见[`off_terminal_subgradient_lower`](WCLB/OffTerminal.lean)。
- **径向修改（引理 10，第 23 页）。** [径向目标与梯度界](WCLB/Radial.lean)使用原文规定的半径，并给出式 (6.1) 的内积下界；[外部 oracle 公式](WCLB/RadialOracle.lean)同时确定函数值和完整次微分。
- **随机归约与缩放（引理 11 及 §6.3，第 26–28 页）。** [`WCLB.randomized_reduction`](WCLB/RandomizedReduction.lean) 在式 (6.5) 的对数维度条件下，对独立的 Haar 随机正交标架和算法私有种子证明联合概率界。对标架取平均后，[`physical_joint_barrier_logarithmic`](WCLB/RandomizedReduction.lean) 给出一个固定的原尺度实例，使从第 0 步到第 $T$ 步的梯度同时超过阈值。主定理用同一个实例得到复杂度下界。

## 复现核验

环境固定为 Lean `4.32.0`、mathlib `11d11a11a667a8fa8ea19d9456fe059f683e308f`。在仓库根目录运行：

```sh
lake exe cache get
python3 scripts/check_wclb.py
```

如持有论文 PDF，可改用 `python3 scripts/check_wclb.py --paper /path/to/WC.pdf` 一并核对文件。参考 PDF 的 SHA-256 是 `002d3616e51469ac2bbc2c12a3e40236b3214cdc1409e3b9bee7cb3e0df63c9c`。

脚本构建项目，检查[清单](wclb_coverage.json)对应的 Lean 声明，并逐项审计传递公理依赖；允许的公理是 `propext`、`Classical.choice` 和 `Quot.sound`。本地生成的回执 `verification_wclb.json` 记录软件与源码版本及运行结果。PDF 与 Lean 声明之间的数学对应见[逐项对照表](WCLB_COVERAGE.md)，需要结合双方的定义和量词阅读。
