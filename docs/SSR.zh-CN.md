# ssreflect（SSR）简要说明

> 面向阅读本仓证明风格的中文读者。不必先学完整套 MathComp。

## 是什么

**ssreflect**（Small Scale Reflection）是 Coq 的一套**证明语言 + 约定**：

- 用短、可组合的战术链改写当前目标；
- 把不少「布尔可判定」的性质，用反射接到命题（Prop）上。

本仓（coq-haskell）依赖它写 typeclass 实例与定律，风格偏 SSR，而不是一长串经典 `intros` / `apply` / `destruct`。

范畴上可粗想：你是在「证明状态」上做局部重写；Haskell 对照就是「一串小变换把表达式化到范形」——只是对象是 goal，不是值。

## 两块东西：战术 vs MathComp

| | **SSR 战术语言** | **MathComp 数学组件库** |
|---|---|---|
| 内容 | `move=>`、`rewrite`、`by`、`//`、`/=`… | 布尔谓词、`reflect`、代数层级等 |
| 本仓用法 | **主要用这块**（见 `src/Ssr.v`） | **不**整套引入；最多用到 `ssreflect` / `ssrfun` / `ssrbool` |

读本仓时：把常见战术当成「压缩版 intro / rewrite / 收尾」即可；不必先啃完 MathComp book。

## 常见战术对照（经典 ↔ SSR）

| 经典风格 | SSR 常见写法 | 作用 |
|---|---|---|
| `intros x` | `move=> x` | 引入假设 / 变量 |
| `rewrite <- H` | `rewrite -H` | 反向改写 |
| `rewrite -> H` | `rewrite H` | 正向改写 |
| `apply H` | `apply: H` | 应用引理 |
| `destruct` / `elim` | `case:` / `elim:` | 分支 / 归纳 |
| 多行 `auto` / `reflexivity` | `by []` 或 `//` | 试清 trivial 并收尾 |
| 中间化简 | `/=` | 在链中化简 |

链式例子（示意）：

```coq
move=> x y; rewrite foo /=; apply: bar.
```

本仓 `Ssr.v` 里有一句极短的样板：

```coq
Lemma and_swap : forall x y z, [&& x, y & z] = [&& y, x & z].
Proof. by case; case; case. Qed.
```

`[&& …]` 是 `ssrbool` 的布尔合取记号；`by case; case; case` 对三个布尔做穷举后直接收尾。

## 反射（reflect）一句话

`reflect P b` 把命题 `P` 和布尔值 `b` 对齐。许多分支可以写成 `case: eqP` 一类，而不是手写 `destruct (eq_dec …)`。本仓核心模块**不强制**你先掌握反射；见到再查即可。

## 和本仓的关系

- `src/Ssr.v`：统一 `Export` `ssreflect` / `ssrfun` / `ssrbool`，并带两个小工具（`decide`、`prop`）。其它 `.v` 常经 Prelude / 此文件间接用到 SSR。
- 证明义务常见形态：`Program Instance` + 短 SSR 战术链。
- 需要函数外延时仍可能出现 `functional_extensionality`——那是**公理**，不是 SSR 本身。
- `_CoqProject` / CI 期望的环境含 ssreflect；与「整套 MathComp 代数」不是一回事。

## 要不要先学透

**不必。** 读 `Functor` / `Monad` 等实例时，认得 `move=>` / `rewrite` / `by` / `//` / `/=` 就够跟着走。真要自己写证明，再对着 [Coq 手册 · SSR](https://coq.inria.fr/refman/proofs/writing-proofs/proof-mode.html#ssreflect-proof-language) 或 MathComp 教程补细节。

相关入口：[README.zh-CN.md](../README.zh-CN.md)、[NOTES.zh-CN.md](../NOTES.zh-CN.md)、[`src/Ssr.v`](../src/Ssr.v)。
