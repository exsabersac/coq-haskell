# coq-haskell（中文说明）

> 英文原文见 [README.md](./README.md)。本文件是面向中文读者的完整说明。

## 仓库目的

给 **Haskell 用户**用的 Gallina **薄封装**：在 Coq 里用熟悉的名字（`Functor` / `Applicative` / `Monad`、`Maybe`、do 记法……）写可抽取的函数式代码，或做算法原型与证明。

它基于 **ssreflect**，尽量少用 Coq 标准库；Haskell 命名的函数/类型在可能时只是 Coq 对应物的别名，方便和别的 Coq 代码互通。目标不是「让 Coq 看起来完全像 Haskell」，而是**缩小心智鸿沟**。

抽取时有一个重要约定：入口与回调不要用裸的 `m a`，而要用 **`Yoneda m a`**，否则抽取会擦掉类型参数 `a`。

## 和 category-theory 的区别

| | **coq-haskell**（本仓） | **category-theory**（同作者另一仓） |
|---|---|---|
| 视角 | Type 上的自函子 / Applicative / join-Monad | 对象·态射级的范畴论 |
| 用途 | Haskell 字典 + 可抽代码 | 形式化 CT |
| 依赖 | ssreflect；逻辑路径 `Hask` | 自有 `Category.Lib` 等 |
| 交叉引用 | **无** Require、无交叉引用 | 独立 |

`Control/Category.v` 更像早期 CT 草稿；正式范畴论体系在 category-theory，不在本仓。

## 构建

```bash
# 依赖（opam / CI 常见锁定）Coq 8.14–8.16 + ssreflect
# Platform 8.20 未在仓库中声明，可能需自行适配
make
```

逻辑路径：`_CoqProject` 里 `-R src Hask`。部分文件（如 `Iso`、`Eff`、`Foldable`/`Traversable`）在仓内但**未进** `_CoqProject`，默认 `make` 不编。仓内有不少 `Admitted` 与注释掉的定律，宜当「可读 typeclass 草图 + 抽取实验」，而非完整证明库。

## 模块地图（精简）

| 层 | 主要文件 | 作用 |
|---|---|---|
| 入口 / 抽取 | `Prelude.v`, `Haskell.v`, `Extract.v` | 别名、抽取映射、Separate Extraction 清单 |
| 核心类 | `Data/Functor.v`, `Control/{Applicative,Monad}.v`, `Data/{Semigroup,Monoid}.v` | F → A → M 塔；Monad 以 **join** 为原语 |
| 数据实例 | `Data/{Maybe,Either,List,…}.v` | Haskell 名 ↔ Coq 归纳型 |
| 抽取相关 | `Data/Functor/Yoneda.v` | `Yoneda` / `Coyoneda`，避免抽掉参数 |
| 控制变体 | `Compose`, `Comonad`, `Lens`, 迷你 `Category` | VL Lens 等；日常 F/M 不挂在 Category 上 |
| Monad 动物园 | `Free`/`Freer`、`Cont`/`State`、若干 `*T` | Free 归纳 vs Freer CPS；变换器 |

## ssreflect（SSR）

本仓证明风格基于 **ssreflect**。中文简要说明（是什么、战术对照、与本仓关系、不必先学透）：

→ [docs/SSR.zh-CN.md](./docs/SSR.zh-CN.md)

## 本仓库 zh-CN 注解

见 [NOTES.zh-CN.md](./NOTES.zh-CN.md)：已译文件列表、未译范围、如何继续。核心 `.v` 采用与 category-theory zh-CN 相同的中英对照注释风格（`(* EN … -------- 中文 … *)`）。
