# zh-CN 注解进度说明

## 风格

证明语言说明见 [docs/SSR.zh-CN.md](./docs/SSR.zh-CN.md)（ssreflect 简要）。

与 category-theory 的 zh-CN 分支一致：

- 块注释：`(*` 英文原意（可略压缩）→ 一行 `--------` → 中文对照 `*)`
- 短行：`(* EN / 中文 *)`
- **不改** Coq 标识符与代码逻辑，只加/改注释与文档

## 进行中（四路并行 / 按目录）

本轮在 `zh-CN` 上拆 worktree **并行**补译，互不改对方目录：

| worktree / 分支 | 负责目录 |
|---|---|
| `zh-CN-data` | `src/Data/**`（实例、Monoid、Functor 变体等） |
| `zh-CN-control` | `src/Control/**`（不含 `Control/Monad/**` 深处时可另分） |
| `zh-CN-monad` | `src/Control/Monad/**`（Free、Freer、State、Cont、Trans…） |
| `zh-CN-misc` | 根 `src/*.v` 剩余 + `research/` |

合并前各分支只 commit、**不 push**；**不能**据此认为全仓已译完——其他 worktree 的最终结果在本目录看不到。

## 已译（早期核心切片 + misc 本批）

| 路径 | 内容 |
|---|---|
| `README.zh-CN.md` | 完整中文说明 |
| `docs/SSR.zh-CN.md` | ssreflect / SSR 证明风格简要 |
| `README.md` | 顶部增加指向中文说明的链接 |
| `src/Prelude.v` | 文件头 + 组合子旁注（misc 略加强） |
| `src/Haskell.v` | 文件头 + 抽取分段旁注 |
| `src/Extract.v` | 文件头 + Separate Extraction 清单旁注 |
| `src/Ssr.v` | 文件头（链到 SSR.zh-CN） |
| `src/Crush.v` | 文件头 + 主要 Ltac 中英旁注（CPDT crush） |
| `src/Ltac.v` | 文件头 + inv/comp/Case 等旁注 |
| `research/*.v` | 各文件头中英说明（标明实验 / 未入 `_CoqProject`） |
| `src/Data/Functor.v` 等 | 见早期核心切片（Data/Control 由其他 worktree 继续） |

### misc 本批 `research/` 文件

- `research/Basics.v` — 公理 + simple_solver
- `research/Endo.v` — Type→Type Functor 早期稿
- `research/Applicative.v` / `Monad.v` — 定律写进类的前身
- `research/Iso.v` — 类型同构
- `research/Functor.v` — 范畴级 Functor / 伴随等大草稿
- `research/Conduit.v` — Source / conduit 草图
- `research/Coinductive.v` — 双模拟 / CoProxy 实验

## 仍可能未完成（其他目录 / 其他 worktree）

- 其余 `src/Data/**`、`src/Control/**`、`src/Control/Monad/**`（并行中）
- `test/`、`doc/`、未列入 `_CoqProject` 的其它草稿

## 如何继续

1. 各 worktree 只改自己负责的目录，风格同上。
2. 本地 `git commit`；**不要 push / merge**，除非明确要求。
3. 合并时再统一更新本 NOTES 的「已译」表，避免误报全仓完成。
