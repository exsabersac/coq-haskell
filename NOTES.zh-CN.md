# zh-CN 注解进度说明

## 风格

证明语言说明见 [docs/SSR.zh-CN.md](./docs/SSR.zh-CN.md)（ssreflect 简要）。

与 category-theory 的 zh-CN 分支一致：

- 块注释：`(*` 英文原意（可略压缩）→ 一行 `--------` → 中文对照 `*)`
- 短行：`(* EN / 中文 *)`
- **不改** Coq 标识符与代码逻辑，只加/改注释与文档

## 状态（四路已合并）

`Data` / `Control` / `Monad` / `misc` 四路 worktree 已合并进本分支 `zh-CN` 并推送。

| 批次 | 范围 |
|---|---|
| 核心切片 | `README*.md`、`docs/SSR.zh-CN.md`、`Prelude`/`Functor`/`Applicative`/`Monad`/`Yoneda`/`Maybe`/`Haskell`/`Extract`/`Ssr` |
| Data | `src/Data/**`（含 Functor 变体；已有核心文件保留原注解） |
| Control | `Category`/`Comonad`/`Compose`/`Impl`/`Iso`/`Lens` |
| Monad | `src/Control/Monad/**`（含 Trans） |
| misc | `Crush`/`Ltac`、根文件加强、`research/*.v` 文件头 |

## 仍可加深（可选）

- 部分文件目前以**文件头 + 关键定义旁注**为主，长证明体未逐行译
- `test/`、`doc/`、Haskell 侧 `haskell/` 源码未译
- 未入 `_CoqProject` 的草稿：已在对应文件头标明实验性质

## 如何继续

1. 在 `zh-CN` 上只加注释，勿改标识符。
2. 加深某文件时保持同一中英对照风格。
3. 提交后 `git push origin zh-CN`；本机 `git pull`。
