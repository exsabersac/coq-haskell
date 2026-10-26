# zh-CN 注解进度说明

## 风格

与 category-theory 的 zh-CN 分支一致：

- 块注释：`(*` 英文原意（可略压缩）→ 一行 `--------` → 中文对照 `*)`
- 短行：`(* EN / 中文 *)`
- **不改** Coq 标识符与代码逻辑，只加/改注释与文档

## 已译（本轮核心切片）

| 路径 | 内容 |
|---|---|
| `README.zh-CN.md` | 完整中文说明 |
| `README.md` | 顶部增加指向中文说明的链接 |
| `src/Prelude.v` | 文件头 + 常用组合子旁注 |
| `src/Data/Functor.v` | 文件头、`Functor` / `FunctorLaws` |
| `src/Control/Applicative.v` | 文件头、`Applicative` / Laws / `Alternative` |
| `src/Control/Monad.v` | 文件头、`Monad` / `bind` / Laws（join 视角） |
| `src/Data/Functor/Yoneda.v` | 文件头 + Yoneda/Coyoneda 简短说明 |
| `src/Haskell.v` | 文件头（抽取映射入口） |
| `src/Extract.v` | 文件头（Separate Extraction 清单） |
| `src/Data/Maybe.v` | 文件头 + 实例样板（Notation / F/A/M） |

## 未译（可按需继续）

- 其余 `Data/*` 实例（`Either`、`List`、`Monoid`…）
- `Control/Comonad.v`、`Compose.v`、`Lens.v`、`Category.v`
- `Control/Monad/**`（Free、Freer、State、Cont、Trans…）
- `Data/Functor/{Const,Kan,Identity,Contravariant,…}`
- `research/`、`test/`、`doc/`
- 未列入 `_CoqProject` 的草稿文件

## 如何继续

1. 在本分支 `zh-CN` 上编辑，只加注释。
2. 优先按「下一层实例 / Monad 变换器 / Free vs Freer」选文件。
3. 本地 `git commit` 即可；**不要 push**，除非明确要求。
