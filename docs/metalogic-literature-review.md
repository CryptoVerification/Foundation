# メタ論理の数学的出典と形式化の対応

調査日：2026-10-12。現在の `Foundation/Logic/Presentation.lean` と
`Foundation/Logic/Translation.lean` を、論文本文と著者らの公開 Coq コードへ照合した記録です。

## 結論

**現在の核に直接対応する数学的記述は、Andrej Bauer、Philipp G. Haselwarter、
Peter LeFanu Lumsdaine の *A general definition of dependent type theories*
（2020）、§2.2 “Closure systems” にあります。**

判断の集合、前提の族と結論からなる規則、仮定付きの証明木、証明木の接ぎ木、
各規則を標的の導出へ送る写像が、定義単位で対応します。
著者らの Coq 形式化 `Auxiliary/Closure.v` にも対応する定義があります。
したがって「単に一般的な構文処理」と説明するだけでは数学的な位置づけとして不十分です。
closure systems とその derived-rule maps の有限前提・有限仮定版として説明できます。

一方、リポジトリの導入時文書・コミットには、この論文を名指しする引用を発見していません。
ここで確認したのは**数学的対応**です。開発時に実際に参照した資料という歴史的な出典や、
Lean と Coq の定義間の機械検証済み同型までは確認していません。

## 1. 一次資料と調査範囲

- 論文：[arXiv:2009.05539v1](https://arxiv.org/abs/2009.05539v1)、
  [本文 HTML](https://arxiv.org/html/2009.05539v1)。特に §2.1–2.2 と Appendix A を参照。
- 著者らの Coq 形式化：
  [`general-type-theories`](https://github.com/peterlefanulumsdaine/general-type-theories)。
  論文の参考文献が指定する `arXiv` ブランチを、今回取得時のコミット
  `da7b16b99a0b329a66e7dbcb77292b8ae7c84b06` に固定。
- 照合したコード：
  [`Auxiliary/Closure.v`](https://github.com/peterlefanulumsdaine/general-type-theories/blob/da7b16b99a0b329a66e7dbcb77292b8ae7c84b06/Auxiliary/Closure.v)
  と同版の `README.md`。外部 Coq プロジェクトのビルド・公理監査は実施していません。
- ローカル履歴：核を導入した `ff1a6d5`（2026-10-07、
  `Add presented crypto logic and EncryptThenMAC reductions`）の核、
  `docs/crypto-logic.md`、現在は存在しない当時の `docs/logic-reconstruction.md` を確認。
  当時の記録も自由な有限前提の論理と任意の依存型理論を区別しています。

## 2. 定義・構成の対応表

ローカルの核：
[`Presentation.lean`](../Foundation/Logic/Presentation.lean)、
[`Translation.lean`](../Foundation/Logic/Translation.lean)。

| 原論文 | 著者らの Coq `Closure.v` | 本プロジェクトの Lean | 対応と差分 |
| --- | --- | --- | --- |
| 定義2.1：集合上の indexed family | `family`（`Auxiliary.Family` を使用） | `Context.length`, `Context.claim` | Lean の仮定族は `Fin length` に制限。同じ判断の複数出現を保持 |
| 定義2.6：closure rule と closure system | `rule`, `premises`, `conclusion`, `system` | `Presentation.Judgment/Rule/arity/premise/conclusion` | `Rule` が規則族の添字。規則ごとの前提は有限。規則の総数を有限とは要求しない |
| 定義2.8：仮定族からの導出 | `derivation`, `hypothesis`, `deduce` | `Derivation`, `hypothesis`, `apply` | 二つの構成子と前提ごとの子導出が直接対応。導出は命題だけでなく証明木を保持する `Type` |
| 補題2.11：grafting | `graft` | `Derivation.substitute` | 各仮定を別の導出へ置換し、規則節点では再帰する同じ構成 |
| 仮定族の写像による導出の輸送 | `derivation_fmap2` | `Derivation.rename` | 判断を保持する添字写像を使い、仮定の並べ替え・再使用を扱う |
| 定義2.10：derived rule と closure system map | `map_over`, `map` | `Translation.judgment/rule` | 判断の写像と、翻訳された前提から翻訳された結論への導出。規則を一つの規則へ送るだけの simple map より一般的 |
| 定義2.12：closure system map の導出への作用 | `derivation_fmap1_over`、より一般に `derivation_fmap_over` | `Translation.translate` | 子導出を翻訳し、指定された規則の導出へ接ぎ木 |
| §2.2末尾：恒等・合成・関手性の説明 | `idmap`, `compose_over`, `compose` | `identity`, `comp`, `translate_identity/translate_comp`, `comp_identity/identity_comp/comp_assoc` | 論文が圏としての詳細を省略した部分について、Lean ではこれらの等式を明示的に証明 |

論文の §2.2 は、接ぎ木を導出の monad 的構造の乗法、derived-rule maps を
Kleisli 的な写像として説明しています。Lean の `substitute_id` と `substitute_assoc`、
`translate_substitute` はその構造と整合する具体的等式です。
現在のコードには、この説明全体を mathlib の monad／圏インスタンスへ登録する宣言はありません。

## 3. モデル・初期性の数学的位置づけ

`Model.Carrier` は判断ごとの値の族、`Model.operation` は各規則の前提値から結論値を
作る演算です。`Derivation.eval` は導出の構造再帰による解釈、`Model.Hom` は規則演算を
保存する写像です。これは判断を sort とする多ソートの自由項代数として理解できます。

- `termModel T Γ` は、仮定族 Γ を生成元とする自由モデル。
- `interpretation_unique` は、生成元の値を指定したときの準同型の一意性。
- `initial` は、仮定族が空の場合の初期性。
- `eval_substitute` は、接ぎ木と解釈の交換則。
- `Translation.pullback/eval_translate` は、derived-rule map に沿うモデルの引き戻しと
  解釈の交換則。
- `eval_preserving` は、明示したモデル準同型を通じた保存。無関係な二つのモデルの
  解釈が自動的に等しいとは要求しません。

これらのモデル・自由性の宣言は、照合した §2.2 の番号付き定義・補題にそのまま
書かれた定理ではありません。§2.2 の導出木を代数として解釈した本実装の明示的な展開です。
自由項代数の普遍性そのものを新しい数学的定理として主張する根拠にはなりません。

## 4. 論文全体の形式化との区別

原論文は §3以降で、束縛を伴う raw syntax、依存型の判断と境界、規則の
acceptable／well-presented 条件、presuppositions、置換除去、型の一意性などを扱います。
現在の Lean の核は、その依存型理論全体を形式化したものではありません。

特に `Derivation.substitute` は**仮定となる証明の接ぎ木**です。
原論文 §3.4 の、束縛変数を含む raw term/type expressions の代入と同一視しません。
判断の内部構文や依存関係は対象論理側で指定する方式です。
核のコメントにある “not an implementation of arbitrary dependent GATs” とも整合します。

関連候補として Taichi Uemura の
[*A General Framework for the Semantics of Type Theory*](https://arxiv.org/abs/1904.04097v3)
（初稿2019、改訂2023）の公式要旨も確認しました。同論文の bi-initial model、
internal language、モデルの2圏との対応は現在の核の `initial` より大きい主張です。
今回の定義単位の直接対応は Bauer–Haselwarter–Lumsdaine §2.2 にあります。
Uemura 論文本文との定理単位の照合は実施していません。

## 5. 暗号・BB84への適用の貢献

数学的基盤、機械形式化、応用上の追加保証を次のように分けて評価できます。

| 層 | 評価する内容 |
| --- | --- |
| 元の数学 | closure systems、導出、接ぎ木、derived-rule maps は明示的な先行研究がある |
| Lean の形式化 | 有限前提・有限仮定版を実装し、置換・翻訳の法則、モデルの自由性、解釈保存を Lean で証明 |
| 古典暗号への具体化 | 同じ導出をコード・安全性・損失・実行証拠へ解釈し、規則展開や再構成でも生成コードと証明書を対応づける |
| BB84への具体化 | 標本上界、量子近似、後処理、正しさと秘密性の合成、中止枝の結合を対象論理として登録し、証明済みの数学で規則・前提を満たす |

古典暗号の具体的な比較対象は
`Crypto/Logic/Presented/{Interpretation,Translation,CompositeRule,Resources,Reconstruction}.lean`
と `Crypto/Meta/{Extraction,NormalForm}.lean` です。
BB84 では `QuantumSamplingLogic` と `AcceptedAbortLogic` の導出が実際の安全性経路で使用されます。

投稿で検討する主張は、例えば次です。

> We mechanize a finitary closure-system calculus and derived-rule translations
> in Lean, and instantiate its proof-relevant semantics with cryptographic
> reductions and finite-dimensional quantum-security bounds. The cryptographic
> instantiations connect generated reduction code to execution certificates,
> resource bounds, and quantitative security losses.

数学的核が既知であることは、暗号への具体化の価値を否定しません。
一方、核の Lean 実装や暗号応用について「初」と主張するには、既存の形式化、
CertiCrypt／EasyCrypt／FCF／SSProve などとの定理単位の比較が必要です。
その比較の後続調査とテーマ判断は [新規性評価と論文テーマ](research-themes.md) に記録しました。
FCF の本文、SSProve の選択した宣言、EasyCrypt の敵対者計算量の公式要旨などを比較しています。
外部基盤全体の定理監査や同一事例の移植比較は未完了です。
