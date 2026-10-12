# 新規性評価と論文テーマ

評価日：2026-10-12。現在の証明成果と一次資料をもとにした投稿テーマの判断です。
評価語の「強い／中程度／弱い」は、数学的発明、形式化成果、方法論のどれを評価するかに
依存します。採録確率や網羅的な先行研究調査の結果を表すものではありません。

## 1. 推奨

**現在の成果で第一論文をまとめるなら、有限鍵 BB84 の全出力安全性を主軸にする。**
メタ論理を主題にする第二論文では、導出変換そのものよりも、
**生成した帰着コードに対する実行・資源・安全性の証明を、導出操作とともに合成する方法**
を中心に据える。

両者を一つの巨大な「古典・量子暗号の万能基盤」論文にまとめると、評価対象の主定理が
ぼやけます。共通する核は説明できますが、BB84 の量子行列の証明と古典帰着コードの
実行証明が同じ強さで一つの backend に統合された、という主張にはしません。

## 2. 新規性の棚卸し

| 成果・主張 | 評価 | 根拠と論文での役割 |
| --- | --- | --- |
| closure systems、仮定付き導出、接ぎ木、derived-rule maps | 数学的新規性は弱い | Bauer–Haselwarter–Lumsdaine §2.2 と直接対応。背景・設計基盤として引用 |
| 自由モデル、初期性、置換・翻訳の恒等則と結合則 | 単独テーマとして弱い | 自由構文の標準的性質。Lean の成果物として有用だが、新しい数学理論の主定理にはしにくい |
| 暗号の健全性と具体的／漸近的な損失上界 | 単独では弱い | CertiCrypt、FCF、EasyCrypt、SSProve に先行例 |
| 計算量・オラクル呼出しと安全性の同時評価 | 広い主張では弱い | FCF §3.7、EasyCrypt CCS2021 が直接の比較対象 |
| 実行と意味論の一致、実装から安全性への接続 | 広い主張では弱い | FCF §3.8、SSProve の The Last Yard などに先行例 |
| 同一の導出からコード・損失・実行証拠を得て、置換・展開・再構成で対応を保持 | 方法論上の新規性候補は中程度 | 本実装のまとまった設計上の差分。既存基盤でも表現可能と考えられ、「既存ではできない」ではなく一般定理と具体的接続の再利用性を評価 |
| 固定有限コードの適応的な帰着について、セル操作・全停止・ゲーム一致・問い合わせ数を証明 | 具体的形式化として中程度 | 抽象的な保証のレコードだけでなく、具体的実行から証拠を構成している。例の暗号方式や計算モデルの範囲を明示 |
| 有限鍵 BB84：任意の有限クラウス・ブロック攻撃、訂正漏洩、公開種、中止、両者の最終鍵、具体的数値の接続 | 現在の最も有望な形式化成果 | 端点が明確で複数の数学層の接続を必要とする。数学的安全性理論は既知。完成済み同等成果との順位は未確定 |
| 非復元抽出の指数上界と数値例 | 補助成果 | Hoeffding 型評価は既知。独立した新しい集中不等式としては弱く、BB84 端点を閉じる証明として重要 |
| 対称モノイダル圏による量子操作、Bohrification | 現時点で主軸への根拠不足 | 圏論自体と原典定理の再構成だけでは差分が薄い。独自の表現・対応定理を選んだ別の監査が必要 |

## 3. 先行研究との比較

### [R1] FCF：抽出・効率性・意味論をすでに扱う

Petcher–Morrisett, *The Foundational Cryptography Framework*：
[本文](https://arxiv.org/html/1410.3735v1)、特に §3.7、§3.8、§4.6。

- 具体的上界と漸近的安全性、admissibility predicates、oracle computations を扱います。
- §3.7 は最悪時の関数費用、計算費用、オラクル費用を扱います。
  shallow embedding の Gallina 関数の費用は axiomatic と説明されています。
- §3.8 は小ステップ実行意味論と分布意味論の対応を定理10で証明し、Coq extraction を利用。
- §3.7 の脚注は、費用公理による証明から抽出 OCaml コード自体の同じ計算量が従うとは
  主張せず、命題的に等価な有効手続きの存在で十分という位置づけを明示しています。

**本実装の比較点**：具体的な有限コード backend では、実際に出力したコードに対する
停止・セル単位の費用・分布一致の証拠を構成する。この差分は、FCF の全体を上回るという
意味ではなく、保証対象となるコードと計算モデルを限定した比較です。
FCF の現行版全体を再監査したものではありません。

### [R2] CertiCrypt：プログラム変換と PPT の先行形式化

[著者の案内](https://gbarthe.github.io/)、
[公式 README](https://github.com/EasyCrypt/certicrypt/blob/master/README.md) を確認。
README は relational Hoare logic、observational equivalence、verified program
transformations、PPT／lossless 証明の tactics、OAEP・FDH・ElGamal 等を列挙しています。

**評価への影響**：変換の正しさ、帰着の効率性、カーネル検査という特徴だけでは差分を
作れません。今回の確認は README の範囲で、個別の費用定理のソース照合は未実施です。

### [R3] EasyCrypt：敵対者の実行時間と合成的安全性

Barbosa ほか, *Mechanized Proofs of Adversarial Complexity and Application to
Universal Composability*（CCS2021）：[公式要旨](https://eprint.iacr.org/2021/156)。

敵対者の execution time と oracle calls を扱う Hoare logic、その意味論に対する健全性、
計算量クラスに属する敵対者の存在量化、成功確率と実行時間の関係、simulation-based
composition と具体的安全性上界、UC への適用を説明しています。

**評価への影響**：「敵対者の計算量を厳密に扱う初の暗号基盤」は不適切です。
本実装は、導出操作と backend 証明書の対応を主張候補にします。
同論文の PDF は今回403で取得できず、定理番号・全費用規約を本文で照合したとは記載しません。

公式の [EasyCrypt の説明](https://www.easycrypt.info/) と
[PRF 暗号のチュートリアル](https://easycrypt.gitlab.io/easycrypt-web/docs/tutorials/encryption-from-prf/)
も確認。PRF から暗号を構成する安全性証明そのものは、代表例として既存です。

### [R4] SSProve：代数的な合成と低水準のプログラム論理の接続

*SSProve: A Foundational Framework for Modular Cryptographic Proofs in Coq*：
[公式要旨・TOPLAS 版](https://eprint.iacr.org/2021/397)。
今回のコード比較はコミット `c6d7d4bc3a0a671c92899aa49dfcfb065d1bdbbd` に固定。
[README](https://github.com/SSProve/ssprove/blob/c6d7d4bc3a0a671c92899aa49dfcfb065d1bdbbd/README.md)
と
[`pkg_advantage.v`](https://github.com/SSProve/ssprove/blob/c6d7d4bc3a0a671c92899aa49dfcfb065d1bdbbd/theories/Crypt/package/pkg_advantage.v)
を確認しました。

- パッケージのインターフェースと状態の条件付きの逐次・並列合成、結合則、恒等則。
- `Advantage_link` はパッケージ合成による帰着の優位性等式。
- `Advantage_triangle_chain` は有限のゲーム列について損失を合成。
- 関係的プログラム論理と高水準の代数的証明の接続を基盤ごと形式化。
- ElGamal、PRF 暗号、KEM–DEM、Σ-protocols 等の事例。

**評価への影響**：「圏・代数的合成を暗号証明に使う」「高水準証明と低水準をつなぐ」
という主張は大きく重なります。本実装の差分候補は、複数の実行 backend の証明書と
明示的な帰着導出の構文を結びつけた保証です。SSProve 全体にその機能がないという
不在証明はしていません。

### [R5] The Last Yard：実装と安全性の foundational な接続

Haselwarter ほか, *The Last Yard: Foundational End-to-End Verification of
High-Speed Cryptography*（CPP2024）：[公式要旨](https://eprint.iacr.org/2023/185)。

Hacspec→SSProve、Jasmin→SSProve の翻訳、Jasmin の operational semantics に対する
正しさ、ハードウェア加速 AES の仕様適合と実装に基づく暗号方式の安全性を扱います。

**評価への影響**：「初の foundational end-to-end 暗号検証」は主張できません。
現在の本実装の有限コードと制御器の保証は、実用 AES や assembly までの保証と
同一視せず、導出からの帰着構成の方法論として評価します。

### [R6] ハイブリッド論法も一般化の競合がある

Larsen–Schürmann, *Mechanizing Nested Hybrid Arguments*（初稿2025、改訂2026）：
[公式要旨](https://eprint.iacr.org/2025/1122)。query-counting、multi-instance、nested cases
を含む一般定理と Nominal-SSProve の事例を説明しています。

本実装の有限／可変段数ハイブリッドを、一般的なハイブリッド機械検証そのものの新規性で
売り出すのは弱いです。固定コードの実行と資源上界へどこまで接続するかを比較します。

## 4. 本実装で主張を絞るべき点

### 実際に意味のある保証

- `General.CertifiedTransform.code_eq`：実行証拠のコードとコンパイラの出力の一致。
- `General.Extraction`：仮定の各出現について、帰着先とコンパイラを抽出。
  `extract_emitted` は通常の生成コード列との一致を保証。
- `Presented.Resources.runWitnesses_emitted`：生成コードに対応する実行証拠の列。
- `quote_runWitnesses`：再構成前後で証明書全体を保存。
- `Presented.Translation.code_eval`：安全性の意味論とは独立したコードモデル。
- `PRFCounterResource` と `CounterWhole`：固定した元コード、適応的な応答、
  全実行の停止・ゲーム一致・CPU 上界・問い合わせ数の接続。
- `EncryptThenMAC.ConcreteOperational`：異なる二つの帰着機械に対する実際の証拠写像、
  時間式、コードとゲームの接続。ただし具体例は既存の一回限りの1ビット暗号。

### 新規性を過大評価しやすい点

1. `CompositeRule.resourceModel` は展開先のモデルの `pullback` です。
   `tree_preserved` は一般的な解釈保存の適用であり、独立に作った二つの資源解析が偶然
   一致するという発見ではありません。独立なコード解釈の保存と具体的 backend の
   実行定理に合わせて評価する必要があります。
2. `General.Normalization` は恒等節点と合成の括弧を整理します。
   元の proof tree と witness は保持する設計です。コードの高速化や資源改善の定理では
   なく、単独で強い最適化論文にはなりません。
3. `ExecutionInterface` は任意の `ExecutesWithin` と `Realizes` を受け取ります。
   構造体だけから正しい時間尺度、停止、非空な敵対者クラスは得られません。
4. `CodeSystem` の `Encodable` は可算な符号化の保証です。
   任意の `runPrimitive` の効率性や計算可能性の証明とは区別します。
   論文では実際に計算できる具体的 backend を示します。
5. BB84 の対象論理に接続したことは、量子攻撃者の実行コードを生成し、
   その量子計算量まで古典 backend と同じ方法で保証したことにはなりません。

## 5. テーマ案と優先順位

### 第一候補：有限鍵 BB84 の全出力安全性

**日本語題案**：認証済み古典通信下の有限鍵 BB84：全出力安全性の Lean 形式化

**英語題案**：*Kernel-Checked Finite-Key BB84 Security with Explicit Sampling and Leakage Budgets*

**研究質問**：実際の公開記録、両者の鍵、中止を保持した有限次元の BB84 を、
量子標本評価から具体的な正の鍵長・小さい総誤差まで、形式的に接続できるか。

中心成果は `UsefulBB84.secure`。
25,165,824信号から65,536出力ビット、操作的総誤差 `2^-60` 以下を検証した例です。
主張は攻撃モデル・出力・安全性距離・パラメータを特定した形式化に置きます。
メタ論理は証明の組織化と再利用を説明する基盤です。

**投稿前に優先する補強**：

1. **対応を証明済み**：`TraceDistanceNorm` と `BB84Completion` が `1/2 Tr sqrt(ΔᴴΔ)` の数値付き安全性まで接続。
2. **物理的成功確率を証明済み**：`HonestBB84` が無攻撃量子実験と古典記録を同定し、`UsefulBB84.honest_success` が全最終状態の受理確率 `≥1/2` を結論。
3. **比較を更新済み**：[固定版コード比較](quantum/code-comparison.md)で Lean-QIT の7ファイルを確認。FVQKD は追加調査でも論文・主定理を特定できず、内容比較不能という結論。
4. **再現手順を整備**：[成果物](quantum/artifact.md)で主定理の公理依存、全依存リビジョン、ソースの内容 ID、全体ビルドと監査の再実行を固定。

認証の実装・鍵消費・雑音下の鍵率は価値のある次段階ですが、認証済み通信を明記した
この第一論文の結論と混同しません。現時点で「世界初」「実用最高性能」は主張しません。

**適した論文の性格**：ITP／CPP 系の形式化・検証論文が自然な候補。
暗号理論系の投稿には、新しい安全性定理や解析改善という別の根拠が必要です。

### 第二候補：導出変換に安定な実行証明付き暗号帰着

**日本語題案**：導出変換に安定な、実行・資源証明付き暗号帰着の構成

**英語題案**：*Operationally Certified Cryptographic Reductions from Derivations in Lean*

**研究質問**：規則展開・仮定置換・複数仮定への分岐を行っても、生成コード、
ゲームの意味、実行資源、損失の対応を同じ導出から保てるか。

中心は closure-system の新発明ではなく、**証明付き帰着コンパイルの一般定理と
具体的な有限実行への接続**です。証明書の変換と生成コードを結ぶ commuting diagram
を主定理の形にし、単にレコードへ証拠を詰めたことより強い再利用性を示します。

**本文の構成案**：

1. 問題：意味論上の帰着から、実行可能な帰着とその資源保証へ移る際の証明義務。
2. 純粋な導出・コンパイラ計画と、意味論・実行証拠の分離。
3. 抽出・仮定置換・導出済み規則の展開についての対応保存定理。
4. PRG パッド、適応的 PRF カウンタ暗号、Encrypt-then-MAC の事例。
5. FCF の費用／抽出、EasyCrypt の敵対者計算量、SSProve の代数的合成との比較。

**投稿前に優先する補強**：

- 一般定理から具体的な停止・費用・意味の保証までをまとめた端点を作り、利用者が何を
  証明すると何が自動的に得られるかを一つの定理文で示す。
- 同じ事例を既存方式と比較し、新規 backend 登録で再利用した定理、残る局所義務、
  手作業の証明量を測る。構文節点の削減を実行速度の改善として測らない。
- 複数 backend の型・費用単位・敵対者クラスを明記し、具体的な非空な適応的事例を示す。
- より説得力のある組合せ事例として、任意長・適応的な認証付き暗号への接続を検討。
  現在の1ビット事例だけでは研究の有用性を小さく評価されやすい。

**評価**：方法論として中程度の新規性候補。上記の再利用効果を示して初めて、
「既知構造の Lean 移植」以上の主張が明確になります。ITP／CPP／CSF 系が検討対象。

### 将来候補：認証と鍵消費を含む BB84 鍵拡張

**題案**：*Kernel-Checked Finite-Key BB84 with Authentication and Net Key Expansion*

公開通信の認証失敗、認証鍵の消費、正直実行の成功、最終鍵の安全性を同じ会計へ接続する
テーマです。現在の BB84 から一段進んだ明確な端点になります。
数学自体は既存の composable QKD との比較が必要ですが、統合された形式化成果として
有望です。現在の線形ハッシュ衝突補題だけでは、適応的偽造安全性や net expansion を
満たさないため、完成済みの第一論文としては扱いません。

## 6. 判断のまとめ

- **現在の第一論文**：有限鍵 BB84。成果の端点が最も明確。
- **基盤を主題とする第二論文**：実行証明付き帰着の合成。単独のメタ論理論文より有望。
- **次の強い拡張目標**：認証鍵消費込みの QKD 鍵拡張。

今回の調査は先行研究の本文・公式要旨・選択したコードの比較です。
外部プロジェクト全体のビルドや同じ事例の移植比較は行っていません。
特に BB84 の同等成果の所在と、敵対者計算量論文の本文照合は残るため、
この文書は優先順位を決める評価であり、絶対的な新規性の確定証明ではありません。
