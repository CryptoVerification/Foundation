# BB84・量子暗号の形式検証と圏論：先行研究レビュー

調査日：2026-10-12。論文投稿の位置づけを決めるための重点調査です。網羅的な systematic review や、他プロジェクトの証明成果物の独立監査ではありません。

## 結論

本プロジェクトの有望な貢献は、**既知の有限鍵 BB84 安全性の数学を、明示的な有限次元のプロトコル出力へ接続し、具体的な正の鍵長と小さい総誤差を Lean の核で検証したこと**です。

- BB84 の形式検証は少なくとも2002年に遡ります。「初の BB84 形式検証」は主張できません。
- 量子プログラム・量子暗号の定理証明基盤には Coq、Isabelle、Lean の先行研究があります。「初の量子安全性の機械検証」「初の Lean 量子情報基盤」も適切ではありません。
- 有限鍵・一般攻撃への BB84 安全性は既知の数学です。今回の指数上界や数値例を、新しい暗号学的安全性理論や最高性能として売り出す根拠はありません。
- 確認した Lean-QIT の BB84 コードと鍵蒸留コードは、今回の数値付き BB84 全出力定理とは異なる段階です。ただし同ライブラリには抽出器・量子側情報・公開種の距離評価があり、基盤や個別補題の重なりは大きいです。
- **FVQKD** という「Machine-checked composable finite-key security of BB84 in Rocq」を掲げる検索索引上の候補が見つかりました。公開コード・論文は確認できていません。この候補を解決せずに「初の機械検証済み有限鍵 BB84」と断定しません。

投稿時の中心的な主張は、順位ではなく、対象プロトコル・攻撃モデル・安全性定義・証明連鎖・再利用可能な境界を具体的に示すものにします。

古典暗号基盤との後続比較を踏まえた [新規性評価と論文テーマ](../research-themes.md) では、
現在の第一論文に有限鍵 BB84、第二論文に実行証明付き帰着の合成を推奨しています。

## 1. 調査方法と証拠の読み方

検索した主な組合せ：`BB84 formal verification`、`BB84 Lean proof`、`BB84 Isabelle verification`、`BB84 Coq`、`quantum key distribution mechanized security proof`、`quantum relational Hoare logic`、`categorical composable cryptography`。

DuckDuckGo、arXiv の検索・論文ページ、Crossref、公式会議ページ、著者ページ、公開 GitHub コードを使い、主要候補を一次資料へ辿りました。検索の要約だけで安全性定理の内容を確定しません。Google は本文取得できず、DuckDuckGo の一部検索は CAPTCHA で止まりました。検索結果が出なかったことは、研究が存在しない証拠ではありません。

以下を区別します。

| 証拠の種類 | この調査で言えること |
| --- | --- |
| 本文・発表資料を確認 | その資料に記載されたモデル、結論、将来課題を比較できる |
| 公開コードの宣言を確認 | 確認した版での型・前提・結論を比較できる。全体ビルドや全依存の監査をしたことにはならない |
| 公式要旨・書誌情報を確認 | 著者が説明した範囲と書誌を確認できる。証明の健全性を独立確認したことにはならない |
| 検索索引のみ | 未解決候補。確立した結果として引用・比較しない |

比較の軸は、(a) 定理証明／モデル検査／記号抽象の違い、(b) 固定した攻撃か任意の量子攻撃か、(c) 最終鍵・公開情報・中止を保持するか、(d) 有限長の総誤差か検出確率だけか、(e) 数値パラメータを機械検証するか、です。

## 2. BB84/QKD の直接の形式検証研究

### [F1] Nagarajan–Gay, *Formal Verification of Quantum Protocols* (2002)

- 一次資料：[arXiv:quant-ph/0203086](https://arxiv.org/abs/quant-ph/0203086)。要旨を確認。
- BB84 を CCS でモデル化し、CWB-NC で初期解析した拡張要旨です。
- **比較**：BB84 の形式検証という課題設定自体には長い先行研究があります。今回の、任意の有限クラウス攻撃と有限鍵の実状態・理想鍵比較とは保証対象を区別します。

### [F2] Elboukhari–Azizi–Azizi, *Analysis of the Security of BB84 by Model Checking* (2010)

- 一次資料：[arXiv:1005.4504](https://arxiv.org/abs/1005.4504)、[DOI:10.5121/ijnsa.2010.2207](https://doi.org/10.5121/ijnsa.2010.2207)。要旨・書誌を確認。
- PRISM による確率的モデル検査で、盗聴検出とチャネル・盗聴者のパラメータの関係を解析します。
- **比較**：確率的な BB84 解析は既存です。検出確率の解析を、量子側情報を含む最終鍵の有限長秘密性と同一視しません。

### [F3] Feng–Ying, *Toward automatic verification of quantum cryptographic protocols* (CONCUR 2015)

- 一次資料：[arXiv:1507.05278](https://arxiv.org/abs/1507.05278)。要旨を確認。
- 分布ベースの双模倣と近似双模倣を導入し、BB84 と理想プロトコルの指数的に小さくなる差を、**intercept-resend 攻撃**について示します。
- **比較**：「理想プロトコルへの近似」「指数誤差」は先行研究にあります。今回との重要な比較点は、攻撃の量化範囲と具体的な全出力の機械検証です。今回の調査では、この論文の全証明を証明支援系で再実行していません。

### [F4] Hirschi, *Symbolic Abstractions for Quantum Protocol Verification* (2019)

- 一次資料：[arXiv:1904.04186v2 本文](https://arxiv.org/html/1904.04186v2)。特に§1.2、§1.3の抽象化と保証の説明を確認。
- 量子的 Dolev–Yao 攻撃者を Tamarin などに符号化し、BB84 の秘密性と古典メッセージの認証条件を解析します。固定 intercept-resend だけでなく、EPR などの複数の能力を扱います。
- 著者は、確率を可能性・固定ビット列へ抽象化し、一般の確率的攻撃すべてを捉えるものではないことを明記しています。
- **比較**：本プロジェクトの数値付き有限次元安全性と相補的です。認証条件の論理的解析はこの研究の重要な強みで、認証を前提にしている本プロジェクトがすでに解決したとは言えません。

### [F5] Do–Ogata, Maude (SEKE 2025) / CafeOBJ (SEKE 2026 発表資料)

- 2025年書誌：[DOI:10.18293/SEKE2025-020](https://doi.org/10.18293/SEKE2025-020)、[公開コードと README](https://github.com/canhminhdo/bb84)を確認。
- 2026年一次資料：[Formal Specification and Analysis of the BB84 Protocol in CafeOBJ](https://ksiresearch.org/seke/seke26present/paper008.pdf)。取得したものは**30ページの発表スライド**であり、論文本体とは区別します。
- スライド13：OTS、1ビットずつのラウンド、雑音なし、tentative key までという範囲を明記。
- スライド26–29：同じ基底だが鍵が異なるなら盗聴者が存在するという不変条件を、任意のラウンド数について proof scores と構造帰納法で証明。確率的・定量的性質は将来課題と記載。
- **比較**：任意ラウンド数の定理証明という価値があります。有限状態のモデル検査だけとして扱いません。一方、任意の密度行列・量子側情報と最終秘密増幅鍵の数値誤差は、確認した発表の結論ではありません。

### [F6] Kammüller–Nagarajan–Parker–White, Isabelle Decoy QKD (SMC 2025)

- 題名：*Formalisation and Analysis of Decoy QKD in the Isabelle Infrastructure and Insider framework using Refinement and Attack Trees*。
- [DOI:10.1109/SMC58881.2025.11342840](https://doi.org/10.1109/SMC58881.2025.11342840)。Crossref で著者・2025-10-05・会議名を確認。
- **本文未確認**。IEEE のページ本文は取得できませんでした。タイトルだけから、任意量子攻撃への有限鍵距離定理の有無は判定しません。詳細比較のための追加取得候補です。

### [U1] FVQKD：最優先の未解決候補

- 検索索引：[GitHub fvqkd](https://github.com/fvqkd)、[repositories](https://github.com/fvqkd?tab=repositories)。索引には `FVQKD` と “Machine-checked composable finite-key security of BB84 in Rocq” の説明が表示されました。
- 調査時の [https://github.com/fvqkd/FVQKD](https://github.com/fvqkd/FVQKD) は HTTP 404。取得できたプロフィールと GitHub API の公開リポジトリ一覧には `fvqkd/CoqQ` のみがありました。
- 論文、著者、完成度、主定理、前提、公理監査を確認できません。非公開・削除・移転などの事情も判定できません。
- **扱い**：存在しないとも、完成した先行成果があるとも断定しません。検索索引を査読済み文献扱いせず、投稿前に所在を確認すべき候補として記録します。絶対的な「初」の主張にはこの不確実性が残ります。

2026-10-12の追加調査では、公開 CoqQ fork の枝と main の固定ツリー、GitHub の複数の
repository search、OpenAlex、ePrint を確認しましたが、対象論文・主定理を特定できませんでした。
検索結果と取得した版は [固定版コード比較](code-comparison.md) に記録しています。

## 3. 定理証明基盤と、最も近い Lean コード

### [P1] Boender–Kammüller–Nagarajan, *Formalization of Quantum Protocols using Coq* (QPL 2015 / EPTCS 195)

- 一次資料：[本文](https://arxiv.org/html/1511.01568v1)、[DOI:10.4204/EPTCS.195.6](https://doi.org/10.4204/EPTCS.195.6)。本文§5–6を確認。
- 多量子ビット・ゲート・測定・もつれを Coq で扱い、テレポーテーションを証明します。
- 結論では、QKD の安全性を Coq で形式化することを将来の挑戦として記載しています。導入で BB84 に言及することと、BB84 の安全性主定理があることは区別します。

### [P2] Unruh, *Quantum Relational Hoare Logic* (POPL 2019)

- 一次資料：[著者ページ](https://ut.ee/~unruh/publications/qrhl.html)、[arXiv:1802.03188](https://arxiv.org/abs/1802.03188)、[DOI:10.1145/3290346](https://doi.org/10.1145/3290346)。著者要旨を確認。
- [qrhl-tool 公式ページ](https://dominique-unruh.github.io/qrhl-tool/)も確認。Isabelle と複素有界作用素の基盤を利用し、量子・ポスト量子暗号の関係的証明を支援します。公式ページには Fujisaki–Okamoto のポスト量子検証などの適用例があります。
- **比較**：量子暗号の機械検証とプログラムの関係的意味論は既存の成熟した研究軸です。公開ページの適用例だけから、有限鍵 BB84 の全出力定理まで実装済みとは推定しません。ツールの全依存や全 qRHL 規則を今回独立監査したわけでもありません。

### [P3] Zhou–Barthe–Strub–Liu–Ying, *CoqQ: Foundational Verification of Quantum Programs* (POPL 2023)

- 一次資料：[公式会議ページ](https://popl23.sigplan.org/details/POPL-2023-popl-research-papers/29/CoqQ-Foundational-Verification-of-Quantum-Programs)、[DOI:10.1145/3571222](https://doi.org/10.1145/3571222)、[コード](https://github.com/coq-quantum/CoqQ)。公式要旨を確認。
- 深く埋め込んだ量子言語、プログラム論理、MathComp/MathComp Analysis に基づく表示的意味論への健全性証明、局所・並行推論を提供します。
- **比較**：「構文・論理・意味論を機械検証でつなぐ」設計自体は新規ではありません。本プロジェクトでは、どの BB84 固有の証明境界や誤差合成を閉じたかを示す必要があります。

### [P4] Zhu ほか, *Lean-QIT: Towards a Formal Infrastructure for Quantum Information Theory* (2026)

- 一次資料：[arXiv:2607.09632](https://arxiv.org/abs/2607.09632)、[本文](https://arxiv.org/html/2607.09632v1)、[公開コード](https://github.com/QuAIR/Lean-QIT)。論文は2026-07-10のプレプリントとして確認。
- 論文の主要実証は Schumacher、HSW、entanglement-assisted capacity などの量子 Shannon 理論です。QKD、安全性、抽出器などの周辺基盤もあります。
- コード調査をコミット **`15a0a5ef13e5824327e0850ea896e472366287af`**（GitHub API が返したコミット日時2026-10-05）に固定しました。ライブラリの全ビルドや全体の公理監査は実施していません。

確認した宣言：

| ファイル | 確認できた内容 | 本プロジェクトとの違い・重なり |
| --- | --- | --- |
| [`QIT/Security/BB84.lean`](https://github.com/QuAIR/Lean-QIT/blob/15a0a5ef13e5824327e0850ea896e472366287af/QIT/Security/BB84.lean) | BB84 状態・射影測定・matched-basis 正しさ・選別・明示的 abort。末尾に entanglement-based security proof を将来課題として記載 | BB84 の Lean コード自体は先行します。確認したファイルにはブロック攻撃から数値付き最終鍵安全性への定理はありません |
| [`QIT/Security/Key.lean`](https://github.com/QuAIR/Lean-QIT/blob/15a0a5ef13e5824327e0850ea896e472366287af/QIT/Security/Key.lean) | 成功枝の劣正規化状態、Renner 型の一様鍵・量子側情報・trace-distance 秘密性。`ComposableKey.main` は定義との同値 | 安全性定義の重なりは大きいですが、定義を展開する同値はプロトコルの安全性証明ではありません |
| [`QIT/Security/KeyDistillation.lean`](https://github.com/QuAIR/Lean-QIT/blob/15a0a5ef13e5824327e0850ea896e472366287af/QIT/Security/KeyDistillation.lean) | 正しさ・秘密性の定義と分解。`KeyDistillation.main` は両方を前提に scaffold を構成。本文コメントも definition-level scaffold と明記 | 本プロジェクトのように実際の攻撃・検査・訂正からそれらの上界を導く定理とは、前提と結論の段階が異なります |
| [`QIT/Security/ExtractorTraceBridge.lean`](https://github.com/QuAIR/Lean-QIT/blob/15a0a5ef13e5824327e0850ea896e472366287af/QIT/Security/ExtractorTraceBridge.lean) | 公開ハッシュ種を保持した抽出器の距離、種平均、CPTP contraction、近似からの `2δ+ε` 秘密性移送 | 本プロジェクトの秘密増幅・公開種・近似合成と実質的に重なります。これら個別のアイデアを初として主張しません |

後続調査では同じコミットの `States/TraceNorm/{Distance,Spectral,Variational}.lean` も
取得し、標準の `1/2` 規約、平方根・特異値との対応、変分的達成を比較しました。
[7ファイルの固定版コード比較](code-comparison.md)を参照してください。
別の枝・将来版・他の全モジュールについて不在を証明したものではありません。

## 4. 数学的な安全性理論との関係

以下は本プロジェクトの数学的な出典・比較基準です。これらの論文が証明支援系の成果物を提供していることは、今回の確認資料からは確認していません。

| 文献 | 役割と本プロジェクトでの扱い |
| --- | --- |
| [M1] Shor–Preskill, *Simple Proof of Security of the BB84 Quantum Key Distribution Protocol*, PRL 85, 441–444 (2000), [arXiv](https://arxiv.org/abs/quant-ph/0003004), [DOI](https://doi.org/10.1103/PhysRevLett.85.441) | BB84 安全性の古典的な基準。もつれ精製・CSS コードから BB84 への帰着。BB84 安全性自体を今回新しく発見したとは扱わない |
| [M2] Renner, *Security of Quantum Key Distribution* (2005 thesis), [arXiv](https://arxiv.org/abs/quant-ph/0512258) | 量子側情報・一様鍵・安全性定義を比較する基準。劣正規化成功枝と中止の規約を明確にする |
| [M3] Bouman–Fehr, *Sampling in a Quantum Population, and Applications*, CRYPTO 2010, [arXiv v5](https://arxiv.org/abs/0907.4246v5) | 本プロジェクトの量子標本抽出と BB84 証明の主要出典。v5 は中止の扱い・composability の表現を修正しているため版を固定する |
| [M4] Tomamichel–Lim–Gisin–Renner, *Tight Finite-Key Analysis for Quantum Cryptography*, Nature Communications 3, 634 (2012), [arXiv](https://arxiv.org/abs/1103.4130), [DOI](https://doi.org/10.1038/ncomms1631) | 一般攻撃に対する有限鍵保証は既知。今回の鍵長・信号数を最高性能や新しい有限鍵理論として主張しない |
| [M5] Hoeffding, *Probability Inequalities for Sums of Bounded Random Variables*, JASA 58(301), 13–30 (1963), [DOI](https://doi.org/10.1080/01621459.1963.10500830) | 母関数・集中不等式の基礎。今回の Lean 補題は既知の数学の形式化 |
| [M6] Serfling, *Probability Inequalities for the Sum in Sampling without Replacement*, Annals of Statistics 2(1) (1974), [DOI](https://doi.org/10.1214/aos/1176342611) | 有限母集団の集中評価という研究史。今回は有限母集団補正を持つ最強の Serfling 評価まで形式化したという主張ではない |

書誌・要旨を確認しました。[M5]・[M6]は Crossref の書誌確認であり、原論文の証明を全て照合したわけではありません。

### 最近の「プロトコル記述と証明の一致」に関する重要文献

- [M7] Mizutani–Sasaki–Kato, *Protocol-level description and self-contained security proof of decoy-state BB84 QKD protocol*, [arXiv:2504.20417v3](https://arxiv.org/abs/2504.20417v3) (2025)。要旨は、フローチャート、自己完結的な情報理論的証明、UC 枠組み、correctness/secrecy のパラメータを説明。**数学的に厳密であることや formal certification に言及することを、Lean/Rocq の核による機械検証と同一視しません**。
- [M8] Tupkary–Tan–Nahar–Kamin–Lütkenhaus, *Security proofs for practical QKD: variations, techniques, gaps, and limitations*, [arXiv:2502.10340v3](https://arxiv.org/abs/2502.10340v3), Reviews of Modern Physics 98, 035003 (2026), [DOI](https://doi.org/10.1103/28rs-frmw)。書誌・要旨を確認。詳しいプロトコル記述と証明手法の不一致、異なる仮定を持つ既存結果の援用を主要な問題として挙げています。
- [M9] Tupkary–Nahar–Arqand–Tan–Lütkenhaus, *A rigorous and complete security proof of decoy-state BB84 quantum key distribution*, [arXiv:2601.18035v1](https://arxiv.org/abs/2601.18035v1) (2026)。要旨は認証・古典処理・source replacement・finite size・squashing・decoy を統合したモジュール的理論を説明。今回の理想的 qubit モデルより装置モデルは広いです。要旨確認の範囲で、証明支援系による核検証済み成果物があるとは判定しません。

これらに対する本プロジェクトの強みの候補は、**仮定から具体的な出力状態・誤差上界までの依存を核で検証し公開すること**です。「他のすべての証明が不完全だった」という著者の表現を無批判に採用したり、こちらが実装・装置のすべてを検証したと主張したりしません。

## 5. 圏論を使うことの先行研究上の位置づけ

### [C1] Abramsky–Coecke, *A categorical semantics of quantum protocols* (LICS 2004)

- 一次資料：[arXiv:quant-ph/0402130](https://arxiv.org/abs/quant-ph/0402130)。要旨・書誌を確認。
- compact closed categories、biproducts、量子テレポーテーションなどの情報流・分岐・Born rule を抽象化します。
- **比較**：量子操作を圏・テンソル積で整理すること自体は既知です。本プロジェクトの `Category.lean` の対称モノイダル構造を、それだけで新規な暗号学的成果とは扱いません。

### [C2] Broadbent–Karvonen, *Categorical composable cryptography*

- 会議版 FoSSaCS 2022：[DOI:10.1007/978-3-030-99253-8_9](https://doi.org/10.1007/978-3-030-99253-8_9)。拡張版：[arXiv:2208.13232v5](https://arxiv.org/abs/2208.13232v5)、[LMCS DOI](https://doi.org/10.46298/lmcs-19(4:30)2023)。書誌・要旨を確認。
- ジャーナルは LMCS 19(4:30), 2023。2024年の v5 は訂正版であり、2024年の別の新規論文として数えません。
- simulation paradigm、抽象的攻撃モデル、逐次・並行合成、安全なプロトコルの対称モノイダル圏を説明します。
- **比較**：行列操作が対称モノイダル圏をなすことと、攻撃者・simulator・resource construction を含む composable security の圏を構成したことは異なります。既存の `Approx.pre/post/trans` と BB84 の誤差合成は重要ですが、これだけで同論文の一般的な simulation-based 定理や UC 定理を形式化したとは言えません。
- 圏論を論文の主要貢献にするなら、**具体的な攻撃・距離モデルと抽象的な合成安全性との橋を核で証明し、部品の置換で利用する**ことが次の候補です。

### [C3] Heunen–Landsman–Spitters, *A topos for algebraic quantum theory*, CMP 291(1), 63–110 (2009)

- 一次資料：[arXiv:0709.4364v3](https://arxiv.org/abs/0709.4364v3)、[DOI](https://doi.org/10.1007/s00220-009-0865-6)。要旨・書誌を確認。
- 可換部分代数の文脈からトポス、内部可換 C*-代数、内部スペクトル、valuation を構成します。
- **比較**：本プロジェクトの `SpectralStages.lean`・Bohrification はこの研究系統です。有限鍵 BB84 の数値誤差を改善する手段と同一視せず、内部・外部スペクトル対応などの別の主定理として評価します。

## 6. 本プロジェクトとの比較

対象は現在の開発中コード（基点コミット `5a0dae53dc0cadb508534e81c4ec64f57d50b610` と、その上の `UsefulBB84` 等の変更）です。本プロジェクトについても独立した外部レビューを実施したという意味ではありません。

| 評価軸 | 本プロジェクトの証明済み範囲 | 投稿時に明記する境界 |
| --- | --- | --- |
| 攻撃 | `BlockAttack` による任意の有限クラウス・ブロック攻撃、有限の量子側情報 | 任意の実装欠陥・光学的 source/squashing/decoy モデル・無限次元まで保証したとは主張しない |
| プロトコル出力 | `realState` の両者の鍵、公開記録、検証・PA 種、中止を保持 | ハードウェアや実行可能コードへの refinement は別 |
| 安全性 | `IdealKey.Secure` と `1/2 Tr sqrt(ΔᴴΔ)` の上界との同値、具体的 BB84 の同距離 `≤2^-60` | 任意環境の UC/resource security との橋は別。距離の同値だけで一般 UC を主張しない |
| 集中評価 | 任意の固定誤り集合、非復元抽出の指数上界、量子標本誤差への接続 | Hoeffding/Serfling 型の数学自体は新規ではない |
| 数値 | 25,165,824信号、65,536出力ビット、総誤差 `2^-60` 以下 | 誤り許容0の非自明な例。最適鍵率や実用装置の性能優位とは主張しない |
| 非自明性 | `HonestBB84.outcome_eq_errorFreeRecords` が無攻撃の実際の量子測定と古典記録を同定。`UsefulBB84.honest_success` が最終訂正・検証・PAを含む物理状態の受理確率 `≥1/2` | 雑音下の完全性、鍵率最適化は別 |
| 認証 | 認証済み公開通信が前提 | 現在の線形タグ衝突補題は、観測後の適応的偽造への認証定理ではない。認証鍵消費込みの net key expansion は未証明 |
| 信頼基盤 | 主定理の公理依存は `propext`・`Classical.choice`・`Quot.sound`。ビルド・監査記録あり | 公理監査だけでモデルの科学的正しさを保証するわけではない。他ライブラリの信頼基盤との比較にはその監査も必要 |

### 現時点で妥当な貢献の書き方

> We present a kernel-checked Lean formalization of a specified finite-dimensional BB84 protocol under authenticated classical communication. The development connects quantum sampling, finite-population concentration, explicit reconciliation leakage, public-seed privacy amplification, verification, and abort-preserving real/ideal output security. A concrete instantiation certifies a positive output key length with a small total operational error.

この表現は順位・最高性能・装置認証・一般 UC の主張を含みません。投稿時は各項目を定理番号と公開成果物のタグに対応させます。

仮題候補：**Kernel-Checked Finite-Key BB84 Security in Lean with Explicit Sampling and Leakage Budgets**。

## 7. 投稿判断を変える追加作業

優先順：

1. **[U1] FVQKD の所在と主定理を確認**。完成した同等の結果があるなら、証明経路・前提・プロトコル・再利用性を比較する。「初」を避けることで成果の価値が直ちに消えるわけではありません。
2. **[P4] Lean-QIT の固定版と定理単位の比較**。鍵安全性の定義、公開種の距離評価、抽出器の前提、完成した BB84 端点を区別。ライブラリ規模や証明行数だけで優劣をつけない。
3. **安全性とプロトコル意味論の独立レビュー**。[M8] が指摘する仕様・前提のずれを確認。trace-distance 規約の対応は `TraceDistanceNorm` と `BB84Completion` で証明済み。公開の順序、攻撃モデルの量化範囲の外部レビューは残る。
4. **正直実行の拡張**。無攻撃量子実験と誤りなし記録の接続・最終受理確率は証明済み。次は雑音下の完全性を評価する。
5. **成果物の公開固定**。[再現手順](artifact.md)は内容ハッシュ、依存リビジョン、全体ビルド、主定理・公理監査を固定する。公開リリースタグや DOI の発行は別途行う。
6. 圏論を主題にする場合は [C2] の合成安全性との橋を追加し、単なる量子回路の圏の再構成を主要な新規性にしない。Bohrification は別の主定理・論文軸にする。

## 8. メタ論理の数学的基盤

後続の調査で、既存の `Presentation`、`Derivation.substitute`、`Translation` が
Bauer–Haselwarter–Lumsdaine, *A general definition of dependent type theories*
（2020）の §2.2 “Closure systems” と定義単位で対応することを確認しました。
著者らの Coq `Auxiliary/Closure.v` の版も固定して照合しています。
規則・仮定付き導出・接ぎ木・規則を導出へ送る写像は、明示的な数学的先行研究です。

[メタ論理の出典・対応表・応用上の貢献](../metalogic-literature-review.md)に詳細を記録しました。
現在の核はこの部分の有限前提・有限仮定版であり、同論文の依存型理論全体とは区別します。
コード・資源・損失の複数解釈への接続と BB84 への適用は、数学的核とは別に評価します。

## 9. 調査の限界

- arXiv・Crossref・検索索引に未登録の論文、修士・博士論文、非公開成果物、他言語の全資料を網羅していません。
- 外部の Coq/Rocq/Isabelle/Lean プロジェクトを全て取得してビルドしたわけではありません。[P4] は版を固定した7ファイルの宣言を確認しました。
- 論文の要旨、本文、スライド、コード、検索索引を混同しないことを優先しています。特に [F6] は書誌のみ、[U1] は未解決です。
- 「今回確認した資料に同じ端点が見つからない」から「世界初」とは結論しません。

この調査により、投稿の中心となる差分は具体化できました。掲載可能性や絶対的な新規性の最終判断には、未解決候補の取得と独立レビューが残ります。
