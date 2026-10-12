# Lean-QIT と FVQKD：固定版のコード比較

調査日：2026-10-12。宣言の前提・結論を比較し、検索できない成果を不在とは扱いません。

## Lean-QIT

対象：`QuAIR/Lean-QIT` コミット
**`15a0a5ef13e5824327e0850ea896e472366287af`**。
GitHub API の日時は `2026-10-05T10:53:29Z`、メッセージは `Sync public Lean-QIT export`。
今回確認した固定版は [こちら](https://github.com/QuAIR/Lean-QIT/tree/15a0a5ef13e5824327e0850ea896e472366287af)。

以下の7ファイルを取得して確認しました。外部プロジェクト全体をビルド・監査したという
意味ではなく、本プロジェクトとの機械検証済み相互運用も実装していません。

| Lean-QIT のファイル・宣言 | 前提と結論 | 本プロジェクトとの比較 |
| --- | --- | --- |
| `Security/BB84.lean`：`prepare_normalized`, `matched_basis_prob_self`, `matched_basis_prob_compl` | 単一量子ビットの準備と同基底の射影測定の Born 確率。自己ビット1・反対ビット0 | 基本 BB84 準備・測定の正しさは明確に重なる |
| 同：`processRounds`, `keptBits`, `buildTranscript` | 古典的なラウンド列から keep／abort と選別記録を構成 | 本実装は任意長のブロック密度、独立基底、実際の非復元検査、最終両鍵まで接続。確認したファイル末尾は entanglement-based security を将来課題とする |
| `Security/Key.lean`：`ComposableKey.main` | 劣正規化成功枝の Renner 秘密性述語と定義した距離上界の同値 | 安全性定義の重なりは大きい。この `main` はプロトコルから秘密性を導く定理ではない |
| `Security/KeyDistillation.lean`：`KeyDistillation.main` | 正しさ・Alice 秘密性・誤差和の上界を前提に `IsRennerEpsilonFullSecurityScaffold` を構成 | コメントは definition-level scaffold と明記。本実装の `AcceptedAbort.secure` は実際の理想化した全状態への距離、`UsefulBB84.secure_half_traceNorm` は BB84 固有の解析から数値上界を満たす |
| `Security/ExtractorTraceBridge.lean`：`extractorSecrecyDistance_le_two_mul_normalizedTraceDistance_add` | 近い状態の既証明秘密性から `2δ+ε` を導く。理想化チャネルの縮小性を使用 | 本実装の近似合成と重なる。これを独自の新アイデアとしない |
| 同：`extractorSecrecyDistance_le_seedAverageTraceDistance` | 公開種を含む全抽出器出力の距離を、各種の距離平均で抑える | 公開種・量子側情報の平均化は重なる。本実装の貢献は元の BB84 公開記録と中止を含む端点への接続 |
| `States/TraceNorm/Distance.lean`：`traceNorm`, `normalizedTraceDistance` | `traceNorm M = Re Tr sqrt(MᴴM)`、距離は `1/2 * traceNorm (A-B)` | 新しい `TraceDistanceNorm.lean` は同じ平方根の式への同定を証明。係数は一致。型や理想状態の構成の機械的な同値は未証明 |
| `States/TraceNorm/Spectral.lean`：`traceNorm_eq_singularValueSum`, `traceNorm_eq_singularValues_support_sum` | `Tr sqrt(MᴴM)` と mathlib の特異値和の対応。一般行列を扱う | Lean-QIT は一般行列の広い API。本実装は密度行列差に必要な Hermitian の固有値絶対値和と平方根の対応へ絞る |
| `States/TraceNorm/Variational.lean`：`traceNorm_eq_max_unitary_abs_trace`, `traceNorm_variational_contraction_abs_trace_le` | 一般行列の trace norm のユニタリ達成・上界、収縮行列への拡張 | 同じ有限次元の標準数学。本実装は trace-zero Hermitian 差の二値効果について最適射影を構成し、既存の `StateApprox` と同値にする |

今回直接取得した7ファイルは `BB84`、`Key`、`KeyDistillation`、`ExtractorTraceBridge`、
`Distance`、`Spectral`、`Variational` です。

## FVQKD：追加調査の結果

以前の検索索引が示した “Machine-checked composable finite-key security of BB84 in Rocq”
という説明から、完成済み成果と断定することはできません。
今回の追加調査でも論文・主定理・著者を特定できませんでした。

| 確認対象 | 2026-10-12 の結果 |
| --- | --- |
| `https://github.com/fvqkd/FVQKD` | HTTP 404 |
| GitHub API `users/fvqkd/repos` | 公開リポジトリは `fvqkd/CoqQ` のみ |
| `fvqkd/CoqQ` のメタデータ | `coq-quantum/CoqQ` の fork。既定枝 `main`。push 時刻 `2026-08-02T14:25:30Z` |
| その公開枝 | `main`: `0f6f38e1438beee61764cd6d7705d97566eb52f1`、`ci`: `70fa0b9cef57a61c7562557b47aca0977d033c34`、`opam`: `cdab337447eea783009adcb3c183bf75ccc930b8` |
| main の固定版ツリー | `BB84`／`bb84`／`QKD`／`qkd` を含むパスは取得したツリーにない。ファイル内容の全探索・他枝の証明監査ではない |
| GitHub repository search `FVQKD` | 2件の文字列一致。名前・説明から対象成果に結びつける証拠なし |
| repository search `BB84 language:Coq`、`"quantum key distribution" language:Coq` | ともに0件。言語判定・公開設定・索引に依存するため不在証明ではない |
| repository search `"finite-key" BB84` | 9件。返された説明は主にシミュレータ等で、対象 Rocq 成果を特定できない |
| OpenAlex `"FVQKD"` | 0件 |
| ePrint `BB84 Rocq`、`"BB84" "formal"` | 対象成果を特定できない。後者の結果1件は別題の鍵交換研究 |
| Google／DuckDuckGo／Bing | Google は JS 要求、DuckDuckGo は CAPTCHA、Bing は無関係な結果。題名の裏付けには利用しない |

**比較できる結論**：公開状態からは FVQKD の保証内容を比較できない。
したがって、投稿の差分は本実装の定理・前提・証明経路を明示する形にし、
「世界初」「既存 Rocq では未達」といった順位・不在の主張を採用しません。
所在確認には、対象の公開資料か著者からの情報が必要です。

## 現在の主張への反映

- trace-distance や基本的な matched-basis 正しさを新規な数学として主張しない。
- 数値付きの有限鍵 BB84 全出力定理と、正直な物理実験の受理確率を本実装の端点として示す。
- 認証済み公開通信、有限次元・有限クラウス攻撃、誤り許容0というモデルを明記する。
- この比較を外部コード全体の独立検証や、任意の将来版についての不在証明としない。
