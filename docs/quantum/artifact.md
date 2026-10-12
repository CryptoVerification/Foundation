# 数値付き有限鍵 BB84 の再現可能な成果物

現在の到達点と再開時の課題は [BB84 形式検証の区切りと残課題](bb84-status.md) を参照してください。

## 保証と入口

最小の論文入口は
[`BB84PaperAudit.lean`](../../Foundation/Quantum/QKD/BB84PaperAudit.lean) です。
通常の `Foundation.lean` ビルドにも `GoalAudit` を通じて含まれます。

| 主張 | 宣言 |
| --- | --- |
| 既存の操作的上界と標準距離上界の同値 | `Density.stateApprox_iff_traceDistance_le` |
| 標準式 `D(ρ,σ) = 1/2 Tr sqrt(ΔᴴΔ)` | `Density.traceDistance_eq_half_traceNorm` |
| 最適な二値効果の存在 | `Density.exists_effect_attaining_traceDistance` |
| 直交量子ビットの距離は1 | `QKD.traceDistance_orthogonal_qubits` |
| 全出力理想鍵の距離規約 | `IdealKey.secure_iff_traceDistance` |
| 任意の有限クラウス・ブロック攻撃への数値付き安全性 | `UsefulBB84.secure_half_traceNorm` |
| 無攻撃量子測定と誤りなし記録の分布一致 | `HonestBB84.outcome_eq_records/outcome_eq_errorFreeRecords` |
| 最終量子出力の正直実行受理確率 `≥1/2` | `UsefulBB84.honest_success` |
| 正の出力鍵長 | `UsefulBB84.output_positive` |

パラメータは 25,165,824信号、3,145,728検査、最低生鍵長8,388,608、
一致検証64ビット、最終鍵65,536ビット、誤り許容0、安全性誤差 `2^-60`。
公開通信は認証済みというモデルです。距離は公開記録、両者の最終鍵、中止、
検証／PAの種と量子側情報を含む全状態に対するものです。
認証鍵消費込みの net expansion や一般 UC の定理とは区別します。

## 固定するもの

- Lean：`leanprover/lean4:v4.33.0`（`lean-toolchain`）。
- mathlib：`db584cd6d46c92f209a44c0f1c829460d327499d`。
- 全依存：`lake-manifest.json` の具体的な git リビジョン。
- 全ソースと文書：`artifact-manifest.json` にファイルごとの SHA-256 と総内容 ID を記録。
- 主定理の公理依存：[`paper-axioms.txt`](paper-axioms.txt)。
- 広い量子成果の公理依存：[`goal-axioms.txt`](goal-axioms.txt)。

許容公理は `{propext, Classical.choice, Quot.sound}`。
スクリプトは実行出力を解析し、追加の公理・`sorryAx`・不足した監査宣言を拒否します。
数学的前提やモデルの科学的正しさは、定理文と上記の境界で別に確認します。

内容 ID は git コミットではなく、**未コミットの証明も含めたソーススナップショットの ID**
です。アーカイブに `.git`、`.lake`、ビルドキャッシュは含めません。
ソースの絶対パスやローカル作業ツリーへ依存せず、展開先で再実行できます。

## 再実行

Python 3.9以上、Elan／Lake、git を用意し、成果物のソースを展開したルートで実行します。
出力先はソースツリーの外を指定してください。

```sh
python3 docs/quantum/reproduce.py --output /tmp/bb84-verification
```

このコマンドは次を行います。

1. ファイル一覧と全内容を manifest に照合。
2. `lake build` で全体をビルド。依存取得には初回ネットワーク接続が必要。
3. 各依存の実際の HEAD と変更状態、実行 Lean の版を確認。
4. 論文入口と全量子目標の監査を実行し、保存出力と完全一致を確認。
5. `build.log`、`lean-version.txt`、監査出力、`verification.json`、ソースアーカイブを生成。

`verification.json` はソース ID、アーカイブの SHA-256、Lean の実行版、
監査した各宣言の公理を保持します。アーカイブの圧縮メタデータは実行ごとに変わり得ますが、
展開後のソース ID は同じです。

## 開発者が新しいスナップショットを作る場合

文書・証明を更新した後の明示的な更新コマンドです。既存成果物の検証には使いません。

```sh
python3 docs/quantum/reproduce.py --output /tmp/bb84-freeze --freeze --refresh-audits
```

全体ビルドと公理検査が成功した後に監査出力と manifest を更新します。
生成されたアーカイブを別のディレクトリへ展開し、更新フラグなしの再実行で検証できます。

## 先行成果との固定版比較

[`code-comparison.md`](code-comparison.md) に Lean-QIT の7ファイルと FVQKD の所在調査を
記録しています。FVQKD は追加検索でも論文・主定理を特定できず、内容比較不能という
結論です。この不確実性を成果物の保証や「初」の根拠へ混ぜません。
