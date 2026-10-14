# ROM の最終目標への接続経路

## 到達条件

問い合わせ意味論の `prefixFreeMD_query_indifferentiable` と
`SecretPrefixMAC.public_constructed_security` は既に証明済み。
以下の作業で必要なのは、同じ候補シミュレータを通常の機械命令で実現し、
停止・費用・全状態・履歴を保持する証明を作って、そのコード生成器を認証済み論理へ登録すること。
ホスト側の表探索、追加の実現仮定、`sorry` に置換して完成扱いにはしない。

## 最短の依存順序

1. **固定終端ガードと失敗路を完成する。今回実装・検証。**
   `NativeSimulatorTerminalGuard.code` は固定の terminal に依存する。
   検査するのは terminal の反転ビット列と true マーカーのみであり、
   問い合わせの連鎖値を IV と一致させる条件は入れない。
   `actual_eq_expected_iff` が `terminalMessage` の入口述語との厳密な対応を与える。
   `accepted_run`、`rejected_run` は入力表と全セルを保持する。
   不一致後は `OutputSeekFlag.recover` で元のフラグ位置に復帰し、
   `NativeSimulatorNonterminalFresh.rejected_after_rewind` が既存の乱数生成・表追加へ接続する。
   各継続コードは `CodeRelocation.host` で結合し、不一致路の内部番地も正しく移す。

2. **前駆辺を一つ選ぶ表走査。全表反復・最初の一致・停止・資源評価まで証明済み。**
   `RawTapeEquality.component` は固定14命令で、生の応答フィールドと、
   空白で終わる実行時ターゲットを比較する。
   幅の一致を入口条件として、入力表の次のマーカー・全接尾辞を保存する。
   `NativeSimulatorPredecessorRecord.run` は元の record marker・delimited key を
   実際の移動命令で越えて、この比較器へ入る。
   `NativeSimulatorPredecessorFilter.guarded_run` は表末尾の false マーカーを先に判定し、
   非空項目では false のデータマーカー／true の終端マーカーを実際の命令で選別する。
   `skipRemaining_run` は終端項目を飛ばし、`toResponse_run` は候補の応答位置へ進む。
   `RawTapeEquality.return_run` は実際の halt を return jump に変え、`first_joint` は
   実際の最初の停止時刻を保証する。
   `NativeSimulatorPredecessorCandidate.select_run` は実際の比較フラグによる制御分岐を証明し、
   `rejected_next_run` は不一致後のターゲット復元と次の継続入口までを同一コードで実行する。
   `NativeSimulatorPredecessorStep` は発見・表末尾・不一致・終端スキップの4停止箇所を持つ一巡。
   `NativeSimulatorPredecessorLookup` は不一致・終端スキップの停止のみを先頭への実際の jump に変える。
   同じ `5*n+4*κ+29` 命令のコードが任意の有限表を走査し、`dataEdges.lookup` と同じ最初の一致を選ぶ。
   `selected_layout` は選ばれた項目の符号化キーと残り表の物理配置を保証する。
   時間は `table.length*(8*n+2*κ+14)+n+3` 以下で、正確な最初の停止時刻と
   全途中状態・停止状態の符号長上界も証明した。
   `NativeSimulatorPredecessorExtract.run` は選択キーから previous/block を通常命令で取り出す。
   `NativeSimulatorPredecessorLookupExtract.run` は found halt を実 jump に変え、検索と抽出を合成する。
   合成コード長は継続を除いて `14*n+18*κ+44`、成功時間は
   `table.length*(8*n+2*κ+14)+8*n+10*κ+16` 以下。辺欠落の halt は保持する。

3. **再構成ループを通常命令へ落とす。入口契約からの反復・停止・全状態資源評価まで証明済み。**
   `MessagePrefixLoop.find_eq` は先頭から最初の一致を選ぶことを証明する。
   `run_eq` の不変条件は、残り fuel・現在 target・回収済み suffix に対して
   `run.message = (messagePrefix fuel target).map (fun blocks => blocks ++ suffix)`。
   前駆辺を見つけたら block を suffix の先頭へ積むので、最後にブロック列を再反転する必要はない。
   `run_bounds` は最大 fuel 回の探索、最大 `fuel * table.length` 回のレコード検査を保証する。
   これはレコード単位の参照費用であり、CPU 遷移予算ではない。
   `NativeSimulatorPredecessorLookupExtract.reconstruct_step` は実検索・抽出の出力が
   raw previous と `encodeList (fixedBits κ) (block :: suffix)` になることを証明する。
   target 前の `[none]` と古い target セルは実書込みで消費する scratch、右の suffix は保持する。
   `NativeSimulatorReconstruct.cycle_run` は選択 record marker から表先頭への実巻戻し、
   固定 IV 比較、入力テープ上の unary fuel 消費、次の反復への実 back-edge を同一コードで接続する。
   コード長は `17*n+18*κ+69`、表長・fuel に依存しない。IV 判定は fuel 消費より先に行う。
   `run` / `run_at_budget` は任意の衝突・循環を含む有限表で参照ループと同じ結果を返して停止する。
   `reconstruct_eq` / `message_law` は元 `messagePrefix` と機械観測分布の一致を保証する。
   遷移上界は `(fuel+1)*(table.length*(17*n+8*κ+26)+20*n+10*κ+50+6*(fuel+used))`。
   `encoded_peak` / `encoded_finish` は全途中状態／停止状態のコード・counter・表・両テープ・外部状態・履歴を評価する。
   IV 到達は空メッセージを含む成功、辺欠落・fuel 消尽は失敗。
   衝突・循環があっても参照実装と同じ結果になることを要求する。
   `ReverseOutputCopy.run` は片方のヘッドを左、もう片方を右へ動かすコピー部品を提供する。
   コピー先の空白領域は別途実際の命令で確保する必要があり、無料ではない。

4. **理想ハッシュ呼出しと表更新を接続する。未完了。**
   `NativeSimulatorTerminalFuel.accepted_run` は終端ガード成功路からの実行時表長計数・unary counter 初期化を接続する。
   同じ有限コードで全レコードを数え、input は `UnaryFuel.tape table.length 0 tableCells` になる。
   元 query は保持し、一時 output counter は実消去する。成功時間は
   `table.length*(12*n+8*κ+29)+n+2*κ+18`。全途中状態の符号長も評価する。
   `NativeSimulatorFuelPrepare.with_reconstruct_law` は、target と encoded empty suffix を供給した入口から
   実 fuel 初期化・再構成を合成し、元 `messagePrefix` と観測分布の一致を証明する。
   `NativeSimulatorKeyProtect.run` は counter-ready 出口から元 packet を input の fuel 終端空白の外へ
   実コピーし、表先頭へ戻ってから output に空 suffix を配置する。
   `UnaryFuel.counterWith` / `NativeSimulatorReconstruct.startWith` の保存領域契約が、
   各反復境界と全停止路で元キーを保持する。同じ再構成コード・遷移予算を使う。
   `NativeSimulatorTerminalReconstruct.accepted_law` / `stopped_key` は終端ガードから再構成停止までを
   同一コードで接続し、外部状態・全履歴・保存キー・`terminalMessage` の結果を同時に保証する。
   コード長は `31*n+33*κ+131+rejected.length`、全途中状態の符号長も評価する。
   回収したメッセージを公開パケットへ符号化し、元の問い合わせキーを退避してから `.call` する。
   応答読込みが出力テープを置換するため、キーを同じテープに残したまま呼び出さない。
   `SimulatorRemember`・応答返却の既存部品を再利用し、`compressionSimulator_eq` と
   全分岐の分布を対応させる。ここで `admissible` を除く。

5. **二窓口サービス・全攻撃・資源評価を接続する。未完了。**
   `NativePublicWorld` 系列の service/round 契約を、完成した ideal world に対して構成する。
   既存の `whole_result_gap` は `WholeWitness` を引数に要求する橋渡し定理。
   新たな実現仮定を追加せず、同じ emitted code について halts/queries/realizes を構成する。
   `WholeWitness.code` は security parameter の量化の外にあるので、固定幅の展開部品から
   一般の family へ接続する際には幅の実行時読取りを含む uniform code が必要。
   私有表と新規要求を同時に保持するサービスでは、既存の max 型入口サイズ仮定を
   そのまま使わず、実際の加算サイズに合う資源契約を証明する。

6. **MAC の emitted code と認証済み論理へ登録する。未完了。**
   型付きの `mergeAttack` とその意味論・問い合わせ予算証明を再利用する。
   `WholeReduction` の `compiler`、`mapWitness`、`code_eq` を具体的に構成し、
   `Backends.Interactive.reduction` で `interactiveObject` 間の `CertifiedReduction` へ変換する。
   現在の interactive compiler 構文は identity/suffix/constant/comp のみ。
   任意の caller の call site へサービスを挿入する変換を実現するには、
   必要な有限構文コンパイラとその実行証明を追加する必要がある。
   `Presented.Syntax` の rule の登録は単なる定理 import ではなく、
   `Presented.Interpretation` によるコード生成・witness・security 解釈まで接続して完成とする。

## 現在の範囲

上記の1、2の全表走査・選択キー抽出、3の入口契約からの機械再構成反復と資源評価を実装した。
終端成功路からの実 fuel 初期化・保護キー退避・空 suffix 配置・再構成停止まで接続した。
理想ハッシュ呼出しと保存キーの実回収・応答表更新、完全な理想世界、
新たな WholeWitness/WholeReduction、MAC のコード生成・論理登録は未完了。
この区別を保持したまま、2 → 3 → 4 → 5 → 6 の順に接続する。
