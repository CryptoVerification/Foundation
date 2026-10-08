# Foundation

Lean 4 のライブラリです。Nix の開発用シェルで Lean と Lake（Lean のビルドツール）を利用できます。

## ディレクトリ構成

```text
Foundation/
├── Logic/                   # 意味論に依存しない理論提示と導出
├── Crypto/
│   ├── Core/                # goal、family、bound、reduction、関係
│   └── Semantics/
│       ├── Probability/
│       ├── Asymptotic/
│       ├── Resource/
│       ├── Machine/
│       └── Security/
├── Notions/
│   ├── PKE/
│   │   ├── INDCPA/
│   │   └── INDCCA2/
│   └── Signature/
│       ├── EUFCMA/
│       └── StrongEUFCMA/
├── Assumptions/
├── Constructions/
└── Examples/
```

`Crypto/Core/Family.lean` に instance family、adversary family、adversary class の定義をまとめています。Core のプロジェクト内 import は Core 内で完結します。確率・漸近解析・資源・機械実行・安全性の意味論は `Crypto/Semantics` に配置します。Lean の宣言名は維持し、import のモジュール名をこの配置に合わせています。

意味論に依存しない論理の核を [理論提示と導出](Foundation/Logic/Presentation.lean) に配置しています。判断と推論規則を与えると、導出、仮定の置換、モデルへの解釈を構成できます。モデルは命題だけでなく数値や証明構造も保持します。置換の恒等則・結合則、解釈との整合性、自由な構文モデルへの解釈の一意性を証明しています。現在の暗号論理は `Crypto/Logic/Presented` でその具体例として再構成します。帰着コードは構文から直接生成し、安全性・資源・分布の意味は別に解釈します。論理の構成と保証の範囲は [安全性論理の説明](docs/crypto-logic.md#意味論に依存しない理論提示への再構成) を参照してください。

[理論の翻訳](Foundation/Logic/Translation.lean) は、判断と規則を別の理論の判断と導出へ写します。恒等翻訳・合成・仮定の置換との整合性・解釈の一致を証明しています。コード・優位性上界・資源を保存する条件は、各モデルの間の写像として明示します。[暗号化してから認証する方式の具体的な帰着](Foundation/Constructions/Symmetric/EncryptThenMAC/ConcreteOperational.lean) は、暗号化とメッセージ認証という異なる二つの仮定を使う規則を展開し、有限コード、実際の停止証拠、ゲームの分布の一致、元の資源情報を接続します。具体的な実行への接続は一回限りの1ビット暗号化と二行の認証表について構成し、一般の方式には意味論上の合成定理を提供します。

この具体例について、[認証表の偽造確率](Foundation/Constructions/Symmetric/EncryptThenMAC/TableMACSecurity.lean) と [1ビット暗号化の完全秘匿性](Foundation/Constructions/Symmetric/EncryptThenMAC/OneBitSecurity.lean) も証明しています。認証への問い合わせが高々1回なら、幅 `w` ビットのタグの偽造確率は `2^(-w)` 以下です。一回の暗号化が成功した後は追加要求が失敗応答になるため、元の攻撃者が複数回要求しても、この帰着の認証問い合わせは高々1回です。[具体的な合成安全性](Foundation/Constructions/Symmetric/EncryptThenMAC/ConcreteSecurity.lean) は、暗号化の識別優位が厳密にゼロであることと認証の上界を合成規則に代入し、有限コードの攻撃者に対する上界 `2^(-w)` を、計算困難性の仮定なしに導きます。

方式間の再利用に向けて、[部品の実行契約](Foundation/Crypto/Semantics/Procedure.lean) は、入力と出力の型、機械の完全な配置、実際の費用分布と上界を保持します。途中の終了配置が次の実行へ進む場合も合成でき、データのコピーは配置の一致だけで省略できません。[有限コードの呼び出し](Foundation/Crypto/Semantics/Machine/ProcedureCall.lean) は、既存の命令列の実行と終了後の制御移譲を接続し、移譲に1段階を数えます。[一回限りの暗号化の共通定理](Foundation/Constructions/Symmetric/EncryptThenMAC/OneUsePrivacy.lean) は、鍵・平文・暗号文・状態の型を限定せずに適応的な攻撃への完全秘匿性を導きます。既存の1ビット方式と [任意長のワンタイムパッド](Foundation/Constructions/Symmetric/EncryptThenMAC/OneUsePad.lean) が同じ定理を使います。これらは部品と意味論の一般化です。任意長の方式について帰着機械全体と資源証拠を生成する接続は、引き続き構成する必要があります。

[有限コードを順に実行する制御](Foundation/Crypto/Semantics/Machine/Sequence.lean) は、部品間で入力・出力テープをそのまま引き継ぎます。命令位置と終了フラグの変更に1段階を数えます。次の部品の入口配置との一致を証明して初めて部品を合成でき、入力準備やコピーが必要なら、そのための実際のコードを加える必要があります。[二つのコードの実行例](Foundation/Examples/NativeSequence.lean) は、最初のコードの乱数ビットを、次のコードが同じテープ上で読み取って反転させる全実行を証明します。

[状態の条件の保存](Foundation/Crypto/Semantics/Invariant.lean)、[全実行の分布の対応](Foundation/Crypto/Semantics/Simulation.lean)、および [秘密側と公開側の履歴の対応](Foundation/Crypto/Semantics/Oracle/History.lean) も方式に依存しない共通定理です。既存の認証側の履歴証明と、秘密性側・認証側の攻撃者の状態の観測へ適用しています。一段階の分布の対応や実装の全配置の分布の一致は、各実装が証明する必要があります。

[呼び出し元の状態の保持](Foundation/Crypto/Semantics/Framing.lean) は、部品に保存した呼び出し元の状態を渡さず、全実行中にその状態を保持します。[具体例](Foundation/Examples/SavedCaller.lean) は、完全な機械配置を保持した鍵生成と二つのコードの実行を証明します。保存状態への入口の処理、入力準備、および応答のコピーの費用は別途証明する必要があります。

[コピーの実行契約](Foundation/Crypto/Semantics/Machine/CopyContracts.lean) は、既存の有限コピーコードを部品として使えるようにします。区切りの後のデータを残すコピーと、入力の先頭へ戻るコピーについて、完全な入口・出口配置と費用を保持します。入力の先頭へ戻る [共通のコードと証明](Foundation/Crypto/Semantics/Machine/RetainedCopy.lean) は、既存の暗号方式の鍵コピーでも再利用します。これらの契約の入口に必要な配置は、呼び出し元が実際の処理で用意する必要があります。

[問い合わせと再開の共通契約](Foundation/Crypto/Semantics/Oracle/QueryTransfer.lean) は、攻撃者の実際の呼び出し命令、要求の読み取り、外部問い合わせ、応答の書き込みとヘッドの復帰を接続します。要求長を `R` ビット、応答長の上界を `B` ビットとすると、制御の上界は `2*R+3*B+6` 段階です。問い合わせ先の内部計算の費用は別扱いです。[部品の応答を取り出す制御](Foundation/Crypto/Semantics/Machine/ResponseExport.lean) は、停止した部品の物理的な出力テープを先頭へ戻し、空白まで読み取り、応答の順序を復元します。長さ `L` ビットについて制御移譲を含めて `3*L+4` 段階です。[適用例](Foundation/Examples/ResponseExport.lean) は、任意幅 `w` の乱数生成とパッド暗号の暗号化を同じ制御へ接続し、それぞれ `8*w+6`、`11*w+6` 段階の上界を証明します。暗号化の入力準備と、これらの共通制御から帰着全体を生成する接続は引き続き必要です。

[部品から攻撃者への応答](Foundation/Crypto/Semantics/Oracle/NativeCallback.lean) は、部品の実行、物理テープからの応答の取り出し、攻撃者側への書き込み、再開を一つの制御へ接続します。部品の時間上界を `T`、応答長の上界を `B` ビットとすると、上界は `T+6*B+7` 段階です。部品が早く終了した場合は、実際の終了時点から応答を返し、残りの時間で攻撃者を実行します。[全実行の適用例](Foundation/Examples/NativeCallback.lean) は、任意幅 `w` の乱数生成とパッド暗号の暗号化から、再開した攻撃者の実際の停止命令までを、それぞれ `11*w+10`、`14*w+10` 段階で証明します。この契約の入口には部品の入力が準備済みである条件が残ります。元の攻撃者の要求を入力準備へ渡す処理、複数回の呼び出しを扱う帰着全体、および論理の資源証拠への登録は引き続き必要です。

[二つの入力の物理的な準備](Foundation/Crypto/Semantics/Machine/PairPreparation.lean) は、別々のテープのビットを一セルずつ読んで交互に書き込み、元の二つのテープと準備したテープのヘッドを先頭へ戻します。各入力が `w` ビットなら制御の時間は `12*w+3` 段階です。長さの不一致は明示的に拒否し、正常終了では区切りの後の全セルも保持します。[パッド暗号への適用](Foundation/Examples/PairPreparation.lean) は、準備した実際のテープ上で既存の暗号化コードが停止し、正しい暗号文を出すことを証明します。末尾の空白の表現を無料で変更する処理はありません。

[準備から応答までの共通制御](Foundation/Crypto/Semantics/Oracle/PreparedCallback.lean) は、別々の入力テープから実際の入力を準備し、暗号部品を実行し、応答を攻撃者へ返して再開する一回の呼び出しを接続します。準備した物理配置と部品の入口の一致を証明する条件があり、実行時には実際のバッファを渡します。[完全な配置を扱う暗号化契約](Foundation/Crypto/Semantics/Machine/PreparedXor.lean) は、末尾の空白と後続のセルを保持した入力上で既存の暗号化コードを実行します。[全実行の例](Foundation/Examples/PreparedCallback.lean) は、任意幅 `w` の鍵と平文が別々のテープにある入口から、攻撃者の実際の停止命令まで `26*w+14` 段階で接続します。元の鍵・平文テープの全セルも保持します。鍵生成、元の攻撃者から始める帰着全体の費用と分布、複数回の問い合わせ、および安全性論理の資源証拠への登録は引き続き必要です。

[元の呼び出しからの入口](Foundation/Crypto/Semantics/Oracle/SourceEntry.lean) は、攻撃者の実際の呼び出し命令から要求を取り出し、元の要求テープを共通の入力準備へ渡す制御です。要求長 `R` ビットについて `2*R+4` 段階で、命令位置の更新、要求の読み取りと順序の復元、準備への制御移譲を証明します。[任意幅の適用例](Foundation/Examples/SourceEntry.lean) は、実際の平文要求から、鍵と要求を持つ準備処理の入口へ接続します。応答の書き込み後に攻撃者へ戻す移譲にも1段階を数えます。使用済み状態と拒否応答、鍵生成、および安全性論理への登録は引き続き必要です。

[外側の制御での呼び出し契約](Foundation/Crypto/Semantics/Oracle/SourceCallback.lean) は、実際の準備・部品実行・応答処理・攻撃者への復帰を、最初の復帰時点までの費用分布として構成します。元の呼び出し命令を含める `invoke` は、任意の攻撃者の命令列と保存する命令位置を扱い、残りの時間で外側の攻撃者を実行します。[パッド暗号の全実行](Foundation/Examples/SourceCallback.lean) は、実際の呼び出し命令から再開後の停止命令まで、任意幅 `w` について `28*w+19` 段階で接続します。鍵生成と、一回限りの使用を強制する状態の制御は、この例には含めません。

[成功・拒否の共通応答](Foundation/Crypto/Semantics/Machine/ResponsePacket.lean) は、拒否を `[false]`、正常応答を `true :: payload` として区別します。空の正常応答も拒否とは異なります。符号化と復号の往復、余分なビットを持つ拒否の不正判定、および各セルの書き込みとヘッド移動を別々に数える有限制御の実行を証明します。本文が `L` ビットなら書き込みは `2*L+3` 段階、拒否は3段階です。これは新しい応答用テープへ書く部品の契約であり、既存の暗号化出力からの取り出し、応答の配送、使用済み状態の制御への接続は別途必要です。

[不正な長さの入力への拒否処理](Foundation/Crypto/Semantics/Machine/PreparationCheck.lean) は、入力準備の拒否時に実際の二つの入力テープと作業バッファを保持し、各ヘッドを戻してから共通の拒否応答をテープへ書きます。短い方の入力が `m` ビットなら上界は `12*m+10` 段階です。元の入力テープは区切りの後のセルまで復元します。正常入力の準備は同じ制御で従来の `12*w+3` 段階です。外側の攻撃者への拒否応答の配送と使用済み状態への接続は引き続き必要です。

[拒否応答から攻撃者への復帰](Foundation/Crypto/Semantics/Oracle/FailureCallback.lean) は、不正な長さの入力の準備、ヘッドの復帰、拒否応答の物理的な書き込み、テープからの応答の取り出し、攻撃者への書き込みと再開を同じ制御で接続します。短い入力が `m` ビットなら上界は `12*m+24` 段階で、実際の費用分布を保持して残りの時間で攻撃者を実行します。[全実行の例](Foundation/Examples/FailureCallback.lean) は、再開した攻撃者の停止命令まで `12*m+25` 段階で実行し、秘密データ用テープと元の要求テープを保持します。入口は要求が既に捕捉された配置であり、外側の呼び出し命令と使用済み状態の接続は引き続き必要です。

[一回限りの使用を強制する外側の制御](Foundation/Crypto/Semantics/Oracle/OneUseSource.lean) は、実際の呼び出し命令から要求を捕捉し、正常な長さの要求を受け付けた時点で使用済みにします。使用済みの要求は暗号化部品へ渡さず、物理的な拒否応答を返します。任意の実行時間と問い合わせ先について受付は高々一回で、使用済み状態は元へ戻りません。[共通の受付回数の定理](Foundation/Crypto/Semantics/OneUseCounter.lean) は証明用の回数を記録しても実行分布を変えないことを証明します。[二回の呼び出しの全実行](Foundation/Examples/OneUseSource.lean) は、使用済みの鍵に対して二回拒否して実際に停止し、最初の要求長 `R` ビットについて `2*R+47` 段階です。正常・拒否の応答を扱う [共通制御](Foundation/Crypto/Semantics/Oracle/CheckedCallback.lean) の正常経路について、任意長の暗号化部品の分布と資源上界の契約を接続する証明は引き続き必要です。

[正常応答の分布と費用の契約](Foundation/Crypto/Semantics/Oracle/CheckedResponse.lean) は、任意の暗号化部品の実行、応答の取り出し、成功の印の実際の書き込み、攻撃者への配送と再開を、正常・拒否の共通制御へ接続します。部品の上界が `T` 段階、本文の上界が `B` ビットなら、部品開始から再開まで `T+11*B+22` 段階です。復帰配置の分布は、部品の出力分布の各応答に成功の印を付けた分布に一致します。[任意長のパッド暗号への適用](Foundation/Examples/CheckedResponse.lean) は、入力準備済みの配置から実際の停止命令まで `19*w+25` 段階で証明します。この契約は入力準備済みの配置を入口にします。

小さな安全性論理を `Crypto/Logic`、導出からの帰着構成と健全性の証明を `Crypto/Meta` に配置しています。帰着の式は恒等・登録済み帰着・合成からなり、安全性の導出は仮定の使用と帰着による輸送からなります。導出から、使用した仮定、有限の帰着コンパイラ、多項式停止予算、優位性の損失を取り出します。既存の ElGamal と具体的な素数位数の群にも接続しています。`CompactProgram` は、約1477億命令になる具体的な帰着コードを展開せず、証明付きの長さと命令取得を提供します。定義・保証の範囲・確認方法は [安全性論理の説明](docs/crypto-logic.md) に記載しています。停止予算は解析用データであり、初版では係数・次数の数値計算や一般の完全性を要求しません。

二前提の拡張は、一人の攻撃者から二つの攻撃者を構成し、二つの優位性の損失付きの和で元の優位性を抑えます。導出から各仮定へのプログラムと停止予算を取り出し、仮定の置換によるコードと上界の合成を証明しています。三つの確率的な実験の区別困難性を具体例として確認しています。

共通鍵暗号については、[ワンタイムパッド](Foundation/Constructions/Symmetric/OneTimePad.lean) の完全秘匿性と、[PRG から作る一回限りの暗号](Foundation/Constructions/Symmetric/PRGResource.lean) の帰着を追加しています。PRG は擬似乱数生成器です。元の有限攻撃コードから二つの帰着コードを生成し、XOR と入力転送を含む時間上界、各帰着の一回の問い合わせ、確率分布の実現を証明します。暗号文長が `L(n)` ビットで元の攻撃時間が `t(n)` 遷移なら、PRG の `t(n) + 2n + 10L(n) + 9` 遷移での識別優位の上界 `ε(n)` から、暗号の識別優位の上界 `2ε(n)` を導きます。特定の PRG の安全性や、同じ鍵で複数回暗号化する場合の安全性は仮定・結論に含めません。

`Models`、`Theories`、`Zoo` は、それぞれモデルの具体化、暗号学的理論、証明済みの含意・同値・分離の整理に使う予定です。

実行機械を一般化した論理は `CryptoLogic.General` にあります。ビット命令列、XOR を行う前処理機械、対話的な問い合わせ機械を、共通の導出・帰着抽出に接続しています。帰着の入力と出力には機械の型が付きます。生成したコードそのものについて、各機械の停止・資源上界・確率分布の実現を保証します。旧 API の導出も、生成コードを変えずに変換できます。[実行機械の一般化](docs/crypto-logic.md#実行機械の一般化) に保証の範囲を記載しています。 [PRGLogic.lean](Foundation/Constructions/Symmetric/PRGLogic.lean) は PRG 暗号の二前提帰着をこの論理に登録します。同じ PRG 安全性の仮定を二回使い、二つの生成コードと損失項を保持します。共通の健全性定理で漸近的な安全性を導き、共通の優位性上界定理で具体的な `2ε` の上界を導きます。 共通 API の `runWitnesses` は、各生成コードに対象機械の停止・資源・分布の証拠を付けて返します。明示的な `Analysis` を使うと、仮定の置換後も指定した証明木の損失式を保持できます。 帰着コンパイラの `normalize` は恒等と合成の構文を整理し、生成コード・損失式・資源証拠を厳密に保存します。

資源上界の合成に必要な数値計算は、[PolynomialBound.lean](Foundation/Crypto/Semantics/Resource/PolynomialBound.lean) にまとめています。攻撃者に対する資源上界とプログラムに対する資源上界は、この共通補題を使います。機械実行の証明では、`Step.halt` と `Step.resumeAt_halt` が停止命令の実行を扱います。`GuardedCompiler.sourceStorage_le_of_initial_run` は、入力から実行した後のテープ容量を入力長と操作回数で評価します。


任意の固定段数のハイブリッド導出には、各段階の帰着コードと、損失・停止上界の証明があります。可変段数の共通上界は、入力に指定した回数だけ問い合わせる一つの固定された有限コードの実行にも接続しています。擬似乱数関数（PRF）からカウンターを使う複数回暗号化への帰着は、理想実験の完全秘匿性、有限コードの全実行の一致、停止・時間・問い合わせ上界まで証明しています。`PRFCounterLogic` は既存の二前提規則にこの帰着を登録し、同じ PRF 仮定から `2ε` の上界を導きます。公開の問い合わせ上限を入力テープとして与える実行モデルです。[定理と実行モデルの範囲](docs/crypto-logic.md#任意の固定段数と可変段数のハイブリッド) を参照してください。

ワンタイムパッドについて、鍵生成・暗号化・復号を固定された有限ビット命令列で実装しています。鍵生成と暗号化を一つのコードで行い、生成した鍵と暗号文の同時分布も証明しました。実コードから定義した安全性実験の識別優位は、計算困難性の仮定なしに厳密にゼロです。既存の二前提論理にも接続しています。鍵は一回だけ使用する方式です。[実装と安全性の保証](docs/crypto-logic.md#ワンタイムパッドの有限コードと無条件の安全性) を参照してください。

## セットアップ

```sh
nix develop path:.
lake build
```

開発用シェルを開かずにビルドする場合は、`nix develop path:. -c lake build` を実行してください。`path:.` は、Git にまだ登録していない設定ファイルも現在の作業ディレクトリから読み込む指定です。
Lean のソースコードは `Foundation/` に追加し、`Foundation.lean` から読み込んでください。

## ElGamal の安全性定理の使い分け

sampling は厳密一様性を維持する方針です。[FiniteRandomness.lean](Foundation/Crypto/Semantics/Machine/FiniteRandomness.lean) は、有限の実行予算では厳密一様 sampling に `q ∣ 2^B` が必要であることを証明しています。[ExpectedExecution.lean](Foundation/Crypto/Semantics/Machine/ExpectedExecution.lean) は期待操作回数を定義し、有限期待時間から非停止確率が0に収束することを証明しています。[LimitExecution.lean](Foundation/Crypto/Semantics/Machine/LimitExecution.lean) は、その収束を仮定して停止出力の極限分布を構成し、全分岐の有限停止上界がある場合に既存の有限 evaluator と一致することを証明しています。[RejectionSamplingSemantics.lean](Foundation/Crypto/Semantics/Machine/RejectionSamplingSemantics.lean) は、一つの固定された有限コードについて、全ての正の q の厳密一様分布と、全入力で `24*(入力長+1)` 操作の期待上界を証明しました。このコードには q=3 で有限の最悪時停止上界がないことも証明しています。

計算量を制限した攻撃者についての主結果は、[MachineSecurity.lean](Foundation/Constructions/ElGamal/MachineSecurity.lean) の
`ElGamal.secureRepresentedINDCPA_of_secureRepresentedDDH_nativeMachinePPT` です。
DDH 側の `representedDDHInterface … .pptClass` 上の安全性から、ElGamal 側の
`representedINDCPAElementPPTClass` 上の IND-CPA 安全性を導きます。
後者は実際に到達する IND-CPA リクエストの長さも制限します。攻撃者と構成したシミュレータの機械コードは、すべての有限入力・乱択分岐について多項式時間で停止します。

この定理には次の前提があります。

- `RepresentedSimulatorPrimitives`：instance と群要素の符号化・長さ上界、および群乗算の有限機械コード、正しさ、全入力・全分岐の多項式停止の証明。
- `RepresentedChooseNormalizer`：choose 応答の正規化のコードと証明。
- `hDDH`：上記 DDH 攻撃者 class に対する暗号学的困難性の仮定。

シミュレータの変換 witness `T` を外部から渡す必要はありません。シミュレータが呼び出さない scalar sampler と累乗の停止証明も、この定理には不要です。従来の全演算 interface `RepresentedMachinePrimitives` は残しており、`toSimulatorPrimitives` で必要な field を取り出せます。厳密 sampler 単体の期待時間は証明済みです。[FramedScalarPreparation.lean](Foundation/Crypto/Semantics/Machine/FramedScalarPreparation.lean) は、要求フレームから `q` の canonical bits と元の固定幅カウンターを実命令で準備し、固定幅表現での多項式予算を証明します。[FramedScalarSampler.lean](Foundation/Crypto/Semantics/Machine/FramedScalarSampler.lean) は保存カウンター付き抽選と固定幅返却まで有限コードを接続し、成功する実行分岐を証明します。[SavedRejectionSamplingSemantics.lean](Foundation/Crypto/Semantics/Machine/SavedRejectionSamplingSemantics.lean) は保存データを保持した抽選処理単体の厳密な一様分布・確率1での停止・法のビット長に対する線形期待操作回数を証明します。[ScalarSamplerContinuationDistribution.lean](Foundation/Crypto/Semantics/Machine/ScalarSamplerContinuationDistribution.lean) は、準備済みの実テープから抽選・固定幅化・呼出元の停止まで接続した有限コードの厳密な一様分布と、公開幅に対する線形期待操作回数を証明します。[FramedScalarSamplerSemantics.lean](Foundation/Crypto/Semantics/Machine/FramedScalarSamplerSemantics.lean) は、要求フレームの準備・抽選・固定幅化・停止を含むコード全体の厳密な一様分布、確率1での停止、多項式の期待操作回数を証明します。[PrimeOrderScalarSampler.lean](Foundation/Constructions/ElGamal/PrimeOrderScalarSampler.lean) は、その機械出力を既存 ElGamal の scalar 符号化と理想分布へ接続します。[PrimeOrderNativeKeygen.lean](Foundation/Constructions/ElGamal/PrimeOrderNativeKeygen.lean) は、要求読取り・厳密抽選・実際の累乗・鍵対返却まで含む一つの有限コードの出力分布が、既存方式の `scheme.keygen` と一致することを証明します。有効な parameter family に対する多項式の期待操作回数も証明済みです。[NativeEncryption.lean](Foundation/Crypto/Semantics/Machine/NativeEncryption.lean) は、要求読取り・厳密抽選・同じ scalar による二つの累乗・乗算・暗号文返却・停止を接続した有限コードについて、数値上の厳密な暗号文分布、確率1での停止、多項式の期待操作回数を証明します。[PrimeOrderNativeEncryption.lean](Foundation/Constructions/ElGamal/PrimeOrderNativeEncryption.lean) は、この暗号文分布が既存方式の `scheme.encrypt` を既存の群要素 codec で符号化した分布と一致することを証明します。同じコード・要求について、確率1の停止と任意の有効な parameter family に対する多項式の期待操作回数も接続しています。公開要求を物理テープ上に保存する前処理と、保存データを保持した抽選・固定幅化の実行分岐も構成済みです。

[PrimeOrderGroup.lean](Foundation/Constructions/ElGamal/PrimeOrderGroup.lean) は、素数有限体内の素数位数部分群と、その codec・群法則・復号の正しさを構成します。[BinaryArithmetic.lean](Foundation/Examples/BinaryArithmetic.lean) では有限ビットコードによる比較・加減算・条件付き二倍剰余・剰余加算の正しさと全入力停止を確認しています。[PrimeOrderRepresentation.lean](Foundation/Constructions/ElGamal/PrimeOrderRepresentation.lean) は、既存の構成・codec・理想 scalar 分布への数学的な接続を証明します。[BinaryProductWorkspace.lean](Foundation/Examples/BinaryProductWorkspace.lean) は、乗算用の作業領域の初期化・未処理ビットの選択・算術入力の準備・結果の書き戻しの有限コードを確認します。[BinaryProduct.lean](Foundation/Examples/BinaryProduct.lean) では、これらを一つの有限乗算コードとして接続し、全入力での4次多項式による停止上界と、妥当な入力での剰余積の正しさを確認しています。[BinaryPower.lean](Foundation/Examples/BinaryPower.lean) では、完全な有限累乗コードの全入力停止と、有効な入力に対する剰余累乗の正しさを確認しています。[BinaryWorkspacePreparation.lean](Foundation/Crypto/Semantics/Machine/BinaryWorkspacePreparation.lean) は作業幅を１列広げる３ビットの書き込みと巻き戻しを実命令で行い、[BinaryProductPadded.lean](Foundation/Crypto/Semantics/Machine/BinaryProductPadded.lean) はその返却テープを乗算コードへ接続して全入力停止と剰余積を証明します。[BinaryProductExternalWidth.lean](Foundation/Crypto/Semantics/Machine/BinaryProductExternalWidth.lean) は、高位の作業ビットを消す３命令まで乗算コードへ接続し、全入力停止と有効な生入力に対する外部幅どおりの剰余積を証明します。[BinaryPowerExternalWidth.lean](Foundation/Crypto/Semantics/Machine/BinaryPowerExternalWidth.lean) は、作業幅を広げて累乗を計算した後、実命令で高位ビットを消し、外部幅で返します。両コードは全入力で停止します。[PrimeOrderArithmetic.lean](Foundation/Constructions/ElGamal/PrimeOrderArithmetic.lean) は、生の三数入力に対する乗算・累乗結果が具体的な群の積・累乗の符号化と一致することを証明します。[FramedArithmeticPrefix.lean](Foundation/Crypto/Semantics/Machine/FramedArithmeticPrefix.lean) は security parameter と instance frame の読み飛ばしを一つの有限コードとして接続し、全入力停止と有効な入力でのヘッド位置を証明します。[PrimeOrderChooseValidation.lean](Foundation/Constructions/ElGamal/PrimeOrderChooseValidation.lean) で任意応答の正規化器も構成済みです。[PrimeOrderMachineSecurity.lean](Foundation/Constructions/ElGamal/PrimeOrderMachineSecurity.lean) の最終定理には具体的な乗算・正規化 witnesses を代入しており、外部実装引数 `M` / `N` / `T` は残っていません。これらの証明を与えても、DDH 困難性は安全性定理の前提として残ります。現在の class と機械モデルの制約を含む定理であり、任意の計算モデルとの同値性までは主張しません。

一方、[ConcreteSecurity.lean](Foundation/Constructions/ElGamal/ConcreteSecurity.lean) の
`secureINDCPA_of_secureDDH_all` は **計算量を制限しない全 adversary family** に対する DDH 安全性を仮定します。
これは分布に基づく安全性輸送を確認する一般補題です。通常の「効率的な攻撃者に対する DDH 困難性」の前提には置き換えられません。

[UnrestrictedDDH.lean](Foundation/Constructions/ElGamal/UnrestrictedDDH.lean) は、明示された有限一様 sampling と生成元の累乗の全単射を使い、指数を回復する数学的な識別器の優位性が `1 − 1/q` になることを証明します。
`not_secureDDH_all` は、この実験との sampling の一致と各 parameter で `q ≥ 2` を仮定すると、`all` class 上の安全性が成立しないことを示します。識別器に効率性は主張しません。
[UnrestrictedDDHExamples.lean](Foundation/Constructions/ElGamal/UnrestrictedDDHExamples.lean) では二要素の例の優位性 `1/2` と、従来の unrestricted 前提の否定を確認しています。

## 復号の正しさと秘匿性

[PKE.Correct](Foundation/Notions/PKE/Correctness.lean) は、鍵生成と暗号化の分布の support に現れるすべての鍵・暗号文が元のメッセージに復号されることを表します。
[Correctness.lean](Foundation/Constructions/ElGamal/Correctness.lean) の `groupDecrypt` は ElGamal の復号 `ζ / β^x` を定義し、
`concreteInstance_correct` がこの復号関数を使う方式の正しさを証明します。
必要な仮定は群構造、構成の `mul` と群乗算の一致、および共有鍵の指数交換則です。交換則は `FiniteAlgebra.power_mul` と scalar 乗算の可換性からも導けます。

[CorrectnessExamples.lean](Foundation/Constructions/ElGamal/CorrectnessExamples.lean) は、実際に復号できる二要素の例と、同じ方式について正しさ・機械 class 上の秘匿性輸送を併記する例を含みます。
二要素の群は検証用であり、DDH 困難性を持つ実用的な群ではありません。
従来の `ConcreteExamples.bitDecrypt` は常に失敗する等式 API の検証例として残しています。IND-CPA ゲームは復号を使わないため、優位性等式だけから復号の正しさは導けません。
ここで追加した数学的な復号関数には、有限機械コードや多項式実行時間の証明はまだありません。

### 参考文献

Victor Shoup, *Sequences of Games: A Tool for Taming Complexity in Security Proofs*, 2006-01-18 版、IACR ePrint 2004/332。
[論文 PDF](https://eprint.iacr.org/2004/332.pdf) の §1 は効率的な攻撃者と negligibility、§3.1 は公開鍵暗号の correctness、§3.2 は ElGamal の復号、§3.3 は計算量を制限した DDH 仮定と安全性証明を扱います。

[一回限りの制御での入力準備と正常応答](Foundation/Crypto/Semantics/Oracle/OneUsePreparation.lean) は、別々の物理テープからの入力準備、長さ確認後の利用済み状態への変更、任意の計算部品、応答の配送と再開を接続します。部品の入口が実際の準備済みバッファと一致する証明を要求します。鍵と要求がそれぞれ `w` ビット、部品の時間上界が `T` 段階、応答本文の上界が `B` ビットなら、入力準備開始から再開まで `12*w+T+11*B+27` 段階です。[任意長のパッド暗号への適用](Foundation/Examples/OneUsePreparation.lean) は、この区間の上界 `31*w+29` 段階と、暗号文・応答履歴・利用済み状態を含む復帰配置の分布を証明します。鍵生成、呼び出し元の要求送信、拒否経路との全実行の接続、全体の記憶量上界と論理への登録は引き続き未完了です。

[利用状態を保持する共通配送](Foundation/Crypto/Semantics/Oracle/OneUseDelivery.lean) は、正常応答と拒否応答の双方で使います。既に書かれた `L` ビットの応答テープから取り出し、呼び出し元へ配送・復帰する上界は `6*L+8` 段階です。[不正長の拒否](Foundation/Crypto/Semantics/Oracle/OneUseRejection.lean) は、実際の入力準備開始から拒否応答の配送・復帰まで `12*m+25` 段階を証明します。`m` は鍵と要求のビット長の小さい方です。鍵テープを復元し、未使用状態のまま再開します。残余時間は実際の呼び出し元を実行します。[拒否後の停止の具体例](Foundation/Examples/OneUseRejection.lean) は、この区間と停止命令を合わせて `12*m+26` 段階で証明します。要求送信と鍵生成はこの区間に含みません。

[有限コードによる私有領域の初期化](Foundation/Crypto/Semantics/Machine/PrivateInitialization.lean) は、任意の乱択計算部品が実際に書いた出力テープを私有領域へ移し、一セルずつヘッドを戻します。部品の時間上界が `T` 段階、生成する秘密データが最大 `B` ビットなら、先頭へ戻して準備する上界は `T+B+2` 段階です。[一回限りの利用制御への開始](Foundation/Crypto/Semantics/Oracle/OneUseInitialization.lean) は最後の移譲も数えて `T+B+3` 段階とし、元の攻撃者配置と未使用状態を保持します。復帰後の残余時間は実際の利用制御を実行します。[任意長の一様な鍵の例](Foundation/Examples/OneUseInitialization.lean) では、固定した有限コードで `w` ビットの鍵を生成し、初期化の上界 `6*w+5` 段階と、鍵の一様分布を持つ開始配置を証明します。鍵生成と各応答契約を合わせた全実行、安全性との接続、および全体の資源証拠の登録は引き続き未完了です。

[実際の要求送信と応答契約の接続](Foundation/Crypto/Semantics/Oracle/OneUseInvocation.lean) は、任意の呼び出し元コード、命令位置、問い合わせ先の状態と履歴を扱います。要求が `R` ビットなら、要求の捕捉・読み取り・移譲の上界 `2*R+4` 段階を応答処理の上界へ加えます。正常応答・不正長の拒否・使用済み状態での拒否へ同じ接続を使えます。任意長のパッド暗号の正常要求は、要求送信から呼び出し元の停止まで `33*w+34` 段階です。[鍵生成から停止までの実行](Foundation/Examples/OneUseExperiment.lean) は、一様な鍵の実際の生成、私有領域の初期化、要求送信、入力準備、暗号化、応答配送と停止を `39*w+39` 段階で証明します。実際の応答テープの分布は、成功の印を付けた一様な `w` ビットの分布です。この応答を読む任意の確率的観測者について完全秘匿性を証明します。この例の要求は開始配置で固定されています。適応的な攻撃者と繰り返しの要求を含む全安全性、全体の記憶量上界、および論理への登録は引き続き未完了です。

[使用済み状態での適応的な実行](Foundation/Crypto/Semantics/Oracle/SpentSource.lean) は、秘密鍵を持たない制御で、実際の一回限りの利用制御の以後の実行を再現します。呼び出し元コード、問い合わせ先の状態、乱択、物理テープ、応答履歴、および繰り返しの要求は任意です。任意の実行段数で分布が対応し、鍵を除いた状態の分布は秘密鍵と暗号化コードに依存しません。[正常応答からの継続](Foundation/Crypto/Semantics/Oracle/OneUseContinuation.lean) は、最初の応答までの実際の費用を引いた残余時間でこの制御を実行する等式を証明します。任意長のパッド暗号にも適用しました。[応答による分岐の例](Foundation/Examples/SpentSource.lean) は、受け取ったビットを読んで異なる命令位置から次の要求を送るコードを検証します。これは最初の正常応答以後の対応です。最初の要求を選ぶ攻撃者の実行、初期化からの全安全性、および全体の資源証拠の登録は引き続き未完了です。

[最初の要求を選ぶ呼び出し元の実行](Foundation/Crypto/Semantics/Oracle/SourcePrefix.lean) は、上界内に最初の要求または実際の終了へ到達する証明から、実機械の実行契約を構成します。到達した状態・履歴・実際の費用の分布は、秘密鍵と暗号化コードに依存しません。残余時間は実機械の実行へ戻します。後続処理の契約との合成と上界の加算、および実際の入力準備への一段階の移譲も証明しました。[乱択による任意長の要求選択](Foundation/Examples/SourcePrefix.lean) は、乱数命令で先頭ビットを選び、残りの任意のビット列と合わせた要求を送るコードを検証します。要求が `R` ビットなら選択・捕捉の上界は `2*R+4` 段階、入力準備への移譲まで含めると `2*R+5` 段階です。未使用状態での繰り返しの拒否と最初の受理、初期化からの全安全性、および全体の資源証拠の登録は引き続き未完了です。

[費用を保持した繰り返し契約](Foundation/Crypto/Semantics/ProcedureIteration.lean) は、各回の結果を次回の入力へ渡します。物理的な終了配置と次回の開始配置の一致を証明に要求します。一回の上界が一様に `B` 段階なら、`N` 回の上界は `N*B` 段階です。実際の費用は各回の費用の和で、上界に合わせた余分な実行は加えません。[実際の遷移への適用](Foundation/Crypto/Semantics/ProcedureSteps.lean) は、元の機械の結果分布と累積費用への一致を証明します。[初期化を含む要求回数](Foundation/Crypto/Semantics/Oracle/InitializationSteps.lean) は、呼び出し命令の発行回数が実行段数以下、正常な受理回数が一回以下であることを証明します。拒否される呼び出しも発行回数に含みます。証明用の計数を取り除くと元の実行分布に一致します。[実際の二回の拒否の例](Foundation/Examples/OneUseIteration.lean) でも、結果・費用・停止への一致を確認しました。これらは繰り返しを組み立てる共通部品です。未使用状態での拒否から最初の受理までの全安全性、記憶量を含む資源上界、および論理への登録は引き続き未完了です。

[局所的な資源増加からの上界](Foundation/Crypto/Semantics/ResourceGrowth.lean) は、任意の確率的な遷移と状態の大きさを扱います。一遷移での増加が高々 `K` なら、開始時の大きさ `S` から `T` 段階までの全ての途中状態は `S+T*K` 以下です。境界までの実行には予算でなく実際の費用を使います。[実テープの記憶量](Foundation/Crypto/Semantics/Machine/Storage.lean) は、入力・出力の両テープの保持セルを空白も含めて数え、一遷移の増加が高々一セルであることを証明します。任意の既存の機械実行契約に、途中状態のセル数上界を適用できます。[任意長の適用例](Foundation/Examples/NativeStorage.lean) は、`w` ビットの鍵生成で高々 `6*w+4` セル、準備済みの `w` ビットの排他的論理和で高々 `10*w+4` セルを保証します。これらはテープセルの上界で、コードや制御整数の符号化、外側の制御、攻撃者の履歴を含む全記憶量の上界は引き続き必要です。

[要求選択・送信中の保存データの上界](Foundation/Crypto/Semantics/Oracle/SourceStorage.lean) は、攻撃者の両テープ、要求送信時に保存するテープのコピー、一時ビット列、既存の履歴、および利用者が指定した問い合わせ先の状態の大きさを数えます。開始時の攻撃者のテープセル数が `M`、他の保存データの大きさが `S` なら、最初の問い合わせまでの `T` 段階の全ての途中状態は `S+2*M+2*T` 以下です。一回限りの利用制御の境界到達契約にも接続し、私有鍵のセル数と実際の到達費用を含めた上界を証明します。[乱択による要求選択への適用](Foundation/Examples/SourceStorage.lean) は任意長の要求と任意の末尾セルを保持します。これは保存するセルとビットの個数であり、プログラム・制御整数・リストのポインタの符号化を含むバイト数ではありません。正常・拒否の応答処理、履歴の追加、初期化を合わせた全体の上界と論理への登録は引き続き必要です。

[入力準備のビット値を消す解析](Foundation/Crypto/Semantics/Machine/PreparationShape.lean) は、空白とテープ位置を保ったまま、ビット値を全て偽に写します。準備・不正長の復元・拒否応答の書き込みの各遷移との一致を証明します。[拒否の実際の費用の独立性](Foundation/Crypto/Semantics/Oracle/RejectionTiming.lean) は、同じ長さで末尾の空白配置も同じ入力について、拒否後の公開配置と実際の費用の同時分布が鍵のビット値や暗号化コードに依存しないことを証明します。要求を送る実際の呼び出し命令も含みます。[任意長の鍵への適用](Foundation/Examples/RejectionTiming.lean) は、長さが一致しない任意の要求と任意の末尾セルを扱います。これは拒否の復帰時点の保証です。途中の私有作業バッファの一致、未使用状態での拒否の繰り返しから最初の正常受理までの安全性、全体の記憶量、論理への登録は引き続き必要です。

[停止条件付きの実行契約の繰り返し](Foundation/Crypto/Semantics/ProcedureStoppedIteration.lean) は、各回の結果から停止条件を判定し、境界到達後の費用をゼロにします。元の実行を停止命令へ置き換えるのではなく、未使用の時間で元の機械を再開する契約を保ちます。一回の上界が `B` 段階、繰り返し上限が `N` 回なら上界は `N*B` 段階です。[境界への到達可能性](Foundation/Crypto/Semantics/BoundaryReachability.lean) は、報告した費用ちょうどで実際に結果へ到達することと、境界外から到達する最後の遷移の存在を証明します。[最初の正常受理までの実行](Foundation/Crypto/Semantics/Oracle/FirstAcceptance.lean) は、実際の適応的な利用制御へ適用し、拒否の繰り返しもそのまま実行します。受理した結果には実際の受理遷移の証拠を与え、未受理のまま予算が尽きた結果は区別します。[任意長の検証例](Foundation/Examples/FirstAcceptance.lean) は、既存の正常・拒否の全実行へ適用します。境界への実行分解は成立しますが、拒否を繰り返す攻撃者に対する鍵の独立性と正常受理後の安全性の合成、初期化からの全安全性、全記憶量、論理への登録は引き続き未完了です。

[公開状態と費用を保存する繰り返し](Foundation/Crypto/Semantics/CostedIteration.lean) は、各回の公開状態と実際の費用の同時分布が共通の公開処理に一致するなら、結果に応じて次の処理を変える繰り返し全体でも、その一致を保つことを証明します。停止条件にも同じ公開状態から判定できる証明を要求します。元の実行契約の繰り返しへ接続し、費用は実際の費用の和です。[使用済み鍵の実制御への適用](Foundation/Crypto/Semantics/Oracle/SpentIteration.lean) は、私有鍵を実際の物理配置に保持したまま、任意の公開停止条件までの公開復帰配置と費用の同時分布が鍵と暗号化コードに依存しないことを証明します。未使用状態での拒否の繰り返しについて同じ局所条件を満たす実行契約を構成し、正常受理と接続する証明は引き続き必要です。

[鍵の事前分布を保持する繰り返し](Foundation/Crypto/Semantics/KeyedIteration.lean) は、任意の鍵分布について、各回の公開状態と実際の費用が共通の処理に一致するなら、繰り返し後の鍵・公開状態・累積費用の同時分布が、鍵の事前分布と公開結果の分布の積に一致することを証明します。公開停止条件と、開始時の公開状態が鍵に依存しないことも要求します。[不正長の実際の要求への適用](Foundation/Examples/RejectionKeyDistribution.lean) は、要求送信から拒否後の復帰までの公開状態と費用を観測しても、任意の鍵の事前分布が独立な成分として残ることを証明します。拒否が実際の私有鍵テープを保持し未使用で戻ることも確認します。鍵生成の費用を含む初期化との接続、要求選択・拒否・復帰を合成した各回の契約、正常受理後との安全性の統合、全記憶量と論理への登録は引き続き必要です。

[実行結果に応じた契約の選択](Foundation/Crypto/Semantics/ProcedureDispatch.lean) は、選択結果を入力として実行契約を選びます。合成時には実際の終了配置と次の開始配置の一致を要求します。[乱数による要求選択と拒否の接続](Foundation/Examples/SelectedRejection.lean) は、実際の乱数命令で任意長の要求の先頭ビットを選び、不正長の要求を送信して拒否後に同じ呼び出し元へ復帰する実行を証明します。鍵長を `w`、要求長を `R` とすると上界は `2*R+12*min(w,R)+30` 段階です。公開復帰配置と実際の費用の同時分布は、同じ長さの鍵の値と暗号化コードに依存しません。この例は一回の選択・拒否です。拒否の繰り返しと正常受理、初期化からの全安全性、全記憶量と論理への登録は引き続き未完了です。

[公開結果と費用を保つ合成](Foundation/Crypto/Semantics/ProcedurePublicComposition.lean) と [任意の要求選択からの拒否](Foundation/Crypto/Semantics/Oracle/SelectedRejection.lean) を追加しました。[適応的な拒否の実行契約](Foundation/Crypto/Semantics/Oracle/RejectionPlan.lean) は、要求選択の実行証明、拒否後と次回開始時の物理配置の一致、一様な時間上界を与えると、拒否の繰り返しを実機械の契約として構成します。各回の要求選択と実際の費用が共通の公開分布に一致するなら、任意の鍵の事前分布について、停止条件付き繰り返しの公開結果と累積費用の独立性を証明します。各鍵で暗号化コードが異なっても構いません。残余時間は元の機械へ戻します。[乱数選択例での再利用](Foundation/Examples/SelectedRejectionReuse.lean) も検証しました。正常受理との接続、鍵生成からの全安全性、全記憶量、論理への登録、第二方式への適用は未完了です。

[鍵を保持した前半・後半の安全性の合成](Foundation/Crypto/Semantics/KeyedContinuation.lean) は、前半の公開状態と費用の鍵からの独立性と、鍵で平均した後半の安全性から、合成後の公開状態・出力・累積費用の分布を導出します。[拒否の繰り返しへの接続](Foundation/Crypto/Semantics/Oracle/RejectionContinuation.lean) は、実際の未使用鍵と復帰配置から後続処理へ接続し、上界を加算します。[任意長の正常暗号化への適用](Foundation/Examples/OneUseAdaptiveSecrecy.lean) は、任意の呼び出し元コードと公開状態に応じた平文を扱います。物理的に接続する前半契約の公開分布が共通なら、二つの平文について応答と累積契約費用の分布が一致します。共通の時間上界を満たす時点で元の機械の応答を読む任意の確率的な観測者への安全性も証明します。正常処理は既存の `33*w+34` 段階の契約であり、最初の停止時刻の分布の新しい証明ではありません。拒否から正常要求へ進む具体的なプログラムの検証、鍵生成を含む統合、全記憶量、論理への登録、第二方式への適用は残ります。

[実際の単一セル命令列の契約](Foundation/Crypto/Semantics/Oracle/StraightLine.lean) と [任意長の要求の書き込み](Foundation/Crypto/Semantics/Oracle/PacketWriter.lean) を追加しました。書き込み・区切り・先頭への移動は `R` ビットについて `3*R+1` 段階です。[拒否後の正常要求の具体例](Foundation/Examples/RejectionThenRequest.lean) は、正の任意の鍵幅 `w` について、空要求の拒否後に実命令で正常な要求を書き込み、暗号化・停止まで接続します。全実行の上界は `36*w+64` 段階です。最初の受理の実際の遷移の証拠と、一様な鍵に対する最終応答の一様な暗号文分布も証明します。この例は一回の拒否で、要求ごとに有限の書き込み命令列を構成します。複数回の適応的な拒否、入力平文を読む固定コード、初期化からの統合、全記憶量、論理への登録、第二方式への適用は残ります。

[入力平文を読む固定コード](Foundation/Crypto/Semantics/Oracle/BalancedCopy.lean) は、19 命令の同じプログラムで任意長の入力をコピーして正常な呼び出し位置へ到達します。0 と 1 の分岐を同じ時間にそろえ、`R` ビットのコピー・先頭への復帰は `11*R+5` 段階です。[実際の拒否から暗号化への接続](Foundation/Examples/InputRejectionThenEncrypt.lean) は、正の任意の鍵幅 `w` について、空要求の拒否後に実際の入力平文を読み、正常暗号化へ接続します。前半の結果・費用の同時分布は鍵や平文のビット値に依存しません。同じ固定コードを使う二つの平文について、一様な鍵と共通の実行上界 `44*w+68` 段階で最終応答を読む任意の確率的な観測者への安全性を、共通の合成定理から証明しました。複数回の適応的な拒否、実際の鍵生成からの統合、全記憶量、論理への登録、第二方式への適用は残ります。

[初期化と後続処理の共通契約](Foundation/Crypto/Semantics/Oracle/InitializationContinuation.lean) は、生成した実際の鍵テープとの物理的な一致を要求し、鍵生成と後続処理の費用を加算します。鍵と生成時間の相関も保持します。[鍵生成からの全実行](Foundation/Examples/InputRejectionExperiment.lean) は、実際の乱数命令による鍵生成から、私有テープの移譲、空要求の拒否、固定コードによる入力平文の読み取り、正常暗号化・停止までを接続します。正の鍵幅 `w` について上界は `50*w+73` 段階です。最終応答の一様な暗号文分布と、任意の確率的な観測者への完全秘匿性を証明しました。鍵を外から一様に与える仮定は、この具体例では不要です。複数回の適応的な拒否、任意の攻撃者との初期化の統合、全記憶量、論理への登録、第二方式への適用は残ります。

[初期化を含む共通の安全性定理](Foundation/Crypto/Semantics/InitializedContinuation.lean) は、鍵と生成時間が相関する場合にも使えます。生成時間ごとの鍵分布による、後続処理の公開結果と費用の分布の一致から、初期化を含む公開結果と合計費用の一致を導きます。一般の実行契約では実際の出口と入口の一致を要求します。一様鍵、固定の生成時間、暗号化方式の種類は仮定しません。ただし、鍵と生成時間の同時分布を表す証明と、各生成時間についての後続処理の比較証明が必要です。この定理だけで具体的な攻撃者や全実行履歴の安全性が証明されるわけではありません。

[初期化の純粋な推論規則](Foundation/Crypto/Logic/Initialization/Syntax.lean) と [実行契約による解釈](Foundation/Crypto/Logic/Initialization/Interpretation.lean) を追加しました。構文には確率分布や機械を含めず、鍵・生成時間の分布と、生成時間ごとの後続処理の安全性を二つの前提として扱います。解釈は物理的な引き渡しと資源上界の証明を要求し、公開結果・合計費用の一致と、両実験の加算した上界を導きます。比較する二つの実行機械や結果型も異なって構いません。暗号化と認証を組み合わせる既存方式の [実際の認証鍵生成への適用](Foundation/Constructions/Symmetric/EncryptThenMAC/PrivacyInitializationProcedure.lean) も追加しました。これは初期化の再利用であり、第二方式の全実行の安全性を新たに完成したという意味ではありません。

[応答を読む拒否ループの具体例](Foundation/Examples/AdaptiveRejectionLoop.lean) は、幅や鍵に依存しない固定コードで、拒否応答を読む分岐、乱数命令による次の一ビット要求の選択、実際の拒否と応答配送を繰り返します。鍵幅 `w` は `w != 1` を満たす任意の幅です。最大 `N` 回の区間の上界は `N*(12*min(w,1)+34)` 段階です。任意の公開停止条件を扱い、公開履歴と累積実行費用の同時分布が鍵と拒否に使われない暗号化コードによらないことを証明します。初期配置には失敗を表すビットを置き、二回目以降の分岐は実際に配送された拒否応答を読みます。有限区間の終了は機械の停止ではありません。実際の鍵生成との接続は次の具体例で扱います。正常問い合わせへの接続は残ります。

[鍵生成と複数回の拒否の接続](Foundation/Examples/AdaptiveRejectionInitialization.lean) は、実際の乱数命令による鍵生成、私有テープの移譲、固定コードによる拒否ループを共通契約で接続します。鍵幅 `w != 1`、最大 `N` 回について、上界は `6*w+5+N*(12*min(w,1)+34)` 段階です。生成した鍵と公開結果の分布が独立であることを証明します。この独立性の主張では費用を観測しません。合計費用の解析では初期化の実際の時間分布を保持し、拒否区間の公開結果・費用の分布と合成します。正常問い合わせへ進む具体的な呼び出し元との接続は残ります。

[呼び出し元コードの配置変更](Foundation/Crypto/Semantics/Oracle/CodeRelocation.lean) は、既存の対話コードを別の命令列の後ろへ配置し、分岐先とジャンプ先を一括してずらします。元のコードの全実行分布と、費用・上界を含む実行契約を再利用できます。テープ、応答、公開履歴、外部状態を保持し、保持データの大きさも変わりません。先行する命令列の実行やブロックへ入るジャンプの費用を無償にする規則ではありません。私有鍵を処理する外側の制御機械への適用は次の規則で扱います。複数回の拒否から正常暗号化へ進む具体例の接続は残ります。

[私有鍵を扱う機械への配置変更](Foundation/Crypto/Semantics/Oracle/OneUseCodeRelocation.lean) は、要求検査、拒否、正常暗号化、応答の配送、呼び出し元の復帰を含めて実行分布と費用を保存します。暗号化部品の内部の命令番地は変更せず、呼び出し元の番地だけをずらします。[既存の正常暗号化の証明への適用](Foundation/Examples/RelocatedInputRejection.lean) で、一回の拒否と入力平文の読み取りの後に暗号化・停止するブロックを任意の位置へ配置し、時間上界と最終暗号文の安全性証明を再利用しました。先行命令列を実行してこのブロックへ入る引き渡し、および複数回の拒否からの接続は残ります。

[処理済み入力を保持するコピー](Foundation/Crypto/Semantics/Oracle/BalancedCopyFramed.lean) は、入力の左側に残ったデータを消さず、実際の空白区切りで巻き戻しを止めます。従来と同じ `11*w+5` 段階で平文をコピーできます。[印を数える固定呼び出し元](Foundation/Crypto/Semantics/Oracle/CountedCaller.lean) は、拒否応答を読んで次の要求を選び、拒否後の二命令で入力の印を一つ消費します。印の終了地点からは三命令でコピー部へ進みます。[正常処理の安全性](Foundation/Examples/CountedCallerNormal.lean) は、この終了地点から正常暗号化・停止までを、任意の処理済み入力について上界 `44*w+42` 段階で証明します。複数回の拒否契約をこの新しい呼び出し元で合成し、印の終了地点へ到達する全実行の証明は残ります。


複数回の拒否から正常問い合わせ位置への接続も追加しました。`Oracle/CountedRejection.lean` は実際の要求選択、拒否、印の消費を一回の契約へ合成します。`Oracle/CountedRejectionIteration.lean` は任意の有限回数について、未処理の印の数、入力データと外部状態の保存、未使用の私有鍵を保持した物理的な出口を証明します。各回で保存する任意の観測値についても保存則を再利用できます。`prepare` は印の数だけ拒否した後に入力をコピーし、同じ固定コードの正常問い合わせ命令へ到達します。鍵幅を `w != 1`、印の数を `N`、入力長を `L` とすると、上界は `N*(12*min(w,1)+36)+11*L+8` 段階です。実際の累積費用と結果の分布は私有鍵と暗号化部品のコードによらず、契約の終了後は残り時間だけ元の機械を実行します。入力を含む論理値全体について平文秘匿性を主張する定理ではありません。この複数回の区間から正常暗号化の安全性への接続、実際の鍵生成との統合、全記憶量と全バックエンドへの登録は引き続き残ります。


複数回の拒否を含む正常暗号化と初期化の接続を追加しました。`CountedRejection.publicCost_payload` と `CountedRejectionIteration.execution_public_cost` は、入力平文を観測から除くと、拒否履歴と実際の累積費用の同時分布が平文の内容によらないことを証明します。`prepare_public_cost` は固定コードによる入力読み取りの費用も含みます。`Examples/CountedRejectionThenEncrypt.lean` は任意の有限の印の列について正常暗号化・停止へ接続し、共通の時間上界で最終暗号文を読む任意の確率的な観測者への完全秘匿性を証明します。鍵幅 `w` は正で一以外です。印の数を `N` とすると上界は `N*(12*min(w,1)+36)+44*w+42` 段階です。`Examples/CountedRejectionExperiment.lean` は実際の乱数命令による鍵生成と私有テープの移譲も同じ実行機械へ接続します。全実行の上界は `N*(12*min(w,1)+36)+50*w+47` 段階です。最終応答は成功印と一様な `w` ビット列の分布に一致し、平文によらないことを証明します。これは最終暗号文の観測に対する主張です。全私有テープや全入力の秘匿性、初期化を含む履歴・費用の同時観測への安全性を主張していません。全記憶量の上界、第二方式の全実行での再利用、帰着プログラム抽出の全バックエンドへの登録は引き続き残ります。


記憶量の証明を制御部品にも一般化しました。`Machine/ControllerStorage.lean` は、要求の二つのテープと作業用テープ、読み取って保持する一時ビット、拒否後の復元、応答の書き込み、暗号文の取り出し、実際の鍵生成と巻き戻しについて、保存したテープセルと一時リストを数えます。各段階の増加量を証明し、任意の実行途中の上界を導きます。暗号文の取り出しでは初期量に実行時間の二倍、要求検査と初期化では初期量に実行時間を加えた上界です。早期に到達する境界では宣言した予算ではなく実際の経過時間を使います。`FramingStorage.lean` は、任意の保存データを保持する実行について、そのデータの大きさを加えて部品の上界を再利用します。

`Oracle/ControllerStorage.lean` は、私有鍵を扱う外側の制御機械の全保持データを数える共通尺度を定義します。保存した呼び出し元、私有テープ、要求、外部状態、履歴、応答配送の状態が重複して保持される場合は各コピーを別々に数えます。要求検査、暗号化・取り出し、鍵生成の部品区間の上界には保存データの量も含めます。`ControllerStorageRelocation.lean` はコードの番地変更がこの尺度を保存し、元の実行途中の上界を配置後の機械へ移送できることを証明します。ここで数えるのはモデルが保持するセル、ビット、一時リスト、利用側が与える外部状態の大きさです。有限コード、制御タグ、整数番地の符号化、ホスト環境の実メモリ使用量は別の資源です。外側の保存・配送による複製遷移を含む全実行の最大記憶量の上界、第二方式の全実行での再利用、帰着プログラム抽出の全バックエンドへの登録は引き続き残ります。


保存・配送の複製を含む保持量の増加則を追加しました。`Oracle/SourceAllocation.lean` は要求テープのコピーを計上し、外部問い合わせでは状態の増加量と応答長の上界を明示的な前提にします。`CallbackAllocation.lean` は復帰時に作る呼び出し元、状態、履歴、要求、応答のコピーを計上します。`CheckedAllocation.lean` と `OneUseAllocation.lean` は検査、拒否、暗号化、タグの書き込み、配送、復帰を含む全遷移の増加量を証明します。`InitializationAllocation.lean` は実際の鍵生成と私有テープの移譲も接続します。これらの局所証明は任意のネイティブコードと任意の幅に再利用できます。

`Semantics/AllocationCounter.lean` は各遷移の明示的な増加量の上界を解析用に累積します。元の状態へ射影した実行分布は元の機械と一致します。任意の元の実行途中の状態には、その同じ実行経路から得られる累積量の証拠があり、保持量は初期量と累積量の和以下です。この累積量は解析用の上界であり、実測した割当量や実行命令数ではありません。`OneUseAllocation.peak` と `InitializationAllocation.peak` は、保存・配送のコピー量を `C` 以下に保つ不変条件から、全実行の任意の時点について初期量に `H*(C+2)` を加えた上界を導きます。`H` は実行時間の上界です。外部問い合わせには外部状態の増加量と応答長の契約も必要です。具体的な複数回の拒否・暗号化の実行でコピー量の不変条件を証明して幅・回数だけの多項式上界を確定する作業は残ります。第二方式の全実行での再利用、帰着プログラム抽出の全バックエンドへの登録も引き続き残ります。


全実行の保持データについて多項式上界を導きました。`Machine/ControllerExtent.lean` は、実際のテープと一時リストの最大長を追跡します。コピーはこの長さを増やさず、元の命令と各制御部品の一段階の遷移は最大長を一以下しか増やしません。`Oracle/ControllerExtent.lean` は、外部状態の大きさ、履歴の長さ、履歴中の要求と応答の最大長も含む尺度 `E` を定義します。重複を含む全保持量は `4*E^2+11*E+2` 以下です。`ControllerExtentExecution.lean` は私有鍵を扱う機械の全遷移と鍵生成の接続を証明し、実行途中の最大長を初期値と時間上界から導きます。一般の外部問い合わせには外部状態の一回の増加量 `S` と応答長上界 `R` を要求します。時間上界 `H` の任意の時点で、最大長は初期値に `H*(S+R+2)` を加えた値以下です。保存・配送のコピー量の不変条件を別に仮定する必要はありません。

`Examples/CountedRejectionStorage.lean` は、実際の鍵生成から複数回の拒否、正常暗号化、応答配送、停止までの固定コードへ一般定理を適用します。外部状態は単一の値だけを持つ型であり、初期履歴と処理済みの印は空です。外部問い合わせは空の応答を返します。正の鍵幅 `w` と印の数 `N` について、全実行の任意の時点の保持量は `4*(97*N+101*w+98)^2+11*(97*N+101*w+98)+2` 以下です。これは一時データと保存した各コピーを含むモデル内のセル・保持ビット・リストの上界です。有限コード、制御タグ、整数番地の符号化、ホスト環境の実メモリ使用量を含む上界ではありません。一般定理は初期の外部状態や履歴がある場合もその大きさを数えて扱います。第二方式の全実行での再利用と、帰着プログラム抽出の全バックエンドへの登録は引き続き残ります。


暗号化後に認証タグを付ける方式にも、共通の初期化・後続処理の規則を適用しました。`EncryptThenMAC/PrivacySourceProcedure.lean` は実際の認証鍵生成、任意の有限コードの問い合わせ、タグ生成、応答配送、停止を一つの実行契約へ接続します。`PrivacyContractSecurity.lean` は既存の一ビット暗号の完全秘匿性をこの契約へ移送します。`PrivacyContractBackend.lean` は既存の有限コードのコンパイラと停止・資源証明に接続し、帰着先の識別結果と費用の分布が一致することを証明します。暗号鍵は外部の暗号化ゲームが標本化します。認証鍵は制御機械が実際に生成します。認証タグの幅は任意ですが、暗号文は既存方式の一ビットです。

`IntegrityInitializationProcedure.lean` と `IntegritySourceProcedure.lean` は、改ざんに対する安全性の制御機械にも同じ規則を適用します。実際の暗号鍵生成の費用は3段階です。後続処理は任意の有限コードと、指定した長さのタグを返す認証問い合わせを扱います。任意の観測関数について実際の全実行との一致を証明し、後続処理の観測分布の比較を全実行へ移送できます。`IntegrityContractBackend.lean` は既存の停止証明を再利用し、偽造候補と実際の認証履歴を含む帰着先の分布に接続します。この側では認証鍵を外部の認証ゲームが標本化します。

両側の費用は停止後の余り時間も含めた共通の実行上界です。停止に初めて到達する時刻の分布が秘密によらないという主張ではありません。プライバシー側の上界はタグ幅 `w` と元の実行段階数 `c` に対して `12*w+5+c*(29*w+39)` 段階、改ざん側は `3+c*(5*w+36)` 段階です。停止の証拠と外部応答の長さの証拠は明示的に要求します。コンパイル結果は従来の有限命令列を保持し、証明用の実行木を実行コードに含めません。第二方式の保持データ全体の上界、および他の帰着方式への適用は引き続き残ります。


保持データの資源解析も共通化しました。`Semantics/ResourceEnvelope.lean` は、任意の確率的実行機械について、各段階で増える尺度、全保持量を覆う単調な関数、尺度の増加量を一つの契約にまとめます。契約から実行途中の全保持量の上界を導きます。早い境界では実際の経過段階数を使います。単調な単位変換にも対応します。`Oracle/ControllerResourceEnvelope.lean` は既存の私有鍵制御機械をこの契約に接続し、実際の境界到達時の保持量を証明します。`Oracle/SourceActionExtent.lean` は、外側の機械が問い合わせを別に処理する場合にも、元の対話機械の決定的・乱数遷移の証明を再利用する規則です。

`EncryptThenMAC/IntegrityStorage.lean` は、改ざん側の機械の全テープ、私有ビット、一時リスト、元の問い合わせ履歴、実際の認証履歴を数えます。同時に保持するコピーは別々に数えます。尺度 `E` に対して全保持量は `4*E^2+7*E+2` 以下です。`IntegrityStorageExecution.lean` は、実際の鍵生成、暗号化、認証、失敗応答、書き込み、巻き戻し、収集、反転、呼び出し元への配送を含む全遷移の増加量を証明します。外部状態の一回の増加量を `S`、タグ長の上界を `R` とすると、尺度の一段階の増加量は `S+R+2` 以下です。任意の初期状態と任意の有限コードに使えます。

`IntegrityStorageBackend.lean` は既存の有限コードの帰着先へ全実行途中の上界を適用します。タグ幅 `w`、初期入力長 `L`、元の実行段階数 `c`、時間上界 `H=3+c*(5*w+36)` に対し、尺度の上界は `L+1+H*(w+2)` です。その値を `4*E^2+7*E+2` へ代入した保持量上界を証明します。初期入力長が多項式であるという追加の前提から、既存の証明付き帰着の幅・時間証明を使って保持量の多項式上界も導きます。時間上界だけから初期入力長の上界を推測しません。この尺度も有限コード、制御タグ、整数番地の符号化、ホスト環境の割当量を数えるものではありません。プライバシー側の機械の保持量への適用と、他の帰着方式への適用は引き続き残ります。


プライバシー側の全保持量も共通の資源契約へ接続しました。`EncryptThenMAC/PrivacyStorage.lean` は、実際の認証鍵生成、保持した鍵、認証に使う入力テープ、保存した呼び出し元、一時応答、元の問い合わせ履歴、外部の暗号化問い合わせ履歴を数えます。複数の場所に保持するコピーは別々に数えます。尺度 `E` に対して、全保持量は `4*E^2+7*E+2` 以下です。`PrivacyStorageExecution.lean` は、鍵生成・巻き戻し、ヘッダ作成、鍵コピー、認証タグ生成、応答の収集・反転、配送、履歴更新を含む全遷移の尺度の増加量を証明します。各遷移は既存の命令列で実行し、解析用の尺度を実行機械へ追加していません。一般の外部問い合わせでは、外部状態の一回の増加量 `S` と応答長上界 `R` を明示的に要求し、尺度の増加量を `S+R+2` 以下に抑えます。

`PrivacyStorageBackend.lean` は既存の証明付き帰着プログラムにこの上界を適用します。タグ幅 `w`、初期入力長 `L`、元の実行段階数 `c`、時間上界 `H=12*w+5+c*(29*w+39)` に対し、尺度の上界は `2*w+L+1+4*H` です。外部の一ビット暗号化問い合わせの応答長が高々2ビットであることを実際の定義から証明しています。外部状態は使用済みかどうかを保持する1ビットであり、その量も保持量に含めます。初期入力長が多項式なら、既存の帰着証明が持つ幅・段階数の証拠から、全実行途中の保持量の多項式上界が得られます。任意の初期入力長を実行時間だけから抑えるとは主張しません。

この結果により、暗号化後に認証タグを付ける方式のプライバシー側と改ざん側の両方で、同じ初期化規則と同じ資源契約を再利用できます。各証明は有限コードと停止の証拠に接続します。記憶量の対象はモデル内のセル・保持ビット・リスト・利用者が指定する外部状態の大きさです。有限コード、制御タグ、整数番地の符号化、実機の割当量は別の資源です。任意長の暗号文を扱う方式への全帰着機械の接続と、他の帰着方式への適用は引き続き残ります。


実行機械の状態表現を変える場合の資源証明も共通化しました。`Semantics/ResourceSimulation.lean` は、一段階の確率分布が状態の対応で一致することと、対応先の保持量の増加を評価する単調な関数を明示的に要求します。元の資源契約から、対応先の全実行途中の保持量上界を導きます。対応先の任意の状態への上界や、観測の一致だけからの記憶量上界は主張しません。対応する入口から到達する状態が対象です。早期の境界に対する規則では、境界までの実行の一致だけを要求し、実際の経過段階数を使います。既存の `Procedure.transport` と接続した `transport_resource` は、同じ実際の入口、費用分布、時間上界を持つ契約へ保持量の保証を移送します。

`Semantics/FramingResourceEnvelope.lean` は、任意の単調な保持量上界を、呼び出し元の保存データを保持した実行に再利用します。以前の線形増加則に限定せず、今回の二次式の上界も扱います。保存したデータの大きさは入口の尺度と全保持量に加えます。保存用の配置を作ることやコピーすることを費用ゼロとは扱いません。`Examples/EncryptThenMACFramedStorage.lean` は、暗号化後に認証タグを付ける方式のプライバシー側と改ざん側の実行機械に同じ規則を適用し、保存データの維持と実行途中の保持量を証明します。

`Oracle/ControllerResourceSimulation.lean` は、私有鍵を持つ制御機械の全保持量を共通の資源契約にまとめ、実際のコード配置変更へ資源移送の規則を適用します。呼び出し元の命令番地をずらしても、私有鍵、要求、応答、保存した呼び出し元、履歴を含む保持量の上界を再利用できます。先行命令列の後ろへ配置したコードの入口から実行する定理です。先行命令列そのものの実行や配置の準備は、別の契約で計上する必要があります。整数番地の符号化の長さや実機の割当量は依然として別の資源です。任意長の暗号文を扱う方式の全帰着機械と、他の帰着方式への登録は引き続き残ります。


任意長のワンタイムパッドの問い合わせ証明を、具体例から再利用するライブラリへ移しました。`Oracle/OneUseXorResponse.lean`、`OneUseXorInvocation.lean`、`OneUseBitInitialization.lean` は、既存の有限命令列、応答配送、実際の呼び出し元の停止、私有鍵生成の証明を保持します。元の具体例の名前は互換参照として残しました。`Semantics/ProcedurePhysical.lean` は、異なる結果型の部品を全物理状態という共通の出力型にまとめます。物理的な出口と費用の同時分布を保持し、私有データを消して型を合わせる操作ではありません。

`EncryptThenMAC/OneUsePadInvocation.lean` は、任意幅の鍵・平文・暗号文を持つ既存の `OneUsePad.scheme` と、実際の問い合わせ処理を接続します。未使用の鍵なら成功ビットと暗号文を返し、使用済みなら失敗応答を返します。どちらも鍵を使用済みとして返します。幅0も含む同じ定理です。実際の呼び出し命令、要求テープの配置、未停止の呼び出し元を明示的に要求します。元の有限コードは問い合わせ後も実行を継続し、余り時間を別の仮想機械へ移しません。幅 `w` に対して、未使用の問い合わせの上界は `33*w+33` 段階、使用済みの問い合わせは `2*w+22` 段階です。共通の資源解析により、前処理、暗号化、配送の途中の保持量も評価します。

`OneUsePadInitializedInvocation.lean` は、この型付きの問い合わせへ実際の私有鍵生成を共通の初期化・後続処理の規則で接続します。鍵生成から問い合わせの戻りまでの上界は `39*w+38` 段階です。論理的な戻りの分布は一様な鍵と、それを使った方式の暗号文を保持します。実際の費用分布と残り時間の実行も契約に保持します。全実行途中の記憶量には、元から保持している呼び出し元のテープと履歴も含めます。入口は平文の要求テープをすでに持つ実際の問い合わせ命令です。そのテープを作る処理はこの契約より前で計上する必要があります。戻りの分布を、任意の呼び出し元に対して固定時間で観測した最終状態の分布と同一視しません。任意の適応的な有限コード全体の停止・分布証明を生成する帰着先への登録は引き続き残ります。

私有鍵を扱う制御機械について、有限コードと実行状態全体のビット列の長さも評価しました。[PrivateEncodedStorage.lean](Foundation/Crypto/Semantics/Oracle/PrivateEncodedStorage.lean) は、鍵生成コード、暗号処理コード、呼び出し元コード、および全実行途中の状態を復号可能な表現にします。状態には私有鍵、保存した呼び出し元、要求、応答、履歴、各制御段階の一時データを含めます。命令番地の増加は実際の遷移から導きます。利用側には外部状態の符号化とその長さ上界、外部問い合わせによる状態の増加量と応答長の上界を要求します。初期番地、初期データ量、時間、状態増加量、応答長が多項式で抑えられるなら、固定した三つの有限コードを含む全表現の長さも多項式で抑えられます。[OneUseAdaptiveEchoEncoding.lean](Foundation/Examples/OneUseAdaptiveEchoEncoding.lean) は、この定理を任意長の鍵による正常応答・再問い合わせの拒否・停止と実際の鍵生成へ適用します。

[OneUseEncodedObservedBackend.lean](Foundation/Crypto/Logic/General/OneUseEncodedObservedBackend.lean) は、この長さの保証を安全性の共通インターフェースへ登録します。登録された証明から、全実行途中の長さ上界と、その多項式性を取り出せます。既存の時間・保持量の証明には `attachEncoding` で追加できます。`forgetEncoding` で保持量の証明へ戻したときも、元の有限コードと資源設定が保存されます。`secure_of_logical` は、同じ論理的実験の安全性から実際の機械を観測するクラスの安全性を導きます。暗号処理には任意の有限コードを渡せます。[OneUseAdaptiveEchoResources.lean](Foundation/Examples/OneUseAdaptiveEchoResources.lean) は任意長の具体例の登録に必要な符号化の証明を提供します。

このビット列の長さは状態表現の上界です。符号化・復号を実行する別の機械の時間や、ホスト環境の割当量を証明したものではありません。安全性の観測関数は既存の実行契約が指定するものを保持します。全私有状態を観測者へ公開しても安全であるという主張ではありません。別方式の制御機械への同じ表現保証の適用と、呼び出し元の問い合わせをより細かく数える実行との比較は引き続き残ります。

暗号化後に認証タグを付ける方式の秘匿性側にも、有限コードと状態表現全体のビット数の保証を接続しました。[PrivacyEncoding.lean](Foundation/Constructions/Symmetric/EncryptThenMAC/PrivacyEncoding.lean) は、私有認証鍵、保存した呼び出し元、認証専用の入力、応答を収集する一時状態、および元の問い合わせ履歴と外部の暗号化問い合わせ履歴を復号可能な表現にします。[PrivacyAddresses.lean](Foundation/Constructions/Symmetric/EncryptThenMAC/PrivacyAddresses.lean) は、実際の鍵生成、鍵コピー、認証処理、応答配送、呼び出し元の再開における命令番地の増加を証明します。呼び出し元の決定的・乱数・問い合わせの各動作には、方式に依存しない [SourceActionAddresses.lean](Foundation/Crypto/Semantics/Oracle/SourceActionAddresses.lean) の規則を再利用します。

[PrivacyEncodedStorage.lean](Foundation/Constructions/Symmetric/EncryptThenMAC/PrivacyEncodedStorage.lean) は、三つの固定ネイティブコードと呼び出し元の有限コードも表現に含め、実際の全実行途中の上界を導きます。[PrivacyEncodedBackend.lean](Foundation/Constructions/Symmetric/EncryptThenMAC/PrivacyEncodedBackend.lean) は、既存の安全性の証明付きコンパイラが出力するコードへこの定理を適用します。タグ幅を `w`、初期入力長を `L`、元の実行段階数を `c` とすると、時間上界は既存の `H=12*w+5+c*(29*w+39)` をそのまま使います。データ尺度の上界は `e=2*w+L+1+4*H` です。固定コードから求める番地増加係数を `J`、コードを表現するビット数を `K` とすると、表現全体の上界は `K+32*H*J+144*(4*e^2+7*e+2)+16*e+330` ビットです。初期入力長が多項式で抑えられるなら、元の証明が持つ幅と段階数の多項式性から、この上界の多項式性も導きます。

表現の再利用には `FiniteBitEncoding.retract` を追加しました。既存の表現へ変換する関数と、それを元へ戻す関数が往復で元の値を保存すれば、復号可能な表現とその長さの式を再利用できます。今回の私有鍵生成の状態はこの規則で既存の初期化の表現へ接続します。認証付き暗号のこの実行機械ではタグ幅は任意ですが、暗号文は既存の一ビット方式です。外部の暗号化ゲームが保持する暗号鍵は帰着機械の状態には含めません。任意長の暗号文を扱う全帰着機械と、表現の符号化・復号を実行する機械の時間保証は引き続き残ります。

認証付き暗号の改ざん側も、有限コードと状態全体の表現サイズへ接続しました。[IntegrityEncoding.lean](Foundation/Constructions/Symmetric/EncryptThenMAC/IntegrityEncoding.lean) は、私有の暗号鍵、使用済みの印、保存した呼び出し元、認証タグ、一時応答、元の問い合わせ履歴と実際の認証履歴を保持する復号可能な表現です。要求を準備する処理段階とヘッダを書く処理段階は自然数として保持されるため、その値も表現と上界に含めます。これらの段階数は従来のセル・リストの保持量には含まれていません。[IntegrityAddresses.lean](Foundation/Constructions/Symmetric/EncryptThenMAC/IntegrityAddresses.lean) は、命令番地と処理段階の最大値の増加を実際の全遷移から導きます。任意の初期状態に適用する定理では、初期の数値も明示的に数えます。

[IntegrityEncodedStorage.lean](Foundation/Constructions/Symmetric/EncryptThenMAC/IntegrityEncodedStorage.lean) は共通の資源増加の定理と保持量の証明を使い、二つの固定ネイティブコードと有限呼び出し元コードを含む上界を導きます。[IntegrityEncodedBackend.lean](Foundation/Constructions/Symmetric/EncryptThenMAC/IntegrityEncodedBackend.lean) は、既存の安全性の証明付きコンパイラが出力するコードへ適用します。タグ幅を `w`、初期入力長を `L`、元の実行段階数を `c` とすると、時間上界は既存の `H=3+c*(5*w+36)` です。データ尺度の上界は `e=L+1+H*(w+2)` です。固定コードから求める数値の増加係数を `J`、コードを表現するビット数を `K` とすると、全表現の上界は `K+32*H*J+144*(4*e^2+7*e+2)+16*e+522` ビットです。初期入力長の多項式性を追加条件として、既存の幅と実行段階数の証明からこの上界の多項式性も導きます。外部の認証ゲームが保持する認証鍵は帰着機械の状態には含みません。

これにより、秘匿性側と改ざん側の両方で、同じ復号可能な表現の組み合わせ、呼び出し元の番地解析、全実行途中の資源増加の規則を再利用できます。タグ幅は任意ですが、両方の制御機械が使用する暗号文は既存の一ビット方式です。符号化・復号を実行する別の機械の時間、実機の割当量、任意長の暗号文を持つ全帰着機械の証明は別途必要です。

資源保証を安全性の対象へ追加する操作も、方式ごとの定義から共通規則へ移しました。[ExecutionRefinement.lean](Foundation/Crypto/Logic/General/ExecutionRefinement.lean) の `SecurityObject.refine` は、元のプログラムのクラスへ追加の証明条件を付けます。条件は対象のインスタンス族、有限コード、資源設定について述べます。元の実行条件、実験との一致、元のクラスへの所属をすべて保持します。`attach` と `forget` は追加条件の証明を付け外しし、往復で元の証明付きコードを保存します。二つの条件を一度に追加しても、順に追加しても、同じプログラムのクラスになります。

共通の `CertifiedTransform.refine`、`CertifiedReduction.refine`、`CertifiedBinaryReduction.refine` は、既存の変換が出力する正確なコードと資源設定について追加条件を証明したとき、条件付きの対象間へ帰着を移します。元のコンパイラ、実験との一致、帰着の損失を保持します。二分岐の帰着では各帰着先に異なる条件を付けられます。追加条件は証明の情報であり、実行コードに含めません。

[PrivacyEncodedSecurity.lean](Foundation/Constructions/Symmetric/EncryptThenMAC/PrivacyEncodedSecurity.lean) と [IntegrityEncodedSecurity.lean](Foundation/Constructions/Symmetric/EncryptThenMAC/IntegrityEncodedSecurity.lean) は、この規則を実際の帰着へ適用します。帰着元には初期入力長の多項式性を要求します。帰着先の追加条件は、有限コードと全実行途中の状態表現を覆う多項式のビット数上界が存在することです。その条件を持つ帰着先のプログラムのクラスに対する安全性から、入力長の条件を持つ帰着元の安全性を導きます。具体的な誤差上界についても、既存の `ResourceSecurity` の定理を使って同じ損失で移します。すべての元のプログラムについて初期入力長の多項式性を自動で主張するものではありません。

[ConcreteEncodedSecurity.lean](Foundation/Constructions/Symmetric/EncryptThenMAC/ConcreteEncodedSecurity.lean) は認証付き暗号の二つの仮定を使う帰着にも適用します。暗号化側と認証側はそれぞれの実行時間と状態表現の上界を保持し、帰着元には両方の初期入力長の多項式性を要求します。各帰着先の誤差上界を `epsilon(n)` と `delta(n)` とすると、帰着元の上界は既存の `epsilon(n)+delta(n)` のままです。[EncryptThenMACEncodedClasses.lean](Foundation/Examples/EncryptThenMACEncodedClasses.lean) は、既存の有限停止コードと実際の私有鍵初期化の証明から、追加条件付きの帰着元と両帰着先の証明を構成します。追加条件が不可能でクラスが空になるためだけに安全性を得ているわけではありません。これらの適用例の暗号文は引き続き一ビットであり、任意長の暗号文を持つ全帰着機械の実行証明は別途必要です。

任意長の暗号文を扱うため、応答の準備と認証処理を有限コードの契約から合成する部品を追加しました。[ResponseHandoffProgram.lean](Foundation/Constructions/Symmetric/EncryptThenMAC/ResponseHandoffProgram.lean) は、任意の長さの応答をセルごとに書き、私有鍵を既存の有限コードでコピーし、応答と鍵を含む私有入力を巻き戻して、任意の有限処理コードへ渡します。従来の一ビット用の認証コードを渡した場合、一段階の遷移は元の機械と一致します。応答が `L` ビット、鍵が `K` ビットなら準備の上界は `9*K+3*L+8` 段階です。コピーの費用分布には実際の停止時間を使い、余った時間の制御移譲も契約に保持します。

後続処理には、私有入力 `payload ++ key` の実際のテープ配置から実行する証明を要求します。元の鍵は後続処理専用の入力と別のテープで保持します。`complete` はその準備と後続処理の契約を同じ実行機械で合成し、上界に後続処理の予算を加えます。結果分布と実際の費用分布を保持します。`complete_run` は後続処理の出口が停止状態であるという証明から、十分な時間での実際の最終状態の分布を導きます。応答内容の長さを一ビットには限定しません。

[ResponseHandoffProgramResources.lean](Foundation/Constructions/Symmetric/EncryptThenMAC/ResponseHandoffProgramResources.lean) は、この部品の全実行途中について保持量と命令番地の増加を証明します。初期保持量を `C`、初期番地を `A`、時間上界を `H` とすると、保持量は `C+H` 以下です。固定されたコピーコードと後続処理コードから求める番地増加係数を `J` とすると、番地は `A+H*J` 以下です。二つの有限コードを表現する長さを `B` とすると、コードと制御状態全体の表現は `B+2*(A+H*J)+18*(C+H)+32` ビット以下です。初期量と時間が多項式で抑えられるなら、この上界も多項式で抑えられます。

この合成契約の入口は、鍵を `Tape.ofBits key` の配置で保持し、応答のリストをすでに持つ状態です。鍵生成と暗号化問い合わせは入口より前の契約で数える必要があります。後続処理が認証を正しく行うことは、その有限コードの実行契約と型付きの方式の意味との一致から別途証明します。再問い合わせ時の実際の鍵テープ配置、元の呼び出し元全体への配送、および任意長の方式の安全性の帰着への登録は続けて接続する必要があります。今回の任意長の部品だけから方式全体の安全性を主張しません。

複数回の要求を扱う実行にも、全実行途中の保持量と有限コードを含むビット数の上界を追加しました。[ReusableResponseEncoded.lean](Foundation/Constructions/Symmetric/EncryptThenMAC/ReusableResponseEncoded.lean) は、任意の有限処理コード、呼び出し元、鍵、要求、履歴を扱います。[ReusableResponseTwoQueriesResources.lean](Foundation/Examples/ReusableResponseTwoQueriesResources.lean) は、実際の二回問い合わせの全実行途中に適用します。方式全体の安全性と小さい論理への登録は別途必要です。

[ReusableCertifiedSource.lean](Foundation/Crypto/Semantics/Oracle/ReusableCertifiedSource.lean) は、実際の呼び出し元が選ぶ要求と、証明済みの処理部品を共通の契約で合成します。[ReusableSourceExecution.lean](Foundation/Crypto/Semantics/Oracle/ReusableSourceExecution.lean) は、応答後の状態の条件を保持して有限回合成し、追加の停止証明から全体の最終分布を導きます。任意の処理結果型と応答長を扱い、元の実際の費用を保持します。具体的な呼び出し元の証明の再構成と第二方式への適用は続けて必要です。

[ProcedurePotential.lean](Foundation/Crypto/Semantics/ProcedurePotential.lean) は、状態ごとに残す予算を使って適応的な実行を合成します。証明する状態の型に含まれる配置だけを対象とし、結果に応じた次の契約と実際の費用を保持します。[ReusableResponseTwoQueriesPotential.lean](Foundation/Examples/ReusableResponseTwoQueriesPotential.lean) は、既存の二回問い合わせの実行全体をこの規則で再構成し、任意長の鍵と初回要求について上界 `18*K+5*L+66` 段階と最終状態を検証します。

[ContractObservedBackend.lean](Foundation/Crypto/Logic/General/ContractObservedBackend.lean) は、機械の種類に依存せず、完了した実行契約と観測実験の一致から一般論理の安全性の対象を構成します。全実行途中の資源上界も追加できます。[ReusableResponseContractBackend.lean](Foundation/Examples/ReusableResponseContractBackend.lean) は、保持鍵から始まる二回問い合わせの実際の停止契約と、有限コードを含むビット数上界を同じ証明へ接続します。暗号方式の意味との一致と安全性は利用側の証明条件です。

[ReusableResponseInitialization.lean](Foundation/Crypto/Semantics/Oracle/ReusableResponseInitialization.lean) は、任意の有限鍵生成コードの実際の出力を複数要求の機械へ渡します。保持テープの配置調整も二段階で実行して数えます。[ReusableResponseInitializedTwoQueries.lean](Foundation/Examples/ReusableResponseInitializedTwoQueries.lean) は、任意幅の一様な鍵生成から二回問い合わせと最終停止までを、上界 `24*W+5*L+72` 段階で検証します。[登録例](Foundation/Examples/ReusableResponseInitializedBackend.lean) は公開インスタンスごとに変わる文脈も扱います。初期化を含む全実行途中のビット数上界は続けて必要です。

[ReusableInitializationEncoded.lean](Foundation/Constructions/Symmetric/EncryptThenMAC/ReusableInitializationEncoded.lean) は、鍵生成から任意回数の問い合わせまで、四つの有限コードと全実行途中の状態表現を多項式で評価します。元の呼び出し元も全段階で数えます。[登録例](Foundation/Examples/ReusableResponseInitializedEncodedBackend.lean) は、実際の鍵生成と二回問い合わせの停止契約に、このビット数上界を同じ実行機械で付けます。公開インスタンスに応じて変わる文脈も扱います。

[ProcedureModel.lean](Foundation/Crypto/Semantics/Machine/ProcedureModel.lean) は、任意の入力型・内部結果型を持つ有限コードの実行契約と、数学的な分布を接続します。内部結果に鍵を保持したまま、公開出力だけの分布と識別優位性を実際の実行へ移します。停止契約の導出でも最終状態と実際の費用の相関を保持します。[OneTimePadProcedureModel.lean](Foundation/Constructions/Symmetric/OneTimePadProcedureModel.lean) は、任意幅の鍵生成・暗号化・新しい鍵を生成する暗号化に適用します。時間上界以上の任意の観測時点で、暗号化の正しさと完全秘匿性を共通規則から導きます。保持鍵の要求配置への具体的な接続は、以下の `BlockPadResponse` で扱います。第二方式への適用は引き続き必要です。

[ReusableSupportedResponse.lean](Foundation/Crypto/Semantics/Oracle/ReusableSupportedResponse.lean) は、到達する結果だけに停止・テープ配置などの証明を要求する応答契約です。既存の応答契約へ変換しても、結果と実際の時間の同時分布を保存します。[ReusableResponseModel.lean](Foundation/Constructions/Symmetric/EncryptThenMAC/ReusableResponseModel.lean) は、任意の型を持つ暗号処理のモデルを、実際の鍵コピー・要求準備・応答配送へ接続します。機械の入口と準備後のテープ配置の一致、および応答テープの配置の証明が必要です。暗号方式の内部結果を公開出力から復元する必要はありません。この保持鍵の配置に一致する任意幅の具体例は、以下の `BlockPadResponse` です。

[FlaggedBlockXor.lean](Foundation/Crypto/Semantics/Machine/FlaggedBlockXor.lean) は、区切りを持つ要求列の後に鍵列を置く配置で、任意幅の排他的論理和を実行する固定コードです。[BlockPadResponse.lean](Foundation/Constructions/Symmetric/EncryptThenMAC/BlockPadResponse.lean) は共通モデルと応答処理へ適用し、幅 `W` の処理上界を `45*W+28` 段階と証明します。[ReusableBlockPad.lean](Foundation/Examples/ReusableBlockPad.lean) は、実際の鍵生成から一回の暗号化要求と呼び出し元の停止までを `55*W+41` 段階で検証します。暗号文だけを観測する実験について完全秘匿性を証明します。[ReusableBlockPadResources.lean](Foundation/Examples/ReusableBlockPadResources.lean) は、四つの有限コードを含む全実行途中のビット数上界を付けます。入力準備は入口以前の別契約です。同じ鍵で複数回暗号化する安全性と、第二方式の全実行・安全性への適用は引き続き必要です。

[ReusableBlockPadBackend.lean](Foundation/Examples/ReusableBlockPadBackend.lean) は、この全実行を一般論理へ登録し、暗号文に対する決定的な判定関数の識別優位性がゼロであることを証明します。判定関数自身は数学的な観測であり、その実行時間は暗号化の時間上界に含めません。[ReusableBlockPadEncodedBackend.lean](Foundation/Examples/ReusableBlockPadEncodedBackend.lean) は、同じ有限コードと観測実験へ全実行途中のビット数上界を付けます。`unitWitness` は、外部状態と履歴が空の具体例で、幅の多項式上界だけから資源付きの実行証明を構成します。初期のテープ量と外部遷移の条件は実際の配置から証明します。第二方式への適用は引き続き必要です。

[GeneratedBlockMask.lean](Foundation/Constructions/Symmetric/EncryptThenMAC/GeneratedBlockMask.lean) は、一様分布に限定せず、任意の証明済みの有限生成コードを同じ暗号化実験へ接続します。生成時間を `B`、出力幅を `W` とすると全体の上界は `B+50*W+39` 段階です。[疑似乱数生成器との接続](Foundation/Constructions/Symmetric/EncryptThenMAC/GeneratedBlockMaskPRG.lean) は、実際の生成分布とモデルの一致を条件に、暗号化の識別優位性を二つの帰着先の優位性の和で評価します。`Implementation` は全パラメータで有限コードを固定します。[資源評価](Foundation/Constructions/Symmetric/EncryptThenMAC/GeneratedBlockMaskResources.lean) は、実際の生成コードを含む全実行途中を数えます。[一様生成の具体例](Foundation/Examples/GeneratedBlockMask.lean) は、以前の実験と全観測時点で一致します。具体的な伸長生成器の有限コードとその安全性仮定の適用は引き続き必要です。

### 実行コードによる暗号文の判定

`Machine.NativeContinuation` は、停止が証明された確率的な処理から、固定の有限な判定コードへ実行を接続します。接続は 1 ステップを消費します。判定コードは、指定された実際の機械の入力・出力テープとヘッド位置を引き継ぎます。接続時に変更するのは命令位置と停止フラグだけです。生成側の状態は別に保持され、判定コードの命令には渡されません。結果と時間の相関を含む合成則も証明しています。

`Foundation.Examples.ReusableBlockPad.NativeObserver` では、任意の長さのワンタイムパッドにこの接続を適用しています。公開する機械の両テープが暗号文だけから決まることを確認し、実際の判定コードを含む完全秘匿性を証明しています。暗号文長を W、判定コードの時間上界を T とすると、全体の時間上界は `55W + 42 + T` です。判定コードの上界は長さ W の暗号文に対してだけ要求します。すべての入力長に共通の定数上界は要求しません。

具体例には、先頭セルを読む 5 命令のコードと、実際の乱数命令を使う 2 命令のコードがあります。全体の時間上界はそれぞれ `55W + 45` と `55W + 44` です。ゼロ長の暗号文も含みます。秘密性の観測対象は最終的な判定ビットです。判定実行を含む全体の符号化記憶量上界は、次の共通規則で扱います。実行時間も公開する場合の秘密性と、実際に出力を伸長する生成器の接続は、引き続き別の証明が必要です。


### 判定実行を含む全体の記憶量

`Machine.NativeContinuation.Resources` は、暗号化などの処理と、その後の判定コードを合わせた記憶量上界を扱います。実行途中の状態を、元の処理の実行途中と、1 回の接続を経た判定実行途中に分ける定理を用います。保存した元の状態、判定コード、両テープ、命令位置を復元可能なビット列として表し、指定した実行ステップ数までのすべての分岐・実行途中で長さを抑えます。判定の停止や安全性は、この記憶量の定理の前提には含まれません。

`Foundation.Examples.ReusableBlockPad.NativeObserver.Resources` は、この共通規則を任意長のワンタイムパッドへ適用します。鍵生成、鍵コピー、暗号化、呼び出し元、判定の五つの有限コードを数えます。元の呼び出し元、秘密鍵、履歴と、判定中の実際の機械状態も数えます。外部状態・応答の大きさに上界があれば、全実行途中の符号化長に上界を与えます。`unit_peak` は、外部からデータを受け取らない具体例で、これらの条件を実装から証明しています。`unitBound_polynomial` は、固定の判定コードについて、暗号文長と判定時間の上界が多項式で抑えられる場合に、全体の符号化記憶量も多項式で抑えられることを示します。符号化は数学的な記憶量の表現です。その符号化を作る処理を機械命令として追加したものではありません。


### 任意の生成器と実際の判定コード

`GeneratedBlockMask.NativeObserver` は、証明済みの任意の有限生成コードを使い、暗号化から実際の判定コードまで接続します。生成分布の一様性は要求しません。生成時間上界 B、出力幅 W、判定時間上界 T に対して、全体の時間上界は `B + 50W + 40 + T` です。公開する両テープは暗号文だけから決まり、秘密の生成結果や履歴は判定命令の状態に含めません。

`GeneratedBlockMask.PRG.NativeObserver` は、実際の生成分布が擬似乱数生成器の実分布と一致する条件の下で、全体実行の識別優位性を、帰着先の二つの識別優位性の和で抑えます。固定の生成コードと固定の判定コードを使うパラメータの族について、二つの帰着先の優位性が無視できる場合の結論も証明しています。帰着先の識別器の有限コード実装と、仮定する攻撃者クラスへの登録は、次の節の共通契約で証明します。

`GeneratedBlockMask.NativeObserver.Resources` は、任意の生成コードと判定コードについて、五つのコードと全実行途中を含む符号化記憶量を抑えます。生成時間、出力幅、判定時間、初期配置と外部データの各上界が多項式で抑えられる場合の合成則もあります。公開テープの選択と停止の共通証明は `CryptoOracle.Interactive.ReusableNativeObservation` に移しています。既存のワンタイムパッドの証明も同じ定義を使います。`Examples/GeneratedBlockMaskNativeObserver.lean` は、一様ビット生成を接続した場合に、以前の実際の判定実験をすべての観測時点で回復することを確認します。この具体例は伸長生成器ではありません。


### 帰着先の有限実装と攻撃者クラスへの登録

`NativeMaskReduction` は、受信済みのチャレンジと公開メッセージを物理テープ上の入力として、実際にマスク処理と判定コードを実行します。数学的な帰着との一致を証明し、暗号文長 W と判定上界 T に対して `49W + 36 + T` の時間上界を与えます。公開メッセージは、フラグ付きの形式で呼び出し元のテープに置かれていることを入力条件とします。

`NativeMaskChallenge` は、外部チャレンジへの問い合わせ、応答のセル単位の書き込みと巻き戻し、私有テープのヘッド位置合わせを追加します。全体の時間上界は `52W + 42 + T` です。外部の実験がチャレンジを生成する費用は、識別器の費用とは分けます。応答を識別器へ読み込む処理は計上します。証明用のカウンタで、全実行途中の問い合わせ回数が高々 1 回であり、完了時にはちょうど 1 回であることを証明しています。カウンタは実行の分布を変更しません。

`CountedContractObservedBackend` は、停止・時間・観測分布の実行契約に、問い合わせなどの事象の回数上界を追加する共通の登録規則です。`ConstrainedObservedExecution` は、登録する実行環境に条件を課す共通規則です。`NativeMaskReductionBackend` では、外部チャレンジの実分布・理想分布と公開メッセージが指定したものに一致することを要求します。任意の応答分布や、二つの世界を識別する隠れた助言を設定から渡すことは許しません。

`NativeMaskReductionSecurity.security_and_time` は、この登録済みの攻撃者クラスに対する擬似乱数生成器の安全性を前提に、実際の生成・暗号化・判定を含む識別優位性が無視できることを導きます。二つの帰着先のクラス所属は、実際の有限コードと実行契約から証明します。生成時間・出力幅・判定時間に多項式上界があれば、全体の時間の多項式上界も同時に導きます。具体例には先頭セルを読むコードと乱数命令を使うコードがあり、どちらの帰着分岐にも適用できます。

ここで登録する実行機械は、明示した制御器と固定の有限コードを組み合わせたものです。単一のネイティブ命令列への平坦化や、別の計算機モデルとの時間単位の同一視は主張しません。問い合わせ応答の読み込みを含む全体の符号化記憶量の登録は、後の「帰着全体の保存量と安全性」の節で追加します。具体的な伸長生成器の接続は引き続き残っています。


### 応答読み込み区間の保存量の一般化

`ResponseLoadingResources` は、既存の応答読み込み処理を対象に、暗号方式・応答分布・外部オラクルに依存しない保存量上界を与えます。読み込み完了後に保存した機械が再開する直前を区間の境界とします。境界までの遷移は実行機械の遷移と一致し、境界で得られる状態と実際の使用時間の同時分布も一致します。再開後の機械が停止するという仮定は必要ありません。

読み込み途中では、外部状態・履歴・保存したプログラム位置が変わらず、保存セル数が 1 ステップ当たり高々 1 個増えることを証明しています。応答の未処理部分、作業テープ、保存した機械、外部状態、履歴を含む全配置の復号可能な符号化を測定します。有限コードも一度含めた符号化ビット数に上界を与えます。初期保存量・プログラム位置・履歴件数・時間の上界が多項式なら、この符号化保存量にも多項式上界があります。

`NativeMaskChallengeResources` は、この共通補題を任意長のチャレンジに適用します。幅 W のチャレンジについて初期保存セル数は W + 3 です。読み込み途中の全配置と、実際に使用した時間で評価した境界配置を扱います。この結果は読み込み区間の証明です。問い合わせ・位置合わせ・マスク処理・判定までを含む外側の制御器全体の保存量登録は、次の節で追加します。


### 帰着全体の保存量と安全性

`NativeContinuationGrowth` は、生成側の状態を保持したまま有限の判定コードへ移行する実行について、保存量とプログラム位置の局所的な増分を扱う共通補題です。停止や安全性の仮定を使わず、前後の制御器へ合成できます。

`NativeMaskChallengeWholeResources.peak` は、問い合わせから応答読み込み、位置合わせ、マスク処理、判定までの全実行途中について、全状態の復号可能な符号化ビット数を評価します。読み込み中も保持する公開メッセージ、判定中も保持する私有データと履歴、作業テープ、各制御位置、六つの有限コードを含めます。固定コードは状態の外側で一度ずつ符号化します。元の呼び出し元の配置は、全体の入力の表現と既存の生成側の表現の両方で数えるため、上界は保守的です。チャレンジを生成する外部実験の内部状態や応答分布そのものの表現は、攻撃者の保存量には含めません。

`CertifiedObservedExecution` は、既存の実行証明に追加の資源証明を組み合わせる一般規則です。有限コード、実行環境、時間上界、観測分布と、以前の資源証明を保持します。`NativeMaskReductionSpaceBackend` はこの規則を使い、同じ帰着に実行時間・問い合わせ回数・全実行途中の符号化保存量の証明を同時に付けます。指定したチャレンジ分布と公開メッセージを要求する環境条件も保持します。

`NativeMaskReductionSpaceSecurity.security_time_and_reduction_space` は、この資源証明付きの攻撃者クラスに対する生成器の安全性を前提に、実際の生成・暗号化・判定の識別優位性が無視できることを導きます。暗号化実験の実行時間と、二つの帰着の全実行途中の保存量には多項式上界があります。帰着の資源証明の存在には、生成器の安全性仮定を使いません。具体的な伸長生成器の実装と安全性仮定への接続、標準的な確率的多項式時間攻撃者との対応、単一のネイティブ命令列への平坦化は、この証明だけでは完成しません。

`Examples.NativeMaskReductionSpace` は、先頭セルを読む固定コードと乱数命令を使う固定コードの両方について、この三種類の資源証明を持つ帰着を構成します。先頭セルを読む場合の時間上界は `52W + 45` です。左右の帰着は同じ有限コードを使います。


### 有限コードの連結と生成器の内部結果

[SubroutineContract](Foundation/Crypto/Semantics/Machine/SubroutineContract.lean) は、有限コードの実行を、実際に呼び出し元へ戻るまでの契約に変換します。実行がコードの範囲から逸脱しないこと、入口が有効であること、到達する結果で停止することを要求します。復帰までの実際の時間と、両テープを含む機械状態の同時分布を保持します。停止状態で予算まで待つ時間を、復帰までの実時間には加えません。

[NativeCompositionContract](Foundation/Crypto/Semantics/Machine/NativeCompositionContract.lean) は、二つの契約を一つの固定された有限コードへ連結します。第二の処理は、第一の処理から実際に返された両テープとヘッド位置を引き継ぎます。接続時に意味上の出力からテープを再構成しません。第一の時間上界を B、第二の到達可能な入力での共通上界を C とすると、最終停止を含む上界は `B+C+1` 段階です。結果と使用時間の相関を含む合成則があります。[具体例](Foundation/Examples/NativeCompositionContract.lean) は、乱数命令と先頭セルの判定を 10 命令のコードに連結します。任意の元のテープに対し、6 段階以上での全機械状態の分布と、入力テープの保存を証明します。この連結は二つのネイティブ処理についての結果です。問い合わせなどを含む外側の制御器全体の平坦化は、引き続き別の課題です。

[ProjectedPrivateInitialization](Foundation/Crypto/Semantics/Machine/ProjectedPrivateInitialization.lean) と [ReusableProjectedInitialization](Foundation/Crypto/Semantics/Oracle/ReusableProjectedInitialization.lean) は、生成器の内部結果と、後続処理で使う鍵を分離します。内部結果には種や作業領域を含められます。内部結果から鍵への写像が一対一であることは要求しません。生成中は既存の実行機械の全状態を保持します。実際に出力テープを私有領域へ移す遷移の後に、鍵だけを後続契約の論理的な結果として扱います。鍵から内部結果を復元する条件はありません。

[ProjectedGeneratedBlockMask](Foundation/Constructions/Symmetric/EncryptThenMAC/ProjectedGeneratedBlockMask.lean) は、この共通初期化を任意長のマスク暗号化へ接続します。生成時間 B、鍵幅 W に対する時間上界は `B+50W+39` 段階です。[生成器の共通仕様](Foundation/Constructions/Symmetric/EncryptThenMAC/ProjectedGeneratedBlockMaskPRG.lean) は、実際の内部結果の分布から鍵を取り出した分布だけが、擬似乱数生成器の実分布に一致することを要求します。以前の、内部結果自体が鍵である仕様も特別な場合として含みます。暗号文分布の一致と、任意の数学的な判定関数についての識別優位性の上界を証明しています。この新仕様から実際の有限な判定コードへの接続と、資源証明付きの帰着への接続は、次の節で扱います。具体的な伸長生成器の実装と安全性仮定への適用は、引き続き必要です。


### 内部結果を分けた生成器の資源証明と安全性

`ProjectedGeneratedBlockMask.NativeObserver` は、内部結果と鍵を分けた生成器から、実際の暗号化と有限の判定コードへ接続します。全体の時間上界は `B+50W+40+T` 段階です。判定コードが受け取る両テープは暗号文だけから決まります。生成中の全機械状態は、既存の転送遷移まで保持します。転送後の私有状態に保持するのは出力した鍵であり、生成時の作業機械そのものではありません。

`ProjectedGeneratedBlockMask.Resources` と `ProjectedGeneratedBlockMask.NativeObserver.Resources` は、新仕様の生成・暗号化・判定について全実行途中の符号化保存量を評価します。実際の生成コード、生成中の入力テープと作業領域、元の呼び出し元、履歴、私有の鍵、判定コードと判定中の両テープを含めます。停止や擬似乱数性は、この保存量の証明に必要ありません。初期配置と外部データに関する上界は明示的な前提です。

[ProjectedNativeMaskReductionSpaceSecurity](Foundation/Constructions/Symmetric/EncryptThenMAC/ProjectedNativeMaskReductionSpaceSecurity.lean) は、既存の時間・問い合わせ回数・保存量の証明を持つ二つの帰着を、そのまま新仕様の安全性評価へ接続します。帰着は外部から鍵のチャレンジを受け取るため、生成器の内部結果に依存しません。資源証明付きの攻撃者クラスに対する生成器の安全性を前提に、実際の生成・暗号化・判定の識別優位性が無視できること、全体の時間と帰着の保存量に多項式上界があることを導きます。具体的な伸長生成器、標準的な確率的多項式時間攻撃者との対応、外側の制御器全体の単一コードへの平坦化は、引き続き必要です。


### 到達する結果の条件と、種を生成する有限コード

[ControlClosure](Foundation/Crypto/Semantics/Machine/ControlClosure.lean) は、有限命令列の分岐先と次の命令位置を調べる決定可能な十分条件を定義します。この条件から、停止していない遷移がコード内に留まることを証明します。乱数命令の両方の遷移も含みます。停止することや時間上界を、この条件だけから導くものではありません。種の一様生成と既存の連結例は、この共通定理を使います。

[ExportedProcedure](Foundation/Crypto/Semantics/Machine/ExportedProcedure.lean) は、実際に到達する終了配置にだけ停止と出力テープの配置条件を要求します。終了配置にその条件の証明を付けた型を使うことで、以前の初期化契約へ接続します。有限コード、入口、全終了配置、使用時間との相関を保持し、追加の機械命令は導入しません。数学的な復号関数はこの型上で正しいことを証明します。到達しない入力に対する復号の既定値は実行に使いません。

[PhysicalGeneratorImplementation](Foundation/Constructions/Symmetric/EncryptThenMAC/PhysicalGeneratorImplementation.lean) は、この規則を生成器の実装へ適用します。内部結果の型全体に停止条件を課す代わりに、到達する結果の実際の終了配置に条件を課せます。変換後も同じ有限コード・入口・時間上界を使います。終了配置と時間の同時分布の一致も証明します。

[SeededGeneratorImplementation](Foundation/Constructions/Symmetric/EncryptThenMAC/SeededGeneratorImplementation.lean) は、任意長の一様な種を実際に生成する固定コードと、証明済みの伸長処理の固定コードを連結します。伸長処理は、種のテープとその実際のヘッド位置を引き継ぎます。生成関数を機械の外で無償に評価したり、種から入力テープを作り直したりしません。伸長処理の条件は、到達する結果の出力テープが指定した生成関数の値を持つことです。作業テープの全配置が決定的であることは要求しません。種の長さ S、伸長処理の時間上界 C に対して、生成器全体の上界は `5S+C+3` 段階です。パラメータごとにコードを作り直すことはありません。

[SeededGeneratorSecurity](Foundation/Constructions/Symmetric/EncryptThenMAC/SeededGeneratorSecurity.lean) は、この生成器、マスク暗号化、実際の判定コードを、資源証明付きの帰着へ接続します。種の長さ S、伸長上界 C、出力長 W、判定上界 T に対して、全体の上界は `5S+C+50W+43+T` 段階です。これらの量が多項式で抑えられ、登録した攻撃者クラスに対して生成器が安全なら、実際の実験の識別優位性が無視できることを導きます。帰着の保存量にも多項式上界があります。

[任意長の接続例](Foundation/Examples/SeededGeneratorAssembly.lean) は、種をそのまま出力する処理を接続し、固定の 10 命令、時間上界 `5S+4`、実際のコードが出力する一様分布と、消費済みの入力テープを保持することを検証します。ゼロ長にも適用できます。この例は接続規則の検証であり、出力を伸長する生成器ではありません。具体的な伸長処理の実装とその擬似乱数性への適用は、引き続き必要です。


### 入力条件を持つ有限コードの連結

[TypedSubroutineContract](Foundation/Crypto/Semantics/Machine/TypedSubroutineContract.lean) は、実際の復帰配置から、到達した論理的な結果を復号できる場合の契約です。復号の正しさは到達する結果にだけ要求します。論理的な結果を付ける操作は証明上の操作であり、機械命令やテープの再配置は追加しません。論理的な結果を除くと、実際の全復帰配置と使用時間の同時分布が一致します。

[TypedNativeComposition](Foundation/Crypto/Semantics/Machine/TypedNativeComposition.lean) は、異なる入力型を持つ二つの有限コードを連結します。第二の処理は、その入力型で表す正しい配置に対してだけ実行契約を持てば十分です。第一の処理が実際に返す配置と、第二の処理の実際の入口が一致することを、到達する結果ごとに要求します。変換関数だけを与えて無償にテープを作り直す接続は認めません。コード長、結果の分布、使用時間との相関、全体の実行との一致を証明します。時間上界は以前と同じ `B+C+1` 段階です。

`SeededGeneratorImplementation.Expander` は、この共通規則を使い、種の型を入力型にします。生成後の正しい種の配置についてだけ、実行・停止・時間・出力テープの条件を要求します。不正なテープ上でも伸長処理が停止するという証明は不要です。以前の、任意の機械配置に対する契約は `ConfigurationExpander` として保持しています。`ConfigurationExpander.typed` により、新しい仕様へ同じコード・入口・予算・結果と時間の同時分布で接続できます。暗号化と資源証明付きの安全性への接続は新仕様でも検証します。

[入力条件の具体例](Foundation/Examples/TypedSeedPrecondition.lean) は、正しい種の終端の空白セルでは停止し、現在セルがデータである不正な配置では永久にループする有限コードを使います。任意長の種の生成から始めた連結コードについて、時間上界 `5S+5` と一様な出力分布を証明します。同じ部品に不正な配置を与えた場合は、任意の実行時間で停止しないことを証明します。その不正な配置を入口に含む停止契約が存在し得ないことも証明します。したがって、任意の配置に対する停止条件を隠れて要求してはいません。この例は種をそのまま出力し、伸長は行いません。


### 生成器と暗号化実験の全実行途中の保存量

[NativeEncodedResources](Foundation/Crypto/Semantics/Machine/NativeEncodedResources.lean) は、任意の有限コードと全機械配置を一緒に復号できるビット表現を定義します。コードの区切りに使うビットも数えます。両テープの空白セルとヘッド位置、プログラム位置、停止フラグを含め、すべての乱数分岐・全実行途中の長さを評価します。復帰地点では、実際に使用した時間に対応する保存量上界も与えます。停止・暗号学的な安全性の仮定は不要です。初期配置の大きさと時間上界が多項式なら、この保存量も多項式で抑えられます。既存の私有状態の制御器と判定への接続も、同じ有限コードの符号化を使います。表現を実際に生成・復号する時間の評価は含みません。

[SeededGeneratorResources](Foundation/Constructions/Symmetric/EncryptThenMAC/SeededGeneratorResources.lean) は、一様な種の生成と伸長処理を連結した実際のコードへ、この共通定理を適用します。種の長さ S と伸長処理の時間上界 C から、全生成途中の保存量を導きます。初期テープのセル数は `S+2` 以下です。生成時間の上界は `5S+C+3` 段階です。生成器の作業領域について別の仮定は要求しません。実際に使用する作業領域は全機械配置に含め、遷移ごとの増加量から評価します。

同じモジュールは、外部データを保持しない単位型のオラクルについて、生成・暗号化・実際の判定までを含む全実行途中の保存量を評価します。出力幅を W とすると、元の呼び出し元と種の入力を含む初期の大きさは `S+2W+3` 以下です。判定の上界 T を含む全体の時間は `5S+C+50W+43+T` 段階です。生成器の実際の連結コード、鍵コピー、マスク処理、呼び出し元、判定の五つのコードと、鍵・履歴・全作業テープを数えます。元の呼び出し元は実行機械の文脈としても保持するため、上界は保守的です。

`resource_profiles` は、種と出力の長さ、伸長時間、判定時間に多項式上界があれば、生成中の保存量、全体の時間、暗号化実験全体の保存量、二つの帰着の保存量を同時に多項式で評価します。外部状態や応答データが変化する実験は、既存の一般的な資源定理の条件を別途使います。公開メッセージを入口のフラグ付き形式へ準備する時間は、この実行より前の契約で扱います。今回の上界には、準備済みの公開メッセージを保持する保存量を含めます。

[検証例](Foundation/Examples/SeededGeneratorResources.lean) は、正しい種の配置でだけ停止を保証する部品を使い、先頭セルを読む判定コードと乱数命令による判定コードの両方で保存量の多項式上界を証明します。任意長の種・メッセージと全実行途中を対象にします。例は恒等生成器のままであり、具体的な伸長生成器の実装は引き続き必要です。

### 入力と終了状態の関係を保証する実行契約

[ProcedureRelation](Foundation/Crypto/Semantics/ProcedureRelation.lean) は、入力と出力の関係を、起こり得る結果について証明した実行契約を構成します。元の入力を証明上の情報として保持します。この情報を除くと、元の出力と使用時間の同時分布が一致します。入力を機械のテープへ複製する操作は追加しません。元の入力との一致は、実際に起こり得る認証済みの結果について証明します。認証された型の任意の値が現在の入力を持つとは仮定しません。

[RelationalProcedure](Foundation/Crypto/Semantics/Machine/RelationalProcedure.lean) は、入力と全終了配置の任意の関係を保証する有限コードの契約です。出力テープの形式に限定せず、入力に応じたテープの内容や配置などを条件にできます。コード・入口・時間上界を保持します。全終了配置と使用時間の同時分布、および任意の物理状態の観測分布も保持します。条件の成立と暗号学的な安全性は別の証明です。

[TypedCompositionRelation](Foundation/Crypto/Semantics/Machine/TypedCompositionRelation.lean) は、二つの部品の実際に起こり得る結果から、連結コードの事後条件を導きます。`inputTape_frame` は、第一の部品が入力に応じたテープを返し、第二の部品が自身の入力テープを保存する場合に、全体がそのテープを保存することを示します。第二の入口と第一の復帰配置の実際の一致を使います。異なる論理的な入力型を持つ部品にも適用できます。認証後も、連結コード・時間上界・終了配置と使用時間の同時分布は変わりません。[任意長の種の生成例](Foundation/Examples/SeededGeneratorAssembly.lean) の入力テープ保持証明は、この共通規則を使います。

### 命令位置ごとの条件から全実行途中の性質を導く規則

[ProgramAssertions](Foundation/Crypto/Semantics/Machine/ProgramAssertions.lean) は、各命令位置で満たすべき両テープの条件と、停止時の命令位置・両テープの条件を指定する共通規則です。一命令の実行後に条件を保証するため、その命令の前に満たすべき条件を `Instruction.precondition` で定義します。乱数命令では両方の結果に条件を要求します。`verified_iff_preserves` は、各命令位置の証明義務と命令列の外での停止の証明義務が、指定した条件の一段階の保存と同値であることを示します。テープに関する数学的な条件を自動判定する手続きではありません。

この規則から、任意の実行時間・すべての乱数分岐での条件の保存を導きます。停止した場合には事後条件を導きます。停止すること自体は別の証明です。独立した二つの条件の証明も組み合わせられます。[SubroutineAssertions](Foundation/Crypto/Semantics/Machine/SubroutineAssertions.lean) は、有限コードを別の命令列へ埋め込んだ場合にも、復帰までの全配置が元の条件を満たす配置の移動に対応することを示します。復帰後の呼び出し元の実行は、この定理の対象外です。

[AssertedProcedure](Foundation/Crypto/Semantics/Machine/AssertedProcedure.lean) は、入力ごとに指定した命令位置の条件から、全終了配置の関係を保証する実行契約を導きます。報告された結果が実際にその使用時間で到達するという証明を明示的に要求します。コード・入口・時間上界・全終了配置と使用時間の同時分布を保持します。

[乱数ループの例](Foundation/Examples/ProgramAssertions.lean) は、任意の初期テープについて全実行途中の条件と非停止を証明します。命令列の外での停止条件を省くと受理してしまう仕様について、正しい規則が拒否することも証明します。[任意長の種の生成例](Foundation/Examples/AssertedBitGeneration.lean) は、既存の六命令の種の生成コードに共通規則を適用します。時間上界は `5W+2` 段階のままです。ゼロ長を含む任意長 W について、入力のビット列が全実行途中で保存されることを証明します。[TapeReading](Foundation/Crypto/Semantics/Machine/TapeReading.lean) の共通補題は、ヘッド移動によるビット列の観測の保存を扱います。全物理テープの等式や、テープ全体を一命令で読む操作とは区別します。

### 順位から停止と実行費用を導く共通規則

[Ranking](Foundation/Crypto/Semantics/Ranking.lean) は、実行地点に自然数の順位を与え、終了地点へ着かない各遷移で順位が厳密に減ることから、全分岐が `初期順位+1` 段階以内に終了地点へ着くことを導きます。順位がゼロの実行中の状態からも、終了地点へ一段階で進めます。不変条件の保存は終了地点へ着く前にだけ要求します。終了地点が呼び出し元への能動的な復帰である場合も扱えます。戻った後の呼び出し元の動作を停止させる条件は要求しません。順位を実行機械のカウンタとして追加する操作も行いません。

この規則は、全終了配置と実際の初回到達時間を保持する実行契約を構成します。順位の上界まで早い分岐を引き延ばしません。各結果が報告された時間で実際に到達することも証明します。[ProgramRanking](Foundation/Crypto/Semantics/Machine/ProgramRanking.lean) は、有限コードの各命令位置の条件と順位の減少から、この契約を構成します。乱数の両方の結果と、命令列の外での暗黙の停止を扱います。任意の論理的入力型を、条件を満たす実際の入口配置へ対応させられます。入口の準備操作は追加しません。

[PrivateBitGenerationRanking](Foundation/Crypto/Semantics/Machine/PrivateBitGenerationRanking.lean) は、任意長 W の種の生成を、この規則で認証する共通実装です。命令位置と未消費の入力から順位を定め、既存のコード全体の停止証明を前提にせず、六命令のコードの停止と `5W+2` 段階の上界を導きます。従来の実行証明は、出力の一様分布と全終了配置の同定に再利用します。`typed` は種のビット列を返す実行契約です。コード・入口・出口を従来の種の生成処理と同じに保ち、実際の初回到達時間を保持します。全生成途中のコードと全配置の保存量にも多項式上界を与えます。ゼロ長も対象です。

`SeededGeneratorImplementation.sampler` は、この順位による種の生成契約を使います。後続の伸長処理との連結、暗号化、既存の安全性と資源量の定理へ接続します。全体のコードと時間上界は従来どおりです。`sampler_costed` は、種の生成部分の全終了配置と実際の初回到達時間の同時分布を示します。

[使用時間が分岐で異なる例](Foundation/Examples/RankedVariableTime.lean) は、同じ有限コードが乱数ビットに応じて三段階または四段階で停止することを扱います。`costed` は、全終了配置とその二つの時間の同時分布を証明します。四段階という上界を両方の分岐の使用時間に置き換えてはいません。具体的な伸長生成器と標準的な攻撃者モデルとの対応は、この停止規則とは別に引き続き必要です。

### 入力ごとの条件から生成器と資源証明を構成する規則

[RankedFamily](Foundation/Crypto/Semantics/Machine/RankedFamily.lean) は、一つの有限コードについて、元の入力に応じた不変条件と順位を指定する共通の実行契約です。条件は元の入力と全終了配置の関係を表せます。元の入力を終了配置から復元する条件や、入力をテープへ複製する操作は追加しません。停止・事後条件・実際の初回到達時間を導きます。

[RankedFamilyResources](Foundation/Crypto/Semantics/Machine/RankedFamilyResources.lean) は、その契約からコードと全配置の保存量の上界を導きます。全実行途中と、実際の初回到達時間に応じた終了状態を対象にします。入力サイズごとに任意の有効入力の集合を指定でき、全有効入力に共通する入口・時間の上界が多項式なら、保存量にも共通の多項式上界を与えます。

[RankedExpander](Foundation/Constructions/Symmetric/EncryptThenMAC/RankedExpander.lean) は、種ごとの条件・順位・出力テープの証明から、既存の生成器の組立が要求する実装契約を構成します。全プログラムの実行定理や終了分布を別途与える必要はありません。実際の入口と有限コードの制御条件は証明義務として残ります。

[一ビット追加の例](Foundation/Examples/RankedBitExtension.lean) は、任意長 n の種に公開された固定ビットを追加します。実際の書込み・ヘッド移動・停止の三命令を、共通部品 [OutputAppend](Foundation/Crypto/Semantics/Machine/OutputAppend.lean) で認証します。種の生成との連結コードは十二命令で、実行上界は `5n+6` 段階です。生成・暗号化・帰着の資源定理にも接続します。判定時間の上界を T とすると、暗号化実験の上界は `55n+96+T` 段階です。

この例の生成器は意図的に安全ではありません。実機の出力の最後のビットは固定値で、一様分布の最後のビットは公平な乱数です。[BitSampling](Foundation/Constructions/Symmetric/BitSampling.lean) は、この比較に使う任意長の一様ビット列の分布則を提供します。実装と資源の証明は暗号学的安全性を含みません。安全性を仮定する具体的な伸長生成器への適用、標準的な攻撃者モデルとの対応、外側の制御器全体の統合は引き続き残ります。

### 停止証明と機能上の条件を独立に再利用する規則

[RankedFamilyRefinement](Foundation/Crypto/Semantics/Machine/RankedFamilyRefinement.lean) は、順位で停止を認証したコードへ、独立に証明した入力ごとの条件を追加します。`Ranking.restrict` は、元の条件を含む強い条件の下でも同じ順位を使います。`RankedFamily.enrich` は二つの条件を組み合わせ、全終了配置と実際の使用時間の同時分布が元の契約と一致することを示します。時間と保存量の上界も同じです。元の実行契約を使い続ける利用者にも、新しい事後条件を適用できます。

[TapeObservationAssertions](Foundation/Crypto/Semantics/Machine/TapeObservationAssertions.lean) は、指定したテープへの書込み・消去・乱数書込みを行わないという有限検査から、任意の初期配置・全実行途中でビット列が保存されることを導きます。指定したテープのヘッド移動は許し、その実行時間は通常どおり数えます。全物理テープの保持とは異なります。別のテープへの書込みは制限しません。保存性を持つ全コードを判定する規則ではなく、十分条件を検査する規則です。

[任意長の乱数生成への適用](Foundation/Examples/RankedSamplerFrame.lean) は、既存の停止順位と、この有限検査からのビット列保存を組み合わせます。全ビット列の入力を対象にし、ゼロ長や真以外のビットを含む入力も扱います。元の六命令、時間上界 `5n+2` 段階、終了配置と使用時間の同時分布を保持します。長さ n の全入力に共通する保存量の多項式上界も導きます。入力への破壊的な書込みを検査が拒否することも確認します。既存の [AssertedBitGeneration](Foundation/Examples/AssertedBitGeneration.lean) の条件の保存証明も、命令ごとの個別証明からこの共通検査へ置き換えています。

### 連結コードの観測値・到達・保存量の共通証明

[TypedCompositionRelation](Foundation/Crypto/Semantics/Machine/TypedCompositionRelation.lean) の `tapes_frame` は、両テープから定める任意の観測値を扱います。第一の部品が入力に応じた観測値を確立し、第二の部品が自身の入口の観測値を保存する場合、実際の受け渡しの一致から全体の観測値を導きます。入力テープ全体の保存規則も、この共通規則を使います。出力テープ全体や、両テープのビット列・長さを組み合わせた条件にも適用できます。観測は証明上の関数であり、実行機械へ無料の読出し操作を追加しません。

[NativeCompositionReachability](Foundation/Crypto/Semantics/Machine/NativeCompositionReachability.lean) は、連結コードの各終了結果について、報告された時間で実際にその全配置へ到達することを示します。部品の契約の残余実行の等式だけから到達を仮定せず、実際の初回復帰を記録する呼び出しから導きます。配置の対応に沿った契約の変換、論理的な出力への復号、二つの呼び出し、最後の停止を組み合わせます。元の部品の契約へ追加の到達条件を要求しません。

[NativeCompositionResources](Foundation/Crypto/Semantics/Machine/NativeCompositionResources.lean) は、連結後のコードと全配置の保存量を、全実行途中と実際の使用時間に応じた終了状態で評価します。コードの連結で追加した制御命令も表現に含めます。サイズごとの全有効入力に共通する入口と二つの時間契約の上界から、共通の多項式上界を導けます。`SeededGeneratorImplementation.Expander.assembled_operational` と `SeededGeneratorResources.generator_costed_storage` は、この到達と保存量の規則を任意の種の生成・伸長処理の組立へ適用します。従来の生成中の保存量の証明も共通規則を使います。

[任意長の組立例](Foundation/Examples/NativeCompositionCertificates.lean) は、同じ実機コードについて、入力ビット列と出力長の同時観測、実際の使用時間での到達、その時間による全配置の保存量を証明します。恒等生成器を用いる実装の検証例であり、安全な伸長生成器の候補ではありません。外側の暗号化制御器全体を一つの有限コードへ統合する作業は、この二部品の連結とは別に残ります。

### 連結済みのコードを次の連結に再利用する部品

[NativeComponent](Foundation/Crypto/Semantics/Machine/NativeComponent.lean) は、実機の実行契約と、そのコード内の制御・入口・停止の証明を一つの部品にまとめます。`ofRankedFamily` は順位で認証したコードを部品にします。`link` では、論理的な結果の復号、実際のテープの受け渡し、第二の時間上界だけを新しく証明します。制御に関する証明は再利用します。

`TypedNativeComposition.Link.component` は連結済みの実機コードを再び部品にします。`append` はそのコードへ次の部品を連結します。この操作を繰り返せるため、固定した有限個の部品を同じ規則で組み立てられます。三部品の全体の時間上界は `第一の上界+第二の上界+第三の上界+2`、コード長は `三部品のコード長の和+6` です。追加した停止命令と制御命令も数えます。`append_semantics` は三つの分布の順次実行と、実際に保持した両テープの受け渡しを示します。連結順序を変更しても同じコードや使用時間になるという主張は含みません。

種の生成と伸長処理の組立も、この部品の契約を使います。`samplerComponent` と `Expander.component` は個々の部品、`Expander.assembledComponent` は組立済みの生成器を、さらに連結できる形で公開します。生成器の有限コードと時間上界は従来どおりです。

[三部品の検証例](Foundation/Examples/ThreeNativeComponents.lean) は、任意長の既存データの末尾へ、三つの部品で順に一ビットずつ追加します。任意の入力テープ全体を保持し、三ビットを追加した正確な終了配置を証明します。コードは十五命令、上界は十一段階です。到達と全実行途中の保存量の共通規則も使います。保存量は既存データの長さと入力テープの表現セル数の和で多項式評価します。入口は既存データの末尾を指す配置であり、その配置を準備する時間を十一段階に含むとは主張しません。暗号学的安全性の証明例ではありません。

### 既存の暗号処理を部品として使う構成

[NativeFixedComponent](Foundation/Crypto/Semantics/Machine/NativeFixedComponent.lean) は、既存のコード全体の実行定理から部品を構成します。順位から構成する方法と併用できます。与えた時間での全状態分布と、コード内の制御・入口・停止を要求します。入口の配置を無料で準備する操作は追加しません。連結時の実際の初回復帰時間は、既存の境界での実行規則で扱います。

[RetainedCopyComponent](Foundation/Crypto/Semantics/Machine/RetainedCopyComponent.lean) は、元のデータを保持する十二命令のコピーを部品として公開します。任意長の元のデータと任意の既存の出力側のセル列を対象にします。時間上界は `8n+5` 段階です。両方の既存データを数えた全実行途中の保存量にも多項式上界を与えます。既存の `PrivateKeyCopy.component` から同じ部品を使えます。

[FlaggedBlockXorComponent](Foundation/Crypto/Semantics/Machine/FlaggedBlockXorComponent.lean) は、区切り付きメッセージと鍵の排他的論理和を計算する三十七命令のコードを部品にします。鍵とメッセージは同じ任意長 n のビット列です。時間上界は `24n+8` 段階、入口の表現セル数は `3n+3` 以下です。全終了配置、暗号文、全実行途中の保存量を扱います。

[FlaggedBlockXorContinuation](Foundation/Crypto/Semantics/Machine/FlaggedBlockXorContinuation.lean) は、このマスク処理と任意の後続の有限コードを、一つの有限コードに連結します。両テープをそのまま引き継ぎ、後続の時間上界を T とすると全体は `24n+9+T` 段階以内です。この後続処理は秘密の入力テープも受け取る内部処理であり、公開の攻撃者のインターフェースとしては扱いません。

[実機で最後の暗号文ビットを読む例](Foundation/Examples/NativeMaskedLastBit.lean) は、マスク処理、[実際の一セルのヘッド移動](Foundation/Crypto/Semantics/Machine/NativeTapeMove.lean)、現在セルを読む有限コードを連結します。五十命令の固定コードで、時間上界は `24n+15` 段階です。最後のビットと空列での偽という結果、秘密の入力の保持、全実行途中の保存量を証明します。鍵コピーの出口とマスク処理の入口はテープの役割とヘッド位置が異なるため、その二つの直接の連結には実際の配置変換が別途必要です。鍵の生成や公開の暗号化実験全体まで有限コード化したとは主張しません。

### 入力形式とテープの役割を変えて部品を再利用する規則

[NativeComponentReindex](Foundation/Crypto/Semantics/Machine/NativeComponentReindex.lean) は、論理上の入力形式を変えて既存の部品を再利用します。入口は変換先の既存の入口そのもので、コード・時間・出力と時間の同時分布を保持します。入力形式の変換を実行時に計算したり、テープをロードしたりする命令ではありません。

[TapeSwapProcedure](Foundation/Crypto/Semantics/Machine/TapeSwapProcedure.lean) は、既存の命令の入力側・出力側という指定を入れ替えた有限コードへ、実行契約と制御証明を移します。論理的な結果と実際の使用時間の同時分布を保持し、物理的な入口・出口は両テープを入れ替えた関係で証明します。実行途中にテープ全体を交換する操作は追加しません。コードの命令数は保持しますが、符号化したコードのビット長が等しいとは主張しません。保存量は変換後のコード自体を数え直します。

[NativeBitstringRewind](Foundation/Crypto/Semantics/Machine/NativeBitstringRewind.lean) は、任意長の連続したビット列を左に走査して先頭へ戻す四命令の部品です。時間上界は `2n+4` 段階です。現在セルと右側の任意のセル、およびもう一方のテープを保持します。ビット列の直前は空白という入口条件があります。出力側で走査する部品も同じ証明から構成します。

[RetainedCopyRewind](Foundation/Crypto/Semantics/Machine/RetainedCopyRewind.lean) は、元のデータを保持するコピーと、コピー先の実際の巻き戻しを連結します。元のデータが n ビット、既存の前置きデータが h ビットの場合、固定十九命令、時間上界 `10n+2h+10` 段階で動きます。正確な全終了配置、実際の到達、元のデータの保持、全実行途中の保存量の多項式上界を証明します。出力ヘッドは前置きデータとコピーしたデータの先頭を指します。走査で表現に残った空白も終了配置に保持します。元の鍵の消去、マスク処理への入口の適合、公開実験全体の安全性への接続は引き続き別の証明です。

### 実際の消去と、余分な空白を持つ入口での実行

[NativeForwardErasure](Foundation/Crypto/Semantics/Machine/NativeForwardErasure.lean) は、現在位置から連続した n ビットを一セルずつ消し、その直後の空白で停止する五命令の部品です。時間上界は `4n+2` 段階です。左側の任意の保存セル、空白より右側の任意のセル、他方のテープを保持します。消したセルは空白として表現に残ります。正確な全終了配置と、全実行途中の保存量の多項式上界を証明します。テープ指定を変えた出力側の部品も構成できます。

[NativeEquivalentEntry](Foundation/Crypto/Semantics/Machine/NativeEquivalentEntry.lean) は、同じ各セルと制御状態を表す別の入口配置で、任意の既存の部品を実行します。実際の配置から元のコードを実行し、その全終了配置の分布を保持します。表現上の空白の個数に依存しない観測と事後条件は、元の部品の証明から導けます。時間上界は元の上界を使い、保存量は実際の入口の表現セル数で評価します。空白を取り除く無料の操作は導入しません。

[RetainedCopyCleanup](Foundation/Crypto/Semantics/Machine/RetainedCopyCleanup.lean) は、コピー・コピー先の巻き戻し・コピー元の消去を連結します。元のデータが n ビット、前置きデータが h ビットなら、固定二十七命令、時間上界 `14n+2h+13` 段階です。コピー元の各セルが空白になり、コピー先の全テープが保持されることを証明します。全実行途中の保存量にも多項式上界があります。

[PreparedBlockMask](Foundation/Crypto/Semantics/Machine/PreparedBlockMask.lean) は、この準備処理と、テープ指定を変えたマスク処理を接続します。同長 n ビットの鍵とメッセージについて、固定六十七命令、時間上界 `42n+24` 段階で、入力側のテープに鍵とメッセージの排他的論理和を返します。実際の到達、全状態分布、および全実行途中の保存量の多項式上界を証明します。入口では鍵と区切り付き要求が既に物理的に置かれていることを要求します。マスク処理後も、出力側の作業テープに要求と鍵が残ります。公開の攻撃者へその全状態を渡せるという安全性は主張しません。鍵の生成や要求の作成から始める公開実験全体の有限コード化と安全性への接続は残ります。

### 終了配置の関係を次の部品と観測へ引き継ぐ規則

[NativeRepresentationRelation](Foundation/Crypto/Semantics/Machine/NativeRepresentationRelation.lean) は、全配置のセルの同値関係の推移、命令位置とテープ指定の変更との対応を公開します。既存の部品の標準の結果が一つなら、実際の別の表現での全結果がその出口と同じセルを表すことも導けます。

[NativeEquivalentComposition](Foundation/Crypto/Semantics/Machine/NativeEquivalentComposition.lean) は、実際の前の結果が次の部品の入口と同じセルを表すとき、その部品を連結します。前の結果の実際のテープから次の元のコードを実行します。追加するのは既存の連結用の制御命令だけで、正規化や支持集合の検査を行う実行時の命令は追加しません。次の論理入力を前の結果に応じて変えることもできます。

[NativeBackwardErasure](Foundation/Crypto/Semantics/Machine/NativeBackwardErasure.lean) は、ビット列の直後から左向きに一セルずつ消す既存の五命令を部品にします。n ビットの時間上界は `4n+3` 段階です。直前の空白を越えた保存領域、右側の保存セル、他方のテープを保持します。入力側で消す部品と、全保存領域を数えた保存量の多項式上界も公開します。

[CleanBlockMask](Foundation/Crypto/Semantics/Machine/CleanBlockMask.lean) は、マスク処理後に要求と鍵の作業領域を実際に消去します。固定七十五命令、時間上界 `54n+32` 段階です。暗号文を保持し、作業テープの全セルが空白になることを証明します。全実行途中の保存量にも多項式上界があります。空白の有限表現そのものは残ります。

[NativeContinuationObservation](Foundation/Crypto/Semantics/Machine/NativeContinuationObservation.lean) は、全配置の関係から、任意の有限の実機コードを続けたときの観測分布を論理結果の分布で表します。観測はセルの同値関係に対して不変であることを要求します。[CleanBlockMaskObservation](Foundation/Crypto/Semantics/Machine/CleanBlockMaskObservation.lean) は、消去後の実際の全配置からの後続処理が、暗号文だけを持つ標準の入口からの処理と同じ観測分布になることを証明します。暗号文のヘッドは末尾にあり、先頭へ移すには実際の巻き戻しが必要です。有限表現の符号化を任意に検査する攻撃者や、時間・保存量の全てを含む公開実験の安全性への接続は、この観測定理だけの結論ではありません。

### 使用時間との相関と、平文からの要求・鍵生成

[NativeCostedContinuation](Foundation/Crypto/Semantics/Machine/NativeCostedContinuation.lean) は、後続の実機による観測と前段の契約が報告する時間の同時分布を、論理結果と時間の同時分布から記述します。時間を忘れず、秘密や結果との相関を保持します。報告時間での実際の到達は、前段の到達証明で別に保証します。使用時間が秘密と独立だという安全性を仮定なしに導く規則ではありません。セルの同値関係による部品の再利用も、ランダムな標準結果を持つ部品について、実際の全結果に対応する標準の出口が存在することを導けるようにしました。

[NativeRequestGeneration](Foundation/Crypto/Semantics/Machine/NativeRequestGeneration.lean) は、任意の保存済みの入力・出力のビット列を伴う二つの部品を提供します。区切り付き要求の書込みは固定十五命令、時間上界 `8n+4` 段階です。乱数ビットの追加は既存の固定六命令を使い、時間上界 `5n+2` 段階です。入力の各ビットを長さの目印として使い、既存の出力の末尾へ一様な n ビットを追加します。全配置の分布と、追加した鍵を論理的に読むと一様分布になることを証明します。

[GeneratedRequest](Foundation/Crypto/Semantics/Machine/GeneratedRequest.lean) は、平文だけの入口から要求を書き、保存した平文を巻き戻し、その長さの一様な鍵を要求の末尾へ追加します。固定三十一命令、時間上界 `15n+12` 段階です。鍵の一様分布と、実際の終了配置の両テープの関係を証明します。[NativeRequestResources](Foundation/Crypto/Semantics/Machine/NativeRequestResources.lean) は、二つの単独部品について保存済みの全データを含めたサイズ、組立後は平文長による、全実行途中の保存量の多項式上界を与えます。組立後も元の平文と生成した鍵は保持されています。平文の消去、要求と鍵の巻き戻し、マスク処理への接続と公開実験全体の安全性の証明は続きの構成です。


### 平文から消去後の暗号文までの実行と完全秘匿性

[NativeEquivalentObservation](Foundation/Crypto/Semantics/Machine/NativeEquivalentObservation.lean) は、連結した部品の観測分布を元の部品の分布から導く共通規則です。実際の配置からコードを続け、各セルと制御状態が同じ配置では値が変わらない観測について、確率の重みを含む分布の等式を証明します。

[GeneratedMaskPreparation](Foundation/Crypto/Semantics/Machine/GeneratedMaskPreparation.lean) は、要求と一様な鍵の生成後に元の平文を消し、要求と鍵を実際に巻き戻します。[GeneratedBlockEncryption](Foundation/Crypto/Semantics/Machine/GeneratedBlockEncryption.lean) はマスク処理と作業領域の消去を追加します。入口には平文だけを置きます。全体は固定94命令、n ビットについて時間上界 `61n+40` 段階です。暗号文は入力側のテープに残り、作業テープは全セルが空白になります。[GeneratedEncryptionResources](Foundation/Crypto/Semantics/Machine/GeneratedEncryptionResources.lean) は、実際の全実行途中についてコードと配置の保存量の多項式上界を証明します。

[GeneratedEncryptionSecrecy](Foundation/Crypto/Semantics/Machine/GeneratedEncryptionSecrecy.lean) は、一様な鍵を一度だけ使うワンタイムパッドの完全秘匿性へ接続します。同じ長さの任意の二つの平文について、暗号文の分布が一致します。任意の有限の実機コードを終了配置から続けた場合も、上記のセルの同値関係に対して不変な観測の分布が一致します。暗号文のヘッドは末尾にあります。使用時間や有限表現の符号化そのものを公開する安全性、多項式時間の攻撃者を含む公開実験との接続は別の証明です。


`NativeContinuationSecurity.continuation_eq_of_view_eq` は暗号方式に依存しない規則です。任意の部品について、二つの入力の論理的な観測結果の分布が一致し、各物理的な出口がその観測結果だけの入口と同じセルを表すなら、任意の有限の後続コードによる観測の分布も一致します。ワンタイムパッドの `native_perfect_secrecy` はこの共通規則を使います。`run_ciphertext_uniform` と `run_native_perfect_secrecy` は契約上の分布だけでなく、平文だけの入口から94命令のコードを実行した分布について直接述べます。後続処理への命令位置の変更は呼出し境界の記述であり、コードを物理的に連結するときの制御と時間は既存の連結規則で計上します。


### 時間を含む観測と定量的な安全性の移送

[ObserverBound](Foundation/Crypto/Semantics/Probability/ObserverBound.lean) は指定した観測者の集合について識別差の上界を表し、合成した観測者の所属証明から確率的な後処理へ上界を移します。[NativeTimedObservationSecurity](Foundation/Crypto/Semantics/Machine/NativeTimedObservationSecurity.lean) は、前段の報告時間に応じて後続のコード・実行段階数・観測を選ぶ場合にも、論理結果と時間の同時分布から観測の一致や上界を導きます。[ProcedureCostObservation](Foundation/Crypto/Semantics/ProcedureCostObservation.lean) は、報告時間が全結果で同じという仮定を使う場合を整理します。同じ時間上界だけでは十分ではありません。

[NativeBoundaryObservation](Foundation/Crypto/Semantics/Machine/NativeBoundaryObservation.lean) は、実際の機械について、セルが同じ配置からの停止条件への到達時間と終了状態の同時観測を移します。[NativeBoundaryContinuation](Foundation/Crypto/Semantics/Machine/NativeBoundaryContinuation.lean) は前段の報告時間と後段の実際の使用時間の両方を観測する場合へ接続します。段階数を使い切った結果も保持し、成功した停止には別の完了証明を要求します。[TimeObservation](Foundation/Examples/TimeObservation.lean) は出力の一致だけでは時間を含む安全性が導けない反例です。観測者の効率、前段の報告時間での実際の到達、暗号化処理そのものの時間を含む安全性は、それぞれ別に証明する必要があります。


### 既存の部品から実際の停止時間を保持する部品への再利用

[NativeFirstArrival](Foundation/Crypto/Semantics/Machine/NativeFirstArrival.lean) の `NativeComponent.firstArrival` は既存のコード・入口・時間上界を変更せず、最初に停止した全配置と実際の使用時間を保持する部品を構成します。停止後の余分な実行段階を使用時間へ加えません。報告時間での到達、全結果での停止、実際の時間による終了時の保存量を証明します。同じセルを表す別の入口での再利用も、観測と実際の時間の同時分布を保持します。

[BoundaryStability](Foundation/Crypto/Semantics/BoundaryStability.lean) は、全結果が停止条件へ到達する十分な上界なら、解析用の段階数を増やしても全終了状態と実際の使用時間の分布が変わらないことを示します。[NativeFirstArrival の例](Foundation/Examples/NativeFirstArrival.lean) は、契約が一律4段階を報告する部品から、乱数による3段階・4段階の停止を復元します。[GeneratedEncryptionFirstArrival](Foundation/Crypto/Semantics/Machine/GeneratedEncryptionFirstArrival.lean) は94命令の暗号化処理へ適用します。暗号文と実際の時間の相関を保持して後続の観測へ接続します。この同時分布が同長の平文間で一致することは、後述の GeneratedEncryptionExactTime で証明しました。


`NativeComponent.firstArrival_costed_eq_of_code_entry` は、同じコードと同じ入口を証明する二つの停止契約について、論理結果の型や上界が違っても実際の停止状態と時間の分布が一致することを保証します。


### 正確な停止時間を局所的な遷移条件から証明する規則

[ExactBoundaryClock](Foundation/Crypto/Semantics/ExactBoundaryClock.lean) は、有効な状態では停止条件と残り時間ゼロが一致し、停止前の全ての遷移で残り時間がちょうど1減るという証明をまとめます。十分な実行段階数について、全結果が停止条件へ到達し、実際の使用時間が入口の残り時間と一致することを導きます。[NativeExactClock](Foundation/Crypto/Semantics/Machine/NativeExactClock.lean) は既存の部品の最初の停止を保持する契約へ接続し、実際の固定時間と論理的な観測結果の分布の一致から、時間を見て後続コードを選ぶ観測の一致を導きます。各セルが同じ別の入口での再利用にも、実際の固定時間を移せます。

[ExactClockTransport](Foundation/Crypto/Semantics/ExactClockTransport.lean) は、状態の可逆な対応が各遷移とその確率を一対一に保つ場合に、この証明を移します。[NativeExactClockSwap](Foundation/Crypto/Semantics/Machine/NativeExactClockSwap.lean) はテープ指定を入れ替えたコードへ適用します。実行時の時計やテープ交換は追加しません。

[RewindExactClock](Foundation/Crypto/Semantics/Machine/RewindExactClock.lean)、[ForwardErasureExactClock](Foundation/Crypto/Semantics/Machine/ForwardErasureExactClock.lean)、[BackwardErasureExactClock](Foundation/Crypto/Semantics/Machine/BackwardErasureExactClock.lean) は既存の巻き戻し・前向き消去・後ろ向き消去について、正確な全終了配置と実際の使用時間の同時分布を証明します。長さ n について、それぞれ `2n+4`、`4n+2`、`4n+3` 段階です。各処理の契約で許す任意の保存領域の内容に依存せず、反対側のテープを処理する版にも適用します。[ExactClockRejection](Foundation/Examples/ExactClockRejection.lean) は、乱数で3段階・4段階に分かれる既存のコードが、4段階以内で止まるというだけではこの一定時間の条件を満たさないことを検証します。94命令の暗号化処理全体への接続は、後述の GeneratedEncryptionExactTime で証明しました。


### 乱数生成と要求の書込みの正確な実行時間、実行手順の証明の再利用

[TapeBitSpan](Foundation/Crypto/Semantics/Machine/TapeBitSpan.lean) は現在位置から最初の空白までのビット数を数える共通定義です。[SamplerExactClock](Foundation/Crypto/Semantics/Machine/SamplerExactClock.lean) は既存データの末尾へ n ビットの乱数を追加する処理が、乱数やデータの値によらず正確に `5n+2` 段階で停止することを証明します。全終了状態と実際の時間の同時分布、追加した一様な鍵と一定時間との同時分布を保持します。同じセルを表す実際の別の入口でも、鍵と時間の分布を再利用できます。[RequestExactClock](Foundation/Crypto/Semantics/Machine/RequestExactClock.lean) は区切り付き要求の書込みについて正確な `8n+4` 段階と全終了状態を証明します。両方とも入口の既存データを許します。

[NativeTraceTime](Foundation/Crypto/Semantics/Machine/NativeTraceTime.lean) は、実際の命令遷移を列挙した既存の証明から、乱数命令のないコードの実行時間を導きます。終点が停止状態なら遷移数が最初の停止までの実際の時間になります。停止後の空回りはこの証明形式には含まれません。巻き戻しの全終了状態と時間の定理は既存の実行手順の証明へ接続しました。一般の確率的なコードには、引き続き全乱数分岐を扱う時計などの証明を使います。マスク処理と連結による全体の正確な時間は、後述の隣接時刻の規則と NativeAppendFirstArrivalTime で証明しました。


### 単独実行の正確な時間を呼出しと連結へ移す規則

[BoundaryInvariantSimulation](Foundation/Crypto/Semantics/BoundaryInvariantSimulation.lean) は、有効な状態と停止前の支持集合上での遷移の対応だけから、全状態と実際の到達時間の同時分布を移します。[ClosedSubroutineArrival](Foundation/Crypto/Semantics/Machine/ClosedSubroutineArrival.lean) は既存の呼出し用コードへ適用します。元の停止命令が戻り先へのジャンプになる1段階も含め、任意の有限の段階数で到達状態と時間を保ちます。

[NativeInvocationTime](Foundation/Crypto/Semantics/Machine/NativeInvocationTime.lean) は部品の制御証明を再利用し、単独実行の最初の停止の分布を呼出しの最初の戻りの分布へ移します。時計から得た固定時間も使えます。[NativeLinkArrivalTime](Foundation/Crypto/Semantics/Machine/NativeLinkArrivalTime.lean) は既存の型付きの結果復元と連結へ接続します。[NativeLinkFixedTime](Foundation/Crypto/Semantics/Machine/NativeLinkFixedTime.lean) は連結した契約の時間を、前段の戻り時間と後段の戻り時間の和に最後の停止1段階を加えた値として導きます。

[GeneratedRequestExactTime](Foundation/Crypto/Semantics/Machine/GeneratedRequestExactTime.lean) は要求の書込みと巻き戻しを連結した実行契約について、正確な全終了状態と報告時間 `10n+9` 段階の同時分布を証明します。各呼出しの実際の戻り時間を使い、制御を無料にする規則は追加しません。

[ProcedureFixedTime](Foundation/Crypto/Semantics/ProcedureFixedTime.lean) は一定の報告時間が契約の上界以上なら、その時刻での全状態の実行分布を導きます。途中の終了状態が吸収的である必要はありません。[BoundaryExactTime](Foundation/Crypto/Semantics/BoundaryExactTime.lean) は停止後に状態が変わらない機械について、ある時刻の全結果が停止し、その1段階前の全結果が未停止なら、最初の停止時刻がその時刻と一致することを証明します。全終了状態と実際の時間の同時分布も保ちます。

[NativeLinkFirstArrivalTime](Foundation/Crypto/Semantics/Machine/NativeLinkFirstArrivalTime.lean) はこの規則を既存の連結へ適用します。各呼出しの時間が一定で、その和が連結本体の契約上界以上なら、連結契約と最初の停止の同時分布が一致します。最後の停止命令1段階を含みます。GeneratedRequestExactTime はこれを二重の連結へ再利用し、要求の書込み・巻き戻し・乱数生成からなる31命令のプログラムの最初の停止が `15n+12` 段階であることと、一様な鍵とその時間の同時分布を証明します。94命令の暗号化全体の時間を含む安全性は次節で証明しました。余裕のある契約上界や可変時間での連結への一般化は、後述の NativeLinkFirstArrival で証明しました。


### 準備・暗号化・消去の実際の時間を含む秘密性

[NativeAdjacentTime](Foundation/Crypto/Semantics/Machine/NativeAdjacentTime.lean) は、停止直前の未停止の実行分布と次の停止分布から、部品の最初の停止時間を導きます。証明に使う上界が実際の時間より大きい場合も使えます。[FlaggedBlockXorExactTime](Foundation/Crypto/Semantics/Machine/FlaggedBlockXorExactTime.lean) は既存のマスク処理の各段階の実行証明を再利用し、全終了状態と正確な `24n+8` 段階の同時分布を示します。

[NativeFirstArrivalTimeTransport](Foundation/Crypto/Semantics/Machine/NativeFirstArrivalTimeTransport.lean) は、時計・実行列・隣接時刻のいずれで証明した実際の時間でも、同じセルを表す別の入口と、テープ指定を交換したコードへ移します。[NativeAppendFirstArrivalTime](Foundation/Crypto/Semantics/Machine/NativeAppendFirstArrivalTime.lean) は、既存の連結の後ろへ部品を追加する共通規則です。実際に受け継ぐテープから実行し、前段の結果に依存する後段の入力を許します。実際の一定時間を元の部品から移す規則を備えます。後述の NativeLinkFirstArrival により、本体上界が実際の時間より大きい場合も扱えるようにしました。

[GeneratedMaskPreparationExactTime](Foundation/Crypto/Semantics/Machine/GeneratedMaskPreparationExactTime.lean) は平文消去まで `19n+16`、要求・鍵の巻き戻しまで `25n+23` 段階を証明します。[GeneratedEncryptionExactTime](Foundation/Crypto/Semantics/Machine/GeneratedEncryptionExactTime.lean) はマスク処理まで `49n+32`、最後の作業領域消去まで `61n+40` 段階を証明します。いずれも最初の停止までの実際の段階数です。空入力と全乱数分岐を含み、既存の94命令のコードを変更しません。

`arrival_ciphertext_time_uniform` は実際の暗号文と停止時間の同時分布が、一様な暗号文と `61n+40` 段階の組に一致することを示します。`arrival_time_perfect_secrecy` は、停止時間を見て後続コード・実行上界・観測を選ぶ場合の観測分布が、同長の平文間で一致することを示します。`arrival_boundary_perfect_secrecy` は後段の実際の使用時間も観測できます。観測は、同じセル内容を表すテープの内部表現を区別しない条件を要求します。`run_arrival_ciphertext_time_uniform` は平文だけの実際の入口からコードを実行した分布について直接述べます。可変時間の有限な連結は次節で証明しました。生の符号化に含まれる配置情報の秘密性と、標準的な確率的多項式時間攻撃者のクラスとの対応は残っています。


### 可変時間と余裕のある上界を許す最初の停止の合成

[BoundaryComposition](Foundation/Crypto/Semantics/BoundaryComposition.lean) は、前段の終了条件までの実際の到達と、その終了状態から後段の終了条件までの実際の到達を合成します。前段の終了前には後段の終了条件に到達しないことを、保存される状態の条件から証明します。両段階の完了を別々に要求し、実行上界の枯渇を到達と扱いません。使用時間は分岐ごとに加算し、未使用の上界は加算しません。途中の終了状態で機械が停止し続ける必要はありません。

[NativeInvocationComposition](Foundation/Crypto/Semantics/Machine/NativeInvocationComposition.lean) は実際の呼出し用コードへこの規則を適用します。[NativeLinkFirstArrival](Foundation/Crypto/Semantics/Machine/NativeLinkFirstArrival.lean) の `firstArrival_costed_eq` は、任意の既存の有限な部品連結について、連結契約が報告する全終了状態・時間の同時分布が、最初の停止の同時分布と一致することを示します。各部品の時間が入力や乱数で変わってもよく、契約上界に余裕があっても適用します。`firstArrival_costed_from_components` は元の各部品の最初の停止の同時分布から全体の分布を直接導きます。前段の結果に応じた後段の入力と、状態・時間の相関を保持します。最後の呼出し元の停止命令1段階も数えます。

`appendEquivalent_firstArrival_fixed_time_of_sources` は、元の各部品が一定時間である場合の追加連結について、本体上界が実際の時間以下という以前の条件を不要にします。以前の規則は互換用に保持します。[NativeVariableTimeLink](Foundation/Examples/NativeVariableTimeLink.lean) は前段の上界9段階、後段の上界7段階を使い、連結上界17段階に対して実際の最初の停止が5段階または6段階となる同時分布を証明します。元の前段は乱数で3段階または4段階となり、後段は1段階で停止します。上界までの空回りを実際の時間に混ぜないことを検証します。可変時間を保持すること自体は、その時間から秘密が漏れないという主張ではありません。安全性には観測する結果と時間の同時分布を使います。


### セル内容・有限表現の配置・時間を一緒に観測する規則

[RepresentationLayout](Foundation/Crypto/Semantics/Machine/RepresentationLayout.lean) は、各テープのヘッドの左右に表現されたリストの長さを記録します。同じセル内容を表す状態とこの配置情報から、実際の有限な状態を完全に復元できることを証明します。命令位置と停止フラグも、元のセル内容の同値関係が保持する情報です。復元は数学的な関数であり、実行時の無料の正準化を追加するものではありません。

[NativeRepresentationObservation](Foundation/Crypto/Semantics/Machine/NativeRepresentationObservation.lean) は、公開する値・実際の配置・時間の同時分布から、完全な有限表現を区別する任意の観測へ接続します。以前の「同じセル内容を表す内部表現を区別しない」という観測側の条件は要求しません。代わりに配置情報を隠さず同時分布へ含めます。配置が公開する値だけから決まると別途証明できれば、公開する値と時間の安全性から完全な状態を観測する安全性を導けます。定量的な識別優位性の規則では、合成した観測の攻撃者クラスへの所属を明示的に要求します。符号化の実行時間や効率性をこの数学的な復元だけから推測しません。

[RepresentationLeakage](Foundation/Examples/RepresentationLeakage.lean) は、セル内容も実際の停止時間1段階も同じなのに、空白のリスト長だけが入力ビットを保持するネイティブな反例です。完全な状態の復号可能な符号化を観測すると、そのビットを完全に区別できます。具体的な暗号化方式の反例ではなく、配置情報を消してよいと推測できないことを検証します。

[GeneratedEncryptionRepresentation](Foundation/Crypto/Semantics/Machine/GeneratedEncryptionRepresentation.lean) は94命令の暗号化へ接続します。暗号文・配置・実際の停止時間が、完全な終了状態とその符号化を決定することを証明します。`arrival_encoded_secrecy_of_public_layout` は配置が公開暗号文から決まるという追加条件の下で、符号化と時間の秘密性を導きます。任意長の配置条件と全状態・時間の秘密性は、その後に追加した [GeneratedEncryptionPhysical](Foundation/Crypto/Semantics/Machine/GeneratedEncryptionPhysical.lean) で証明しています。

[GeneratedEncryptionLayoutCheck](Foundation/Examples/GeneratedEncryptionLayoutCheck.lean) は平文長0〜4について全平文と全乱数分岐を探索し、実際の終了配置の四つのリスト長と停止時間を検査します。不一致はビルドを失敗させます。入力テープの左右の長さは n と1、出力テープは0と `3n+2` でした。この有限検査に加え、現在は任意長の配置の証明もあります。


[NativePadPhysicalPreparation](Foundation/Crypto/Semantics/Machine/NativePadPhysicalPreparation.lean) は、任意の生成・入力準備の実装を、マスクによる暗号化・消去・符号化・識別へ接続します。実際に残った空白セルを保持し、準備から始まる全体の時間と保存量を評価します。[PRGNativePipeline](Foundation/Constructions/Symmetric/PRGNativePipeline.lean) は生成器の実装条件から安全性の帰着を移します。[PRGNativeReduction](Foundation/Constructions/Symmetric/PRGNativeReduction.lean) は受領済みの生成器出力と公開メッセージから始まる帰着について、入力準備を含む固定コードと資源上界を構成します。暗号化側の具体的な生成器の実装証明と、外部への問い合わせを含む攻撃者クラスへの登録は、まだ必要です。帰着側の入力準備は後述の具体的なコードで実装しています。

[NativePadPipelineObservation](Foundation/Crypto/Semantics/Machine/NativePadPipelineObservation.lean) と [NativePadPhysicalObservation](Foundation/Crypto/Semantics/Machine/NativePadPhysicalObservation.lean) は、暗号文と準備の実際の時間の同時分布から、識別処理後の状態と総時間の観測へ接続します。有限表現まで一致する準備条件なら完全な状態を扱えます。空白を保持する弱い条件では、同じセル内容を表す状態を区別しない観測を扱います。


[PRGNativeReductionConcrete](Foundation/Constructions/Symmetric/PRGNativeReductionConcrete.lean) は、帰着側の入力準備を具体的な62命令の固定コードで実装します。公開パラメータ、平文と受領済みの生成器出力から、元入力の消去・暗号化・符号化・識別を実行します。全体は元の識別コードに157命令を加えた長さです。生成器の出力長が多項式なら、準備を含む時間と全実行途中の記憶量も多項式で抑えられます。利用者に帰着側の入力準備の実装証明を要求しません。外部への問い合わせと応答の受領、および暗号化側の具体的な生成器の評価は、引き続き別の接続証明が必要です。


[DelimitedResponseLoading](Foundation/Crypto/Semantics/Machine/DelimitedResponseLoading.lean) は、受信した生の応答を既存の公開入力の末尾へ、一セルずつ区切り付きで書き込みます。[NativeSingleChallengeControl](Foundation/Crypto/Semantics/Machine/NativeSingleChallengeControl.lean) は、問い合わせ・走査・読込み・巻き戻し・固定コードの実行を持つ共通制御です。全実行途中で問い合わせは高々一回であり、終了した実行ではちょうど一回であることを証明しています。[NativeResponsePacket](Foundation/Crypto/Semantics/Machine/NativeResponsePacket.lean) は各段階の実際のテープの受渡しを証明します。全制御の停止上界と判定分布を合成して、具体的な帰着の攻撃者クラスへ登録する証明は引き続き残っています。


任意長の擬似乱数生成器への帰着には、[公開入力から始める全実行](Foundation/Constructions/Symmetric/PRGNativeQueryExecution.lean) と [全実行途中の保存量](Foundation/Constructions/Symmetric/PRGNativeQueryResources.lean) を追加しています。外部問い合わせ、応答の実際の読込み、固定した入力準備・暗号処理・識別コードを接続します。[攻撃者クラスへの登録](Foundation/Constructions/Symmetric/PRGNativeQueryBackend.lean) は、同じ有限コードについて多項式時間、一回の問い合わせ、多項式の符号化保存量を同時に証明します。[安全性の移送](Foundation/Constructions/Symmetric/PRGNativeQuerySecurity.lean) は、この登録済みクラスに対する生成器の安全性から暗号化実験の安全性を導きます。公開入力と応答分布を固定する登録条件があり、秘密の補助入力は含めません。[共通の実行系](Foundation/Crypto/Logic/General/NativeSingleChallengeBackend.lean) と [保存量評価](Foundation/Crypto/Semantics/Machine/NativeSingleChallengeResources.lean) は方式に依存しません。具体的な生成器の評価実装と安全性、適応的な複数回の問い合わせ、単独のネイティブ命令列への平坦化は別途必要です。


複数回の実行については、[回ごとに異なる資源上界を持つ合成](Foundation/Crypto/Semantics/ProcedureScheduledIteration.lean) と、[固定した五命令で行う任意長の適応的な問い合わせ](Foundation/Crypto/Semantics/Oracle/AdaptiveBitstringLoopExecution.lean) を追加しています。具体例では応答が次の要求になります。任意回数の実際の停止、完全な履歴、[累積した実際の時間の分布](Foundation/Crypto/Semantics/Oracle/AdaptiveBitstringLoopCost.lean)、[全実行途中の符号化保存量](Foundation/Crypto/Semantics/Oracle/AdaptiveBitstringLoopResources.lean) を証明します。[問い合わせコードの構造的な符号化](Foundation/Crypto/Semantics/Oracle/StructuredCodeStorage.lean) と保存量の評価は、任意の有限問い合わせコードに再利用できます。具体的な複数回暗号方式の安全性と、一般の攻撃者の要求選択処理への接続は別途必要です。


[空白セルを保持する応答取り出し](Foundation/Crypto/Semantics/Machine/CellResponseExport.lean) と [ネイティブ部品からの配送契約](Foundation/Crypto/Semantics/Machine/NativeCellResponse.lean) は、有限テープの空白配置を正規化せずに、実際の暗号部品の出力を返します。到達可能な結果にだけ配置条件を要求し、応答長 s の配送を `3s+4` 遷移で実行します。[実際の入力配置への移送](Foundation/Crypto/Semantics/Machine/NativeCellResponseEquivalent.lean) は、セル内容が同じ入口に対し、応答と累積実行時間の同時分布を保存します。[毎回新しい鍵を生成する具体例](Foundation/Crypto/Semantics/Machine/FreshMaskResponse.lean) は、既存の94命令の暗号化を使い、幅 n の暗号文と実際の時間 `64n+44` の同時分布が平文に依存しないことを証明します。入口には平文が実際のテープ上にあることを要求します。要求の読み込み、呼び出し元への再読込み、および複数回の全実行への接続はこの契約より外側で数える必要があります。同じ鍵を再利用する暗号方式の安全性は主張しません。


[要求の読み込みを含む共通実行](Foundation/Crypto/Semantics/Machine/NativePacketService.lean) は、生の要求バッファからセルごとに書き込み、実際のテープを暗号部品へ渡します。準備と制御移譲は要求長 r に対して `3r+3` 遷移です。[新しい鍵で暗号化する適用例](Foundation/Crypto/Semantics/Machine/FreshMaskPacketService.lean) は、幅 n の生の入力から応答取り出しまで、実際の時間 `67n+47` と一様な暗号文の同時分布を証明します。[応答パケットを返す部品用の呼び出し制御](Foundation/Crypto/Semantics/Oracle/PacketResponseSource.lean) と [合成契約](Foundation/Crypto/Semantics/Oracle/PacketResponseService.lean) は、保持した状態、要求、完全な履歴と呼び出し元を引き継ぎます。[具体的な呼び出し元への返却](Foundation/Crypto/Semantics/Oracle/FreshMaskCallerService.lean) は、任意の生の要求について、暗号処理と応答の再読込みを含む時間を `70n+51` 遷移以下で抑えます。呼び出し元の次の命令は、この契約の後に実行します。要求を呼び出し元から書き出す処理と複数回の全実行は、次の契約で接続します。


[呼び出し元の共通実行契約](Foundation/Crypto/Semantics/Oracle/CallerRuntime.lean) は、要求を選ぶ実行、実際の制御移譲、停止の条件を、応答配送の実装から独立させます。[二つの既存実行系への適用](Foundation/Crypto/Semantics/Oracle/CallerRuntimeInstances.lean)、[一回の共通合成](Foundation/Crypto/Semantics/Oracle/CallerRound.lean)、[任意回数の共通合成](Foundation/Crypto/Semantics/Oracle/CallerExecution.lean) を証明しています。[実際の暗号部品を使う適応的な実行](Foundation/Crypto/Semantics/Oracle/FreshMaskAdaptiveExecution.lean) は、固定した五命令の呼び出し元で、前回の暗号文を次の要求に使います。幅 n、呼び出し回数 q の場合、要求の書出し、暗号部品への読込み、毎回の乱数生成・暗号処理・消去・書出し、呼び出し元への再読込みと、最後の実際の停止までを `q*(72n+58)+2` 遷移以下で実行します。全履歴と実際のカウンタ配置を保持し、呼び出し件数 q と停止を証明します。初期の要求と一進カウンタは所定のテープ配置にあることが前提です。この新しい部品込みの実行系の全実行途中の保存量は、次の共通規則で証明します。安全性帰着への登録は引き続き残ります。


[暗号部品の読み込みと応答取り出しの保存量](Foundation/Crypto/Semantics/Machine/NativePacketServiceResources.lean)、[呼び出し元全体の局所的な増加量](Foundation/Crypto/Semantics/Oracle/PacketResponseGrowth.lean)、[復号可能な全状態の符号化](Foundation/Crypto/Semantics/Oracle/PacketResponseEncoding.lean)、[全実行途中の共通上界](Foundation/Crypto/Semantics/Oracle/PacketResponseResources.lean) を追加しています。[実際の複数回の暗号処理への適用](Foundation/Crypto/Semantics/Oracle/FreshMaskAdaptiveResources.lean) は、元の五命令と暗号部品のコード、保持した呼び出し元、部品の両テープ、全バッファ、空白セル、完全な履歴と指定した外部状態を含む符号化長を、全ての支持される実行途中で評価します。一般の外部応答法則には状態増加と応答長の上界を明示します。外部応答を使わない実験の `peak_closed` はその仮定を必要としません。固定したコードについて、状態サイズ、呼び出し回数と幅などの資源プロファイルが多項式なら保存量も多項式です。今回の実行系の安全性帰着への登録と、実際の累積時間を観測に含める安全性の接続は引き続き必要です。

応答の実際の時間を扱う共通定理として、`CellResponseExportExactTime` と
`NativeCellResponseExactTime` を追加しています。任意の証明済みネイティブ部品について、
最初の応答返却時刻が部品の最初の停止時刻と物理的な応答取り出し時間の和になることを証明します。
解析用の時間上界を増やしても記録する返却時刻は増えません。

[残り遷移数による共通規則](Foundation/Crypto/Semantics/BoundaryCountdown.lean) は、境界前の各遷移が残りの数を正確に1減らすことから、最初の到達時刻と出口分布を導きます。[生の要求から最初の返却までの証明](Foundation/Crypto/Semantics/Machine/NativePacketServiceExactTime.lean) は、物理的な読込み、任意の暗号部品と応答取り出しを接続します。[呼び出し元への時間の移送](Foundation/Crypto/Semantics/Oracle/PacketResponseServiceExactTime.lean) は、契約費用が最初の応答準備完了時刻と一致する部品に適用できます。[実際の暗号部品への適用](Foundation/Crypto/Semantics/Oracle/FreshMaskCallerServiceExactTime.lean) は、幅 n の要求について、再開した呼び出し元と累積費用 `70n+51` の同時分布を証明します。複数回の全実行の最初の停止時刻と安全性帰着への登録は引き続き必要です。

[要求選択と応答の共通費用則](Foundation/Crypto/Semantics/Oracle/CallerRoundCosted.lean) は、要求・応答と実行時間の相関を保持して合成します。[最初の要求捕捉時間](Foundation/Crypto/Semantics/Oracle/SourcePrefixExactTime.lean) と [実際の適応的な一回の費用](Foundation/Crypto/Semantics/Oracle/FreshMaskAdaptiveRoundExactTime.lean) を証明しています。[任意回数の累積費用](Foundation/Crypto/Semantics/Oracle/FreshMaskAdaptiveExecutionCosted.lean) は、最終状態と費用 `q*(72n+58)+2` の同時分布を与えます。全体の最初の停止時刻との一致には、早い停止を除外する証明が引き続き必要です。

[呼び出し元の停止判定](Foundation/Crypto/Semantics/Oracle/PacketResponseTerminal.lean) と [全実行の最初の停止時刻](Foundation/Crypto/Semantics/Oracle/FreshMaskAdaptiveFirstHalt.lean) を追加しています。全実行の一遷移前にはまだ停止していないことを証明し、累積費用 `q*(72n+58)+2` が実際の最初の停止時刻に一致することを導きます。[公開の終状態と時間の安全性](Foundation/Crypto/Semantics/Oracle/FreshMaskAdaptivePublicSecurity.lean) は、少なくとも一回、新しい鍵で暗号化した後の最終的な呼び出し元の機械配置と停止時刻を見る任意の確率的な観測について、同じ幅の平文の非依存性を証明します。要求履歴や中間状態の全観測を含む主張ではありません。安全性帰着の論理への登録は引き続き残っています。

[最初の停止時刻を観測する共通登録](Foundation/Crypto/Logic/General/FirstArrivalObservedBackend.lean) は、終状態と実際の停止時刻の同時分布、全分岐の停止、および任意の全実行途中の保存量証明を安全性帰着の論理へ接続します。[実際の複数回暗号処理への登録](Foundation/Crypto/Logic/General/FreshMaskAdaptiveFirstArrivalBackend.lean) は、回数と幅の多項式上界から実行証明を構成します。保存量には呼び出し元と暗号部品のコード、全テープ、バッファと履歴を含みます。目標の暗号実験との一致を明示的に与えれば、少なくとも一回暗号化する今回の公開観測に対する識別優位が0であることを導けます。観測関数自体のプログラム実装費用を証明する登録ではありません。

[目標実験との一致も証明した具体例](Foundation/Examples/FreshMaskAdaptiveRegisteredSecurity.lean) は、公開事象に対する実際の確率差を目標の優位と定義し、時間・保存量付きの実行証明まで構成します。登録先との一致を追加の仮定として残しません。一般化を開始した時点の四つの接続要件と、確率・符号化・履歴・部品合成・停止・資源・論理への登録の対応は、[全体監査](docs/crypto-logic.md#再利用に向けた一般化の全体監査)に記録しています。
