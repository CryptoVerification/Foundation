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

意味論に依存しない論理の核を [理論提示と導出](Foundation/Logic/Presentation.lean) に配置しています。判断と推論規則を与えると、導出、仮定の置換、モデルへの解釈を構成できます。モデルは命題だけでなく数値や証明構造も保持します。置換の恒等則・結合則、解釈との整合性、自由な構文モデルへの解釈の一意性を証明しています。現在の暗号論理は `Crypto/Logic/Presented` でその具体例として再構成します。帰着コードは構文から直接生成し、安全性・資源・分布の意味は別に解釈します。移行の範囲とチェックポイントは [再構成の記録](docs/logic-reconstruction.md) を参照してください。

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

残る設計・実装課題の仕様は、[厳密 sampling と期待停止時間](docs/issue-specs/0002.md)、[素数位数の群表現と機械実装](docs/issue-specs/0003.md) に整理しています。[旧実行モデルの削除記録](docs/issue-specs/0001.md) には依存調査と削除範囲を記載しています。
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
