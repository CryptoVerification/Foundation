# Foundation

Lean 4 のライブラリです。Nix の開発用シェルで Lean と Lake（Lean のビルドツール）を利用できます。

## ディレクトリ構成

```text
Foundation/
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

今後の論理体系は `Crypto/Logic`、その健全性・完全性などの証明は `Crypto/Meta` を配置先とします。`Models`、`Theories`、`Zoo` は、それぞれモデルの具体化、暗号学的理論、証明済みの含意・同値・分離の整理に使う予定です。

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
