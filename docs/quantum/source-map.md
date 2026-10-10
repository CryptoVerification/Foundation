# 原典と Lean の対応

この対応表は、Heunen の原典の有限次元・基底選択済みの場合と、今回独自に再構成した等式論理を区別します。本文ページは指定 PDF の印刷番号です。PDF の通しページは本文ページに8を加えます。

名前はすべて `Foundation.Quantum` 名前空間内です。各ファイルへのリンクはこのリポジトリ内を指します。

| 原典の参照 | Lean の宣言と所在 | 対応の範囲・追加した設計 |
| --- | --- | --- |
| §2.1、§3.1 の fdHilb、例3.2.14 p.61 | [Space.lean](../../Foundation/Quantum/Space.lean) の `Space`、`Space.Basis`、[Finite.lean](../../Foundation/Quantum/Finite.lean) の `Op` | 単位、ビット、任意の有限次元、テンソルの型を構文として保持します。射は複素行列です。基底を選ぶ制限があります。 |
| §2.2 の対称モノイド圏 | [Category.lean](../../Foundation/Quantum/Category.lean) の `matrixCategory`、`matrixMonoidalStruct`、`MonoidalCategory Space` と `SymmetricCategory Space` のインスタンス | 合成、テンソル、結合子、単位子、交換を与え、自然性・五角形・三角形・六角形の整合性を証明します。 |
| ダガー、定義3.2.1 p.57、§3.2.10 p.59 | `Op.dagger`、`Op.conjugate`、`Op.dagger_dagger`、`Op.dagger_seq`、`Op.dagger_tensor` | ダガーは共役転置です。双対の基底を選んだ共役と区別します。 |
| 例3.2.14 p.61、式(2.18)、定義2.6.2 p.42 | `Op.cup`、`Op.cap`、`Op.snake_left`、`Op.snake_right`、[Structures.lean](../../Foundation/Quantum/Structures.lean) の `ExactPairing a a`、`RigidCategory Space` | 有限次元の自己双対表示です。カップは非正規化です。無限次元の恒等作用素から同じカップを作れるとは主張しません。 |
| 定義3.2.9 p.59 | `dagger_compact` | キャップのダガーと交換からカップが得られることを証明します。 |
| 定義3.3.4 p.68、例3.3.5 pp.68–69 | `ClassicalStructure`、`standardClassical`、`Op.copy`、`Op.erase`、`Op.copy_coassoc`、`Op.copy_comm`、`Op.copy_leftErase`、`Op.copy_rightErase`、`Op.copy_special`、`Op.copy_frobenius` | 正規直交基底をコピー・削除する具体的構造です。任意の古典構造が基底から生じるという分類定理は未実装です。 |
| 補題3.3.6 p.69 | `Op.cup_copy` | 標準基底の構造で、カップがコピーと削除のダガーの合成であることを証明します。任意の抽象古典構造についての一般化は未実装です。 |
| 定義3.3.7 p.69 | `IsMeasurement`、`Op.mix_dagger_epi`、`mix_isMeasurement` | 測定の条件は `m ∘ m† = id` です。具体的ゲート `Op.mix` は本実装の例で、原典の特定の測定角ではありません。 |
| 式(2.19)、定理3.3.9の証明 p.70 | `Op.name`、`Op.correlated_cup` | 行列に対する任意の `m` について `(conjugate m ⊗ m) cup = name (m ∘ m†)` を証明します。 |
| §3.3.8 p.69、図式(3.4) p.70 | [Syntax.lean](../../Foundation/Quantum/Syntax.lean) の `Term.correlated`、`Term.alice`、`Term.bob` | 型付きの操作構文です。二つの量子系に局所的な測定を適用し、それぞれ一方の古典出力を削除する操作を表します。 |
| 定理3.3.9 p.70 | `Proof.measuredCup`、`Proof.qkd`、`qkdConditional`、[Semantics.lean](../../Foundation/Quantum/Semantics.lean) の `qkd_correct` | 測定の等式を仮定した有限導出を実際に作ります。健全性で行列等式を得ます。任意のダガー対称モノイド圏への一般化は今回の結果に含みません。 |
| 原典の図式計算を独自に再構成 | `Equation`、`Law`、`Rule`、`presentation`、`Proof` | 等式の推論体系は独自設計です。原典にこの構文と規則がそのまま掲載されているとは主張しません。任意の真理を導入する規則はありません。 |
| 既存メタ論理への接続（独自設計） | `Term.eval`、`Equation.Valid`、`Law.valid`、`model`、`sound`、`interpretation_substitute` | `Foundation.Logic.Model` を実際に構成します。仮定置換は既存の `Derivation.substitute` と `eval_substitute` を再利用します。 |
| 導出済み規則の提供（独自設計） | [Derived.lean](../../Foundation/Quantum/Derived.lean) の `Derived.presentation`、`Derived.expansion`、`Derived.interpretation_expansion`、`Derived.expansion_substitute` | 一回の鍵配送の規則を、元の対象論理の複数の規則からなる導出へ展開します。既存の `Translation` の解釈と置換の保存を具体化します。 |
| fdHilb への具体的対応 | [Hilbert.lean](../../Foundation/Quantum/Hilbert.lean) の `HilbertSpace`、`Op.linear`、`Op.linear_injective`、`Op.linear_dagger`、`Op.linear_seq`、`qkd_hilbert` | mathlib の有限次元複素ヒルベルト空間への忠実な表示です。行列のダガーが実際の内積に関する随伴となります。原典の抽象ヒルベルト圏の埋め込み定理3.7.18ではありません。 |
| 本実装の検証例 | `qkdMix`、[QuantumLogic.lean](../../Foundation/Examples/QuantumLogic.lean) の `Examples.qkd_mix`、`Examples.measured_mix`、`Examples.alice_mix_value` | 複素振幅を持つ重ね合わせを生成するゲートについて、測定条件を証明した閉導出とその具体的な非零の解釈です。盗聴者を含む鍵配送プロトコル全体の証明ではありません。 |
| 本実装の区別を確認する例 | `Examples.classical_copy_not_clone`、`Examples.no_zero_identity`、`Examples.distinct_proofs` | 古典コピーの具体的な非複製例、偽の行列等式に閉導出がないこと、導出木の区別を確認します。一般的な量子複製不可能定理や完全性定理ではありません。 |

`Law.mixEpi` は名前を固定した具体的なゲートの等式です。任意の意味論上の証明を `Law` に渡すことはできません。その妥当性は `Op.mix_dagger_epi` で検証します。その他の変数ゲートの解釈は任意です。したがってモデルがすべての変数ゲートに測定条件を暗黙に仮定することもありません。

第一段階の有限導出の健全性は、極限を使う任意の量子推論体系の健全性を意味しません。第4章・第5章・無限次元への継続実装は、以下の追補と[拡張文書](extensions.md)を参照してください。

## 継続実装の対応表

以下の章・定理番号は Heunen の指定 PDF を指します。Watrous と明記した行は安全性に向けた追加数学です。対象論理の規則と具体的な暗号例は本実装の再構成です。

| 原典の参照 | Lean の宣言と所在 | 対応の範囲と制限 |
| --- | --- | --- |
| Watrous §2.1、密度演算子の定義2.5（本文p.62）、§2.2 | [States.lean](../../Foundation/Quantum/States.lean) の `Density`、`Kraus.linear`、`Kraus.completely_positive`、`Channel.run`、`Channel.seq` | 有限次元、有限クラウス族です。正値性・完全正値性・トレース保存を証明します。全完全正値写像の分類や無限次元のトレース級作用素は含みません。 |
| Watrous §2.3 の測定（本文pp.100以降） | [Effects.lean](../../Foundation/Quantum/Effects.lean) の `Effect.probability`、`probability_run`、[Instrument.lean](../../Foundation/Quantum/Instrument.lean) の `probability_sum`、`record` | 有限分岐の装置を独自に構成します。分岐状態は正規化前の状態です。Heunen 定義3.3.7のダガー全射と同じ定義ではありません。 |
| Watrous §2.1–2.2 の部分系の廃棄 | [PartialTrace.lean](../../Foundation/Quantum/PartialTrace.lean) の `discardRight`、`discardRight_apply` | 有限次元の部分トレースをクラウス族として実装します。古典構造の振幅の削除 `Op.erase` と区別します。 |
| Watrous §3.1・3.3 に動機を持つ追加設計 | [Distinguishability.lean](../../Foundation/Quantum/Distinguishability.lean) の `Approx`、`Adversary`、`Approx.pre/post/trans/seq` | 任意の有限補助系を含む、一回の使用の受理確率の差です。トレース距離・ダイヤモンドノルムとの同値性や、対話的な合成の定理を仮定していません。 |
| 独自に再構成した誤差の対象論理 | [SecuritySyntax.lean](../../Foundation/Quantum/SecuritySyntax.lean)、[Security.lean](../../Foundation/Quantum/Security.lean) の `Security.presentation/model/sound/interpretation_substitute` | 具体的な秘密性の規則はパウリ平均の計算から証明します。意味論上の任意の真理を規則に渡せません。変数は現在、同じ型への物理的チャネルに限定しています。 |
| 前段階の等式論理の意味保存（独自設計） | [CoherentBridge.lean](../../Foundation/Quantum/CoherentBridge.lean) の `coherent_action_sound`、`coherent_auxiliary_sound`、`approximate_of_coherent_eq` | 等しい行列は補助系を含む正値写像として等しく作用します。物理的チャネルへ移す際は等長性を別途要求します。 |
| 定理4.3.3 pp.111–112 | [Predicate.lean](../../Foundation/Quantum/Predicate.lean) の `Predicate.orthomodular` | 基底選択済みの有限複素ヒルベルト空間における部分空間の直交モジュラー則です。一般のダガー核圏の抽象定理ではありません。 |
| 定理4.4.2 pp.117–118 | `Predicate.existsAlong`、`Predicate.pull`、`Predicate.exists_pull` | 線形写像の像と逆像の随伴です。`PredicateLogic.Formula.existsAlong/pull` は前段階の操作項を実際に引数として使います。 |
| 命題4.4.16 pp.124–125 | `Predicate.sasaki_adjunction`、`hook_formula`、`andThen_formula` | 直交射影による像と逆像から佐々木随伴を構成し、束の表示との一致を証明します。 |
| 第4章を基に独自に再構成した対象論理 | [PredicateLogic.lean](../../Foundation/Quantum/PredicateLogic.lean) の `presentation/model/sound/interpretation_substitute`、[QuantumExtensions.lean](../../Foundation/Examples/QuantumExtensions.lean) の `mixTransport`、`mix_transport_interpreted`、`noncommuting_measurements` | 有限導出、仮定置換、具体的測定射に沿った述語輸送、非可換な射影の例を検証します。完全性や、全ての抽象モデルへの表現は含みません。 |
| 定義5.3.6 p.159、定理5.3.8 pp.159–160 の基礎となる構成 | [Contexts.lean](../../Foundation/Quantum/Contexts.lean) の `Bohr.Context`、`tautological`、`local_commutativity`、`inclusion_mul/star/norm` | 単位的 C*-代数の閉じた可換な部分代数の外部の図式です。関手と包含による演算保存を検証します。定理5.3.8の内部 C*-代数の全証明ではありません。 |
| §5.3 の内部論理に向けた命題論理の再構成 | `Bohr.Persistent`、`Persistent.implication_adjunction`、`Bohr.presentation/model/sound/interpretation_substitute`、[QuantumContexts.lean](../../Foundation/Examples/QuantumContexts.lean) の `excluded_middle_not_derivable` | 文脈の包含に沿う Kripke 意味論を構成します。具体的な ℂ×ℂ の文脈で排中律の非導出性を証明します。内部スペクトル・ゲルファント双対性・点の不存在の定理とは区別します。 |
| §3.1 の Hilb、§3.2 の随伴・核に関わる具体的ヒルベルト空間の追加基盤 | [Infinite.lean](../../Foundation/Quantum/Infinite.lean) の `double_orthogonal`、`kernel_adjoint`、`range_adjoint`、`finite_projection_limit`、`sequence_space_approximation` | 完備な複素内積空間と有界作用素を扱います。二重直交補と像には閉包が必要です。有限射影の収束は数学的な極限定理です。無限の導出木とは区別します。原典の抽象表現定理3.7.18を実装したものではありません。 |
| 定理4.4.2を閉部分空間の具体的モデルに適用 | [InfiniteLogic.lean](../../Foundation/Quantum/InfiniteLogic.lean) の `presentation/model/sound/interpretation_substitute`、`sequence_transport` | 存在輸送は像の閉包です。ℓ²(ℕ,ℂ) に解釈する実際の有限導出を構成します。無界作用素や無限次元の量子チャネルは含みません。 |
| 安全性基盤の具体的な検証例（追加数学） | [OneTimePad.lean](../../Foundation/Quantum/OneTimePad.lean) の `decrypt_encrypt`、`average_auxiliary`、`perfect_privacy` | 一様で独立な秘密鍵二ビットによる、一量子ビットの一回の暗号化です。補助系を含む平均の行列要素を直接計算します。Heunen §3.3 の量子鍵配送の安全性を証明したものではありません。 |
| 既存の暗号意味論への接続（独自設計） | [ProbabilityBridge.lean](../../Foundation/Quantum/ProbabilityBridge.lean) の `classicalOutcome_event`、`Adversary.experiment_acceptance`、`oneTimePad_existing_probability` | 既存の `ProbComp` と `probabilityGap` に測定・受理の確率を保存します。量子命令の実行時間・資源証明の登録は別の未達条件です。 |

今回の対象論理の判断は性質や誤差の証拠です。文脈中の証拠の再使用は、量子入力を複製する操作を与えません。導出木の等しさと、意味論の行列・確率・命題の等しさも別に扱っています。

## 全目標へ向けた継続実装

今回の目標は引き続き未達です。詳細な完了条件と未達の証明義務は [full-goal.md](full-goal.md) に記録しています。

| 原典・追加数学の参照 | Lean の宣言と所在 | 証明した範囲と残る義務 |
| --- | --- | --- |
| Heunen 定義5.3.6、定理5.3.8 pp.159–160、定理5.3.16 pp.162–163 の依存 | [ContextSpectrum.lean](../../Foundation/Quantum/ContextSpectrum.lean) の `Context.commCStarAlgebra/gelfand/restrict_comp/gelfand_naturality/transport_positiveOpen`、`SpectralOpen` | 局所の通常のスペクトル、自然性、正の観測の生成元、持続する開集合の外部の位相を構成します。内部の生成元・被覆によるロケールとの同値は未達です。 |
| 第5章の内部スペクトルの命題論理に向けた再構成 | [SpectralLogic.lean](../../Foundation/Quantum/SpectralLogic.lean) の `model/sound/interpretation_substitute` | 実際のスペクトルの開集合のフレームに解釈します。以前の文脈中の観測の有無のモデルとは別です。原典の内部言語全体の証明ではありません。 |
| 安全性に必要な追加作用素論 | [GeneralCP.lean](../../Foundation/Quantum/GeneralCP.lean) の `comp/amplification_positive/ofHom`、[GeneralCPLogic.lean](../../Foundation/Quantum/GeneralCPLogic.lean) の `model/sound/interpretation_substitute` | 一般の C*-代数上で完全正値性と合成、対象論理への接続を扱います。正常性・前双対・トレース保存は別の未達条件です。 |
| Hilb と安全性のために追加する核型作用素の構成 | [NuclearSeries.lean](../../Foundation/Quantum/NuclearSeries.lean) の `operator_hasSum/operator_apply/norm_operator_le/post_operator/operator_compact/summable_trace` | 絶対収束する階数1の級数を実際の作用素と結びつけます。表示のトレース式が収束します。表示・基底からの独立性は後述の `NuclearTrace.lean` に接続しました。トレースノルムとその完備性は未達です。 |
| 無限次元の追加具体例 | [GeometricOperator.lean](../../Foundation/Quantum/GeometricOperator.lean) の `geometricSeries_trace/geometricOperator_coordinate/geometricOperator_compact` | 平方可算列空間上の幾何級数の作用を検証します。トレース式は1です。一般の状態空間の完成の代替とは扱いません。 |
| BB84 に向けた追加数学 | [BB84Attack.lean](../../Foundation/Quantum/QKD/BB84Attack.lean) の `zeroZ_of_errors/zeroX_of_error/factorization/environmentState/environment_test_independent/environment_amplitude_bound` | 補助系を持つ一量子ビットへの等長攻撃について、零擾乱の場合の独立性と定量的振幅評価を証明します。有限長の BB84 全実験の秘密性は未達です。 |
| 量子操作の有限次元での拡張表示（追加数学） | [Dilation.lean](../../Foundation/Quantum/Dilation.lean) の `Channel.dilation_gram/dilated/discard_dilation` | 有限クラウス族の等長拡張と部分トレースによる元の操作の再現を証明します。一般の無限次元での表示定理は未達です。 |

| 原典・追加数学の参照 | Lean の宣言と所在 | 証明した範囲と残る義務 |
| --- | --- | --- |
| 追加する無限次元の作用素論 | [NuclearTrace.lean](../../Foundation/Quantum/NuclearTrace.lean) の `trace_double_summable/trace_diagonal/trace_independent`、[TraceClass.lean](../../Foundation/Quantum/TraceClass.lean) の `TraceClass.trace_eq_diagonal/trace_nonneg/trace_congr` | 二重和の絶対収束から和の交換を正当化し、表示と正規直交基底から独立なトレースを証明します。巡回性と線形性は下記の追加実装で証明しました。トレースノルムと完備性は未達です。 |
| 追加する無限次元の状態 | `TraceDensity`、`pureTraceDensity`、[InfiniteStates.lean](../../Foundation/Quantum/InfiniteStates.lean) の `geometricOperator_positive/geometricDensity/geometricDensity_coordinate` | 実際の正値作用素でトレース1の状態を構成します。幾何級数による具体例を含みます。一般の量子操作、有限射影によるトレースノルム収束は未達です。 |


| 原典・追加数学の参照 | Lean の宣言と所在 | 証明した範囲と制限 |
| --- | --- | --- |
| 安全性に必要な追加作用素論（Heunen の章の定理そのものではありません） | [NuclearAlgebra.lean](../../Foundation/Quantum/NuclearAlgebra.lean) の `pre_operator/add_operator/scale_operator/trace_cyclic`、[TraceAlgebra.lean](../../Foundation/Quantum/TraceAlgebra.lean) の `traceLinear/trace_conjugate/trace_conjugate_isometry` | 実際の作用素の線形構造・両側の合成での閉性・巡回性を証明します。トレースノルムと完備性は未達です。 |
| 無限次元操作の追加構成 | [HilbertChannel.lean](../../Foundation/Quantum/HilbertChannel.lean) の `positive_apply/trace_apply/run`、[HilbertChannelLogic.lean](../../Foundation/Quantum/HilbertChannelLogic.lean) の `model/sound/interpretation_substitute` | 任意の完備複素ヒルベルト空間、有限クラウス族です。正常完全正値写像の前双対による分類とは別です。対象構文は合成等式の独自設計です。 |
| 無限次元の独自具体例 | [Pinching.lean](../../Foundation/Quantum/Pinching.lean) の `coordinateSuperposition/coordinatePinching_coherence/coordinatePinching_changes_state` | 平方可算列空間上の正規化した状態を変える具体的な操作です。全操作の一般性をこの一例で代替しません。 |
| BB84 の追加構成。Heunen §3.3.8・定理3.3.9は基底相関の先行結果です。 | [BB84Basis.lean](../../Foundation/Quantum/QKD/BB84Basis.lean) の `hadamard_square/prepare/measurementEffect/matched_basis_correct` | 正規化した二つの相補基底の準備・測定と、攻撃のない場合の確率1の正しさです。原典の定理3.3.9を有限長安全性の定理として引用しません。 |
| BB84 の単一送信への追加補題 | [BB84Measurement.lean](../../Foundation/Quantum/QKD/BB84Measurement.lean) の `zError_probability/environment_joint_reduction`、[BB84Complementary.lean](../../Foundation/Quantum/QKD/BB84Complementary.lean) の `xPlusError_probability/environment_independent_of_tests` | 二つの基底の平方振幅の誤りを測定確率へ接続します。有限補助系の任意の等長攻撃を扱います。複数送信にまたがる一般攻撃・有限誤差・標本検査は未達です。 |
| 独自に再構成した BB84 の対象論理と検証例 | [BB84Logic.lean](../../Foundation/Quantum/QKD/BB84Logic.lean) の `complementaryProof/model/sound/interpretation_substitute`、[BB84Examples.lean](../../Foundation/Quantum/QKD/BB84Examples.lean) の `copyZ_xPlusError/copyZ_environment_readout/honest_proof_interpreted` | 三つの測定仮定から補助系の情報の独立性を導出します。実際の攻撃の例で計算基底だけでは秘密性が得られないことを確認します。有限長 BB84 の安全性の代替ではありません。 |

| 単一送信の零誤差の場合の追加秘密性 | [BB84KeyState.lean](../../Foundation/Quantum/QKD/BB84KeyState.lean) の `keyEnvironment/key_state_independent_of_tests/key_state_test`、`BB84Logic.idealKeyProof`、`BB84Examples.honest_ideal_key_interpreted` | 一様鍵と補助系の共同密度演算子を構成し、零誤差の三検査から独立な積状態との一致を証明します。対象論理から同じ等式を導出・解釈します。公開記録と中止を含む実験や一般の有限誤差は未達です。 |


| 原典・独自追加の位置付け | Lean の宣言と所在 | 証明した範囲と制限 |
| --- | --- | --- |
| 安全性のための追加測定構成 | [InstrumentOps.lean](../../Foundation/Quantum/InstrumentOps.lean) の `pre/amplify/amplify_pre_apply`、[InstrumentMarginal.lean](../../Foundation/Quantum/InstrumentMarginal.lean) の `amplify_probability/record_forget_marginal` | 任意の有限クラウス前処理と有限補助系を扱います。古典分岐と量子出力を保持します。無限次元の可算装置の構成ではありません。 |
| BB84 の独自実験構成。Heunen §3.3.8–3.3.9 は基底相関の先行結果です。 | [BB84Instrument.lean](../../Foundation/Quantum/QKD/BB84Instrument.lean) の `measurementRecord/signalRecord/signalOutcome_event/zError_outcome/xPlusError_outcome` | 実際の測定分岐・補助系の保持・既存の確率的実験への接続を証明します。標本検査・公開記録全体の実装とは別です。 |
| 独自に導いた有限誤差の追加数学 | [VectorEffect.lean](../../Foundation/Quantum/VectorEffect.lean) の `factor_contract/weight_sub_bound`、[BB84Vector.lean](../../Foundation/Quantum/QKD/BB84Vector.lean) の `correct_vector_distance`、[BB84FiniteError.lean](../../Foundation/Quantum/QKD/BB84FiniteError.lean) の `environment_test_bound_zero_one/environment_bound_of_tests` | 単一送信への等長攻撃について、補助系の次元に依存しない識別上界を証明します。係数の最適性は主張しません。原典の定理としてこの数値上界を引用しません。 |
| 独自の有限誤差推論体系と具体例 | [BB84ErrorLogic.lean](../../Foundation/Quantum/QKD/BB84ErrorLogic.lean) の `processedProof/model/sound/interpretation_substitute`、[BB84WeakAttack.lean](../../Foundation/Quantum/QKD/BB84WeakAttack.lean) の `xPlusError/leakage_positive/privacyError_lt_one/processed_proof_interpreted` | 三つの測定上界と後処理を解釈します。非零の誤り・漏洩がある具体的攻撃で1未満の上界を検証します。一般の複数送信の有限長安全性ではありません。 |
| 両基底の一様入力との追加対応 | [BB84AveragedError.lean](../../Foundation/Quantum/QKD/BB84AveragedError.lean) の `bitError_outcome/averaged_environment_bound/averaged_proof_interpreted` | 各基底の平均の真の誤答確率から識別上界を得て、対象論理の実際の導出へ接続します。有限標本の経験的な比率との高確率の評価は未達です。 |


| 原典・独自追加の位置付け | Lean の宣言と所在 | 証明した範囲と制限 |
| --- | --- | --- |
| BB84 の独自の列全体の実験 | [Qubits.lean](../../Foundation/Quantum/QKD/Qubits.lean) の `bitStringEquiv/blockGate_isometry`、[BB84Block.lean](../../Foundation/Quantum/QKD/BB84Block.lean) の `block_matched_correct/BlockAttack.outcome_event/record_forget` | 任意長の準備と測定、列全体への有限クラウス攻撃、補助系を保持した測定記録です。独立攻撃を仮定しません。原典の安全性定理として引用しません。 |
| 公開記録と生鍵の独自構成 | [ClassicalMap.lean](../../Foundation/Quantum/ClassicalMap.lean) の `classicalMap_quantum_marginal`、[DiscardMiddle.lean](../../Foundation/Quantum/DiscardMiddle.lean) の `discardMiddle_apply`、[BB84RawProtocol.lean](../../Foundation/Quantum/QKD/BB84RawProtocol.lean) の `publicState/abort_keys/tested_not_key/raw_keys_agree` | 基底照合、指定した標本、公開記録、中止と生鍵を実際のチャネルへ接続します。鍵の一致には未検査位置での一致を要求します。誤り訂正・秘密増幅は未実装です。 |
| 独自の古典標本評価 | [Sampling.lean](../../Foundation/Quantum/QKD/Sampling.lean) の `undetected_probability`、[SamplingBound.lean](../../Foundation/Quantum/QKD/SamplingBound.lean) の `experiment_bound`、[BB84Sampling.lean](../../Foundation/Quantum/QKD/BB84Sampling.lean) の `sampledErrors_bound/accepts_zero_undetected` | 任意の誤り配置と分布、新鮮な一様部分集合による零誤り検査の見逃し確率です。相補基底の未測定の位相誤りを推定する定理とは区別します。 |
| 独自の標本推論体系と共同攻撃の例 | [BB84SamplingLogic.lean](../../Foundation/Quantum/QKD/BB84SamplingLogic.lean) の `model/sound/interpretation_substitute/cnot_sample_interpreted`、[BB84BlockExamples.lean](../../Foundation/Quantum/QKD/BB84BlockExamples.lean) の `cnot_isometry/cnot_not_product/cnotAttack` | 非積の二信号操作を具体的チャネルとして構成し、標本上界の導出を解釈します。メタ論理の核は変更しません。最終鍵の秘密性の主張ではありません。 |
| 実際の受理と生鍵の正しさについての独自追加 | [BB84Sampling.lean](../../Foundation/Quantum/QKD/BB84Sampling.lean) の `badAccepted_bound/keyMismatch_bound`、[BB84SamplingLogic.lean](../../Foundation/Quantum/QKD/BB84SamplingLogic.lean) の `acceptedProof/correctnessProof/cnot_correctness_interpreted` | 実際の全測定結果と一様標本の実験について、零誤り検査の誤受理と生鍵不一致を条件付けずに評価します。誤り訂正前の弱い上界です。最終鍵の秘密性とは別です。 |


| 原典・独自追加の位置付け | Lean の宣言と所在 | 証明した範囲と制限 |
| --- | --- | --- |
| 独自の有限混合と観測の対応 | [Mixture.lean](../../Foundation/Quantum/Mixture.lean) の `mixture/mixture_observation/mixture_channel`、[RecordObservation.lean](../../Foundation/Quantum/RecordObservation.lean) の `recordEvent/Instrument.encoded_record_event` | 密度演算子の混合と任意の古典事象の物理的な測定を構成します。既存の確率的実行系と観測確率が一致します。原典の定理として引用しません。 |
| BB84 の独自の乱数化した実験 | [BB84Randomized.lean](../../Foundation/Quantum/QKD/BB84Randomized.lean) の `record/keyState/publicState/record_event/insufficient_abort` | 一様な入力・基底と一様な検査位置を含む共同状態です。標本数が不足する場合の中止を証明します。誤り訂正と秘密増幅は後続です。 |
| 生鍵の独自の弱い正しさ評価と推論体系 | [BB84RandomizedCorrectness.lean](../../Foundation/Quantum/QKD/BB84RandomizedCorrectness.lean) の `correctness/physical_correctness`、[BB84RandomizedLogic.lean](../../Foundation/Quantum/QKD/BB84RandomizedLogic.lean) の `correctnessProof/sound/interpretation_substitute/cnot_randomized_interpreted` | 全乱数を平均した零誤り検査での不一致確率を評価し、物理的状態と既存メタ論理に接続します。最終鍵の秘密性は未達です。 |
| 共同状態の独自の誤差合成 | [StateDistance.lean](../../Foundation/Quantum/StateDistance.lean) の `StateApprox.of_channel/trans/postprocess/mixture`、[StateDistanceLogic.lean](../../Foundation/Quantum/StateDistanceLogic.lean) の `processedMixtureProof/sound/interpretation_substitute/pad_processed_interpreted` | 任意の二値観測による状態の比較と、実際の分布の混合・物理的後処理を形式化します。具体的モデルは量子ワンタイムパッドです。これを BB84 の秘密性の代替にしません。 |


| 原典・独自追加の位置付け | Lean の宣言と所在 | 証明した範囲と制限 |
| --- | --- | --- |
| 無限次元操作のための追加解析学 | [NuclearMass.lean](../../Foundation/Quantum/NuclearMass.lean) の `mass_add/mass_post_le/trace_norm_le_mass`、[NuclearNorm.lean](../../Foundation/Quantum/NuclearNorm.lean) の `nuclearNorm/nuclearNorm_eq_zero_iff/nuclearNorm_add_le/nuclearNorm_smul/traceContinuous` | 全ての核型表示の質量の下限から実際の作用素のノルムを構成します。トレースを連続線形汎関数にします。スペクトルによるトレースノルムとの同値は後続です。 |
| 完備性と有限和近似の追加証明 | [NuclearFlatten.lean](../../Foundation/Quantum/NuclearFlatten.lean) の `flatten_mass/flatten_operator`、[TraceCompleteness.lean](../../Foundation/Quantum/TraceCompleteness.lean) の `summable_norm_imp_limit`、[TraceApproximation.lean](../../Foundation/Quantum/TraceApproximation.lean) の `partial_error/partial_tendsto/geometricDensity_norm/geometric_partial_error_exact/geometric_partial_tendsto` | 二重級数の絶対収束から、任意の完備複素ヒルベルト空間上の核ノルムの完備性を証明します。具体的な無限階数状態の有限和近似を含みます。一般の有限直交射影の近似とは区別します。 |
| 量子操作と対象論理への追加接続 | [TraceIdealNorm.lean](../../Foundation/Quantum/TraceIdealNorm.lean) の `norm_conjugate_le/conjugateContinuous`、[HilbertChannelNorm.lean](../../Foundation/Quantum/HilbertChannelNorm.lean) の `continuous/norm_apply_le/trace_continuous`、[HilbertContinuousLogic.lean](../../Foundation/Quantum/HilbertContinuousLogic.lean) の `sound/interpretation_substitute/eval_tsum/pinching_identity_interpreted/interpreted_pinching_changes` | 有限クラウス操作を連続線形写像として既存の有限メタ論理へ解釈します。具体的な無限次元状態を変えるモデルを含みます。正常性、一般の前双対、最適な縮小性は未達です。 |

## 第5章の生成関係と段階ごとのフレームの追補

次の本文ページには指定PDFの印刷番号を使います。構文と対象論理の規則は本実装の再構成です。

| 原典の参照 | Lean の宣言と所在 | 対応の範囲と制限 |
| --- | --- | --- |
| §5.2.10、式(5.3)–(5.8)、pp.152–153 | [SpectralGenerators.lean](../../Foundation/Quantum/SpectralGenerators.lean) の `Context.positiveOpen_neg_disjoint/neg_square/add_le/mul/regular`、既存の `positiveOpen_one` | 局所の通常のゲルファントスペクトルで生成関係を検証します。積と負の二乗は自己随伴元を要求します。その他の一部の局所等式は実部による解釈によって非自己随伴元にも拡張しています。自由フレームの普遍性は未証明です。 |
| §5.2.10を本実装のために再構成 | [SpectralGeneratorLogic.lean](../../Foundation/Quantum/SpectralGeneratorLogic.lean) の `Term/Rule/presentation/model/sound/interpretation_substitute/additionCoverProof/eval_transport` | 有限の導出と、特定の有理数の被覆を意味する項です。全ての意味論上の真理を導入する規則はありません。原典の構成的な生成理論の完全性とは区別します。 |
| 定理5.3.16(a,c,d)、pp.162–163 の外部の台と制限 | [SpectralStages.lean](../../Foundation/Quantum/SpectralStages.lean) の `StageFrame/stageRestriction/spectralFrameDiagram/stageRestriction_fiber/stage_outside` | 文脈以上に台を持つ開集合のフレームと、文脈の拡張による切り詰めです。内部の正則イデアルによる提示との同値は未達です。 |
| 外部フレームに付随する追加証明 | 同ファイルの `stage_himp_val/stageRestriction_himp`、[SpectralStageLogic.lean](../../Foundation/Quantum/SpectralStageLogic.lean) の `model/sound/interpretation_substitute/eval_restrict/sound_restrict` | 台に相対的な含意と、その制限による保存です。既存の命題論理を段階ごとに解釈します。任意の連続写像の逆像による含意の保存を主張しません。 |
| 本実装の外部フレームの生成定理 | [SpectralExtension.lean](../../Foundation/Quantum/SpectralExtension.lean) の `extendLocal/extendLocal_fiber_self/liftLocal_le_iff/spectralOpen_generated` | 局所の開集合の将来への拡張と、任意の外部の開集合の局所の値からの生成です。原典の正則イデアルの構成的な普遍性の代用ではありません。 |
| 生成論理と段階の接続（独自設計） | [SpectralGeneratorStages.lean](../../Foundation/Quantum/SpectralGeneratorStages.lean) の `stageModel/stage_valid_iff/stage_sound/stage_interpretation_substitute/stageEval_fiber` | 同じ生成規則を段階のフレームへ、局所の包含関係を反映するモデルとして解釈します。 |
| 本実装の非自明な具体例 | [SpectralGeneratorExamples.lean](../../Foundation/Quantum/SpectralGeneratorExamples.lean) の `firstCharacter/secondCharacter/spectralObservation_proper/additionCover_interpreted/positivity_not_derivable/stage_positive_distinguished/additionCover_stage_interpreted` | ℂ×ℂ の観測(0,1)を区別する二つの指標を構成します。実際の複合導出を両方のモデルで解釈し、偽の判断の導出不可能性も証明します。 |

| 原典の参照 | Lean の宣言と所在 | 対応の範囲と制限 |
| --- | --- | --- |
| 補題5.2.19、p.155 の局所意味論 | [SpectralCover.lean](../../Foundation/Quantum/SpectralCover.lean) の `Context.rational_separator/shifted_well_inside/compact_subset_shift/well_inside_positive_iff` | 実際の開集合について、分離用の開集合の存在と正の有理数による内側へのずれの同値を証明します。原典の自由生成された束 `LA` の等式との同値は未証明です。実部による解釈を使うため、局所の証明は非自己随伴元にも拡張しています。 |
| 定理5.2.23(b)、p.156 のコンパクト性による有限証拠 | 同ファイルの `Context.compact_rationalCut/finite_shift_subcover/positiveOpen_cover_iff` | 任意の添字集合の開被覆と、各正の有理数について存在する有限の部分被覆の同値です。証拠の不等式は実際の開集合の間のものです。束 `LA` 内の不等式、提示の普遍性、内部化は残ります。 |

## 最終鍵の比較対象と BB84 出力への接続

以下は本実装による追加設計と量子情報の数学です。Heunen の鍵配送の等式を、盗聴者を含む最終鍵の安全性の定理として引用しません。

| 根拠・目的 | Lean の宣言と所在 | 検証した範囲と制限 |
| --- | --- | --- |
| 物理的な古典処理の合成 | [ClassicalComposition.lean](../../Foundation/Quantum/ClassicalComposition.lean) の `classicalMap_compose` | 量子補助系を保持した任意の共同作用素で、古典ラベルの関数合成と解釈された操作の合成が一致します。導出木やクラウスの表示の同一性は要求しません。 |
| 明示的な理想鍵状態（独自設計） | [IdealKey.lean](../../Foundation/Quantum/QKD/IdealKey.lean) の `Output/idealize/public_idealize/idealize_from_public/idealize_idempotent/idealize_correct/idealize_abort_empty` | 受理時の独立な一様の共通鍵と、中止時の空の鍵を実際の密度演算子で構成します。公開記録・中止・攻撃者の共同状態を保持します。 |
| 共同状態の安全性の比較（独自設計） | 同ファイルの `Secure/idealize_approx/secure_perturbation/secure_correctness` | 全ての二値測定による比較と、誤差の移送・正しさへの帰結です。実際の BB84 に対する秘密性の上界、トレース距離との同値、無限次元への拡張は未達です。 |
| 既存メタ論理への接続（独自設計） | [IdealKeyLogic.lean](../../Foundation/Quantum/QKD/IdealKeyLogic.lean) の `presentation/model/sound/interpretation_substitute/fixedComposition` | 指定した理想化と誤差の有限の推論体系です。実状態の安全性を無条件で導入しません。 |
| 非自明な検証例（自作） | [IdealKeyExamples.lean](../../Foundation/Quantum/QKD/IdealKeyExamples.lean) の `idealization_changes_state/mismatch_security_error/chosen_ideal_probability/chosen_security_error/fixed_interpreted` | 異なる鍵の状態には誤差1以上、共に固定値0の鍵の状態にも誤差1/2以上が必要です。理想化の閉導出を状態が実際に変わるモデルで検証します。BB84 の実行結果と同一視しません。 |
| BB84 の共同出力への接続（独自設計） | [BB84Finalization.lean](../../Foundation/Quantum/QKD/BB84Finalization.lean) の `output/channel/state/public_channel/ideal_public/security_correctness` | 任意の共同攻撃と全乱数を含む既存の生鍵状態を、新しい公開種によるハッシュ処理へ実際に接続します。誤り訂正と、秘密増幅に適したハッシュ族に対する上界の証明は含みません。 |

## 二普遍ハッシュ族の追加構成

| 根拠・目的 | Lean の宣言と所在 | 検証した範囲と制限 |
| --- | --- | --- |
| 有限加法群の一様な逆像の数え上げ（追加数学） | [UniformFiber.lean](../../Foundation/Quantum/QKD/UniformFiber.lean) の `Hashing.uniform_hom_fiber` | 全射準同型の各出力の確率を入力の一様分布から計算します。数学的な証明であり、衝突率を仮定する規則ではありません。 |
| 二元体上の線形ハッシュ（追加構成） | [LinearHash.lean](../../Foundation/Quantum/QKD/LinearHash.lean) の `Hashing.linearHash/hash_difference_surjective/linear_collision` | 一様な行列種に対して、異なる入力の衝突率が正確に出力集合の大きさの逆数です。量子側情報に対する秘密性の評価は別の未達条件です。 |
| BB84 の任意の生鍵への接続 | [BB84LinearHash.lean](../../Foundation/Quantum/QKD/BB84LinearHash.lean) の `Hashing.encodeRaw_injective/rawHash/raw_collision/linearState/linearState_ideal_public` | 欠落と値0を区別する単射符号化、任意の異なる生鍵の衝突率、公開種と攻撃者を保持する実際の共同状態を構成します。種の長さの最適性は主張しません。 |
| 有限の衝突確率の推論（独自設計） | [HashLogic.lean](../../Foundation/Quantum/QKD/HashLogic.lean) の `presentation/run/model/sound/interpretation_substitute` | 入力対の決定後に独立な一様の種を選ぶ実験と有限混合です。意味論上の任意の真理を導入せず、既存の核を使います。 |
| 具体的な検証例（自作） | [HashExamples.lean](../../Foundation/Quantum/QKD/HashExamples.lean) の `absent_zero_collision/mixedProof/mixed_interpreted/presence_separates/cnotHashed/cnotHashed_ideal_public` | 欠落と値0の衝突率1/4、有限混合の導出、区別する具体的な行列、二信号への共同攻撃後の物理的なハッシュ状態を検証します。BB84 の秘密性の上界は未達です。 |

秘密増幅の後続の追加資料として [Tomamichel–Schaffner–Smith–Renner, arXiv:1002.2436](https://arxiv.org/pdf/1002.2436) の定義1と定理6の本文と証明を確認しました。ハッシュ種を含む量子側情報の距離と条件付きエントロピーの評価が必要です。この対応は後続の依存の記録であり、定理6を今回形式化したという意味ではありません。

## 最適推測と有限の公開情報（追加数学と独自の構文）

| 目的 | Lean の宣言と所在 | 検証した範囲と制限 |
| --- | --- | --- |
| 全ての量子測定に対する最適推測 | [Guessing.lean](../../Foundation/Quantum/QKD/Guessing.lean) の `CQ/Measurement/guessingProbability/guessingProbability_le_of_dominated` | 正規化した古典・量子状態と完全な測定、作用素の不等式からの上界です。最小エントロピーとの双対性や平滑化は未達です。 |
| 公開情報の損失 | [GuessLeakage.lean](../../Foundation/Quantum/QKD/GuessLeakage.lean) の `leakage_chain/leakage_of_dominated` | 公開値ごとの任意の量子測定を許し、公開値の種類数による損失を証明します。具体的な誤り訂正方式の評価は含みません。 |
| 量子後処理 | [GuessProcessing.lean](../../Foundation/Quantum/QKD/GuessProcessing.lean) の `pull/score_post/guessingProbability_post` | 実際の有限クラウスチャネルによる推測確率の単調性です。 |
| 共同密度演算子と BB84 | [CQRepresentation.lean](../../Foundation/Quantum/QKD/CQRepresentation.lean) の `CQ.density/CQ.density_block/ofDensity/bb84Blocks` | 実際の共同状態への接続です。BB84 のラベル全体を鍵だけのエントロピーと同一視しません。 |
| メタ論理への接続 | [GuessLogic.lean](../../Foundation/Quantum/QKD/GuessLogic.lean) の `presentation/model/sound/interpretation_substitute/leakProof` | 固定した推測上界の規則の妥当性、導出の健全性、仮定置換を証明します。 |
| 具体的モデル（自作） | [GuessExamples.lean](../../Foundation/Quantum/QKD/GuessExamples.lean) の `prior_guessing/revealed_guessing/leak_derivation_interpreted/coherentState` | 独立の量子系を保持した一様ビットの推測確率が、公開によって1/2から1に変わります。導出の前提を実際に証明します。 |

## BB84 の公開情報を含む推測と追加通信（追加数学・独自設計）

| 目的 | Lean の宣言と所在 | 検証した範囲と制限 |
| --- | --- | --- |
| 古典的なブロックの処理と物理チャネル | [CQRelabel.lean](../../Foundation/Quantum/QKD/CQRelabel.lean) の `relabel_physical/read_relabel_physical` | 全行列成分で一致します。量子側情報の非対角成分を古典分布へ置換しません。 |
| 部分トレースとの整合性 | [ClassicalDiscard.lean](../../Foundation/Quantum/ClassicalDiscard.lean) の `classicalMap_discardMiddle` | 任意の相関を持つ共同作用素で古典処理と量子系の破棄が交換します。 |
| BB84 の鍵と公開記録 | [BB84GuessState.lean](../../Foundation/Quantum/QKD/BB84GuessState.lean) の `RawGuess.state/state_physical/public_state/probability_joint/message_cost` | ボブの私的な鍵を破棄し、公開部分は既存の実状態と一致します。任意の共同攻撃を許します。位相誤りからの秘密性は未達です。 |
| 公開記録への任意の共同測定 | [GuessPublic.lean](../../Foundation/Quantum/QKD/GuessPublic.lean) の `withPublic_optimal` | 公開値ごとの測定と、公開レジスタと量子系への任意の測定の最適値が等しいことを証明します。 |
| 追加メッセージだけの損失 | [GuessAdditionalLeak.lean](../../Foundation/Quantum/QKD/GuessAdditionalLeak.lean) の `additional_leakage/disclosure_cost/additional_interpreted` | 以前の公開情報と量子系を保持した推測確率に対して、追加の種類数を乗じる上界です。既存の導出とモデルへ接続します。具体的な誤り訂正方式の成功は主張しません。 |
| 推測から定義する操作的な量 | [GuessEntropy.lean](../../Foundation/Quantum/QKD/GuessEntropy.lean) の `guessingProbability_pos/guessingEntropy/additional_entropy/bit_disclosure_entropy` | r ビットの追加通信による操作的な損失が高々 r ビットです。作用素の最適化との同値、平滑化、秘密増幅は後続です。受理した枝の状態は次の表の追加で接続します。 |
| 非対角成分を持つ自作例 | [GuessExamples.lean](../../Foundation/Quantum/QKD/GuessExamples.lean) の `coherent_public_joint_guessing/coherent_hidden_entropy/coherent_public_entropy` | 公開前後の推測確率と、操作的な量の1から0への変化を証明します。 |

## 受理した枝の重み付き推測（追加数学・独自設計）

| 目的 | Lean の宣言と所在 | 検証した範囲と制限 |
| --- | --- | --- |
| 正規化が1以下の状態 | [Subnormalized.lean](../../Foundation/Quantum/QKD/Subnormalized.lean) の `State/restrict/mass_partition/probability_le_mass/probability_zero_mass` | 事象の確率で割らず、重み付きの成功を評価します。最適化の主要な定理は空でない古典集合について証明します。 |
| 物理的な枝の選択 | [SubnormalizedPhysical.lean](../../Foundation/Quantum/QKD/SubnormalizedPhysical.lean) の `joint_positive/joint_trace_complex/restrict_physical/restrict_mass_probability` | 実際の正の共同作用素、選択するクラウス操作、元の状態での測定確率との一致です。 |
| 作用素の上界と後処理 | [SubnormalizedGuess.lean](../../Foundation/Quantum/QKD/SubnormalizedGuess.lean) の `probability_le_dominated/mass_post/probability_post/probability_restrict` | 全ての完全な量子測定を許します。枝の選択後の条件付き成功の単調性を主張しません。 |
| 公開記録と追加通信 | [SubnormalizedPublic.lean](../../Foundation/Quantum/QKD/SubnormalizedPublic.lean)、[SubnormalizedLeak.lean](../../Foundation/Quantum/QKD/SubnormalizedLeak.lean)、[SubnormalizedRelabel.lean](../../Foundation/Quantum/QKD/SubnormalizedRelabel.lean) の `public_probability/public_restrict_le/additional_leakage/relabel_physical/disclosure_cost` | 公開値ごとの測定と任意の共同測定の対応、枝の重みの保存、追加通信の種類数による損失を証明します。 |
| BB84 の実際の受理した枝 | [BB84Accepted.lean](../../Foundation/Quantum/QKD/BB84Accepted.lean) の `physical/mass_acceptance/probability_le_acceptance/probability_zero/probability_le_original/message_cost` | 全乱数と共同攻撃を含みます。受理した枝の推測上界を、位相誤りから評価することは未達です。 |
| 既存メタ論理との接続 | [SubnormalizedLogic.lean](../../Foundation/Quantum/QKD/SubnormalizedLogic.lean) の `presentation/model/sound/interpretation_substitute/selectProcess` | 行列不等式・重みの上界から、枝の選択と量子後処理を含む上界を導出します。任意の真理を導入しません。 |
| 自作の具体例 | [SubnormalizedExamples.lean](../../Foundation/Quantum/QKD/SubnormalizedExamples.lean) の `branch_mass/branch_probability/branch_public_probability/branch_coherence/processed_coherence/processed_probability/impossible_probability/interpreted` | 重みと成功確率は1/2です。実際の量子後処理で非対角成分が1/4から0に変わります。成立しない枝の成功は0です。合成した導出の前提を行列で証明します。 |

## 秘密増幅の量子衝突量（追加資料と独自の構文）

根拠は [Tomamichel–Schaffner–Smith–Renner, arXiv:1002.2436](https://arxiv.org/pdf/1002.2436) の補題5と証明（取得PDF通しpp.5–6）です。有限行列での計算を形式化します。参照状態の逆根・台の扱いと、補題4・定理6の距離評価と平滑化は未達です。

| 目的 | Lean の宣言と所在 | 検証した範囲と制限 |
| --- | --- | --- |
| 量子衝突量の平均 | [HashCollision.lean](../../Foundation/Quantum/QKD/HashCollision.lean) の `grouped_expansion/output_expansion/output_le` | 量子ブロックの積のトレースを保持し、同じ種の分布で証明した衝突率を使います。正規化1を要求しません。 |
| 正値行列による重み付け | [WeightedCollision.lean](../../Foundation/Quantum/QKD/WeightedCollision.lean) の `sandwich_pair/sandwich_grouped/weighted_positive_le` | 任意の正値な重み付けの行列と、非可換な入力ブロックを許します。逆根の構成は別途必要です。 |
| 一様な比較対象との差 | [CollisionVariance.lean](../../Foundation/Quantum/QKD/CollisionVariance.lean) の `variance_identity/variance_expansion/variance_nonneg/variance_sharp_le` | 同じ量子周辺状態を持つ比較対象に対し、中心化した衝突量の恒等式と上界を証明します。距離の上界ではありません。 |
| 実際の BB84 の入力と行列ハッシュ | [BB84Collision.lean](../../Foundation/Quantum/QKD/BB84Collision.lean) の `raw_collision/acceptedInput/accepted_hash_physical/accepted_weighted_variance` | 共同攻撃、全乱数、受理した枝、公開記録、量子側情報を保持します。新しい一様な行列種を使います。 |
| 既存メタ論理への接続 | [CollisionLogic.lean](../../Foundation/Quantum/QKD/CollisionLogic.lean) の `presentation/model/sound/interpretation_substitute/proof` | 衝突量の上界の有限導出です。秘密性を導入する規則はありません。 |
| 非可換な具体例（自作） | [CollisionExamples.lean](../../Foundation/Quantum/QKD/CollisionExamples.lean) の `blocks_noncommute/cross_pair/input_value/total_value/output_value/variance_value/interpreted` | 実際の非可換な量子ブロックに対し、中心化した量1/4と合成した導出を検証します。 |
| 距離評価に使う内積の不等式 | [TraceCauchy.lean](../../Foundation/Quantum/TraceCauchy.lean) の `trace_cauchy/trace_square_nonneg/trace_cauchy_sqrt` | 有限の自己共役作用素に対する実際のトレースの不等式です。作用素ノルムと別の局所的な内積を使います。 |


## 行列の二乗量と観測差（独自の有限行列の証明・構文）

前節の追加資料の補題4（取得PDF通しpp.4–5）を動機とします。以下は再構成行列を明示的な前提にした、全ての二値測定の差に関する独自の証明です。原著のトレースノルム評価全体や、台・逆根の構成の形式化とは区別します。

| 目的 | Lean の宣言と所在 | 検証した範囲と制限 |
| --- | --- | --- |
| 二値測定の重み付き評価 | [WeightedObservation.lean](../../Foundation/Quantum/WeightedObservation.lean) の `trace_interval_contrast/weighted_effect_contrast/weighted_observation` | 正値な区間とトレース内積から上界を証明します。非可換な行列を許します。再構成行列の可逆性は要求しません。 |
| 実際の作用素の距離と後処理 | [OperatorDistance.lean](../../Foundation/Quantum/OperatorDistance.lean) の `OperatorApprox.of_factor/postprocess/trans/state_iff/subnormalizedApprox_of_factor` | 正規化した状態と、重みが等しい正規化1以下の枝を扱います。重みで割りません。 |
| 既存メタ論理との接続 | [OperatorDistanceLogic.lean](../../Foundation/Quantum/OperatorDistanceLogic.lean) の `presentation/model/sound/interpretation_substitute/weightedPostSymm` | 再構成等式と二乗量からの有限導出です。核の変更や任意の意味論上の真理を導入する規則はありません。 |
| 上界を達成する自作例 | [WeightedObservationExamples.lean](../../Foundation/Quantum/WeightedObservationExamples.lean) の `square_value/close/observed_gap/error_lower_bound/interpreted/dephase_equal` | X 基底の純粋状態と最大混合状態の観測差は1/2です。導出の前提を証明し、量子後処理の後の実際の行列等式も検証します。 |


## 公開種を保持した秘密増幅の観測差（追加数学・独自の構文）

この追加は、前節の有限行列の再構成等式を用いる独自の証明です。逆根・台の構成、平滑化、BB84 の位相誤りによる入力上界は含めません。

| 目的 | Lean の宣言と所在 | 検証した範囲と制限 |
| --- | --- | --- |
| 種と任意の共同測定 | [PublicMixtureObservation.lean](../../Foundation/Quantum/PublicMixtureObservation.lean) の `Effect.readPublic/publicMixture_observation/publicMixture_approx/probability_sqrt_bound/publicMixture_of_factors` | 公開値に応じて異なる測定と、種間の非対角成分を持つ共同測定を含みます。実際の種の確率で平均します。 |
| 古典レジスタと量子の差 | [ClassicalBlocks.lean](../../Foundation/Quantum/ClassicalBlocks.lean) の `representation/positive/hermitian/mul/adjoint/trace_square/constant_cost/reconstruct/joint` | 正値な状態と、中心化による正値でない差を実際の共同作用素として扱います。 |
| ハッシュ後の観測差 | [HashDistance.lean](../../Foundation/Quantum/QKD/HashDistance.lean) の `hashed_difference/hashed_trace/deviation_reconstruct/published_distance/published_two_universal` | 公開種を含む共同観測差を、重み付き入力衝突量から評価します。再構成等式は証明すべき前提です。 |
| BB84 の実状態への接続 | [BB84HashDistance.lean](../../Foundation/Quantum/QKD/BB84HashDistance.lean) の `accepted_hashed_operator/accepted_published_trace/accepted_published_comparator_trace/accepted_published_distance` | 受理した枝、アリスのハッシュ鍵、従来の公開記録、量子側情報を保持します。重みを保存し、条件付き正規化をしません。ボブの正しさと最終安全性への合成は後続です。 |
| メタ論理への接続 | [HashDistanceLogic.lean](../../Foundation/Quantum/QKD/HashDistanceLogic.lean) の `presentation/model/sound/interpretation_substitute/proof` | ハッシュ、再構成と衝突量からの観測差、上界を広げる規則の健全性を証明します。 |
| 非可換な自作例 | [HashDistanceExamples.lean](../../Foundation/Quantum/QKD/HashDistanceExamples.lean) の `interpreted/real_entry/ideal_entry/actual_ne_ideal` | 導出の前提を行列で証明します。観測差の上界は1/2です。同じ行列成分の0と3/16が、実状態と比較対象の違いを示します。 |


## 可逆な有限参照状態の四乗根（追加数学）

| 目的 | Lean の宣言と所在 | 検証した範囲と制限 |
| --- | --- | --- |
| 正の四乗根と逆行列 | [ReferenceRoot.lean](../../Foundation/Quantum/QKD/ReferenceRoot.lean) の `quarterRoot_positive/quarterRoot_fourth/quarterRoot_isUnit/inverse_quarter_reconstruct` | 関数計算から実際に行列を構成し、全入力作用素の再構成を証明します。参照行列の可逆性が必要です。台に制限した一般逆行列は未達です。 |
| 公開種を含む観測差と有限導出 | 同ファイルの `faithful_reference_distance/faithful_reference_interpreted` | 正規化した参照状態により費用が1となります。再構成と費用の前提を証明してから、既存の有限導出を解釈します。入力の上界は別途証明します。 |
| BB84 の受理した実状態 | [BB84HashDistance.lean](../../Foundation/Quantum/QKD/BB84HashDistance.lean) の `accepted_faithful_distance` | 公開種と従来の公開記録、量子補助系を保持します。位相誤りの評価、平滑化、最終安全性への合成は未達です。 |


## 作用素の上界と秘密増幅の誤差（追加数学の独自再構成）

| 目的 | Lean の宣言と所在 | 検証した範囲と制限 |
| --- | --- | --- |
| 重み付き衝突量の入力上界 | [DominatedCollision.lean](../../Foundation/Quantum/QKD/DominatedCollision.lean) の `inverse_quarter_reference/dominated_block_collision/dominated_input_collision` | 可逆な参照状態と各ブロックの作用素の不等式から `q × 枝の重み` を証明します。非可換な入力を許し、受理確率で割りません。 |
| 公開種を含む観測差 | 同ファイルの `dominated_published_distance` | 入力上界を、四乗根の構成と既存のメタ論理の合成した導出へ渡します。入力の作用素の上界は別途証明する必要があります。 |
| BB84 の受理した状態 | [BB84HashDistance.lean](../../Foundation/Quantum/QKD/BB84HashDistance.lean) の `accepted_dominated_distance/accepted_input_mass` | 全公開記録と量子補助系を保持します。上界に現れる重みを物理的な受理確率へ接続します。位相誤りからの前提の証明は未達です。 |
| 非可換な具体例（自作） | [DominatedCollisionExamples.lean](../../Foundation/Quantum/QKD/DominatedCollisionExamples.lean) の `reference_isUnit/domination/collision_bound/interpreted/error_lt_half/blocks_noncommute` | 一様な二ビットと、最初のビットに依存する非可換な量子状態から、実際の一行行列ハッシュを実行します。参照状態の可逆性と作用素の前提を証明し、公開種を含む観測差の上界 `√(1/2)/2` を得ます。 |


## 可逆でない参照状態と有限導出（独自の有限次元の極限証明）

| 目的 | Lean の宣言と所在 | 検証した範囲と制限 |
| --- | --- | --- |
| 参照状態の摂動と正規化 | [ReferenceRegularization.lean](../../Foundation/Quantum/QKD/ReferenceRegularization.lean) の `regularizeReference/regularizeReference_isUnit/regularizeReference_scaled/regularizeReference_domination` | 正の恒等行列を加えて可逆にし、正規化による係数の変化を証明します。有限次元を使います。 |
| 可逆性を要求しない距離評価 | 同ファイルの `dominated_published_distance_general` | 実作用素と比較対象を固定し、数値の誤差上界の極限を取ります。台の上の逆根や無限次元近似の構成ではありません。 |
| 有限の対象論理 | [PrivacyAmplificationLogic.lean](../../Foundation/Quantum/QKD/PrivacyAmplificationLogic.lean) の `presentation/model/sound/interpretation_substitute/proof` | 規則は二つの前提を持ちます。極限は規則の健全性の証明に使います。核の拡張はありません。 |
| BB84 の実状態との接続 | [BB84HashDistance.lean](../../Foundation/Quantum/QKD/BB84HashDistance.lean) の `accepted_dominated_distance_general` | 参照状態の可逆性なしに、受理した枝へ有限導出を解釈します。検査結果から作用素の前提を得る証明は未達です。 |
| 特異で非対角成分を持つ具体例（自作） | [PrivacyAmplificationExamples.lean](../../Foundation/Quantum/QKD/PrivacyAmplificationExamples.lean) の `reference_singular/reference_coherence/state_coherence/domination/interpreted/actual_ne_ideal` | 実際の純粋参照状態と一様な二ビットから、公開行列種を持つ観測差の上界1/4を証明します。実状態と比較対象の行列成分は0と1/16で異なります。 |


## 公開メッセージの作用素上界と秘密増幅（追加数学）

| 目的 | Lean の宣言と所在 | 検証した範囲と制限 |
| --- | --- | --- |
| 公開レジスタを含む参照状態 | [DominatedLeak.lean](../../Foundation/Quantum/QKD/DominatedLeak.lean) の `leakedReference/leakedReference_scaled` | 新しい一様な公開レジスタと従来の参照状態を組み合わせ、正規化と係数の恒等式を証明します。新しい値の集合は空でないものです。 |
| 追加通信の作用素の損失 | 同ファイルの `branch_dominated/withPublic_dominated/additional_dominated/disclose_dominated/bit_disclose_dominated` | 以前の公開情報と量子系を保ったまま、新しいメッセージの種類数だけを係数へ掛けます。r ビットの場合は `2^r` です。 |
| 通信後の有限導出 | 同ファイルの `mass_disclosed/disclose_privacy` | 保存した枝の重みと通信後の作用素の前提を、既存の秘密増幅の導出へ渡します。核の変更はありません。 |
| BB84 との接続 | [BB84HashDistance.lean](../../Foundation/Quantum/QKD/BB84HashDistance.lean) の `accepted_disclosed_privacy` | アリスの生鍵と古い公開記録から指定した関数を公開します。能動的な改ざん、認証、誤り訂正方式の正しさは後続です。 |
| 損失が必要な具体例（自作） | [DominatedLeakExamples.lean](../../Foundation/Quantum/QKD/DominatedLeakExamples.lean) の `hidden_dominated/public_dominated/public_probability/coefficient_lower_bound/exposed_coherence/interpreted` | 私的ビットの公開で係数が1/2から1になり、どの参照状態でも1未満にはできません。量子側情報の非対角成分と、通信後の有限導出も検証します。 |


## 受理した枝の共通鍵への誤差の合成（追加数学・独自の構文）

この部分は Heunen 論文の定理の転記ではありません。有限の古典鍵と有限次元の量子補助系について、既存の作用素の定義から証明した追加数学です。

| 目的 | Lean の宣言と所在 | 検証した範囲と制限 |
| --- | --- | --- |
| 古典処理の結合による評価 | [ClassicalCoupling.lean](../../Foundation/Quantum/QKD/ClassicalCoupling.lean) の `joint_event_observation/relabel_observation/relabel_coupling/joint_injective/relabel_comp` | 元の量子ブロックを保持し、全ての共同二値測定の差をラベルの不一致の重みで抑えます。 |
| 共通の一様な理想鍵 | [CommonKeyComposition.lean](../../Foundation/Quantum/QKD/CommonKeyComposition.lean) の `uniformize_public/ideal_block/ideal_public/ideal_correctness/mass_ideal` | 同じ公開記録と量子周辺作用素、同じ受理の重みを保ち、両者へ同じ一様な古典鍵を配置します。 |
| 誤差の加法的合成 | 同ファイルの `correctness_observation/correctness_le_error/repair_close/compose` | 鍵の不一致の重み δ とアリスの秘密性 ε から、両者の鍵を含む共同観測差 δ+ε を証明します。中間の修復状態は比較用です。 |
| メタ論理との接続 | [CommonKeyLogic.lean](../../Foundation/Quantum/QKD/CommonKeyLogic.lean) の `presentation/model/sound/interpretation_substitute/proof` | 二前提の合成規則の妥当性、導出の健全性、仮定置換との一致を検証します。 |
| 正しさが独立に必要な具体例 | [CommonKeyExamples.lean](../../Foundation/Quantum/QKD/CommonKeyExamples.lean) の `correctness/alice_uniform/secrecy/interpreted/error_lower_bound/erroneous_coherence` | 公開記録を含めてアリスの秘密性は0、不一致の重みは1/4、共通鍵の共同観測差の上界と下界は1/4です。非対角成分も保持します。自作の例です。 |

中止を含む既存の最終出力への埋め込み、実際の BB84 の前提の導出、誤り訂正と認証は残ります。


## 中止を含む既存の理想鍵への接続（追加数学・独自の構文）

| 目的 | Lean の宣言と所在 | 検証した範囲と制限 |
| --- | --- | --- |
| 一様な鍵の置換との一致 | [CommonKeyIdealization.lean](../../Foundation/Quantum/QKD/CommonKeyIdealization.lean) の `replaceKeys_block/ideal_uniform_replacement` | 有限の古典鍵について、前節の理想状態と新しい一様な共通鍵を置く操作の平均が、共同作用素として等しいことを証明します。 |
| 受理と中止の実密度演算子 | [AcceptedAbortComposition.lean](../../Foundation/Quantum/QKD/AcceptedAbortComposition.lean) の `state/replace_abort/replace_accept/accepted_ideal/idealize_state` | 二つの枝の重みの和が1であることを要求します。既存の `IdealKey.idealize` との一致を証明します。公開記録と量子補助系を両方の枝で保持します。 |
| 全体の安全性へ誤差を渡す | 同ファイルの `correctness_probability/secure_of_common/secure` | 受理確率で割らず、既存の `IdealKey.Secure` の誤差 δ+ε を結論します。実プロトコルとの状態の等式は別途必要です。 |
| 二段の有限導出 | [AcceptedAbortLogic.lean](../../Foundation/Quantum/QKD/AcceptedAbortLogic.lean) の `presentation/model/sound/interpretation_substitute/proof` | 受理した枝の合成、全体の安全性への接続の妥当性と健全性を証明します。メタ論理の核の変更はありません。 |
| 中止の重みが正である具体例 | [AcceptedAbortExamples.lean](../../Foundation/Quantum/QKD/AcceptedAbortExamples.lean) の `accepted_mass/aborted_mass/alice_uniform/correctness/interpreted/error_lower_bound/accepted_coherence/aborted_coherence` | 受理と中止が各1/2、秘密性の誤差0、不一致の重み1/4、全体の安全性の誤差の上界・下界1/4です。両方の枝が非対角成分を持ちます。自作の例です。 |

この部分は Heunen 論文に推論体系として記載された規則の転記ではありません。BB84 の実際の最終状態との同一性、位相誤りから秘密性の前提を得る証明、誤り訂正と認証は後続です。


## BB84 の最終状態との同一性と安全性への接続（追加数学）

| 目的 | Lean の宣言と所在 | 検証した範囲と制限 |
| --- | --- | --- |
| 入力の後で選ぶ独立な種 | [SeededCQ.lean](../../Foundation/Quantum/QKD/SeededCQ.lean) の `independent/relabel_independent/physical` | 指定した種の分布と固定した量子入力から構成し、物理的な古典チャネルの混合と共同作用素として等しいことを証明します。 |
| 正の枝への分割 | [ClassicalBranching.lean](../../Foundation/Quantum/QKD/ClassicalBranching.lean) の `joint_partition/final_partition/final_mass` | 確率だけでなく、量子補助系を含む作用素の等式を証明します。枝の重みを保存します。 |
| 実際の BB84 の枝 | [BB84FinalSecurity.lean](../../Foundation/Quantum/QKD/BB84FinalSecurity.lean) の `source/acceptedBranch/abortBranch/branch_mass` | 共同攻撃の出力、両者のハッシュ鍵、古い公開記録、新しい公開種、量子側情報を保持します。 |
| 既存の最終状態との同一性 | 同ファイルの `output_partition/state_partition/state_eq` | 既存の `Finalization.output` と `Finalization.state` が分割した実験と同じであることを証明します。ハッシュの安全性は等式の前提ではありません。 |
| 物理的な確率との一致 | 同ファイルの `correctness_probability/acceptance_probability` | 不一致の重みと受理の重みを、既存の最終状態における測定確率へ接続します。 |
| メタ論理による全体の比較 | 同ファイルの `secure` | 実際の枝へ既存の二段の有限導出を解釈し、正しさ δ と秘密性 ε を全体の誤差 δ+ε へ渡します。両方の前提は実際の状態について証明する必要があります。 |

これは Heunen 論文の安全性定理の転記ではありません。秘密増幅の作用素と公開レジスタの配置の対応、位相誤りと検査からの前提の導出、平滑化、具体的な誤り訂正と認証は未達です。


## 秘密増幅と BB84 の全最終状態の合成（追加数学）

| 目的 | Lean の宣言と所在 | 検証した範囲と制限 |
| --- | --- | --- |
| 基底の付け替えと観測 | [BasisTransport.lean](../../Foundation/Quantum/BasisTransport.lean) の `operator/pull/trace/observation/approx` | 全単射による行列の付け替えが、全共同二値測定の差の上界を保つことを証明します。 |
| 正の枝への種の追加 | [SeededSubnormalized.lean](../../Foundation/Quantum/QKD/SeededSubnormalized.lean) の `seeded_mass/seed/mass_seed/seed_ofCQ/seed_restrict/seed_relabel/restrict_relabel` | 重みを保存し、指定した古典処理と枝の選択との整合性を証明します。 |
| 秘密増幅の配置との一致 | [HashLayout.lean](../../Foundation/Quantum/QKD/HashLayout.lean) の `basis/output/output_block/output_public/public_block/real/ideal/secrecy` | 新しい種、ハッシュ鍵、従来の公開記録、量子系を保持し、実作用素と比較対象の両方の等式を証明します。 |
| 実際のアリスの鍵との一致 | [BB84PrivacyComposition.lean](../../Foundation/Quantum/QKD/BB84PrivacyComposition.lean) の `alice_output/accepted_mass/input_mass_probability` | ボブの私的鍵だけを捨てた最終枝と、既存の秘密増幅の枝を接続します。重みは実際の最終出力の受理確率です。 |
| 全最終状態の誤差 | 同ファイルの `secrecy/secure` | 実入力の作用素の上界 qτ と正しさ δ から、既存の最終状態について `δ + ½√(d(1−1/d)qm)` を証明します。d は鍵の種類数、m は受理の重みです。 |

この部分は、Heunen 論文にある推論体系の転記ではなく、既存の有限行列の秘密増幅の評価と最終出力の定義を接続する追加証明です。検査結果と位相誤りから qτ の前提を得る証明、平滑化、具体的な誤り訂正と認証は残ります。

## 相補基底での有限の重ね合わせ（追加数学）

一次資料は Bouman–Fehr, *Sampling in a Quantum Population, and Applications*, arXiv:0907.4246v5 の補題1（p.12）、系1（p.13）、付録C（pp.27–28）です。[原論文](https://arxiv.org/pdf/0907.4246v5) の本文を確認しました。Heunen 論文の定理番号として扱いません。

| 対応 | Lean の宣言と所在 | 検証した範囲と制限 |
| --- | --- | --- |
| 付録Cで用いる正作用素の比較 | [CoherentSupport.lean](../../Foundation/Quantum/QKD/CoherentSupport.lean) の `variance_identity/sum_dominated/flat_dominated` | 有限個の補助系ベクトルの重ね合わせを、項数倍の非干渉の共分散で抑えます。原論文の Cauchy–Schwarz による証明を転記せず、ベクトルの差の外積の和を正の証拠として構成しました。 |
| 測定後の参照状態 | 同ファイルの `synthesis_covariance/measurement_covariance/measured_dominated` | 有限の余等長行列と入力のトレース正規化から、測定分岐と参照密度演算子を実際に構成します。補助系ベクトルの直交性や参照行列の可逆性は要求しません。 |
| 系1へ向けた全 Hadamard 基底の特殊化 | [BB84PhaseSupport.lean](../../Foundation/Quantum/QKD/BB84PhaseSupport.lean) の `gate_flat/dominated/guessing` | n量子ビット、相補基底の有限支持 J に対し、係数を `card J / 2^n` とします。二項係数のエントロピーによる評価、平滑最小エントロピー、標本検査からの支持条件は証明していません。 |
| 実際の量子操作との一致 | 同ファイルの `input_normalized/physical_block` | 信号と補助系の純粋な共同入力を構成し、既存の Hadamard チャネルを補助系へ拡大した後の測定対角ブロックとの等式を証明します。量子系の非対角成分を保持します。 |
| メタ論理への接続 | 同ファイルの `privacy` | 既存の `PrivacyAmplificationLogic.proof` の作用素の前提を今回の定理で証明し、`Model` で解釈します。意味論上の任意の真理を導入する規則は追加しません。 |

これは原論文の最小エントロピーの補題全体の形式化ではありません。量子標本抽出定理、平滑化、準備と測定による BB84 ともつれを用いる BB84 の同等性は、独立の開始条件と証明を必要とします。

`PhaseSupportExamples.lean` の `normalized/reference_matrix/coefficient/guessing/coherence/input_cross_entry/collision/interpreted` は自作の有限モデルです。3信号、2個の相補基底の支持、1量子ビットの補助系について、実際の行列と具体的な二進行列のハッシュを計算します。推測上界と1ビットへの秘密増幅の観測差の上界は各1/4です。補助系の測定後の非対角成分1/16と入力の共同非対角成分1/2を証明します。原論文の数値例の転記ではありません。

## 量子標本抽出の平方根評価（追加数学）

Bouman–Fehr, arXiv:0907.4246v5, 定理3とその証明（§4.2、pp.11–12）では、良い部分空間への正規化射影を構成し、古典的な失敗確率の平方根で量子状態の距離を抑えます。[一次資料](https://arxiv.org/pdf/0907.4246v5) の証明本文を確認しました。以下は任意の有限次元の純粋な共同状態について、その作用素と全二値観測による有限の再構成です。無限次元のトレース距離や全 BB84 の位相推定までを、この定理の達成範囲に含めません。

| 対応 | Lean の宣言と所在 | 検証した範囲と制限 |
| --- | --- | --- |
| 純粋状態の射影による距離評価 | [PureProjection.lean](../../Foundation/Quantum/PureProjection.lean) の `rank_mul/orthogonal_projection/normalized_projection` | 良い・悪い成分の二方向が張る射影を実際に構成します。既存の重み付き観測評価により、捨てる成分の重みの平方根を証明します。原論文が使うトレース距離の公式を公理として導入しません。 |
| 正規化した良い支持の状態 | [SupportProjection.lean](../../Foundation/Quantum/SupportProjection.lean) の `vector_unit/supported/approximation` | 良い成分の重みが零の場合は、指定した良い基底方向を使います。その方向が良い集合に属することを、支持定理では明示的に要求します。零の確率で割りません。 |
| 古典的な上界から量子状態の比較へ | [QuantumSampling.lean](../../Foundation/Quantum/QKD/QuantumSampling.lean) の `average_mass/realState/idealState/approximation/sampling/processed` | 入力の各基底添字での古典的な失敗上界 ε から、公開標本と量子系全体の観測差 √ε を証明します。補助系は全体の基底に含められます。混合入力の純粋化の構成は別途必要です。 |
| 誤り位置に対する具体的な標本抽出 | [QuantumErrorSampling.lean](../../Foundation/Quantum/QKD/QuantumErrorSampling.lean) の `classical/approximation/accepted_support` | 既存の非復元一様標本の二項係数の比による上界を使います。誤りが多く、かつ標本で検出されない基底添字を良い支持から除きます。誤り位置の独立性は要求しません。 |
| 実際の二結果の量子検査 | [QuantumErrorTest.lean](../../Foundation/Quantum/QKD/QuantumErrorTest.lean) の `test/accepted_operator/accepted_support/accepted_zero_row` | 対角射影から完全な二結果の測定を構成します。受理した理想状態では、大きい誤りパターンに属する行列の行が零となります。実 BB84 の位相検査との同等性を仮定しません。 |
| メタ論理への接続 | [QuantumSamplingLogic.lean](../../Foundation/Quantum/QKD/QuantumSamplingLogic.lean) の `presentation/model/sound/interpretation_substitute/proof` | 点ごとの古典上界を前提として、量子状態の比較と処理後の比較を結論する有限規則です。核は変更しません。この推論体系は独自の設計です。 |
| 相関を持つ具体例 | [QuantumSamplingExamples.lean](../../Foundation/Quantum/QKD/QuantumSamplingExamples.lean) の `normalized/classical/omitted/retained/input_coherence/ideal_cross_entry/interpreted/zero_good_branch` | 2量子ビットのもつれた入力と一様な公開ビットを使います。良い成分・悪い成分は各1/2であり、量子観測差の上界 √(1/2) を有限導出から得ます。入力の非対角成分1/2と、対応する近似状態の成分0を証明します。自作の例です。 |

具体例の `measurement/channels/recorded` は、公開標本によって判定する実際の二結果の量子検査を使います。`interpreted` の後処理は、その検査の結果を忘れるチャネルです。`recorded` は検査結果も残すチャネルです。どちらも既存の `Instrument` から完全性を証明して構成します。

## もつれた送信源への置換（追加数学）

Bouman–Fehr, arXiv:0907.4246v5 の §5.2（p.15）は、BB84 基底の状態の送信を、もつれた対の片側を送って他方を後で測定する操作へ置き換える説明をしています。§6（pp.18–19）は、もつれを用いる BB84 の量子状態の配布を定めます。[一次資料](https://arxiv.org/pdf/0907.4246v5) の本文を確認しました。以下では「同じ観測を与える」という結論を前提にせず、任意の有限クラウス攻撃の後の共同密度演算子の等式を構成します。Heunen 論文の安全性定理の転記ではありません。

| 目的 | Lean の宣言と所在 | 検証した範囲と制限 |
| --- | --- | --- |
| 異なる系に対する局所操作の可換性 | [LocalOperations.lean](../../Foundation/Quantum/LocalOperations.lean) の `Op.tensor_local_right/Op.tensor_right_local/Kraus.commute_right` | 任意の共同作用素について、保持する系への共役操作と有限クラウス写像が可換であることを証明します。入力が積状態であるとは仮定しません。 |
| 正規化したもつれた対 | [SourceReplacement.lean](../../Foundation/Quantum/SourceReplacement.lean) の `pair_unit/pair/rotated_pair` | 有限基底と実際の係数から密度演算子を構成します。係数の正規化を要求します。 |
| アリスの結果に属する量子ブロック | 同ファイルの `amplify_slice/prepared_matrix/rotated_slice/replacement` | 基底行列の対称性と等長性を明示し、攻撃後の各ブロックと重み付き送信状態の等式を証明します。攻撃は列全体の任意の有限クラウスチャネルです。 |
| 基底操作を攻撃後へ遅らせる | [DelayedSource.lean](../../Foundation/Quantum/DelayedSource.lean) の `rotate_commute/delayed/delayed_replacement` | 入力のもつれた対と攻撃は、後で選ぶアリスの基底に依存しません。局所操作の可換性から遅延後の等式を証明します。 |
| 第二の系の測定と結果の記録 | [SecondRegister.lean](../../Foundation/Quantum/SecondRegister.lean) の `complete/channel/apply_entry/cq/physical` | クラウス作用素の完全性を証明してチャネルを構成します。第一の系の量子コヒーレンスを全て残し、実際の出力と CQ 表現の共同状態の等式を証明します。 |
| 任意長の BB84 列への特殊化 | [BB84SourceReplacement.lean](../../Foundation/Quantum/QKD/BB84SourceReplacement.lean) の `normalized/blockGate_symmetric/state/block/record_block/record_eq/outcome_weight` | 各位置の Z/X 基底が混在する列に対応します。測定したアリスの文字列は重み `2^(-n)` を持ち、ボブと攻撃者の共同状態は既存の `BlockAttack.jointState` です。 |
| 既存の一様な状態準備分布との一致 | 同ファイルの `uniform_weight/ensemble/ensemble_eq/uniform_replacement` | 一様分布の実際の質量から係数を証明します。アリスの私的文字列も古典レジスタに残した共同状態の等式です。 |
| メタ論理による源の置換 | [SourceReplacementLogic.lean](../../Foundation/Quantum/QKD/SourceReplacementLogic.lean) の `presentation/model/sound/interpretation_substitute/proof` | 源の置換、一様とは限らない有限の基底混合、その後の物理的処理を有限導出として扱います。構文は独自の設計です。核の拡張はありません。 |
| 具体的な盗聴攻撃 | [SourceReplacementExamples.lean](../../Foundation/Quantum/QKD/SourceReplacementExamples.lean) の `isometry/attacked_X_entry/record_coherence/outcome_uniform/source_coherence/interpreted` | 計算基底の値を補助系へ保存する等長攻撃です。X の結果ではボブと攻撃者の非対角成分が保持され、源の記録でその値は1/4です。基底混合と物理的後処理の閉導出を解釈します。自作の検証例です。 |

原論文 §6 の方式は、基底を共有して測定する方式です。この等式だけで、既存実装の独立な基底選択、基底照合、標本選択、中止、全最終出力との同一性が自動的に成立したとは扱いません。位相側の標本検査と鍵の支持の対応、秘密増幅の入力上界への接続も後続です。


### 既存の生鍵出力への源の置換の適用

次の二つのモジュールは、上記の共同状態の等式を既存の実行系へ接続する独自の追加設計です。原典にこの Lean の推論体系や公開記録の型があるとは主張しません。

| 目的 | Lean の宣言と所在 | 検証した範囲と制限 |
| --- | --- | --- |
| 古典ラベルによる物理的なチャネルの選択 | [ClassicalControl.lean](../../Foundation/Quantum/ClassicalControl.lean) の `select_complete/channel/select_block/apply/basis` | 各選択肢のチャネルの完全性から、全体のクラウス作用素の完全性を証明します。古典ラベル間の非対角成分を捨て、各枝の量子系全体の成分を保持します。 |
| 実際の生鍵出力との一致 | [BB84RawSource.lean](../../Foundation/Quantum/QKD/BB84RawSource.lean) の `selected/channel/state/selected_record/prepared/interpreted` | ボブの測定、基底照合、指定した標本の公開検査、中止、私的鍵を、既存の `RawProtocol.record` と同じ物理的処理で構成します。アリスの私的文字列は一様に平均します。両者の基底と検査集合はここでは固定しています。 |
| 標本不足の中止条件と公開記録 | 同ファイルの `configuration/public_record` | 既存の `Randomized.requiredLength` による中止条件を保持します。公開チャネルを適用した後も、全公開記録と攻撃者の系の共同状態が一致します。全乱数を持つ `Randomized.record` との分布の等式は後続です。 |

`interpreted` は `SourceReplacementLogic` の源の規則の閉導出を `Model` で解釈し、その行列の等式へ実際の生鍵チャネルを適用します。後処理の出力空間は源の記録空間と異なります。固定した空間内の構文の後処理規則へこのチャネルを無理に代入せず、証明した行列の等式に物理的写像を適用します。核の拡張は必要ありません。


### 全乱数を含む源の置換と有限クラウス攻撃の純粋化

前節で後続とした分布の対応を、実際の有限確率質量関数について証明しました。以下は、原典の源の置換の説明を既存の実験へ接続する独自の追加数学です。Heunen 論文の安全性定理として扱いません。

| 目的 | Lean の宣言と所在 | 検証した範囲と制限 |
| --- | --- | --- |
| 実際の密度演算子の混合の法則 | [MixtureLaws.lean](../../Foundation/Quantum/MixtureLaws.lean) の `mixture_congr_matrix/mixture_bind/mixture_pure/mixture_map/mixture_uniform_equiv/mixture_uniform_product/mixture_commute` | 有限確率質量関数の逐次選択、写像、一様分布の全単射と直積、独立な選択の交換を、共同行列の等式として証明します。条件付きの分布の交換は仮定しません。 |
| 既存の全乱数の分解 | [BB84RandomSource.lean](../../Foundation/Quantum/QKD/BB84RandomSource.lean) の `seedEquiv/randomized_decomposed` | アリス・ボブの独立な一様基底と一様な私的文字列を、既存の `Randomized.Seed` と全単射で対応させます。検査集合の分布と標本不足の中止条件は基底にのみ依存することを定義から確認します。 |
| 全生鍵・公開状態との一致 | 同ファイルの `record/record_eq/keyState_eq/publicState_eq` | 既存の非復元一様標本をそのまま使います。両者の私的生鍵、公開記録、中止、攻撃者の系を含む共同状態が一致します。古典観測の一致だけには限定しません。 |
| 最終出力と安全性判断の保存 | 同ファイルの `finalState/finalState_eq/secure_iff` | 任意の新鮮な種の有限分布と任意の決定的ハッシュについて、既存の `Finalization.state` と一致します。理想鍵との観測差による `IdealKey.Secure` を同じ誤差で両方向に移せます。秘密性の前提をこの等式から生成しません。 |
| 補助系を残す有限クラウス操作の純粋化 | [DilationAuxiliary.lean](../../Foundation/Quantum/DilationAuxiliary.lean) の `discardRight_amplify_apply/Channel.discard_dilation_amplify/Channel.pure_dilation/Channel.pure_dilation_unit` | 既存の `Channel.dilated` を任意の補助系へ拡大します。入力の補助系を捨てず、新しいクラウス添字レジスタだけを捨てれば元の共同作用素へ戻ります。積入力は要求しません。純粋入力に対する新しい共同ベクトルと正規化を構成します。 |
| BB84 の攻撃後の具体的な純粋入力 | [BB84PurifiedSource.lean](../../Foundation/Quantum/QKD/BB84PurifiedSource.lean) の `vector/unit/state/pure/recover` | 正規化したもつれた源に任意の有限クラウス攻撃を適用した純粋な共同ベクトルを構成します。アリス、ボブ、元の攻撃者の系、新しいレジスタを保持します。元の攻撃が純粋出力を持つとは仮定しません。 |

今回の純粋化は、有限クラウス表示を持つ既存のチャネルと純粋なもつれた源についての構成です。任意の混合密度演算子のスペクトル分解による純粋化、無限次元の一般の正常完全正値写像の表現定理は、この追加では証明していません。公開検査のビット誤りと仮想的な位相誤りの対応、標本を捨てた残りの鍵の支持条件は引き続き後続です。


### 攻撃後の相補基底の座標と、量子状態を保持する標本検査

以下は、実際の有限クラウス攻撃の純粋化へ量子標本抽出を適用する独自の追加数学です。Bouman–Fehr の定理3（§4.2、pp.11–12）の射影による評価を、構成した共同入力へ特殊化します。定理5の証明（§6、pp.19–21、特に式(2)、式(3)と図1）の本文も再確認しました。[一次資料](https://arxiv.org/pdf/0907.4246v5) では、制御 NOT と基底に依存する出力の付け替えを使い、誤り側の測定を鍵側の測定より先に行います。以下の固定した X 基底での標本検査だけで、その測定実験の同等性を証明したとは扱いません。

| 目的 | Lean の宣言と所在 | 検証した範囲と制限 |
| --- | --- | --- |
| 一部の値だけを記録する測定 | [PartitionMeasurement.lean](../../Foundation/Quantum/PartitionMeasurement.lean) の `instrument/branch_entry/probability/event_probability/acceptance` | 任意の有限な基底ラベルの関数を測定します。同じ値を与える基底方向の間の非対角成分を保持します。粗い受理判定と全検査値の記録について、確率だけを同一視します。 |
| 攻撃後の相補基底での実際の共同状態 | [BB84PhaseCoordinates.lean](../../Foundation/Quantum/QKD/BB84PhaseCoordinates.lean) の `gate/isometry/channel/vector/state/pure/unit` | ボブとアリスの全信号へ Hadamard を適用します。元の攻撃者の系とクラウス添字のレジスタへは恒等操作を適用します。出力の純粋な共同ベクトルと正規化を証明します。 |
| 具体的な誤り位置と部分測定 | 同ファイルの `pattern/label/accepted_iff/measurement/measurement_entry/label_eq_of_tested/untested_coherence/acceptance_probability` | 誤り位置は両者の相補基底の値が異なる位置です。指定した検査集合の値だけを記録します。検査で同じ値を持つ行・列なら、未検査位置や補助系の値が異なっても成分を保持します。 |
| 攻撃に依存する正規化した近似状態 | [BB84PhaseSampling.lean](../../Foundation/Quantum/QKD/BB84PhaseSampling.lean) の `joint_nonempty/fallback/fallback_pattern/fallback_good/approximation` | 正規化から補助系の基底方向を取り、両者が零の文字列を持つ誤り零の代替方向を構成します。良い射影の重みが零でも定義します。失敗上界は非復元一様標本の二項係数の比であり、量子観測差はその平方根です。 |
| 受理した詳細な記録の支持 | 同ファイルの `accepted_zero_row/accepted_measurement_zero_row` | 零許容誤りの検査を通った近似状態では、指定した誤り数以上に属する行が全て零です。詳細な記録の測定後についても別途証明し、粗い測定の事後状態の等式は使いません。 |
| メタ論理の具体化 | 同ファイルの `channels/interpreted/recorded` | 既存の `QuantumSamplingLogic` の有限導出を、任意の実際の攻撃のベクトルへ解釈します。古典的な前提は標本抽出の証明で満たします。公開標本と検査値を記録する物理的後処理後も、同じ誤差で比較します。 |

適用範囲は固定した相補基底の座標と零許容誤りの標本検査です。既存の独立な基底選択・基底照合を含む実際の `Randomized.record` の公開検査から、この支持条件を導くための制御 NOT の等式、測定の遅延、鍵側の残りの系への対応は未達です。許容誤りが正の場合の偏差評価と、原論文の指数関数による評価も別途必要です。


`PhaseSamplingExamples.lean` の `amplitude/phase_coherence/measured_coherence` は、自作の検証例です。実際の計算基底の盗聴攻撃を相補基底の座標に変換します。攻撃者の量子系の非対角成分は、検査前と、非空の検査集合で両者の零の値を記録した枝の両方で1/8です。`copyAttack` は任意長の基底の値を補助系へ保存する等長操作です。未知の重ね合わせを独立な同一状態へ複製しません。`finite_bound/interpreted_two` は2信号のうち1信号を標本にするモデルです。指定した誤り数1に対する古典上界は1/2であり、有限導出を解釈して量子観測差の上界 √(1/2) を得ます。これは最終鍵の秘密性の数値例ではありません。

### 制御 NOT による共同測定実験の変換

一次資料は Bouman–Fehr, §6、本文pp.19–20、式(2)、式(3)、図1です。この追加は Heunen の論文に安全性定理があるという主張ではありません。原典はアリス・ボブの順です。以下の行列はボブ・アリスの順とし、アリスを制御にします。

| 原典・目的 | Lean の宣言と所在 | 検証した範囲と制限 |
| --- | --- | --- |
| §6、式(2)、本文p.19の計算・Hadamard 基底での制御 NOT | [BB84ErrorTransform.lean](../../Foundation/Quantum/QKD/BB84ErrorTransform.lean) の `bit_coefficient/block_coefficient/operation` | 実際の2×2成分から証明して任意長へ拡張します。位置ごとの基底は混在できます。両者の基底は共通です。 |
| §6、式(3)、本文p.20の可逆な結果の変換 | 同ファイルの `relabel_involution/read_relabel/errorBits_relabel/keyBits_relabel` | 誤りビットは両者の排他的論理和です。鍵側の値は基底によりアリスまたはボブの値です。 |
| 図1の左・中央、本文p.20の共同状態の一致 | [BB84ErrorExperiment.lean](../../Foundation/Quantum/QKD/BB84ErrorExperiment.lean) の `amplified/recorded_of_amplified/recorded_eq` | 任意の有限補助系と共同入力を許します。実際の量子チャネル、測定、古典ラベル変換の出力行列を比較します。図1の右の遅延測定の等式は後続です。 |
| 物理的な基底の全単射と測定記録への移送 | [BasisChannel.lean](../../Foundation/Quantum/BasisChannel.lean) の `isometry/apply`、[FirstRegister.lean](../../Foundation/Quantum/FirstRegister.lean) の `complete/apply_entry/relabel` | 独自の追加数学です。補助系の非対角成分を保持します。 |
| 既存のメタ論理による有限導出 | [BB84CNOTLogic.lean](../../Foundation/Quantum/QKD/BB84CNOTLogic.lean) の `presentation/model/sound/interpretation_substitute/proof` | 独自の構文設計です。証明済み操作等式を零前提規則とし、測定、混合、後処理を前提付き規則にします。核は変更しません。 |
| 非自明な具体的モデル | [ErrorTransformExamples.lean](../../Foundation/Quantum/QKD/ErrorTransformExamples.lean) の `unit/input_coherence/amplitude/measured_coherence/interpreted` | 独自の三量子ビットのもつれた例です。入力の非対角成分1/2と、測定枝内の攻撃者の非対角成分1/8を計算します。最終鍵の安全性を結論しません。 |

独立な基底選択の後の一致位置の選別は、この共通基底の実験へまだ接続していません。原典の定理5全体の形式化として扱うためには、この選別、誤り側と鍵側の測定順序、残りの鍵の支持、秘密増幅への移送が必要です。

### 誤り側と鍵側の測定順序

一次資料は Bouman–Fehr §6、本文p.20、図1の中央・右と直後の遅延測定の説明です。次の段落（本文p.21）は例5の対ごとの選択を適用し、アリス側 X・ボブ側 Z の参照基底を使います。以下の操作等式だけで、この標本抽出と最終鍵の安全性まで証明したとは扱いません。

| 原典・目的 | Lean の宣言と所在 | 検証した範囲と制限 |
| --- | --- | --- |
| 図1の中央・右、本文p.20の測定順序 | [PartitionDelay.lean](../../Foundation/Quantum/PartitionDelay.lean) の `record_entry/branches_commute/sequential/simultaneous/sequential_eq` | 二つの有限ラベルの実際の測定を順に合成します。両方の古典レジスタと残りの量子出力の等式を証明します。途中の状態と全測定後の状態は区別します。 |
| 誤りビットと鍵ビットへの特殊化 | [BB84DelayedMeasurements.lean](../../Foundation/Quantum/QKD/BB84DelayedMeasurements.lean) の `errorLabel/keyLabel/first/first_entry/delayed_eq/of_coherent` | 任意長の共通基底と任意の共同入力を許します。攻撃者の補助系は有限で、信号と相関していて構いません。独立な基底選択・選別への接続は未達です。 |
| 既存のメタ論理への接続 | [BB84CNOTLogic.lean](../../Foundation/Quantum/QKD/BB84CNOTLogic.lean) の `Rule.delay/model/sound/interpretation_substitute/delayedProof` | 制御 NOT の作用素等式を前提とする独自の規則です。規則の妥当性を測定順序の定理で証明します。導出全体と仮定置換は既存の核で扱います。 |
| 未測定部分に量子相関が残る具体例 | [ErrorTransformExamples.lean](../../Foundation/Quantum/QKD/ErrorTransformExamples.lean) の `transformed_amplitude/transformed_rank/error_first_coherence/delayed_interpreted` | 実際の制御 NOT 後の三量子ビットのもつれた状態を使います。誤り側の測定後も異なる鍵値・攻撃者の値の間の成分1/8が残ります。独自の例です。 |

公開の受理・中止処理を二つの測定の間に挿入する等式、信号の破棄と既存の古典記録との対応、例5の古典・量子標本抽出、秘密増幅への支持条件の移送は後続です。原典より強い積入力・独立攻撃の仮定は追加していません。

### 二つの測定の間に公開判定を挿入する構成

原典の対応箇所は Bouman–Fehr §6、本文p.20、図1の直後の遅延測定の説明です。下記の最小鍵長と整数の許容誤り数を明示する構文は、既存の実験へ接続する独自の設計です。

| 目的 | Lean の宣言と所在 | 検証した範囲と制限 |
| --- | --- | --- |
| 測定枝への物理的後処理と全記録の等式 | [InstrumentPost.lean](../../Foundation/Quantum/InstrumentPost.lean) の `post/post_apply/record_congr` | 完全性を既存のクラウスチャネルの完全性から証明します。確率零の枝も正規化せず扱います。 |
| 公開判定の順序の変更 | [PartitionDecision.lean](../../Foundation/Quantum/PartitionDecision.lean) の `test_entry/decideBefore/decideAfter/decision_branch/decision_entry/decision_record` | 第一のラベルだけに依存する判定を、第二の測定の前後へ移します。受理・中止の双方と量子出力を保持します。 |
| 既存の BB84 の公開判定との対応 | [BB84DelayedDecision.lean](../../Foundation/Quantum/QKD/BB84DelayedDecision.lean) の `accepts/raw_accepts/branch_eq/record_eq/of_coherent` | 共通基底について `RawProtocol.accepts` と一致します。最小の残りの鍵長と任意の許容誤り数を扱います。独立基底選択・選別や外側の標本数の条件は別途接続が必要です。 |
| メタ論理と具体的なモデル | [BB84CNOTLogic.lean](../../Foundation/Quantum/QKD/BB84CNOTLogic.lean) の `Rule.decide/model/sound/interpretation_substitute/decisionProof`、[ErrorTransformExamples.lean](../../Foundation/Quantum/QKD/ErrorTransformExamples.lean) の `sample_decisions/length_abort/accepted_coherence/decision_interpreted` | 証明済みの操作等式を前提とする有限規則です。もつれた実入力で受理枝の攻撃者の成分1/8を検証します。具体例は全信号を標本とするので、最終鍵の安全性は主張しません。 |

中止時にも後から測った鍵値を残す拡張出力を使っています。中止時の鍵値や量子信号を捨て、既存の最終記録と一致させる証明は後続です。この拡張出力をそのまま実プロトコルの公開記録とは扱いません。

### 信号の破棄と既存の生鍵出力形式

原典の対応箇所は Bouman–Fehr §6、本文p.20、式(3)と図1です。以下の部分トレースと既存の `RawProtocol.Output` への接続は独自の追加数学です。

| 目的 | Lean の宣言と所在 | 検証した範囲と制限 |
| --- | --- | --- |
| 測定後の信号だけを捨てる構成 | [PartitionDiscard.lean](../../Foundation/Quantum/PartitionDiscard.lean) の `discard_entry/discard_eq/sequential_discard_eq` | 任意の共同入力作用素を扱います。部分測定の後で信号を捨てた出力は、全信号を測定して余分な古典情報を忘れた出力と一致します。補助系の非対角成分を保持します。 |
| 可逆な誤り・鍵の座標と元の値の復元 | [BB84OutcomeCoordinates.lean](../../Foundation/Quantum/QKD/BB84OutcomeCoordinates.lean) の `decode_encode/encode_decode/equivalence/originalOutcomes_encode` | 任意長、位置ごとに Z/X が混在する共通基底を扱います。行列の信号の順序はボブ・アリスです。 |
| 既存の生鍵・公開出力形式との等式 | [BB84DeferredRaw.lean](../../Foundation/Quantum/QKD/BB84DeferredRaw.lean) の `recover_signal/abort_keys/output_of_coherent/output_eq/public_eq` | 制御 NOT と順次測定の実際の出力を、通常の共通基底測定から作る `RawProtocol.output` と比較します。信号は捨て、補助系を残します。中止時の私的鍵は全て空です。全乱数を含む `RawProtocol.record` との一致は別途必要です。 |
| メタ論理と具体例 | [BB84CNOTLogic.lean](../../Foundation/Quantum/QKD/BB84CNOTLogic.lean) の `Rule.rawOutput/model/sound/interpretation_substitute/rawProof`、[ErrorTransformExamples.lean](../../Foundation/Quantum/QKD/ErrorTransformExamples.lean) の `raw_key_present/raw_interpreted/raw_abort_interpreted` | 制御 NOT の等式を前提とする有限規則です。もつれた同じ入力に受理時・中止時の導出を解釈します。未検査の鍵を残す具体例には標本がないため、秘密性を主張しません。 |

明示的な判定レジスタを持つ前節の `before` との合成、独立な基底の照合・選別、外側の標本数の条件、対ごとの標本抽出と位相支持の接続は引き続き後続です。

### 公開判定から生鍵出力までのチャネルの合成

原典との対応箇所は Bouman–Fehr §6、本文p.20、図1の直後の遅延測定の説明です。重複する古典レジスタの破棄と既存の生鍵レコードの復元は独自の追加数学です。

| 目的 | Lean の宣言と所在 | 検証した範囲と制限 |
| --- | --- | --- |
| 明示的な判定レジスタを物理的に捨てる | [InstrumentForgetRecord.lean](../../Foundation/Quantum/InstrumentForgetRecord.lean) の `forgetRecord_apply/forget_record` | 装置の全枝を足す非選択的な作用素と、古典レジスタの部分トレースが一致します。量子出力を保持します。 |
| 記録済みのラベルを読む判定の非選択的な作用 | [PartitionDecisionForget.lean](../../Foundation/Quantum/PartitionDecisionForget.lean) の `decision_forget/decision_record_forget` | 判定は第一の古典ラベルだけに依存します。判定レジスタを捨てると元の順次測定に戻ります。受理枝だけへ条件付ける等式ではありません。 |
| 早い公開判定から既存の生鍵・公開出力まで | [BB84DecisionRaw.lean](../../Foundation/Quantum/QKD/BB84DecisionRaw.lean) の `recovered_acceptance/decided_deferred/output_of_coherent/output_eq/public_eq` | 一つの物理的チャネルとして合成します。中止時の私的鍵は空で、受理・中止フラグは最終記録に残します。信号を捨て、攻撃者の系を残します。対象は共通基底です。 |
| メタ論理と具体例 | [BB84CNOTLogic.lean](../../Foundation/Quantum/QKD/BB84CNOTLogic.lean) の `Rule.decisionRaw/model/sound/interpretation_substitute/decidedRawProof`、[ErrorTransformExamples.lean](../../Foundation/Quantum/QKD/ErrorTransformExamples.lean) の `decidedRaw_interpreted/decidedRaw_abort_interpreted` | 同じもつれた入力に、鍵位置を残す場合と鍵長不足による中止の場合の閉導出を解釈します。最終鍵の秘密性は結論しません。 |

通常の共通基底測定と既存の準備実験 `BB84RawSource`・`RawProtocol.record` との接続、および独立基底選択・選別を含む全分布の対応は後続です。

### 共通基底での実際の準備実験への接続

上記の後続条件のうち、共通基底の準備実験との接続を追加しました。原典の対応箇所は Bouman–Fehr §6、本文pp.19–20の源の置換、本文p.20の式(3)と図1です。以下の測定表現の対応、信号の破棄、既存のレコードとの一致は独自の追加数学です。

| 目的 | Lean の宣言と所在 | 検証した範囲と制限 |
| --- | --- | --- |
| 因子の移送と局所的な操作 | [TensorExchange.lean](../../Foundation/Quantum/TensorExchange.lean) の `operation/local_operations` | ボブ・攻撃者・アリスの順序をボブ・アリス・攻撃者へ移します。任意の共同入力作用素を扱います。 |
| 二つの測定表現の対応 | [BasisRecordDiscard.lean](../../Foundation/Quantum/BasisRecordDiscard.lean) の `basis_record_discard`、[InstrumentRecordPre.lean](../../Foundation/Quantum/InstrumentRecordPre.lean) の `amplify_record_pre_apply` | 測定前のチャネルと測定対象の破棄を、補助系を保持した古典・量子記録へ接続します。 |
| 基底・標本に依存しない実入力 | [BB84PreparedInput.lean](../../Foundation/Quantum/QKD/BB84PreparedInput.lean) の `input/common_rotated/slice/measured_block` | 最大にもつれた源と、送信列全体への任意の有限クラウス攻撃を使います。測定ブロックが、実際の一様な準備文字列の重み付き状態と一致します。補助系の非対角成分を含みます。 |
| 既存の私的・公開出力との一致 | [BB84PreparedRaw.lean](../../Foundation/Quantum/QKD/BB84PreparedRaw.lean) の `raw_record_discard/reference_prepared/decided_prepared/public_prepared` | 共通基底での `RawProtocol.record` の平均と一致します。ボブの量子出力だけを捨てます。公開投影は `RawProtocol.publicState` の平均と一致します。任意長・任意の指定標本・最小鍵長・許容誤り数を扱います。 |
| 有限導出の解釈と実際の攻撃例 | [BB84PreparedRawInterpretation.lean](../../Foundation/Quantum/QKD/BB84PreparedRawInterpretation.lean) の `interpreted/public_interpreted/public_experiment`、[ErrorTransformExamples.lean](../../Foundation/Quantum/QKD/ErrorTransformExamples.lean) の `prepared_attack_interpreted/prepared_attack_abort_interpreted` | 既存の `decidedRawProof` と `sound` を実入力へ適用します。計算基底を記録する攻撃では X 準備のボブ・攻撃者間の成分1/2を確認します。同じ攻撃で鍵位置を残す設定と鍵長不足による中止を解釈します。秘密性は結論しません。 |

両者の基底が異なる位置の選別と再配置を含む、独立基底・標本の全分布への適用は後続です。既存の `BB84RandomSource` による全乱数の源の置換自体は証明済みですが、今回の共通基底の変換をその実験へ適用する証明はまだ必要です。対ごとの選択による標本抽出、位相側の支持への近似、秘密増幅、誤り訂正・認証の未達条件は維持します。

### 独立基底の一致位置による分解と量子信号の再配置

Bouman–Fehr §6 の本文p.19は既に共通基底のもつれた源を使います。以下は、このリポジトリの独立基底の準備方式から、本文p.20の式(3)・図1の実験へ接続するための追加数学です。原典の明示的な推論体系ではありません。

| 目的 | Lean の宣言と所在 | 検証した範囲と制限 |
| --- | --- | --- |
| 一致位置と基底の独立な乱数 | [BB84SiftingRandomness.lean](../../Foundation/Quantum/QKD/BB84SiftingRandomness.lean) の `basisEquiv/matched_bob/test_eq/length_eq/source_record_eq/record_eq/keyState_eq/publicState_eq` | 一致位置を全ての部分集合上で一様に選び、アリスの基底を独立に一様に選ぶ実験が、実際の独立基底の実験と一致します。検査分布、標本数不足の中止、私的・公開記録と量子補助系を含みます。 |
| 相関を保持した信号の再配置 | [BB84SiftedInput.lean](../../Foundation/Quantum/QKD/BB84SiftedInput.lean) の `join_split/split_join/splitEquiv/jointEquiv/input/input_entry/common_bases` | 一致位置のボブ・アリスを前へ集め、残りの両者の信号と攻撃者を量子補助系として保持します。実際の攻撃後の源を使います。入力は基底・標本に依存しません。 |
| 基底操作と再配置の整合性 | [BB84SiftedGates.lean](../../Foundation/Quantum/QKD/BB84SiftedGates.lean) の `gate_entry/product_split/split_gate_entry/gate_operation/fullGate_isometry/selectedGate_isometry/gate_apply` | 任意の共同入力作用素で証明します。残りの位置でも各位置の基底操作を行います。位置ごとの独立状態は仮定しません。 |
| 保持する基底と残りの基底の独立性 | [BB84SiftedBases.lean](../../Foundation/Quantum/QKD/BB84SiftedBases.lean) の `basesEquiv/uniform_bases_split/record_split_eq` | 一致位置を固定した後で二つの基底文字列が独立に一様となることです。実際の `Randomized.record` の全共同状態へ適用します。 |
| メタ論理と実際の攻撃による検証 | [BB84SiftedInput.lean](../../Foundation/Quantum/QKD/BB84SiftedInput.lean) の `interpreted`、[SiftingExamples.lean](../../Foundation/Quantum/QKD/SiftingExamples.lean) の `counts/source_input_coherence/selected_coherence/selected_interpreted/randomized_public_interpreted` | 既存の `decidedRawProof` と `sound` を再配置後の実入力に適用します。計算基底を記録する攻撃で非対角成分1/2を保持します。核と規則を変更しません。 |

保持する位置の番号への検査集合の再符号化、検査分布・誤り数・鍵長の対応、残りの位置の測定と公開情報の処理、元の生鍵レコードの復元は後続です。選別後の閉導出の解釈と元の全出力の一致は、まだ一つの定理へ合成していません。対ごとの選択による標本抽出と最終鍵の秘密性への接続も未達です。

### 選別後の検査集合と元の生鍵レコードの対応

上記の条件のうち、検査集合・分布・判定・生鍵の復元を追加しました。Bouman–Fehr §6、本文p.19の一様検査集合と、本文p.20の式(3)・図1への接続のための追加数学です。

| 目的 | Lean の宣言と所在 | 検証した範囲と制限 |
| --- | --- | --- |
| 一様な非復元標本の移送 | [SamplingTransport.lean](../../Foundation/Quantum/QKD/SamplingTransport.lean) の `sample_congr/uniform_map_embedding/sample_map` | 単射で母集団と検査集合の番号を変更します。誤り位置の独立性は不要です。 |
| 検査集合の両方向の対応と分布 | [BB84SiftedTests.lean](../../Foundation/Quantum/QKD/BB84SiftedTests.lean) の `restrict_lift/lift_restrict/lift_card/restrict_card/lift_univ/lift_powersetCard/sample_lift/testDistribution_lift` | 元の検査集合は一致位置内とします。標本不足時の空集合を含み、既存の全分布を保存します。 |
| 誤り数・鍵長・受理判定 | [BB84SiftedDecision.lean](../../Foundation/Quantum/QKD/BB84SiftedDecision.lean) の `errors_eq/key_card/accepts_eq/requiredLength_eq/key_mem/private_keys` | 任意の許容誤り数と最小鍵長を扱います。受理・中止双方の私的鍵を比較します。位相誤りの評価ではありません。 |
| 全古典出力の復元 | [BB84SiftedOutput.lean](../../Foundation/Quantum/QKD/BB84SiftedOutput.lean) の `expand_index/expand_test/restore_output` | 元の公開基底を明示します。検査集合・両者の公開検査値・受理フラグ・両者の私的鍵が既存の出力と一致します。 |
| 実際の全共同状態と閉導出の解釈 | [BB84SiftedRecord.lean](../../Foundation/Quantum/QKD/BB84SiftedRecord.lean) の `reindexed_record_eq/reindexed_public_eq/restored_interpreted` | 全乱数を含む準備実験へ検査分布の対応を適用します。別途、再配置後の実入力に解釈した閉導出へ物理的な復元チャネルを適用します。核・規則を変更しません。 |
| 具体的な検証 | [SiftingExamples.lean](../../Foundation/Quantum/QKD/SiftingExamples.lean) の `reindexed_public_interpreted/restored_attack_interpreted/reindexed_error_abort` | 実際の等長攻撃で公開状態と閉導出を検証します。2位置のうち一つが一致し、そこに検査誤りがある場合に両番号で中止します。独自の例です。 |

再配置後の残りの量子信号の測定・破棄を含む全出力の一致は後続です。復元した選別後の閉導出の出力には、まだその量子信号が補助系として残ります。元の準備実験との合成、対ごとの選択による量子標本抽出、最終鍵の安全性へ進むための未達条件を保持します。

### 選別しない信号の操作と物理的破棄

上記の条件のうち、残りの信号の破棄と局所的な基底操作を処理しました。Bouman–Fehr §6、本文p.20の図1と遅延測定の説明への接続のための追加数学です。

| 目的 | Lean の宣言と所在 | 検証した範囲と制限 |
| --- | --- | --- |
| 捨てる信号の局所的な操作 | [DiscardMiddleLocal.lean](../../Foundation/Quantum/DiscardMiddleLocal.lean) の `middle_local_entry/discardMiddle_local` | 任意の共同入力作用素の各ブロックを共役で表します。中央への等長操作は部分トレース後の両端の共同状態を変えません。 |
| 部分測定と不要な全測定ラベルの破棄 | [FirstRegisterSplit.lean](../../Foundation/Quantum/FirstRegisterSplit.lean) の `selectedDiscard_entry/selectedDiscard_eq/selectedDiscard_full/local_record/discard_local_record` | 第一の信号だけを記録して第二を捨てる出力は、全測定から第二の古典ラベルを忘れた出力と一致します。途中の量子状態の同一視はしません。 |
| 生鍵番号の復元と信号の破棄を閉導出へ合成 | [BB84SiftedDiscard.lean](../../Foundation/Quantum/QKD/BB84SiftedDiscard.lean) の `finish/delayedOutput/referenceOutput/finished_interpreted/public_finished_interpreted` | 再配置後の実際の攻撃入力へ解釈した閉導出を使います。元の攻撃者の補助系を残します。核・規則の変更はありません。 |
| 実際の異なる基底操作の処理 | 同ファイルの `unmatched_irrelevant/unmatchedGate_isometry/unmatched_basis_irrelevant` | 残りの位置で両者が使う実際の操作を構成し、等長性から破棄後の出力不変を得ます。 |
| 実際の攻撃での検証 | [SiftingExamples.lean](../../Foundation/Quantum/QKD/SiftingExamples.lean) の `discarded_attack_interpreted/unmatched_attack_irrelevant` | 以前と同じ非自明な等長攻撃を使います。全ての位置の基底が異なる具体例は鍵長不足で中止し、秘密鍵の安全性は主張しません。 |

異なる信号空間間の全測定記録の移送、異なる両者の基底を含む源のブロックと準備実験の対応、および `reindexedRecord` との全出力等式への合成は後続です。物理的な出力空間が一致することだけで元の実験との等式を達成したとは扱いません。


## 独立基底の全準備実験への接続

| 原典の参照 | Lean の宣言と所在 | 対応の範囲・追加数学 |
| --- | --- | --- |
| Bouman–Fehr §6 本文p.18の準備方式との関係、p.19のプロトコル | [BB84MixedPreparedInput.lean](../../Foundation/Quantum/QKD/BB84MixedPreparedInput.lean) の `rotated`、`slice`、`measured_block` | アリスとボブの基底を別々に指定した実際の攻撃後の源の測定成分です。全ブロックへの任意の有限 Kraus 攻撃と攻撃者の全行列成分を扱います。有限行列の構成は追加数学です。 |
| 同上。p.19の原典の方式は共通基底です。 | [BB84MixedPreparedRaw.lean](../../Foundation/Quantum/QKD/BB84MixedPreparedRaw.lean) の `reference_prepared`、`source_interpreted`、`public_experiment` | 独立基底と選別を含む元の準備実験の全生鍵・公開記録・攻撃者の共同状態との等式です。既存の源の置換の閉導出を解釈して合成します。 |
| 同上。独立基底を選別する今回の実装の追加数学 | [BB84MixedRandomSource.lean](../../Foundation/Quantum/QKD/BB84MixedRandomSource.lean) の `source_interpreted`、`record_eq`、`public_eq` | 全基底・検査集合について平均した実際の乱択実験の全出力です。検査分布と不足時の中止条件を保持します。最終鍵の安全性は主張しません。 |
| 空間の再配置に関する追加数学 | [FirstRegisterTransport.lean](../../Foundation/Quantum/FirstRegisterTransport.lean) の `transport` | 異なる有限量子空間間の基底の全単射に沿った全測定記録の対応です。補助系を保持します。選別後の遅延実験との全合成は未達です。 |
| 独自の検証例 | [SiftingExamples.lean](../../Foundation/Quantum/QKD/SiftingExamples.lean) の `mixed_attack_interpreted`、`mixed_randomized_interpreted`、`mixed_public_interpreted` | 共同非対角成分を持つ実際の等長攻撃に適用します。異なる X/Z 基底と、独立基底を全て平均した場合を確認します。 |


## 選別後の遅延測定と元の全出力の合成

| 原典の参照 | Lean の宣言と所在 | 対応の範囲・追加数学 |
| --- | --- | --- |
| 信号の再配置と測定に関する追加数学 | [BB84SiftedMeasurement.lean](../../Foundation/Quantum/QKD/BB84SiftedMeasurement.lean) の `signal_associate`、`selected_record` | 全信号の測定から不要な古典ラベルを忘れる処理と、保持する信号だけの測定・残りの量子信号の部分トレースの対応です。全共同入力作用素を扱います。 |
| Bouman–Fehr §6 本文pp.18–19の準備方式とプロトコル、p.20式(3)・図1 | [BB84SiftedFullRecord.lean](../../Foundation/Quantum/QKD/BB84SiftedFullRecord.lean) の `restored_measurement`、`full_reference`、`delayed_prepared`、`delayed_source` | 独立基底の選別、元の位置番号の復元、実際の基底操作と物理的な破棄を合成します。源の置換と誤り側を先に測定する閉導出の解釈を元の全出力へ接続します。原典の共通基底の方式を独立基底の選別へ対応させる追加数学です。 |
| 同上。全乱択分布への追加数学 | [BB84SiftedRandomExperiment.lean](../../Foundation/Quantum/QKD/BB84SiftedRandomExperiment.lean) の `delayed_reindexed`、`delayed_record_eq`、`delayed_public_eq` | 全基底・検査集合を平均した選別後の遅延実験と元の乱択準備実験の全出力・公開出力の等式です。不足時の中止と攻撃者の量子状態を保持します。秘密増幅の前提や安全性評価は未達です。 |
| 独自の検証例 | [SiftingExamples.lean](../../Foundation/Quantum/QKD/SiftingExamples.lean) の `delayed_attack_prepared`、`delayed_unmatched_source`、`delayed_randomized_public` | 非零の共同非対角成分を持つ実際の等長攻撃に適用します。保持する信号がある場合、ない場合、全乱択公開実験を検証します。 |


## 固定基準での対ごとの測定への対応

| 原典の参照 | Lean の宣言と所在 | 対応の範囲・追加数学 |
| --- | --- | --- |
| Bouman–Fehr §6 本文p.21の固定基準 | [BB84PairwiseReference.lean](../../Foundation/Quantum/QKD/BB84PairwiseReference.lean) の `factor`、`basis_factor`、`key_support` | ボブZ・アリスXの固定基準と、誤りビットを変えない鍵側の基底操作へ、実際の共通基底操作を分解します。任意の共同作用素を扱う追加数学です。 |
| 同p.20図1、p.21の測定の説明 | [BB84PairwiseMeasurement.lean](../../Foundation/Quantum/QKD/BB84PairwiseMeasurement.lean) の `branch_key`、`actual_reference`、`existing_first_reference` | 非正規化の各測定枝と全記録の等式です。基底に依存しない固定入力からの誤り側の測定へ対応させ、既存の第一測定チャネルへ接続します。鍵側の操作を省略した途中状態を同一視しません。 |
| 例5 本文p.8、§6 p.21 | [BB84PairwiseSelection.lean](../../Foundation/Quantum/QKD/BB84PairwiseSelection.lean) の `selectorEquiv`、`selected_bits`、`complementary_bits`、`uniform_selector` | 一様な基底列と各対から一方を選ぶ二値列の対応です。検査集合との共同分布の集中評価は未達です。 |
| 独自の有限対象論理 | [BB84PairwiseLogic.lean](../../Foundation/Quantum/QKD/BB84PairwiseLogic.lean) の `presentation`、`model`、`sound`、`interpretation_substitute`、`firstProof`、`proof` | 第一測定、混合、物理的後処理の規則とその妥当性、既存メタ論理による健全性・仮定置換です。原典にこの構文が掲載されているとは主張しません。 |
| 実際の独立基底選別への追加数学 | [BB84PairwiseSource.lean](../../Foundation/Quantum/QKD/BB84PairwiseSource.lean) の `selected_interpreted`、`uniform_reference`、`public_interpreted` | 実際の攻撃後の選別入力への閉導出の解釈です。平均した基底列と公開レジスタへ保持した基底列を区別します。 |
| 独自の検証例 | [PairwiseExamples.lean](../../Foundation/Quantum/QKD/PairwiseExamples.lean) の `attacked_interpreted`、`mixed_interpreted`、`public_interpreted`、`attacked_coherence` | 共同非対角成分が非零の実際の等長攻撃に適用します。量子標本抽出の誤差上界や最終鍵の安全性は未達です。 |


## 対ごとの標本抽出の有限事象数と量子近似

| 原典の参照 | Lean の宣言と所在 | 対応の範囲・追加数学 |
| --- | --- | --- |
| Bouman–Fehr 例5 本文p.8、付録B.5 pp.25–26 | [PairwiseSampling.lean](../../Foundation/Quantum/QKD/PairwiseSampling.lean) の `independent`、`probability_count`、`classical`、`errorBound_formula` | 二値選択と固定サイズ検査の実際の共同分布、および有限事象数による正確な最悪確率です。整数偏差を使います。指数関数による解析的上界は未達です。 |
| 同§4の古典的誤差から量子近似への構成、§6 p.21の位相支持 | [PairwiseQuantumSampling.lean](../../Foundation/Quantum/QKD/PairwiseQuantumSampling.lean) の `approximation`、`supported`、`interpreted`、`observed_tested`、`observed_zero_row` | 公開選択・検査集合を保持した、良い支持の正規化された近似状態です。実際の記録された検査値との偏差条件と理想測定枝の支持を結びます。鍵側の基底操作前の主張です。 |
| 同§6 p.20の純粋な共同状態への移行とp.21の固定基準 | [PairwiseAttackSampling.lean](../../Foundation/Quantum/QKD/PairwiseAttackSampling.lean) の `pure`、`unit`、`approximation` | 実際の任意の有限 Kraus 攻撃を純粋化し、選別して固定基準へ移した状態に適用します。追加環境・残りの信号を保持します。元の出力への部分トレースとの全合成は未達です。 |
| 独自の有限検証例 | [PairwiseSamplingExamples.lean](../../Foundation/Quantum/QKD/PairwiseSamplingExamples.lean) の `two_signal_max`、`two_signal_error` | 2対・検査1位置・整数偏差1で、8通り中最大4通り、確率 `1/2` をカーネルで検証します。 |
| 独自の実際の攻撃例 | [PairwiseAttackExamples.lean](../../Foundation/Quantum/QKD/PairwiseAttackExamples.lean) の `attacked_X_coherence`、`approximation`、`interpreted` | 2信号の計算基底を記録する等長攻撃です。X入力の共同非対角成分 `1/4` と誤差 `sqrt(1/2)`、既存メタ論理への解釈を検証します。最終鍵の安全性は未達です。 |

## 公開選択値を保持した詳細測定と量子標本近似

| 原典の参照 | Lean の宣言と所在 | 対応の範囲・追加数学 |
| --- | --- | --- |
| 独自の有限チャネル構成 | [RetainedControl.lean](../../Foundation/Quantum/RetainedControl.lean) の `tag`、`channel`、`apply_entry`、`public_apply` | 古典的な制御値を出力にも保持する、任意の補助系を含む物理的なチャネルです。作用素の全成分を扱います。 |
| Bouman–Fehr §6 図1・遅延測定、本文p.20、固定基準・位相支持p.21 | [PairwiseRecordedSampling.lean](../../Foundation/Quantum/QKD/PairwiseRecordedSampling.lean) の `measurement`、`real_eq`、`ideal_eq`、`approximation`、`ideal_zero_row`、`observed_zero_row` | 同じ実際の選択依存の詳細測定を量子近似の両側に適用し、公開選択・検査集合と詳細記録を保持します。記録値による支持条件は鍵側の操作前です。詳細な誤り列全ての公開や最終鍵の安全性は主張しません。 |
| 独自の対象論理の解釈の一般化 | [QuantumSamplingLogic.lean](../../Foundation/Quantum/QKD/QuantumSamplingLogic.lean) の `model`、`sound`、`interpretation_substitute`、[PairwiseRecordedSampling.lean](../../Foundation/Quantum/QKD/PairwiseRecordedSampling.lean) の `interpreted` | 記録追加で出力空間が変わる後処理を扱います。構文・メタ論理の核はそのままで、古典的前提は実際の有限事象数の証明で満たします。 |
| 同§6 本文pp.20–21への適用と独自の検証例 | [PairwiseRecordedExamples.lean](../../Foundation/Quantum/QKD/PairwiseRecordedExamples.lean) の `attacked_real`、`attacked_approximation`、`attacked_interpreted`、`two_signal_approximation` | 実際の任意の有限 Kraus 攻撃の純粋化した選別入力、非零の共同コヒーレンスを持つ2信号攻撃への接続です。追加環境の回復と全最終出力への合成は後続の義務です。 |

## 純粋化の回復と元のBB84第一測定

| 原典の参照 | Lean の宣言と所在 | 対応の範囲・追加数学 |
| --- | --- | --- |
| 独自の有限チャネル構成 | [NestedDiscard.lean](../../Foundation/Quantum/NestedDiscard.lean) の `channel`、`apply_entry`、`local_operations`、[NestedDiscardRecord.lean](../../Foundation/Quantum/NestedDiscardRecord.lean) の `record` | 入れ子の最後の追加環境だけを捨てる部分トレースです。任意の信号チャネル・詳細測定記録と交換し、他の系を保持します。 |
| 独自の測定装置の合成補題 | [RetainedInstrumentPost.lean](../../Foundation/Quantum/RetainedInstrumentPost.lean) の `retained_post`、`record_pre` | 記録を保持した物理的前処理・後処理と、測定装置の各枝への操作の一致です。 |
| Bouman–Fehr §6 本文p.20の純粋な共同入力への移行 | [PairwiseRecovery.lean](../../Foundation/Quantum/QKD/PairwiseRecovery.lean) の `selected`、`reference`、[PairwiseRecordedRecovery.lean](../../Foundation/Quantum/QKD/PairwiseRecordedRecovery.lean) の `actual_eq`、`recovered_approximation` | 任意の有限 Kraus 攻撃の追加環境の回復を、選別・固定基準の操作・公開記録付き詳細測定の後まで合成します。元の攻撃者の系と選別されなかった信号は保持します。 |
| 同§6 本文p.21の固定基準と位相支持 | [PairwiseRecoveredSupport.lean](../../Foundation/Quantum/QKD/PairwiseRecoveredSupport.lean) の `approximant_eq`、`recovered_zero_row`、`recovered_observed_zero_row` | 同じ回復後の正規化した近似状態の支持です。実際の誤り記録による検査重みを使います。相補的な鍵側の操作前の主張です。 |
| 同§6 図1と測定の遅延、本文pp.20–21 | [PairwiseRecoveredFirst.lean](../../Foundation/Quantum/QKD/PairwiseRecoveredFirst.lean) の `key_public`、`original_eq`、`original_approximation` | 鍵側の操作を加えた実状態は、元の攻撃後の選別入力に既存の `actualFirst` を作用させた状態と等しく、同じ標本誤差で近似できます。最終生鍵の全出力への近似誤差の合成は未達です。 |
| 独自の有限導出の解釈と検証例 | [PairwiseRecoveredSupport.lean](../../Foundation/Quantum/QKD/PairwiseRecoveredSupport.lean) の `recovered_interpreted`、[PairwiseRecoveryExamples.lean](../../Foundation/Quantum/QKD/PairwiseRecoveryExamples.lean) の `original_interpreted`、`two_signal_original` | 詳細測定・回復・鍵側操作の実際の合成を後処理規則へ解釈します。古典的前提は証明済みです。2信号の非自明な攻撃に適用します。 |

## 中止を含む全乱数化生鍵出力への標本近似

| 原典の参照 | Lean の宣言と所在 | 対応の範囲・追加数学 |
| --- | --- | --- |
| Bouman–Fehr §6 図1・測定の遅延、本文p.20 | [PairwiseRawPost.lean](../../Foundation/Quantum/QKD/PairwiseRawPost.lean) の `afterFirst`、`after_first_decided`、`restore`、`restored_prepared` | 鍵測定・検査による受理／中止・中止時の生鍵消去・元の位置の復元を含む、既存の実際の準備実験との全出力等式です。 |
| 同§6 本文p.21の標本近似の後の鍵測定 | [PairwiseRawSampling.lean](../../Foundation/Quantum/QKD/PairwiseRawSampling.lean) の `real_eq`、`approximation`、`interpreted` | 公開選択・検査集合を保持した、同じ実状態と構成した近似状態への誤差移送です。選別集合と残りの基底は固定し、十分な検査数の場合を扱います。 |
| 独自の有限乱数・物理的除去の補題 | [PublicMixtureForget.lean](../../Foundation/Quantum/PublicMixtureForget.lean) の `publicMixture_forget`、[PairwiseRawMarginal.lean](../../Foundation/Quantum/QKD/PairwiseRawMarginal.lean) の `marginal_delayed`、`marginal_approximation` | 追加した選択・検査のコピーだけを捨て、元の全公開記録を保持します。実際の一様基底と新鮮な非復元検査の共同分布を使用します。 |
| 同§6への実際の独立基底・全乱数の接続 | [PairwiseRandomizedSampling.lean](../../Foundation/Quantum/QKD/PairwiseRandomizedSampling.lean) の `conditional_approximation`、`approximation`、`public_approximation` | 検査位置不足の中止枝も保持した、元の `Randomized.record` と公開状態全体への近似です。誤差は選別集合の実際の確率で平均した有限式です。秘密鍵の理想資源との比較や指数関数上界は未達です。 |
| 独自の検証例 | [PairwiseRawExamples.lean](../../Foundation/Quantum/QKD/PairwiseRawExamples.lean) の `two_signal_total_error`、`attacked_randomized`、`attacked_public` | 共同コヒーレンスが非零の2信号攻撃で、全4選別集合を平均した誤差 `(1/4) * sqrt(1/2)` を検証します。安全な最終鍵の生成は主張しません。 |
| 独自の既存有限推論規則への解釈 | [PairwiseRandomizedLogic.lean](../../Foundation/Quantum/QKD/PairwiseRandomizedLogic.lean) の `randomized_interpreted`、`interpreted_real_eq`、`interpreted_ideal_eq`、`interpreted_error_eq` | 全実験の混合を既存 `StateDistanceLogic` の導出へ解釈し、前提を証明で満たします。状態の両側と誤差の式を対応させます。核や規則の追加変更はありません。 |


## 標本近似状態の実際の位相支持と秘密増幅

原典は Bouman–Fehr §6 本文p.21です。以下の有限行列による作用素順序の証明と対象論理の解釈は追加数学です。原典の条件付き最小エントロピーの表現との同値性は未証明です。

| 原典の参照 | Lean の宣言と所在 | 対応の範囲・追加数学 |
| --- | --- | --- |
| 同p.21の固定基準と反対の基底での測定 | [PairwisePhaseCoordinates.lean](../../Foundation/Quantum/QKD/PairwisePhaseCoordinates.lean) の `key_coefficient`、[PairwisePhaseAmplitude.lean](../../Foundation/Quantum/QKD/PairwisePhaseAmplitude.lean) の `rotated_amplitude` | 任意の混在基底を誤り・鍵座標へ可逆に変更し、実際の鍵ゲートの全係数と補助系付きの振幅を与えます。 |
| 同p.21の良いハミング重みの重ね合わせ | [PairwisePhaseSlices.lean](../../Foundation/Quantum/QKD/PairwisePhaseSlices.lean) の `slice_supported`、`supported_amplitude`、[PairwisePhaseBand.lean](../../Foundation/Quantum/QKD/PairwisePhaseBand.lean) の `phaseSet_band` | 既存の同じ支持射影で構成した近似状態の支持を、実際の誤り記録から定まる整数ハミング重みの帯と同定します。 |
| 同p.21の Corollary 1 の適用 | [PairwisePhaseDomination.lean](../../Foundation/Quantum/QKD/PairwisePhaseDomination.lean) の `key_block`、`key_covariance`、`key_dominated` | 実際の誤り測定枝・鍵ゲート・鍵測定の作用素を、同じ攻撃者の周辺作用素と支持個数によって抑えます。エントロピーや解析的な個数評価は未証明です。 |
| 同p.21の公開誤り記録への条件付け | [PairwisePhaseState.lean](../../Foundation/Quantum/QKD/PairwisePhaseState.lean) の `jointState`、`reference`、[PairwisePhasePublic.lean](../../Foundation/Quantum/QKD/PairwisePhasePublic.lean) の `accepted_dominated` | 誤り列全体を公開した正規化参照状態を構成し、既存の受理述語を満たす枝の作用素上界を証明します。枝ごとの正規化は行いません。 |
| 同p.21の Theorem 2 による秘密増幅 | [PairwisePhasePrivacy.lean](../../Foundation/Quantum/QKD/PairwisePhasePrivacy.lean) の `privacy`、`attacked_dominated`、[PairwisePhaseHash.lean](../../Foundation/Quantum/QKD/PairwisePhaseHash.lean) の `collision`、`hashed_distance` | 既存の有限導出に実際の支持から前提を与え、公開する二値行列ハッシュを適用します。任意の有限クラウス攻撃の近似状態へ適用します。検査鍵値の公開、検査位置の削除、実際の全最終出力との接続は後続です。 |
| 独自の非自明な攻撃の検証例 | [PairwisePhaseExamples.lean](../../Foundation/Quantum/QKD/PairwisePhaseExamples.lean) の `support_count`、`dominated`、`guessing`、`interpreted` | 2信号の計算基底記録攻撃の同じ近似状態で、支持個数1、作用素係数 `1/4`、公開ハッシュ後の距離 `1/4` を検証します。実際の残りの最終鍵の安全性とは扱いません。 |


## アリスの実際の鍵と検査位置の公開・削除

| 原典の参照 | Lean の宣言と所在 | 対応の範囲・追加数学 |
| --- | --- | --- |
| Bouman–Fehr §6 本文p.21の公開基底・誤り列の下での `W` と `X` の可逆な対応 | [PairwiseAliceCoordinates.lean](../../Foundation/Quantum/QKD/PairwiseAliceCoordinates.lean) の `alice_involution`、`alice_physical`、[PairwiseAlicePhysical.lean](../../Foundation/Quantum/QKD/PairwiseAlicePhysical.lean) の `original_alice` | 既存の元の測定結果の復元関数と同じアリス座標であることを証明します。 |
| 同p.21のアリスの鍵への上界の移行 | [SubnormalizedEquiv.lean](../../Foundation/Quantum/QKD/SubnormalizedEquiv.lean) の `relabel_equiv_block`、[PairwiseAliceState.lean](../../Foundation/Quantum/QKD/PairwiseAliceState.lean) の `aliceState`、[PairwiseAlicePrivacy.lean](../../Foundation/Quantum/QKD/PairwiseAlicePrivacy.lean) の `acceptedAlice_dominated`、`alicePrivacy` | 同じ近似状態の物理的な古典ラベル変更と、公開誤り列を保持した同じ係数での上界・既存導出への解釈です。 |
| 同p.21の検査鍵値の公開と検査位置の削除による `k` ビットの損失 | [SplitLeak.lean](../../Foundation/Quantum/QKD/SplitLeak.lean) の `split_dominated`、[PairwiseTestKey.lean](../../Foundation/Quantum/QKD/PairwiseTestKey.lean) の `test_bits`、`remaining_bits`、`tested_dominated` | 同じ実際の位置選択で未検査鍵と検査値を分割します。公開係数は `2^(T.card)` です。作用素順序による再構成は追加数学です。 |
| 同p.21の訂正情報の `m` ビットの損失と秘密増幅 | [PairwiseTestPrivacy.lean](../../Foundation/Quantum/QKD/PairwiseTestPrivacy.lean) の `syndrome_dominated`、`testedPrivacy` | 指定された未検査鍵の `m` ビットのメッセージの公開係数と、未検査鍵に対する既存導出への解釈です。符号・復号器・正しさ・認証は未構成です。 |
| 独自の実際の攻撃の検証例 | [PairwiseAliceExamples.lean](../../Foundation/Quantum/QKD/PairwiseAliceExamples.lean) の `interpreted`、[PairwiseTestExamples.lean](../../Foundation/Quantum/QKD/PairwiseTestExamples.lean) の `dominated`、`guessing`、`interpreted` | 同じ2信号の攻撃の近似状態で、アリス座標への移行、1検査値の公開、残りの1ビットの公開ハッシュまで確認します。実状態との全最終出力の安全性は後続です。 |


## 同じ共同状態から既存の生鍵記録と位置付きハッシュへ

| 原典の参照 | Lean の宣言と所在 | 対応の範囲・追加数学 |
| --- | --- | --- |
| Bouman–Fehr §6 本文pp.20–21の詳細測定と反対の基底での鍵測定 | [PairwisePhaseMeasured.lean](../../Foundation/Quantum/QKD/PairwisePhaseMeasured.lean) の `measured_joint`、[PairwisePhaseLabels.lean](../../Foundation/Quantum/QKD/PairwisePhaseLabels.lean) の `labelled_joint` | 支持由来の証明に使う同じ共同状態が、全量子補助系を保持した実際の完全測定・信号除去の出力と等しいことです。 |
| 同pp.20–21の元の生鍵実験との対応 | [PairwiseRawCertificate.lean](../../Foundation/Quantum/QKD/PairwiseRawCertificate.lean) の `decoded_acceptance`、`rawState_physical` | 既存の同じ生鍵復元処理を使い、誤り測定・鍵測定・信号除去・受理／中止・両者の生鍵と公開記録の作用素等式を証明します。全選別集合の混合と追加環境の回復は後続です。 |
| 同p.21の検査位置を除いたアリスの鍵 | [PairwiseOptionalKey.lean](../../Foundation/Quantum/QKD/PairwiseOptionalKey.lean) の `optionalKey_injective`、`decoded_alice_key` | 受理時の既存の位置付き生鍵と、未検査鍵の単射な符号化の一致です。検査位置の欠如と値零を区別します。 |
| 同p.21の秘密増幅への適用と独自の既存ハッシュへの接続 | [PairwiseOptionalKey.lean](../../Foundation/Quantum/QKD/PairwiseOptionalKey.lean) の `remaining_collision`、[PairwiseRawHashPrivacy.lean](../../Foundation/Quantum/QKD/PairwiseRawHashPrivacy.lean) の `rawHashPrivacy` | 既存の実際の位置付き生鍵ハッシュを、支持・検査公開の上界を満たす同じ近似状態に適用します。公開種・検査値・誤り列・量子補助系を保持します。 |
| 独自の非自明な攻撃の検証例 | [PairwiseRawHashExamples.lean](../../Foundation/Quantum/QKD/PairwiseRawHashExamples.lean) の `interpreted` | 同じ2信号攻撃の近似状態と既存の位置付きハッシュで、観測差 `sqrt(1/2)/2` を検証します。実状態との標本誤差を含む最終鍵の安全性とは扱いません。 |


## 公開混合と環境回復を含む全最終出力への標本誤差

| 原典の参照 | Lean の宣言と所在 | 対応の範囲・追加数学 |
| --- | --- | --- |
| Bouman–Fehr §6 本文pp.20–21の詳細測定と相補的な鍵測定の順序 | [PairwiseRecordOrder.lean](../../Foundation/Quantum/QKD/PairwiseRecordOrder.lean) の `record_key`、`rawState_retained` | 全誤り記録と量子成分を保持し、同じ支持由来の状態を既存の記録保持の処理順序へ同定します。 |
| 同p.20の純粋な共同状態への移行への追加数学 | [NestedDiscardClassical.lean](../../Foundation/Quantum/NestedDiscardClassical.lean) の `discard_signal`、`classical_map`、[PairwiseRawRecovery.lean](../../Foundation/Quantum/QKD/PairwiseRawRecovery.lean) の `raw_record_recovery` | 追加の純粋化環境だけの除去が、鍵ゲート・全信号の測定と除去・古典復元に交換できることです。 |
| 同§6への実際の全位置付き生鍵実装の接続 | [PairwiseRawRestoration.lean](../../Foundation/Quantum/QKD/PairwiseRawRestoration.lean) の `recoveredRaw_eq`、`raw_ideal_eq` | 元の攻撃者の系と全位置を復元し、公開選択・検査集合を保持した同じ全生鍵近似状態との作用素等式を証明します。 |
| 同p.21の公開乱数で平均した量子標本誤差 | [PairwiseRandomizedCertificate.lean](../../Foundation/Quantum/QKD/PairwiseRandomizedCertificate.lean) の `certificate_eq`、`certificate_approximation` | 全選別集合・残りの基底・検査位置不足の中止枝を含む、既存の全乱数化近似状態と同じ構成であることです。 |
| 同p.21の標本誤差の後処理への移送 | [PairwiseFinalCertificate.lean](../../Foundation/Quantum/QKD/PairwiseFinalCertificate.lean) の `final_certificate_approximation` | 独立な公開ハッシュ種、両者の最終鍵、全公開記録、受理・中止、攻撃者を持つ既存の実際の最終状態への同じ標本誤差です。秘密鍵の理想資源との距離は未証明です。 |
| 独自の非自明な攻撃の全最終出力の検証例 | [PairwiseCertificateExamples.lean](../../Foundation/Quantum/QKD/PairwiseCertificateExamples.lean) の `attacked_final` | 2信号の攻撃と既存の位置付き二値行列ハッシュで、全乱数化した最終出力の標本近似誤差 `(1/4)*sqrt(1/2)` を検証します。安全な最終鍵の生成は主張しません。 |


## 受理生鍵の公開記録付き一様鍵比較

| 原典の参照 | Lean の宣言と所在 | 対応の範囲・追加数学 |
| --- | --- | --- |
| Bouman–Fehr §6 本文p.21の公開情報を条件とした秘密増幅への追加数学 | [PublicRegisterExpose.lean](../../Foundation/Quantum/QKD/PublicRegisterExpose.lean) の `joint_expose`、`uniformize_expose`、`secrecy`、[PublicKeyProcess.lean](../../Foundation/Quantum/QKD/PublicKeyProcess.lean) の `publicProcess_secrecy` | 古典対角な公開レジスタの明示化と公開記録の変換で、一様化した同じ周辺状態との比較を移します。 |
| 同p.21のアリスの鍵・公開検査値 | [PairwisePublicTranscript.lean](../../Foundation/Quantum/QKD/PairwisePublicTranscript.lean) の `decoded_transcript`、[PairwisePublicSecrecy.lean](../../Foundation/Quantum/QKD/PairwisePublicSecrecy.lean) の `public_raw_secrecy` | 既存の元の生鍵復元処理の公開記録への同定と、その形式での秘密増幅の評価です。 |
| 同p.21の秘密増幅への実際のハッシュ実装の接続 | [PairwiseAcceptedHash.lean](../../Foundation/Quantum/QKD/PairwiseAcceptedHash.lean) の `acceptedRawHash_eq`、`accepted_raw_secrecy` | 支持由来の同じ近似状態の実際の受理生鍵ハッシュと、同じ公開・量子周辺状態を持つ一様鍵との比較です。固定した選別後の信号・検査集合が対象です。全位置への復元と全乱数化の安全性は後続です。 |
| 独自の非自明な攻撃の検証例 | [PairwisePublicExamples.lean](../../Foundation/Quantum/QKD/PairwisePublicExamples.lean) の `accepted_interpreted` | 2信号攻撃の近似状態の受理枝と、実際の公開記録・公開種付き1ビット一様鍵との観測差 `sqrt(1/2)/2` を確認します。全プロトコルの安全な鍵生成は主張しません。 |


## 一様鍵の比較を保つ追加環境の除去

| 原典の参照 | Lean の宣言と所在 | 対応の範囲・追加数学 |
| --- | --- | --- |
| Bouman–Fehr §6 本文pp.20–21の純粋化と秘密増幅への追加数学 | [SubnormalizedProcessing.lean](../../Foundation/Quantum/QKD/SubnormalizedProcessing.lean) の `post_physical`、[CommonKeyProcessing.lean](../../Foundation/Quantum/QKD/CommonKeyProcessing.lean) の `uniformize_post`、`quantumProcess_secrecy` | 部分正規化した実際の共同状態への量子処理と、同じ周辺状態を持つ一様鍵の比較の保存です。 |
| 同p.20の純粋な共同状態から元の攻撃者の系への回復 | [PairwiseAuxiliaryRecovery.lean](../../Foundation/Quantum/QKD/PairwiseAuxiliaryRecovery.lean) の `auxiliaryDiscard_retained`、`recoveredRawCQ_physical` | 追加クラウスラベルだけの部分トレースと、既存の生鍵回復処理との作用素等式です。選別されなかった信号と元の攻撃者の系を残します。 |
| 同p.21の同じアリスの鍵への秘密増幅 | [PairwiseRecoveredSecrecy.lean](../../Foundation/Quantum/QKD/PairwiseRecoveredSecrecy.lean) の `recoveredAcceptedHash_eq`、`recovered_accepted_secrecy` | 回復済みの生鍵状態の実際の受理ハッシュと、同じ公開・量子周辺状態を保つ一様鍵との比較です。全位置の復元と全乱数化は後続です。 |
| 独自の非自明な攻撃の検証例 | [PairwiseRecoveredExamples.lean](../../Foundation/Quantum/QKD/PairwiseRecoveredExamples.lean) の `accepted_recovered` | 同じ2信号攻撃で、追加環境を除いた受理ハッシュ状態の観測差 `sqrt(1/2)/2` を確認します。 |


## 全位置ハッシュと復元した公開記録

| 原典の参照 | Lean の宣言と所在 | 対応の範囲・追加数学 |
| --- | --- | --- |
| Bouman–Fehr §6 本文p.21の未検査鍵への秘密増幅と実際のハッシュ実装への追加数学 | [PairwiseExpandedHash.lean](../../Foundation/Quantum/QKD/PairwiseExpandedHash.lean) の `expand_injective`、`expanded_collision`、`expandedHashPrivacy` | 任意の選別集合で元の全位置付き鍵を復元し、元の全信号数の実際のハッシュ種の一様分布へ適用します。 |
| 同p.21の公開基底・検査位置・検査値への追加数学 | [PairwiseExpandedPublished.lean](../../Foundation/Quantum/QKD/PairwiseExpandedPublished.lean) の `restore_transcript`、`expanded_public_raw_secrecy` | 既存の全位置復元出力と同じ公開記録と公開種を持つ一様鍵比較です。 |
| 同p.21の同じアリスの鍵への秘密増幅 | [PairwiseExpandedAccepted.lean](../../Foundation/Quantum/QKD/PairwiseExpandedAccepted.lean) の `expandedAcceptedHash_eq`、`expanded_accepted_raw_secrecy` | 同じ生鍵復元状態の受理枝に対する実際の全位置復元・ハッシュ・公開記録との同定です。 |
| 同pp.20–21の純粋化と元の攻撃者の系への回復 | [PairwiseExpandedRecovered.lean](../../Foundation/Quantum/QKD/PairwiseExpandedRecovered.lean) の `recoveredExpandedHash_eq`、`recovered_expanded_secrecy` | 追加環境だけの除去後も同じ一様鍵比較を保ちます。選別されなかった信号は残しています。 |
| 独自の非自明な攻撃の検証例 | [PairwiseExpandedExamples.lean](../../Foundation/Quantum/QKD/PairwiseExpandedExamples.lean) の `accepted_expanded` | 同じ2信号攻撃で、元の全位置の種と公開記録を持つ受理ハッシュの観測差 `sqrt(1/2)/2` を検証します。 |


## 復元済み生鍵との同定と基底・検査集合の平均

| 原典の参照 | Lean の宣言と所在 | 対応の範囲・追加数学 |
| --- | --- | --- |
| Bouman–Fehr §6 本文pp.20–21の共同状態から実際の鍵への対応への追加数学 | [SubnormalizedDiscard.lean](../../Foundation/Quantum/QKD/SubnormalizedDiscard.lean) の `discardFirst_retained`、[PairwiseFinishedRaw.lean](../../Foundation/Quantum/QKD/PairwiseFinishedRaw.lean) の `finishedRawCQ_physical` | 選別されなかった信号だけを除き、元の攻撃者を残す処理と、既存の全位置復元生鍵状態との作用素等式です。 |
| 同p.21の同じアリスの鍵への秘密増幅 | [PairwiseFinishedSecrecy.lean](../../Foundation/Quantum/QKD/PairwiseFinishedSecrecy.lean) の `finishedAcceptedHash_eq`、`finished_accepted_secrecy` | 同じ復元済み生鍵の受理枝を実際の全位置ハッシュで処理し、同じ公開・量子周辺状態を持つ一様鍵と比較します。 |
| 同p.21の公開乱数で平均した誤差への追加数学 | [SubnormalizedMixture.lean](../../Foundation/Quantum/QKD/SubnormalizedMixture.lean) の `joint_mixture`、`mixture_approx`、[CommonKeyMixture.lean](../../Foundation/Quantum/QKD/CommonKeyMixture.lean) の `uniformize_mixture`、`mixture_secrecy` | 枝の元の受理確率を保持した混合と、平均後の同じ周辺状態を持つ一様鍵比較です。 |
| 同p.21の基底・検査集合の公開乱数への適用 | [PairwiseConditionalSecrecy.lean](../../Foundation/Quantum/QKD/PairwiseConditionalSecrecy.lean) の `conditionalAcceptedHash`、`conditionalPrivacyError`、`conditional_accepted_secrecy` | 固定した選別集合と残りの基底について、実際の基底選択・検査集合の分布で秘密性誤差を平均します。全選別集合と中止枝の接続は後続です。 |
| 独自の非自明な攻撃の検証例 | [PairwiseFinishedExamples.lean](../../Foundation/Quantum/QKD/PairwiseFinishedExamples.lean) の `accepted_finished` | 同じ2信号攻撃で、復元・部分トレース後の受理ハッシュの観測差 `sqrt(1/2)/2` を確認します。 |


## 条件付き近似状態から直接得る受理ハッシュ

| 原典の参照 | Lean の宣言と所在 | 対応の範囲・追加数学 |
| --- | --- | --- |
| Bouman–Fehr §6 本文p.21の同じ古典・量子状態への追加数学 | [ReadClassicalState.lean](../../Foundation/Quantum/QKD/ReadClassicalState.lean) の `readDensity_CQ`、`readDensity_mixture` | 既存の共同作用素と条件付き量子成分との対応、実際の混合との交換です。 |
| 同p.21の公開乱数の平均と秘密増幅への追加数学 | [SubnormalizedMixtureLaws.lean](../../Foundation/Quantum/QKD/SubnormalizedMixtureLaws.lean) の `mixture_restrict`、`mixture_seed`、`mixture_relabel`、[AcceptedHashProcess.lean](../../Foundation/Quantum/QKD/AcceptedHashProcess.lean) の `fromDensity_mixture` | 受理確率を保持した枝の抽出と、公開種付きの実際のハッシュ処理が混合と交換することです。 |
| 同p.21の同じアリスの鍵への秘密増幅 | [PairwiseConditionalHashProcess.lean](../../Foundation/Quantum/QKD/PairwiseConditionalHashProcess.lean) の `conditional_hash_process`、`conditional_certificate_secrecy` | 秘密性を証明した混合状態を、既存の条件付き近似状態から直接得る同じ受理ハッシュへ同定します。検査位置が十分な枝が対象です。 |
| 独自の非自明な攻撃の検証例 | [PairwiseConditionalProcessExamples.lean](../../Foundation/Quantum/QKD/PairwiseConditionalProcessExamples.lean) の `attacked_conditional` | 同じ2信号攻撃の条件付き近似状態へ、実際の公開乱数について平均した有限式の秘密性評価を適用します。 |


## 不足時の中止枝を保持した全受理鍵の秘密性

| 原典の参照 | Lean の宣言と所在 | 対応の範囲・追加数学 |
| --- | --- | --- |
| Bouman–Fehr §6 本文pp.20–21への実際の BB84 の条件の追加数学 | [BB84AbortBranches.lean](../../Foundation/Quantum/QKD/BB84AbortBranches.lean) の `RawProtocol.too_short`、`reference_abort`、[PairwiseInsufficientSecrecy.lean](../../Foundation/Quantum/QKD/PairwiseInsufficientSecrecy.lean) の `delayed_abort`、`conditional_insufficient_zero` | 既存の最低鍵長条件と実際の遅延測定実験から、検査位置不足時の受理部分が零であることを証明します。全中止状態は保持します。 |
| 同p.21の公開情報を条件とした秘密増幅と平均した誤差 | [PairwiseGlobalSecrecy.lean](../../Foundation/Quantum/QKD/PairwiseGlobalSecrecy.lean) の `conditional_all_secrecy`、`globalAcceptedHash`、`privacyError`、`global_accepted_secrecy` | 全選別集合と残りの基底を実際の分布で平均した同じ全近似状態の受理鍵と、一様鍵との比較です。実状態との標本誤差は後続です。 |
| 独自の非自明な攻撃と不足時の検証例 | [PairwiseGlobalExamples.lean](../../Foundation/Quantum/QKD/PairwiseGlobalExamples.lean) の `attacked_global`、`insufficient_empty_selected` | 同じ2信号攻撃の全乱数化した受理鍵の有限式の評価と、空の選別集合の受理部分が零であることを確認します。 |


## 実際の受理鍵への標本誤差と秘密増幅の合成

| 原典の参照 | Lean の宣言と所在 | 対応の範囲・追加数学 |
| --- | --- | --- |
| Bouman–Fehr §6 本文p.21の標本近似後の処理への追加数学 | [SelectiveDistance.lean](../../Foundation/Quantum/SelectiveDistance.lean) の `OperatorApprox.selective`、[SubnormalizedDistance.lean](../../Foundation/Quantum/QKD/SubnormalizedDistance.lean) の `readDensity_approx`、`restrict_approx`、[SeedDistance.lean](../../Foundation/Quantum/QKD/SeedDistance.lean) の `seed_approx`、[AcceptedHashDistance.lean](../../Foundation/Quantum/QKD/AcceptedHashDistance.lean) の `fromDensity_approx` | 受理確率で割らず、実際の同じ受理ハッシュ処理で距離が増えないことです。 |
| 同p.21の同じ鍵の秘密性への追加数学 | [UniformKeyDistance.lean](../../Foundation/Quantum/QKD/UniformKeyDistance.lean) の `uniformize_approx`、`secrecy_transfer` | 比較先を実状態の同じ公開・量子周辺状態を持つ一様鍵へ戻し、誤差 `2*δ+ε` を導きます。係数はこの実装の合成から証明します。 |
| 同p.21の量子標本近似と秘密増幅の合成 | [PairwiseRealSecrecy.lean](../../Foundation/Quantum/QKD/PairwiseRealSecrecy.lean) の `real_hash_certificate`、`real_accepted_secrecy` | 既存の全乱数化した元の BB84 生鍵実状態の受理鍵について、標本誤差の2倍と支持由来の秘密増幅誤差を加えた評価です。共通鍵の正しさ・認証は後続です。 |
| 独自の非自明な攻撃の実状態の検証例 | [PairwiseRealExamples.lean](../../Foundation/Quantum/QKD/PairwiseRealExamples.lean) の `attacked_real` | 同じ2信号の共同攻撃の元の実状態へ、全公開乱数を平均した有限式の評価を適用します。 |


## 既存の全最終化出力と共通鍵の比較

| 原典の参照 | Lean の宣言と所在 | 対応の範囲・追加数学 |
| --- | --- | --- |
| Bouman–Fehr §6 本文p.21の同じアリスの鍵への追加数学 | [FinalAcceptedHash.lean](../../Foundation/Quantum/QKD/FinalAcceptedHash.lean) の `readDensity_fin_relabel`、`FinalSecurity.alice_accepted_hash` | 証明済みの受理ハッシュが、既存の実際の最終化受理枝のアリス鍵部分と等しいことです。 |
| 同p.21の秘密増幅と全最終出力への追加数学 | [PairwiseFinalSecurity.lean](../../Foundation/Quantum/QKD/PairwiseFinalSecurity.lean) の `final_security_of_correctness`、`final_correctness_probability`、`final_security_with_actual_cost` | 既存の理想資源との距離を、実際の鍵不一致確率と証明済みの秘密性誤差で評価します。小さな正しさの誤差、誤り訂正、認証は未証明です。既存の `AcceptedAbortLogic` の導出を解釈します。 |
| 独自の非自明な攻撃の全出力の検証例 | [PairwiseFinalSecurityExamples.lean](../../Foundation/Quantum/QKD/PairwiseFinalSecurityExamples.lean) の `attacked_full_output` | 同じ2信号の共同攻撃の既存の全最終状態と共通鍵の理想資源に、実際の不一致費用を含む有限式の評価を適用します。 |


## 具体的な反復符号による公開シンドロームと復号（追加数学）

Bouman–Fehr §6 本文p.21は、検査後の鍵に関する公開 `m` ビットのシンドロームの費用を含めて秘密増幅します。具体的な符号や復号アルゴリズムは同箇所で指定していません。

| Lean の宣言 | 対応・限定 |
| --- | --- |
| `RepetitionReconciliation.syndrome`, `decode`, `decode_correct` | 独自に選んだ二元反復符号の公開2ビットと具体的な復号です。3ビット中1個以下の誤りを訂正します。原典の定理ではありません。 |
| `decode_syndrome`, `double_error_failure`, `fiber_card` | パリティの一致と鍵の一致の違いを検証します。2個の誤りによる誤訂正と各パリティの逆像の個数です。 |
| `block_correct`, `quantum_correct` | 任意の組数へ拡張します。各組の誤り条件が必要です。測定後の古典鍵を扱い、長さを3の倍数へ限定します。 |
| `RepetitionReconciliation.process_alice_view` | 実際のボブの復号後のアリス鍵・公開メッセージ・量子系が、同じアリス鍵からメッセージを生成する処理と等しいことです。追加数学です。 |
| `RepetitionReconciliation.process_correctness` | 任意の古典・量子入力で、復号後の不一致の重みを入力の悪い事象の重みで抑えます。確率の小ささは別途必要です。 |
| `PairwisePhaseCoordinates.repetition_dominated` | 同じ支持近似状態の残り鍵から生成した具体的な `2b` ビットのパリティを公開します。本文p.21のシンドローム費用に対応します。 |
| `repetition_privacy`, `repetition_raw_privacy` | 公開費用を含む証明済みの作用素上界を、既存の Presentation と Model による秘密増幅導出へ与えます。後者は既存の生鍵の二元行列ハッシュです。 |
| `RepetitionReconciliationExamples.correct`, `retained_coherence` | 非零の誤りと量子系の非対角成分を持つ具体的入力で復号を検証します。BB84 の全実験からの生成は未接続です。 |

今回の方式は、正の安全な鍵長や実用的な受理確率を与える最終的な符号として選定したものではありません。既存の全最終出力への復号の同定、任意の鍵長の扱い、公開の一致検査と中止、その確率と公開費用の合成を後続範囲として残します。


## 独立な公開ハッシュによる鍵の一致検査（追加数学）

今回の一致検査は、今回の実装のために構成した追加数学です。Heunen の博士論文の推論規則や、Bouman–Fehr §6 本文p.21の具体的なアルゴリズムとして引用しません。公開した検査値の費用を、同箇所の公開情報を含む秘密増幅へ接続する作業が残ります。

| Lean の宣言 | 内容と限定 |
| --- | --- |
| `KeyVerification.accepted`, `aborted`, `branch_mass` | 入力確定後の独立種とアリスの検査値を公開し、ボブが比較します。成功・失敗の枝で全公開記録と量子系を保持します。公開通信の改変は未モデル化です。 |
| `correctness_expansion`, `correctness_le`, `correctness_budget` | 検査後の不一致の重みを、衝突確率と元の不一致の重みで評価します。受理後に正規化した確率ではありません。 |
| `KeyVerificationLogic.presentation`, `model`, `proof`, `sound` | 重みの普遍的上界と検査の規則で、仮定なしの有限導出を構成し、実際の検査状態へ解釈します。 |
| `interpretation_substitute` | 既存の核の仮定置換と解釈の整合性を適用します。 |
| `RepetitionReconciliation.verified_correctness`, `verified_correctness_bad_event` | 前段階の実際のパリティ公開と復号に検査を続けます。訂正半径を超えた入力も対象です。 |
| `BB84KeyVerification.correctness` | 従来の全乱数化した BB84 の受理生鍵の実状態へ、既存の二元行列ハッシュによる検査を適用します。この適用では復号は実行しません。 |
| `KeyVerificationExamples.residual_error`, `passing_mass`, `rejection_mass`, `retained_wrong_key_coherence` | 不一致の重み `1/4` の入力が、検査後に受理の重み `7/8`、拒否の重み `1/8`、受理かつ不一致の重み `1/8` を持つことです。誤って受理される枝の量子系の非対角成分も非零です。 |
| `attacked_raw_verification` | 既存の2信号の共同攻撃に8ビットの検査を追加し、無条件の不一致の重みを `1/256` 以下にします。追加の公開値を含む秘密性は未合成です。 |

独立種、指定した公開値の正しい伝達、部分正規化状態という限定を保持します。認証済みの全最終プロトコルの安全性や、有用な安全な鍵長の結果として扱いません。


## 検査による選択と公開値を含む秘密性（追加数学）

Bouman–Fehr §6 本文p.21の公開情報の費用を含む秘密増幅を、今回の実装の一致検査へ拡張します。検査や以下の作用素の補題を、Heunen の原典の定理として扱いません。

| Lean の宣言 | 内容と限定 |
| --- | --- |
| `Subnormalized.Below`, `restrict_below`, `relabel_below`, `withPublic_below`, `dominated_of_below` | 受理部分の選択と指定した公開処理の下で、量子作用素の上界を保存します。確率だけの大小ではありません。 |
| `KeyVerification.selected_alice_dominated` | 両者の鍵に依存する一致検査でも、アリスの量子成分の上界は同じ係数で成り立ちます。入力の作用素上界は前提です。 |
| `fixed_dominated`, `fixed_privacy` | 実際の検査値を公開した候補数の費用を含め、既存メタ論理の秘密増幅導出を解釈します。検査の種を固定した評価です。 |
| `averaged_privacy` | 検査の種を公開したまま独立な分布で平均します。種の候補数を費用に加えません。入力を種に応じて変更するモデルは対象外です。 |
| `fixedInput_label`, `accepted_mixture` | 同じ検査・アリス鍵・公開値・量子成分の生成と、前段階の実装との等式です。全最終出力のレジスター配置への同定は残ります。 |
| `KeyVerificationPrivacyExamples.dominated`, `checked_dominated`, `interpreted` | 前段階と同じ不一致を含む入力で係数 `1/2` を証明します。1ビットの検査値の費用を含め、2つの独立公開種の秘密増幅誤差を `1/2` 以下にします。全 BB84 の具体例ではありません。 |

全 BB84 について入力の作用素上界を導くこと、元の全最終出力と同じ理想資源への同定、認証と有用な安全性の数値評価が未達です。


## 同じ BB84 支持近似状態での一致検査（追加数学）

Bouman–Fehr §6 本文pp.20–21の同じ測定座標と残り鍵の支持由来の評価を使います。以下の一致検査とデコーダーとの等式は今回の追加数学です。

| Lean の宣言 | 内容と限定 |
| --- | --- |
| `PairwisePhaseCoordinates.rawState_coordinates` | 同じ支持近似状態のアリス鍵・誤り記録を元の生鍵デコーダーで処理すると、既存の `rawState` と等しくなります。 |
| `coordinate_alice_key`, `coordinate_bob_key`, `coordinate_verification` | 元の受理条件の下で、両者の実際の位置付き生鍵と、新しい検査値の比較を同定します。 |
| `verificationInput_alice`, `verifiedAlice_dominated` | 既に証明した同じ支持由来の作用素上界を、実際の両者の鍵の検査後へ適用します。新しい秘密性の前提はありません。 |
| `verified_test_dominated`, `verified_tag_dominated` | 検査位置の削除と公開、指定した検査値の公開の費用を、詳細な誤り記録と量子系を保持して評価します。 |
| `verified_hash_privacy`, `verified_hash_average` | 元の位置付き鍵の二元行列ハッシュで秘密増幅し、検査用と秘密増幅用の種を公開したまま平均します。元の実状態からの標本誤差は未合成です。 |
| `verifiedAlice_coordinates`, `checkedRaw_coordinates` | 元の生鍵状態を実際に受理条件とタグの一致で選択した状態との、量子成分を含む等式です。 |
| `PairwiseVerificationExamples.dominated`, `interpreted` | 同じ2信号の非自明な共同攻撃で係数1と誤差 `1/2` の評価を検証します。固定した基底・検査集合の支持近似状態が対象です。 |

全位置・公開記録の復元、補助系の除去、全選別集合・基底の平均、元の実状態への標本誤差、全最終出力との同定は後続範囲です。復号の全実験への接続、認証、安全な正の鍵長と受理確率という条件も維持します。


## 検査後の元の生鍵出力と公開記録への配置変更（追加数学）

Bouman–Fehr §6 本文pp.20–21の、元のアリスの残り鍵と公開情報を使う秘密増幅へ対応させます。具体的な一致検査と以下の配置変更は追加数学です。

| Lean の宣言 | 内容と限定 |
| --- | --- |
| `PublicRegisterExpose.expose_seed_relabel` | 既存の古典レジスターを、独立な種による指定した処理の後に明示的な公開ラベルへ移します。同じ量子成分を持つ状態の等式です。 |
| `Subnormalized.restrict_intersection` | 元の受理と追加の検査を、重みを正規化せずに共通部分として選びます。 |
| `PairwisePhaseCoordinates.verifiedDisclosure_diagonal`, `verifiedTestExposed_diagonal` | 配置変更するレジスターが既に古典であることです。 |
| `verifiedTestExposed_eq`, `verifiedPublished_eq`, `verified_published_secrecy` | 同じ公開値とハッシュ値の生成との等式と、同じ周辺状態の一様鍵比較への距離保存です。 |
| `coordinate_public_record`, `verifiedRawHash_eq` | 元の生鍵出力と元の公開記録を直接処理する結果へ同定します。検査用の種・検査値・秘密増幅の種を保持します。 |
| `verified_raw_secrecy`, `verified_raw_average_secrecy` | 元の生鍵を直接検査・ハッシュした支持近似状態で秘密性を評価します。検査用の種を公開したまま平均します。 |
| `PairwiseVerificationPublicExamples.direct_raw`, `averaged_raw` | 同じ2信号の非自明な共同攻撃の支持近似状態で、距離の上界 `1/2` を検証します。 |

精製用補助系の除去、全位置への復元、全位置用の2つの公開種、全選別集合と基底の平均、元の実状態への標本誤差は後続範囲です。認証済みの全最終出力の安全性を達成したとは扱いません。


## 精製用補助系を除去した検査・秘密増幅（追加数学）

Bouman–Fehr §6 本文pp.20–21の同じ攻撃を受けた状態と残り鍵を使います。具体的な検査と、以下の部分トレース・処理の交換は追加数学です。

| Lean の宣言 | 内容と限定 |
| --- | --- |
| `VerifiedHash.fixed`, `average`, `fromDensity` | 元の受理条件、独立な公開種の一致検査、別の独立種による秘密増幅を、指定した生鍵の条件付き量子状態または物理的密度作用素に実行します。定義だけでは秘密性を仮定しません。 |
| `post_fixed`, `post_mixture`, `post_average` | 生鍵以外の量子補助系に作用するチャネルと、この全処理との線形な等式です。 |
| `PairwisePhaseCoordinates.recoveredVerifiedHash_eq`, `recoveredVerifiedAverage_eq` | 前段階の出力から精製用のクラウス添字だけを除去すると、回復した生鍵に同じ処理を実行した出力と等しくなります。 |
| `recovered_verified_secrecy`, `recovered_verified_average_secrecy` | 元の攻撃者の量子系と全公開情報を保持し、同じ周辺状態の一様鍵比較へ評価を移します。 |
| `recovered_verified_physical`, `recovered_verified_physical_secrecy` | 物理的な `recoveredRaw` を直接処理した状態へ同定します。対象は支持近似状態であり、元の実状態からの標本誤差は未合成です。 |
| `VerifiedHash.fixed_approx`, `average_approx`, `fromDensity_approx` | 検査と秘密増幅の全処理が入力の距離を増やさないことです。後続の全実験で標本誤差を合成するために使います。 |
| `PairwiseVerifiedRecoveryExamples.recovered_physical` | 同じ2信号の非自明な共同攻撃の物理的な回復後の状態で、秘密性の距離の上界 `1/2` を検証します。 |

元の全位置用の2つの公開種、全位置への復元、不一致基底の信号の除去、全選別集合と基底の平均、元の実状態への標本誤差は後続範囲です。全最終出力の安全性の完了としては扱いません。

## 全位置用の2つの公開種と物理的な復元

Bouman–Fehr §6 本文pp.20–21の同じ残り鍵と公開情報を使う秘密増幅に、追加数学として検査と全位置への復元を接続しました。Heunen の博士論文に今回の検査の定理を帰属させません。

| Lean モジュール・宣言 | 内容と限定 |
| --- | --- |
| `QKD/PairwiseExpandedVerification.coordinate_verification`, `verifiedAlice_dominated` | 全位置用の検査種で展開後の両鍵を検査する等式と、同じ支持由来の係数。追加の秘密性の前提はなし。 |
| `QKD/PairwiseExpandedVerificationPrivacy.verified_hash_privacy`, `verified_hash_average` | 既存の対象論理の導出と健全性による秘密増幅。別の独立な全位置用の種を使い、検査値と両方の種を公開する。 |
| `QKD/PairwiseExpandedVerificationRaw.checkedRaw_coordinates` | 同じ生鍵状態の直接の検査との、条件付き量子行列の等式。 |
| `QKD/PairwiseExpandedVerificationPublic.verifiedPublished_eq`, `verified_published_secrecy` | 古典的な公開レジスターの配置変更と、同じ周辺状態を使う一様鍵との比較。 |
| `QKD/PairwiseExpandedVerificationPublicRaw.verifiedRawHash_eq`, `verified_raw_average_secrecy` | 元の公開記録、検査値、両方の全位置用の種を保持する処理との等式と秘密性。 |
| `QKD/PairwiseVerifiedRestoration.restoredVerifiedHash_eq`, `restored_verified_average_secrecy` | 実際の全位置への鍵と公開記録の復元に対する等式と秘密性。種の分布の同一性は仮定しない。 |
| `QKD/PairwiseVerifiedFinish.finishedVerifiedHash_eq`, `finished_verified_physical`, `finished_verified_physical_secrecy` | 精製用添字と不一致基底の信号の部分トレース、元の攻撃者を保持した全位置の物理的な密度作用素の直接処理。固定した構成の支持近似状態に限定する。 |
| `QKD/PairwiseVerifiedFinishExamples.full_position_physical` | 具体的な3信号の共同攻撃と、選別された2信号・除去する1信号の例。距離上界 `1/2`。有用な鍵長の達成例ではない。 |

全選別集合・基底・検査集合の平均、元の実状態からの標本誤差の合成、検査失敗の中止枝、一般の復号器と認証は今回の追加範囲では未完了です。

## 元の実状態からの、両鍵と中止を含む検査・秘密増幅

Bouman–Fehr §6 本文pp.20–21の公開情報の費用を含む秘密増幅と、実状態への近似誤差の合成に対応します。下記の検査と全出力の構成は追加数学です。Heunen の博士論文に今回の検査・安全性の定理を帰属させません。

| Lean 宣言 | 内容と限定 |
| --- | --- |
| `QKD/VerifiedHashLaws.fromDensity_mixture`, `fromDensity_abort_map` | 同じ両公開種を保持した実際の混合との交換。受理不能な出力の受理部分は零。 |
| `QKD/PairwiseVerifiedAbort.conditional_insufficient_zero` | 信号数が検査に足りない枝の受理部分は零。元の中止枝は残す。 |
| `QKD/PairwiseVerifiedGlobalSecrecy.global_verified_secrecy` | 選別集合・全基底・検査集合を実際の分布で平均した支持近似状態の秘密性。 |
| `QKD/PairwiseVerifiedRealSecrecy.real_verified_secrecy` | 元の実状態自身の周辺状態に対する秘密性。上界は標本誤差の2倍と秘密増幅誤差の和。 |
| `QKD/VerifiedHashBothKeys.bothAverage_alice`, `bothAverage_verifier`, `bothAverage_correctness` | 両者が各自の鍵に実際の秘密増幅をする処理との等式。不一致確率は実際の検査の衝突確率以下。 |
| `QKD/VerifiedHashFullOutput.average_branch_mass`, `fullState`, `full_secure` | 元の中止と検査失敗を保持した正規化済みの全出力。両方の種を中止時にも公開する設計。既存の `AcceptedAbortLogic` の有限の導出とモデルを使う。 |
| `QKD/PairwiseVerifiedSecurity.realVerifiedState`, `real_verified_secure` | 元の実際の全 BB84 状態に対する `IdealKey.Secure`。有限クラウス表示・有限次元補助系に限定。通信の認証は未実装。 |
| `QKD/PairwiseVerifiedSecurityExamples.attacked_correctness`, `attacked_full_output` | 具体的なコヒーレントな2信号の攻撃。8ビットの検査後の最終鍵の不一致確率は `1/256` 以下。全出力の誤差式も適用するが、有用な秘密鍵を得た例ではない。 |

正の有用な鍵長と受理確率、解析的な標本・支持の上界、任意の鍵長の復号と症候群の公開の統合、通信の認証とその誤差の合成は未完了です。全出力の誤差式を証明したことを全安全性の目標の達成とは扱いません。

## 任意長の具体的な復号と、公開されたメッセージを含む支持近似状態の検査・秘密増幅

Bouman–Fehr §6 本文p.21の、訂正に使う公開メッセージのビット数を秘密増幅の前に差し引く箇所に接続します。具体的な符号、末尾の公開、復号・検査の構成は追加数学です。Heunen の博士論文の符号の定理として帰属させません。

| Lean 宣言 | 内容と限定 |
| --- | --- |
| `QKD/ArbitraryReconciliation.decode_correct`, `quantum_correct` | 任意長の残り鍵を扱う具体的な復号。各完全な3ビットの組で高々1ビットの誤りを訂正し、末尾は公開メッセージから復元する。 |
| `QKD/ArbitraryReconciliation.message_card`, `publicBits_add_blocks` | 全パリティと末尾を課金した公開ビット数と集合の大きさ。算術だけを量子エントロピーの下界とは扱わない。 |
| `QKD/ArbitraryReconciliationCQ.process_alice`, `process_correctness`, `verified_correctness`, `verified_bad_event`, `branch_mass` | 同じ古典量子入力の具体的な復号と検査。既存の公開記録と量子補助系を保持。有限の検査の導出を解釈する。 |
| `QKD/PairwiseReconciledCoordinates.correctedBob_remaining`, `reconciledInput_alice`, `verifiedAlice_dominated` | 同じ BB84 測定からのボブの残り鍵に復号を適用する。アリス側の等式から、既存の支持由来の係数を適用する。 |
| `QKD/PairwiseReconciledPrivacy.coefficient_public_bits`, `verified_privacy`, `published_secrecy` | 実際のパリティ・末尾・検査値の費用を含む秘密増幅。全位置用の独立種を使い、既存の秘密増幅の対象論理の導出と健全性へ接続する。 |
| `QKD/PairwiseReconciledPublished.published_average_secrecy`, `finished_published_secrecy` | 両方の種を公開した平均。精製用補助系と不一致基底の信号を除去し、元の攻撃者を保持する。固定した構成の支持近似状態に限定する。 |
| `QKD/ArbitraryReconciliationExamples.decoded`, `correct`, `retained_coherence` | 7ビット中3ビットの誤りを訂正する具体的な古典量子入力。BB84 の独立な雑音の仮定ではない。量子側の非対角成分 `1/4` を保持する。 |
| `QKD/PairwiseReconciledExamples.corrected_verified_public` | コヒーレントな4信号の具体的な攻撃の支持近似状態。残り3ビットの復号・検査・公開メッセージを含む距離上界 `1/2`。有用な鍵長の例ではない。 |

元の全位置の物理的な生鍵へ直接復号する処理との等式、全構成の平均、元の実状態からの標本誤差の再合成、復号後の全出力の受理・中止との同定は後続の接続条件です。復号なしの既存の全出力の安全性の定理を、そのまま復号後の全出力の定理とは扱いません。

## 生鍵の直接の復号・検査・秘密増幅と物理的な回復

Bouman–Fehr §6 本文p.21の、訂正の公開メッセージと検査ビットの費用を差し引く秘密増幅に対応します。具体的な公開記録の格納と復元、生鍵の直接処理との同定、部分トレースとの交換は追加数学です。

| Lean 宣言 | 内容と限定 |
| --- | --- |
| `QKD/ReconciliationMessageRecord.message_roundtrip`, `messageRecord_injective` | 全パリティと末尾を固定した型の公開記録に格納し、全体を復元する。実際の公開量が格納先以下という条件を明示する。 |
| `QKD/RawReconciliation.remaining_optional`, `bobKey_public`, `coordinate_message`, `coordinate_bobKey`, `coordinate_verification` | 元の生鍵から残り鍵を取り出す逆写像。ボブは公開記録から復号器の全入力を復元する。同じ BB84 測定座標との等式。 |
| `QKD/PairwiseReconciledRaw.selectedRaw_coordinates`, `checkedRaw_coordinates` | 元の生鍵の直接の復号と検査が、証明済みの状態の選択と同じであること。ボブの復号結果と全量子成分を保持する。 |
| `QKD/PairwiseReconciledPublicRaw.rawHash_eq`, `raw_average_secrecy` | 元の公開記録、実際の公開メッセージ、検査値、両方の全位置用の種を保持する直接の秘密増幅との等式と秘密性。 |
| `QKD/ReconciledHashProcess.fromDensity`, `fromDensity_approx`, `fromDensity_mixture`, `rawAverage_process` | 任意の物理的な生鍵の直接処理。量子チャネルとの交換、距離の上界、固定した選別・検査集合での混合との交換。秘密性は定義だけからは主張しない。 |
| `QKD/PairwiseReconciledRecovery.recovered_physical`, `recovered_physical_secrecy` | 精製用のクラウス添字を除去した物理的な `recoveredRaw` の直接の復号・検査・秘密増幅。固定した構成の支持近似状態に限定する。 |
| `QKD/PairwiseReconciledRestoration.finished_hash_physical`, `finished_secrecy` | 全位置の公開記録の復元と不一致基底の信号の除去。元の攻撃者、公開メッセージ、検査値、両方の種を保持する。 |
| `QKD/PairwiseReconciledRawExamples.public_record`, `bob_from_public`, `recovered_physical`, `restored_public_output` | 非零の末尾を持つ公開記録からの7ビットの実際の復号。具体的なコヒーレントな4信号の攻撃の物理的な生鍵の直接処理。距離上界 `1/2` は有用な鍵長の例ではない。 |

元の全位置の生鍵の公開情報から選別・検査集合を定める処理との同定、全構成の平均、元の実状態からの標本誤差の再合成、復号後の両者の鍵と受理・中止を含む全出力への接続は後続範囲です。復号なしの全出力の定理を、復号後の全出力の定理として扱いません。
