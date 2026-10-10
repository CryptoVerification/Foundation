# Foundation

暗号方式の安全性と実行資源を形式的に証明する、証明支援言語 Lean 4 のライブラリです。

## セットアップ

Nix（開発環境を用意するツール）を使用します。

```sh
nix develop path:.
lake build
```

`lake` は Lean のビルドツールです。開発用シェルを開かずにビルドする場合は、`nix develop path:. -c lake build` を実行してください。

## ドキュメント

[安全性論理の説明](docs/crypto-logic.md)に、設計と保証の範囲を記載しています。

[量子モデルと論理の設計](docs/quantum/design.md)には、Heunen の博士論文の調査、最初に形式化する範囲と完了条件を記載しています。[原典と Lean の対応表](docs/quantum/source-map.md)で宣言と出典を確認できます。

[量子基盤の拡張](docs/quantum/extensions.md)には、密度演算子、測定確率、補助系を含む識別誤差の合成、量子ワンタイムパッドの秘密性、第4章・第5章の論理、無限次元の閉部分空間の実装範囲と未達事項を記載しています。

[BB84 と後続範囲の進捗](docs/quantum/full-goal.md)には、任意長の送信と公開記録、標本検査の確率上界、内部スペクトルと無限次元操作の未達条件を記載しています。
