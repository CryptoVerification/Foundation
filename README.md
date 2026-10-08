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
