# Foundation

Lean 4 のライブラリです。Nix の開発用シェルで Lean と Lake（Lean のビルドツール）を利用できます。

## セットアップ

```sh
nix develop path:.
lake build
```

開発用シェルを開かずにビルドする場合は、`nix develop path:. -c lake build` を実行してください。`path:.` は、Git にまだ登録していない設定ファイルも現在の作業ディレクトリから読み込む指定です。
Lean のソースコードは `Foundation/` に追加し、`Foundation.lean` から読み込んでください。
