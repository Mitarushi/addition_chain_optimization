# Optimal Addition Chain Solver

このプログラムは2つの変数を用いた場合の最適なAddition Chainを計算します。
このソルバーには最適なAddition Chainを計算する他にも、求められたAddition Chainからコードを生成する機能があります。

## 使い方

```bash
cargo run --release -- -m [TARGET]
```

### オプション

- `-m <size>` (必須): **目標値** (ターゲットの数値)。
- `-t <terminal_table_size>` (オプション, デフォルト値: `5000`): **終盤テーブルのサイズ**。
- `-i <initial_state>` (オプション, デフォルト値: `1,1`): ソルバーの**初期状態** (カンマ区切り形式, 例: `1,1`)。
- `-c <code_template>` (オプション, デフォルト値: `"{r} = {x} * {y};"`): **コード生成テンプレート**
  。操作手順に基づいて出力されるコードをカスタマイズ可能。-
    - 使用可能なプレースホルダ:
        - `{r}`: 結果
        - `{x}`: 第一オペランド
        - `{y}`: 第二オペランド

- `-s` (オプション): **コード出力を抑制**。
- `-p` (オプション): **総コスト出力を抑制**。

## 例

以下は、目標値が`1234`の場合のAddition Chainを計算する例です。

```bash
cargo run --release -- -m 1234
```

出力:

```
Cost: 13
x = x * x;
x = x * x;
x = x * x;
x = x * x;
x = x * x;
x = x * x;
y = x * y;
y = y * y;
x = x * y;
y = y * y;
y = y * y;
y = y * y;
y = x * y;
```
