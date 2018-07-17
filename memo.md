## p172 トレース制約で１つ前のプロセスが１ステップ進む可能性があるとしているのはなぜ？

これ、言ってる意味が分からない。
インスタンスの図を描いてみたほうがよさそう。

## p175 pred progress

この述語はfactでもいいのではないか？

実際、これをfactにして、assertを

```
assert AtLeastOneElected |
  some elected.Time
}
check AtLeastOneElected for 3 but 7 Time
```

としてもcounterexampleは見つからなかった。

## p176 上の話はスコープ単調性を壊すということ？だとしたら問題になる？

スコープ単調性ってなんだっけ？
