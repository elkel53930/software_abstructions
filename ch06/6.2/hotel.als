module examples/hotel
open util/ordering[Time]
open util/ordering[Key]

// Keyは鍵の組み合わせ。客が差し込む物理的な鍵はカードと呼ぶ
sig Key{}
sig Time {}

// 客室は、ある時刻における現在の鍵を保持する
sig Room {
	keys: set Key,
	currentKey: keys one -> Time
	}

// 複数の部屋の錠前に所属する鍵はない
fact DisjointKeySets{
	/*
		この式は「宣言式」で、keysフィールドが単射であると言っている
		「Room <:」はGuestのフィールドとの混同を避けるためにある
		loneによって、高々１つの客室が各鍵に対応付けられることを示している。
	*/
	Room <: keys in Room lone -> Key
	}

one sig FrontDesk {
	// 最新の鍵の組み合わせを客室に対応させる関係
	// loneは初期化前の客室を表現するため
	lastKey: (Room -> lone Key) -> Time,
	// 客室を宿泊客に対応付ける関係
	occupant: (Room -> Guiest) -> Time
	}

// 宿泊客は、ある時刻における鍵を持つ
sig Guest {
	keys: Key -> Time
	}

// 「ksに属していてkより大きい集合の中で最小(min)のもの」が次の鍵
fun nextKey(k: Key, ks: set Key): lone Key {
	min [k.nexts & ks]
	}
