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

pred init (t: Time) {
	// 鍵を持つ客はいない
	no Guiest.keys.t
	// フロントの宿泊簿は、すべての客室が空いていることを示す
	no FrontDesk.occupant.t
	// フロントの「最新の鍵」と各客室の「現在の鍵」は一致している
	all r:Room | FrontDesk.lastKey.t [r] = r.currentKey.t
	}

pred entry (t, t': Time, g: Guest, r: Room, k: Key) {
	// 事前条件
	// kは客が持っている鍵のうちの一つである
	k in g.keys.t
	// 事後条件
	let ck = r.currentKey |
		// カードの鍵と、現在の鍵が一致して、次の時間における錠前の鍵は変化しない
		(k = ck.t and ck.t' = ck.t) or
		// カードの鍵はと次の鍵が一致して、次の時間における錠前の鍵は変化する
		(k = nextKey [ck.t, r.keys] and ct.t' = k)
	// フレーム条件 : 状態のどの部分が変化しないかを示す
	// 他の客室は変化しない
	noRoomChangeExcept [t, t', r]
	// 宿泊客が持つ鍵の集合は変化しない
	noGuestChangeExcept [t, t', none]
	// フロントの鍵の情報は変化しない
	noFrontDeskChange [t, t']
	}

pred noFrontDeskChange (t, t': Time) {
	// 鍵も宿泊簿も変化しない
	FrontDesk.lastKey.t = FrontDesk.lastKey.t'
	FrontDesk.occupant.t = FrontDesk.occupant.t'
	}

pred noRoomChangeExcept (t, t': Time, rs: set Room) {
	// 指定された部屋たち(rs)を除き、鍵は変化しない
	all r: Room - rs | r.currentKey.t = r.currentKey.t'
	}

pred noGuestChangeExcept (t, t': Time, gs: set Guest) {
	// 指定された客たち(gs)を除き、客の持つ鍵の集合は変化しない
	all g: Guest - gs | g.keys.t = g.keys.t'
	}

pred checkout (t, t': Time, g: Guest) {
	let occ = FrontDesk.occupant {
		// ある時刻tにおいて、客gが宿泊している部屋がある
		some occ.t.g
		// 次の時刻t'において、客gが宿泊している部屋の情報は宿泊簿から削除される
		occ.t' = occ.t - Room -> g
		}
	// フロントの鍵の情報は変化しない
	FrontDesk.lastKey.t = FrontDesk.lastKey.t'
	// すべての客室は変化しない
	noRoomChangeExcept [t, t', none]
	// すべての宿泊客が持つ鍵の集合は変化しない
	noGuestChangeExcept [t, t', none]		
	}

pred checkin (t, t': Time, g: Guest, r: Room, k: Key) {
	// 宿泊客に鍵が渡される
	g.keys.t' = g.keys.t + k
	let occ = FrontDesk.occupant {
		// 事前条件
		// 部屋が空いている
		no occ.t [r]
		// 事後条件
		// 部屋に宿泊客を紐づく
		occ.t' = occ.t + r -> g
		}
	let lk = FrontDesk.lastKey {
		// 新しい鍵は、最新の鍵の、次の鍵
		k = nextKey [lk.t[r], r.keys]
		// フロントの記録が次の鍵に上書きされる
		lk.t' = lk.t ++ r -> k
		}
	// すべての客室は変化しない
	noRoomChangeExcept [t, t', none]
	// チェックインした宿泊客以外の宿泊客は変化しない
	noGuestChangeExcept [t, t', g]
	}

fact Traces {
	// 最初の時刻ではinitが成り立つ
	first.init
	// すべてのtからt'への時間遷移において
	all t: Time - last | let t' = t.next |
		// 入室、チェックイン、チェックアウトのいずれかが発生する
		some g: Guest, r: Room, k: Key |
			entry [t,t',g,r,k]
			or chechin [t,t',g,r,k]
			or checkout [t,t',g]
	}

assert NoBadEntry {
	all t: Time, r: Room, g: Guest, k: Key |
		let o = FrontDesk.occupant.t [r] |
			entry [t, t.next, g, r, k] and some o => g in o
	}




