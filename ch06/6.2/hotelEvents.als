module examples/hotelEvents
open util/ordering[Time]
open util/ordering[Key]

sig Key, Time {}

sig Room {
	keys: set Key,
	currentKey: keys one -> Time
	}
fact DisjointKeySets {
	Room <: keys in Room lone -> Key
	}

one sig FrontDesk {
	lastKey: (Room -> lone Key) -> Time,
	occupant: (Room -> Guest) -> Time
	}

sig Guest {
	keys: Key -> Time
	}

fun nextKey (k: Key, ks: set Key): lone Key {
	min [k.nexts &ks]
	}

pred init (t: Time) {
	no Guest.keys.t
	no FrontDesk.occupant.t
	all r: Room | FrontDesk.lastKey.t [r] = r.currentKey.t
	}

abstract sig Event {
	// イベントが発生する前の時刻と、後の時刻
	pre, post: Time,
	// イベントを起こす宿泊客
	guest: Guest
	}	

abstract sig RoomKeyEvent extends Event {
	room: Room,
	key: Key
	}

sig Entry extends RoomKeyEvent {} {
	// 事前条件：入室直前に宿泊客が鍵を持っている
	key in guest.keys.pre
	let ck = room.currentKey |
		// 事前条件：鍵は、現在の鍵と一致するか、もしくは次の鍵と一致する
		key = ck.pre or key = nextKey [ck.pre, room.keys]
		// 事後条件：鍵が再コードされる(現在の鍵と一致する場合は変化しない)
		currentKey.post = currentKey.pre ++ room -> key
	}

sig Checkin extends RoomKeyEvent {} {
	// 事後条件：宿泊客は鍵を受け取る
	keys.post = keys.pre + guest -> key
	let occ = FrontDesk.occupant {
		// 事前条件：部屋には誰もチェックインしていない
		no occ.pre [room]
		// 事後条件：宿泊客を部屋と紐づける
		occ.post = occ.pre + room -> guest
		}
	let lk = FrontDesk.lastKey {
		// 事後条件：最新の鍵の情報を更新
		lk.post = lk.pre ++ room -> key
		// keyは部屋に紐づけられた最新の鍵の、次の鍵である
		key = nextKey [lk.pre [room], room.keys]
		}
	}

sig Checkout extends Event{} {
	let occ = FrontDesk.occupant {
		// 事前条件：部屋に宿泊客がいる
		some occ.pre.guest
		// 事後条件：宿泊客の情報が削除される
		occ.post = occ.pre - Room -> guest
		}
	}

fact Traces {
	// 最初の時刻でinitが成り立つ
	first.init
	all t: Time - last | let t' = t.next |
		some e:Event {
			// postはpreの次の時刻
			e.pre = t and e.post = t'
			// 最新の鍵が更新されるなら、Entry
			currentKey.t != currentKey.t' => e in Entry
			// 宿泊簿が更新されるなら、CheckinかCheckout
			occupant.t != occupant.t' => e in Checkin + Checkout
			// フロントの最新の鍵と、部屋の鍵のセットが更新されるなら、Checkin
			(lastKey.t != lastKey.t' or keys.t != keys.t')
				=> e in Checkin
		}
	}

assert NoBadEntry {
	all e: Entry | let o = FrontDesk.occupant.(e.pre) [e.room] |
		some o => e.guest in o
	}
check NoBadEntry for 5 but 3 Room, 3 Guest, 9 Time, 8 Event

fact NoIntervening {
	all c: Checkin |
		c.post = last
		or some e: Entry {
			e.pre = c.post
			e.room = c.room
			e.guest = c.guest
		}
	}

run {}

