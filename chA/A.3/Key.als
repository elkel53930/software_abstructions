open util/ordering[Time]
open util/ordering[Key]

sig Time, Key {}

sig Room{
	fst: Key -> Time,
	snd: Key -> Time
	}

fact DisjointKeySets {
  all t: Time | Room <: fst.t != snd.t
  }

sig Guest{
	fst: Key lone -> Time,
	snd: Key lone -> Time
	}

one sig FrontDesk {
  lastKey: (Room -> lone Key) -> Time,
  occupant: (Room -> Guest) -> Time,
  usedKeys: set Key -> Time
}

fun newKey (t:Time): lone Key {
  min[max[usedKeys.t].nexts]
}

pred init (t: Time) {
  no Guest.fst.t
  no Guest.snd.t
  no FrontDesk.occupant.t
}

run {}
