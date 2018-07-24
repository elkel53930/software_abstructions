// 非反射的
assert isSame1 {
	all r: univ -> univ |
		no iden & r iff
			all x:univ | x -> x not in r
	}
check isSame1 for 8

// 対称的
assert isSame2 {
	all r: univ -> univ |
		~r in r iff
			(all x,y:univ | x -> y in r => y -> x in r)
	}
check isSame2 for 8

// 関数的
assert isSame3 {
	all r: univ -> univ |
		~r.r in iden iff
			(all x:univ | all disj y,z:univ | x -> y in r => not x -> z in r)
}
check isSame3 for 8

// 単射的
assert isSame4 {
	all r: univ -> univ |
		r.~r in iden iff
			(all x:univ | all disj y,z:univ | y -> x in r => not z -> x in r)
	}
check isSame4 for 8

// 推移的
/*
	a->bとb->cを持つとき、a->cも持つなら推移的
*/
assert isSame5 {
	all r: univ -> univ |
		r.r in r iff
			(all x,y,z: univ | x -> y + y -> z in r => x -> z in r)
	}
check isSame5 for 8

// 全域
assert isSame6 {
	all r: univ -> univ |
		univ in r.univ iff
			(all x: univ | some y: univ | x in univ => x -> y in r)
	}
check isSame6 for 8

// 全射的
assert isSame7 {
	all r: univ -> univ |
		univ in univ.r iff
			(all x: univ | some y: univ | x in univ => y -> x in r)
	}
check isSame7 for 8
