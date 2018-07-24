// 非反射的
assert isSame1 {
	all r: univ -> univ |
		no iden & r iff
			all x:univ | x -> x not in r
	}
check isSame1 for 4

// 対称的
assert isSame2 {
	all r: univ -> univ |
		~r in r iff
			(all x,y:univ | x -> y in r => y -> x in r)
	}
check isSame2 for 4

// 関数的
assert isSame3 {
	all r: univ -> univ |
		~r.r in iden iff
			(all x:univ | all disj y,z:univ | x -> y in r => not x -> z in r)
}
check isSame3 for 4

// 単射的
assert isSame4 {
	all r: univ -> univ |
		r.~r in iden iff
			(all x:univ | all disj y,z:univ | y -> x in r => not z -> x in r)
	}
check isSame4 for 4
