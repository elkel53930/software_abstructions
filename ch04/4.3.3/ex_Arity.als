sig A {r : B->C}
sig B {}
sig C {}

fact{
	all a:A | a.r in B -> one C
	}

run {} for 3
