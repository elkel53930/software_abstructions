abstract sig A{f:B}
sig A1 extends A {}
sig A2 extends A {}
abstract sig B {}
sig B1 extends B{}
sig B2 extends B{}

pred show{}
//run show for 2
run show for 1 A1, 1 A2, 1 B1, 1 B2
