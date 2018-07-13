module tour/addressBook2

abstract sig Target {}
sig Addr extends Target {}
abstract sig Name  extends Target {}


sig Alias, Group extends Name {}

sig Book {addr: Name -> Target}
	{no n:Name | n in n.^addr}
fact {
	lone Alias.(Book.addr)
	}

pred add (b,b': Book, n:Name, t:Target){b'.addr = b.addr + n -> t}

pred showAdd(b,b': Book, n:Name, t:Target){
	add [b,b',n,t]
	#Name.(b'.addr) > 1
	}

assert isSame{
	(all b: Book | all a: Alias | lone a.(b.addr)) <=> lone Alias.(Book.addr)
	}
check isSame for 5

run showAdd for 5 but 2 Book
