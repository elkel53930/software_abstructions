// 順序関係を表現するためのライブラリを利用
open util/ordering[Day]

//担当日。メインとサブがいる
sig Day{
	main: Person,
	sub: Person
}

//担当者。メインとなる日と、サブとなる日がある。
abstract sig Person{
	mainDays: set Day,
	subDays: set Day
}

//それぞれの職員
one sig PersonS extends Person{}
one sig PersonO extends Person{}
one sig PersonW extends Person{}

//スケジュールのルール
fact{
	// メインを担当する人と、サブを担当する人が等しくなる日はない
	no d: Day | d.main = d.sub
	// すべての人は、メインとなる日にサブに割り当てられることはない
	all d: Day, p: Person | d in p.mainDays implies d not in p.subDays
	// dのメインがpならpのメイン担当日にdは入っている。そうじゃなければ入ってない
	all d: Day, p: Person |
		p in d.main implies d in p.mainDays else d not in p.mainDays
	// dのサブがpならpのサブ担当日にdは入っている。そうじゃなければ入ってない
	all d: Day, p: Person |
		p in d.sub implies d in p.subDays else d not in p.subDays
	// dのメイン担当者がpならpはdのサブ担当者ではない
	all d: Day, p: Person |
		p in d.main implies p not in d.sub
}

// すべての人の担当日数の差は１日以内
fact{
	all p1, p2: Person | #p1.(mainDays+subDays) - #p2.(mainDays+subDays) =< 1
}

// 決まっている担当
fact{
	first.main in PersonO
	first.next.main in PersonW
	first.next.next.main in PersonS
}

// メイン担当は次の日に何も担当しない
fact{
	all d: (Day-last) | d.main not in (d.next.main+d.next.sub)
}

assert mainEqualmainDay{
	~mainDays = main
	~subDays = sub
}

run {} for 3 but 6 Day
check mainEqualmainDay for 3 but 6 Day
