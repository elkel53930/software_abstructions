module exercises/properties

run {
	some r: univ -> univ {
		some r			// 非空的
//		r.r in r		// 推移的
		no iden & r	// 非反射的
		~r in r			// 対称的
		~r.r in iden	// 関数的
		r.~r in iden	// 単射的
		univ in r.univ // 全域
		univ in univ.r	// 全射的
		}
	} for 8

/*
	非空的を削除すると、空集合が充足する
	推移的を削除すると、全単射な関係が充足する
		u1 <-> u2
		u3 <-> u4
	非反射的を削除すると、自分自身への関係を持った関係が充足する
		u1 -> u1
		u2 -> u2
*/
