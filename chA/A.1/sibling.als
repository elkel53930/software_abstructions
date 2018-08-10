sig Father {}
sig Mother {}

sig Child {
	father : Father,
	mother : Mother,
	brothers : set Child
	}

fact {
	all c1,c2 : Child | (c1.father = c2.father and c1.mother = c2.mother)
		and c2 in c1.brothers =>
			c1 in c2.brothers
	all c : Child | c not in c.brothers
	}

run {some brothers}
