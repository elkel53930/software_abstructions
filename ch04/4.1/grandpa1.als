module language/grandpa1
abstract sig Person {
	father: lone Man,
	mother: lone Woman
	}
sig Man extends Person {
	wife: lone Woman
	}
sig Woman extends Person {
	husband: lone Man
	}

fact Biology{
	no p: Person | p in p.^(mother + father)
	}
fact Terminology {
	wife = ~ husband
	}
/*
fact SocialConvention {
	no (wife + husband) & ^(mother + father)
	}
*/
pred SocialConvention {
	no (wife + husband) & ^(mother + father)
	}

pred SocialConvention' {
	let parent = mother + father {
		no m: Man | some m.wife and m.wife in (m.^parent.mother + m.mother)
		no w: Woman | some w.husband and w.husband in (w.^parent.father + w.father)
		}
	}

assert Same {
	SocialConvention <=> SocialConvention'
	}
check Same for 5

assert NoSelfFather {
	no m: Man | m = m.father
	}
//check NoSelfFather

fun grandpas (p: Person) : set Person {
	let parent = mother + father + father.wife + mother.husband |
		p.parent.parent & Man
	}
pred ownGrandpa (p: Person) {
	p in grandpas [p]
	}
assert NoSelfGrandpa {
	no p: Person | p in grandpas [p]
	}

run ownGrandpa for 4 Person
//check NoSelfGrandpa for 4 Person
