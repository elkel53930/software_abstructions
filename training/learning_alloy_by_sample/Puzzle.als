abstract sig Event {}
one sig GraduationCeremony extends Event{}
one sig TravelingAbroad extends Event{}
one sig InitiationCeremony extends Event{}
one sig FlowerViewing extends Event{}
one sig Hiking extends Event{}

abstract sig Item{}
one sig Shoes extends Item{}
one sig Handkerchief extends Item{}
one sig Shirt extends Item{}
one sig Slacks extends Item{}
one sig Camera extends Item{}

abstract sig Person{
	event: Event,
	item: Item
}
one sig Tanaka extends Person{}
one sig Takeuchi extends Person{}
one sig Ishida extends Person{}
one sig Kasai extends Person{}
one sig Aoyama extends Person{}

// 参加した人はみんな、ひとつの行事に参加し、一つのものを買っている
// 参加した行事と買ったものはそれぞれ異なる
fact{
	all p1, p2: Person | p1 = p2 implies p1.event = p2.event else p1.event != p2.event
	all p1, p2: Person | p1 = p2 implies p1.item = p2.item else p1.item != p2.item
}

// 田中さん「私はシャツを買いました」
fact{
	Tanaka.item in Shirt
}

// 竹内さん「私は花見に行く前にズボンを買いました」
fact{
	Takeuchi.item in Slacks
	Takeuchi.event in FlowerViewing
}

// 石田さん「私ではありませんが、入社式に行った人は靴を買ったそうです」
fact{
	all p:Person | p.event in InitiationCeremony implies p.item in Shoes
	Ishida.item not in Shoes
	Ishida.event not in InitiationCeremony
}

// 葛西さん「私も田中さんも卒業式には行っていません」
fact{
	Kasai.event not in GraduationCeremony
	Tanaka.event not in GraduationCeremony
}

// 青山さん「私が行ったのは卒業式でもハイキングでもありません」
// 青山さん「買ったのは靴でもカメラでもありません」
fact{
	Aoyama.event not in GraduationCeremony + Hiking
	Aoyama.item not in Shoes + Camera
}

pred show{}
run show
