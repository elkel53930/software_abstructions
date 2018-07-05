abstract sig Object {}
sig Directory extends Object {contents: set Object}
one sig Root extends Directory {}
sig File extends Object {}
sig Alias extends File {to: Object}

fact{
	// Rootをコンテンツに持つDirectoryはない
	all d: Directory | all r: Root| not r in d.contents
	// Rootを除くすべてのObjectはRootを「根」に持つ
	all r: Root | r.^contents = Object - Root
	// Directoryは、自分の下に自分自身が現れることはない
	all d: Directory | not d in d.^contents
	// 複数のDirectoryに属するObjectはない
	contents in Directory lone -> set Object
	// Aliasのtoは循環していない
	all a: Alias | not a in a.^to
	}

run {} for 5
