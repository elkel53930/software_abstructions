module examples/ringElection
open util/ordering[Time]
open util/ordering[Process]

sig Time {}
// Processのアトムはそのままプロセスの識別子になる
sig Process {
	succ: Process,				// 次のプロセス
	toSend: Process -> Time	,	// リング(ネットワーク)上に送信するプロセス識別子のプール
	elected: set Time			// 自らがリーダーとして選ばれたとみなす時刻の集合
	}
fact Ring {all p: Process | Process in p.^succ}	// succをたどればすべてのプロセスに到達可能

pred init (t: Time) {all p: Process | p.toSend.t = p}

pred step (t, t': Time, p: Process) {
	let from = p.toSend, to = p.succ.toSend |
		some id: from.t {
			from.t' = from.t - id
			to.t' = to.t + (id - p.succ.prevs)
			}
	}

run step
