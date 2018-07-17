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

// succをたどればすべてのプロセスに到達可能
fact Ring {all p: Process | Process in p.^succ}

// 各プロセスは自分自身の識別子だけを送ろうとしている。
pred init (t: Time) {all p: Process | p.toSend.t = p}
run init

pred step (t, t': Time, p: Process) {
	let from = p.toSend, to = p.succ.toSend |
		some id: from.t {
			// fromからはidが消える
			from.t' = from.t - id
			// toにはidが追加されるが、自分より小さな識別子(Processはordering)の場合は削除される
			to.t' = to.t + (id - p.succ.prevs)
			}
	}

pred skip (t, t': Time, p: Process) {p.toSend.t = p.toSend.t'}

fact Traces {
	// 最初の時刻でinitが成立する
	// init[first]と同等
	first.init
	// 最後の時刻以外で以下の制約が成立する
	all t: Time - last | let t' = t.next |
		all p: Process |
			/*
				プロセスpが1ステップ進む step [t, t', p] か
				一つ前のプロセスsucc.pが1ステップ進む step [t, t', succ.p] か
				何もしない skip [t ,t', p] かのいずれかである。
				p.succは次のプロセスを表すが、succ.pは前のプロセスを表している。
			*/
			step [t, t', p] or step [t, t', succ.p] or skip [t ,t', p]
	}

fact DefineElected {
	// 最初の時刻では、どのプロセスも選出されていない
	no elected.first
	all t: Time - first |
		/*
			現時刻(t)でtoSendにプールされていて、ひとつ前の時刻(t.prev)でプールされていない
			プロセスが「その時刻で追加されたプロセス p.toSend.t - p.toSend.(t.prev)」
			その時刻で追加されたプロセスに自分自身が含まれていれば、選出となる
		*/
		elected.t = {p: Process | p in p.toSend.t - p.toSend.(t.prev)}
	}

// 高々１つのプロセスが選出される
assert AtMostOneElected {
	lone elected.Time
	}
check AtMostOneElected for 3 Process, 7 Time

// 少なくとも１つのプロセスが選出される
assert AtLeastOneElected {
	progress => some elected.Time
	}
check AtLeastOneElected for 3 but 7 Time

// factにしてもいいのでは？
pred progress {
	// 最後の時刻以外のある時刻では
	all t: Time -last | let t' = t.next |
		//  識別子プールが空でないプロセスがあった場合、
		some Process.toSend.t =>
			// skipでは「ない」プロセスが存在する
			some p: Process | not skip [t, t', p]
	}

pred looplessPath {no disj t, t': Time | toSend.t = toSend.t'}
run looplessPath for 13 Time, 3 Process

pred show {
	some elected
	}
run show for 3 Process, 4 Time
