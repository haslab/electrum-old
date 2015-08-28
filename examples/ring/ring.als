module election --- the final version (as depicted in Fig 6.1)

open util/ordering[Process] as PO

sig Process {
	succ: Process,
	var toSend: set Process,
	}

var sig elected in Process {}

fact ring {
	all p: Process | Process in p.^succ
	}

pred init  {
	all p: Process | p.toSend = p
	}

pred step [p: Process] {
		some id: p.toSend {
			p.toSend' = p.toSend - id
			p.succ.toSend' = p.succ.toSend + (id - p.succ.prevs)
		}
	}

fact defineElected {
	no elected
	next always (elected = {p: Process | p in p.toSend and previous p not in p.toSend})
	}

fact traces {
	init 
	always (all p: Process | step[p] or step [succ.p] or skip [p])
	}

pred skip [p: Process] {
	p.toSend' = p.toSend
	}

pred show { eventually some elected }
run show for 3 Process, 4 Time
// This generates an instance similar to Fig 6.4

//assert AtMostOneElected { lone elected.Time }
assert AtMostOneElected { 
	always (some elected implies (lone elected and next always no elected))
 }
// with Counting-LTL: possible??

check AtMostOneElected for 3 Process, 7 Time
// This should not find any counterexample

pred progress  {
	always (some Process.toSend => some p: Process | not skip [p])
	}

assert AtLeastOneElected { progress => eventually some elected }
check AtLeastOneElected for 3 Process, 7 Time
// This should not find any counterexample

