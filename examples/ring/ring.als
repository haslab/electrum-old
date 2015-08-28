module ring

open util/ordering[Id] 

sig Id {}

sig Process {
	succ: Process,
	var toSend: set Id,
	id : Id
} {
	@id in Process lone -> Id
}

var sig elected in Process {}

fact ring {
	all p: Process | Process in p.^succ
	}

pred init  {
	all p: Process | p.toSend = p.id
	}

pred step [p: Process] {
		some id_: p.toSend {
			p.toSend' = p.toSend - id_
			p.succ.toSend' = p.succ.toSend + (id_ - prevs[p.succ.id])
		}
	}

fact defineElected {
	no elected
	always { elected' = {p: Process | (after { p.id in p.toSend }) and p.id not in p.toSend} }
}

fact traces {
	init
	always { all p: Process | step[p] or step [p.~succ] or skip [p] }
	}

pred skip [p: Process] {
	p.toSend' = p.toSend
	}

assert GoodSafety { 
	always { all x : elected | always { all y : elected | x = y }}
 }

pred Progress  {
	always {some Process.toSend => after { some p: Process | not skip [p]} }
	}

assert BadLiveness { some Process => eventually { some elected } }

assert GoodLiveness { some Process && Progress => eventually { some elected } }

// Ring (1) scenario
check BadLiveness for 3 but 10 Time
// Ring (2) scenario
check GoodLiveness for 3 but 10 Time
// Ring (3) scenario
check GoodSafety for 3 but 10 Time
