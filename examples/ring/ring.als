module ring

open util/ordering[Time] as TO
open util/ordering[Id] 

sig Id {}
sig Time {
	next_ : one Time
} 
one sig Loop extends Time {}
fact {
	next_ = next + last->Loop
}

sig Process {
	succ: Process,
	toSend: Id -> Time,
	elected: set Time,
	id : Id
} {
	@id in Process lone -> Id
}

fact ring {
	all p: Process | Process in p.^succ
	}

pred init  {
	all p: Process | p.toSend.first = p.id
	}

pred step [t, t': Time, p: Process] {
		some id_: p.toSend.t {
			p.toSend.t' = p.toSend.t - id_
			p.succ.toSend.t' = p.succ.toSend.t + (id_ - prevs[p.succ.id])
		}
	}

fact defineElected {
	no elected.first
	all t: Time-first | elected.t = {p: Process | p.id in p.toSend.t - p.toSend.(t.TO/prev)}
	}

fact traces {
	init
	all t: Time |
		let t' = t.next_ |
			all p: Process | step[t,t',p] or step [t,t',p.~succ] or skip [t,t',p] 
	}

pred skip [t, t': Time, p: Process] {
	p.toSend.t' = p.toSend.t
	}

assert GoodSafety { 
lone elected.Time
 }

pred Progress  {
	all t: Time |
		let t' = next_ [t] |
			some Process.toSend.t => some p: Process | not skip [t, t', p]
	}

assert BadLiveness { some Process => some elected.Time }

assert GoodLiveness { some Process && Progress => some elected.Time  }

// Ring (1) scenario
check BadLiveness for 3 but 10 Time
// Ring (2) scenario
check GoodLiveness for 3 but 10 Time
// Ring (3) scenario
check GoodSafety for 3 but 10 Time
