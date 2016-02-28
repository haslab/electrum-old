open trace[Time]

abstract sig Feature {}

one sig V,B,F,C,T,S extends Feature {}

sig Product in Feature {}

fact {
	V + B in Product
	S in Product or T in Product
}

sig Time {}

abstract sig State {
	state : set Time
}
one sig S1,S2,S3,S4,S5,S6,S7,S8 extends State {}

fact {
	state in State one -> Time
}

abstract sig Event {
	pre,pos : Time,
	feature : Feature
}

sig Pay extends Event {} {
	state.pre = S1
	state.pos = S2
	feature = V
}

sig Free extends Event {} {
	state.pre = S1
	state.pos = S3
	feature = F
}

sig Change extends Event {} {
	state.pre = S2
	state.pos = S3
	feature = V
}

sig Cancel extends Event {} {
	state.pre = S3
	state.pos = S4
	feature = C
}

sig Return extends Event {} {
	state.pre = S4
	state.pos = S1
	feature = C
}

sig Soda extends Event {} {
	state.pre = S3
	state.pos = S5
	feature = S
}

sig Tea extends Event {} {
	state.pre = S3
	state.pos = S6
	feature = T
}

sig ServeSoda extends Event {} {
	state.pre = S5
	state.pos = S7
	feature = S
}

sig ServeTea extends Event {} {
	state.pre = S6
	state.pos = S7
	feature = T
}

sig Skip extends Event {} {
	state.pre = S7
	state.pos = S1
	feature = F
}

sig Open extends Event {} {
	state.pre = S7
	state.pos = S8
	feature = V
}

sig Close extends Event {} {
	state.pre = S8
	state.pos = S1
	feature = V
}

fact Priorities {
	F in Product implies no Pay and no Open
}

fact {
	state.first = S1
	all t : Time, t' : t.next | one e : Event | e.pre = t and e.pos = t' and e.feature in Product
}

run {} for 3 but 2 Time, 1 Event

check {
	all t : Time | S4 not in state.t
} for 3 but 3 Time, 2 Event

check {
	finite or some t : Time | S3 in state.t
} for 3 but 8 Time, 8 Event
