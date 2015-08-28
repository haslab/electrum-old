module examples/algorithms/opt_spantree

open util/ordering[Lvl] as lo
open util/ordering[State]
open util/graph[Process] as graph

sig State {
	Next : one State
}
lone sig Loop in State {}

fact {
	Next = next + last -> Loop
}

sig Process {
  adj : set Process,
  lvl: Lvl lone -> State,
  parent: Process lone -> State,
}

one sig Root extends Process {}

sig Lvl {}

fact processGraph {
  graph/noSelfLoops[adj] 
  graph/undirected[adj]    
  Process in Root.*adj 
}

pred Init[t:State] {
  no lvl.t
  no parent.t
}

pred Nop[t,t': State] {
  lvl.t = lvl.t'
  parent.t = parent.t'
}

pred MayAct[p : Process, t : State] {
  no lvl.t[p]
  (p = Root || some lvl.t[p.adj])
}

pred Act[p : Process, t,t' : State] {
  no lvl.t[p]
  (p = Root) => {
    lvl.t'[p] = lo/first
    no parent.t'[p]
  } else {
    some adjProc: p.adj {
        some lvl.t[adjProc]
        lvl.t'[p] = lo/next[lvl.t[adjProc]]
        parent.t'[p] = adjProc
  }
}
  all p1 : Process-p | lvl.t[p1] = lvl.t'[p1] and parent.t[p1] = parent.t'[p1]
}

pred Fairness {
  all t : *Next[ordering/first] | ((some p : Process | MayAct[p,t]) =>
		(some t1 : t.*Next, p : Process | Act[p,t1,Next[t1]]))
}

fact Trace {
  Init[first]
  all t : *Next[ordering/first] | (some p : Process | Act[p, t, Next[t]]) || Nop[t,Next[t]]
}

pred IsSpanTree[t : State] {
  Process in Root.*~(parent.t)
  graph/dag[~(parent.t)]
}

pred SuccessfulRun {
  some t : *Next[ordering/first] | IsSpanTree[t]
}

pred Liveness {
	some Loop => some t : *Next[ordering/first] | IsSpanTree[t]
}

pred Safety {
	all t : *Next[ordering/first] | no p : Process | p in p.^(parent.t)
}

assert BadLiveness {
	Liveness
}

assert GoodLiveness {
	Fairness => Liveness
}

assert GoodSafety {
	Safety
}

// Span (1) scenario
check BadLiveness for 3 but 10 State
// Span (2) scenario
check GoodLiveness for 3 but 10 State
// Span (3) scenario
check GoodSafety for 3 but 10 State


