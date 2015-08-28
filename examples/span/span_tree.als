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

fact Fairness {
  all t : *Next[ordering/first] | ((some p : Process | MayAct[p,t]) =>
		(some t1 : t.*Next, p : Process | Act[p,t1,Next[t1]]))
}

fact Trace {
  Init[first]
  all t : *Next[ordering/first] | (some p : Process | Act[p, t, Next[t]]) || Nop[t,Next[t]]
}

/*pred PossTrans[t, t' : State] {
  all p : Process | (some p : Process | Act[p, t, t']) || Nop[t,t']
}*/

pred IsSpanTree[t : State] {
  Process in Root.*~(parent.t)
  graph/dag[~(parent.t)]
}

pred SuccessfulRun {
  some t : *Next[ordering/first] | IsSpanTree[t]
}

/*pred TraceWithoutLoop {
  all s, s' : State | s!=s' => {
    !EquivStates[s, s']
    (s' in so/nexts[s] && (s' != so/next[s])) => !PossTrans[s,s']
  }
  all s: State | !SpanTreeAtState[s]
}*/

/*pred EquivStates[t,t' : State] {
  lvl.t = lvl.t'
  parent.t = parent.t'
}*/

assert Liveness {
	some Loop => some t : *Next[ordering/first] | IsSpanTree[t]
}

assert Safety {
	all t : *Next[ordering/first] | no p : Process | p in p.^(parent.t)
}

/*assert Closure {
  all t : State |
    IsSpanTree[t] => (parent.t = parent.(Next[t]))
}*/

fact {
all p : Process | #adj[p] < 3
}

// note that for the worst case topology and choice of root,
// the scope of Lvl must equal the scope of Process
run SuccessfulRun for 12 State, exactly 4 Process, 3 Lvl expect 1
// run TraceWithoutLoop for 8 but 9 State expect 1
check Liveness for 5 but 5 Process, 5 Lvl, 30 State expect 0
check Safety for 5 but 5 Process, 5 Lvl, 20 State expect 1
//check Closure for 5 but 20 State expect 0
