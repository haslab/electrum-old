module firewire

abstract sig Msg {}
one sig Req, Ack extends Msg {}

sig Node {to, from: set Link} {
  to = {x: Link | x.target = this}
  from = {x: Link | x.source = this}
  }

var sig Waiting, Active, Contending, Elected in Node {}

fact {
	always {
		Waiting & Active = none
		Waiting & Contending = none
		Waiting & Elected = none
		Contending & Active = none
		Contending & Elected = none
		Elected & Active = none
		Waiting + Active + Contending + Elected = Node
	}
}

sig Link {
	target, source: Node, 
	reverse: Link,
	var queue : Queue
} {
  reverse.@source = target
  reverse.@target = source
  }

var sig ParentLinks extends Link {}

/**
 * at most one link between a pair of nodes in a given direction
 */
fact {no x,y: Link | x!=y && x.source = y.source && x.target = y.target}

/**
 * topology is tree-like: acyclic when viewed as an undirected graph
 */
fact Topology {
some tree: Node lone -> Node, root: Node {
  Node in root.*tree
  no ^tree & iden & Node->Node
  tree + ~tree = ~source.target
  }
}

abstract sig Op {}
one sig Init, AssignParent, ReadReqOrAck, Elect, WriteReqOrAck,
ResolveContention, Stutter extends Op {}

one var sig Happen in Op {}

pred SameState {
  Waiting = Waiting'
  Active = Active'
  Contending = Contending'
  Elected = Elected'
  ParentLinks = ParentLinks'
  all x: Link | SameQueue [queue[x], queue'[x]]
  }

pred Trans {
  Happen' != Init
//  Happen' != Stutter
  Happen' = Stutter => SameState
  Happen' = AssignParent => {
    some x: Link {
      x.target in Waiting & Waiting'
      NoChangeExceptAt [x.target]
      ! IsEmptyQueue [x]
      ParentLinks' = ParentLinks + x
      ReadQueue [x]
      }}
  Happen' = ReadReqOrAck => {
    ParentLinks' = ParentLinks
    some x: Link {
      x.target in (Active + Contending) & (PeekQueue [x, Ack] => Contending' else Active')
      NoChangeExceptAt [x.target]
      ! IsEmptyQueue [x]
      ReadQueue [x]
      }}
  Happen' = Elect => {
    ParentLinks' = ParentLinks
    some n: Node {
      n in Active & Elected'
      NoChangeExceptAt [n]
      n.to in ParentLinks
      QueuesUnchanged [Link]
      }}
  Happen' = WriteReqOrAck => {
    -- note how this requires access to child ptr
    ParentLinks' = ParentLinks
    some n: Node {
      n in Waiting & Active'
      lone n.to - ParentLinks
      NoChangeExceptAt [n]
      all x: n.from | WriteQueue [x, (x.reverse in ParentLinks => Ack else Req)]
      QueuesUnchanged [Link - n.from]
      }}
  Happen' = ResolveContention => {
    some x: Link {
      x.(source + target) in Contending & Active'
      NoChangeExceptAt [x.(source + target)]
      ParentLinks' = ParentLinks + x
      }
    QueuesUnchanged [Link]
    } 
}

pred NoChangeExceptAt [nodes: set Node] {
  (Node - nodes) & Waiting = (Node - nodes) & Waiting'
  (Node - nodes) & Active = (Node - nodes) & Active'
  (Node - nodes) & Contending = (Node - nodes) & Contending'
  (Node - nodes) & Elected = (Node - nodes) & Elected'
  }

sig Queue {slot: lone Msg, overflow: lone Msg}

pred SameQueue [q, q1: Queue] {
    q.slot = q1.slot && q.overflow = q1.overflow
  }

pred ReadQueue [x: Link] {
--  let q = s'.queue[x] | no q.(slot + overflow)
  no queue'[x].(slot + overflow)
  all x1: Link - x | queue'[x1] = queue[x1]
  }

pred PeekQueue [x: Link, m: Msg] {
  m = queue[x].slot
  }

pred WriteQueue [x: Link, m: Msg] {
  no queue[x].slot =>
    ( (queue'[x]).slot = m && no (queue'[x]).overflow) else
    some (queue'[x]).overflow
  }

pred QueuesUnchanged [xs: set Link] {
  all x: xs | queue'[x] = queue[x]
  }

pred IsEmptyQueue [x: Link] {
  no queue[x].(slot + overflow)
--  let q = s.queue[x] | no q.(slot + overflow)
  }

pred Initialization {
  Happen = Init
  Node in Waiting
  no ParentLinks
  all x: Link | IsEmptyQueue [x] 
  }

pred Execution  {
  Initialization
  always { Trans }
  }

pred ElectionHappens {
    Execution
    eventually { some Elected }
//	no Elected
}

assert AtMostOneElected {
  Execution  => (always { lone Elected })
  }

assert OneEventuallyElected {
  Execution  => (eventually { some Elected })
  }

assert NoOverflow {
  Execution  => (always { all x: Link | no queue[x].overflow })
  }

run Execution for 7 Op, 2 Msg,
  exactly 2 Node, 4 Link, 4 Queue, exactly 6 Time expect 1

run ElectionHappens for 7 Op, 2 Msg,
  exactly 3 Node,  6 Link, 3 Queue, exactly 7 Time expect 1

-- only 5 queues needed: just count
-- no solution: establishes at most 3 queues needed
check NoOverflow for 7 Op, 2 Msg,
  3 Node, 6 Link, 5 Queue, 9 Time expect 0

check AtMostOneElected for 7 Op, 2 Msg,
  3 Node, 6 Link, 3 Queue, exactly 9 Time expect 0

check OneEventuallyElected for 7 Op, 2 Msg,
  3 Node, 6 Link, 3 Queue,  9 Time expect 1

// DEFINED VARIABLES
// Defined variables are uncalled, no-argument functions.
// They are helpful for getting good visualization.
fun queued: Link -> Msg {
  {L: Link, m: Msg | m in L.(queue).slot}
}
