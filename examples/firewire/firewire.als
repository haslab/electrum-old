module firewire


open util/ordering[State] as ord

abstract sig Msg {}
one sig Req, Ack extends Msg {}

sig Node {to, from: set Link} {
  to = {x: Link | x.target = this}
  from = {x: Link | x.source = this}
  }

sig Link {target, source: Node, reverse: Link} {
  reverse.@source = target
  reverse.@target = source
  }

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

sig Op {}
one sig Init, AssignParent, ReadReqOrAck, Elect, WriteReqOrAck,
ResolveContention, Stutter extends Op {}

sig State {
  disj waiting, active, contending, elected: set Node,
  parentLinks: set Link,
  queue: Link -> one Queue,
  op: Op -- the operation that produced the state
  } {
  waiting + active + contending + elected = Node
}

pred SameState [s, s': State] {
  s.waiting = s'.waiting
  s.active = s'.active
  s.contending = s'.contending
  s.elected = s'.elected
  s.parentLinks = s'.parentLinks
  all x: Link | SameQueue [s.queue[x], s'.queue[x]]
  }

pred Trans [s, s': State] {
  s'.op != Init
  s'.op = Stutter => SameState [s, s']
  s'.op = AssignParent => {
    some x: Link {
      x.target in s.waiting & s'.waiting
      NoChangeExceptAt [s, s', x.target]
      ! IsEmptyQueue [s, x]
      s'.parentLinks = s.parentLinks + x
      ReadQueue [s, s', x]
      }}
  s'.op = ReadReqOrAck => {
    s'.parentLinks = s.parentLinks
    some x: Link {
      x.target in s.(active + contending) & (PeekQueue [s, x, Ack] => s'.contending else s'.active)
      NoChangeExceptAt [s, s', x.target]
      ! IsEmptyQueue [s, x]
      ReadQueue [s, s', x]
      }}
  s'.op = Elect => {
    s'.parentLinks = s.parentLinks
    some n: Node {
      n in s.active & s'.elected
      NoChangeExceptAt [s, s', n]
      n.to in s.parentLinks
      QueuesUnchanged [s, s', Link]
      }}
  s'.op = WriteReqOrAck => {
    -- note how this requires access to child ptr
    s'.parentLinks = s.parentLinks
    some n: Node {
      n in s.waiting & s'.active
      lone n.to - s.parentLinks
      NoChangeExceptAt [s, s', n]
      all x: n.from |
        let msg = (x.reverse in s.parentLinks => Ack else Req) |
          WriteQueue [s, s', x, msg]
      QueuesUnchanged [s, s', Link - n.from]
      }}
  s'.op = ResolveContention => {
    some x: Link {
      let contenders = x.(source + target) {
        contenders in s.contending & s'.active
        NoChangeExceptAt [s, s', contenders]
        }
      s'.parentLinks = s.parentLinks + x
      }
    QueuesUnchanged [s, s', Link]
    }
}

pred NoChangeExceptAt [s, s': State, nodes: set Node] {
  let ns = Node - nodes {
  ns & s.waiting = ns & s'.waiting
  ns & s.active = ns & s'.active
  ns & s.contending = ns & s'.contending
  ns & s.elected = ns & s'.elected
  }}

sig Queue {slot: lone Msg, overflow: lone Msg}

pred SameQueue [q, q': Queue] {
    q.slot = q'.slot && q.overflow = q'.overflow
  }

pred ReadQueue [s, s': State, x: Link] {
--  let q = s'.queue[x] | no q.(slot + overflow)
  no s'.queue[x].(slot + overflow)
  all x': Link - x | s'.queue[x'] = s.queue[x']
  }

pred PeekQueue [s: State, x: Link, m: Msg] {
  m = s.queue[x].slot
  }

pred WriteQueue [s, s': State, x: Link, m: Msg] {
        let q = s'.queue[x] |
  no s.queue[x].slot =>
    ( q.slot = m && no q.overflow) else
    some q.overflow
  }

pred QueuesUnchanged [s, s': State, xs: set Link] {
  all x: xs | s'.queue[x] = s.queue[x]
  }

pred IsEmptyQueue [s: State, x: Link] {
  no s.queue[x].(slot + overflow)
--  let q = s.queue[x] | no q.(slot + overflow)
  }

pred Initialization [s: State] {
  s.op = Init
  Node in s.waiting
  no s.parentLinks
  all x: Link | IsEmptyQueue [s, x]
  }

pred Execution  {
  Initialization [ord/first]
  all s: State - ord/last | let s' = ord/next[s] | Trans [s, s']
  }

pred ElectionHappens {
    Execution
        some s: State | some s.elected
    some s: State | no s.elected
}

assert BadSafety {
  Execution  => (all s : State | lone s.elected)
  }

assert BadLiveness {
  Execution  => (some s : State | some s.elected)
  }

// Firewire (1) scenario
check BadLiveness for 0 but 3 Node, 4 Link, exactly 3 Queue, 12 State
// Firewire (2) scenario
check BadSafety for 0 but 3 Node, 4 Link, exactly 3 Queue, 12 State



