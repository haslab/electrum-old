------------------------------ MODULE SpanTree ------------------------------
EXTENDS Naturals 

CONSTANT Process, Lvl, NONE
VARIABLES process, adj, lvl, parent, root

ASSUME Lvl \in SUBSET Nat

TypeInv == /\ process \in SUBSET Process 
           /\ adj \in [process -> SUBSET process]
           /\ lvl \in [process -> Lvl \cup {NONE}]
           /\ parent \in [process -> process \cup {NONE}]
           /\ root \in process

succstar[visited \in SUBSET Process, p \in Process] == 
    IF p \in visited THEN {} ELSE adj[p] \cup UNION { succstar[visited \cup {p}, p1] : p1 \in adj[p] } \cup {p}

adjs[p \in Process] == succstar[{},p]       
           
Init == /\ process \in SUBSET Process
        /\ lvl = [p \in process |-> NONE]
        /\ parent = [p \in process |-> NONE]
        /\ root \in process
        /\ adj \in [process -> SUBSET process]
        /\ \A p \in process : p \notin adj[p]
        /\ \A p1,p2 \in process : p1 \in adj[p2] => p2 \in adj[p1]
        /\ \A p \in process : p \in adjs[root] 
        

Act(p) == /\ lvl[p] = NONE
          /\ (p = root \/ \E p1 \in adj[p] : lvl[p1] # NONE)
          /\ IF p = root THEN lvl' = [lvl EXCEPT ![p] = 0] /\ parent' = [parent EXCEPT ![p] = NONE]
             ELSE \E p1 \in adj[p] : lvl[p1] # NONE /\ lvl' = [lvl EXCEPT ![p] = lvl[p1] + 1] /\ parent' = [parent EXCEPT ![p] = p1]
          /\ UNCHANGED<<process,adj,root>>
             
Next == \E p \in process : Act(p)

Fairness == WF_<<process, adj, lvl, parent, root>>(\E p \in process : Act(p))

Spec == Init /\ [][Next]_<<process, adj, lvl, parent, root>> /\ Fairness

childstar[visited \in SUBSET Process, p \in Process] ==
    LET c == IF p \in visited THEN {} ELSE {p1 \in process : parent[p1] = p} IN
    c \cup UNION { childstar[visited \cup {p}, p1] : p1 \in c }

children[p \in Process] == childstar[{},p]

parentstar[visited \in SUBSET Process, p \in Process] == 
    IF parent[p] = NONE THEN {} ELSE
    IF p \in visited THEN {} ELSE {parent[p]} \cup parentstar[visited \cup {p}, parent[p]]

ancestors[p \in Process \cup {NONE}] == IF p = {NONE} THEN {} ELSE parentstar[{},p]       


SpanTree  == /\ \A p \in process : p \in children[root] \/ p = root
             /\ \A p \in process : p \notin ancestors[p]
                   

Liveness == <>(SpanTree)
Safety == [](\A p \in process : p \notin ancestors[p])


=============================================================================
\* Modification History
\* Last modified Tue Jul 07 16:51:26 WEST 2015 by nmm
\* Created Mon Jun 22 16:45:35 WEST 2015 by nmm
