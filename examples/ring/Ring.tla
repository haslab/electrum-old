------------------------------ MODULE Ring ------------------------------

EXTENDS Naturals

CONSTANT PROCESS 
VARIABLES toSend, succ, elected, process

-----------------------------------------------------------------------------

succstar[visited \in SUBSET process, p \in process] == 
    IF p \in visited THEN {} ELSE {succ[p]} \cup succstar[visited \cup {p}, succ[p]]

successors[p \in process] == succstar[{},p]

Init == /\ process \in SUBSET PROCESS
        /\ succ \in [process -> process]
        /\ toSend = [p \in process |-> {p}]
        /\ \A p \in process : process = successors[p]
        /\ elected = {}
         
         
TypeInv == /\ process \in SUBSET PROCESS
            /\ toSend \in [process -> SUBSET process]
            /\ succ \in [process -> process]
            /\ elected \in SUBSET process

Step(p) == /\ \E i \in toSend[p] : 
               (toSend' = [toSend EXCEPT ![p] = @ \ {i}, ![succ[p]] = IF i < succ[p] THEN @ ELSE @ \cup {i} ] /\
                elected' = IF i = succ[p] THEN elected \cup {i} ELSE elected)
           /\ UNCHANGED <<succ,process>>

Next == \E p \in process : Step(p)

Fairness == WF_<<toSend,succ,elected,process>>(\E p \in process : Step(p))

Spec == Init /\ [][Next]_<<toSend,succ,elected,process>> /\ Fairness

-----------------------------------------------------------------------------

Liveness == <>(elected /= {})
Safety == \neg <>(\E i1,i2 \in elected : i1 /= i2)

=============================================================================



\* Modification History
\* Last modified Wed Jul 08 15:39:59 WEST 2015 by nmm
\* Created Mon Feb 23 12:03:05 WET 2015 by nmm
