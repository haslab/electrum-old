------------------------------- MODULE Hotel -------------------------------
EXTENDS Naturals 
CONSTANT Key, Room, Guest
VARIABLE keys, currentKey, lastKey, occupant, gKeys, room, guest
-----------------------------------------------------------------------------
TypeInv == /\ room \in SUBSET Room
           /\ guest \in SUBSET Guest
           /\ keys \in [room -> SUBSET Key]
           /\ currentKey \in [room -> Key]
           /\ \A r \in room : currentKey[r] \in keys[r]
           /\ \A r1,r2 \in room : (keys[r1] \cap keys[r2]) # {} => r1 = r2
           /\ lastKey \in [room -> Key]
           /\ occupant \in [room -> SUBSET guest]
           /\ gKeys \in [guest -> SUBSET Key]
           
           
Init == /\ room \in SUBSET Room
        /\ guest \in SUBSET Guest
        /\ keys \in [room -> SUBSET Key]
        /\ currentKey \in [room -> Key]
        /\ \A r \in room : currentKey[r] \in keys[r]
        /\ \A r1,r2 \in room : (keys[r1] \cap keys[r2]) # {} => r1 = r2
        /\ lastKey = currentKey
        /\ occupant = [r \in room |-> {}]
        /\ gKeys = [g \in guest |-> {}]

vars == <<keys,currentKey,lastKey,occupant,gKeys,guest,room>>
       
nextKey[k \in Key, ks \in SUBSET Key] == {x \in ks : x > k /\ (\A y \in ks : y > k => x <= y)} 

Entry(g,r,k) == /\ (k = currentKey[r] \/ {k} = nextKey[currentKey[r],keys[r]])
                /\ k \in gKeys[g]
                /\ currentKey' = [currentKey EXCEPT ![r] = k]
                /\ UNCHANGED<<keys,lastKey,occupant,gKeys,guest,room>>
                
Checkout(g) == /\ \E r \in room : g \in occupant[r]
               /\ occupant' = [r \in DOMAIN occupant |-> occupant[r] \ {g}]
               /\ UNCHANGED<<keys,lastKey,currentKey,gKeys,guest,room>>
                              
Checkin(g,r,k) == /\ occupant[r] = {}
                  /\ {k} = nextKey[lastKey[r],keys[r]]
                  /\ occupant' = [occupant EXCEPT ![r] = @ \cup {g}]
                  /\ gKeys' = [gKeys EXCEPT ![g] = @ \cup {k}]
                  /\ lastKey' = [lastKey EXCEPT ![r] = k]
                  /\ UNCHANGED<<keys,currentKey,guest,room>>

Next == \E g \in guest : Checkout(g) \/ \E r \in room, k \in Key : Entry(g,r,k) \/ Checkin(g,r,k)

Spec == Init /\ [Next]_vars
-----------------------------------------------------------------------------
NoBadEntries == 
  [][\A g \in guest, r \in room, k \in Key : Entry(g,r,k) /\ occupant[r] # {} => g \in occupant[r]]_vars

NoIntervenes == 
  [\A g \in guest, k \in Key, r \in room : (g \in occupant[r] /\ k \in gKeys[g] /\ lastKey[r] = k /\ currentKey[r] # k) => Entry(g,r,k)]_vars
=============================================================================
\* Modification History
\* Last modified Tue Mar 31 10:44:29 WEST 2015 by nmm
\* Created Fri Feb 27 09:57:00 WET 2015 by nmm
