module chapter6/hotel2 --- the final model in Fig 6.7

open util/ordering[Time] as to
open util/ordering[Key] as ko

sig Key {}
sig Time {}

sig Room {
	keys: set Key,
	currentKey: keys one -> Time
	}

fact DisjointKeySets {
	-- each key belongs to at most one room
	Room<:keys   in   Room lone-> Key
	}

one sig FrontDesk {
	lastKey: (Room -> lone Key) -> Time,
	occupant: (Room -> Guest) -> Time
	}

sig Guest {
	keys: Key -> Time
	}

fun nextKey [k: Key, ks: set Key]: set Key {
	min [k.nexts & ks]
	}

pred init [t: Time] {
	no Guest.keys.t
	no FrontDesk.occupant.t
	all r: Room | FrontDesk.lastKey.t [r] = r.currentKey.t
	}

pred entry [t, t': Time, g: Guest, r: Room, k: Key] {
	k in g.keys.t
	let ck = r.currentKey |
		(k = ck.t and ck.t' = ck.t) or 
		(k = nextKey[ck.t, r.keys] and ck.t' = k)
	noRoomChangeExcept [t, t', r]
	noGuestChangeExcept [t, t', none]
	noFrontDeskChange [t, t']
	}

pred noFrontDeskChange [t, t': Time] {
	FrontDesk.lastKey.t = FrontDesk.lastKey.t'
	FrontDesk.occupant.t = FrontDesk.occupant.t'
	}

pred noRoomChangeExcept [t, t': Time, rs: set Room] {
	all r: Room - rs | r.currentKey.t = r.currentKey.t'
	}
	
pred noGuestChangeExcept [t, t': Time, gs: set Guest] {
	all g: Guest - gs | g.keys.t = g.keys.t'
	}

pred checkout [t, t': Time, g: Guest] {
	let occ = FrontDesk.occupant {
		some occ.t.g
		occ.t' = occ.t - Room ->g
		}
	FrontDesk.lastKey.t = FrontDesk.lastKey.t'
	noRoomChangeExcept [t, t', none]
	noGuestChangeExcept [t, t', none]
	}

pred checkin [t, t': Time, g: Guest, r: Room, k: Key] {
	g.keys.t' = g.keys.t + k
	let occ = FrontDesk.occupant {
		no occ.t [r]
		occ.t' = occ.t + r -> g
		}
	let lk = FrontDesk.lastKey {
		lk.t' = lk.t ++ r -> k
		k = nextKey [lk.t [r], r.keys]
		}
	noRoomChangeExcept [t, t', none]
	noGuestChangeExcept [t, t', g]
	}

fact traces {
	init [first]
	all t: Time-last | let t' = t.next |
		some g: Guest, r: Room, k: Key |
			entry [t, t', g, r, k]
			or checkin [t, t', g, r, k]
			or checkout [t, t', g]
	}

fact NoIntervening {
	all t: Time-last | let t' = t.next, t" = t'.next |
		all g: Guest, r: Room, k: Key |
			checkin [t, t', g, r, k] => (entry [t', t", g, r, k] or no t")
	}

assert NoBadEntry {
	all t: Time, r: Room, g: Guest, k: Key |
		let t' = t.next, o = FrontDesk.occupant.t[r] | 
			entry [t, t', g, r, k] and some o => g in o
	}

/*fact a {
	some disj r1,r2,r3,r4 : Room, disj k1,k2,k3,k4,k5,k6 : Key |
		r1.keys = k1+k3 && r2.keys = k4+k2 && r3.keys = k5 && r4.keys=k6 &&
		r1.currentKey.first = k3 && r2.currentKey.first = k4 && r3.currentKey.first = k5 && r4.currentKey.first = k6
}*/

// After adding the NoIntervening fact,
// these commands no longer generate counterexamples
/*check NoBadEntry for 3 but exactly 4 Room, exactly 4 Guest, exactly 6 Key, 30 Time
check NoBadEntry for 3 but exactly 4 Room, exactly 4 Guest, exactly 6 Key, 29 Time
check NoBadEntry for 3 but exactly 4 Room, exactly 4 Guest, exactly 6 Key, 28 Time
check NoBadEntry for 3 but exactly 4 Room, exactly 4 Guest, exactly 6 Key, 27 Time
check NoBadEntry for 3 but exactly 4 Room, exactly 4 Guest, exactly 6 Key, 26 Time
check NoBadEntry for 3 but exactly 4 Room, exactly 4 Guest, exactly 6 Key, 25 Time
check NoBadEntry for 3 but exactly 4 Room, exactly 4 Guest, exactly 6 Key, 24 Time
check NoBadEntry for 3 but exactly 4 Room, exactly 4 Guest, exactly 6 Key, 23 Time
check NoBadEntry for 3 but exactly 4 Room, exactly 4 Guest, exactly 6 Key, 22 Time
check NoBadEntry for 3 but exactly 4 Room, exactly 4 Guest, exactly 6 Key, 21 Time
check NoBadEntry for 3 but exactly 4 Room, exactly 4 Guest, exactly 6 Key, 20 Time
check NoBadEntry for 3 but exactly 4 Room, exactly 4 Guest, exactly 6 Key, 19 Time
check NoBadEntry for 3 but exactly 4 Room, exactly 4 Guest, exactly 6 Key, 18 Time
check NoBadEntry for 3 but exactly 4 Room, exactly 4 Guest, exactly 6 Key, 17 Time
check NoBadEntry for 3 but exactly 4 Room, exactly 4 Guest, exactly 6 Key, 16 Time
check NoBadEntry for 3 but exactly 4 Room, exactly 4 Guest, exactly 6 Key, 15 Time
check NoBadEntry for 3 but exactly 4 Room, exactly 4 Guest, exactly 6 Key, 14 Time
check NoBadEntry for 3 but exactly 4 Room, exactly 4 Guest, exactly 6 Key, 13 Time
check NoBadEntry for 3 but exactly 4 Room, exactly 4 Guest, exactly 6 Key, 12 Time
check NoBadEntry for 3 but exactly 4 Room, exactly 4 Guest, exactly 6 Key, 11 Time
check NoBadEntry for 3 but exactly 4 Room, exactly 4 Guest, exactly 6 Key, 10 Time
check NoBadEntry for 3 but exactly 4 Room, exactly 4 Guest, exactly 6 Key, 9 Time
check NoBadEntry for 3 but exactly 4 Room, exactly 4 Guest, exactly 6 Key, 8 Time
check NoBadEntry for 3 but exactly 4 Room, exactly 4 Guest, exactly 6 Key, 7 Time
check NoBadEntry for 3 but exactly 4 Room, exactly 4 Guest, exactly 6 Key, 6 Time
check NoBadEntry for 3 but exactly 4 Room, exactly 4 Guest, exactly 6 Key, 5 Time
check NoBadEntry for 3 but exactly 4 Room, exactly 4 Guest, exactly 6 Key, 4 Time
check NoBadEntry for 3 but exactly 4 Room, exactly 4 Guest, exactly 6 Key, 3 Time
check NoBadEntry for 3 but exactly 4 Room, exactly 4 Guest, exactly 6 Key, 2 Time
check NoBadEntry for 3 but exactly 4 Room, exactly 4 Guest, exactly 6 Key, 1 Time*/

check NoBadEntry for 3 but exactly 3 Room, exactly 3 Guest, exactly 5 Key, 30 Time
check NoBadEntry for 3 but exactly 3 Room, exactly 3 Guest, exactly 5 Key, 29 Time
check NoBadEntry for 3 but exactly 3 Room, exactly 3 Guest, exactly 5 Key, 28 Time
check NoBadEntry for 3 but exactly 3 Room, exactly 3 Guest, exactly 5 Key, 27 Time
check NoBadEntry for 3 but exactly 3 Room, exactly 3 Guest, exactly 5 Key, 26 Time
check NoBadEntry for 3 but exactly 3 Room, exactly 3 Guest, exactly 5 Key, 25 Time
check NoBadEntry for 3 but exactly 3 Room, exactly 3 Guest, exactly 5 Key, 24 Time
check NoBadEntry for 3 but exactly 3 Room, exactly 3 Guest, exactly 5 Key, 23 Time
check NoBadEntry for 3 but exactly 3 Room, exactly 3 Guest, exactly 5 Key, 22 Time
check NoBadEntry for 3 but exactly 3 Room, exactly 3 Guest, exactly 5 Key, 21 Time
check NoBadEntry for 3 but exactly 3 Room, exactly 3 Guest, exactly 5 Key, 20 Time
check NoBadEntry for 3 but exactly 3 Room, exactly 3 Guest, exactly 5 Key, 19 Time
check NoBadEntry for 3 but exactly 3 Room, exactly 3 Guest, exactly 5 Key, 18 Time
check NoBadEntry for 3 but exactly 3 Room, exactly 3 Guest, exactly 5 Key, 17 Time
check NoBadEntry for 3 but exactly 3 Room, exactly 3 Guest, exactly 5 Key, 16 Time
check NoBadEntry for 3 but exactly 3 Room, exactly 3 Guest, exactly 5 Key, 15 Time
check NoBadEntry for 3 but exactly 3 Room, exactly 3 Guest, exactly 5 Key, 14 Time
check NoBadEntry for 3 but exactly 3 Room, exactly 3 Guest, exactly 5 Key, 13 Time
check NoBadEntry for 3 but exactly 3 Room, exactly 3 Guest, exactly 5 Key, 12 Time
check NoBadEntry for 3 but exactly 3 Room, exactly 3 Guest, exactly 5 Key, 11 Time
check NoBadEntry for 3 but exactly 3 Room, exactly 3 Guest, exactly 5 Key, 10 Time
check NoBadEntry for 3 but exactly 3 Room, exactly 3 Guest, exactly 5 Key, 9 Time
check NoBadEntry for 3 but exactly 3 Room, exactly 3 Guest, exactly 5 Key, 8 Time
check NoBadEntry for 3 but exactly 3 Room, exactly 3 Guest, exactly 5 Key, 7 Time
check NoBadEntry for 3 but exactly 3 Room, exactly 3 Guest, exactly 5 Key, 6 Time
check NoBadEntry for 3 but exactly 3 Room, exactly 3 Guest, exactly 5 Key, 5 Time
check NoBadEntry for 3 but exactly 3 Room, exactly 3 Guest, exactly 5 Key, 4 Time
check NoBadEntry for 3 but exactly 3 Room, exactly 3 Guest, exactly 5 Key, 3 Time
check NoBadEntry for 3 but exactly 3 Room, exactly 3 Guest, exactly 5 Key, 2 Time
check NoBadEntry for 3 but exactly 3 Room, exactly 3 Guest, exactly 5 Key, 1 Time

/*check NoBadEntry for 3 but exactly 2 Room, exactly 2 Guest, exactly 4 Key, 30 Time
check NoBadEntry for 3 but exactly 2 Room, exactly 2 Guest, exactly 4 Key, 29 Time
check NoBadEntry for 3 but exactly 2 Room, exactly 2 Guest, exactly 4 Key, 28 Time
check NoBadEntry for 3 but exactly 2 Room, exactly 2 Guest, exactly 4 Key, 27 Time
check NoBadEntry for 3 but exactly 2 Room, exactly 2 Guest, exactly 4 Key, 26 Time
check NoBadEntry for 3 but exactly 2 Room, exactly 2 Guest, exactly 4 Key, 25 Time
check NoBadEntry for 3 but exactly 2 Room, exactly 2 Guest, exactly 4 Key, 24 Time
check NoBadEntry for 3 but exactly 2 Room, exactly 2 Guest, exactly 4 Key, 23 Time
check NoBadEntry for 3 but exactly 2 Room, exactly 2 Guest, exactly 4 Key, 22 Time
check NoBadEntry for 3 but exactly 2 Room, exactly 2 Guest, exactly 4 Key, 21 Time
check NoBadEntry for 3 but exactly 2 Room, exactly 2 Guest, exactly 4 Key, 20 Time
check NoBadEntry for 3 but exactly 2 Room, exactly 2 Guest, exactly 4 Key, 19 Time
check NoBadEntry for 3 but exactly 2 Room, exactly 2 Guest, exactly 4 Key, 18 Time
check NoBadEntry for 3 but exactly 2 Room, exactly 2 Guest, exactly 4 Key, 17 Time
check NoBadEntry for 3 but exactly 2 Room, exactly 2 Guest, exactly 4 Key, 16 Time
check NoBadEntry for 3 but exactly 2 Room, exactly 2 Guest, exactly 4 Key, 15 Time
check NoBadEntry for 3 but exactly 2 Room, exactly 2 Guest, exactly 4 Key, 14 Time
check NoBadEntry for 3 but exactly 2 Room, exactly 2 Guest, exactly 4 Key, 13 Time
check NoBadEntry for 3 but exactly 2 Room, exactly 2 Guest, exactly 4 Key, 12 Time
check NoBadEntry for 3 but exactly 2 Room, exactly 2 Guest, exactly 4 Key, 11 Time
check NoBadEntry for 3 but exactly 2 Room, exactly 2 Guest, exactly 4 Key, 10 Time
check NoBadEntry for 3 but exactly 2 Room, exactly 2 Guest, exactly 4 Key, 9 Time
check NoBadEntry for 3 but exactly 2 Room, exactly 2 Guest, exactly 4 Key, 8 Time
check NoBadEntry for 3 but exactly 2 Room, exactly 2 Guest, exactly 4 Key, 7 Time
check NoBadEntry for 3 but exactly 2 Room, exactly 2 Guest, exactly 4 Key, 6 Time
check NoBadEntry for 3 but exactly 2 Room, exactly 2 Guest, exactly 4 Key, 5 Time
check NoBadEntry for 3 but exactly 2 Room, exactly 2 Guest, exactly 4 Key, 4 Time
check NoBadEntry for 3 but exactly 2 Room, exactly 2 Guest, exactly 4 Key, 3 Time
check NoBadEntry for 3 but exactly 2 Room, exactly 2 Guest, exactly 4 Key, 2 Time
check NoBadEntry for 3 but exactly 2 Room, exactly 2 Guest, exactly 4 Key, 1 Time*/

/*check NoBadEntry for 3 but exactly 1 Room, exactly 1 Guest, exactly 3 Key, 30 Time
check NoBadEntry for 3 but exactly 1 Room, exactly 1 Guest, exactly 3 Key, 29 Time
check NoBadEntry for 3 but exactly 1 Room, exactly 1 Guest, exactly 3 Key, 28 Time
check NoBadEntry for 3 but exactly 1 Room, exactly 1 Guest, exactly 3 Key, 27 Time
check NoBadEntry for 3 but exactly 1 Room, exactly 1 Guest, exactly 3 Key, 26 Time
check NoBadEntry for 3 but exactly 1 Room, exactly 1 Guest, exactly 3 Key, 25 Time
check NoBadEntry for 3 but exactly 1 Room, exactly 1 Guest, exactly 3 Key, 24 Time
check NoBadEntry for 3 but exactly 1 Room, exactly 1 Guest, exactly 3 Key, 23 Time
check NoBadEntry for 3 but exactly 1 Room, exactly 1 Guest, exactly 3 Key, 22 Time
check NoBadEntry for 3 but exactly 1 Room, exactly 1 Guest, exactly 3 Key, 21 Time
check NoBadEntry for 3 but exactly 1 Room, exactly 1 Guest, exactly 3 Key, 20 Time
check NoBadEntry for 3 but exactly 1 Room, exactly 1 Guest, exactly 3 Key, 19 Time
check NoBadEntry for 3 but exactly 1 Room, exactly 1 Guest, exactly 3 Key, 18 Time
check NoBadEntry for 3 but exactly 1 Room, exactly 1 Guest, exactly 3 Key, 17 Time
check NoBadEntry for 3 but exactly 1 Room, exactly 1 Guest, exactly 3 Key, 16 Time
check NoBadEntry for 3 but exactly 1 Room, exactly 1 Guest, exactly 3 Key, 15 Time
check NoBadEntry for 3 but exactly 1 Room, exactly 1 Guest, exactly 3 Key, 14 Time
check NoBadEntry for 3 but exactly 1 Room, exactly 1 Guest, exactly 3 Key, 13 Time
check NoBadEntry for 3 but exactly 1 Room, exactly 1 Guest, exactly 3 Key, 12 Time
check NoBadEntry for 3 but exactly 1 Room, exactly 1 Guest, exactly 3 Key, 11 Time
check NoBadEntry for 3 but exactly 1 Room, exactly 1 Guest, exactly 3 Key, 10 Time
check NoBadEntry for 3 but exactly 1 Room, exactly 1 Guest, exactly 3 Key, 9 Time
check NoBadEntry for 3 but exactly 1 Room, exactly 1 Guest, exactly 3 Key, 8 Time
check NoBadEntry for 3 but exactly 1 Room, exactly 1 Guest, exactly 3 Key, 7 Time
check NoBadEntry for 3 but exactly 1 Room, exactly 1 Guest, exactly 3 Key, 6 Time
check NoBadEntry for 3 but exactly 1 Room, exactly 1 Guest, exactly 3 Key, 5 Time
check NoBadEntry for 3 but exactly 1 Room, exactly 1 Guest, exactly 3 Key, 4 Time
check NoBadEntry for 3 but exactly 1 Room, exactly 1 Guest, exactly 3 Key, 3 Time
check NoBadEntry for 3 but exactly 1 Room, exactly 1 Guest, exactly 3 Key, 2 Time
check NoBadEntry for 3 but exactly 1 Room, exactly 1 Guest, exactly 3 Key, 1 Time*/

/*check NoBadEntry for 3 but exactly 0 Room, exactly 0 Guest, exactly 2 Key, 30 Time
check NoBadEntry for 3 but exactly 0 Room, exactly 0 Guest, exactly 2 Key, 29 Time
check NoBadEntry for 3 but exactly 0 Room, exactly 0 Guest, exactly 2 Key, 28 Time
check NoBadEntry for 3 but exactly 0 Room, exactly 0 Guest, exactly 2 Key, 27 Time
check NoBadEntry for 3 but exactly 0 Room, exactly 0 Guest, exactly 2 Key, 26 Time
check NoBadEntry for 3 but exactly 0 Room, exactly 0 Guest, exactly 2 Key, 25 Time
check NoBadEntry for 3 but exactly 0 Room, exactly 0 Guest, exactly 2 Key, 24 Time
check NoBadEntry for 3 but exactly 0 Room, exactly 0 Guest, exactly 2 Key, 23 Time
check NoBadEntry for 3 but exactly 0 Room, exactly 0 Guest, exactly 2 Key, 22 Time
check NoBadEntry for 3 but exactly 0 Room, exactly 0 Guest, exactly 2 Key, 21 Time
check NoBadEntry for 3 but exactly 0 Room, exactly 0 Guest, exactly 2 Key, 20 Time
check NoBadEntry for 3 but exactly 0 Room, exactly 0 Guest, exactly 2 Key, 19 Time
check NoBadEntry for 3 but exactly 0 Room, exactly 0 Guest, exactly 2 Key, 18 Time
check NoBadEntry for 3 but exactly 0 Room, exactly 0 Guest, exactly 2 Key, 17 Time
check NoBadEntry for 3 but exactly 0 Room, exactly 0 Guest, exactly 2 Key, 16 Time
check NoBadEntry for 3 but exactly 0 Room, exactly 0 Guest, exactly 2 Key, 15 Time
check NoBadEntry for 3 but exactly 0 Room, exactly 0 Guest, exactly 2 Key, 14 Time
check NoBadEntry for 3 but exactly 0 Room, exactly 0 Guest, exactly 2 Key, 13 Time
check NoBadEntry for 3 but exactly 0 Room, exactly 0 Guest, exactly 2 Key, 12 Time
check NoBadEntry for 3 but exactly 0 Room, exactly 0 Guest, exactly 2 Key, 11 Time
check NoBadEntry for 3 but exactly 0 Room, exactly 0 Guest, exactly 2 Key, 10 Time
check NoBadEntry for 3 but exactly 0 Room, exactly 0 Guest, exactly 2 Key, 9 Time
check NoBadEntry for 3 but exactly 0 Room, exactly 0 Guest, exactly 2 Key, 8 Time
check NoBadEntry for 3 but exactly 0 Room, exactly 0 Guest, exactly 2 Key, 7 Time
check NoBadEntry for 3 but exactly 0 Room, exactly 0 Guest, exactly 2 Key, 6 Time
check NoBadEntry for 3 but exactly 0 Room, exactly 0 Guest, exactly 2 Key, 5 Time
check NoBadEntry for 3 but exactly 0 Room, exactly 0 Guest, exactly 2 Key, 4 Time
check NoBadEntry for 3 but exactly 0 Room, exactly 0 Guest, exactly 2 Key, 3 Time
check NoBadEntry for 3 but exactly 0 Room, exactly 0 Guest, exactly 2 Key, 2 Time
check NoBadEntry for 3 but exactly 0 Room, exactly 0 Guest, exactly 2 Key, 1 Time*/

/*check NoBadEntry for 4 but 30 Time
check NoBadEntry for 4 but 29 Time
check NoBadEntry for 4 but 28 Time
check NoBadEntry for 4 but 27 Time
check NoBadEntry for 4 but 26 Time
check NoBadEntry for 4 but 25 Time
check NoBadEntry for 4 but 24 Time
check NoBadEntry for 4 but 23 Time
check NoBadEntry for 4 but 22 Time
check NoBadEntry for 4 but 21 Time
check NoBadEntry for 4 but 20 Time
check NoBadEntry for 4 but 19 Time
check NoBadEntry for 4 but 18 Time
check NoBadEntry for 4 but 17 Time
check NoBadEntry for 4 but 16 Time
check NoBadEntry for 4 but 15 Time
check NoBadEntry for 4 but 14 Time
check NoBadEntry for 4 but 13 Time
check NoBadEntry for 4 but 12 Time
check NoBadEntry for 4 but 11 Time
check NoBadEntry for 4 but 10 Time
check NoBadEntry for 4 but 9 Time
check NoBadEntry for 4 but 8 Time
check NoBadEntry for 4 but 7 Time
check NoBadEntry for 4 but 6 Time
check NoBadEntry for 4 but 5 Time
check NoBadEntry for 4 but 4 Time
check NoBadEntry for 4 but 3 Time
check NoBadEntry for 4 but 2 Time
check NoBadEntry for 4 but 1 Time*/

/*check NoBadEntry for 3 but 30 Time
check NoBadEntry for 3 but 29 Time
check NoBadEntry for 3 but 28 Time
check NoBadEntry for 3 but 27 Time
check NoBadEntry for 3 but 26 Time
check NoBadEntry for 3 but 25 Time
check NoBadEntry for 3 but 24 Time
check NoBadEntry for 3 but 23 Time
check NoBadEntry for 3 but 22 Time
check NoBadEntry for 3 but 21 Time
check NoBadEntry for 3 but 20 Time
check NoBadEntry for 3 but 19 Time
check NoBadEntry for 3 but 18 Time
check NoBadEntry for 3 but 17 Time
check NoBadEntry for 3 but 16 Time
check NoBadEntry for 3 but 15 Time
check NoBadEntry for 3 but 14 Time
check NoBadEntry for 3 but 13 Time
check NoBadEntry for 3 but 12 Time
check NoBadEntry for 3 but 11 Time
check NoBadEntry for 3 but 10 Time
check NoBadEntry for 3 but 9 Time
check NoBadEntry for 3 but 8 Time
check NoBadEntry for 3 but 7 Time
check NoBadEntry for 3 but 6 Time
check NoBadEntry for 3 but 5 Time
check NoBadEntry for 3 but 4 Time
check NoBadEntry for 3 but 3 Time
check NoBadEntry for 3 but 2 Time
check NoBadEntry for 3 but 1 Time*/

/*check NoBadEntry for 2 but 30 Time
check NoBadEntry for 2 but 29 Time
check NoBadEntry for 2 but 28 Time
check NoBadEntry for 2 but 27 Time
check NoBadEntry for 2 but 26 Time
check NoBadEntry for 2 but 25 Time
check NoBadEntry for 2 but 24 Time
check NoBadEntry for 2 but 23 Time
check NoBadEntry for 2 but 22 Time
check NoBadEntry for 2 but 21 Time
check NoBadEntry for 2 but 20 Time
check NoBadEntry for 2 but 19 Time
check NoBadEntry for 2 but 18 Time
check NoBadEntry for 2 but 17 Time
check NoBadEntry for 2 but 16 Time
check NoBadEntry for 2 but 15 Time
check NoBadEntry for 2 but 14 Time
check NoBadEntry for 2 but 13 Time
check NoBadEntry for 2 but 12 Time
check NoBadEntry for 2 but 11 Time
check NoBadEntry for 2 but 10 Time
check NoBadEntry for 2 but 9 Time
check NoBadEntry for 2 but 8 Time
check NoBadEntry for 2 but 7 Time
check NoBadEntry for 2 but 6 Time
check NoBadEntry for 2 but 5 Time
check NoBadEntry for 2 but 4 Time
check NoBadEntry for 2 but 3 Time
check NoBadEntry for 2 but 2 Time
check NoBadEntry for 2 but 1 Time*/

/*check NoBadEntry for 1 but 30 Time
check NoBadEntry for 1 but 29 Time
check NoBadEntry for 1 but 28 Time
check NoBadEntry for 1 but 27 Time
check NoBadEntry for 1 but 26 Time
check NoBadEntry for 1 but 25 Time
check NoBadEntry for 1 but 24 Time
check NoBadEntry for 1 but 23 Time
check NoBadEntry for 1 but 22 Time
check NoBadEntry for 1 but 21 Time
check NoBadEntry for 1 but 20 Time
check NoBadEntry for 1 but 19 Time
check NoBadEntry for 1 but 18 Time
check NoBadEntry for 1 but 17 Time
check NoBadEntry for 1 but 16 Time
check NoBadEntry for 1 but 15 Time
check NoBadEntry for 1 but 14 Time
check NoBadEntry for 1 but 13 Time
check NoBadEntry for 1 but 12 Time
check NoBadEntry for 1 but 11 Time
check NoBadEntry for 1 but 10 Time
check NoBadEntry for 1 but 9 Time
check NoBadEntry for 1 but 8 Time
check NoBadEntry for 1 but 7 Time
check NoBadEntry for 1 but 6 Time
check NoBadEntry for 1 but 5 Time
check NoBadEntry for 1 but 4 Time
check NoBadEntry for 1 but 3 Time
check NoBadEntry for 1 but 2 Time
check NoBadEntry for 1 but 1 Time*/

/*check NoBadEntry for 0 but 30 Time
check NoBadEntry for 0 but 29 Time
check NoBadEntry for 0 but 28 Time
check NoBadEntry for 0 but 27 Time
check NoBadEntry for 0 but 26 Time
check NoBadEntry for 0 but 25 Time
check NoBadEntry for 0 but 24 Time
check NoBadEntry for 0 but 23 Time
check NoBadEntry for 0 but 22 Time
check NoBadEntry for 0 but 21 Time
check NoBadEntry for 0 but 20 Time
check NoBadEntry for 0 but 19 Time
check NoBadEntry for 0 but 18 Time
check NoBadEntry for 0 but 17 Time
check NoBadEntry for 0 but 16 Time
check NoBadEntry for 0 but 15 Time
check NoBadEntry for 0 but 14 Time
check NoBadEntry for 0 but 13 Time
check NoBadEntry for 0 but 12 Time
check NoBadEntry for 0 but 11 Time
check NoBadEntry for 0 but 10 Time
check NoBadEntry for 0 but 9 Time
check NoBadEntry for 0 but 8 Time
check NoBadEntry for 0 but 7 Time
check NoBadEntry for 0 but 6 Time
check NoBadEntry for 0 but 5 Time
check NoBadEntry for 0 but 4 Time
check NoBadEntry for 0 but 3 Time
check NoBadEntry for 0 but 2 Time
check NoBadEntry for 0 but 1 Time*/
