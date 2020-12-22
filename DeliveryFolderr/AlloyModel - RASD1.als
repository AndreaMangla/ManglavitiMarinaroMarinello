/*
** in this model we assume that timetables of supermarkets are updated every  
** midnight so that there are not timetables of past days and the first 
** element of seq timetable is the timetable of the current day
** Also, we assume that this application will be used by only one chain of 
** Supermarkets
*/


/* ** SIGNATURES ** */

/*
** Signatures of Position are empty because no further details are needed
** We only need to state that a position in different form another one 
** and Alloy does it already
*/
abstract sig Position{}
sig SupermarketPosition extends Position {}
sig GPSPosition extends Position {}

/*
** Signature of Time with details because we need to verify if
** a time is precedent to other times
** There is also a fact that states the correctness of a time
*/
sig Time {
    hour: one Int,
    minute: one Int,
    second: one Int
} {
    hour > 0
    minute > 0
    second > 0
}

/*
** Signature of Date: it is empty for the same reason stated in
** comment of signature Position
*/
sig Date {} {
    all d: Date | some tt: Timetable | tt.date = d
}

/*
** Data represents the database of the system and contains data of
** registered users, supermarkets of the chain, valid/used entrances
*/
one sig Data {
    users: set User,
    supermarkets: set Supermarket,
    entrances: set Entrance
}

/*
** Signatures Customer modelizes the different behaviour of a registered
** customer (User) and unregistered ones (modelized as a Singleton)
*/
abstract sig Customer {}
sig User extends Customer {
    name: lone String,
    surname: lone String,
    position: one GPSPosition,
    activeEntrance: lone Entrance
} {
    activeEntrance != none implies (activeEntrance.customer = this and activeEntrance.state = VALID)
}
one sig nonUser extends Customer {}

/*
** Supermarket, with some constraints obvious
*/
sig Supermarket {
    name: lone String,
    capacity: one Int,
    position: one SupermarketPosition,
    timetable: seq Timetable,
    supermarketCategories: set Category,
    manager: one Manager,
    ticketMachine: one TicketMachine,
    lines: one Lines,
    statistics: one Statistics
} {
    #timetable > 0
    #supermarketCategories > 0
    !(timetable.hasDups)
    capacity > #lines.people or capacity = #lines.people
    ticketMachine.supermarket = this
}

/*
** Signatures completing the description of the Supermarket one
*/
sig Statistics {
    supermarket: one Supermarket
} {
    supermarket.statistics = this
}
sig Manager {
    supermarket: one Supermarket
} {
    supermarket.manager = this
}
sig TicketMachine {
    supermarket: one Supermarket
} {
    supermarket.ticketMachine = this
}

/*
** Signatures completing the desctiption of Entrance one
*/
sig QR {}
abstract sig EntranceState {}
one sig VALID extends EntranceState {}
one sig USED extends EntranceState {}
one sig EXPIRED extends EntranceState {}

/*
** signature that modelize the category of products in the supermarket
** each category must belong to at least one supermarket, otherwise
** it has no sense to exist (customers cannot purchase products of a
** category that does not exist in any supermarket)
*/
sig Category {} {
    all c: Category | some s: Supermarket | c in s.supermarketCategories
}

/*
** signature that modelize the vehicle that user should take to reach the
** supermarket, to help the system calculate the waiting time.
** each vahicle should be associated to one or more tickets
*/
sig Vehicle {} {
    all v: Vehicle | some t: Ticket | t.vehicle = v
}

/*
** Signature of possible entrances:
** 1) The main signature contiains all common attributes, important to 
**    identify the entrance
** 2) Ticket signature extends Entrance one, adding its own specific 
**    characteristic
** 3) Visit signature also adds some constraints, such as customer has  
**    to be a registered one, or the consistency of the timeslot
** As regard the constraints of the signature:
** 1) we state that if an entrance is done by a customer and it is  
**    valid, then it is the active entrance of that user: in this way, 
**    we have that if  an entrance does not appear as the active entrance 
**    of a user, then its state must not be valid or its owner is a nonUser
** 2) we state also that if the owner of the entrance is a nonUser, then 
**    there cannot be a user that has that entrance as an active entrance
*/
abstract sig Entrance {
    code: one QR,
    customer: one Customer,
    supermarket: one Supermarket,
    date: one Date,
    arrivalTime: lone Time,
    timeSpent: lone Time,
    state: one EntranceState,
} {
    ((customer in User and state = VALID) implies customer.activeEntrance = this)
    customer = nonUser implies (no u: User | u.activeEntrance = this)
}
sig Ticket extends Entrance {
    vehicle: one Vehicle
}
sig Visit extends Entrance {
    categories: set Category,
    exitTime: one Time
} {
    customer in Data.users
    arrivalTime != none
    timeIsPrecedent[arrivalTime, exitTime]
    #categories > 0
    all c: Category | c in categories implies c in supermarket.supermarketCategories
}

/*
** Timetable of the supermarket, in which for each day it is stated opening  
** and closure time, providing consistency with predicate timeIsPrecedent
*/ 
sig Timetable {
    date: one Date,
    openingTime: one Time,
    closureTime: one Time
} {
    timeIsPrecedent[openingTime, closureTime]
}

/*
** Core of the application, that allows the correct lining-up of customers
** There are two constraints:
** 1) registered customers must line-up only in their own line
** 2) unregistered customers must line-up in their own line (fallback option)
*/
sig Lines {
    supermarket: one Supermarket,
    people: set Entrance,
    userLineUp: set Ticket,
    nonUserLineUp: set Ticket,
    visits: set Visit
} {
    supermarket.lines = this
    all e: Entrance | e in people implies e.date = supermarket.timetable.first.date
    all e: Entrance | e in userLineUp implies (e.customer in User and e.date = supermarket.timetable.first.date)
    all e: Entrance | e in nonUserLineUp implies (e.customer = nonUser and e.date = supermarket.timetable.first.date)
}

/*
** Time slot of visits
*/
sig TimeSlot{
    supermarket: one Supermarket,
    arrivalTime: one Time,
    exitTime: one Time
} {
    supermarket in Data.supermarkets
    timeIsPrecedent[arrivalTime, exitTime]
}

/*
** Signature that modelizes the request to line-up in a specific supermarket
** enabling the availability check of space and the computing of other 
** solutions
*/
sig AvailabilityRequestTicket {
    user: one User,
    supermarket: one Supermarket
} {
    user.activeEntrance = none
}

/*
** Signature equivalent as the precedent, but for Visits
*/
sig AvailabilityRequestVisit {
    user: one User,
    timeSlot: one TimeSlot
} {
    user.activeEntrance = none
}

/*
** This is the response for the previous request (Ticket)
** If the requested supermarket is in the list, then the list must
** contain only that supermarket
*/
sig SuggestTicket {
    request: one AvailabilityRequestTicket,
    ticketSuggestions: set Supermarket
} {
    #ticketSuggestions > 0
    request.supermarket in ticketSuggestions implies #ticketSuggestions = 1
    request.supermarket not in ticketSuggestions implies (
        all s: Supermarket | s in ticketSuggestions iff (
            #request.supermarket.lines.userLineUp > #s.lines.userLineUp and 
            s.capacity > #s.lines.userLineUp
        )
    )
}

/*
** This is the response for the previous request (Visit)
** As before, if the requested time slot is in the list, the the list
** must contain only that slot
** Otherwise the list will contain all those time slots that satisfy only
** one of the following requirements:
** 1) same supermarket, but different time slot
** 2) same time slot, but different supermarket
*/
sig SuggestVisit {
    request: one AvailabilityRequestVisit,
    visitSuggestions: set TimeSlot
} {
    #visitSuggestions > 0
    request.timeSlot in visitSuggestions implies #visitSuggestions = 1
    request.timeSlot not in visitSuggestions implies (
        all ts: TimeSlot | ts in visitSuggestions implies ((
            ts.supermarket = request.timeSlot.supermarket and (
            (timeIsPrecedent[ts.exitTime, request.timeSlot.arrivalTime] and 
            timeIsPrecedent[request.timeSlot.supermarket.timetable.first.openingTime, ts.arrivalTime])
            or (timeIsPrecedent[request.timeSlot.exitTime, ts.arrivalTime] and 
            timeIsPrecedent[ts.exitTime, request.timeSlot.supermarket.timetable.first.closureTime]))
            ) or 
            (ts.supermarket != request.timeSlot.supermarket and 
            ts.arrivalTime = request.timeSlot.arrivalTime and
            ts.exitTime = request.timeSlot.exitTime)
        )
    )
}

/*
** Signature of notification, that can arrive only to registered users without 
** an active entrance. The purpose of this signature is to show that if such a
** notification exists, the corresponding user has no active entrance and its
** time slot correspond to at least one of that user's used visit
*/
sig Notification {
    user: one User,
    notification: one TimeSlot
} {
    user in Data.users
    user.activeEntrance = none 
    some v: Visit | (v in Data.entrances and v.customer = user) implies (
        notification.supermarket = v.supermarket and notification.arrivalTime = v.arrivalTime
        and notification.exitTime = v.exitTime
    )
}


/* ** FACTS ** */

/*
** data must contain only data of registered customers (users), data of 
** supermarkets and data of non expired entrances of registered customers 
** (users)
*/
fact dataConsistency {
    all u: User | u in Data.users
    all s: Supermarket | s in Data.supermarkets
    all e: Entrance | e in Data.entrances iff (e.state != EXPIRED and e.customer in User)
}

/*
** every entrance must have one unique QR to distinguish it
** from other entrances
*/
fact uniqueQR {
    all e1, e2: Entrance | e1.code = e2.code iff e1 = e2
    all qr: QR | one e: Entrance | e.code = qr
}

/*
** every supermarket is unique, i.e. there cannot be more
** supermarkets with same references
*/
fact uniqueSupermarkets {
    all s1, s2: Supermarket | s1.position = s2.position iff s1 = s2
    all s1, s2: Supermarket | s1.lines = s2.lines iff s1 = s2
    all s1, s2: Supermarket | s1.ticketMachine = s2.ticketMachine iff s1 = s2
    all s1, s2: Supermarket | s1.manager = s2.manager iff s1 = s2
    all s1, s2: Supermarket | s1.statistics = s2.statistics iff s1 = s2
    #Supermarket = #SupermarketPosition
}

/*
** users cannot be in the same position, otherwise they would be the same 
** person (we exclude multiple smartphones for one person)
*/
fact noUsersSamePosition {
    all u1, u2: User | u1.position = u2.position iff u1 = u2
    #User > #GPSPosition or #User = #GPSPosition
}

/*
** customers are not allowed after closure
** (only visits scheduled for future days are allowed)
*/
fact noCustomersInsideAfterClosure {
    all s: Supermarket | all t: Time |  
    timeIsPrecedent[s.timetable.first.closureTime, t] implies (
        (#s.lines.people = 0 and #s.lines.userLineUp = 0 and #s.lines.nonUserLineUp = 0) and 
        (all v: Visit | v in s.lines.visits implies v.date != s.timetable.first.date)
    )
}

/*
** customers are not allowed before opening
** (only visits scheduled for future days are allowed)
*/
fact noCustomersInsideBeforeOpening {
    all s: Supermarket | all t: Time |
    timeIsPrecedent[t, s.timetable.first.openingTime] implies (
        (#s.lines.people = 0 and #s.lines.userLineUp = 0 and #s.lines.nonUserLineUp = 0)
    )
}

/*
** no entrances after closure
*/
fact noEntrancesAfterClosure {
    all s: Supermarket | no tk: Ticket | timeIsPrecedent[s.timetable.first.closureTime, tk.arrivalTime] 
        and s.timetable.first.date = tk.date
    all s: Supermarket | no v: Visit | timeIsPrecedent[s.timetable.first.closureTime, v.arrivalTime] 
        and s.timetable.first.date = v.date
}

/* 
** no entrances before opening
*/
fact noEntrancesBeforeOpening {
    all s: Supermarket | no tk: Ticket | timeIsPrecedent[tk.arrivalTime, s.timetable.first.openingTime] 
        and s.timetable.first.date = tk.date
    all s: Supermarket | no v: Visit | timeIsPrecedent[v.arrivalTime, s.timetable.first.openingTime] 
        and s.timetable.first.date = v.date
}

/*
** This is the most important fact, because it shows that entrances can 
** be correctly lined-up  (purpose of the application)
** 1) every entrance that is lined-up in every lines it must be VALID
** 2) an entrance to be valid must be correctly lined-up in one and only 
**    one sublines of the corresponding supermarket
** 3) every supermarket lines cannot contain entrances of other 
**    supermarkets
*/
fact correctlyLined {
    all e: Entrance | all l: Lines | (e in l.people or e in l.userLineUp or e in l.nonUserLineUp 
        or e in l.visits) implies e.state = VALID
    all e: Entrance | e.state = VALID iff inLines[e, e.supermarket.lines]
    all l: Lines | all e: Entrance | l != e.supermarket.lines implies (e not in l.people and 
        e not in l.userLineUp and e not in l.nonUserLineUp and e not in l.visits)
}

/*
** User cannot send more than one request at a time while creating 
** an entrance and, consequently (iff), he/she cannot receive
** more than one response
*/
fact noContemporaneousRequests {
    all rt: AvailabilityRequestTicket | all rv: AvailabilityRequestVisit | rt.user != rv.user
    all rt1, rt2: AvailabilityRequestTicket | rt1.user = rt2.user iff rt1 = rt2
    all rv1, rv2: AvailabilityRequestVisit | rv1.user = rv2.user iff rv1 = rv2
}

/*
** Consistency of answers from server: one for each request
*/
fact oneAnswerForEachRequest {
    all st1, st2: SuggestTicket | st1.request = st2.request iff st1 = st2
    all sv1, sv2: SuggestVisit | sv1.request = sv2.request iff sv1 = sv2
}

/*
** As before, but for notifications
*/
fact noContemporaneousNotification {
    all n1, n2: Notification | n1.user = n2.user iff n1 = n2
}

/*
** As said before, this fact states that a notification can 
** happen onlyif the customer has already booked and 
** exploited at least one visit
*/ 
fact noNotificationWithoutData {
    all u: User | (no v: Visit | v in Data.entrances and v.customer = u) implies (
        no n: Notification | n.user = u
    )
}

/*
** Timetables can exists only if they are linked to a supermarket
*/
fact NoLonelyTimetables {
    no tt: Timetable | (all s: Supermarket | #(s.timetable.indsOf[tt]) = 0)
}


/* ** PREDICATES ** */

/*
** predicate that allows to check if an entrance e correctly 
** belongs to lines l, that is, e belongs to one and only one 
** of the sublines of l
*/
pred inLines[e: Entrance, l: Lines] {
    (e in l.people and e not in l.userLineUp and e not in l.nonUserLineUp and e not in l.visits) or
    (e not in l.people and e in l.userLineUp and e not in l.nonUserLineUp and e not in l.visits 
        and e in Ticket) or
    (e not in l.people and e not in l.userLineUp and e in l.nonUserLineUp and e not in l.visits 
        and e in Ticket) or
    (e not in l.people and e not in l.userLineUp and e not in l.nonUserLineUp and e in l.visits 
        and e in Visit)
}
run inLines

/*
** predicate that allows to check if a time t1 precedes 
** a time t2
*/
pred timeIsPrecedent [t1: Time, t2: Time] {
    (t2.hour > t1.hour) or (t2.hour = t1.hour and t2.minute > t1.minute)
}
run timeIsPrecedent

/*
** This predicate aims to show the correct separation of lines 
** in a supermarket
*/
pred LineDistinction {
    #Ticket = 2
    #Visit = 2
    #User = 3
    #Supermarket = 1
    one t: Ticket | t.customer in User
    #Supermarket.lines.people = 1
    #Supermarket.lines.userLineUp = 1
    #Supermarket.lines.nonUserLineUp = 1
    #Supermarket.lines.visits = 1
}
run LineDistinction for 7

/*
** This predicate aims to show the correct behaviour of 
** a notification
*/
pred timeToShop (n: Notification, u: User, v: Visit){
    n.user = u
    #Notification = 1
    #User = 1
}
run timeToShop for 7

/*
** This predicate aims to show the correct answer to 
** an availability request from a user during the creation
** of a ticket (indeed that user has no active entrance). 
** We put 3 supermarkets, in which the request is made on 
** the most crowded, instead the two other are way less crowded
** and they can appear in the recommendations
*/
pred suggestionToChangeSupermarket (u: User, s, s', s'': Supermarket, st: SuggestTicket, 
    rt: AvailabilityRequestTicket, d: Date) {
    #Supermarket = 3
    #s.lines.people = 1
    s.capacity = 1
    #s.lines.userLineUp = 2
    #s'.lines.people = 0
    s'.capacity = 1
    #s'.lines.userLineUp = 0
    #s'.lines.nonUserLineUp = 0
    #s'.lines.visits = 0
    #s''.lines.people = 0
    s''.capacity = 1
    #s''.lines.userLineUp = 0
    #s''.lines.nonUserLineUp = 0
    #s''.lines.visits = 0
    s' != s''
    rt.user = u
    rt.supermarket = s
    st.request = rt
    s not in st.ticketSuggestions
    all super: Supermarket | super.timetable.first.date = d
}
run suggestionToChangeSupermarket for 7

/*
** This predicate aims to show the correct answer to 
** an availability request from a user during the creation 
** of a ticket (indeed that user has no active entrance). 
** We put 3 supermarkets, in which the request is made on 
** the most crowded, instead only one of the two others is way 
** less crowded and it can appear in the recommendations
*/
pred suggestionToChangeSupermarket_OneSuggestion (u: User, s, s', s'': Supermarket, st: SuggestTicket, 
    rt: AvailabilityRequestTicket, d: Date) {
    #Supermarket = 3
    #s.lines.people = 1
    s.capacity = 1
    #s.lines.userLineUp = 2
    #s'.lines.people = 0
    s'.capacity = 1
    #s'.lines.userLineUp = 0
    #s'.lines.nonUserLineUp = 0
    #s'.lines.visits = 0
    #s''.lines.people = 1
    s''.capacity = 1
    #s''.lines.userLineUp = 2
    s != s''
    rt.user = u
    rt.supermarket = s
    st.request = rt
    s not in st.ticketSuggestions
    all super: Supermarket | super.timetable.first.date = d
}
run suggestionToChangeSupermarket_OneSuggestion for 10 but 5 int, 10 seq

/*
** This predicate aims to show the correct answer to 
** an availability request from a user during the 
** creation of a visit (indeed that user has no active entrance). 
** We put 2 supermarkets, in which the request is made on
** the most crowded, instead the other one is way less crowded
** and it can appear in the recommendations
*/
pred suggestionToChangeSupermarket_Visit (u: User, s, s': Supermarket, ts: TimeSlot, sv: SuggestVisit, 
    rv: AvailabilityRequestVisit, d: Date) {
    #Supermarket = 2
    #s.lines.people = 1
    s.capacity = 1
    #s.lines.userLineUp = 2
    #s'.lines.people = 0
    s'.capacity = 1
    #s'.lines.userLineUp = 0
    #s'.lines.nonUserLineUp = 0
    #s'.lines.visits = 0
    rv.user = u
    rv.timeSlot = ts
    ts.supermarket = s
    sv.request = rv
    ts not in sv.visitSuggestions
    all super: Supermarket | super.timetable.first.date = d
}
run suggestionToChangeSupermarket_Visit for 7

/*
** This predicate aims to show the correct answer to 
** an availability request from a user during the creation
** of a visit (indeed that user has no active entrance). 
** We put 1 supermarkets, so that the selected slot is not 
** available and the suggested slot is another one of the 
** same supermarket, but different timing
*/
pred suggestionToChangeSlot_Visit (u: User, s: Supermarket, ts: TimeSlot, sv: SuggestVisit, 
    rv: AvailabilityRequestVisit, d: Date) {
    #User = 1
    #Ticket = 0
    #Visit = 0
    #s.timetable = 1
    #Supermarket = 1
    #s.lines.people = 0
    s.capacity = 1
    rv.user = u
    rv.timeSlot = ts
    ts.supermarket = s
    sv.request = rv
    ts not in sv.visitSuggestions
    all super: Supermarket | super.timetable.first.date = d
}
run suggestionToChangeSlot_Visit for 7

/*
** This pred wants to show the correct behaviour of 
** the answer to a request for an available supermarket
** during the process of creation of a ticket
*/
pred requestAvailabilityTicket_Available(u: User, s: Supermarket, st: SuggestTicket, 
    rt: AvailabilityRequestTicket, d: Date) {
    #User = 1
    #Supermarket = 1
    #s.lines.people = 0
    #s.lines.userLineUp = 0
    s.capacity = 1
    rt.user = u
    rt.supermarket = s
    st.request = rt
    s in st.ticketSuggestions
    #Ticket = 0
    #s.timetable = 1
    all super: Supermarket | super.timetable.first.date = d
}
run requestAvailabilityTicket_Available for 7

/*
** This pred wants to show the correct behaviour of 
** the answer to a request for an available supermarket
** during the process of book a visit
*/
pred requestAvailabilityVisit_Available(u: User, s: Supermarket, ts: TimeSlot, sv: SuggestVisit, 
    rv: AvailabilityRequestVisit, d: Date) {
    #User = 1
    #Supermarket = 1
    #s.lines.people = 0
    #s.lines.userLineUp = 0
    s.capacity = 1
    ts.supermarket = s
    rv.user = u
    rv.timeSlot = ts
    sv.request = rv
    ts in sv.visitSuggestions
    #Ticket = 0
    #s.timetable = 1
    all super: Supermarket | super.timetable.first.date = d
}
run requestAvailabilityVisit_Available for 7

/*
** predicate that verifies the correctness of 
** a very complex situation
*/
pred ExtremeModel (d: Date) {
    #User > 3
    #Supermarket > 1
    #Entrance > 6
    #Visit > 1
    #SuggestTicket > 0
    #SuggestVisit > 0
    #Notification = 1
    all s: Supermarket | s.capacity = 2
    all s: Supermarket | #s.lines.people = s.capacity
    some s: Supermarket | #s.lines.userLineUp > 0
    some s: Supermarket | #s.lines.nonUserLineUp > 0
    some s: Supermarket | #s.lines.visits > 0
    some e: Entrance | e.state = EXPIRED
    some t: Ticket | t.customer in User
    some v: Visit | v.state = VALID
    all super: Supermarket | super.timetable.first.date = d
}
run ExtremeModel for 10 but 5 int, 10 seq


/* ** ASSERTIONS ** */

/*
** This assertion wants to prove that 
** a notification cannot exist without
** some data
*/
assert allNotificationsHasData {
    all n: Notification | some v: Visit | v.customer = n.user
}
check allNotificationsHasData

/*
** This assertion wants to prove that 
** a supermarket does not contains more customers
** that its capacity
*/
assert noMoreCustomersThanCapacity {
    all s: Supermarket | s.capacity > #s.lines.people or s.capacity = #s.lines.people
}
check noMoreCustomersThanCapacity

/*
** This assertion wants to prove that every 
** supermarket has all the characteristics
** to be considered a supermarket
*/
assert everySupermarketHasAllFunctionalities {
    all m: Manager | one s: Supermarket | s.manager = m
    all tm: TicketMachine | one s: Supermarket | s.ticketMachine = tm
    all st: Statistics | one s: Supermarket | s.statistics = st
    all l: Lines | one s: Supermarket | s.lines = l
    all sp: SupermarketPosition | one s: Supermarket | s.position = sp
}
check everySupermarketHasAllFunctionalities

/*
** This assertsion wants to prove that 
** our model does not allow "ghost users",
** that are GpsPositions without an owner 
** (we cannot register GpsPositions that
** does not belong to anyone)
*/
assert noGhostUsers {
    all gps: GPSPosition | one u: User | u.position = gps
}
check noGhostUsers