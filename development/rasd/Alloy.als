// project PowerEnjoy
// team Erba Alessandro, Leveni Filippo, Lodi Luca
module PowerEnjoyService
open util/boolean


sig Location {} //  Location

sig PowerenjoyUser { //  user
	currentLocation: one Location, //  a user have only one own position
	currentReservation: lone Reservation, //  max 1 reservation
	currentRent: lone Rent //  max 1 rent
}{
	currentRent != none implies currentReservation = none //  rent --> ! reserv
	currentReservation != none implies currentRent = none //  reservation --> ! rent
	(currentRent != none and currentRent.car.state = PickedUp) implies currentRent.car.currentLocation = currentLocation //  During a rent, user and car are in the same position
}

sig EmergencyStaff { //  emergency staff
	emergenciesQueue: set Emergency //  queue of emergencies to be handled by this specific emergency staff
}

abstract sig Emergency {//  emergency
}

sig EmptyBattery extends Emergency { //  empty battery emergency
	involvedCar: one Car //  only one car belongs to an EmptyBattery emergency
}{
	involvedCar.batteryCharge = 0 //  battery is empty to raise emergency
}

fact NoDoubleEmptyBattery { //  only one BatteryEmpty emergency raise for each car that has an empty battery
	no c: Car | #~involvedCar[c] > 1
}

sig CarAccident extends Emergency { //  car accident
	accidentCar: one Car //  only one car belongs to a CarAccident emergency(if more than one our cars is involved in the same accident, there is a different CarAccident emergency for each car)
}

sig FieldStaff { //  field staff
}

sig RelocationRequest { // relocation request
	assignedCar: one Car,	//  a relocation request is associated to a only one car
	destination: one Location //  is possible to relocate a car in only one position
}{
	not(assignedCar.state in (PickedUp + Reserved + OnStopover)) //  car to be relocated have not to be picked up or reserved
	destination != assignedCar.currentLocation //  no relocation in the same place where the car is
	assignedCar.state != Broken //  no relocation of broken cars
}

fact NoMultipleRelocationsOnSamePlace { //  no multiple relocations on the same place
		no disjoint r1,r2:RelocationRequest | r1.assignedCar = r2.assignedCar
}

sig Car { //  car
	currentLocation: one Location, //  a car have only one own position
	batteryCharge : one Int, //  a car have only one battery
	state : one CarState //  a car have only one state
}{
	no disjoint r1,r2: Reservation | r1.targetCar = r2.targetCar //  no multiple reservation on car
	no disjoint r1,r2: Rent | r1.car = r2.car //  no multiple rent on car
	no r1: Reservation, r2: Rent | r1.targetCar = r2.car //  no rent while a reservation is active on car and vice versa
	no disjoint r1,r2: RelocationRequest | r1.assignedCar = r2.assignedCar //  no multiple relocation requests on car
	0<=batteryCharge and batteryCharge <= 4 //  battery charge range 0 - 100:
	/*
		0 --> 0				battery empty	battery autonomy overcharge zone
		1 --> [1,19]								battery autonomy overcharge zone
		2 --> [20,50]							neural zone
		3 --> [51,99]							battery autonomy discount zone
		4 --> [100]		battery full		battery autonomy discount zone
	*/
	state = Available implies (one s: SafeArea | this in s.parkedCars) //  available cars must be parked in safe area
	#~accidentCar[this] > 0 implies state = Broken //  cars with accident are not available
	batteryCharge = 0 implies state = Broken //  cars with battery charge = 0 are considered broken
	state in  PickedUp + OnStopover implies (one r:Rent | r.car = this)
}

fact PreserveBatteryChargeInEvent { //  the events are istantaneous, so the battery charge is the same before and after it
	all disjoint c,c': Car | event[c,c'] implies c.batteryCharge = c'.batteryCharge
}

fact NoCarsShareLocation {//  cars don't share location
	all disjoint c1,c2: Car |
		not(
			event[c1,c2]
		)
		implies different_location[c1,c2]
}

sig Reservation { //  reservation
	targetCar : one Car, //  one reservation refers to only one car
}{
	one u: PowerenjoyUser | u.currentReservation = this //  at least a user made this reservation
	targetCar.state = Reserved //  reserved cars have according state
}

sig Passenger { //  passenger
}{
	one r: Rent | this in r.passengers //  one passenger belongs to exactly one rent
}

sig Rent { //  rent
	car: one Car,	 //  each rent has associated only one car
	passengers: set Passenger //  each rent has associated a set of passengers, excluding the driver
}{
	one u: PowerenjoyUser | u.currentRent = this //  is associated to only one user
	car.state in  PickedUp + OnStopover //  target car state must be picked-up or on stopover
	#passengers >= 0 //  passengers range 0 - 4
	#passengers <= 4
	car.batteryCharge > 0 //  no rent of empty battery cars
}

sig MoneySavingRent extends Rent { //  money saving rent
	inputtedDestination: one Location
}

sig Payment {  //  payment
	paymentRent: one Rent, //  a payment refers to only one rent
	discounts: set Discount //  a payment can have a set of discounts to be applied
}
fact NoMultiplePaymentsPerRent { //  each rent has at most one payment associated
	all r: Rent | #~paymentRent[r] <= 1
}

abstract sig Discount { //  discount
}{
	some p: Payment | this in p.discounts //  a discount is represented only if there is at least a payment with it as discount
}

lone sig PassengersDiscount extends Discount {} //  passenger discount

lone sig FarFromPowerPlugDiscount extends Discount {} //  far from power plug charge and battery autonomy charge

lone sig BatteryAutonomyDiscount extends Discount {} //  battery autonomy discount

lone sig PowerPluggedDiscount extends Discount {} //  power plugged discount

lone  sig MoneySavingDiscount extends Discount {} //  money saving discount

abstract sig CarState { //  car state
}{
  some c: Car | c.state = this //  a state is represented only if there is at least a machine with it as state
}

lone sig Available extends CarState {} //  available state

lone sig Reserved extends CarState {} //  reserved state

lone sig PickedUp extends CarState {} //  picked up state

lone sig  OnStopover extends CarState {} //  on stopover state

lone sig Relocating extends CarState {} //  relocating state

lone sig Broken extends CarState {} //  broken state

lone sig  UnderMaintenance extends CarState {} //  under maintenance state

lone sig Dismissed extends CarState {} //  dismissed state

sig SafeArea { //  safe area
	parkedCars: set Car //  a safe area has a set of parked cars
}{
	no disjoint s1,s2: SafeArea, l: Location | Contains[s1,l] and Contains[s2,l] //  safe area aren't overlapped
	all c: parkedCars | Contains[this, c.currentLocation] //  all cars parked in this safe area are contained in it
}

fact PreserveParkingInEvent{
		all disjoint c,c': Car | event[c,c'] implies ~parkedCars[c] = ~parkedCars[c'] //  since the events are istantaneous, if a car is parked in a safe area before, it is still parked in the same area after
}

sig PowerPlugSlot extends SafeArea{ //  power plug slot
	currentLocation : one Location //  a power plug has only one own position
}{
	no p: PowerPlugSlot | p!=this and p.currentLocation=this.currentLocation //  power plug slots don't share location
	(no disjoint c,c': Car | event[c,c']) implies #parkedCars <= 1 //  only one car can be parked in a power plug slot in a certain instant, with the exception of the machine involved in an event that is represented by two different cars(before and after it)
	(no disjoint c,c': Car | not(event[c,c']) and (c in parkedCars and c' in parkedCars))
	parkedCars != none implies parkedCars.currentLocation = currentLocation //  if a car is parked in a power plug slot, they have the same position
	all disjoint c,c': Car | event[c,c'] implies (c in parkedCars <=> c' in parkedCars) //  since the events are istantaneous, if a car is parked in a safe area before, it is still parked in the same area after
}


pred Contains[s: SafeArea, l: Location]{ //  contains
}

pred far_from_power_plug[c: Car]{ //  far from power plug

}

pred different_location[c1,c2: one Car]{ //  different location
	c1.currentLocation != c2.currentLocation //  two cars have different location iff their locations are different
}


pred evtCarAccident[ //  car accident
	a: one CarAccident,
	c,c': one Car, //  car before and after the event
	e,e': one EmergencyStaff, //  emergency staff before and after event
	]{
	c.state not in Dismissed //  a car to be in an accident, can't be dismissed
	c' = a.accidentCar //  the car involved in the accident is the considered car after the event
	c != c' //  the car before and after the event is represented by two different cars
	c.currentLocation = c'.currentLocation //  since the event is istantaneous, the car's location before and after it is the same
	c'.batteryCharge = c.batteryCharge or c'.batteryCharge = 0 //  since the event is istantaneous, the car's battery charge before and after it is the same, or the battery is broken
	c'.state in Broken //  the car after the accident is broken
	a in e'.emergenciesQueue //  add car accident to emergency queue
	a not in e.emergenciesQueue //  accident was not in queue
	(e.emergenciesQueue & e'.emergenciesQueue = e.emergenciesQueue) //  preserve emergency queue
	e!=e' //  the emergency staff before and after the event is represented by two different emergency staff
	#(~accidentCar)[c] = 0 //  the car before the event isn't involved in any accident
	#(~accidentCar)[c'] = 1 //  the car after the event is involved in an accident
	(~car[c] != none) implies (one p: Payment | p.paymentRent = ~car[c] and compute_discounts[p.paymentRent,p]) //  all car in accident must pay the current rent

}

pred event[c,c': one Car]{ //  car event
	(some u,u': PowerenjoyUser | evtReservation[u,u',c,c'] or evtReservation[u,u',c',c] ) or
	(some u,u': PowerenjoyUser, p: Payment | evtEndRent[u,u',c,c',p] or evtEndRent[u,u',c',c,p] ) or
	(some e,e': EmergencyStaff, a: CarAccident | evtCarAccident[a,c,c',e,e'] or evtCarAccident[a,c',c,e,e'] ) //  the only events considered for the cars are the reservation, the end of rent and the car accident
}

fact {
	all disjoint c,c': Car | event[c,c'] <=> event[c',c] //  simmetry property of the event
}

pred event[u,u': one PowerenjoyUser]{ //  user event
	(some c,c': Car | evtReservation[u,u',c,c'] or evtReservation[u,u',c',c] ) and
	(some c,c': Car, p: Payment | evtEndRent[u,u',c,c',p] or evtEndRent[u,u',c',c,p] ) //  the only events considered for the users are the reservation and the end of rent
}

fact {
	all disjoint u,u': PowerenjoyUser | event[u,u'] <=> event[u',u] //  simmetry property of the event
}

pred evtReservation[ //  reservation
	u,u': one PowerenjoyUser, //  power enjoy user before and after the event
	c,c': one Car //  car before and after the event
	]{
	c.state = Available //  car to be reserved must be available
	c'.state = Reserved //  car after a reservation is reserved
	c.batteryCharge = c'.batteryCharge //  since the event is istantaneous, the car's battery charge before and after it is the same
	c.currentLocation = c'.currentLocation //  since the event is istantaneous, the car's location before and after it is the same
	u.currentLocation = u'.currentLocation //  since the event is istantaneous, the user's location before and after it is the same
	one r: Reservation | u'.currentReservation = r and r.targetCar = c' //  there is only one reservation with this user and this car involved
	u.currentReservation = none //  user must not have any active reservation in order to reserve a car
	u.currentRent = none //  user must not have any active rent in order to reserve a car
}

pred evtEndRent[ //  end rent
	u,u': one PowerenjoyUser, //  power enjoy user before and after the event
	c,c': one Car, //  car before and after the event
	p: one Payment //  payment related to the rent
	]{
	(no p': Payment | p!=p') //  no payments unrelated to event
	u.currentRent != none //  the involved user must have an active rent before the event
	u.currentRent.car = c //  the car considered is the car rented by the user
	u'.currentRent = none //  the involved user must not have any active rent after the event
	c'.state = Available //  the car after the event is available
	c.currentLocation = c'.currentLocation //  since the event is istantaneous, the car's location before and after it is the same
	u.currentLocation = u'.currentLocation //  since the event is istantaneous, the user's location before and after it is the same
	parked_in_safe_area[c] //  car rent ends only if a car is parked in a safe area
	parked_in_safe_area[c']  //  since the event is istantaneous, the car is still parked in a safe area after the event
	#~paymentRent[u.currentRent] = 1 //  the rent has associated exactly one payment
	compute_discounts[u.currentRent, p]
}

pred compute_discounts[r: Rent, p: Payment]{
	(one d:PassengersDiscount | d in p.discounts) <=> #r.passengers >= 2 //  passengers discount is earned iff the rent's passengers are at least two
	not(r in MoneySavingRent) implies not(MoneySavingDiscount in p.discounts) //  money saving discount can be earned only if the rent considered is a MoneySavingRent
	(one d:MoneySavingDiscount | d in p.discounts) <=> (r.inputtedDestination = r.car.currentLocation and r in MoneySavingRent)
	(one d:PowerPluggedDiscount | d in p.discounts) <=> ~parkedCars[r.car] in PowerPlugSlot //  power plugged discount is earned iff the the car considered is park in a power plug slot
	(one d:BatteryAutonomyDiscount | d in p.discounts) 	<=> r.car.batteryCharge >= 3 //  battery autonomy discount is earned iff the battery charge is over the level 3
	(one d:FarFromPowerPlugDiscount | d in p.discounts) <=> (r.car.batteryCharge <= 1) or (far_from_power_plug[r.car]) //  far from power plug discount is charged iff car's battery level is lower than 1 or the car is parked far from power plug
}

pred parked_in_safe_area[c: Car]{//  parked in a safe area
	(one s: SafeArea | c in s.parkedCars) //  a car is parked in a safe area iff exists a safe area in which the car is parked
}


fact EmergenciesOfEmergencyStaffMustBeDisjoint { //  emergencies of emergency staff must be disjoint, with the exception of the emergency staff involved in an event that is represented by two different emergency staff(before and after it)
		all disjoint e1,e2: EmergencyStaff |
			(no a:CarAccident,c1,c2:Car | evtCarAccident[a,c1,c2,e1,e2] or evtCarAccident[a,c2,c1,e1,e2]) implies (e1.emergenciesQueue) & (e2.emergenciesQueue) = none
}

pred scenario1[
	a: one CarAccident,
	c,c': one Car,
	e,e': one EmergencyStaff,
	] {
	evtCarAccident[a,c,c',e,e'] and #c.(~car)>0 and
	(no c'': Car | c'' != c and c'' != c' and (event[c'',c'] or event[c, c'']) )
}

pred scenario2[
	u,u': one PowerenjoyUser,
	c,c': one Car
	] {
	evtReservation[u,u',c,c'] and
	(no c'': Car | c'' != c and c'' != c' and (event[c'',c'] or event[c, c'']) )
}

pred scenario3[
		u,u':PowerenjoyUser,
		c,c': Car,
		p: Payment
	]{
	evtEndRent[u,u',c,c',p] and
	(no c'': Car | c'' != c and c'' != c' and (event[c'',c'] or event[c, c'']) )
}

run scenario1
//run scenario2
//run scenario3
