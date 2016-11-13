// project PowerEnjoy
// team Erba Alessandro, Leveni Filippo, Lodi Luca
module PowerEnjoyService
open util/boolean


sig Location {} //s: Location

sig PowerenjoyUser { //s: user
	currentLocation: one Location, //f: a user have only one own position
	currentReservation: lone Reservation, //f: max 1 reservation
	currentRent: lone Rent //f: max 1 rent
}{
	currentRent != none implies currentReservation = none //f: rent --> ! reserv
	currentReservation != none implies currentRent = none //f: reservation --> ! rent
	(currentRent != none and currentRent.car.state = PickedUp) implies currentRent.car.currentLocation = currentLocation //f: During a rent, user and car are in the same position
}

sig EmergencyStaff { //s: emergency staff
	handledEmergency: lone Emergency, //f: max 1 emergency handled at the same time
	emergenciesQueue: set Emergency //f: queue of emergencies to be handled by this specific emergency staff
}{
	handledEmergency = none implies #emergenciesQueue = 0 //f: no queued emergencies if not handling one
	handledEmergency not in emergenciesQueue //f: no handled emergency in queued emergencies
}



abstract sig Emergency {//s: emergency
}

sig EmptyBattery extends Emergency { //s: empty battery emergency
	involvedCar: one Car //f: only one car belongs to an EmptyBattery emergency
}{ 
	involvedCar.batteryCharge = 0 //f: battery is empty to raise emergency
}

fact NoDoubleEmptyBattery { //f: only one BatteryEmpty emergency raise for each car that has an empty battery
	no c: Car | #~involvedCar[c] > 1
}

sig CarAccident extends Emergency { //s: car accident
	accidentCar: one Car //f: only one car belongs to a CarAccident emergency(if more than one our cars is involved in the same accident, there is a different CarAccident emergency for each car)
}

sig FieldStaff { //s: field staff
}

sig RelocationRequest { //s:relocation request
	assignedCar: one Car,	//f: a relocation request is associated to a only one car
	destination: one Location //f: is possible to relocate a car in only one position
}{
	not(assignedCar.state in (PickedUp + Reserved + OnStopover)) //f: car to be relocated have not to be picked up or reserved
	destination != assignedCar.currentLocation //f: no relocation in the same place where the car is
}

fact NoMultipleRelocationsOnSamePlace { //f: no multiple relocations on the same place
		no disjoint r1,r2:RelocationRequest | r1.assignedCar = r2.assignedCar
}

sig Car { //s: car
	currentLocation: one Location, //f: a car have only one own position
	batteryCharge : one Int, //f: a car have only one battery
	state : one CarState //f: a car have only one state
}{
	no disjoint r1,r2: Reservation | r1.targetCar = r2.targetCar //f: no multiple reservation on car
	no disjoint r1,r2: Rent | r1.car = r2.car //f: no multiple rent on car
	no r1: Reservation, r2: Rent | r1.targetCar = r2.car //f: no rent while a reservation is active on car and vice versa
	no disjoint r1,r2: RelocationRequest | r1.assignedCar = r2.assignedCar //f: no multiple relocation requests on car
	0<=batteryCharge and batteryCharge <= 4 //f: battery charge range 0 - 100: 
	/*
		0 --> 0				battery empty	battery autonomy overcharge zone
		1 --> [1,19]								battery autonomy overcharge zone
		2 --> [20,50]							neural zone
		3 --> [51,99]							battery autonomy discount zone
		4 --> [100]		battery full		battery autonomy discount zone
	*/
	state = Available implies (one s: SafeArea | this in s.parkedCars) //f: available cars must be parked in safe area
	#~accidentCar[this] > 0 implies state = Broken //f: cars with accident are not available
	batteryCharge = 0 implies state = Broken //f: cars with battery charge = 0 are considered broken
}

fact PreserveBatteryChargeInEvent { //f: the events are istantaneous, so the battery charge is the same before and after it
	all disjoint c,c': Car | event[c,c'] implies c.batteryCharge = c'.batteryCharge
}

fact NoCarsShareLocation {//f: cars don't share location
	all disjoint c1,c2: Car |
		not(
			event[c1,c2]
		)
		implies different_location[c1,c2]
}

sig Reservation { //s: reservation
	targetCar : one Car, //f: one reservation refers to only one car
}{
	one u: PowerenjoyUser | u.currentReservation = this //f: at least a user made this reservation
	targetCar.state = Reserved //f: reserved cars have according state
}

sig Passenger { //s: passenger
}{
	one r: Rent | this in r.passengers //f: one passenger belongs to exactly one rent
}

sig Rent { //s: rent
	car: one Car,	 //f: each rent has associated only one car
	passengers: set Passenger //f: each rent has associated a set of passengers, excluding the driver
}{
	one u: PowerenjoyUser | u.currentRent = this //f: is associated to only one user
	car.state in  PickedUp + OnStopover //f: target car state must be picked-up or on stopover
	#passengers >= 0 //f: passengers range 0 - 4
	#passengers <= 4
	car.batteryCharge > 0 //f: no rent of empty battery cars
}

sig MoneySavingRent extends Rent { //s: money saving rent
	inputtedDestination: one Location
}

sig Payment {  //s: payment
	paymentRent: one Rent, //f: a payment refers to only one rent
	discounts: set Discount //f: a payment can have a set of discounts to be applied
}
fact NoMultiplePaymentsPerRent { //f: each rent has at most one payment associated
	all r: Rent | #~paymentRent[r] <= 1
}

abstract sig Discount { //s: discount
}{
	some p: Payment | this in p.discounts //f: a discount is represented only if there is at least a payment with it as discount
}

lone sig PassengersDiscount extends Discount {} //s: passenger discount

lone sig FarFromPowerPlugDiscount extends Discount {} //s: far from power plug charge and battery autonomy charge

lone sig BatteryAutonomyDiscount extends Discount {} //s: battery autonomy discount

lone sig PowerPluggedDiscount extends Discount {} //s: power plugged discount

lone  sig MoneySavingDiscount extends Discount {} //s: money saving discount

abstract sig CarState { //s: car state
}{
  some c: Car | c.state = this //f: a state is represented only if there is at least a machine with it as state
}

lone sig Available extends CarState {} //s: available state

lone sig Reserved extends CarState {} //s: reserved state

lone sig PickedUp extends CarState {} //s: picked up state

lone sig  OnStopover extends CarState {} //s: on stopover state

lone sig Relocating extends CarState {} //s: relocating state

lone sig Broken extends CarState {} //s: broken state

lone sig  UnderMaintenance extends CarState {} //s: under maintenance state

lone sig Dismissed extends CarState {} //s: dismissed state

sig SafeArea { //s: safe area
	parkedCars: set Car //f: a safe area has a set of parked cars
}{
	no disjoint s1,s2: SafeArea, l: Location | Contains[s1,l] and Contains[s2,l] //f: safe area aren't overlapped
	all c: parkedCars | Contains[this, c.currentLocation] //f: all cars parked in this safe area are contained in it
}

fact PreserveParkingInEvent{
		all disjoint c,c': Car | event[c,c'] implies ~parkedCars[c] = ~parkedCars[c'] //f: since the events are istantaneous, if a car is parked in a safe area before, it is still parked in the same area after
}

sig PowerPlugSlot extends SafeArea{ //s: power plug slot
	currentLocation : one Location //f: a power plug has only one own position
}{
	no p: PowerPlugSlot | p!=this and p.currentLocation=this.currentLocation //f: power plug slots don't share location
	(no disjoint c,c': Car | event[c,c']) implies #parkedCars <= 1 //f: only one car can be parked in a power plug slot in a certain instant, with the exception of the machine involved in an event that is represented by two different cars(before and after it)
	(no disjoint c,c': Car | not(event[c,c']) and (c in parkedCars and c' in parkedCars))
	parkedCars != none implies parkedCars.currentLocation = currentLocation //f: if a car is parked in a power plug slot, they have the same position
	all disjoint c,c': Car | event[c,c'] implies (c in parkedCars <=> c' in parkedCars) //f: since the events are istantaneous, if a car is parked in a safe area before, it is still parked in the same area after 
}


pred Contains[s: SafeArea, l: Location]{ //p: contains
}

pred far_from_power_plug[c: Car]{ //p: far from power plug
}

pred different_location[c1,c2: one Car]{ //p: different location
	c1.currentLocation != c2.currentLocation //f: two cars have different location iff their locations are different
}


pred evtCarAccident[ //p: car accident
	a: one CarAccident,
	c,c': one Car, //f: car before and after the event
	e,e': one EmergencyStaff, //f: emergency staff before and after event
	]{
	c.state not in Dismissed //f: a car to be in an accident, can't be dismissed
	c' = a.accidentCar //f: the car involved in the accident is the considered car after the event
	c != c' //f: the car before and after the event is represented by two different cars
	c.currentLocation = c'.currentLocation //f: since the event is istantaneous, the car's location before and after it is the same
	c'.batteryCharge = c.batteryCharge or c'.batteryCharge = 0 //f: since the event is istantaneous, the car's battery charge before and after it is the same, or the battery is broken
	c'.state in Broken //f: the car after the accident is broken
	e.handledEmergency!=none implies (a in e'.emergenciesQueue and e.handledEmergency=e'.handledEmergency) //f: since the event is istantaneous, if an emergency staff is handling an emergency, the emergency handled before and after the event is the same
	e.handledEmergency=none implies a = e'.handledEmergency //f: if an emergency staff isn't handling an emergency, the accident is handled by him after the event
	e!=e' //f: the emergency staff before and after the event is represented by two different emergency staff
	#(~accidentCar)[c] = 0 //f: the car before the event isn't involved in any accident
	#(~accidentCar)[c'] = 1 //f: the car after the event is involved in an accident
}

pred event[c,c': one Car]{ //p: car event
	(some u,u': PowerenjoyUser | evtReservation[u,u',c,c'] or evtReservation[u,u',c',c] ) or 
	(some u,u': PowerenjoyUser, p: Payment | evtEndRent[u,u',c,c',p] or evtEndRent[u,u',c',c,p] ) or 
	(some e,e': EmergencyStaff, a: CarAccident | evtCarAccident[a,c,c',e,e'] or evtCarAccident[a,c',c,e,e'] ) //f: the only events considered for the cars are the reservation, the end of rent and the car accident
}

fact {
	all disjoint c,c': Car | event[c,c'] <=> event[c',c] //f: simmetry property of the event
}

pred event[u,u': one PowerenjoyUser]{ //p: user event
	(some c,c': Car | evtReservation[u,u',c,c'] or evtReservation[u,u',c',c] ) and
	(some c,c': Car, p: Payment | evtEndRent[u,u',c,c',p] or evtEndRent[u,u',c',c,p] ) //f: the only events considered for the users are the reservation and the end of rent
}

fact {
	all disjoint u,u': PowerenjoyUser | event[u,u'] <=> event[u',u] //f: simmetry property of the event
}

pred evtReservation[ //p: reservation
	u,u': one PowerenjoyUser, //f: power enjoy user before and after the event
	c,c': one Car //f: car before and after the event
	]{
	c.state = Available //f: car to be reserved must be available
	c'.state = Reserved //f: car after a reservation is reserved
	c.batteryCharge = c'.batteryCharge //f: since the event is istantaneous, the car's battery charge before and after it is the same
	c.currentLocation = c'.currentLocation //f: since the event is istantaneous, the car's location before and after it is the same
	u.currentLocation = u'.currentLocation //f: since the event is istantaneous, the user's location before and after it is the same
	one r: Reservation | u'.currentReservation = r and r.targetCar = c' //f: there is only one reservation with this user and this car involved
	u.currentReservation = none //f: user must not have any active reservation in order to reserve a car
	u.currentRent = none //f: user must not have any active rent in order to reserve a car
}

pred evtEndRent[ //p: end rent
	u,u': one PowerenjoyUser, //f: power enjoy user before and after the event
	c,c': one Car, //f: car before and after the event
	p: one Payment //f: payment related to the rent
	]{
	u.currentRent != none //f: the involved user must have an active rent before the event
	u.currentRent.car = c //f: the car considered is the car rented by the user
	u'.currentRent = none //f: the involved user must not have any active rent after the event
	c'.state = Available //f: the car after the event is available
	c.currentLocation = c'.currentLocation //f: since the event is istantaneous, the car's location before and after it is the same
	u.currentLocation = u'.currentLocation //f: since the event is istantaneous, the user's location before and after it is the same
	parked_in_safe_area[c] //f: car rent ends only if a car is parked in a safe area 
	parked_in_safe_area[c']  //f: since the event is istantaneous, the car is still parked in a safe area after the event
	#~paymentRent[u.currentRent] = 1 //f: the rent has associated exactly one payment
	PassengersDiscount in p.discounts <=> #u.currentRent.passengers >= 2 //f: passengers discount is earned iff the rent's passengers are at least two
	not (u.currentRent = MoneySavingRent) implies not(MoneySavingDiscount in p.discounts) //f: money saving discount can be earned only if the rent considered is a MoneySavingRent
	PowerPluggedDiscount in p.discounts <=> ~parkedCars[c] in PowerPlugSlot //f: power plugged discount is earned iff the the car considered is park in a power plug slot
	BatteryAutonomyDiscount in p.discounts 	<=> c.batteryCharge >= 3 //f: battery autonomy discount is earned iff the battery charge is over the level 3
	FarFromPowerPlugDiscount  in p.discounts <=> (c.batteryCharge <= 1) or (far_from_power_plug[c]) //f: far from power plug discount is charged iff car's battery level is lower than 1 or the car is parked far from power plug
}

pred parked_in_safe_area[c: Car]{//p: parked in a safe area
	(one s: SafeArea | c in s.parkedCars) //f: a car is parked in a safe area iff exists a safe area in which the car is parked
}


fact EmergenciesOfEmergencyStaffMustBeDisjoint { //f: emergencies of emergency staff must be disjoint, with the exception of the emergency staff involved in an event that is represented by two different emergency staff(before and after it)
		all disjoint e1,e2: EmergencyStaff |
			(no a:CarAccident,c1,c2:Car | evtCarAccident[a,c1,c2,e1,e2] or evtCarAccident[a,c2,c1,e1,e2]) implies ({e1.handledEmergency}+e1.emergenciesQueue) & ({e2.handledEmergency}+e2.emergenciesQueue) = none
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

run scenario3
