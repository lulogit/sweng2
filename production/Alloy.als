// project PowerEnjoy
// team Erba Alessandro, Leveni Filippo, Lodi Luca

// basic atoms are Locations and Addresses (which map to a location)
sig Location {} //s: Location

/* sig Address {
	relatedLocation: one Location
} */

// both Users and Cars have a current location:
// cars cannot share Locations
sig PowerenjoyUser { //s: user
	currentLocation: one Location,
	currentReservation: lone Reservation, //f: max 1 reservation
	currentRent: lone Rent //f: max 1 rent
}{
	currentRent != none implies currentReservation = none //f: rent --> ! reserv
	currentReservation != none implies currentRent = none //f: reservation --> ! rent
	(currentRent != none and currentRent.car.state = PickedUp) implies currentRent.car.currentLocation = currentLocation
}

sig EmergencyStaff {
	handledEmergency: lone Emergency,
	emergenciesQueue: set Emergency
}{ //s: emergency staff
	handledEmergency = none implies #emergenciesQueue = 0 //f: no queued em. if not handling one
	handledEmergency not in emergenciesQueue //f: no handled emergency in queued emergencies
}



abstract sig Emergency {}

sig EmptyBattery extends Emergency {
	involvedCar: one Car
}{ //s: empty battery emergency
	involvedCar.batteryCharge = 0 //f: battery is empty to raise emergency
}
fact NoDoubleEmptyBattery {
	no c: Car | #~involvedCar[c] > 1
}

sig CarAccident extends Emergency {
	accidentCar: one Car
}{ //s: car accident
}

sig FieldStaff {

	}{ //s: field staff

	}

sig RelocationRequest {
	assignedCar: one Car,
	destination: one Location
}{ //s:relocation request
	not(assignedCar.state in (PickedUp + Reserved + OnStopover)) //f: car to be relocated have not to be picked up or reserved
	destination != assignedCar.currentLocation //f: no relocate same place
}

fact NoMultipleRelocationsOnSamePlace { //f: NoMultipleRelocationsOnSamePlace
		no disjoint r1,r2:RelocationRequest | r1.assignedCar = r2.assignedCar
}

sig Car {
	currentLocation: one Location,
	batteryCharge : one Int,
	state : one CarState
}{ //s: car
	no disjoint r1,r2: Reservation | r1.targetCar = r2.targetCar //f: no multiple reservation on car

	no disjoint r1,r2: Rent | r1.car = r2.car //f: no multiple rent on car

	no r1: Reservation, r2: Rent | r1.targetCar = r2.car //f: no rent while reservation on car

	no disjoint r1,r2: RelocationRequest | r1.assignedCar = r2.assignedCar //f: no multiple relocation requests on car

	0<=batteryCharge and batteryCharge <= 4 //f: battery charge range 0 - 100: 
	/*
		0 --> 0
		1 --> [1,19]
		2 --> [20,50]
		3 --> [51,99]
		4 --> [100]
	*/

	state = Available implies (one s: SafeArea | this in s.parkedCars) //f: available cars must be parked in safe area

	#~accidentCar[this] > 0 implies state = Broken //f: cars with accident are not available

	batteryCharge = 0 implies state = Broken 
}
fact PreserveBatteryChargeInEvent {
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
	targetCar : one Car, //f: one cannot reserve more cars
	//expiryTime : one Int
}{
	one u: PowerenjoyUser | u.currentReservation = this //f: at least a user made this reservation
	targetCar.state = Reserved //f: reserved cars have according state
}

sig Passenger {
}{ //s: passenger
	one r: Rent | this in r.passengers //f: belong to at least one rent
}


sig Rent { //s: rent
	car: one Car,
	passengers: set Passenger
}{
	one u: PowerenjoyUser | u.currentRent = this //f: is associated to only one user
	car.state in  PickedUp + OnStopover //f: target car state must be picked-up
	#passengers >= 0 //f: passengers range 0 - car.maxpassengers
	#passengers <= 4
	car.batteryCharge > 0 //f: no rent of empty battery cars
}

sig MoneySavingRent extends Rent { //s: money saving rent
	inputtedDestination: one Location
}

sig Payment {  //s: payment
	paymentRent: one Rent,
	discounts: set Discount
}
fact NoMultiplePaymentsPerRent {
	all r: Rent | #~paymentRent[r] <= 1 
}

abstract sig Discount { //s: discount
}{
	some p: Payment | this in p.discounts //f: must be associated to a payment
}

lone sig PassengersDiscount extends Discount {} //s: discount

lone sig FarFromPowerPlugDiscount extends Discount {} //s: discount

lone sig BatteryAutonomyDiscount extends Discount {} //s: discount

lone sig PowerPluggedDiscount extends Discount {} //s: discount

lone  sig MoneySavingDiscount extends Discount {}

abstract sig CarState {
}{
  some c: Car | c.state = this
}

lone sig Available extends CarState {}

lone sig Reserved extends CarState {}

lone sig PickedUp extends CarState {}

lone sig  OnStopover extends CarState {}

lone sig Relocating extends CarState {}

lone sig Broken extends CarState {}

lone sig  UnderMaintenance extends CarState {}

lone sig Dismissed extends CarState {}

sig SafeArea {
	parkedCars: set Car
}{
	no disjoint s1,s2: SafeArea, l: Location | Contains[s1,l] and Contains[s2,l]
	all c: parkedCars | Contains[this, c.currentLocation]
}

fact PreserveParkingInEvent{
		all disjoint c,c': Car | event[c,c'] implies ~parkedCars[c] = ~parkedCars[c']
}

sig PowerPlugSlot extends SafeArea{
	currentLocation : one Location
}{
	no p: PowerPlugSlot | p!=this and p.currentLocation=this.currentLocation
	(no disjoint c,c': Car | event[c,c']) implies #parkedCars <= 1
	(no disjoint c,c': Car | not(event[c,c']) and (c in parkedCars and c' in parkedCars))
	parkedCars != none implies parkedCars.currentLocation = currentLocation
	all disjoint c,c': Car | event[c,c'] implies (c in parkedCars <=> c' in parkedCars) 
}


pred SuggestedDestination[r: MoneySavingRent, d: Location]{}

pred Contains[s: SafeArea, l: Location]{
	
}

pred IsPlugged[p: PowerPlugSlot, c: Car]{}

pred far_from_power_plug[c: Car]{
   
}

pred different_location[c1,c2: one Car]{
	c1.currentLocation != c2.currentLocation
}

pred evtCarAccident[
	a: one CarAccident,
	c,c': one Car,
	e,e': one EmergencyStaff,
	]{
	c.state not in Dismissed
	c' = a.accidentCar
	c != c'
	c.currentLocation = c'.currentLocation
	c'.batteryCharge = c.batteryCharge or c'.batteryCharge = 0
	c'.state in Broken
	e.handledEmergency!=none implies (a in e'.emergenciesQueue and e.handledEmergency=e'.handledEmergency)
	e.handledEmergency=none implies a = e'.handledEmergency
	e!=e'
	//#(~accidentCar)[c'] = #(~accidentCar)[c] + 1
	#(~accidentCar)[c] = 0
	#(~accidentCar)[c'] = 1
}

pred event[c,c': one Car]{
	(some u,u': PowerenjoyUser | evtReservation[u,u',c,c'] or evtReservation[u,u',c',c] ) or 
	(some u,u': PowerenjoyUser, p: Payment | evtEndRent[u,u',c,c',p] or evtEndRent[u,u',c',c,p] ) or 
	(some e,e': EmergencyStaff, a: CarAccident | evtCarAccident[a,c,c',e,e'] or evtCarAccident[a,c',c,e,e'] )
}
fact {
	all disjoint c,c': Car | event[c,c'] <=> event[c',c]
}

pred event[u,u': one PowerenjoyUser]{
	(some c,c': Car | evtReservation[u,u',c,c'] or evtReservation[u,u',c',c] ) and
	(some c,c': Car, p: Payment | evtEndRent[u,u',c,c',p] or evtEndRent[u,u',c',c,p] ) 
}
fact {
	all disjoint u,u': PowerenjoyUser | event[u,u'] <=> event[u',u]
}

pred evtReservation[
	u,u': one PowerenjoyUser,
	c,c': one Car
	]{
	c.state = Available
	c'.state = Reserved 	

	c.batteryCharge = c'.batteryCharge
	c.currentLocation = c'.currentLocation
	u.currentLocation = u'.currentLocation

	one r: Reservation | u'.currentReservation = r and r.targetCar = c'
	u.currentReservation = none
	u.currentRent = none
}

pred evtEndRent[u,u': one PowerenjoyUser, c,c': one Car, p: one Payment] {
	u.currentRent != none
	u.currentRent.car = c
	u'.currentRent = none
	c'.state = Available
	c.currentLocation = c'.currentLocation
	u.currentLocation = u'.currentLocation
	parked_in_safe_area[c]
	parked_in_safe_area[c']
	#~paymentRent[u.currentRent] = 1
	PassengersDiscount in p.discounts <=> #u.currentRent.passengers >= 2
	not (u.currentRent = MoneySavingRent) implies not(MoneySavingDiscount in p.discounts)
	PowerPluggedDiscount in p.discounts <=> ~parkedCars[c] in PowerPlugSlot
	BatteryAutonomyDiscount in p.discounts 	<=> c.batteryCharge >= 3
	FarFromPowerPlugDiscount  in p.discounts <=> (c.batteryCharge <= 1) or (far_from_power_plug[c])
}
pred parked_in_safe_area[c: Car]{
	(one s: SafeArea | c in s.parkedCars)
}



fact EmergenciesOfEmergencyStaffMustBeDisjoint { //f: EmergenciesOfEmergencyStaffMustBeDisjoint
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
