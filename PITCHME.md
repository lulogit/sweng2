#HSLIDE
# PowerEnJoy
- Erba Alessandro
- Leveni Filippo
- Lodi Luca

#HSLIDE
# PowerEnjoy:
a new car sharing

#HSLIDE
# Goals

#VSLIDE
### Business driver related goals
<li> **G.1** user's simple access to the PowerEnjoy services</li><!-- .element: class="fragment" -->
<li> **G.2** higher probability of ﬁnding a car, compared to competitors</li> <!-- .element: class="fragment" -->
<li> **G.3** eﬃcient maintenance and recharge process of the cars</li> <!-- .element: class="fragment" -->

#VSLIDE
### Car sharing related goals
<li> **G.4** car reservation, reservation cancellation</li> <!-- .element: class="fragment" -->
<li> **G.5** minimum interaction with payment interfaces </li><!-- .element: class="fragment" -->
<li> **G.6** drive cars, ﬁnd safe areas where to park </li><!-- .element: class="fragment" -->
<li> **G.7** To encourage users’ virtuous behaviour in relation to service’s fairness. </li><!-- .element: class="fragment" -->

#VSLIDE
### Process efficiency related goals
<li> **G.8** system monitorable / administrable by authorized personal </li><!-- .element: class="fragment" -->
<li> **G.9** authorized personal quickly react to emergencies, user’s safety </li><!-- .element: class="fragment" -->
<li> **G.10** programmable interface, reduce maintainance costs, third party developers. </li><!-- .element: class="fragment" -->

#HSLIDE
# Our solution

#VSLIDE
1) car distribution algorithm --> user finds car nearby -- > user satisfaction
#VSLIDE
2) car distribution algorithm --> automatic relocation request assignment --> maximum staff's efficiency
#VSLIDE
3) configurability and extensibility --> minimum maintenance cost

#HSLIDE
# Actors

#HSLIDE 
### PowerEnJoy user
![icon](presentation/powerenjoy_user.png)
#VSLIDE
**R.6** to find the locations of available cars within a certain distance from their
current location or from a specified address.
#VSLIDE
**R.7** to reserve a single car, among the available ones, provided that the user
has not ended a rent on that car within last 15 minutes.
#VSLIDE
R.8 to cancel the reservation before it's expiration (1 hour after reservation)
 paying a cost proportional to the reservation time

 the minimum amount is relative to a quarter of an hour
#VSLIDE
R.9 to be charged of a fee (1e) whether the reserved car is not picked{up
within one hour from the reservation.
 the car must be tagged as available again
 the reservation expires
#VSLIDE
R.10 to rent a car (reserved or available), specically:
 to unlock a car when it is within a certain distance (threshold) from
the car
 to enable engine by inputting a personal PIN code.
 to be charged for a given amount of money per minute as soon as the
car is unlocked.
 to be notiFIed of the current price through a screen on the car.
 to be able to lock/unlock the car, starting/finishing a stopover (with
different fare)
 to stop being charged as soon as the car is parked in a safe area, he
exits the car (that is automatically locked) and select to end the rent.
 to transparently pay for the rent 5 minutes after its termination,
being notified of the final price (including discounts).
#VSLIDE
R.11 to be excluded from the fruition of PowerEnjoy services whether the
payment is unable to complete, until all pending payment are performed.
#VSLIDE
R.12 to be applied a discount of 10% on the last ride, whether it brings at
least two other passengers onto the car (the discount is applied for the
actual time the car was transporting at least 2 passengers).
#VSLIDE
R.13 to be applied a discount of 20% on the last ride, whether the car is left
with more than 50% of the battery's charge.
#VSLIDE
R.14 to be applied a discount of 30% on the last ride, whether it takes care
of plugging-in the car to the power plug .
#VSLIDE
R.15 to be applied an overcharge of 30% on the last ride, whether the car
is left farer than 3 KM from the nearest charge station or with less than
20% of the battery's charge.
#VSLIDE
R.16 to enable the money saving option in order to minimize the total cost
of a rent regarding to the destination, specically:
 to input a destination
 to be shown suggestions about where to park the car (within 1km
from entered destination) in order to get discounts described above
 to be applied an additional discount whether the rent is terminated in
the suggested location, calculated by BPM with respect to secondary
business goals.
#VSLIDE
R.17 to be notified of changes in the service policies
 different fares
 updated terms of service
#HSLIDE
### Field staff users
![icon](presentation/field_staff.png)
#VSLIDE
R.18 to be notified of relocation/maintenance requests for cars (and the can-
cellation / modification of an assigned request)
#VSLIDE
R.19 to relocate an assigned car:
 locate assigned car
 unlock assigned car
 check diagnostic of assigned car
 power on assigned car
 enable / disable power plugs
 lock assigned car
 locate maintenance facility
#VSLIDE
R.20 to ask for special equipment (e.g: tow truck) or additional eld sta
help after evaluating the situation.
#HSLIDE 
### Management staff users
![icon](presentation/management_staff.png)
#VSLIDE
R.21 to configure the list of available safe areas and power plugs over the
service covered area.
#VSLIDE
R.22 to cofigure the list of cars available for the service
#VSLIDE
R.23 to configure service policies:
 update existing service's fares
 introducing new service's fares
 update discounts
 introducing new discounts
 update the terms of the service
#VSLIDE
R.24 to manage personnel's accounts:
 create
 delete
 modify
for:
 field staff user
 emergency staff user
 management staff user
#VSLIDE
R.25 to handle exceptional cases of unpaid rents:
 check pending payment status.
 re-enable PowerEnjoy users to the service.
#HSLIDE
Requirements
#VSLIDE
### Emergency staff user
![icon](presentation/emergency_staff.png)
#VSLIDE
R.26 to be promptly notied of potentially dangerous situations / emergen-
cies:
 cars malfunctioning during a rent
 car accidents
 cars with empty battery not parked in safe areas
#VSLIDE
R.27 to be promptly notied of PowerEnjoy users' help request.
#VSLIDE
R.28 to have an overview regarding the state and location of:
 cars
 power plugs
 current rents
 reservation
 field staff users
#VSLIDE
R.29 to perform actions to resolve issue:
 cancel a PowerEnjoy user's reservation
 recover a PowerEnjoy user's pin code
 unlock / lock rented car
 set a car as available / unavailable
 speak with user on rented cars through installed hands-free commu-
nication set
 assign a field staff user to relocate a car with priority
 notify appropriate authorities of a car accident (first-aid, re-ghters,
police, insurance company ...)

#HSLIDE
# BPM
### Back-end Process Management

#VSLIDE 
# Relocations

#VSLIDE
# Money saving option

#HSLIDE
# Hardware

#VSLIDE
### Cars

#VSLIDE
### Smart devices

#HSLIDE
# Scenarios

#VSLIDE
### smart device interface

#VSLIDE
### car screen interface

#HSLIDE
# Use cases

#HSLIDE
# UML

#VSLIDE
### UML

#VSLIDE
### UML

#VSLIDE
### UML

#HSLIDE
# Alloy

#VSLIDE
### screen1
#VSLIDE
### screen2
#VSLIDE
### screen3
