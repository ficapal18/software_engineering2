open util/boolean
open util/integer

//DATA TYPES
sig Strings{}
sig Date{}

	

//SIGNATURES
sig User{
	id: one Int,
}

sig NonRegisteredUser extends User{
	lastConnection : lone Date,
}

sig GPSPosition{
	latitude : one Strings,
	longitude : one Strings,
}

sig PaymentDetails{
	cardNumber : one Strings,
	cardSecurityCode : one Strings,
	expirationDate : one Date,
	client : one Client,
}

sig DrivingLicense{
	licenseNumber : one Strings,
	expirationDate : one Date,
	client : one Client,
}

sig Client extends User{
	name : one Strings,
	surname : one Strings,
	birthday : one Date,
	password : one Strings,
	lastKnownPosition : one GPSPosition,
	drivingLicense : one DrivingLicense,
	paymentDetails : one PaymentDetails,
}

sig Billing{
	amount : one Strings,
	service : one Service,
}

abstract sig Service{
	serviceId : one Int,
	client : one Client,
	car : one Car,
	status : one ServiceStatus,
}

sig Ride extends Service{
	duration : one Int,
	booking : one Booking,
	modifiers : set PriceModifier,
}

sig Booking extends Service{
	expirationDate : one Date,
	ride : lone Ride,
}

enum ServiceStatus { 
	ACTIVE,
	CANCELLED,
	CLOSED
}

abstract sig PriceModifier{
	percentage : one Int,
}
{
	percentage > 0
	percentage <= 100
}

abstract sig Discount extends PriceModifier{
}

abstract sig ExtraCharge extends PriceModifier{
}

sig batteryLevelDiscount extends Discount{
}{
	percentage = 20
}

sig carSharingDiscount extends Discount{
}{
	percentage = 10
}

sig plugDiscount extends Discount{
}{
	percentage = 30
}

sig noPlugsExtraCharge extends ExtraCharge{
}{
	percentage = 30
}

sig lowBatteryExtraCharge extends ExtraCharge{
}{
	percentage = 30
}

sig Car{
	plate : one Strings,
	occupiedSeats : one Int,
	engineStarted : one Bool,
	plugged : one Bool,
	position : one GPSPosition,
	battery : one BatteryLevel,
	status : one CarStatus,
}

sig BatteryLevel{
	percentage : one Int,
}
{
	percentage > 0
	percentage <= 100
}

enum CarStatus{
	AVAILABLE,
	BOOKED,
	RENT
}

sig Area{
	borders : set GPSPosition,
}
{
	#borders >= 3
}

sig SafeArea extends Area{
}

sig RechargeSite extends SafeArea{
}


//FACTS 

//Defines the != for GPSPosition
fact DifferentGPS{
	all g1, g2 : GPSPosition | g1 != g2 implies
	(g1.latitude != g2.latitude || g1.longitude != g2.longitude)
}

//Defines the != for Car
fact DifferentCar{
	all c1,c2 : Car | c1 != c2 implies c1.plate != c2.plate
}

//Defines the rules to associate a billing to a service
fact ServicesBillingLogic{
	all s : Booking | s.status = CLOSED 
		implies ((one b : Billing | b.service = s && (no r :Ride | s.ride = r))
			|| (no b:Billing | b.service = s && (one r :Ride | s.ride = r)))
	all s : Ride | s.status = CLOSED 
		implies (one b : Billing | b.service = s)
}

//No more than one billing per service
fact OneBillPerS{
	all b : Billing | (lone s : Service | b.service = s)
}

//Defines the != for User
fact DifferentUser{
	all u1,u2 : User | u1 != u2 implies u1.id != u2.id
}

//The car of an active booking must be booked
fact IfCarInActiveBookingThenBooked{
	all b : Booking | b.status = ACTIVE 
		implies b.car.status = BOOKED
}

//Removes the possibility to have a Cancelled status for a ride
fact RideCannotBeCancelled{
	all r : Ride | r.status != CANCELLED
}

//Different payment details are associated to different clients
fact DifferentPayment{
	all c1,c2 : Client | c1 != c2 
		iff c1.paymentDetails != c2.paymentDetails
}

//Defines the != for PaymentDetails
fact DIfferentPaymentDetails{
	all p1,p2 : PaymentDetails | p1 != p2 
		implies p1.cardNumber != p2.cardNumber
}

//No modifiers existing without a ride
fact OneRidePerDiscount{
 	all pm:PriceModifier | ( some r: Ride | pm in r.modifiers)

}

//Each client has a GPSPosition
fact OneGPSPerClient{
 	all c: Client | (one g: GPSPosition  | c.lastKnownPosition =g) 
}

//Defines the 1:1 association between clients and driving licenses
fact DrivingLicenseClient{
	 drivingLicense =~ client
}

//Establishes that all discounts are applied at the end of the ride
fact NoDiscountsOrExtraChargeDuringRide{
	all r : Ride | r.status = ACTIVE 
		implies (no p : PriceModifier | p in r.modifiers)
}

//The only bookings associated with billings are the one without a ride
fact payOnlyWastedBooking{
	all b : Booking | (b.status = CLOSED 
		&& (one bill : Billing | bill.service = b)) 
			implies (no r : Ride | b.ride = r)
	all b : Booking | ((b.status = CLOSED 
		&&  (no r : Ride | b.ride = r))
			implies (one bill : Billing | bill.service = b))
}

//Defines the 1:1 association between clients and payment details
fact PaymentClient{
	paymentDetails =~ client
}

//Active services can not share neither the client nor the car
fact ServicePerCarAndClient{
	all s1,s2 : Service | 
		(s1 != s2 && s1.status = ACTIVE && s2.status = ACTIVE) 
			implies (s1.client != s2.client && s1.car != s2.car)
}

//Each service is associated to a client
fact OneClientPerService{
 	all s: Service | (one c: Client  | s.client=c) 
}

//Each billing is associated to one service
fact OneServicePerBilling{
 	all b: Billing | (one s: Service  | b.service=s) 
}

//Established the possible relations between booking and ride
fact BookingRide{
	all r : Ride | one b : Booking | r.booking = b
	some b : Booking | one r : Ride | b.ride = r
	all r : Ride | r.booking.ride = r
	some b : Booking | no r : Ride | b.ride = r
}

//The billing is applied only on closed services
fact billingOnlyForClosedServices{
	all b : Billing | b.service.status = CLOSED
}

//If the billing is associated to a booking, than the booking has no ride
fact billingOnlyBookingsClosedWithNoRide{
	all b : Booking |
		(b.status = CLOSED  && (no r : Ride | b.ride = r)) 
			iff ( one bill : Billing | bill.service = b )
}

//The ride of a booking share the same client and car
fact BookandRideConsistency{
	all r:Ride | (r.booking.car=r.car && r.booking.client=r.client)
}

//The booking of a ride must always be closed
fact RideMeansBookingClosed{
	all r : Ride | r.booking.status = CLOSED
}

//No double bookings for the same ride
fact bookingRideAssociation{
	all b : Booking | #b.ride = 1 implies b.ride.booking = b
	all r : Ride | r.booking.ride = r
}

//The car status of a car of an active riding is RENT
fact RidingCarMeansCarInRent{
	all r : Ride | r.status = ACTIVE 
		implies r.car.status = RENT
}

//Defines the != for Service
fact DifferentService{
	all s1,s2 : Service | s1 != s2 
		implies (s1.serviceId != s2.serviceId)
}

//For every car in RENT exists a ride
fact ifCarInRentThenExistsRide{
	all c : Car | c.status = RENT 
		implies (one r : Ride | (r.car = c && r.status = ACTIVE))
}

//For every car BOOKED exists a booking
fact ifCarBookedThenExistsBooking{
	all c : Car | c.status = BOOKED 
		implies (one b : Booking | (b.car = c && b.status = ACTIVE))
}

//Is not possible to take 2 times the same modifier
fact NonRepeatablePriceMod{
	all r : Ride,b,c : batteryLevelDiscount | (b in r.modifiers) implies
	 !(c in r.modifiers && c != b)
	
	all r : Ride,b,c : carSharingDiscount | (b in r.modifiers) implies
	 !(c in r.modifiers && c != b)
	
	all r : Ride,b,c : plugDiscount | (b in r.modifiers) implies
	 !(c in r.modifiers && c != b)

	all r : Ride,b,c : noPlugsExtraCharge | (b in r.modifiers) implies
	 !(c in r.modifiers && c != b)

	all r : Ride,b,c : lowBatteryExtraCharge | (b in r.modifiers) implies
	 !(c in r.modifiers && c != b)

}

//No price modifiers without a ride
fact OneRidePerPriceModifier{
 	all pm: PriceModifier | (one r: Ride  | pm in r.modifiers) 
}

//No battery level without a car
fact OneCarPerBatteryLevel {
	all b:BatteryLevel | (some c : Car | c.battery = b)
} 

//If a car is available the no services can be active on it
fact AvailableCarHasNoActiveService{
	all c : Car | c.status=AVAILABLE 
		implies !(some s: Service | s.status=ACTIVE && s.car=c)  
}

//Every car in ride has its engine started
fact engineStartedDuringRide{
	all c : Car | c.engineStarted = True iff one r : Ride | r.car = c
}


//ASSERTIONS
assert NoFreeCarDuringBookingOrRide{
	all c : Car | c.status = AVAILABLE 
		implies (all s : Service | s.car = c 
			implies (s.status = CLOSED || s.status = CANCELLED))
}
check NoFreeCarDuringBookingOrRide for 5

assert NoClientInTwoActiveServices{
	all s1 : Service | s1.status = ACTIVE
		implies (all s2 : Service |(s1 != s2 && s1.client = s2.client) 
			implies (s2.status = CLOSED || s2.status = CANCELLED))
}
check NoClientInTwoActiveServices for 5

assert NoCarInTwoActiveServices{
	all s1 : Service | s1.status = ACTIVE 
		implies (all s2 : Service |(s1 != s2 && s1.car = s2.car) 
			implies (s2.status = CLOSED || s2.status = CANCELLED))
}
check NoClientInTwoActiveServices for 5

assert allBookedCarsOneBooking{
	all c: Car | c.status = BOOKED 
		implies (one b : Booking | b.car = c && b.status = ACTIVE)
}
check allBookedCarsOneBooking for 5

assert allRentedCarsOneRent{
	all c: Car | c.status = RENT 
		implies (one b : Ride | b.car = c && b.status = ACTIVE)
}
check allRentedCarsOneRent for 5

assert everyBookingHasAride{
	 all r : Ride | one b : Booking | (b.ride = r && r.booking = b)
}
check everyBookingHasAride for 5

assert noUselessBilling{
	all b : Billing | one s : Service | b.service = s && s.status = CLOSED
}
check noUselessBilling for 5

//PREDICATES
pred show{
	#Booking > 1
	#Car > 3
	#Ride > 1
	#GPSPosition > 3
	#BatteryLevel > 1
	#Client > 1
	some b : Booking | b.status = CLOSED && #b.ride = 0
}
run show for 5

pred twoBillings{
	#Billing = 2
	some b : Booking | b.status = ACTIVE && #b.ride = 0
	some b : Booking | b.status = CANCELLED && #b.ride = 0
}
run twoBillings for 5


pred oneCar{
	 #Car = 1
}
run oneCar for 5

pred oneCartwoClients{
	 #Car = 1
	 #Client = 2
}
run oneCartwoClients for 5



