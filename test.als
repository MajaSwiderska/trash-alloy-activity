//Done by Pamerla Mensah
/*
module test

sig Person {
  friends: set Person
}

fact NoSelfFriends {
  no p: Person | p in p.friends
}

run {} for 3
*/

module logistics

sig Person {
    location: one Location
}

sig Material {
    location: one Location
}

abstract sig Location {}

abstract sig ParkingFacility extends Location {
    vehicles: set Vehicle
}

sig ParkingLot extends ParkingFacility {}
sig ParkingGarage extends ParkingFacility {}
sig Dwelling extends Location {}
sig Warehouse extends Location {}

sig Workplace extends Location {
    peopleNeeded: Int,
    materialsNeeded: Int
}

abstract sig Vehicle {
    location: one ParkingFacility,
    passengers: set Person,
    cargo: set Material
}

sig PassengerVehicle extends Vehicle {
    seats: Int
} {
    #passengers <= seats
    no cargo
}

sig CargoVehicle extends Vehicle {
    capacity: Int
} {
    #cargo <= capacity
    no passengers
}

fact VehicleCapacity {
    all v: PassengerVehicle | v.seats >= 0
    all v: CargoVehicle | v.capacity >= 0
}

fact WorkplaceRequirements {
    all w: Workplace |
        w.peopleNeeded >= 0 and
        w.materialsNeeded >= 0
}

pred init {
    all p: Person | p.location in Dwelling
    all m: Material | m.location in Warehouse
    all v: Vehicle | v.location in ParkingFacility
    no passengers
    no cargo
}

run init for 5
run {} for 5
