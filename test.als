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

sig Person {}

sig Material {}

abstract sig Location {}

sig Dwelling extends Location {}
sig Warehouse extends Location {}

sig Workplace extends Location {
    peopleNeeded: Int,
    materialsNeeded: Int
}

abstract sig Vehicle {}

sig PassengerVehicle extends Vehicle {
    seats: Int
}

sig CargoVehicle extends Vehicle {
    capacity: Int
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

run {} for 5