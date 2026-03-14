sig Workplace extends Location {
  required_people: one Int,
  required_materials: one Int,

  var people_present: Int,
  var materials_present: Int
}

sig ParkingFacility extends Location {
  vehicles: set Vehicle
}

sig ParkingLot, ParkingGarage extends ParkingFacility {}

abstract sig Vehicle {
  var location: one ParkingFacility,
  var passangers: set Person,
  var cargo: set Material
}

sig PassangerVehicle extends Vehicle {
  max_seats: one Int
} {
  #passangers <= max_seats
  no cargo
}

sig CargoVehicle extends Vehicle {
  max_capacity: one Int
} {
  #cargo <= max_capacity
  no passangers
}

sig Person {
  var location: one Location
}

sig Material {
  var location: one Location
}

pred init {
  all v: Vehicle | v.location in ParkingFacility

  all p: Person | m.location in ParkingFacility

  all m: Material | m.location in ParkingFacility

  no passangers
  no cargo

  all w: Workplace {
    w.people_present = 0
    w.materials_present = 0
  }

  all v: PassangerVehicle | #v.passangers <= v.max_seats
  all v: CargoVehicle | #v.cargo <= v.max_capacity
}

run init for 5 but 10 Int

pred showInitialConfig {
  init
  some PassangerVehicle
  some CargoVehicle
  some Workplace
  some Person
  some Material

  all w: Workplace {
    w.required_people > 0
    w.required_materials > 0
  }
}
run showInitialConfig for 5 but 10 Int

fact transitions {
  always (
    (some v: Vehicle | moveVehicle[v]) or
    (some v: Vehicle, p: Person | loadPassenger[v, p]) or
    (some v: Vehicle, m: Material | loadMaterial[v, m]) or
    (some v: Vehicle, p: Person | unloadPassenger[v, p]) or
    (some v: Vehicle, m: Material | unloadMaterial[v, m]) or
    (some w: Workplace | completeJob[w]) or
    idle
  )
}

pred moveVehicle[v: Vehicle] {
  some v
  
  some dest: ParkingFacility {
    v.location' = dest
    
    all p: v.passengers | p.location' = dest
    all m: v.cargo | m.location' = dest
  }
  
  passengers' = passengers
  cargo' = cargo
  all other: Vehicle - v | other.location' = other.location
  all other_p: Person - v.passengers | other_p.location' = other_p.location
  all other_m: Material - v.cargo | other_m.location' = other_m.location
  all w: Workplace | w.people_present' = w.people_present and 
                     w.materials_present' = w.materials_present
}

pred loadPassenger[v: PassengerVehicle, p: Person] {
  p.location = v.location
  
  p not in Vehicle.passengers
  
  #(v.passengers + p) <= v.max_seats
  
  passengers' = passengers + (v -> p)
  p.location' = v.location  
  location' = location
  cargo' = cargo
  all other_p: Person - p | other_p.location' = other_p.location
  all w: Workplace | w.people_present' = w.people_present and 
                     w.materials_present' = w.materials_present
}

pred loadMaterial[v: CargoVehicle, m: Material] {
  m.location = v.location
  
  m not in Vehicle.cargo
  
  #(v.cargo + m) <= v.max_capacity
  
  cargo' = cargo + (v -> m)
  m.location' = v.location
  
  location' = location
  passengers' = passengers
  all other_m: Material - m | other_m.location' = other_m.location
  all w: Workplace | w.people_present' = w.people_present and 
                     w.materials_present' = w.materials_present
}

pred unloadPassenger[v: PassengerVehicle, p: Person] {
  p in v.passengers
  v.location in Workplace
  
  passengers' = passengers - (v -> p)
  p.location' = v.location

  let w = v.location {
    w.people_present' = w.people_present + 1
  }
  
  location' = location
  cargo' = cargo
  all other_p: Person - p | other_p.location' = other_p.location
  all other_w: Workplace - v.location | 
        other_w.people_present' = other_w.people_present and
        other_w.materials_present' = other_w.materials_present
}

pred unloadMaterial[v: CargoVehicle, m: Material] {
  m in v.cargo
  
  v.location in Workplace
  
  cargo' = cargo - (v -> m)
  m.location' = v.location
  
  let w = v.location {
    w.materials_present' = w.materials_present + 1
  }

  location' = location
  passengers' = passengers
  all other_m: Material - m | other_m.location' = other_m.location
  all other_w: Workplace - v.location | 
        other_w.people_present' = other_w.people_present and
        other_w.materials_present' = other_w.materials_present
}

pred completeJob[w: Workplace] {
  w.people_present >= w.required_people
  w.materials_present >= w.required_materials
  
  no w'
  
  all other: Workplace - w | 
    other.people_present' = other.people_present and
    other.materials_present' = other.materials_present
}

pred idle {
  location' = location
  passengers' = passengers
  cargo' = cargo
  people_present' = people_present
  materials_present' = materials_present
}

assert PeopleAlwaysLocated {
  always all p: Person | some p.location
}

assert MaterialsAlwaysLocated {
  always all m: Material | some m.location
}

assert PassengersConsistent {
  always all p: Person |
    (some v: Vehicle | p in v.passengers) implies 
    p.location = v.location
}

assert CanCompleteAllJobs {
  all w: Workplace |
    eventually w.people_present >= w.required_people and
               w.materials_present >= w.required_materials
}

check PeopleAlwaysLocated for 5 but 10 steps, 10 Int
check MaterialsAlwaysLocated for 5 but 10 steps, 10 Int
check PassengersConsistent for 5 but 10 steps, 10 Int
check CanCompleteAllJobs for 5 but 10 steps, 10 Int


pred showDelivery {
  init
  
    some w: Workplace {
    w.required_people = 2
    w.required_materials = 3
  }
  
  some pv: PassengerVehicle {
    pv.max_seats = 4
  }
  
  some cv: CargoVehicle {
    cv.max_capacity = 5
  }
  
  #Person = 3
  #Material = 4
  
  eventually {
    some w: Workplace |
      w.people_present >= w.required_people and
      w.materials_present >= w.required_materials
  }
}
run showDelivery for 5 but 10 steps, 10 Int

pred demonstrateCompletion {
  init
  
  eventually some w: Workplace | completeJob[w]
}
run demonstrateCompletion for 5 but 10 steps, 10 Int
