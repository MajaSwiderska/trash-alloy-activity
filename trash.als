//Phase 1
//Each person has a location that can change over time
sig Person {
  var location: one Location
}

//Each material has a location that can change over time
sig Material {
  var location: one Location
}

//Abstract means that you cannot create direct instances of Location
abstract sig Location {}

//Workplaces require resources to complete the job
sig Workplace extends Location {
  //static requirment -> doesn't change
  required_people: one Int,
  required_materials: one Int,

  //dynamic state -> these do change as the resources come
  var people_present: Int,
  var materials_present: Int
}

//Parking facilities can have vehicle parked at them
sig ParkingFacility extends Location {
  vehicles: set Vehicle //set of vehicles parked here
}

//specific facilities 
sig Dwelling extends ParkingFacility {} //where the people live
sig Warehouse extends ParkingFacility {} //where the materials are stored

//abstract vehicle class 
//location -> where they are
//passengers -> who they are carrying
//cargo -> what they are carrying
abstract sig Vehicle {
  var location: one ParkingFacility,
  var passengers: set Person,
  var cargo: set Material
}

//passenger vehicles have seats and can only carry people
sig PassengerVehicle extends Vehicle {
  seats: Int //max number of passangers
} {
  //constraints that must always hold for passenger vehicles
  #passengers <= seats  //can't go over seat capacity
  no cargo //passenger vehicles don't carry cargo

}

//Cargo vehicles have capacity and can only carry materials
sig CargoVehicle extends Vehicle {
  capacity: Int //max amount of cargo
} {
  //constraints that must always hold for cargo vehicles
  #cargo <= capacity //can't go over capacity
  no passengers //cargo vehicles don't carry people
}

//Constraints -> Global
//vehicle capacities must be non-negative
fact VehicleCapacity {
  all v: PassengerVehicle | v.seats >= 0
  all v: CargoVehicle | v.capacity >= 0
}

//Workplace requirments must be non-negative
fact WorkplaceRequirements {
  all w: Workplace {
    w.required_people >= 0
    w.required_materials >= 0
  }
}

//Initial Config
//defines what the world looks like at the startting time 0
pred init {
  //all vehicles start at some parking facility
  all v: Vehicle | v.location in ParkingFacility

  //all people start at some parking facility -> dwelling
  all p: Person | p.location in ParkingFacility

  //alll materials start at some parking facility -> warehouse
  all m: Material | m.location in ParkingFacility

  //no one is in the vehicles at the start
  no passengers
  no cargo

  //workplace starts with zero resources delivered
  all w: Workplace {
    w.people_present = 0
    w.materials_present = 0
  }
}

//command to run and see the initial config
run init for 5 but 10 Int

//a more interesting initial config with requirmenrs > 0
pred showInitialConfig {
  init
  some PassengerVehicle
  some CargoVehicle
  some Workplace
  some Person
  some Material

  //making sure that the workplace actually needs resources
  all w: Workplace {
    w.required_people > 0
    w.required_materials > 0
  }
}

//command to run the interesting initial config
run showInitialConfig for 5 but 10 Int

//Phase 2
//at every step the system have to do one of these actions
fact transitions {
  always (
    (some v: Vehicle | moveVehicle[v]) or //move a vehicle
    (some v: PassengerVehicle, p: Person | loadPassenger[v, p]) or //load a person
    (some v: CargoVehicle, m: Material | loadMaterial[v, m]) or //load materials
    (some v: PassengerVehicle, p: Person | unloadPassenger[v, p]) or //unload a person
    (some v: CargoVehicle, m: Material | unloadMaterial[v, m]) or //unload material
    (some w: Workplace | completeJob[w]) or //complete the job
    idle //nothing
  )
}

//move a vehicle to a different parking facility
pred moveVehicle[v: Vehicle] {
  //choosing a destination parking facility
  some dest: ParkingFacility {
    //vehicle moves to the destination
    v.location' = dest
    
    //all passengers and cargo move with the vehicle
    all p: v.passengers | p.location' = dest
    all m: v.cargo | m.location' = dest
  }
  
  //frame conditions -> everything else stays the same
  passengers' = passengers
  cargo' = cargo
  all other: Vehicle - v | other.location' = other.location
  all other_p: Person - v.passengers | other_p.location' = other_p.location
  all other_m: Material - v.cargo | other_m.location' = other_m.location
  all w: Workplace | 
      w.people_present' = w.people_present and 
      w.materials_present' = w.materials_present
}

//load a person into a passenger vehicle
pred loadPassenger[v: PassengerVehicle, p: Person] {
  p.location = v.location //person must be at the vehicles location
  
  p not in Vehicle.passengers //person not already in a vehicle
  
  #(v.passengers + p) <= v.seats //vehicle has enough seats
  
  passengers' = passengers + (v -> p) //add a person to vehicles passengers
  p.location' = v.location //persons location is now the vehicle
  //everything is stays the same
  location' = location
  cargo' = cargo
  all other_p: Person - p | other_p.location' = other_p.location
  all w: Workplace | 
      w.people_present' = w.people_present and 
      w.materials_present' = w.materials_present
}

//load a material onto a cargo vehicle
pred loadMaterial[v: CargoVehicle, m: Material] {
  m.location = v.location //material must be at vehicles location
  
  m not in Vehicle.cargo //material not already in a vehicle
  
  #(v.cargo + m) <= v.capacity //vehicle has enough capacity
  
  cargo' = cargo + (v -> m) //add material to vehicles cargo
  m.location' = v.location //materials location is now the vehicle
  
  //frame conditions
  location' = location
  passengers' = passengers
  all other_m: Material - m | other_m.location' = other_m.location
  all w: Workplace | 
      w.people_present' = w.people_present and 
      w.materials_present' = w.materials_present
}

//unload a person from a vehicle at a workplace
pred unloadPassenger[v: PassengerVehicle, p: Person] {
  p in v.passengers //person must be in this vehicle
  v.location in Workplace //vehicle must be at a workplace
  
  passengers' = passengers - (v -> p) //remove a person from the vehicle
  p.location' = v.location //person is now at the workplace

  //updating the workplaces people count
  let w = v.location {
    w.people_present' = w.people_present + 1
  }
  
  //frame conditions
  location' = location
  cargo' = cargo
  all other_p: Person - p | other_p.location' = other_p.location
  all other_w: Workplace - v.location | 
      other_w.people_present' = other_w.people_present and
      other_w.materials_present' = other_w.materials_present
}

//unload material from a vehicle at a workplace
pred unloadMaterial[v: CargoVehicle, m: Material] {
  m in v.cargo //material must be in this vehicle
  
  v.location in Workplace //vehicle must be at a workplace
   
  cargo' = cargo - (v -> m) //remove the material from the vehicle
  m.location' = v.location //material is now at the workplace
  
  //updating the workplace materials count
  let w = v.location {
    w.materials_present' = w.materials_present + 1
  }

  //frame conditions
  location' = location
  passengers' = passengers
  all other_m: Material - m | other_m.location' = other_m.location
  all other_w: Workplace - v.location | 
      other_w.people_present' = other_w.people_present and
      other_w.materials_present' = other_w.materials_present
}

//complete a job at a workplace when enough resources have arrived 
pred completeJob[w: Workplace] {
  w.people_present >= w.required_people
  w.materials_present >= w.required_materials
  
  //effect -> the workplace disappears, the job is done
  no w'
  
  //frame conditions -> other workplace stays the same
  all other: Workplace - w | 
      other.people_present' = other.people_present and
      other.materials_present' = other.materials_present
}

//do nothing -> the system can stay in the same state
pred idle {
  location' = location
  passengers' = passengers
  cargo' = cargo
  people_present' = people_present
  materials_present' = materials_present
}

//Properties to check
//people are always somewhere, they don't disappear
assert PeopleAlwaysLocated {
  always all p: Person | some p.location
}

//materials are always somewhere, they don't disappear
assert MaterialsAlwaysLocated {
  always all m: Material | some m.location
}

//vehicle capacity doesn't go over ever
assert CapacityRespected {
  always (
    (all v: PassengerVehicle | #v.passengers <= v.seats) and
    (all v: CargoVehicle | #v.cargo <= v.capacity)
  )
}

//this might fail, not always possoble
assert CanCompleteAllJobs {
  all w: Workplace |
    eventually w.people_present >= w.required_people and
               w.materials_present >= w.required_materials
}

//commands to check each property
check PeopleAlwaysLocated for 5 but 10 steps, 10 Int
check MaterialsAlwaysLocated for 5 but 10 steps, 10 Int
check CapacityRespected for 5 but 10 steps, 10 Int
check CanCompleteAllJobs for 5 but 10 steps, 10 Int

//Scenarios
//show a complete delivery process
pred showDelivery {
  init
  
  //there exists a workplace that needs 2 people and 3 materials
  some Workplace {
    required_people = 2
    required_materials = 3
  }
  
  //we have vehicles that can carry them
  some pv: PassengerVehicle | pv.seats = 2
  some cv: CargoVehicle | cv.capacity = 3
  //we have the actual people and materials -> disj is distinct
  some disj p1, p2: Person
  some disj m1, m2, m3: Material

  //eventually some workplace gets all the resources it needs
  eventually {
    some w: Workplace |
        w.people_present >= w.required_people and
        w.materials_present >= w.required_materials
  }
}
//run the delivery scenerio
run showDelivery for 5 but 10 steps, 10 Int

//show a job being completed
pred showJobCompletion {
  init
  
  //eventually some workplace gets completed
  eventually some w: Workplace | completeJob[w]
}
//run the job completion
run showJobCompletion for 5 but 10 steps, 10 Int
