var sig File {}
var sig Trash in File {}

fact init {
  no Trash
}

pred empty {
  some Trash       // guard
  File' = File - Trash // effect on File
  Trash' = none
}

pred delete [f : File] {
 f not in Trash   // guard
  Trash' = Trash + f // effect on Trash
  File' = File       // frame condition on File
}

pred restore [f : File] {
  f in Trash         // guard
  Trash' = Trash - f // effect on Trash
  File' = File       // frame condition on File
}

pred idle {
  File' = File
  Trash' = Trash
}
fact trans {
  always (
      empty
   or (some f : File | 
        delete[f] 
     or restore[f] 
     or forceDelete[f]
   )
   or idle
  )
}
assert TrashSubset {
  always Trash in File
}

check TrashSubset for 5 but 10 steps // this should check it

// Liveness: Files in trash eventually leave trash
assert EventuallyLeavesTrash {
  always (all f : File |
    f in Trash implies eventually (f not in Trash)
  )
}

// This will FAIL (because empty/forceDelete may remove it permanently)
check EventuallyLeavesTrash for 5 but 10 steps

run {} for 5 but 10 steps
