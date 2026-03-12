var sig File {} //All files in the system
var sig Trash in File {} //Trash is always a subset of Files

//Initial state -> Trash is empty
fact init {
  no Trash
}

//It permanently removes all the files in Trash from the system
pred forceDelete {
  some Trash //guard
  File' = File - Trash //removing the trash files from the system
  Trash' = none  //Trash becomes empty 
}

//Same as forceDelete 
pred empty {
  some Trash       // guard
  File' = File - Trash // effect on File
  Trash' = none
}

//Moving a specific file to Trash (like a soft delete)
pred delete [f : File] {
 f not in Trash   // guard
  Trash' = Trash + f // effect on Trash
  File' = File       // frame condition on File
}

//Restoring a file from Trash back to regular files
pred restore [f : File] {
  f in Trash //guard -> the files have to be in trash to restore
  Trash' = Trash - f //remove file from trash
  File' = File //File set remains unchanged
}

//This does nothing, the system stays idle
pred idle {
  File' = File
  Trash' = Trash
}

//defines all possible next states
fact trans {
  always ( 
      empty or //option 1 -> empty all the trash
      forceDelete or //option 2 -> force delete all trash
  (some f: File | (delete[f] or restore[f])) or //option 3 -> delete or restore one file
  idle //option 4 -> do nothing
  )
}

//propert 1 -> Trash should always have only files that exist 
assert TrashSubset {
  always Trash in File
}
check TrashSubset for 5 but 10 steps // this should check it

// property 2 -> Files don't stay in the trash forever
assert EventuallyLeavesTrash {
  always (all f : File |
    f in Trash implies eventually (f not in Trash)
  )
}
check EventuallyLeavesTrash for 5 but 10 steps

//property 3 -> a file can only be deleted once
assert NoDoubleDelete {
  always (all f: File |
    (once delete[f]) implies
      (after always (f in Trash implies f not in Trash'))
  )
}
check NoDoubleDelete for 5 but 10 steps

//property 4 -> Trash will become empty eventually
assert TrashEventuallyEmpty {
  eventually no Trash
}
check TrashEventuallyEmpty for 5 but 10 steps
run {} for 5 but 10 steps

//This is a scenario, shows a trace where a file gets deleted
pred showDeleteRestore {
  some File
  no Trash

  eventually {
    some f: File | delete[f] //at some point it will delete a file
  }
}
run showDeleteRestore for 5 but 10 steps