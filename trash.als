var sig File {}
var sig Trash in File {}

fact init {
  no Trash
}

pred forceDelete {
  some Trash //guard
  File' = File - Trash //removing the trash files from the system
  Trash' = none  //Trash becomes empty 
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
  always (empty or (some f : File | delete[f] or restore[f]))
}

run example {}
