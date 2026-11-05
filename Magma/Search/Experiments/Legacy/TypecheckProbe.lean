import Lean
#guard_msgs (drop info) in
#check ((throw (IO.userError "must not run")) : IO Unit)
