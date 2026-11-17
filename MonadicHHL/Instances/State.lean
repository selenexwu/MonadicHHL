import MonadicHHL.HHLMonads
import MonadicHHL.HHLWithVal
import MonadicHHL.Instances.StateT
import MonadicHHL.Instances.Id

open HHL
open HHLWithVal
open HHLWithValLawful

variable (σ α : Type)

abbrev State σ := StateT σ Id

#synth HHL (State σ)
#synth HHLWithVal (State σ)
#synth HHLWithValLawful (State σ)

#check get
example : (elemType (State σ) α) = (α × σ) := by rfl

#check Bind.kleisliRight
example : α → (StateM Nat Nat) :=
  (fun _ ↦ get) >=> (fun x ↦ ((fun _ ↦ set (x + 1)) >=> fun _ ↦ pure x) ())
example : StateM Nat Nat := do
  let x <- get
  set (x + 1)
  pure x
