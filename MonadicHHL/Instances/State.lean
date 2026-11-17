import MonadicHHL.HHLMonads
import MonadicHHL.HHLWithVal
import MonadicHHL.Instances.StateT
import MonadicHHL.Instances.Id

open HHL
open HHLWithVal
open HHLWithValLawful

variable (σ α : Type)

abbrev State σ := StateT σ Id

example : (elemType (State σ) α) = (α × σ) := by rfl

example : α → (StateM Nat Nat) :=
  (fun _ ↦ get) >=> (fun x ↦ ((fun _ ↦ set (x + 1)) >=> fun _ ↦ pure x) ())
example : StateM Nat Nat := do
  let x <- get
  set (x + 1)
  pure x

lemma WP_get {α : Type}
(Q : hyperassertion (M := State σ) σ)
: WP (fun _ ↦ get) Q = (fun S ↦ Q ((fun ((_:α), s) ↦ (s,s)) '' S)) := by
  funext S
  simp [WP,semify,relWith,Set.image]
  apply prove_prop_by_eq
  apply Set.ext
  intro p'
  simp
  apply exists_congr
  aesop

lemma WP_set {α : Type}
(Q : hyperassertion (M := State σ) PUnit)
(f : α → σ)
: WP (fun x ↦ set (f x)) Q = (fun S ↦ Q ((fun (a,_) ↦ ((), f a)) '' S)) := by
  funext S
  simp [WP,semify,relWith,Set.image]
  apply prove_prop_by_eq
  apply Set.ext
  intro p'
  simp
  apply exists_congr
  aesop
  
def example_prog_1 {α : Type} : α → (State ℕ Nat) := 
  (fun _ ↦ get) >=> (fun x ↦ set (x + 1)) >=> fun _ ↦ pure 5

example (n : ℕ) : 
HHL.triple (M := State ℕ) 
(H.forallOk (fun ((_,s),_) ↦ H.pure (s = n))) 
(example_prog_1 (α := ℕ)) 
(H.forallOk (fun ((_,s),res) ↦ H.pure (res = 5 ∧ s = n + 1)))
:= by
  simp [triple_equiv]
  intro S P
  simp [elemType,StateT.elemType,Id] at S
  unfold example_prog_1
  simp [WP_bind,WP_get,WP_set,WP_pure_const,Functor.mapConst,Functor.map,Set.image]
  simp [H.forallOk,getVal] at *
  intro s hs
  specialize P s hs
  obtain ⟨_,s⟩ := s
  aesop
