import Mathlib.Data.Set.Functor

instance (m : Type _ → Type _) [Monad m] : Monad (OptionT m) where
  pure x := pure (f := m) (some x)
  bind x f := bind (m := m) x (fun x ↦ match x with | some x => f x | none => pure none)
  
instance : Monad Set where
  pure x := {x}
  bind xs f := ⋃ x ∈ xs, f x
  
def SetT (m : Type _ → Type _) [Monad m] (α : Type _) :=
  Set (m α)
  
instance (m : Type _ → Type _) (α : Type _) [Monad m] : Membership (m α) (SetT m α) where
  mem s x := s x

instance {m : Type _ → Type _} [Monad m] : Monad (SetT m) where
  pure x := Set.singleton (pure (f := m) x)
  bind xs f := ⋃ x ∈ xs, Set.singleton (bind (m := m) x (fun x ↦ sorry))
  
instance {m : Type _ → Type _} [Monad m] : MonadLift m (SetT m) where
  monadLift x := Set.singleton x
