import Mathlib.Data.Set.Basic

inductive TxOperation where
  | Insert
  | Delete
  | Mutate

inductive TxEvent where
  | TxOperation
  | TxAction

def TxAction : Type := List TxEvent

structure Action where
  num_objs : Nat
  relations : List Bool
  tx_action : TxAction

def ObjectType : Type := Set Action

structure SystemSpec (Object : Type) (State: Type) where
  -- **Global State**

  InCreated (o : Object) (s : State) (t : Nat) : Prop
  NotInDeleted (o : Object) (s : State) (t : Nat) : Prop
  InDeleted (o : Object) (s : State) (t : Nat) : Prop

  -- Once an object is in Created it stays there forever
  inCreated_monotone (o : Object) (s : State) (t t' : Nat) :
    t' > t → InCreated o s t → InCreated o s t'

  -- Once an object is in Deleted it stays there forever
  inDeleted_monotone (o : Object) (s : State) (t t' : Nat) :
    t' > t → InDeleted o s t → InDeleted o s t'

  -- If an object was not deleted at t, it was not deleted before t
  notInDeleted_antitone (o : Object) (s : State) (t t' : Nat) :
    t' < t → NotInDeleted o s t → NotInDeleted o s t'

  -- **Untyped Events**

  UntypedInsert (o : Object) (s : State) (t : Nat) : Prop
  UntypedDelete (o : Object) (s : State) (t : Nat) : Prop
  UntypedMutate (o o': Object) (s : State) (t : Nat) : Prop

  -- Insert: the object is in Created and not in Deleted
  untypedInsert_prop (o : Object) (s : State) (t : Nat) :
    UntypedInsert o s t → InCreated o s t ∧ NotInDeleted o s t

  -- Delete: the object was in Created and not in Deleted, afterwards it's in Deleted
  untypedDelete_prop (o : Object) (s : State) (t : Nat) :
    UntypedDelete o s t → InCreated o s (t-1) ∧ NotInDeleted o s (t-1) ∧ InDeleted o s t

  -- Mutate: delete previous object, insert new one
  untypedMutate_prop (o o' : Object) (s : State) (t : Nat) :
    UntypedMutate o o' s t → UntypedDelete o' s t ∧ UntypedInsert o s t

  -- **Typed Events**

  typeOf (o : Object) : ObjectType

  Insert (o : Object) (s : State) (t : Nat) : Prop
  Delete (o : Object) (s : State) (t : Nat) : Prop
  Mutate (o o': Object) (s : State) (t : Nat) : Prop
