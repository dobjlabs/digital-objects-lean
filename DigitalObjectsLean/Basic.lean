import Mathlib.Data.Set.Basic

-- better error messages for a newbie like me.  Forces writing implicit
-- arguments with '{ ... }' notation, but gives better error messages when
-- using undefined symbols
set_option autoImplicit false

inductive Operation where
  | Insert (i : Nat) -- Create i
  | Delete (i : Nat) -- Consume i
  | Mutate (i j : Nat) -- Consume i and create j

def Operation.Creates {Object : Type}
    (op : Operation) (objects : Nat → Object) (o : Object) : Prop :=
  match op with
  | .Insert i => objects i = o
  | .Delete _ => False
  | .Mutate _ j => objects j = o

def Operation.Consumes {Object : Type}
    (op : Operation) (objects : Nat → Object) (o : Object) : Prop :=
  match op with
  | .Insert _ => False
  | .Delete i => objects i = o
  | .Mutate i _ => objects i = o

mutual
  inductive Event (Object : Type) where
    | operation (op : Operation)
    | subaction (a : Action Object) (mapping : Nat → Nat)

  structure Action (Object : Type) where
    relations : List ((Nat → Object) → Prop)
    events : List (Event Object)
end

structure Tx (Object : Type) where
  action : Action Object
  objects : Nat → Object

structure ObjectType (Object : Type) where
  actions : Set (Action Object)

-- Reindex parent's objects through a subaction's mapping.
def reindex {Object : Type}
    (objects : Nat → Object)
    (mapping : Nat → Nat) :
    Nat → Object :=
  fun i => objects (mapping i)

mutual
  -- True if P holds at every action and subaction reachable from this event
  inductive Event.AllSubactions {Object : Type}
      (P : Action Object → (Nat → Object) → Prop) :
      Event Object → (Nat → Object) → Prop where
    | operation {objects : Nat → Object} {op : Operation} :
        Event.AllSubactions P (Event.operation op) objects
    | subaction {objects : Nat → Object}
        (a : Action Object) (mapping : Nat → Nat)
        (h_rec : Action.AllSubactions P a (reindex objects mapping)) :
        Event.AllSubactions P (Event.subaction a mapping) objects

  -- True if P holds at this action and every subaction reachable from it
  inductive Action.AllSubactions {Object : Type}
      (P : Action Object → (Nat → Object) → Prop) :
      Action Object → (Nat → Object) → Prop where
    | mk {a : Action Object} {objects : Nat → Object}
        (h_here : P a objects)
        (h_events : ∀ e ∈ a.events, Event.AllSubactions P e objects) :
        Action.AllSubactions P a objects
end

mutual
  inductive Event.SomeOp {Object : Type}
      (P : Operation → (Nat → Object) → Prop) :
      Event Object → (Nat → Object) → Prop where
    | here {objects : Nat → Object} {op : Operation}
        (h : P op objects) :
        Event.SomeOp P (Event.operation op) objects
    | inSub {objects : Nat → Object}
        (a : Action Object) (mapping : Nat → Nat)
        (h_rec : Action.SomeOp P a (reindex objects mapping)) :
        Event.SomeOp P (Event.subaction a mapping) objects

  inductive Action.SomeOp {Object : Type}
      (P : Operation → (Nat → Object) → Prop) :
      Action Object → (Nat → Object) → Prop where
    | mk {a : Action Object} {objects : Nat → Object} {e : Event Object}
        (h_mem : e ∈ a.events)
        (h_rec : Event.SomeOp P e objects) :
        Action.SomeOp P a objects
end

def Tx.RelationsHold {Object : Type} (tx : Tx Object) : Prop :=
  Action.AllSubactions
    (fun a objects => ∀ rel ∈ a.relations, rel objects)
    tx.action tx.objects

def Tx.Creates {Object : Type} (tx : Tx Object) (o : Object) : Prop :=
  Action.SomeOp (fun op objs => op.Creates objs o) tx.action tx.objects

def Tx.Consumes {Object : Type} (tx : Tx Object) (o : Object) : Prop :=
  Action.SomeOp (fun op objs => op.Consumes objs o) tx.action tx.objects

def InCreated {Object : Type} (o : Object) (h : List (Tx Object)) : Prop :=
  ∃ tx ∈ h, tx.Creates o

def InConsumed {Object : Type} (o : Object) (h : List (Tx Object)) : Prop :=
  ∃ tx ∈ h, tx.Consumes o

-- The history is defined as a list of transactions, where the head is the most
-- recent transaction.
structure SystemSpec (Object : Type) where
  -- Properties that an implementation must define --
  -- A transaction is valid to append to a history
  ValidTx : List (Tx Object) → Tx Object → Prop
  typeOf (o : Object) : Option (ObjectType Object)

  -- Theorems that an implementation must prove --

  -- TODO: Update to support consuming an object created in the tx
  validTx_consumes_created :
    ∀ h tx o, ValidTx h tx → tx.Consumes o → InCreated o h

  validTx_no_double_create :
    ∀ h tx o, ValidTx h tx → tx.Creates o → ¬ InCreated o h

  validTx_no_double_consume :
    ∀ h tx o, ValidTx h tx → tx.Consumes o → ¬ InConsumed o h

  -- validTx_no_intra_double_create :
  --   ∀ h tx, ValidTx h tx → ∀ o₁ o₂, (o₁ ≠ o₂) ∧ ¬ (tx.Creates o₁ ∧ tx.Creates o₂)

  -- validTx_no_intra_double_consume :
  --   ∀ h tx, ValidTx h tx → ∀ o, /- tx consumes o at most once -/

  validTx_relations_hold :
    ∀ h tx, ValidTx h tx → Tx.RelationsHold tx

-- Definitions

namespace SystemSpec

def ValidHistory {Object : Type} (spec : SystemSpec Object) :
    List (Tx Object) → Prop
  | [] => True
  | tx :: history => spec.ValidHistory history ∧ spec.ValidTx history tx

end SystemSpec

def Reaches  {Object : Type} (h h' : List (Tx Object)) : Prop :=  h.IsSuffix h'

-- Generic theorems with proofs (for all SystemSpec)

theorem InCreated.mono {Object : Type} {o : Object} {h h' : List (Tx Object)} :
    Reaches h h' → InCreated o h → InCreated o h' := by
  intro hreach ⟨tx, htx_mem, htx_creates⟩
  exact ⟨tx, hreach.mem htx_mem, htx_creates⟩

theorem InConsumed.mono {Object : Type} {o : Object} {h h' : List (Tx Object)} :
    Reaches h h' → InCreated o h → InCreated o h' := by
  intro hreach ⟨tx, htx_mem, htx_creates⟩
  exact ⟨tx, hreach.mem htx_mem, htx_creates⟩


theorem genesis_empty {Object : Type} {o : Object} :
    (¬ InCreated o []) ∧ (¬ InConsumed o []) := by
    simp [InCreated, InConsumed]

/-
structure SystemSpec (Object : Type) (State: Type) where
  -- **Global State**

  genesis : State

  -- s' results from applying tx to s
  Step (s : State) (tx : Tx Object) (s' : State) : Prop

  step_deterministic (s : State) (tx : Tx Object) (s₁ s₂ : State) :
    Step s tx s₁ → Step s tx s₂ → s₁ = s₂

  -- s' is reachable from s through some sequence of transactions
  Reaches (s s' : State) : Prop

  reaches_refl (s : State) : Reaches s s
  reaches_step (s s' : State) (tx : Tx Object) : Step s tx s' → Reaches s s'
  reaches_trans (s s' s'' : State) :
    Reaches s s' → Reaches s' s'' → Reaches s s''
  -- no forks: guarantees total order of state updates
  reaches_linear (s s' s'' : State) :
    Reaches s s' → Reaches s s'' → Reaches s' s'' ∨ Reaches s'' s'

  InCreated (o : Object) (s : State) : Prop
  InConsumed (o : Object) (s : State) : Prop

  -- Once created, always created
  inCreated_monotone (o : Object) (s s' : State) :
    Reaches s s' → InCreated o s → InCreated o s'
  -- Once consumed, always consumed
  inConsumed_monotone (o : Object) (s s' : State) :
    Reaches s s' → InConsumed o s → InConsumed o s'
  -- An object can only be consumed if it was created
  consumed_implies_created (o : Object) (s : State) :
    InConsumed o s → InCreated o s
  genesis_empty :
    ∀ o : Object, ¬ InConsumed o genesis ∧ ¬ InCreated o genesis

  -- **Untyped Events**

  UntypedInsert (o : Object) (s : State) (t : Nat) : Prop
  UntypedDelete (o : Object) (s : State) (t : Nat) : Prop
  UntypedMutate (o o': Object) (s : State) (t : Nat) : Prop

  -- Insert: the object is in Created and not in Consumed
  untypedInsert_prop (o : Object) (s : State) (t : Nat) :
    UntypedInsert o s t →
      InCreated o s t ∧ NotInConsumed o s t

  -- Delete: the object was in Created and not in Consumed, afterwards it's in Consumed
  untypedDelete_prop (o : Object) (s : State) (t : Nat) (ht : t > 0) :
    UntypedDelete o s t →
      InCreated o s (t-1) ∧ NotInConsumed o s (t-1) ∧ InConsumed o s t

  -- Mutate: delete previous object, insert new one
  untypedMutate_prop (o o' : Object) (s : State) (t : Nat) :
    UntypedMutate o o' s t →
      UntypedDelete o' s t ∧ UntypedInsert o s t

  -- **Typed Events**

  typeOf (o : Object) : Option (ObjectType Object)

  -- Insert (o : Object) (s : State) (t : Nat) : Prop
  -- Delete (o : Object) (s : State) (t : Nat) : Prop
  -- Mutate (o o': Object) (s : State) (t : Nat) : Prop

  -- insert_prop (o : Object) (s : State) (t : Nat) :
  --   Insert o s t →
  --     UntypedInsert o s t ∧
  --     ∃ a : Action, ∃ e : TxEvent,
  --     a ∈ (typeOf o).actions ∧
  --     e ∈ a.tx_action.events ∧
  --     e = TxEvent.operation TxOperation.Mutate
-/
