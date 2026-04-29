import Mathlib.Data.Set.Basic

-- a Vec is a function that maps that maps [0..n-1] to Object
abbrev Vec (α : Type) (n : Nat) : Type := Fin n → α

inductive Operation where
  | Insert (i : Nat)
  | Delete (i : Nat)
  | Mutate (i j : Nat)

mutual
  inductive Event (Object : Type) where
    | operation (op : Operation)
    | subaction (a : Action Object) (mapping : List Nat)

  structure Action (Object : Type) where
    n_objs : Nat
    relations : List ((Vec Object n_objs) → Prop)
    events : List (Event Object)
end

structure Tx (Object : Type) where
  action : Action Object
  objects : Vec Object n_objs → Object

structure ObjectType (Object : Type) where
  actions : Set (Action Object)

def Operation.WellFormed (n : Nat) : Operation → Prop
  | .Insert i => i < n
  | .Delete i => i < n
  | .Mutate i j => i < n ∧ j < n

mutual
  inductive Event.WellFormed {Object : Type} : Nat → Event Object → Prop where
    | operation {n op} :
        Operation.WellFormed n op →
        Event.WellFormed n (Event.operation op)
    | subaction {n} {a : Action Object} {mapping} :
        mapping.length = a.n_objs →
        (∀ k ∈ mapping, k < n) →
        Action.WellFormed a →
        Event.WellFormed n (Event.subaction a mapping)

  inductive Action.WellFormed {Object : Type} : Action Object → Prop where
    | mk {a : Action Object} :
        (∀ e ∈ a.events, Event.WellFormed a.n_objs e) →
        Action.WellFormed a
end

def Tx.WellFormed (tx : Tx Object) : Prop :=
  tx.action.WellFormed

-- Reindex parent's objects through a subaction's mapping
def reindex {Object : Type} {n_parent : Nat}
    (objects : Vec Object n_parent)
    (a : Action Object) (mapping : List Nat)
    -- the mapping has one entry per subaction slot
    (h_len : mapping.length = a.n_objs)
    -- every entry of the mapping is a valid parent slot
    (h_bound : ∀ k ∈ mapping, k < n_parent) :
    Vec Object a.n_objs :=
  fun i =>
    -- indexed list access with a bounds proof.
    let k := mapping[i.val]'(by rw [h_len]; exact i.isLt)
    have : k < n_parent := h_bound _ (List.getElem_mem _)
    objects ⟨k, this⟩

mutual
  -- True if P holds at every action and subaction reachable from this event
  inductive Event.AllSubactions {Object : Type}
      (P : {n : Nat} → Action Object → (Vec Object n) → Prop) :
      {n_parent : Nat} → Event Object → (Vec Object n_parent) → Prop where
    | operation {n_parent} {objects : Vec Object n_parent} {op : Operation} :
        Event.AllSubactions P (Event.operation op) objects
    | subaction {n_parent} {objects : Vec Object n_parent}
        (a : Action Object) (mapping : List Nat)
        (h_len : mapping.length = a.n_objs)
        (h_bound : ∀ k ∈ mapping, k < n_parent)
        (h_rec : Action.AllSubactions P a (reindex objects a mapping h_len h_bound)) :
        Event.AllSubactions P (Event.subaction a mapping) objects

  inductive Action.AllSubactions {Object : Type}
      (P : {n : Nat} → Action Object → (Vec Object n) → Prop) :
      (a : Action Object) → (Vec Object a.n_objs) → Prop where
    | mk {a : Action Object} {objects : Vec Object a.n_objs}
        (h_here : P a objects)
        (h_events : ∀ e ∈ a.events, Event.AllSubactions P e objects) :
        Action.AllSubactions P a objects
end

-- def Tx.RelationsHold (tx : Tx Object) : Prop :=
--   ∀ rel ∈ tx.action.relations, rel tx.objects


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

  -- -- **Untyped Events**

  -- UntypedInsert (o : Object) (s : State) (t : Nat) : Prop
  -- UntypedDelete (o : Object) (s : State) (t : Nat) : Prop
  -- UntypedMutate (o o': Object) (s : State) (t : Nat) : Prop

  -- -- Insert: the object is in Created and not in Consumed
  -- untypedInsert_prop (o : Object) (s : State) (t : Nat) :
  --   UntypedInsert o s t →
  --     InCreated o s t ∧ NotInConsumed o s t

  -- -- Delete: the object was in Created and not in Consumed, afterwards it's in Consumed
  -- untypedDelete_prop (o : Object) (s : State) (t : Nat) (ht : t > 0) :
  --   UntypedDelete o s t →
  --     InCreated o s (t-1) ∧ NotInConsumed o s (t-1) ∧ InConsumed o s t

  -- -- Mutate: delete previous object, insert new one
  -- untypedMutate_prop (o o' : Object) (s : State) (t : Nat) :
  --   UntypedMutate o o' s t →
  --     UntypedDelete o' s t ∧ UntypedInsert o s t

  -- -- **Typed Events**

  -- typeOf (o : Object) : ObjectType Object

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
