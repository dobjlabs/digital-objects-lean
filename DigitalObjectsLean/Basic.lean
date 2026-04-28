import Mathlib.Data.Set.Basic

inductive Operation where
  | Insert (i : Nat)
  | Delete (i : Nat)
  | Mutate (i j : Nat)

mutual
  inductive Event (Object : Type) where
    | operation (op : Operation)
    | subaction (a : Action Object) (mapping : List Nat)

  structure Action (Object : Type) where
    n_objs: Nat
    relations : List ((Fin n_objs → Object) → Prop)
    events: List (Event Object)
end

structure Tx (Object : Type) where
  action : Action Object
  objects : Fin action.n_objs → Object -- fn that maps [0..n_objs) to Object

-- def Tx.RelationsHold (tx : Tx Object) : Prop :=
--   ∀ rel ∈ tx.action.relations, rel tx.objects

structure ObjectType (Object : Type) where
  actions : Set (Action Object)

def Operation.WellFormed (n : Nat) : Operation → Prop
  | .Insert i => i < n
  | .Delete i => i < n
  | .Mutate i j => i < n ∧ j < n

-- TODO: The explicit proofs of termination is annoying, figure out a way to remove them
mutual
  def Event.WellFormed (n_parent : Nat) (e : Event Object) : Prop :=
    match e with
    | .operation op => op.WellFormed n_parent
    | .subaction a mapping =>
        mapping.length = a.n_objs ∧
        (∀ k ∈ mapping, k < n_parent) ∧
        a.WellFormed
  termination_by sizeOf e
  decreasing_by all_goals (simp_wf; omega)

  def Action.WellFormed (a : Action Object) : Prop :=
    -- ∀ e ∈ a.events, e.WellFormed a.n_objs
    Action.allEventsWellFormed a.n_objs a.events
  termination_by sizeOf a
  decreasing_by
    cases a
    simp_wf
    omega


  def Action.allEventsWellFormed (n : Nat) : List (Event Object) → Prop
    | [] => True
    | e :: rest => e.WellFormed n ∧ Action.allEventsWellFormed n rest
  termination_by es => sizeOf es
  decreasing_by all_goals (simp_wf; omega)
end

def Tx.WellFormed (tx : Tx Object) : Prop :=
  tx.action.WellFormed

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
