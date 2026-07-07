import Mathlib.Data.Set.Basic

namespace Spec

-- Type: Observable effect on the system state
inductive Effect (Object : Type) where
  | create (o : Object)
  | consume (o : Object)

-- Prop: The effect list is valid given the sets of already created/consumed
-- objects: each create is fresh, each consume was created and not yet consumed
def ValidEffects {Object : Type} (created consumed : Set Object) :
    List (Effect Object) → Prop
  | [] => True
  | .create o :: es => o ∉ created ∧ ValidEffects (insert o created) consumed es
  | .consume o :: es => o ∈ created ∧ o ∉ consumed ∧ ValidEffects created (insert o consumed) es

-- Type: Operation affecting objects (symbolic or concrete)
inductive Op (α : Type) where
  | insert (x : α)
  | delete (x : α)
  | mutate (from_ to_ : α)
  deriving DecidableEq

abbrev SymbolicOp := Op Nat
abbrev ConcreteOp {Object : Type} := Op Object

-- Fun: Map a symbolic operation to an operation with concrete objects
def SymbolicOp.map {Object : Type} (objects : Nat → Object) : SymbolicOp → (@ConcreteOp Object)
  | .insert i => .insert (objects i)
  | .delete i => .delete (objects i)
  | .mutate i j => .mutate (objects i) (objects j)

-- Fun: Return the effects of a concrete operation
def ConcreteOp.toEffects {Object : Type} : @ConcreteOp Object → List (Effect Object)
  | .insert o => [.create o]
  | .delete o => [.consume o]
  | .mutate o₁ o₂ => [.consume o₁, .create o₂]

-- Prop: A concrete operation creates or consumes an object
def ConcreteOp.Touches {Object : Type} : @ConcreteOp Object → Object → Prop
  | .insert o', o => o' = o
  | .delete o', o => o' = o
  | .mutate o₁ o₂, o => o₁ = o ∨ o₂ = o

mutual
  -- Type: A state affecting event within an action
  inductive Event (Object : Type) where
    | operation (op : SymbolicOp)
    | subaction (a : Action Object) (mapping : Nat → Nat)

  -- Type: A collection of object relations and state changes
  structure Action (Object : Type) where
    relations : List ((Nat → Object) → Prop)
    events : List (Event Object)
end

-- Type: The attempt at applying an action with concrete objects
structure Tx (Object : Type) where
  action : Action Object
  objects : Nat → Object

-- Type: The set of valid actions of an object
structure ObjectType (Object : Type) where
  actions : List (Action Object)

-- Prop: Mutation preserves object type
def ConcreteOp.TypePreserving {Object : Type}
  (typeOf : Object → (ObjectType Object)): (@ConcreteOp Object) → Prop
  | .mutate o₁ o₂ => (typeOf o₁) = (typeOf o₂)
  | _ => True

-- Fun: Reindex parent's objects through a subaction's mapping.
def reindex {Object : Type}
    (objects : Nat → Object)
    (mapping : Nat → Nat) :
    Nat → Object :=
  fun i => objects (mapping i)

-- Fun: List of concrete operations that happen in an action, ignoring subactions
def Action.directConcreteOps {Object : Type}
  (a : Action Object) (objects : Nat → Object) : List (@ConcreteOp Object) :=
  a.events.filterMap (fun e =>
    match e with
    | .operation op => some (op.map objects)
    | .subaction _ _ => none)

-- Prop: All objects touched by this action (ignoring subactions) are touched
-- by an action in the object's type
def Action.OpsTypeMatch {Object : Type}
  (typeOf : Object → ObjectType Object)
  (a : Action Object) (objects : Nat → Object) : Prop :=
  ∀ op ∈ a.directConcreteOps objects,
    ∀ o, op.Touches o → a ∈ (typeOf o).actions

-- NOTE: These mutually recursive function definitions work on mutual recursive
-- types.  Lean requires a proof of termination so that we can use this
-- function in propositions.
mutual
  -- Fun: List of concrete operations of this event and nested actions
  def Event.concreteOps {Object : Type}
    (e : Event Object) (objects : Nat → Object) : List (@ConcreteOp Object) :=
    match e with
    | .operation op => [op.map objects]
    | .subaction a mapping => a.concreteOps (reindex objects mapping)
  termination_by sizeOf e

  -- Fun: List of concrete operations of this action's events and nested actions
  def Action.concreteOps {Object : Type}
    (a : Action Object) (objects : Nat → Object) : List (@ConcreteOp Object) :=
    (a.events.attach.map fun ⟨e, _⟩ => e.concreteOps objects).flatten
  termination_by sizeOf a
  decreasing_by
    rename_i h
    have := List.sizeOf_lt_of_mem h;
    cases a; simp_all; omega
end

-- Fun: List of effects of an action
def Action.effects {Object : Type}
  (a : Action Object) (objects : Nat → Object) : List (Effect Object) :=
  (a.concreteOps objects).flatMap (fun op => op.toEffects)


mutual
  -- Prop: True if P holds at every action and subaction reachable from this event
  inductive Event.AllSubactions {Object : Type}
      (P : Action Object → (Nat → Object) → Prop) :
      Event Object → (Nat → Object) → Prop where
    | operation {objects : Nat → Object} {op : SymbolicOp} :
        Event.AllSubactions P (Event.operation op) objects
    | subaction {objects : Nat → Object}
        (a : Action Object) (mapping : Nat → Nat)
        (h_rec : Action.AllSubactions P a (reindex objects mapping)) :
        Event.AllSubactions P (Event.subaction a mapping) objects

  -- Prop: True if P holds at this action and every subaction reachable from it
  inductive Action.AllSubactions {Object : Type}
      (P : Action Object → (Nat → Object) → Prop) :
      Action Object → (Nat → Object) → Prop where
    | mk {a : Action Object} {objects : Nat → Object}
        (h_here : P a objects)
        (h_events : ∀ e ∈ a.events, Event.AllSubactions P e objects) :
        Action.AllSubactions P a objects
end

-- Prop: All relations in nested actions of the tx hold
def Tx.RelationsHold {Object : Type} (tx : Tx Object) : Prop :=
  Action.AllSubactions
    (fun a objects => ∀ rel ∈ a.relations, rel objects)
    tx.action tx.objects

-- Prop: The tx creates an object at internal index i
def Tx.CreatesAt {Object : Type} (tx : Tx Object) (o : Object) (i : Nat) : Prop :=
  let effects := (tx.action.effects tx.objects)
  effects[i]? = some (Effect.create o)

-- Prop: The tx creates an object at internal index i
def Tx.ConsumesAt {Object : Type} (tx : Tx Object) (o : Object) (i : Nat) : Prop :=
  let effects := (tx.action.effects tx.objects)
  effects[i]? = some (Effect.consume o)

-- Prop: The object has been created in the history
def InCreated {Object : Type} (o : Object) (h : List (Tx Object)) : Prop :=
  ∃ tx ∈ h, Effect.create o ∈ tx.action.effects tx.objects

-- Prop: The object has been consumed in the history
def InConsumed {Object : Type} (o : Object) (h : List (Tx Object)) : Prop :=
  ∃ tx ∈ h, Effect.consume o ∈ tx.action.effects tx.objects

-- The history is defined as a list of transactions, where the head is the most
-- recent transaction.
structure SystemSpec (Object : Type) [DecidableEq Object] where
  -- Properties that an implementation must define --
  -- Prop: A transaction is valid to append to a history
  ValidTx : List (Tx Object) → Tx Object → Prop
  -- Fun: returns the type of the object
  typeOf (o : Object) : ObjectType Object

  -- Theorems that an implementation must prove --

  -- Obligation: The effects in a tx are valid:
  -- create:
  -- * the object was not previously created (in a previous tx, or in a previous effect in the tx)
  -- consume:
  -- * the object was previously created (in a previous tx, or in a previous effect in the tx)
  -- * the object was not previously consumed (in a previous tx, or in a previous effect in the tx)
  validTx_effects :
    ∀ h tx, ValidTx h tx →
    ValidEffects {o | InCreated o h} {o | InConsumed o h} (tx.action.effects tx.objects)

  -- Obligation: A mutate operation is valid if it preserves the type of the object
  validTx_mutate :
    ∀ h tx, ValidTx h tx →
    ∀ op ∈ (tx.action.concreteOps tx.objects), op.TypePreserving typeOf
    -- TODO: Maybe we also want to say that the identity is preserved

  -- Obligation: A transaction is valid if all the reations in actions and subactions hold
  validTx_relations_hold :
    ∀ h tx, ValidTx h tx → Tx.RelationsHold tx

  -- Obligation: A transaction is valid if all touched objects are touched via operations
  -- in actions that belong to their type
  validTx_ops_type_match:
    ∀ h tx, ValidTx h tx →
    Action.AllSubactions (Action.OpsTypeMatch typeOf) tx.action tx.objects


-- Definitions

namespace SystemSpec

-- Prop: The history is valid.  An sound implementation must prove this proposition.
def ValidHistory {Object : Type} [DecidableEq Object] (spec : SystemSpec Object) :
    List (Tx Object) → Prop
  | [] => True
  | tx :: history => spec.ValidHistory history ∧ spec.ValidTx history tx

end SystemSpec

-- Prop: History h happened before h'
def Reaches  {Object : Type} (h h' : List (Tx Object)) : Prop :=  h.IsSuffix h'

-- Generic theorems with proofs (for all SystemSpec)

-- Theorem: If created before, created after
theorem InCreated.mono {Object : Type} {o : Object} {h h' : List (Tx Object)} :
    Reaches h h' → InCreated o h → InCreated o h' := by
  intro hreach ⟨tx, htx_mem, htx_creates⟩
  exact ⟨tx, hreach.mem htx_mem, htx_creates⟩

-- Theorem: If consumed before, consumed after
theorem InConsumed.mono {Object : Type} {o : Object} {h h' : List (Tx Object)} :
    Reaches h h' → InConsumed o h → InConsumed o h' := by
  intro hreach ⟨tx, htx_mem, htx_consumes⟩
  exact ⟨tx, hreach.mem htx_mem, htx_consumes⟩

-- Thereom: The genesis has no created or consumed objects
theorem genesis_empty {Object : Type} {o : Object} :
    (¬ InCreated o []) ∧ (¬ InConsumed o []) := by
    simp [InCreated, InConsumed]

-- TODO: Write theorems that say: things like
-- * There's no way to delete an object except by running an action that consumes it defined by its type
-- * There's no way to create an object except by running an action that creates it defined by its type
-- * There's no way to mutate an object except by running an action that mutates it defined by its type

end Spec
