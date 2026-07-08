import DigitalObjects.Spec

namespace Impl

-- Represents ~256 bit element (4 x Goldilocks prime field)
abbrev Hash := Nat

inductive Rel where
  | objsEq (i : Nat) (j : Nat)
  | objsNe (i : Nat) (j : Nat)
  deriving DecidableEq

mutual
  inductive Event where
    | operation (op : Spec.SymbolicOp)
    | subaction (a : Action) (mapping : List Nat)

  structure Action where
    relations : List Rel
    events : List Event
end

-- The automatic derivation of DecidableEq for recursive Event/Action doesn't
-- go through, so we manually define it here.  This is a very mechanical
-- process.  DecidableEq carries the equality result and the proof.
mutual
  def Event.decEq : (a b : Event) → Decidable (a = b)
    | .operation x, .operation y => decidable_of_iff (x = y) (by simp)
    | .operation _, .subaction _ _ => .isFalse nofun
    | .subaction _ _, .operation _ => .isFalse nofun
    | .subaction a m, .subaction a' m' =>
      have := Action.decEq a a'
      decidable_of_iff (a = a' ∧ m = m') (by simp)
  termination_by a _ => sizeOf a

  def Event.decEqList : (as bs : List Event) → Decidable (as = bs)
    | [], [] => .isTrue rfl
    | [], _ :: _ => .isFalse nofun
    | _ :: _, [] => .isFalse nofun
    | a :: as, b :: bs =>
      have := Event.decEq a b
      have := Event.decEqList as bs
      decidable_of_iff (a = b ∧ as = bs) (by simp)
  termination_by as _ => sizeOf as

  def Action.decEq : (a b : Action) → Decidable (a = b)
    | ⟨r1, e1⟩, ⟨r2, e2⟩ =>
      have := Event.decEqList e1 e2
      decidable_of_iff (r1 = r2 ∧ e1 = e2) (by simp)
  termination_by a _ => sizeOf a
end

instance : DecidableEq Event := Event.decEq
instance : DecidableEq Action := Action.decEq

structure ObjectType where
  actions : List Action
  deriving DecidableEq

structure Object where
  type : ObjectType
  key : Nat
  data : List Nat
  deriving DecidableEq

-- There's a 1:1 mapping between nullifier and object state.  The real
-- implementation of the nullifier is `H(H(obj, obj.key), "txlib-nullifier-v1")`
-- which is injective modulo collision resistance, and we idealize it as the
-- identity for simplicity.  Currently we don't cover privacy in this model, so
-- we skip the property of "derivable only with knowledge of the key".
structure Nullifier where
  object : Object
  deriving DecidableEq

def Object.nullify (o : Object) : Nullifier :=
  ⟨o⟩

def Rel.toProp (r : Rel) (objects : Nat → Object) : Prop :=
  match r with
  | .objsEq i j => (objects i) = (objects j)
  | .objsNe i j => (objects i) ≠ (objects j)

mutual
  def Event.toSpec (e : Event) : (Spec.Event Object) :=
    match e with
    | .operation op => .operation op
    -- An index beyond the mapping lists falls back to 0
    | .subaction a mapping => .subaction a.toSpec (fun i => mapping.getD i 0)
  termination_by sizeOf e

  def Action.toSpec (a : Action) : (Spec.Action Object) :=
    { relations := a.relations.map Rel.toProp
      events := a.events.map Event.toSpec }
  termination_by sizeOf a
  decreasing_by
    rename_i h
    have := List.sizeOf_lt_of_mem h
    cases a; simp_all; omega
end

def ObjectType.toSpec (t : ObjectType) : (Spec.ObjectType Object) :=
  { actions := t.actions.map Action.toSpec }


end Impl
