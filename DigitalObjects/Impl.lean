import DigitalObjects.Spec

namespace Impl

-- Represents ~256 bit element (4 x Goldilocks prime field)
abbrev Hash := Nat

inductive Rel where
  | objsEq (i : Nat) (j : Nat)
  | objsNe (i : Nat) (j : Nat)
  deriving DecidableEq

inductive Event where
  | operation (op : Spec.SymbolicOp)
  | subaction (actionId : Hash) (mapping : List Nat)
  deriving DecidableEq

structure Action where
  relations : List Rel
  events : List Event
  deriving DecidableEq

structure ObjectType where
  actions : List Action
  deriving DecidableEq

structure Object where
  type : ObjectType
  data: List Nat
  deriving DecidableEq

def Rel.toProp (objects: Nat → Object) : Rel → Prop
  | .objsEq i j => (objects i) = (objects j)
  | .objsNe i j => (objects i) ≠ (objects j)

end Impl
