import DigitalObjects.Spec

-- Represents ~256 bit element (4 x Goldilocks prime field)
abbrev Hash := Nat

structure ObjectDict where
  raw : Hash
  type : ObjectType ObjectDict
