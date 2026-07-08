-- Simplified predicates with equivalence proofs.
-- The content of this file is mostly LLM generated

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import DigitalObjects.TxLib.Predicates
import DigitalObjects.Impl

namespace TxLib

--
-- # InputsGrounded ↔ InputsGroundedSimple
--
-- How it's structured
--
-- Faithful → simple (toSimple family): structural recursion on the derivation.
-- Single/Pair aren't recursive, so they're standalone theorems before the
-- mutual block — only InputsGrounded ↔ InputsGroundedRecursive need mutual
-- recursion (mirroring which podlang predicates actually recurse). The obtain
-- ⟨-, rfl⟩ patterns see straight through your SetInsert def to its ∉ ∧ insert
-- body, substituting the set equations; then simp turns x ∈ insert … (insert …
-- ∅) into the disjunction of cases.
--
-- Simple → faithful (ofSimple): well-founded recursion on inputs.card with the
-- three-way split card = 0 / = 1 / > 1:
-- - 0 → empty; 1 → single (Finset.card_eq_one gives inputs = {x}).
-- - > 1 → Finset.one_lt_card yields distinct a ≠ b, both members; prev :=
--   (inputs.erase b).erase a; the two Finset.insert_erase rewrites reassemble
--   inputs = insert b (insert a prev). Note how your strict SetInsert pays off
--   here: the ∉ obligations are exactly Finset.notMem_erase — the erase
--   decomposition produces precisely the disjointness facts the constructor
--   demands.
-- - termination_by inputs.card + decreasing_by: two card_erase_of_mem facts
--   and omega — same recipe as your other termination proofs.
--
-- Two findings worth noting
--
-- 1. pair is confirmed dead weight in this direction: ofSimple never
--    constructs it — even-cardinality inputs bottom out through recursive → … →
--    empty. So the equivalence also documents that Pair is a pure
--    prover-optimization (it's still needed in toSimple, i.e. its existence
--    doesn't break soundness — which is the actual claim worth having on record).
-- 2. Mathlib name drift bit twice during development, worth remembering for
--    future proofs on this toolchain: it's Finset.notMem_empty/notMem_erase
--    (camelCase notMem, post-rename), and Finset.card needs its own import
--    (Mathlib.Data.Finset.Card) — Finset.Basic doesn't pull it in.

-- helper: indexed lookup implies membership
private theorem mem_of_getElem? {α : Type} {l : List α} {i : Nat} {a : α}
    (h : l[i]? = some a) : a ∈ l := by
  rw [List.getElem?_eq_some_iff] at h
  obtain ⟨hlt, rfl⟩ := h
  exact List.getElem_mem hlt

-- helper: membership implies an indexed lookup
private theorem mem_getElem? {α : Type} {l : List α} {a : α}
    (h : a ∈ l) : ∃ i : Nat, l[i]? = some a := by
  obtain ⟨i, hlt, rfl⟩ := List.mem_iff_getElem.mp h
  exact ⟨i, by simp [hlt]⟩

theorem InputsGroundedSingle.toSimple {inputs : Finset Impl.Object} {created : List Impl.Object}
    (h : InputsGroundedSingle inputs created) : InputsGroundedSimple inputs created := by
  obtain ⟨_, _, input, index, h1, ⟨-, rfl⟩⟩ := h
  intro x hx
  simp at hx
  subst hx
  exact mem_of_getElem? h1

theorem InputsGroundedPair.toSimple {inputs : Finset Impl.Object} {created : List Impl.Object}
    (h : InputsGroundedPair inputs created) : InputsGroundedSimple inputs created := by
  obtain ⟨_, _, first, second, set_first, i, j, h1, ⟨-, rfl⟩, h3, ⟨-, rfl⟩⟩ := h
  intro x hx
  simp at hx
  rcases hx with rfl | rfl
  · exact mem_of_getElem? h3
  · exact mem_of_getElem? h1

mutual
  theorem InputsGrounded.toSimple {inputs : Finset Impl.Object} {created : List Impl.Object}
      (h : InputsGrounded inputs created) : InputsGroundedSimple inputs created :=
    match h with
    | .empty _ _ h => by subst h; intro x hx; simp at hx
    | .single _ _ h => h.toSimple
    | .pair _ _ h => h.toSimple
    | .recursive _ _ h => h.toSimple

  theorem InputsGroundedRecursive.toSimple {inputs : Finset Impl.Object} {created : List Impl.Object}
      (h : InputsGroundedRecursive inputs created) : InputsGroundedSimple inputs created :=
    match h with
    | .mk _ _ first second mid prev i j h1 h2 h3 h4 h5 => by
      obtain ⟨-, rfl⟩ := h2
      obtain ⟨-, rfl⟩ := h4
      have ih := h5.toSimple
      intro x hx
      simp at hx
      rcases hx with rfl | rfl | hx
      · exact mem_of_getElem? h3
      · exact mem_of_getElem? h1
      · exact ih x hx
end

theorem InputsGrounded.ofSimple (inputs : Finset Impl.Object) (created : List Impl.Object)
    (h : InputsGroundedSimple inputs created) : InputsGrounded inputs created := by
  obtain hc | hc | hc : inputs.card = 0 ∨ inputs.card = 1 ∨ 1 < inputs.card := by omega
  · exact .empty _ _ (Finset.card_eq_zero.mp hc)
  · obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hc
    obtain ⟨i, hi⟩ := mem_getElem? (h x (Finset.mem_singleton_self x))
    exact .single _ _ (.mk _ _ x i hi ⟨Finset.notMem_empty x, by simp⟩)
  · obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hc
    have hab' : a ∈ inputs.erase b := Finset.mem_erase.mpr ⟨hab, ha⟩
    obtain ⟨i, hi⟩ := mem_getElem? (h a ha)
    obtain ⟨j, hj⟩ := mem_getElem? (h b hb)
    have hrec : InputsGrounded ((inputs.erase b).erase a) created :=
      InputsGrounded.ofSimple _ created fun x hx =>
        h x (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx))
    refine .recursive _ _ (.mk _ _ a b _ _ i j hi ⟨Finset.notMem_erase a _, rfl⟩ hj
      ⟨?_, ?_⟩ hrec)
    · rw [Finset.insert_erase hab']
      exact Finset.notMem_erase b inputs
    · rw [Finset.insert_erase hab', Finset.insert_erase hb]
termination_by inputs.card
decreasing_by
  have h1 : (inputs.erase b).card = inputs.card - 1 := Finset.card_erase_of_mem hb
  have h2 : ((inputs.erase b).erase a).card = (inputs.erase b).card - 1 :=
    Finset.card_erase_of_mem hab'
  omega

theorem inputsGrounded_iff_inputsGroundedSimple (inputs : Finset Impl.Object) (created : List Impl.Object) :
    InputsGrounded inputs created ↔ InputsGroundedSimple inputs created :=
  ⟨InputsGrounded.toSimple, InputsGrounded.ofSimple inputs created⟩

end TxLib
