-- Simplified predicates with equivalence proofs.
-- The content of this file is mostly LLM generated, including comments

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import DigitalObjects.TxLib.Predicates
import DigitalObjects.Impl

namespace TxLib
open Impl (Object Nullifier Chain)

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
-- Worth noting: pair is confirmed dead weight in this direction: ofSimple
-- never constructs it — even-cardinality inputs bottom out through recursive →
-- … → empty. So the equivalence also documents that Pair is a pure
-- prover-optimization (it's still needed in toSimple, i.e. its existence
-- doesn't break soundness — which is the actual claim worth having on record).

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

theorem InputsGroundedSingle.toSimple {inputs : Finset Object} {created : List Object}
    (h : InputsGroundedSingle inputs created) : InputsGroundedSimple inputs created := by
  obtain ⟨_, _, input, index, h1, ⟨-, rfl⟩⟩ := h
  intro x hx
  simp at hx
  subst hx
  exact mem_of_getElem? h1

theorem InputsGroundedPair.toSimple {inputs : Finset Object} {created : List Object}
    (h : InputsGroundedPair inputs created) : InputsGroundedSimple inputs created := by
  obtain ⟨_, _, first, second, set_first, i, j, h1, ⟨-, rfl⟩, h3, ⟨-, rfl⟩⟩ := h
  intro x hx
  simp at hx
  rcases hx with rfl | rfl
  · exact mem_of_getElem? h3
  · exact mem_of_getElem? h1

mutual
  theorem InputsGrounded.toSimple {inputs : Finset Object} {created : List Object}
      (h : InputsGrounded inputs created) : InputsGroundedSimple inputs created :=
    match h with
    | .empty _ _ h => by subst h; intro x hx; simp at hx
    | .single _ _ h => h.toSimple
    | .pair _ _ h => h.toSimple
    | .recursive _ _ h => h.toSimple

  theorem InputsGroundedRecursive.toSimple {inputs : Finset Object} {created : List Object}
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

theorem InputsGrounded.ofSimple (inputs : Finset Object) (created : List Object)
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

theorem inputsGrounded_iff_inputsGroundedSimple (inputs : Finset Object) (created : List Object) :
    InputsGrounded inputs created ↔ InputsGroundedSimple inputs created :=
  ⟨InputsGrounded.toSimple, InputsGrounded.ofSimple inputs created⟩

--
-- # ReplayActions ↔ ReplayActionsSimple
--
-- How it works
--
-- ReplayActionInsert.toReplayAction — the heart of the proof. It builds the
-- 5-statement long derivation from the 2-statement fast path, supplying
-- ReplayAction's four private Txs explicitly (scope_mid, inner_tx, end_tx, mid
-- as concrete {before_tx with …} updates). Everything then discharges by rfl
-- or by reusing the fast path's own hypotheses unchanged — most notably h4 :
-- guard.Valid new before_chain after_chain is accepted where ReplayInsert
-- demands guard.Valid new inner_tx.chain_start inner_tx.chain_end, because
-- after the two structure updates those projections reduce definitionally to
-- before_chain/after_chain. That defeq is precisely the podlang comment's
-- claim ("the public args ARE the action's chain scope") — the model validates
-- it, no rewriting needed. Same for the final h3: the long path's after_tx =
-- {mid with nullifiers := end_tx.nullifiers} reduces to the fast path's
-- after_tx = {before_tx with live := new_live}.
--
-- toSimple — the mutual pair mirrors which predicates are actually mutually
-- recursive (ReplayActions ↔ ReplayActionsStep), same pattern as the
-- InputsGrounded proofs: action → TransGen.single, actions_step →
-- TransGen.head, and action_insert → TransGen.single via the fast-path lemma.
--
-- ofSimple — stated over pairs p q : Tx × Chain so the TransGen motive is
-- directly usable, then head_induction_on peels one ReplayAction at a time
-- into action/actions_step constructors. The final iff applies it at literal
-- pairs, where p.1/p.2 reduce, so no repackaging lemma is needed.

-- Soundness of the K=1 fast path: everything ReplayActionInsert proves, the
-- long path (ReplayAction → ReplayContents → ReplayElement → ReplayInsert)
-- proves as well.  This discharges the claim made in the podlang comment:
-- the guard sees the same chain bounds either way.
theorem ReplayActionInsert.toReplayAction
    {before_tx after_tx : Tx} {before_chain after_chain : Chain}
    (h : ReplayActionInsert before_tx after_tx before_chain after_chain) :
    ReplayAction before_tx after_tx before_chain after_chain := by
  obtain ⟨_, _, _, _, new, new_live, guard, h1, h2, h3, h4⟩ := h
  exact .mk _ _ _ _
    {before_tx with chain_start := before_chain}
    {before_tx with chain_start := before_chain, chain_end := after_chain}
    {before_tx with chain_start := before_chain, chain_end := after_chain, live := new_live}
    {before_tx with live := new_live}
    rfl rfl
    (.element _ _ _ _ (.insert _ _ _ _ (.mk _ _ _ _ new new_live guard h1 h2 rfl h4)))
    rfl h3

mutual
  theorem ReplayActions.toSimple {before_tx after_tx : Tx} {before_chain after_chain : Chain}
      (h : ReplayActions before_tx after_tx before_chain after_chain) :
      ReplayActionsSimple before_tx after_tx before_chain after_chain :=
    match h with
    | .action _ _ _ _ h => Relation.TransGen.single h
    | .actions_step _ _ _ _ h => h.toSimple
    | .action_insert _ _ _ _ h => Relation.TransGen.single h.toReplayAction

  theorem ReplayActionsStep.toSimple {before_tx after_tx : Tx} {before_chain after_chain : Chain}
      (h : ReplayActionsStep before_tx after_tx before_chain after_chain) :
      ReplayActionsSimple before_tx after_tx before_chain after_chain :=
    match h with
    | .mk _ _ _ _ _ _ h1 h2 => Relation.TransGen.head h1 h2.toSimple
end

theorem ReplayActions.ofSimple {p q : Tx × Chain}
    (h : Relation.TransGen (fun before after : Tx × Chain => ReplayAction before.1 after.1 before.2 after.2) p q) :
    ReplayActions p.1 q.1 p.2 q.2 := by
  induction h using Relation.TransGen.head_induction_on with
  | single h => exact .action _ _ _ _ h
  | head h1 _ ih => exact .actions_step _ _ _ _ (.mk _ _ _ _ _ _ h1 ih)

theorem replayActions_iff_replayActionsSimple (before_tx after_tx : Tx) (before_chain after_chain : Chain) :
    ReplayActions before_tx after_tx before_chain after_chain ↔
      ReplayActionsSimple before_tx after_tx before_chain after_chain :=
  ⟨ReplayActions.toSimple, ReplayActions.ofSimple⟩


theorem replayContents_iff_replayContentsSimple (before_tx after_tx : Tx) (before_chain after_chain : Chain) :
    ReplayActions before_tx after_tx before_chain after_chain ↔
      ReplayContentsSimple before_tx after_tx before_chain after_chain :=
  by sorry

end TxLib
