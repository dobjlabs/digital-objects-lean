# digital-objects-lean

A Lean 4 project to formally verify the Digital Objects system.

This project includes
- A formal specification of the system
- (WIP) A formal model of the design of our implementation
- (WIP) A formal proove that the model fulfills the specification

## Digital Objects

Digital Objects is a network system that could be succintly described as a UTXO
model with private programmable objects.

From a user perspective, a Digital Object is a piece of data that someone owns.
An object can be created, mutated and deleted.  Each object has a type, which
defines a list of actions that create/mutate/delete itself and optionally more
objects of other types when certain relations hold.

An implementation of Digital Objects exists built on the following stack:
- plonky2 is used to define a universal recursive circuit that derives valid
  statements from other valid statements via operations.
  See: https://github.com/0xPolygonZero/plonky2
- The standard that defines the behaviour of this circuit and the Input/Output
  formats is pod2.  We use the word pod to refer to an instance of pod2.
  Basically a pod is a zkproof (from the universal circuit mentioend above) and
  a list of public statements that the circuit proves to be true and the user
  wants to expose.
  See: https://github.com/0xPARC/pod2
- An object itself is represented as a merkle-tree encoded dictionary that
  fulfills TxLib predicates from a podlang library.
  See: https://github.com/dobjlabs/digital-objects-network/blob/main/libs/txlib/src/predicates/txlib.podlang
  See: https://github.com/dobjlabs/digital-objects-network/blob/main/libs/txlib/src/predicates/tx_events.podlang
- The networking part of the protocol uses Ethereum blobs to publish
  transactions which include one entry-point object action statement.  In
  practice this is a pod proof with the minimal data to reconstruct the public
  inputs.
- A server called synchronizer monitors Ethereum blobs and gets the
  transactions, verifies them and if successful updates the global state: a
  created objects tree and a nullifier tree.

## Layout

- `DigitalObjects/Spec.lean` - the formal specification.  This is
  implementation agnostic.  This part should be small and easy to understand.
  It describes the intended behaviour of the system.
- `DigitalObjects/Impl.lean` - (WIP) A formal model of our implementation/design.  Should define a
  `SystemSpec` and a computable `ValidTx`.  This part should be easy to compare
  against the real implementation, which is implemented in Rust, plonky2
  circuits and podlang.
- `DigitalObjects/Proof.lean` - (WIP) proofs discharging the `SystemSpec` obligations for the impl.
- `DigitalObjects.lean` - library root; imports the modules above.

The intended shape: `Spec` states obligations; `Impl` defines an implementation; `Proof`
proves the obligations. Keep that separation.

## Build / verify

- `lake build` — build everything (this is what CI runs via `leanprover/lean-action`).
- Toolchain is pinned in `lean-toolchain` (Lean 4.29.1); dependency is Mathlib (`lakefile.toml`).
- `autoImplicit` is intentionally **off**. Write implicit arguments explicitly with `{ ... }`.

## Workflow rules

- **I author the spec.**  When you see a way to simplify the spec or make implementation
  verification more feasible, *suggest* it with concrete before/after snippets ranked by
  impact.  
- Do **not** edit spec files or offer to apply the change — I apply changes
  manually, then ask you to review the diff.
- The goal of this project is to formally verify that our design is sound.  Our
  implementation is in Rust + plonky2 circuits + podlang but we don't aim to
  formally verify the exact implementation code.
  Instead we will reimplement the relevant parts in Lean, perhaps in a
  simplified way, and then prove that they behave according to the spec.  We
  can make reasonable simplifications in the implementation and we can even
  provide axioms to make proving easier as long as they can be clearly
  justified.  The implementation in Lean will define the functions that the
  synchronizer executes.  For this reason some of the specification
  propositions may need to be decidable/computable.

## Digital Objects implementation

Here are some details of how the Digital Objects are implemented:

- A digital object is a dictionary that is modeled as a merkle tree.  The root of the merkle tree defines a unique id of the object.  We'll call this unique id the object root.
- There are three main operations for objects: create, mutate, delete.
- The network defines a global state via consensus that contains two virtual sets: created and deleted.
- All created objects are registered in the created set (by their object root).
  The created set exists is materialized by the synchronizer.
- All deleted objects are registered in the deleted set.  The deleted set is
  not materalized by the syncrhonizer for privacy reasons.  Instead the design
  uses a nullifier tree.  Only the owner of an object can prove the relation
  between the object root and its nullifier.
- The user defines actions that create/mutate/delete objects via modules in podlang.  Here's an example
```
use module 0x845770b5494c1793e749c7110c0db3e0faefd0d675cd11f83901432dc08dccd2 as tx
use intro Vdf(count, input, output) from 0xab82223f501b5056f458f063eb2fc073f8ac01f2ea178a3a2303394fec6828a0
use intro LtEqU256(lhs, rhs) from 0xe0595e5c75467e5a27bd30fa48a45e1dcc66a327076e5ce7c02ce33dfe357311

record FindLogOut = (log)
record FindLogInitials = (log)
record CraftWoodIn = (log)
record CraftWoodOut = (wood)
record CraftSticksIn = (wood)
record CraftSticksOut = (stick_a, stick_b)
record CraftSticksChain = (step_0, step_1)
record CraftSticksInitials = (stick_a, stick_b)
record CraftWoodPickIn = (wood, stick)
record CraftWoodPickOut = (pick)
record CraftWoodPickChain = (step_0, step_1)
record CraftWoodPickInitials = (pick)
record UseWoodPickIn = (wood_pick)
record UseWoodPickOut = (wood_pick)
record MineStoneWithWoodPickOut = (stone)
record MineStoneWithWoodPickInitials = (stone)

// Actions

FindLog(out FindLogOut, chain0, chain, private: log0, work, initials FindLogInitials) = AND(
  Vdf(3, log0, work)
  DictUpdate(initials.log, log0, "work", work)
  tx::TxInsert(chain, chain0, initials.log, out.log, @self_predicate(IsLog))
)

CraftWood(in CraftWoodIn, out CraftWoodOut, chain0, chain, private: chain1, wood0, wood1, key) = AND(
  DictUpdate(wood1, wood0, "key", key)
  LtEqU256(wood1, Raw(0x0020000000000000000000000000000000000000000000000000000000000000))
  tx::TxDelete(chain1, chain0, in.log, @self_predicate(IsLog))
  tx::TxInsert(chain, chain1, wood1, out.wood, @self_predicate(IsWood))
)

CraftSticks(in CraftSticksIn, out CraftSticksOut, chain0, chain, private: chain_steps CraftSticksChain, initials CraftSticksInitials) = AND(
  tx::TxDelete(chain_steps.step_0, chain0, in.wood, @self_predicate(IsWood))
  tx::TxInsert(chain_steps.step_1, chain_steps.step_0, initials.stick_a, out.stick_a, @self_predicate(IsStick))
  tx::TxInsert(chain, chain_steps.step_1, initials.stick_b, out.stick_b, @self_predicate(IsStick))
)

CraftWoodPick(in CraftWoodPickIn, out CraftWoodPickOut, chain0, chain, private: chain_steps CraftWoodPickChain, initials CraftWoodPickInitials) = AND(
  DictContains(initials.pick, "durability", 100)
  tx::TxDelete(chain_steps.step_0, chain0, in.wood, @self_predicate(IsWood))
  tx::TxDelete(chain_steps.step_1, chain_steps.step_0, in.stick, @self_predicate(IsStick))
  tx::TxInsert(chain, chain_steps.step_1, initials.pick, out.pick, @self_predicate(IsWoodPick))
)

UseWoodPick(in UseWoodPickIn, out UseWoodPickOut, chain0, chain, private: wood_pick0, wood_pick1, wood_pick2, durability, key, work) = AND(
  ArrayContains(in, UseWoodPickIn::wood_pick, wood_pick0)
  Gt(wood_pick0.durability, 0)
  Sum(durability, 1, wood_pick0.durability)
  DictUpdate(wood_pick0, "durability", durability, wood_pick1)
  DictUpdate(wood_pick1, "key", key, wood_pick2)
  Vdf(10, wood_pick2, work)
  DictUpdate(wood_pick2, "work", work, out.wood_pick)
  tx::TxMutate(chain, chain0, out.wood_pick, wood_pick0, @self_predicate(IsWoodPick))
)

MineStoneWithWoodPick(out MineStoneWithWoodPickOut, chain0, chain, private: chain1, _UseWoodPick_in_0 UseWoodPickIn, _UseWoodPick_out_0 UseWoodPickOut, initials MineStoneWithWoodPickInitials) = AND(
  UseWoodPick(_UseWoodPick_in_0, _UseWoodPick_out_0, chain0, chain1)
  tx::TxInsert(chain, chain1, initials.stone, out.stone, @self_predicate(IsStone))
)

// Bridges

IsLogFromFindLog(state, chain0, chain, private: out FindLogOut) = AND(
  ArrayContains(out, FindLogOut::log, state)
  FindLog(out, chain0, chain)
)

IsLogFromCraftWood(state, chain0, chain, private: in CraftWoodIn, out CraftWoodOut) = AND(
  ArrayContains(in, CraftWoodIn::log, state)
  CraftWood(in, out, chain0, chain)
)

IsWoodFromCraftWood(state, chain0, chain, private: in CraftWoodIn, out CraftWoodOut) = AND(
  ArrayContains(out, CraftWoodOut::wood, state)
  CraftWood(in, out, chain0, chain)
)

IsWoodFromCraftSticks(state, chain0, chain, private: in CraftSticksIn, out CraftSticksOut) = AND(
  ArrayContains(in, CraftSticksIn::wood, state)
  CraftSticks(in, out, chain0, chain)
)

IsStickFromCraftSticks_stick_a(state, chain0, chain, private: in CraftSticksIn, out CraftSticksOut) = AND(
  ArrayContains(out, CraftSticksOut::stick_a, state)
  CraftSticks(in, out, chain0, chain)
)

IsStickFromCraftSticks_stick_b(state, chain0, chain, private: in CraftSticksIn, out CraftSticksOut) = AND(
  ArrayContains(out, CraftSticksOut::stick_b, state)
  CraftSticks(in, out, chain0, chain)
)

IsWoodFromCraftWoodPick(state, chain0, chain, private: in CraftWoodPickIn, out CraftWoodPickOut) = AND(
  ArrayContains(in, CraftWoodPickIn::wood, state)
  CraftWoodPick(in, out, chain0, chain)
)

IsStickFromCraftWoodPick(state, chain0, chain, private: in CraftWoodPickIn, out CraftWoodPickOut) = AND(
  ArrayContains(in, CraftWoodPickIn::stick, state)
  CraftWoodPick(in, out, chain0, chain)
)

IsWoodPickFromCraftWoodPick(state, chain0, chain, private: in CraftWoodPickIn, out CraftWoodPickOut) = AND(
  ArrayContains(out, CraftWoodPickOut::pick, state)
  CraftWoodPick(in, out, chain0, chain)
)

IsWoodPickFromUseWoodPick(state, chain0, chain, private: in UseWoodPickIn, out UseWoodPickOut) = AND(
  ArrayContains(out, UseWoodPickOut::wood_pick, state)
  UseWoodPick(in, out, chain0, chain)
)

IsStoneFromMineStoneWithWoodPick(state, chain0, chain, private: out MineStoneWithWoodPickOut) = AND(
  ArrayContains(out, MineStoneWithWoodPickOut::stone, state)
  MineStoneWithWoodPick(out, chain0, chain)
)

// Classes

IsLog(state, chain0, chain) = OR(
  IsLogFromFindLog(state, chain0, chain)
  IsLogFromCraftWood(state, chain0, chain)
)

IsWood(state, chain0, chain) = OR(
  IsWoodFromCraftWood(state, chain0, chain)
  IsWoodFromCraftSticks(state, chain0, chain)
  IsWoodFromCraftWoodPick(state, chain0, chain)
)

IsStick(state, chain0, chain) = OR(
  IsStickFromCraftSticks_stick_a(state, chain0, chain)
  IsStickFromCraftSticks_stick_b(state, chain0, chain)
  IsStickFromCraftWoodPick(state, chain0, chain)
)

IsWoodPick(state, chain0, chain) = OR(
  IsWoodPickFromCraftWoodPick(state, chain0, chain)
  IsWoodPickFromUseWoodPick(state, chain0, chain)
)

IsStone(state, chain0, chain) = OR(
  IsStoneFromMineStoneWithWoodPick(state, chain0, chain)
)
```
- In the above example, an object type would be `Log` and it's identified by the predicate `IsLog`.
- To run an action the user build a top level action statement (which fulfills an action predicate) via pod and then proves the `TxFinalized` predicate from TxLib, which is supposed to guarantee some properties over the created and nullifier sets.  A pod is built that only exposes the `TxFinalized` statement.  This pod is sent the Ethereum Network in a blob.  Then the synchronizer decodes the pods in blobs and checks things like:
  - Verify the zkproof with a reconstructed public input, assuming a single statement of the type `TxFinalized`
  - Append to the nullifier set
  - Append to the created set
