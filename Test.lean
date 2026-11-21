import Canonical

/--
info: Try this:
  [apply] exact Nat.zero
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example : Nat := by canonical

open Lean Meta DiscrTree

-- Synthetic simp entries isolate traversal and priority filtering from elaboration.
private def originLeaf : Trie SimpTheorem := .node #[
  { proof := mkConst ``True.intro, origin := .decl `kept, rfl := false },
  { proof := mkConst ``True.intro, origin := .decl `lowPriority, rfl := false,
    priority := 0 }
] #[]

private def allowedConstants : NameSet := .ofList [`Allowed]

-- Compressed edges must retain the same restrictions as ordinary child edges.
#guard Canonical.getOrigins allowedConstants
  (.chain (.const `Allowed 0) originLeaf) == #[.decl `kept]
#guard Canonical.getOrigins allowedConstants
  (.chain (.const `Blocked 0) originLeaf) == #[]
#guard Canonical.getOrigins allowedConstants
  (.chain (.proj `Allowed 0 0) originLeaf) == #[.decl `kept]
#guard Canonical.getOrigins allowedConstants
  (.chain (.proj `Blocked 0 0) originLeaf) == #[]
#guard Canonical.getOrigins allowedConstants (.chain .arrow originLeaf) == #[]
#guard Canonical.getOrigins allowedConstants (.chain .star originLeaf) == #[.decl `kept]
#guard Canonical.getOrigins allowedConstants
  (.chain (.const `Allowed 0) (.chain (.const `Blocked 0) originLeaf)) == #[]

private def keptThm : SimpTheorem :=
  { proof := mkConst ``True.intro, origin := .decl `kept, rfl := false }

private def lowPriorityThm : SimpTheorem :=
  { keptThm with origin := .decl `lowPriority, priority := 0 }

-- A `suffix` stands for a chain of its remaining keys ending in its single value, so each of
-- those keys and the value's priority must be checked as they would be along such a chain.
#guard Canonical.getOrigins allowedConstants (.suffix #[] 0 keptThm) == #[.decl `kept]
#guard Canonical.getOrigins allowedConstants (.suffix #[] 0 lowPriorityThm) == #[]
#guard Canonical.getOrigins allowedConstants
  (.suffix #[.const `Allowed 0, .star] 0 keptThm) == #[.decl `kept]
#guard Canonical.getOrigins allowedConstants
  (.suffix #[.const `Allowed 0, .star] 0 lowPriorityThm) == #[]
#guard Canonical.getOrigins allowedConstants
  (.suffix #[.const `Allowed 0, .const `Blocked 0] 0 keptThm) == #[]
#guard Canonical.getOrigins allowedConstants
  (.suffix #[.const `Allowed 0, .arrow] 0 keptThm) == #[]
-- Keys before the start index were consumed further up the tree and are not part of the path.
#guard Canonical.getOrigins allowedConstants
  (.suffix #[.const `Blocked 0, .const `Allowed 0] 1 keptThm) == #[.decl `kept]
#guard Canonical.getOrigins allowedConstants
  (.chain (.const `Allowed 0) (.suffix #[.const `Blocked 0] 0 keptThm)) == #[]

-- A `lazy` node stands for the trie it merges to on first access.
#guard Canonical.getOrigins allowedConstants
  (.lazy (Thunk.mk fun _ => .chain (.const `Allowed 0) originLeaf)) == #[.decl `kept]
#guard Canonical.getOrigins allowedConstants
  (.lazy (Thunk.mk fun _ => .chain (.const `Blocked 0) originLeaf)) == #[]
#guard Canonical.getOrigins allowedConstants
  (.lazy (Thunk.mk fun _ => .suffix #[.const `Allowed 0] 0 keptThm)) == #[.decl `kept]
#guard Canonical.getOrigins allowedConstants
  (.chain (.const `Allowed 0) (.lazy (Thunk.mk fun _ => originLeaf))) == #[.decl `kept]

-- Canonical suggests a replacement proof and deliberately admits the original goal.
/--
info: Try this:
  [apply] exact fun a a_1 ↦ a.2 (a.1 a_1)
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (P Q R : Prop) : ((P → Q) ∧ (Q → R)) → P → R := by
  canonical (ai := false)
