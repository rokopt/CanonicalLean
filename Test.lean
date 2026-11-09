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
