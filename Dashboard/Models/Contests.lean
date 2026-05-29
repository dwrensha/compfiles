import Batteries.Data.String.Basic
import Lean.Data.NameMap.Basic
import SSG.Html

/-!
# Contest Metadata

Data and identification utilities for each contest (IMO, USAMO, etc.).
To add a new contest, define a new `Contest` instance and add it to `allContests`.
-/

/-- Index for identifying individual problems within a contest.
Currently `Nat × Nat` covers (year, problemNum) and (day, problemNum). -/
abbrev ContestIndex := Nat × Nat

/-- A link to an external resource (solution writeup, official site, etc.). -/
structure WriteupLink where
  url : String
  text : String
  deriving Inhabited

structure Contest (idxType subIdxType : Type := Nat)
  [Ord idxType] [Ord subIdxType] where
  fullName : String
  problems : List (idxType × subIdxType)
  /--
  Prefer name from `NameMap` for consistency.
  This should be `idxType → subIdxType → Lean.Name → Bool`,
  keep this for now due to performance?
  -/
  toName : idxType → subIdxType → Lean.Name
  externalUrls : idxType → subIdxType → List WriteupLink
  /--
  Providing the count of all included problems
  -/
  desc : Nat → List Html

namespace Contest

variable {idx subIdx : Type} [Ord idx] [Ord subIdx]

def filterProblemCount (c : Contest idx subIdx) (f : idx → subIdx → Bool) : Nat :=
  c.problems.foldl (fun count ⟨i, s⟩ => count + if f i s then 1 else 0) 0

/--
All problems listed (including not yet formalized ones)
-/
def problemCount (c : Contest idx subIdx) : Nat := c.filterProblemCount fun _ _ => true

def hasProblemName (c : Contest idx subIdx) (name : Lean.Name) : Bool :=
  c.problems.any fun ⟨idx, subIdx⟩ ↦ c.toName idx subIdx == name

def mergeNeighbors (c : Contest idx subIdx) : List <| idx × List subIdx :=
  c.problems.mergeSort (
    fun a b ↦ match compare a.1 b.1 with
    | .lt => true
    | .eq => compare a.2 b.2 |>.isLE
    | .gt => false
  ) |>.foldr (init := [])
    fun ⟨idx, subIdx⟩ acc ↦ match acc with
    | [] => [(idx, [subIdx])]
    | (curIdx, subs) :: rest =>
      if compare idx curIdx |>.isEq then (curIdx, subIdx :: subs) :: rest
      else (idx, [subIdx]) :: acc

end Contest

def fromCounts (counts : List (Nat × Nat)) : List (Nat × Nat) :=
  counts.flatMap fun ⟨year, count⟩ => (List.range count).map fun i => (year, i + 1)
