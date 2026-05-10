import Dashboard.Models.Contests
import ProblemExtraction

structure ProblemMeta where
  metadata : ProblemExtraction.ProblemFileMetadata
  informal : String
  problemSrc : String
  solutionSrc : String
  proved : Bool

structure ProblemInfo
  {idxType subIdxType : Type} [Ord idxType] [Ord subIdxType]
  (contest : Contest idxType subIdxType)
  where
  idx : idxType
  subIdx : subIdxType
  detail : Option ProblemMeta

namespace ProblemInfo

variable {idxType subIdxType : Type} [Ord idxType] [Ord subIdxType]
  (C : Contest idxType subIdxType)

def leanName (p : ProblemInfo C) : Lean.Name := C.toName p.idx p.subIdx

end ProblemInfo

namespace Contest

variable {idxType subIdxType : Type} [Ord idxType] [Ord subIdxType]

def formalizedCount (c : Contest idxType subIdxType)
  (mds : Lean.NameMap ProblemMeta) : Nat := c.filterProblemCount <|
  fun idx subIdx ↦ mds.get? (c.toName idx subIdx) |>.isSome

def solvedCount (c : Contest idxType subIdxType)
  (mds : Lean.NameMap ProblemMeta) : Nat := c.filterProblemCount <|
  fun idx subIdx ↦
    if let .some pm := mds.get? (c.toName idx subIdx) then
      pm.proved
    else false

end Contest
