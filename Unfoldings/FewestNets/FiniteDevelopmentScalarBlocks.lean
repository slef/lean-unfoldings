module

public import Unfoldings.FewestNets.FiniteDevelopmentScalar100Data

/-! Bounded-size kernel checks of the scalar record table. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open MeshStar

def checkDevelopmentScalarBlock (records : List KeyedDevelopmentScalar) (targetDegrees : ℚ) :
    Bool :=
  records.all fun row => row.2.check certificateDenominator_pos targetDegrees

theorem checkDevelopmentScalar_of_mem_block
    {records : List KeyedDevelopmentScalar} {row : KeyedDevelopmentScalar} {targetDegrees : ℚ}
    (passes : checkDevelopmentScalarBlock records targetDegrees = true) (key : row ∈ records) :
    row.2.check certificateDenominator_pos targetDegrees = true :=
  List.all_eq_true.mp passes row key

def checkQ100DevelopmentScalarBlock (index : ℕ) : Bool :=
  match q100DevelopmentScalarChunks[index]? with
  | none => false
  | some rows => checkDevelopmentScalarBlock rows 81

end Unfoldings.FewestNets
