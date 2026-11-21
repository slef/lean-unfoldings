module

public import Unfoldings.FewestNets.CheckedRoutingChartCache
public import Unfoldings.FewestNets.CheckedMeshNormalization
public import Unfoldings.FewestNets.CheckedRoutingCell
public import Unfoldings.FewestNets.CheckedDevelopmentCellTilt

/-! A uniform typed certificate for each face, seam, or vertex record. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open MeshStar

namespace MeshRecordKey

/-- The number of sides minus one. Both nonvertex families are hexagons. -/
def sidePred : MeshRecordKey → ℕ
  | .vertex => 4
  | _ => 5

def model (q : ℕ) (key : MeshRecordKey) : MeshStar (key.sidePred + 1) :=
  match key with
  | .face i j => MeshStar.face q i j
  | .seam i => MeshStar.seam q i
  | .vertex => pentagon q

def checkedModel (q : ℕ) (key : MeshRecordKey) :
    MeshStar.Checked certificateDenominator (key.model q) :=
  match key with
  | .face i j => checkFace certificateDenominator_pos q i j
  | .seam i => checkSeam certificateDenominator_pos q i
  | .vertex => checkPentagon certificateDenominator_pos q

end MeshRecordKey

/-- The two positive physical scales used by the paper's saved records. -/
inductive RoutingRadiusMode
  | derivative
  | maximum

namespace RoutingRadiusMode

variable {n : ℕ} (mode : RoutingRadiusMode) (q : ℕ) (M : MeshStar (n + 1))
  (checked : MeshStar.Checked certificateDenominator M)

def radius : ℝ :=
  match mode with
  | .derivative => M.derivativeRadius q
  | .maximum => M.maximumRadius

def checkedRadius : CheckedReal certificateDenominator (mode.radius q M) :=
  match mode with
  | .derivative => checked.derivativeRadius certificateDenominator_pos q
  | .maximum => checked.maximumRadius certificateDenominator_pos

def checkedCorner (k : Fin (n + 1)) :
    CheckedPlane certificateDenominator ((mode.radius q M)⁻¹ • (M).physicalVertex k) :=
  match mode with
  | .derivative => checked.derivativeNormalizedVertex certificateDenominator_pos q k
  | .maximum => checked.maximumNormalizedVertex certificateDenominator_pos k

def checkedOffset (k : Fin (n + 1)) :
    CheckedReal certificateDenominator ((M).physicalSideOffset k / mode.radius q M) :=
  match mode with
  | .derivative => checked.derivativeNormalizedSideOffset certificateDenominator_pos q k
  | .maximum => checked.maximumNormalizedSideOffset certificateDenominator_pos k

end RoutingRadiusMode

/-- Numerical witnesses carry their geometric key. The body size is allowed
to vary between records with the same number of sides. -/
structure MeshRoutingRecord (q : ℕ) (key : MeshRecordKey) where
  scalar : DevelopmentScalarRecord
  mode : RoutingRadiusMode
  bodyPred : ℕ
  chart : RoutingChartCache certificateDenominator (key.sidePred + 1)
  witness : RoutingCellWitness (key.sidePred + 1) (bodyPred + 1)

namespace MeshRoutingRecord

variable {q : ℕ} {key : MeshRecordKey} (record : MeshRoutingRecord q key)

local notation "M" => key.model q
local notation "checked" => key.checkedModel q

def checkChart : Bool :=
  record.chart.check (record.mode.checkedCorner q M checked)
    ((checked).physicalSideNormal certificateDenominator_pos)
    (record.mode.checkedOffset q M checked)

def checkedCorner (pass : record.checkChart = true) (k : Fin (key.sidePred + 1)) :
    CheckedPlane certificateDenominator ((record.mode.radius q M)⁻¹ • (M).physicalVertex k) :=
  record.chart.checkedCorner (record.mode.checkedCorner q M checked)
    ((checked).physicalSideNormal certificateDenominator_pos)
    (record.mode.checkedOffset q M checked) pass k

def checkedNormal (pass : record.checkChart = true) (k : Fin (key.sidePred + 1)) :
    CheckedPlane certificateDenominator ((M).physicalSideNormal k) :=
  record.chart.checkedNormal (record.mode.checkedCorner q M checked)
    ((checked).physicalSideNormal certificateDenominator_pos)
    (record.mode.checkedOffset q M checked) pass k

def checkedOffset (pass : record.checkChart = true) (k : Fin (key.sidePred + 1)) :
    CheckedReal certificateDenominator ((M).physicalSideOffset k / record.mode.radius q M) :=
  record.chart.checkedOffset (record.mode.checkedCorner q M checked)
    ((checked).physicalSideNormal certificateDenominator_pos)
    (record.mode.checkedOffset q M checked) pass k

def checkWitness (pass : record.checkChart = true) : Bool :=
  record.witness.check certificateDenominator_pos (record.checkedCorner pass)
    (record.checkedNormal pass) (record.checkedOffset pass) record.scalar

/-- The geometric, physical scaling, and scalar checks of one full record. -/
structure Verified (target : ℚ) : Prop where
  chart : record.checkChart = true
  scale : (record.mode.checkedRadius q M checked).isPositive = true
  geometry : record.checkWitness chart = true
  development : record.scalar.check certificateDenominator_pos target = true
  tilt : checkDevelopmentCellTilt q key record.scalar.tilt = true
  tilt_small : record.scalar.tilt ≤ 1 / 2

end MeshRoutingRecord
end Unfoldings.FewestNets
