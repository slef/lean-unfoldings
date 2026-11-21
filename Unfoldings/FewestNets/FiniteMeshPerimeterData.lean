module

public import Unfoldings.FewestNets.CheckedMeshPerimeter
public import Unfoldings.FewestNets.FiniteMeshExample

/-! Rounded upper bounds for twelve-key blocks of the frequency-100 mesh.
The numerical statements are checked by kernel reduction in the importing modules. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open MeshStar

/-- Each integer represents an upper bound in millionths of a unit. -/
def q100FacePerimeterBounds : List ℕ :=
  [2051333, 2321649, 2377120, 2502847, 2544016, 2575264, 2601490, 2627623, 2658704,
    2700029, 2780786, 2693293, 2748136, 2873177, 2727390, 2814957, 2886354, 2797045,
    2976647, 2782074, 3043108, 2774011, 2956753, 2907494, 2983649, 2921528, 3128833,
    2815621, 3126041, 2860415, 3107235, 2928638, 3069886, 3028191, 3010490, 3196207,
    2897993, 3138198, 3034516, 3050141, 3222712, 2937404, 3140873, 3132991, 3015303,
    3201817, 3063727, 3077488, 3239243, 2978365, 3147925, 3105792, 3058473, 3227378,
    2951147, 3185542, 2982621, 3163469, 2981446, 3167130, 2957722, 3036152, 3086288,
    2970436, 2984306, 2972171, 2947743, 2928235, 2793150, 1006357]

def q100SeamPerimeterBounds : List ℕ := [950397, 962534, 908944, 841080, 133122]

def q100PentagonPerimeterBound : ℕ := 32673

def checkPerimeterBound (k : ℕ) :
    CheckedReal certificateDenominator ((k : ℝ) / 1000000) :=
  ((checkNat _ k).div certificateDenominator_pos
    (checkNat _ 1000000)).convert (by norm_num)

def checkQ100FacePerimeterBlock (i : ℕ) : Bool :=
  (checkFaceBlockPerimeter certificateDenominator_pos 100 12 i).isLT
    (checkPerimeterBound ((q100FacePerimeterBounds[i]?).getD 0))

def checkQ100SeamPerimeterBlock (i : ℕ) : Bool :=
  (checkSeamBlockPerimeter certificateDenominator_pos 100 12 i).isLT
    (checkPerimeterBound ((q100SeamPerimeterBounds[i]?).getD 0))

def checkQ100PentagonPerimeter : Bool :=
  ((checkPentagon certificateDenominator_pos 100).arcUpperPerimeter certificateDenominator_pos).isLT
    (checkPerimeterBound q100PentagonPerimeterBound)

end Unfoldings.FewestNets
