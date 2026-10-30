module
public import OddPiPowers.L99.Arithmetic.TwentyEightLayerCellDefs
@[expose] public section
namespace OddPiPowers.L99
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
theorem cellProbe : ({ leftNumerator := 1, leftDenominator := 99, rightNumerator := 1, rightDenominator := 98, rankCode := 2826829994803152804078150613950794731466692218985831340974729487921551044246794405050906902670640, orderCode := 77698803480897900118573257344671009296177569035784470503524950170241157682368825419306329189229640, floorCode := 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, value := 16 } : TwentyEightCellCertificate).Valid := by decide +kernel
#print axioms cellProbe
end OddPiPowers.L99
