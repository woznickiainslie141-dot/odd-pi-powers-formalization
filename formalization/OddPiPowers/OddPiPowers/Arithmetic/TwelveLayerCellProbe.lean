module
public import OddPiPowers.Arithmetic.TwelveLayerCellDefs
@[expose] public section
namespace OddPiPowers
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
example : ({ leftNumerator := 1, leftDenominator := 69, rightNumerator := 1, rightDenominator := 68, rankCode := 111039596418616124727684240453360, orderCode := 1273226025159533994039293277479016, floorCode := 2736874734008091634300000000000000000000000, value := 6 } : TwelveCellCertificate).Valid := by
  decide
end OddPiPowers
end
