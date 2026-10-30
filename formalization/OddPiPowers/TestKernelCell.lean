import OddPiPowers.Arithmetic.TwelveLayerCells
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open OddPiPowers
def firstCell : TwelveCellCertificate :=
  { left := 0, right := 1/69, rankCode := 1331214537196502869015340298036888,
    floorCode := 0, value := 0 }
example : firstCell.Valid := by
  norm_num [TwelveCellCertificate.Valid, firstCell, twelveRank, twelveRankList,
    twelveCellFloor, twelveCellMinGap, twelveGapCost, twelvePointCost,
    twelveGapLayer, twelvePointLayer, twelveFloorDigit,
    twelveEndpointAffine, twelveEndpointSlope, Fin.forall_fin_succ]
