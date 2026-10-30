module
public import OddPiPowers.Arithmetic.TwelveLayerCellSoundness
public import OddPiPowers.Arithmetic.TwelveLayerValidity00
public import OddPiPowers.Arithmetic.TwelveLayerValidity01
public import OddPiPowers.Arithmetic.TwelveLayerValidity02
public import OddPiPowers.Arithmetic.TwelveLayerValidity03
public import OddPiPowers.Arithmetic.TwelveLayerValidity04
public import OddPiPowers.Arithmetic.TwelveLayerValidity05
public import OddPiPowers.Arithmetic.TwelveLayerValidity06
public import OddPiPowers.Arithmetic.TwelveLayerValidity07
public import OddPiPowers.Arithmetic.TwelveLayerValidity08
public import OddPiPowers.Arithmetic.TwelveLayerValidity09
public import OddPiPowers.Arithmetic.TwelveLayerValidity10
public import OddPiPowers.Arithmetic.TwelveLayerValidity11
public import OddPiPowers.Arithmetic.TwelveLayerValidity12
public import OddPiPowers.Arithmetic.TwelveLayerValidity13
public import OddPiPowers.Arithmetic.TwelveLayerValidity14
public import OddPiPowers.Arithmetic.TwelveLayerValidity15
public import OddPiPowers.Arithmetic.TwelveLayerValidity16
public import OddPiPowers.Arithmetic.TwelveLayerValidity17
public import OddPiPowers.Arithmetic.TwelveLayerValidity18
public import OddPiPowers.Arithmetic.TwelveLayerValidity19
public import OddPiPowers.Arithmetic.TwelveLayerValidity20
public import OddPiPowers.Arithmetic.TwelveLayerValidity21
public import OddPiPowers.Arithmetic.TwelveLayerValidity22
public import OddPiPowers.Arithmetic.TwelveLayerValidity23
public import OddPiPowers.Arithmetic.TwelveLayerValidity24
public import OddPiPowers.Arithmetic.TwelveLayerValidity25
public import OddPiPowers.Arithmetic.TwelveLayerValidity26
public import OddPiPowers.Arithmetic.TwelveLayerValidity27
public import OddPiPowers.Arithmetic.TwelveLayerValidity28
public import OddPiPowers.Arithmetic.TwelveLayerValidity29
@[expose] public section
namespace OddPiPowers
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem twelveLayerCellTable_length : twelveLayerCellTable.length = 1180 := by decide

theorem twelveLayerCellTable_positive_count :
    (twelveLayerCellTable.filter (fun c => 0 < c.value)).length = 1166 := by decide

theorem twelveLayerCellTable_all_valid :
    ∀ c ∈ twelveLayerCellTable, c.Valid := by
  have hall : twelveLayerCellTable.all (fun c => c.Valid) = true := by
    simp only [twelveLayerCellTable, List.all_append,
      twelveCellsChunk0_valid,
      twelveCellsChunk1_valid,
      twelveCellsChunk2_valid,
      twelveCellsChunk3_valid,
      twelveCellsChunk4_valid,
      twelveCellsChunk5_valid,
      twelveCellsChunk6_valid,
      twelveCellsChunk7_valid,
      twelveCellsChunk8_valid,
      twelveCellsChunk9_valid,
      twelveCellsChunk10_valid,
      twelveCellsChunk11_valid,
      twelveCellsChunk12_valid,
      twelveCellsChunk13_valid,
      twelveCellsChunk14_valid,
      twelveCellsChunk15_valid,
      twelveCellsChunk16_valid,
      twelveCellsChunk17_valid,
      twelveCellsChunk18_valid,
      twelveCellsChunk19_valid,
      twelveCellsChunk20_valid,
      twelveCellsChunk21_valid,
      twelveCellsChunk22_valid,
      twelveCellsChunk23_valid,
      twelveCellsChunk24_valid,
      twelveCellsChunk25_valid,
      twelveCellsChunk26_valid,
      twelveCellsChunk27_valid,
      twelveCellsChunk28_valid,
      twelveCellsChunk29_valid, Bool.and_true]
  intro c hc
  exact of_decide_eq_true (List.all_eq_true.mp hall c hc)

end OddPiPowers
end
