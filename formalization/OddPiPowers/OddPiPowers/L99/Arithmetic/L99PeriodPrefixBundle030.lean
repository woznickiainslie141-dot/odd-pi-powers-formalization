module
public import OddPiPowers.L99.Arithmetic.PeriodFloorBlock
public import OddPiPowers.L99.Arithmetic.CellWindowAggregate
@[expose] public section
namespace OddPiPowers.L99.PrimeRates
open OddPiPowers.PrimeRates
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def l99PeriodPrefix150Floors : List ℕ := [
  110756689, 27401486, 12136261, 6814830, 4356963, 3023575, 2220304, 1699290, 1342262, 1086982, 898162, 754587, 642876, 554254, 482769, 424272,
  375797, 335179, 300807, 271463, 246213, 224329, 205237, 188483, 173700, 160591, 148911, 138460, 129073, 120608, 112950, 105999,
  108473046, 26839405, 11887736, 6675396, 4267864, 2961764, 2174926, 1664567, 1314838, 1064776, 879816, 739174, 629746, 542934, 472910, 415608,
  368123, 328334, 294665, 265920, 241186, 219748, 201047, 184635, 170154, 157312, 145871, 135634, 126438, 118146, 110644, 103835
]

theorem l99PeriodPrefix150_checked :
    periodBlockCheck 100000000000000 (periodPrefixLabels 32 (twentyEightLayerCellChunk150.filter selectedCellPredicate))
      l99PeriodPrefix150Floors = true := by decide +kernel

theorem l99PeriodPrefix150_sum : l99PeriodPrefix150Floors.sum = 352009560 := by decide +kernel

theorem l99PeriodPrefix150_lower : (352009560 : ℝ) / 100000000000000 ≤
    ((periodPrefixLabels 32 (twentyEightLayerCellChunk150.filter selectedCellPredicate)).map periodLabelActual).sum := by
  have h := periodBlockCheck_sound 100000000000000 _ _ l99PeriodPrefix150_checked
  simpa only [l99PeriodPrefix150_sum, Nat.cast_ofNat] using h


end OddPiPowers.L99.PrimeRates
