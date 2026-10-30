module

public import OddPiPowers.Arithmetic.PeriodPrefixSum
public import OddPiPowers.Arithmetic.PeriodTailAggregate
public import OddPiPowers.Arithmetic.P6PeriodPrefix00
public import OddPiPowers.Arithmetic.P6PeriodPrefix01
public import OddPiPowers.Arithmetic.P6PeriodPrefix02
public import OddPiPowers.Arithmetic.P6PeriodPrefix03
public import OddPiPowers.Arithmetic.P6PeriodPrefix04
public import OddPiPowers.Arithmetic.P6PeriodPrefix05
public import OddPiPowers.Arithmetic.P6PeriodPrefix06
public import OddPiPowers.Arithmetic.P6PeriodPrefix07
public import OddPiPowers.Arithmetic.P6PeriodPrefix08
public import OddPiPowers.Arithmetic.P6PeriodPrefix09
public import OddPiPowers.Arithmetic.P6PeriodPrefix10
public import OddPiPowers.Arithmetic.P6PeriodPrefix11
public import OddPiPowers.Arithmetic.P6PeriodPrefix12
public import OddPiPowers.Arithmetic.P6PeriodPrefix13
public import OddPiPowers.Arithmetic.P6PeriodPrefix14
public import OddPiPowers.Arithmetic.P6PeriodPrefix15
public import OddPiPowers.Arithmetic.P6PeriodPrefix16
public import OddPiPowers.Arithmetic.P6PeriodPrefix17
public import OddPiPowers.Arithmetic.P6PeriodPrefix18
public import OddPiPowers.Arithmetic.P6PeriodPrefix19
public import OddPiPowers.Arithmetic.P6PeriodPrefix20
public import OddPiPowers.Arithmetic.P6PeriodPrefix21
public import OddPiPowers.Arithmetic.P6PeriodPrefix22
public import OddPiPowers.Arithmetic.P6PeriodPrefix23
public import OddPiPowers.Arithmetic.P6PeriodPrefix24
public import OddPiPowers.Arithmetic.P6PeriodPrefix25
public import OddPiPowers.Arithmetic.P6PeriodPrefix26
public import OddPiPowers.Arithmetic.P6PeriodPrefix27
public import OddPiPowers.Arithmetic.P6PeriodPrefix28
public import OddPiPowers.Arithmetic.P6PeriodPrefix29
public import OddPiPowers.Arithmetic.P6PeriodTail00
public import OddPiPowers.Arithmetic.P6PeriodTail01
public import OddPiPowers.Arithmetic.P6PeriodTail02
public import OddPiPowers.Arithmetic.P6PeriodTail03
public import OddPiPowers.Arithmetic.P6PeriodTail04
public import OddPiPowers.Arithmetic.P6PeriodTail05
public import OddPiPowers.Arithmetic.P6PeriodTail06
public import OddPiPowers.Arithmetic.P6PeriodTail07
public import OddPiPowers.Arithmetic.P6PeriodTail08
public import OddPiPowers.Arithmetic.P6PeriodTail09
public import OddPiPowers.Arithmetic.P6PeriodTail10
public import OddPiPowers.Arithmetic.P6PeriodTail11
public import OddPiPowers.Arithmetic.P6PeriodTail12
public import OddPiPowers.Arithmetic.P6PeriodTail13
public import OddPiPowers.Arithmetic.P6PeriodTail14
public import OddPiPowers.Arithmetic.P6PeriodTail15
public import OddPiPowers.Arithmetic.P6PeriodTail16
public import OddPiPowers.Arithmetic.P6PeriodTail17
public import OddPiPowers.Arithmetic.P6PeriodTail18
public import OddPiPowers.Arithmetic.P6PeriodTail19
public import OddPiPowers.Arithmetic.P6PeriodTail20
public import OddPiPowers.Arithmetic.P6PeriodTail21
public import OddPiPowers.Arithmetic.P6PeriodTail22
public import OddPiPowers.Arithmetic.P6PeriodTail23
public import OddPiPowers.Arithmetic.P6PeriodTail24
public import OddPiPowers.Arithmetic.P6PeriodTail25
public import OddPiPowers.Arithmetic.P6PeriodTail26
public import OddPiPowers.Arithmetic.P6PeriodTail27
public import OddPiPowers.Arithmetic.P6PeriodTail28
public import OddPiPowers.Arithmetic.P6PeriodTail29

/-! Assembly of exact finite prefix and finite tail certificates. -/

@[expose] public section
namespace OddPiPowers.PrimeRates

theorem p6_prefix_floor_lower :
    (412848897248127 : ℝ) / 100000000000000 ≤ selectedUnshrunkRate 32 := by
  rw [← selected_periodPrefixLabels_actual_sum]
  unfold selectedCells
  simp only [twelveLayerCellTable, List.filter_append, periodPrefixLabels_append,
    List.map_append, List.sum_append]
  have h0 := p6PeriodPrefix00_lower
  have h1 := p6PeriodPrefix01_lower
  have h2 := p6PeriodPrefix02_lower
  have h3 := p6PeriodPrefix03_lower
  have h4 := p6PeriodPrefix04_lower
  have h5 := p6PeriodPrefix05_lower
  have h6 := p6PeriodPrefix06_lower
  have h7 := p6PeriodPrefix07_lower
  have h8 := p6PeriodPrefix08_lower
  have h9 := p6PeriodPrefix09_lower
  have h10 := p6PeriodPrefix10_lower
  have h11 := p6PeriodPrefix11_lower
  have h12 := p6PeriodPrefix12_lower
  have h13 := p6PeriodPrefix13_lower
  have h14 := p6PeriodPrefix14_lower
  have h15 := p6PeriodPrefix15_lower
  have h16 := p6PeriodPrefix16_lower
  have h17 := p6PeriodPrefix17_lower
  have h18 := p6PeriodPrefix18_lower
  have h19 := p6PeriodPrefix19_lower
  have h20 := p6PeriodPrefix20_lower
  have h21 := p6PeriodPrefix21_lower
  have h22 := p6PeriodPrefix22_lower
  have h23 := p6PeriodPrefix23_lower
  have h24 := p6PeriodPrefix24_lower
  have h25 := p6PeriodPrefix25_lower
  have h26 := p6PeriodPrefix26_lower
  have h27 := p6PeriodPrefix27_lower
  have h28 := p6PeriodPrefix28_lower
  have h29 := p6PeriodPrefix29_lower
  linarith

theorem p6_tail_floor_lower :
    (205621482243 : ℝ) / 100000000000000 ≤
      (selectedCells.map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  unfold selectedCells
  simp only [twelveLayerCellTable, List.filter_append, List.map_append, List.sum_append]
  have h0 := p6PeriodTail00_lower
  have h1 := p6PeriodTail01_lower
  have h2 := p6PeriodTail02_lower
  have h3 := p6PeriodTail03_lower
  have h4 := p6PeriodTail04_lower
  have h5 := p6PeriodTail05_lower
  have h6 := p6PeriodTail06_lower
  have h7 := p6PeriodTail07_lower
  have h8 := p6PeriodTail08_lower
  have h9 := p6PeriodTail09_lower
  have h10 := p6PeriodTail10_lower
  have h11 := p6PeriodTail11_lower
  have h12 := p6PeriodTail12_lower
  have h13 := p6PeriodTail13_lower
  have h14 := p6PeriodTail14_lower
  have h15 := p6PeriodTail15_lower
  have h16 := p6PeriodTail16_lower
  have h17 := p6PeriodTail17_lower
  have h18 := p6PeriodTail18_lower
  have h19 := p6PeriodTail19_lower
  have h20 := p6PeriodTail20_lower
  have h21 := p6PeriodTail21_lower
  have h22 := p6PeriodTail22_lower
  have h23 := p6PeriodTail23_lower
  have h24 := p6PeriodTail24_lower
  have h25 := p6PeriodTail25_lower
  have h26 := p6PeriodTail26_lower
  have h27 := p6PeriodTail27_lower
  have h28 := p6PeriodTail28_lower
  have h29 := p6PeriodTail29_lower
  linarith

end OddPiPowers.PrimeRates
