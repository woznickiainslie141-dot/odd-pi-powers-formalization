module
import OddPiPowers.Arithmetic.PeriodTailFloor
open OddPiPowers OddPiPowers.PrimeRates
#print periodTailRational
#print rationalPeriodGap
example : 0 < periodTailRational 32 1000000 ⟨1,69,1,68,0,0,0,6⟩ := by
  norm_num [periodTailRational, rationalPeriodGap, TwelveCellCertificate.left,
    TwelveCellCertificate.right]
example : (0 : ℚ) < 1 / 2 := by decide
