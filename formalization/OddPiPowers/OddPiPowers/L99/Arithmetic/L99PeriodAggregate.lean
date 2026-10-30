module
public import OddPiPowers.L99.Arithmetic.PeriodPrefixSum
public import OddPiPowers.L99.Arithmetic.PeriodTailAggregate
public import OddPiPowers.L99.Arithmetic.L99PeriodPrefixBundle000
public import OddPiPowers.L99.Arithmetic.L99PeriodPrefixBundle001
public import OddPiPowers.L99.Arithmetic.L99PeriodPrefixBundle002
public import OddPiPowers.L99.Arithmetic.L99PeriodPrefixBundle003
public import OddPiPowers.L99.Arithmetic.L99PeriodPrefixBundle004
public import OddPiPowers.L99.Arithmetic.L99PeriodPrefixBundle005
public import OddPiPowers.L99.Arithmetic.L99PeriodPrefixBundle006
public import OddPiPowers.L99.Arithmetic.L99PeriodPrefixBundle007
public import OddPiPowers.L99.Arithmetic.L99PeriodPrefixBundle008
public import OddPiPowers.L99.Arithmetic.L99PeriodPrefixBundle009
public import OddPiPowers.L99.Arithmetic.L99PeriodPrefixBundle010
public import OddPiPowers.L99.Arithmetic.L99PeriodPrefixBundle011
public import OddPiPowers.L99.Arithmetic.L99PeriodPrefixBundle012
public import OddPiPowers.L99.Arithmetic.L99PeriodPrefixBundle013
public import OddPiPowers.L99.Arithmetic.L99PeriodPrefixBundle014
public import OddPiPowers.L99.Arithmetic.L99PeriodPrefixBundle015
public import OddPiPowers.L99.Arithmetic.L99PeriodPrefixBundle016
public import OddPiPowers.L99.Arithmetic.L99PeriodPrefixBundle017
public import OddPiPowers.L99.Arithmetic.L99PeriodPrefixBundle018
public import OddPiPowers.L99.Arithmetic.L99PeriodPrefixBundle019
public import OddPiPowers.L99.Arithmetic.L99PeriodPrefixBundle020
public import OddPiPowers.L99.Arithmetic.L99PeriodPrefixBundle021
public import OddPiPowers.L99.Arithmetic.L99PeriodPrefixBundle022
public import OddPiPowers.L99.Arithmetic.L99PeriodPrefixBundle023
public import OddPiPowers.L99.Arithmetic.L99PeriodPrefixBundle024
public import OddPiPowers.L99.Arithmetic.L99PeriodPrefixBundle025
public import OddPiPowers.L99.Arithmetic.L99PeriodPrefixBundle026
public import OddPiPowers.L99.Arithmetic.L99PeriodPrefixBundle027
public import OddPiPowers.L99.Arithmetic.L99PeriodPrefixBundle028
public import OddPiPowers.L99.Arithmetic.L99PeriodPrefixBundle029
public import OddPiPowers.L99.Arithmetic.L99PeriodPrefixBundle030
public import OddPiPowers.L99.Arithmetic.L99PeriodTailBundle000
public import OddPiPowers.L99.Arithmetic.L99PeriodTailBundle001
public import OddPiPowers.L99.Arithmetic.L99PeriodTailBundle002
public import OddPiPowers.L99.Arithmetic.L99PeriodTailBundle003
public import OddPiPowers.L99.Arithmetic.L99PeriodTailBundle004
public import OddPiPowers.L99.Arithmetic.L99PeriodTailBundle005
public import OddPiPowers.L99.Arithmetic.L99PeriodTailBundle006
public import OddPiPowers.L99.Arithmetic.L99PeriodTailBundle007
public import OddPiPowers.L99.Arithmetic.L99PeriodTailBundle008
public import OddPiPowers.L99.Arithmetic.L99PeriodTailBundle009
public import OddPiPowers.L99.Arithmetic.L99PeriodTailBundle010
public import OddPiPowers.L99.Arithmetic.L99PeriodTailBundle011
public import OddPiPowers.L99.Arithmetic.L99PeriodTailBundle012
public import OddPiPowers.L99.Arithmetic.L99PeriodTailBundle013
public import OddPiPowers.L99.Arithmetic.L99PeriodTailBundle014
public import OddPiPowers.L99.Arithmetic.L99PeriodTailBundle015
public import OddPiPowers.L99.Arithmetic.L99PeriodTailBundle016
public import OddPiPowers.L99.Arithmetic.L99PeriodTailBundle017
public import OddPiPowers.L99.Arithmetic.L99PeriodTailBundle018
public import OddPiPowers.L99.Arithmetic.L99PeriodTailBundle019
public import OddPiPowers.L99.Arithmetic.L99PeriodTailBundle020
public import OddPiPowers.L99.Arithmetic.L99PeriodTailBundle021
public import OddPiPowers.L99.Arithmetic.L99PeriodTailBundle022
public import OddPiPowers.L99.Arithmetic.L99PeriodTailBundle023
public import OddPiPowers.L99.Arithmetic.L99PeriodTailBundle024
public import OddPiPowers.L99.Arithmetic.L99PeriodTailBundle025
public import OddPiPowers.L99.Arithmetic.L99PeriodTailBundle026
public import OddPiPowers.L99.Arithmetic.L99PeriodTailBundle027
public import OddPiPowers.L99.Arithmetic.L99PeriodTailBundle028
public import OddPiPowers.L99.Arithmetic.L99PeriodTailBundle029
public import OddPiPowers.L99.Arithmetic.L99PeriodTailBundle030

@[expose] public section
namespace OddPiPowers.L99.PrimeRates
open OddPiPowers.PrimeRates
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] twentyEightLayerCellTable twentyEightCellCertificateOfRaw
attribute [local irreducible] periodPrefixLabels periodLabelActual periodTailRational

private noncomputable def prefixFilteredRate (xs : List TwentyEightCellCertificate) : ℝ :=
  ((periodPrefixLabels 32 (xs.filter selectedCellPredicate)).map periodLabelActual).sum

private noncomputable def tailFilteredRate (xs : List TwentyEightCellCertificate) : ℝ :=
  ((xs.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum

private theorem prefix_filtered_append (xs ys : List TwentyEightCellCertificate) :
    prefixFilteredRate (xs ++ ys) = prefixFilteredRate xs + prefixFilteredRate ys := by
  simp only [prefixFilteredRate, List.filter_append, periodPrefixLabels_append, List.map_append, List.sum_append]

private theorem prefix_lower_append {xs ys : List TwentyEightCellCertificate} {a b : ℕ}
    (hx : (a : ℝ) / 100000000000000 ≤ prefixFilteredRate xs)
    (hy : (b : ℝ) / 100000000000000 ≤ prefixFilteredRate ys) :
    ((a + b : ℕ) : ℝ) / 100000000000000 ≤ prefixFilteredRate (xs ++ ys) := by
  rw [prefix_filtered_append, Nat.cast_add, add_div]
  exact add_le_add hx hy

private theorem prefix_chunk_lower_0 :
    (360678647315123 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk0 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix000_lower

private theorem prefix_chunk_lower_1 :
    (252605201924557 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk1 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix001_lower

private theorem prefix_chunk_lower_2 :
    (137460424849279 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk2 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix002_lower

private theorem prefix_chunk_lower_3 :
    (175421719177726 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk3 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix003_lower

private theorem prefix_chunk_lower_4 :
    (83966597522472 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk4 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix004_lower

private theorem prefix_chunk_lower_5 :
    (61664823472977 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk5 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix005_lower

private theorem prefix_chunk_lower_6 :
    (38834224201095 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk6 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix006_lower

private theorem prefix_chunk_lower_7 :
    (30893983573327 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk7 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix007_lower

private theorem prefix_chunk_lower_8 :
    (25238002496272 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk8 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix008_lower

private theorem prefix_chunk_lower_9 :
    (26317931642138 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk9 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix009_lower

private theorem prefix_chunk_lower_10 :
    (17136063234806 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk10 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix010_lower

private theorem prefix_chunk_lower_11 :
    (14291573318623 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk11 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix011_lower

private theorem prefix_chunk_lower_12 :
    (11279972749785 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk12 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix012_lower

private theorem prefix_chunk_lower_13 :
    (10766260816710 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk13 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix013_lower

private theorem prefix_chunk_lower_14 :
    (9885477165065 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk14 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix014_lower

private theorem prefix_chunk_lower_15 :
    (8424212880239 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk15 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix015_lower

private theorem prefix_chunk_lower_16 :
    (7465344984011 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk16 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix016_lower

private theorem prefix_chunk_lower_17 :
    (5837347532616 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk17 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix017_lower

private theorem prefix_chunk_lower_18 :
    (5943263849939 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk18 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix018_lower

private theorem prefix_chunk_lower_19 :
    (4967433852947 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk19 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix019_lower

private theorem prefix_chunk_lower_20 :
    (4775625805681 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk20 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix020_lower

private theorem prefix_chunk_lower_21 :
    (4241800986996 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk21 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix021_lower

private theorem prefix_chunk_lower_22 :
    (3863630151677 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk22 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix022_lower

private theorem prefix_chunk_lower_23 :
    (3551647573508 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk23 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix023_lower

private theorem prefix_chunk_lower_24 :
    (2708251600241 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk24 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix024_lower

private theorem prefix_chunk_lower_25 :
    (3688356832610 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk25 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix025_lower

private theorem prefix_chunk_lower_26 :
    (2868901808131 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk26 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix026_lower

private theorem prefix_chunk_lower_27 :
    (2632269086585 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk27 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix027_lower

private theorem prefix_chunk_lower_28 :
    (2452392484251 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk28 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix028_lower

private theorem prefix_chunk_lower_29 :
    (1786550433900 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk29 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix029_lower

private theorem prefix_chunk_lower_30 :
    (2572322232040 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk30 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix030_lower

private theorem prefix_chunk_lower_31 :
    (2085572046867 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk31 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix031_lower

private theorem prefix_chunk_lower_32 :
    (2020601798675 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk32 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix032_lower

private theorem prefix_chunk_lower_33 :
    (1830970399858 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk33 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix033_lower

private theorem prefix_chunk_lower_34 :
    (1640858480934 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk34 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix034_lower

private theorem prefix_chunk_lower_35 :
    (1656736045594 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk35 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix035_lower

private theorem prefix_chunk_lower_36 :
    (1364240062466 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk36 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix036_lower

private theorem prefix_chunk_lower_37 :
    (1623339945988 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk37 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix037_lower

private theorem prefix_chunk_lower_38 :
    (1285515603754 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk38 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix038_lower

private theorem prefix_chunk_lower_39 :
    (1215011902514 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk39 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix039_lower

private theorem prefix_chunk_lower_40 :
    (1286588530791 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk40 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix040_lower

private theorem prefix_chunk_lower_41 :
    (1285734893220 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk41 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix041_lower

private theorem prefix_chunk_lower_42 :
    (1333935284775 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk42 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix042_lower

private theorem prefix_chunk_lower_43 :
    (956333459063 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk43 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix043_lower

private theorem prefix_chunk_lower_44 :
    (935261725448 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk44 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix044_lower

private theorem prefix_chunk_lower_45 :
    (1079820672352 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk45 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix045_lower

private theorem prefix_chunk_lower_46 :
    (1048844021967 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk46 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix046_lower

private theorem prefix_chunk_lower_47 :
    (873147953069 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk47 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix047_lower

private theorem prefix_chunk_lower_48 :
    (874369977737 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk48 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix048_lower

private theorem prefix_chunk_lower_49 :
    (526704660585 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk49 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix049_lower

private theorem prefix_chunk_lower_50 :
    (1017083579468 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk50 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix050_lower

private theorem prefix_chunk_lower_51 :
    (739420005991 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk51 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix051_lower

private theorem prefix_chunk_lower_52 :
    (707831697667 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk52 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix052_lower

private theorem prefix_chunk_lower_53 :
    (847358184629 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk53 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix053_lower

private theorem prefix_chunk_lower_54 :
    (723853340662 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk54 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix054_lower

private theorem prefix_chunk_lower_55 :
    (711005031764 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk55 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix055_lower

private theorem prefix_chunk_lower_56 :
    (683886033643 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk56 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix056_lower

private theorem prefix_chunk_lower_57 :
    (643721091257 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk57 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix057_lower

private theorem prefix_chunk_lower_58 :
    (662559482933 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk58 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix058_lower

private theorem prefix_chunk_lower_59 :
    (518974099471 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk59 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix059_lower

private theorem prefix_chunk_lower_60 :
    (722550948554 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk60 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix060_lower

private theorem prefix_chunk_lower_61 :
    (568219084348 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk61 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix061_lower

private theorem prefix_chunk_lower_62 :
    (585010964950 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk62 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix062_lower

private theorem prefix_chunk_lower_63 :
    (547037634230 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk63 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix063_lower

private theorem prefix_chunk_lower_64 :
    (572640614135 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk64 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix064_lower

private theorem prefix_chunk_lower_65 :
    (516862012904 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk65 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix065_lower

private theorem prefix_chunk_lower_66 :
    (497214178977 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk66 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix066_lower

private theorem prefix_chunk_lower_67 :
    (489935122232 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk67 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix067_lower

private theorem prefix_chunk_lower_68 :
    (490802922986 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk68 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix068_lower

private theorem prefix_chunk_lower_69 :
    (452299298877 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk69 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix069_lower

private theorem prefix_chunk_lower_70 :
    (462595312031 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk70 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix070_lower

private theorem prefix_chunk_lower_71 :
    (448679024202 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk71 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix071_lower

private theorem prefix_chunk_lower_72 :
    (403812753716 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk72 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix072_lower

private theorem prefix_chunk_lower_73 :
    (277379241293 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk73 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix073_lower

private theorem prefix_chunk_lower_74 :
    (209948657998 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk74 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix074_lower

private theorem prefix_chunk_lower_75 :
    (526562406491 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk75 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix075_lower

private theorem prefix_chunk_lower_76 :
    (373020097603 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk76 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix076_lower

private theorem prefix_chunk_lower_77 :
    (390371470972 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk77 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix077_lower

private theorem prefix_chunk_lower_78 :
    (330297971329 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk78 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix078_lower

private theorem prefix_chunk_lower_79 :
    (374805953477 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk79 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix079_lower

private theorem prefix_chunk_lower_80 :
    (410041167987 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk80 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix080_lower

private theorem prefix_chunk_lower_81 :
    (356465448708 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk81 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix081_lower

private theorem prefix_chunk_lower_82 :
    (330062472625 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk82 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix082_lower

private theorem prefix_chunk_lower_83 :
    (345035522963 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk83 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix083_lower

private theorem prefix_chunk_lower_84 :
    (328017311616 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk84 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix084_lower

private theorem prefix_chunk_lower_85 :
    (370589826519 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk85 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix085_lower

private theorem prefix_chunk_lower_86 :
    (314227683657 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk86 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix086_lower

private theorem prefix_chunk_lower_87 :
    (309076202111 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk87 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix087_lower

private theorem prefix_chunk_lower_88 :
    (319615820449 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk88 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix088_lower

private theorem prefix_chunk_lower_89 :
    (238799166341 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk89 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix089_lower

private theorem prefix_chunk_lower_90 :
    (366008931913 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk90 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix090_lower

private theorem prefix_chunk_lower_91 :
    (301961817961 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk91 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix091_lower

private theorem prefix_chunk_lower_92 :
    (289746222791 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk92 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix092_lower

private theorem prefix_chunk_lower_93 :
    (292669416386 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk93 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix093_lower

private theorem prefix_chunk_lower_94 :
    (260939598552 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk94 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix094_lower

private theorem prefix_chunk_lower_95 :
    (274578023527 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk95 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix095_lower

private theorem prefix_chunk_lower_96 :
    (287140280574 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk96 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix096_lower

private theorem prefix_chunk_lower_97 :
    (264821115791 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk97 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix097_lower

private theorem prefix_chunk_lower_98 :
    (246443538303 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk98 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix098_lower

private theorem prefix_chunk_lower_99 :
    (149136462876 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk99 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix099_lower

private theorem prefix_chunk_lower_100 :
    (317259305101 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk100 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix100_lower

private theorem prefix_chunk_lower_101 :
    (222048085710 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk101 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix101_lower

private theorem prefix_chunk_lower_102 :
    (244262984898 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk102 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix102_lower

private theorem prefix_chunk_lower_103 :
    (266779260111 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk103 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix103_lower

private theorem prefix_chunk_lower_104 :
    (205447570801 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk104 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix104_lower

private theorem prefix_chunk_lower_105 :
    (245997060219 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk105 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix105_lower

private theorem prefix_chunk_lower_106 :
    (223474243549 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk106 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix106_lower

private theorem prefix_chunk_lower_107 :
    (246755748907 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk107 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix107_lower

private theorem prefix_chunk_lower_108 :
    (224695472497 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk108 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix108_lower

private theorem prefix_chunk_lower_109 :
    (215298725067 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk109 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix109_lower

private theorem prefix_chunk_lower_110 :
    (221996666372 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk110 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix110_lower

private theorem prefix_chunk_lower_111 :
    (185213033250 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk111 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix111_lower

private theorem prefix_chunk_lower_112 :
    (229526151539 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk112 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix112_lower

private theorem prefix_chunk_lower_113 :
    (191755518951 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk113 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix113_lower

private theorem prefix_chunk_lower_114 :
    (199803718773 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk114 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix114_lower

private theorem prefix_chunk_lower_115 :
    (197690594472 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk115 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix115_lower

private theorem prefix_chunk_lower_116 :
    (214335661920 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk116 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix116_lower

private theorem prefix_chunk_lower_117 :
    (191868404572 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk117 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix117_lower

private theorem prefix_chunk_lower_118 :
    (211057486068 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk118 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix118_lower

private theorem prefix_chunk_lower_119 :
    (145898306474 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk119 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix119_lower

private theorem prefix_chunk_lower_120 :
    (215479546864 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk120 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix120_lower

private theorem prefix_chunk_lower_121 :
    (180281169921 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk121 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix121_lower

private theorem prefix_chunk_lower_122 :
    (193214005119 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk122 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix122_lower

private theorem prefix_chunk_lower_123 :
    (174956904283 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk123 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix123_lower

private theorem prefix_chunk_lower_124 :
    (153511234691 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk124 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix124_lower

private theorem prefix_chunk_lower_125 :
    (200515433677 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk125 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix125_lower

private theorem prefix_chunk_lower_126 :
    (160115208327 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk126 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix126_lower

private theorem prefix_chunk_lower_127 :
    (190566408759 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk127 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix127_lower

private theorem prefix_chunk_lower_128 :
    (178276872881 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk128 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix128_lower

private theorem prefix_chunk_lower_129 :
    (155234764328 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk129 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix129_lower

private theorem prefix_chunk_lower_130 :
    (156274963553 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk130 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix130_lower

private theorem prefix_chunk_lower_131 :
    (169819462057 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk131 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix131_lower

private theorem prefix_chunk_lower_132 :
    (152857325154 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk132 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix132_lower

private theorem prefix_chunk_lower_133 :
    (160596639058 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk133 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix133_lower

private theorem prefix_chunk_lower_134 :
    (164253470184 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk134 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix134_lower

private theorem prefix_chunk_lower_135 :
    (164895426791 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk135 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix135_lower

private theorem prefix_chunk_lower_136 :
    (138741252253 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk136 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix136_lower

private theorem prefix_chunk_lower_137 :
    (150163311806 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk137 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix137_lower

private theorem prefix_chunk_lower_138 :
    (142853195572 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk138 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix138_lower

private theorem prefix_chunk_lower_139 :
    (155055239633 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk139 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix139_lower

private theorem prefix_chunk_lower_140 :
    (147766435040 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk140 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix140_lower

private theorem prefix_chunk_lower_141 :
    (143760010919 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk141 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix141_lower

private theorem prefix_chunk_lower_142 :
    (107818421204 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk142 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix142_lower

private theorem prefix_chunk_lower_143 :
    (131039427814 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk143 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix143_lower

private theorem prefix_chunk_lower_144 :
    (144277614647 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk144 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix144_lower

private theorem prefix_chunk_lower_145 :
    (114098834036 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk145 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix145_lower

private theorem prefix_chunk_lower_146 :
    (131795796981 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk146 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix146_lower

private theorem prefix_chunk_lower_147 :
    (39946773930 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk147 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix147_lower

private theorem prefix_chunk_lower_148 :
    (79224453228 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk148 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix148_lower

private theorem prefix_chunk_lower_149 :
    (31335456943 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk149 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix149_lower

private theorem prefix_chunk_lower_150 :
    (352009560 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellChunk150 := by
  simpa only [prefixFilteredRate] using l99PeriodPrefix150_lower

private theorem prefix_whole_lower :
    (1380525198339888 : ℝ) / 100000000000000 ≤ prefixFilteredRate twentyEightLayerCellTable := by
  unfold twentyEightLayerCellTable
  exact prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_lower_append (prefix_chunk_lower_0) prefix_chunk_lower_1) prefix_chunk_lower_2) prefix_chunk_lower_3) prefix_chunk_lower_4) prefix_chunk_lower_5) prefix_chunk_lower_6) prefix_chunk_lower_7) prefix_chunk_lower_8) prefix_chunk_lower_9) prefix_chunk_lower_10) prefix_chunk_lower_11) prefix_chunk_lower_12) prefix_chunk_lower_13) prefix_chunk_lower_14) prefix_chunk_lower_15) prefix_chunk_lower_16) prefix_chunk_lower_17) prefix_chunk_lower_18) prefix_chunk_lower_19) prefix_chunk_lower_20) prefix_chunk_lower_21) prefix_chunk_lower_22) prefix_chunk_lower_23) prefix_chunk_lower_24) prefix_chunk_lower_25) prefix_chunk_lower_26) prefix_chunk_lower_27) prefix_chunk_lower_28) prefix_chunk_lower_29) prefix_chunk_lower_30) prefix_chunk_lower_31) prefix_chunk_lower_32) prefix_chunk_lower_33) prefix_chunk_lower_34) prefix_chunk_lower_35) prefix_chunk_lower_36) prefix_chunk_lower_37) prefix_chunk_lower_38) prefix_chunk_lower_39) prefix_chunk_lower_40) prefix_chunk_lower_41) prefix_chunk_lower_42) prefix_chunk_lower_43) prefix_chunk_lower_44) prefix_chunk_lower_45) prefix_chunk_lower_46) prefix_chunk_lower_47) prefix_chunk_lower_48) prefix_chunk_lower_49) prefix_chunk_lower_50) prefix_chunk_lower_51) prefix_chunk_lower_52) prefix_chunk_lower_53) prefix_chunk_lower_54) prefix_chunk_lower_55) prefix_chunk_lower_56) prefix_chunk_lower_57) prefix_chunk_lower_58) prefix_chunk_lower_59) prefix_chunk_lower_60) prefix_chunk_lower_61) prefix_chunk_lower_62) prefix_chunk_lower_63) prefix_chunk_lower_64) prefix_chunk_lower_65) prefix_chunk_lower_66) prefix_chunk_lower_67) prefix_chunk_lower_68) prefix_chunk_lower_69) prefix_chunk_lower_70) prefix_chunk_lower_71) prefix_chunk_lower_72) prefix_chunk_lower_73) prefix_chunk_lower_74) prefix_chunk_lower_75) prefix_chunk_lower_76) prefix_chunk_lower_77) prefix_chunk_lower_78) prefix_chunk_lower_79) prefix_chunk_lower_80) prefix_chunk_lower_81) prefix_chunk_lower_82) prefix_chunk_lower_83) prefix_chunk_lower_84) prefix_chunk_lower_85) prefix_chunk_lower_86) prefix_chunk_lower_87) prefix_chunk_lower_88) prefix_chunk_lower_89) prefix_chunk_lower_90) prefix_chunk_lower_91) prefix_chunk_lower_92) prefix_chunk_lower_93) prefix_chunk_lower_94) prefix_chunk_lower_95) prefix_chunk_lower_96) prefix_chunk_lower_97) prefix_chunk_lower_98) prefix_chunk_lower_99) prefix_chunk_lower_100) prefix_chunk_lower_101) prefix_chunk_lower_102) prefix_chunk_lower_103) prefix_chunk_lower_104) prefix_chunk_lower_105) prefix_chunk_lower_106) prefix_chunk_lower_107) prefix_chunk_lower_108) prefix_chunk_lower_109) prefix_chunk_lower_110) prefix_chunk_lower_111) prefix_chunk_lower_112) prefix_chunk_lower_113) prefix_chunk_lower_114) prefix_chunk_lower_115) prefix_chunk_lower_116) prefix_chunk_lower_117) prefix_chunk_lower_118) prefix_chunk_lower_119) prefix_chunk_lower_120) prefix_chunk_lower_121) prefix_chunk_lower_122) prefix_chunk_lower_123) prefix_chunk_lower_124) prefix_chunk_lower_125) prefix_chunk_lower_126) prefix_chunk_lower_127) prefix_chunk_lower_128) prefix_chunk_lower_129) prefix_chunk_lower_130) prefix_chunk_lower_131) prefix_chunk_lower_132) prefix_chunk_lower_133) prefix_chunk_lower_134) prefix_chunk_lower_135) prefix_chunk_lower_136) prefix_chunk_lower_137) prefix_chunk_lower_138) prefix_chunk_lower_139) prefix_chunk_lower_140) prefix_chunk_lower_141) prefix_chunk_lower_142) prefix_chunk_lower_143) prefix_chunk_lower_144) prefix_chunk_lower_145) prefix_chunk_lower_146) prefix_chunk_lower_147) prefix_chunk_lower_148) prefix_chunk_lower_149) prefix_chunk_lower_150

theorem l99_prefix_floor_lower : (1380525198339888 : ℝ) / 100000000000000 ≤ selectedUnshrunkRate 32 := by
  have h := prefix_whole_lower
  have heq : prefixFilteredRate twentyEightLayerCellTable = selectedUnshrunkRate 32 := by
    simpa only [prefixFilteredRate, selectedCells] using (selected_periodPrefixLabels_actual_sum 32)
  exact h.trans_eq heq

private theorem tail_filtered_append (xs ys : List TwentyEightCellCertificate) :
    tailFilteredRate (xs ++ ys) = tailFilteredRate xs + tailFilteredRate ys := by
  simp only [tailFilteredRate, List.filter_append, periodPrefixLabels_append, List.map_append, List.sum_append]

private theorem tail_lower_append {xs ys : List TwentyEightCellCertificate} {a b : ℕ}
    (hx : (a : ℝ) / 100000000000000 ≤ tailFilteredRate xs)
    (hy : (b : ℝ) / 100000000000000 ≤ tailFilteredRate ys) :
    ((a + b : ℕ) : ℝ) / 100000000000000 ≤ tailFilteredRate (xs ++ ys) := by
  rw [tail_filtered_append, Nat.cast_add, add_div]
  exact add_le_add hx hy

private theorem tail_chunk_lower_0 :
    (1451647496 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk0 := by
  simpa only [tailFilteredRate] using l99PeriodTail000_lower

private theorem tail_chunk_lower_1 :
    (1605731991 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk1 := by
  simpa only [tailFilteredRate] using l99PeriodTail001_lower

private theorem tail_chunk_lower_2 :
    (1755997527 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk2 := by
  simpa only [tailFilteredRate] using l99PeriodTail002_lower

private theorem tail_chunk_lower_3 :
    (3450824932 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk3 := by
  simpa only [tailFilteredRate] using l99PeriodTail003_lower

private theorem tail_chunk_lower_4 :
    (2639165220 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk4 := by
  simpa only [tailFilteredRate] using l99PeriodTail004_lower

private theorem tail_chunk_lower_5 :
    (2757774857 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk5 := by
  simpa only [tailFilteredRate] using l99PeriodTail005_lower

private theorem tail_chunk_lower_6 :
    (2381299440 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk6 := by
  simpa only [tailFilteredRate] using l99PeriodTail006_lower

private theorem tail_chunk_lower_7 :
    (2528294907 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk7 := by
  simpa only [tailFilteredRate] using l99PeriodTail007_lower

private theorem tail_chunk_lower_8 :
    (2560914702 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk8 := by
  simpa only [tailFilteredRate] using l99PeriodTail008_lower

private theorem tail_chunk_lower_9 :
    (3363255105 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk9 := by
  simpa only [tailFilteredRate] using l99PeriodTail009_lower

private theorem tail_chunk_lower_10 :
    (2672026752 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk10 := by
  simpa only [tailFilteredRate] using l99PeriodTail010_lower

private theorem tail_chunk_lower_11 :
    (2656498775 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk11 := by
  simpa only [tailFilteredRate] using l99PeriodTail011_lower

private theorem tail_chunk_lower_12 :
    (2454625398 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk12 := by
  simpa only [tailFilteredRate] using l99PeriodTail012_lower

private theorem tail_chunk_lower_13 :
    (2729973480 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk13 := by
  simpa only [tailFilteredRate] using l99PeriodTail013_lower

private theorem tail_chunk_lower_14 :
    (2875839669 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk14 := by
  simpa only [tailFilteredRate] using l99PeriodTail014_lower

private theorem tail_chunk_lower_15 :
    (2805476868 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk15 := by
  simpa only [tailFilteredRate] using l99PeriodTail015_lower

private theorem tail_chunk_lower_16 :
    (2811287487 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk16 := by
  simpa only [tailFilteredRate] using l99PeriodTail016_lower

private theorem tail_chunk_lower_17 :
    (2469173209 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk17 := by
  simpa only [tailFilteredRate] using l99PeriodTail017_lower

private theorem tail_chunk_lower_18 :
    (2801578761 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk18 := by
  simpa only [tailFilteredRate] using l99PeriodTail018_lower

private theorem tail_chunk_lower_19 :
    (2601424749 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk19 := by
  simpa only [tailFilteredRate] using l99PeriodTail019_lower

private theorem tail_chunk_lower_20 :
    (2738276982 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk20 := by
  simpa only [tailFilteredRate] using l99PeriodTail020_lower

private theorem tail_chunk_lower_21 :
    (2664995516 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk21 := by
  simpa only [tailFilteredRate] using l99PeriodTail021_lower

private theorem tail_chunk_lower_22 :
    (2651866783 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk22 := by
  simpa only [tailFilteredRate] using l99PeriodTail022_lower

private theorem tail_chunk_lower_23 :
    (2649689848 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk23 := by
  simpa only [tailFilteredRate] using l99PeriodTail023_lower

private theorem tail_chunk_lower_24 :
    (2177780984 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk24 := by
  simpa only [tailFilteredRate] using l99PeriodTail024_lower

private theorem tail_chunk_lower_25 :
    (3209717504 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk25 := by
  simpa only [tailFilteredRate] using l99PeriodTail025_lower

private theorem tail_chunk_lower_26 :
    (2706605101 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk26 := by
  simpa only [tailFilteredRate] using l99PeriodTail026_lower

private theorem tail_chunk_lower_27 :
    (2661927728 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk27 := by
  simpa only [tailFilteredRate] using l99PeriodTail027_lower

private theorem tail_chunk_lower_28 :
    (2656511555 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk28 := by
  simpa only [tailFilteredRate] using l99PeriodTail028_lower

private theorem tail_chunk_lower_29 :
    (2049852885 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk29 := by
  simpa only [tailFilteredRate] using l99PeriodTail029_lower

private theorem tail_chunk_lower_30 :
    (3158756629 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk30 := by
  simpa only [tailFilteredRate] using l99PeriodTail030_lower

private theorem tail_chunk_lower_31 :
    (2736654830 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk31 := by
  simpa only [tailFilteredRate] using l99PeriodTail031_lower

private theorem tail_chunk_lower_32 :
    (2814639939 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk32 := by
  simpa only [tailFilteredRate] using l99PeriodTail032_lower

private theorem tail_chunk_lower_33 :
    (2707093060 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk33 := by
  simpa only [tailFilteredRate] using l99PeriodTail033_lower

private theorem tail_chunk_lower_34 :
    (2564853802 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk34 := by
  simpa only [tailFilteredRate] using l99PeriodTail034_lower

private theorem tail_chunk_lower_35 :
    (2729662619 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk35 := by
  simpa only [tailFilteredRate] using l99PeriodTail035_lower

private theorem tail_chunk_lower_36 :
    (2360958517 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk36 := by
  simpa only [tailFilteredRate] using l99PeriodTail036_lower

private theorem tail_chunk_lower_37 :
    (2963356362 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk37 := by
  simpa only [tailFilteredRate] using l99PeriodTail037_lower

private theorem tail_chunk_lower_38 :
    (2477459578 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk38 := by
  simpa only [tailFilteredRate] using l99PeriodTail038_lower

private theorem tail_chunk_lower_39 :
    (2447445558 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk39 := by
  simpa only [tailFilteredRate] using l99PeriodTail039_lower

private theorem tail_chunk_lower_40 :
    (2709347784 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk40 := by
  simpa only [tailFilteredRate] using l99PeriodTail040_lower

private theorem tail_chunk_lower_41 :
    (2837279412 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk41 := by
  simpa only [tailFilteredRate] using l99PeriodTail041_lower

private theorem tail_chunk_lower_42 :
    (3087912660 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk42 := by
  simpa only [tailFilteredRate] using l99PeriodTail042_lower

private theorem tail_chunk_lower_43 :
    (2313718005 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk43 := by
  simpa only [tailFilteredRate] using l99PeriodTail043_lower

private theorem tail_chunk_lower_44 :
    (2346448328 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk44 := by
  simpa only [tailFilteredRate] using l99PeriodTail044_lower

private theorem tail_chunk_lower_45 :
    (2820315075 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk45 := by
  simpa only [tailFilteredRate] using l99PeriodTail045_lower

private theorem tail_chunk_lower_46 :
    (2858121305 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk46 := by
  simpa only [tailFilteredRate] using l99PeriodTail046_lower

private theorem tail_chunk_lower_47 :
    (2473145260 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk47 := by
  simpa only [tailFilteredRate] using l99PeriodTail047_lower

private theorem tail_chunk_lower_48 :
    (2564803625 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk48 := by
  simpa only [tailFilteredRate] using l99PeriodTail048_lower

private theorem tail_chunk_lower_49 :
    (1592353518 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk49 := by
  simpa only [tailFilteredRate] using l99PeriodTail049_lower

private theorem tail_chunk_lower_50 :
    (3205944844 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk50 := by
  simpa only [tailFilteredRate] using l99PeriodTail050_lower

private theorem tail_chunk_lower_51 :
    (2434046234 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk51 := by
  simpa only [tailFilteredRate] using l99PeriodTail051_lower

private theorem tail_chunk_lower_52 :
    (2402291765 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk52 := by
  simpa only [tailFilteredRate] using l99PeriodTail052_lower

private theorem tail_chunk_lower_53 :
    (2975369196 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk53 := by
  simpa only [tailFilteredRate] using l99PeriodTail053_lower

private theorem tail_chunk_lower_54 :
    (2629221966 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk54 := by
  simpa only [tailFilteredRate] using l99PeriodTail054_lower

private theorem tail_chunk_lower_55 :
    (2666961253 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk55 := by
  simpa only [tailFilteredRate] using l99PeriodTail055_lower

private theorem tail_chunk_lower_56 :
    (2649857770 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk56 := by
  simpa only [tailFilteredRate] using l99PeriodTail056_lower

private theorem tail_chunk_lower_57 :
    (2572768113 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk57 := by
  simpa only [tailFilteredRate] using l99PeriodTail057_lower

private theorem tail_chunk_lower_58 :
    (2728611984 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk58 := by
  simpa only [tailFilteredRate] using l99PeriodTail058_lower

private theorem tail_chunk_lower_59 :
    (2196286405 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk59 := by
  simpa only [tailFilteredRate] using l99PeriodTail059_lower

private theorem tail_chunk_lower_60 :
    (3157854661 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk60 := by
  simpa only [tailFilteredRate] using l99PeriodTail060_lower

private theorem tail_chunk_lower_61 :
    (2561556730 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk61 := by
  simpa only [tailFilteredRate] using l99PeriodTail061_lower

private theorem tail_chunk_lower_62 :
    (2711600624 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk62 := by
  simpa only [tailFilteredRate] using l99PeriodTail062_lower

private theorem tail_chunk_lower_63 :
    (2608247628 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk63 := by
  simpa only [tailFilteredRate] using l99PeriodTail063_lower

private theorem tail_chunk_lower_64 :
    (2807095930 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk64 := by
  simpa only [tailFilteredRate] using l99PeriodTail064_lower

private theorem tail_chunk_lower_65 :
    (2602635164 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk65 := by
  simpa only [tailFilteredRate] using l99PeriodTail065_lower

private theorem tail_chunk_lower_66 :
    (2570501307 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk66 := by
  simpa only [tailFilteredRate] using l99PeriodTail066_lower

private theorem tail_chunk_lower_67 :
    (2598826370 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk67 := by
  simpa only [tailFilteredRate] using l99PeriodTail067_lower

private theorem tail_chunk_lower_68 :
    (2669378827 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk68 := by
  simpa only [tailFilteredRate] using l99PeriodTail068_lower

private theorem tail_chunk_lower_69 :
    (2520691538 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk69 := by
  simpa only [tailFilteredRate] using l99PeriodTail069_lower

private theorem tail_chunk_lower_70 :
    (2641961789 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk70 := by
  simpa only [tailFilteredRate] using l99PeriodTail070_lower

private theorem tail_chunk_lower_71 :
    (2625195425 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk71 := by
  simpa only [tailFilteredRate] using l99PeriodTail071_lower

private theorem tail_chunk_lower_72 :
    (2415715432 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk72 := by
  simpa only [tailFilteredRate] using l99PeriodTail072_lower

private theorem tail_chunk_lower_73 :
    (1690876120 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk73 := by
  simpa only [tailFilteredRate] using l99PeriodTail073_lower

private theorem tail_chunk_lower_74 :
    (1306819367 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk74 := by
  simpa only [tailFilteredRate] using l99PeriodTail074_lower

private theorem tail_chunk_lower_75 :
    (3357784684 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk75 := by
  simpa only [tailFilteredRate] using l99PeriodTail075_lower

private theorem tail_chunk_lower_76 :
    (2463103775 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk76 := by
  simpa only [tailFilteredRate] using l99PeriodTail076_lower

private theorem tail_chunk_lower_77 :
    (2630120057 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk77 := by
  simpa only [tailFilteredRate] using l99PeriodTail077_lower

private theorem tail_chunk_lower_78 :
    (2271563812 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk78 := by
  simpa only [tailFilteredRate] using l99PeriodTail078_lower

private theorem tail_chunk_lower_79 :
    (2630690338 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk79 := by
  simpa only [tailFilteredRate] using l99PeriodTail079_lower

private theorem tail_chunk_lower_80 :
    (2939223665 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk80 := by
  simpa only [tailFilteredRate] using l99PeriodTail080_lower

private theorem tail_chunk_lower_81 :
    (2609872934 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk81 := by
  simpa only [tailFilteredRate] using l99PeriodTail081_lower

private theorem tail_chunk_lower_82 :
    (2466003687 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk82 := by
  simpa only [tailFilteredRate] using l99PeriodTail082_lower

private theorem tail_chunk_lower_83 :
    (2628254501 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk83 := by
  simpa only [tailFilteredRate] using l99PeriodTail083_lower

private theorem tail_chunk_lower_84 :
    (2547383923 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk84 := by
  simpa only [tailFilteredRate] using l99PeriodTail084_lower

private theorem tail_chunk_lower_85 :
    (2936754891 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk85 := by
  simpa only [tailFilteredRate] using l99PeriodTail085_lower

private theorem tail_chunk_lower_86 :
    (2541023451 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk86 := by
  simpa only [tailFilteredRate] using l99PeriodTail086_lower

private theorem tail_chunk_lower_87 :
    (2544406637 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk87 := by
  simpa only [tailFilteredRate] using l99PeriodTail087_lower

private theorem tail_chunk_lower_88 :
    (2680164375 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk88 := by
  simpa only [tailFilteredRate] using l99PeriodTail088_lower

private theorem tail_chunk_lower_89 :
    (2035994064 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk89 := by
  simpa only [tailFilteredRate] using l99PeriodTail089_lower

private theorem tail_chunk_lower_90 :
    (3181419037 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk90 := by
  simpa only [tailFilteredRate] using l99PeriodTail090_lower

private theorem tail_chunk_lower_91 :
    (2677341831 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk91 := by
  simpa only [tailFilteredRate] using l99PeriodTail091_lower

private theorem tail_chunk_lower_92 :
    (2614832135 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk92 := by
  simpa only [tailFilteredRate] using l99PeriodTail092_lower

private theorem tail_chunk_lower_93 :
    (2688255859 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk93 := by
  simpa only [tailFilteredRate] using l99PeriodTail093_lower

private theorem tail_chunk_lower_94 :
    (2438012982 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk94 := by
  simpa only [tailFilteredRate] using l99PeriodTail094_lower

private theorem tail_chunk_lower_95 :
    (2608312110 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk95 := by
  simpa only [tailFilteredRate] using l99PeriodTail095_lower

private theorem tail_chunk_lower_96 :
    (2774435794 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk96 := by
  simpa only [tailFilteredRate] using l99PeriodTail096_lower

private theorem tail_chunk_lower_97 :
    (2601766605 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk97 := by
  simpa only [tailFilteredRate] using l99PeriodTail097_lower

private theorem tail_chunk_lower_98 :
    (2459044604 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk98 := by
  simpa only [tailFilteredRate] using l99PeriodTail098_lower

private theorem tail_chunk_lower_99 :
    (1507687524 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk99 := by
  simpa only [tailFilteredRate] using l99PeriodTail099_lower

private theorem tail_chunk_lower_100 :
    (3267107475 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk100 := by
  simpa only [tailFilteredRate] using l99PeriodTail100_lower

private theorem tail_chunk_lower_101 :
    (2330564942 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk101 := by
  simpa only [tailFilteredRate] using l99PeriodTail101_lower

private theorem tail_chunk_lower_102 :
    (2600269250 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk102 := by
  simpa only [tailFilteredRate] using l99PeriodTail102_lower

private theorem tail_chunk_lower_103 :
    (2885858574 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk103 := by
  simpa only [tailFilteredRate] using l99PeriodTail103_lower

private theorem tail_chunk_lower_104 :
    (2254872405 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk104 := by
  simpa only [tailFilteredRate] using l99PeriodTail104_lower

private theorem tail_chunk_lower_105 :
    (2739384391 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk105 := by
  simpa only [tailFilteredRate] using l99PeriodTail105_lower

private theorem tail_chunk_lower_106 :
    (2525790172 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk106 := by
  simpa only [tailFilteredRate] using l99PeriodTail106_lower

private theorem tail_chunk_lower_107 :
    (2831137719 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk107 := by
  simpa only [tailFilteredRate] using l99PeriodTail107_lower

private theorem tail_chunk_lower_108 :
    (2616543980 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk108 := by
  simpa only [tailFilteredRate] using l99PeriodTail108_lower

private theorem tail_chunk_lower_109 :
    (2543140809 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk109 := by
  simpa only [tailFilteredRate] using l99PeriodTail109_lower

private theorem tail_chunk_lower_110 :
    (2660196420 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk110 := by
  simpa only [tailFilteredRate] using l99PeriodTail110_lower

private theorem tail_chunk_lower_111 :
    (2248307870 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk111 := by
  simpa only [tailFilteredRate] using l99PeriodTail111_lower

private theorem tail_chunk_lower_112 :
    (2827528803 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk112 := by
  simpa only [tailFilteredRate] using l99PeriodTail112_lower

private theorem tail_chunk_lower_113 :
    (2398645696 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk113 := by
  simpa only [tailFilteredRate] using l99PeriodTail113_lower

private theorem tail_chunk_lower_114 :
    (2530894516 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk114 := by
  simpa only [tailFilteredRate] using l99PeriodTail114_lower

private theorem tail_chunk_lower_115 :
    (2536665479 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk115 := by
  simpa only [tailFilteredRate] using l99PeriodTail115_lower

private theorem tail_chunk_lower_116 :
    (2789035960 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk116 := by
  simpa only [tailFilteredRate] using l99PeriodTail116_lower

private theorem tail_chunk_lower_117 :
    (2530520102 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk117 := by
  simpa only [tailFilteredRate] using l99PeriodTail117_lower

private theorem tail_chunk_lower_118 :
    (2820083839 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk118 := by
  simpa only [tailFilteredRate] using l99PeriodTail118_lower

private theorem tail_chunk_lower_119 :
    (1972320066 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk119 := by
  simpa only [tailFilteredRate] using l99PeriodTail119_lower

private theorem tail_chunk_lower_120 :
    (2952468641 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk120 := by
  simpa only [tailFilteredRate] using l99PeriodTail120_lower

private theorem tail_chunk_lower_121 :
    (2503778106 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk121 := by
  simpa only [tailFilteredRate] using l99PeriodTail121_lower

private theorem tail_chunk_lower_122 :
    (2717536909 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk122 := by
  simpa only [tailFilteredRate] using l99PeriodTail122_lower

private theorem tail_chunk_lower_123 :
    (2490804699 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk123 := by
  simpa only [tailFilteredRate] using l99PeriodTail123_lower

private theorem tail_chunk_lower_124 :
    (2209316528 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk124 := by
  simpa only [tailFilteredRate] using l99PeriodTail124_lower

private theorem tail_chunk_lower_125 :
    (2921900128 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk125 := by
  simpa only [tailFilteredRate] using l99PeriodTail125_lower

private theorem tail_chunk_lower_126 :
    (2363372734 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk126 := by
  simpa only [tailFilteredRate] using l99PeriodTail126_lower

private theorem tail_chunk_lower_127 :
    (2846497640 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk127 := by
  simpa only [tailFilteredRate] using l99PeriodTail127_lower

private theorem tail_chunk_lower_128 :
    (2696296953 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk128 := by
  simpa only [tailFilteredRate] using l99PeriodTail128_lower

private theorem tail_chunk_lower_129 :
    (2374663129 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk129 := by
  simpa only [tailFilteredRate] using l99PeriodTail129_lower

private theorem tail_chunk_lower_130 :
    (2416751557 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk130 := by
  simpa only [tailFilteredRate] using l99PeriodTail130_lower

private theorem tail_chunk_lower_131 :
    (2656835539 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk131 := by
  simpa only [tailFilteredRate] using l99PeriodTail131_lower

private theorem tail_chunk_lower_132 :
    (2419102073 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk132 := by
  simpa only [tailFilteredRate] using l99PeriodTail132_lower

private theorem tail_chunk_lower_133 :
    (2569988102 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk133 := by
  simpa only [tailFilteredRate] using l99PeriodTail133_lower

private theorem tail_chunk_lower_134 :
    (2657641247 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk134 := by
  simpa only [tailFilteredRate] using l99PeriodTail134_lower

private theorem tail_chunk_lower_135 :
    (2698541771 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk135 := by
  simpa only [tailFilteredRate] using l99PeriodTail135_lower

private theorem tail_chunk_lower_136 :
    (2295681299 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk136 := by
  simpa only [tailFilteredRate] using l99PeriodTail136_lower

private theorem tail_chunk_lower_137 :
    (2512073208 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk137 := by
  simpa only [tailFilteredRate] using l99PeriodTail137_lower

private theorem tail_chunk_lower_138 :
    (2414802930 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk138 := by
  simpa only [tailFilteredRate] using l99PeriodTail138_lower

private theorem tail_chunk_lower_139 :
    (2648390432 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk139 := by
  simpa only [tailFilteredRate] using l99PeriodTail139_lower

private theorem tail_chunk_lower_140 :
    (2550667507 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk140 := by
  simpa only [tailFilteredRate] using l99PeriodTail140_lower

private theorem tail_chunk_lower_141 :
    (2509266406 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk141 := by
  simpa only [tailFilteredRate] using l99PeriodTail141_lower

private theorem tail_chunk_lower_142 :
    (1899361391 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk142 := by
  simpa only [tailFilteredRate] using l99PeriodTail142_lower

private theorem tail_chunk_lower_143 :
    (2332196405 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk143 := by
  simpa only [tailFilteredRate] using l99PeriodTail143_lower

private theorem tail_chunk_lower_144 :
    (2593976627 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk144 := by
  simpa only [tailFilteredRate] using l99PeriodTail144_lower

private theorem tail_chunk_lower_145 :
    (2069840014 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk145 := by
  simpa only [tailFilteredRate] using l99PeriodTail145_lower

private theorem tail_chunk_lower_146 :
    (2412768432 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk146 := by
  simpa only [tailFilteredRate] using l99PeriodTail146_lower

private theorem tail_chunk_lower_147 :
    (738421821 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk147 := by
  simpa only [tailFilteredRate] using l99PeriodTail147_lower

private theorem tail_chunk_lower_148 :
    (1476369820 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk148 := by
  simpa only [tailFilteredRate] using l99PeriodTail148_lower

private theorem tail_chunk_lower_149 :
    (586625659 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk149 := by
  simpa only [tailFilteredRate] using l99PeriodTail149_lower

private theorem tail_chunk_lower_150 :
    (6607512 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellChunk150 := by
  simpa only [tailFilteredRate] using l99PeriodTail150_lower

private theorem tail_whole_lower :
    (381339545481 : ℝ) / 100000000000000 ≤ tailFilteredRate twentyEightLayerCellTable := by
  unfold twentyEightLayerCellTable
  exact tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_lower_append (tail_chunk_lower_0) tail_chunk_lower_1) tail_chunk_lower_2) tail_chunk_lower_3) tail_chunk_lower_4) tail_chunk_lower_5) tail_chunk_lower_6) tail_chunk_lower_7) tail_chunk_lower_8) tail_chunk_lower_9) tail_chunk_lower_10) tail_chunk_lower_11) tail_chunk_lower_12) tail_chunk_lower_13) tail_chunk_lower_14) tail_chunk_lower_15) tail_chunk_lower_16) tail_chunk_lower_17) tail_chunk_lower_18) tail_chunk_lower_19) tail_chunk_lower_20) tail_chunk_lower_21) tail_chunk_lower_22) tail_chunk_lower_23) tail_chunk_lower_24) tail_chunk_lower_25) tail_chunk_lower_26) tail_chunk_lower_27) tail_chunk_lower_28) tail_chunk_lower_29) tail_chunk_lower_30) tail_chunk_lower_31) tail_chunk_lower_32) tail_chunk_lower_33) tail_chunk_lower_34) tail_chunk_lower_35) tail_chunk_lower_36) tail_chunk_lower_37) tail_chunk_lower_38) tail_chunk_lower_39) tail_chunk_lower_40) tail_chunk_lower_41) tail_chunk_lower_42) tail_chunk_lower_43) tail_chunk_lower_44) tail_chunk_lower_45) tail_chunk_lower_46) tail_chunk_lower_47) tail_chunk_lower_48) tail_chunk_lower_49) tail_chunk_lower_50) tail_chunk_lower_51) tail_chunk_lower_52) tail_chunk_lower_53) tail_chunk_lower_54) tail_chunk_lower_55) tail_chunk_lower_56) tail_chunk_lower_57) tail_chunk_lower_58) tail_chunk_lower_59) tail_chunk_lower_60) tail_chunk_lower_61) tail_chunk_lower_62) tail_chunk_lower_63) tail_chunk_lower_64) tail_chunk_lower_65) tail_chunk_lower_66) tail_chunk_lower_67) tail_chunk_lower_68) tail_chunk_lower_69) tail_chunk_lower_70) tail_chunk_lower_71) tail_chunk_lower_72) tail_chunk_lower_73) tail_chunk_lower_74) tail_chunk_lower_75) tail_chunk_lower_76) tail_chunk_lower_77) tail_chunk_lower_78) tail_chunk_lower_79) tail_chunk_lower_80) tail_chunk_lower_81) tail_chunk_lower_82) tail_chunk_lower_83) tail_chunk_lower_84) tail_chunk_lower_85) tail_chunk_lower_86) tail_chunk_lower_87) tail_chunk_lower_88) tail_chunk_lower_89) tail_chunk_lower_90) tail_chunk_lower_91) tail_chunk_lower_92) tail_chunk_lower_93) tail_chunk_lower_94) tail_chunk_lower_95) tail_chunk_lower_96) tail_chunk_lower_97) tail_chunk_lower_98) tail_chunk_lower_99) tail_chunk_lower_100) tail_chunk_lower_101) tail_chunk_lower_102) tail_chunk_lower_103) tail_chunk_lower_104) tail_chunk_lower_105) tail_chunk_lower_106) tail_chunk_lower_107) tail_chunk_lower_108) tail_chunk_lower_109) tail_chunk_lower_110) tail_chunk_lower_111) tail_chunk_lower_112) tail_chunk_lower_113) tail_chunk_lower_114) tail_chunk_lower_115) tail_chunk_lower_116) tail_chunk_lower_117) tail_chunk_lower_118) tail_chunk_lower_119) tail_chunk_lower_120) tail_chunk_lower_121) tail_chunk_lower_122) tail_chunk_lower_123) tail_chunk_lower_124) tail_chunk_lower_125) tail_chunk_lower_126) tail_chunk_lower_127) tail_chunk_lower_128) tail_chunk_lower_129) tail_chunk_lower_130) tail_chunk_lower_131) tail_chunk_lower_132) tail_chunk_lower_133) tail_chunk_lower_134) tail_chunk_lower_135) tail_chunk_lower_136) tail_chunk_lower_137) tail_chunk_lower_138) tail_chunk_lower_139) tail_chunk_lower_140) tail_chunk_lower_141) tail_chunk_lower_142) tail_chunk_lower_143) tail_chunk_lower_144) tail_chunk_lower_145) tail_chunk_lower_146) tail_chunk_lower_147) tail_chunk_lower_148) tail_chunk_lower_149) tail_chunk_lower_150

theorem l99_tail_floor_lower : (381339545481 : ℝ) / 100000000000000 ≤ selectedTailRationalSum 32 1000000 := by
  simpa only [tailFilteredRate, selectedTailRationalSum, selectedCells] using tail_whole_lower

end OddPiPowers.L99.PrimeRates
