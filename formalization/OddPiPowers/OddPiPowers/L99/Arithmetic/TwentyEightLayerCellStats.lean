module
public import OddPiPowers.L99.Arithmetic.TwentyEightLayerCellDefs
@[expose] public section
namespace OddPiPowers.L99
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

attribute [local irreducible] twentyEightLayerCellTable
attribute [local irreducible] twentyEightLayerCellChunk0 twentyEightLayerCellChunk1 twentyEightLayerCellChunk2 twentyEightLayerCellChunk3 twentyEightLayerCellChunk4 twentyEightLayerCellChunk5 twentyEightLayerCellChunk6 twentyEightLayerCellChunk7 twentyEightLayerCellChunk8 twentyEightLayerCellChunk9 twentyEightLayerCellChunk10 twentyEightLayerCellChunk11 twentyEightLayerCellChunk12 twentyEightLayerCellChunk13 twentyEightLayerCellChunk14 twentyEightLayerCellChunk15 twentyEightLayerCellChunk16 twentyEightLayerCellChunk17 twentyEightLayerCellChunk18 twentyEightLayerCellChunk19 twentyEightLayerCellChunk20 twentyEightLayerCellChunk21 twentyEightLayerCellChunk22 twentyEightLayerCellChunk23 twentyEightLayerCellChunk24 twentyEightLayerCellChunk25 twentyEightLayerCellChunk26 twentyEightLayerCellChunk27 twentyEightLayerCellChunk28 twentyEightLayerCellChunk29 twentyEightLayerCellChunk30 twentyEightLayerCellChunk31 twentyEightLayerCellChunk32 twentyEightLayerCellChunk33 twentyEightLayerCellChunk34 twentyEightLayerCellChunk35 twentyEightLayerCellChunk36 twentyEightLayerCellChunk37 twentyEightLayerCellChunk38 twentyEightLayerCellChunk39 twentyEightLayerCellChunk40 twentyEightLayerCellChunk41 twentyEightLayerCellChunk42 twentyEightLayerCellChunk43 twentyEightLayerCellChunk44 twentyEightLayerCellChunk45 twentyEightLayerCellChunk46 twentyEightLayerCellChunk47 twentyEightLayerCellChunk48 twentyEightLayerCellChunk49 twentyEightLayerCellChunk50 twentyEightLayerCellChunk51 twentyEightLayerCellChunk52 twentyEightLayerCellChunk53 twentyEightLayerCellChunk54 twentyEightLayerCellChunk55 twentyEightLayerCellChunk56 twentyEightLayerCellChunk57 twentyEightLayerCellChunk58 twentyEightLayerCellChunk59 twentyEightLayerCellChunk60 twentyEightLayerCellChunk61 twentyEightLayerCellChunk62 twentyEightLayerCellChunk63 twentyEightLayerCellChunk64 twentyEightLayerCellChunk65 twentyEightLayerCellChunk66 twentyEightLayerCellChunk67 twentyEightLayerCellChunk68 twentyEightLayerCellChunk69 twentyEightLayerCellChunk70 twentyEightLayerCellChunk71 twentyEightLayerCellChunk72 twentyEightLayerCellChunk73 twentyEightLayerCellChunk74 twentyEightLayerCellChunk75 twentyEightLayerCellChunk76 twentyEightLayerCellChunk77 twentyEightLayerCellChunk78 twentyEightLayerCellChunk79 twentyEightLayerCellChunk80 twentyEightLayerCellChunk81 twentyEightLayerCellChunk82 twentyEightLayerCellChunk83 twentyEightLayerCellChunk84 twentyEightLayerCellChunk85 twentyEightLayerCellChunk86 twentyEightLayerCellChunk87 twentyEightLayerCellChunk88 twentyEightLayerCellChunk89 twentyEightLayerCellChunk90 twentyEightLayerCellChunk91 twentyEightLayerCellChunk92 twentyEightLayerCellChunk93 twentyEightLayerCellChunk94 twentyEightLayerCellChunk95 twentyEightLayerCellChunk96 twentyEightLayerCellChunk97 twentyEightLayerCellChunk98 twentyEightLayerCellChunk99 twentyEightLayerCellChunk100 twentyEightLayerCellChunk101 twentyEightLayerCellChunk102 twentyEightLayerCellChunk103 twentyEightLayerCellChunk104 twentyEightLayerCellChunk105 twentyEightLayerCellChunk106 twentyEightLayerCellChunk107 twentyEightLayerCellChunk108 twentyEightLayerCellChunk109 twentyEightLayerCellChunk110 twentyEightLayerCellChunk111 twentyEightLayerCellChunk112 twentyEightLayerCellChunk113 twentyEightLayerCellChunk114 twentyEightLayerCellChunk115 twentyEightLayerCellChunk116 twentyEightLayerCellChunk117 twentyEightLayerCellChunk118 twentyEightLayerCellChunk119 twentyEightLayerCellChunk120 twentyEightLayerCellChunk121 twentyEightLayerCellChunk122 twentyEightLayerCellChunk123 twentyEightLayerCellChunk124 twentyEightLayerCellChunk125 twentyEightLayerCellChunk126 twentyEightLayerCellChunk127 twentyEightLayerCellChunk128 twentyEightLayerCellChunk129 twentyEightLayerCellChunk130 twentyEightLayerCellChunk131 twentyEightLayerCellChunk132 twentyEightLayerCellChunk133 twentyEightLayerCellChunk134 twentyEightLayerCellChunk135 twentyEightLayerCellChunk136 twentyEightLayerCellChunk137 twentyEightLayerCellChunk138 twentyEightLayerCellChunk139 twentyEightLayerCellChunk140 twentyEightLayerCellChunk141 twentyEightLayerCellChunk142 twentyEightLayerCellChunk143 twentyEightLayerCellChunk144 twentyEightLayerCellChunk145 twentyEightLayerCellChunk146 twentyEightLayerCellChunk147 twentyEightLayerCellChunk148 twentyEightLayerCellChunk149 twentyEightLayerCellChunk150

private theorem cell_length_append {xs ys : List TwentyEightCellCertificate} {a b : ℕ}
    (hx : xs.length = a) (hy : ys.length = b) : (xs ++ ys).length = a + b := by
  rw [List.length_append, hx, hy]

private theorem cell_positive_append {xs ys : List TwentyEightCellCertificate} {a b : ℕ}
    (hx : (xs.filter (fun c => 0 < c.value)).length = a)
    (hy : (ys.filter (fun c => 0 < c.value)).length = b) :
    ((xs ++ ys).filter (fun c => 0 < c.value)).length = a + b := by
  rw [List.filter_append, List.length_append, hx, hy]

theorem twentyEightCellsChunk0_length :
    twentyEightLayerCellChunk0.length = 20 := by decide +kernel
theorem twentyEightCellsChunk0_positive_count :
    (twentyEightLayerCellChunk0.filter (fun c => 0 < c.value)).length = 19 := by decide +kernel

theorem twentyEightCellsChunk1_length :
    twentyEightLayerCellChunk1.length = 20 := by decide +kernel
theorem twentyEightCellsChunk1_positive_count :
    (twentyEightLayerCellChunk1.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk2_length :
    twentyEightLayerCellChunk2.length = 20 := by decide +kernel
theorem twentyEightCellsChunk2_positive_count :
    (twentyEightLayerCellChunk2.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk3_length :
    twentyEightLayerCellChunk3.length = 20 := by decide +kernel
theorem twentyEightCellsChunk3_positive_count :
    (twentyEightLayerCellChunk3.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk4_length :
    twentyEightLayerCellChunk4.length = 20 := by decide +kernel
theorem twentyEightCellsChunk4_positive_count :
    (twentyEightLayerCellChunk4.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk5_length :
    twentyEightLayerCellChunk5.length = 20 := by decide +kernel
theorem twentyEightCellsChunk5_positive_count :
    (twentyEightLayerCellChunk5.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk6_length :
    twentyEightLayerCellChunk6.length = 20 := by decide +kernel
theorem twentyEightCellsChunk6_positive_count :
    (twentyEightLayerCellChunk6.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk7_length :
    twentyEightLayerCellChunk7.length = 20 := by decide +kernel
theorem twentyEightCellsChunk7_positive_count :
    (twentyEightLayerCellChunk7.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk8_length :
    twentyEightLayerCellChunk8.length = 20 := by decide +kernel
theorem twentyEightCellsChunk8_positive_count :
    (twentyEightLayerCellChunk8.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk9_length :
    twentyEightLayerCellChunk9.length = 20 := by decide +kernel
theorem twentyEightCellsChunk9_positive_count :
    (twentyEightLayerCellChunk9.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk10_length :
    twentyEightLayerCellChunk10.length = 20 := by decide +kernel
theorem twentyEightCellsChunk10_positive_count :
    (twentyEightLayerCellChunk10.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk11_length :
    twentyEightLayerCellChunk11.length = 20 := by decide +kernel
theorem twentyEightCellsChunk11_positive_count :
    (twentyEightLayerCellChunk11.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk12_length :
    twentyEightLayerCellChunk12.length = 20 := by decide +kernel
theorem twentyEightCellsChunk12_positive_count :
    (twentyEightLayerCellChunk12.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk13_length :
    twentyEightLayerCellChunk13.length = 20 := by decide +kernel
theorem twentyEightCellsChunk13_positive_count :
    (twentyEightLayerCellChunk13.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk14_length :
    twentyEightLayerCellChunk14.length = 20 := by decide +kernel
theorem twentyEightCellsChunk14_positive_count :
    (twentyEightLayerCellChunk14.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk15_length :
    twentyEightLayerCellChunk15.length = 20 := by decide +kernel
theorem twentyEightCellsChunk15_positive_count :
    (twentyEightLayerCellChunk15.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk16_length :
    twentyEightLayerCellChunk16.length = 20 := by decide +kernel
theorem twentyEightCellsChunk16_positive_count :
    (twentyEightLayerCellChunk16.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk17_length :
    twentyEightLayerCellChunk17.length = 20 := by decide +kernel
theorem twentyEightCellsChunk17_positive_count :
    (twentyEightLayerCellChunk17.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk18_length :
    twentyEightLayerCellChunk18.length = 20 := by decide +kernel
theorem twentyEightCellsChunk18_positive_count :
    (twentyEightLayerCellChunk18.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk19_length :
    twentyEightLayerCellChunk19.length = 20 := by decide +kernel
theorem twentyEightCellsChunk19_positive_count :
    (twentyEightLayerCellChunk19.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk20_length :
    twentyEightLayerCellChunk20.length = 20 := by decide +kernel
theorem twentyEightCellsChunk20_positive_count :
    (twentyEightLayerCellChunk20.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk21_length :
    twentyEightLayerCellChunk21.length = 20 := by decide +kernel
theorem twentyEightCellsChunk21_positive_count :
    (twentyEightLayerCellChunk21.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk22_length :
    twentyEightLayerCellChunk22.length = 20 := by decide +kernel
theorem twentyEightCellsChunk22_positive_count :
    (twentyEightLayerCellChunk22.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk23_length :
    twentyEightLayerCellChunk23.length = 20 := by decide +kernel
theorem twentyEightCellsChunk23_positive_count :
    (twentyEightLayerCellChunk23.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk24_length :
    twentyEightLayerCellChunk24.length = 20 := by decide +kernel
theorem twentyEightCellsChunk24_positive_count :
    (twentyEightLayerCellChunk24.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk25_length :
    twentyEightLayerCellChunk25.length = 20 := by decide +kernel
theorem twentyEightCellsChunk25_positive_count :
    (twentyEightLayerCellChunk25.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk26_length :
    twentyEightLayerCellChunk26.length = 20 := by decide +kernel
theorem twentyEightCellsChunk26_positive_count :
    (twentyEightLayerCellChunk26.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk27_length :
    twentyEightLayerCellChunk27.length = 20 := by decide +kernel
theorem twentyEightCellsChunk27_positive_count :
    (twentyEightLayerCellChunk27.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk28_length :
    twentyEightLayerCellChunk28.length = 20 := by decide +kernel
theorem twentyEightCellsChunk28_positive_count :
    (twentyEightLayerCellChunk28.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk29_length :
    twentyEightLayerCellChunk29.length = 20 := by decide +kernel
theorem twentyEightCellsChunk29_positive_count :
    (twentyEightLayerCellChunk29.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk30_length :
    twentyEightLayerCellChunk30.length = 20 := by decide +kernel
theorem twentyEightCellsChunk30_positive_count :
    (twentyEightLayerCellChunk30.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk31_length :
    twentyEightLayerCellChunk31.length = 20 := by decide +kernel
theorem twentyEightCellsChunk31_positive_count :
    (twentyEightLayerCellChunk31.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk32_length :
    twentyEightLayerCellChunk32.length = 20 := by decide +kernel
theorem twentyEightCellsChunk32_positive_count :
    (twentyEightLayerCellChunk32.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk33_length :
    twentyEightLayerCellChunk33.length = 20 := by decide +kernel
theorem twentyEightCellsChunk33_positive_count :
    (twentyEightLayerCellChunk33.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk34_length :
    twentyEightLayerCellChunk34.length = 20 := by decide +kernel
theorem twentyEightCellsChunk34_positive_count :
    (twentyEightLayerCellChunk34.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk35_length :
    twentyEightLayerCellChunk35.length = 20 := by decide +kernel
theorem twentyEightCellsChunk35_positive_count :
    (twentyEightLayerCellChunk35.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk36_length :
    twentyEightLayerCellChunk36.length = 20 := by decide +kernel
theorem twentyEightCellsChunk36_positive_count :
    (twentyEightLayerCellChunk36.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk37_length :
    twentyEightLayerCellChunk37.length = 20 := by decide +kernel
theorem twentyEightCellsChunk37_positive_count :
    (twentyEightLayerCellChunk37.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk38_length :
    twentyEightLayerCellChunk38.length = 20 := by decide +kernel
theorem twentyEightCellsChunk38_positive_count :
    (twentyEightLayerCellChunk38.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk39_length :
    twentyEightLayerCellChunk39.length = 20 := by decide +kernel
theorem twentyEightCellsChunk39_positive_count :
    (twentyEightLayerCellChunk39.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk40_length :
    twentyEightLayerCellChunk40.length = 20 := by decide +kernel
theorem twentyEightCellsChunk40_positive_count :
    (twentyEightLayerCellChunk40.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk41_length :
    twentyEightLayerCellChunk41.length = 20 := by decide +kernel
theorem twentyEightCellsChunk41_positive_count :
    (twentyEightLayerCellChunk41.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk42_length :
    twentyEightLayerCellChunk42.length = 20 := by decide +kernel
theorem twentyEightCellsChunk42_positive_count :
    (twentyEightLayerCellChunk42.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk43_length :
    twentyEightLayerCellChunk43.length = 20 := by decide +kernel
theorem twentyEightCellsChunk43_positive_count :
    (twentyEightLayerCellChunk43.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk44_length :
    twentyEightLayerCellChunk44.length = 20 := by decide +kernel
theorem twentyEightCellsChunk44_positive_count :
    (twentyEightLayerCellChunk44.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk45_length :
    twentyEightLayerCellChunk45.length = 20 := by decide +kernel
theorem twentyEightCellsChunk45_positive_count :
    (twentyEightLayerCellChunk45.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk46_length :
    twentyEightLayerCellChunk46.length = 20 := by decide +kernel
theorem twentyEightCellsChunk46_positive_count :
    (twentyEightLayerCellChunk46.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk47_length :
    twentyEightLayerCellChunk47.length = 20 := by decide +kernel
theorem twentyEightCellsChunk47_positive_count :
    (twentyEightLayerCellChunk47.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk48_length :
    twentyEightLayerCellChunk48.length = 20 := by decide +kernel
theorem twentyEightCellsChunk48_positive_count :
    (twentyEightLayerCellChunk48.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk49_length :
    twentyEightLayerCellChunk49.length = 20 := by decide +kernel
theorem twentyEightCellsChunk49_positive_count :
    (twentyEightLayerCellChunk49.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk50_length :
    twentyEightLayerCellChunk50.length = 20 := by decide +kernel
theorem twentyEightCellsChunk50_positive_count :
    (twentyEightLayerCellChunk50.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk51_length :
    twentyEightLayerCellChunk51.length = 20 := by decide +kernel
theorem twentyEightCellsChunk51_positive_count :
    (twentyEightLayerCellChunk51.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk52_length :
    twentyEightLayerCellChunk52.length = 20 := by decide +kernel
theorem twentyEightCellsChunk52_positive_count :
    (twentyEightLayerCellChunk52.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk53_length :
    twentyEightLayerCellChunk53.length = 20 := by decide +kernel
theorem twentyEightCellsChunk53_positive_count :
    (twentyEightLayerCellChunk53.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk54_length :
    twentyEightLayerCellChunk54.length = 20 := by decide +kernel
theorem twentyEightCellsChunk54_positive_count :
    (twentyEightLayerCellChunk54.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk55_length :
    twentyEightLayerCellChunk55.length = 20 := by decide +kernel
theorem twentyEightCellsChunk55_positive_count :
    (twentyEightLayerCellChunk55.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk56_length :
    twentyEightLayerCellChunk56.length = 20 := by decide +kernel
theorem twentyEightCellsChunk56_positive_count :
    (twentyEightLayerCellChunk56.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk57_length :
    twentyEightLayerCellChunk57.length = 20 := by decide +kernel
theorem twentyEightCellsChunk57_positive_count :
    (twentyEightLayerCellChunk57.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk58_length :
    twentyEightLayerCellChunk58.length = 20 := by decide +kernel
theorem twentyEightCellsChunk58_positive_count :
    (twentyEightLayerCellChunk58.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk59_length :
    twentyEightLayerCellChunk59.length = 20 := by decide +kernel
theorem twentyEightCellsChunk59_positive_count :
    (twentyEightLayerCellChunk59.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk60_length :
    twentyEightLayerCellChunk60.length = 20 := by decide +kernel
theorem twentyEightCellsChunk60_positive_count :
    (twentyEightLayerCellChunk60.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk61_length :
    twentyEightLayerCellChunk61.length = 20 := by decide +kernel
theorem twentyEightCellsChunk61_positive_count :
    (twentyEightLayerCellChunk61.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk62_length :
    twentyEightLayerCellChunk62.length = 20 := by decide +kernel
theorem twentyEightCellsChunk62_positive_count :
    (twentyEightLayerCellChunk62.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk63_length :
    twentyEightLayerCellChunk63.length = 20 := by decide +kernel
theorem twentyEightCellsChunk63_positive_count :
    (twentyEightLayerCellChunk63.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk64_length :
    twentyEightLayerCellChunk64.length = 20 := by decide +kernel
theorem twentyEightCellsChunk64_positive_count :
    (twentyEightLayerCellChunk64.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk65_length :
    twentyEightLayerCellChunk65.length = 20 := by decide +kernel
theorem twentyEightCellsChunk65_positive_count :
    (twentyEightLayerCellChunk65.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk66_length :
    twentyEightLayerCellChunk66.length = 20 := by decide +kernel
theorem twentyEightCellsChunk66_positive_count :
    (twentyEightLayerCellChunk66.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk67_length :
    twentyEightLayerCellChunk67.length = 20 := by decide +kernel
theorem twentyEightCellsChunk67_positive_count :
    (twentyEightLayerCellChunk67.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk68_length :
    twentyEightLayerCellChunk68.length = 20 := by decide +kernel
theorem twentyEightCellsChunk68_positive_count :
    (twentyEightLayerCellChunk68.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk69_length :
    twentyEightLayerCellChunk69.length = 20 := by decide +kernel
theorem twentyEightCellsChunk69_positive_count :
    (twentyEightLayerCellChunk69.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk70_length :
    twentyEightLayerCellChunk70.length = 20 := by decide +kernel
theorem twentyEightCellsChunk70_positive_count :
    (twentyEightLayerCellChunk70.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk71_length :
    twentyEightLayerCellChunk71.length = 20 := by decide +kernel
theorem twentyEightCellsChunk71_positive_count :
    (twentyEightLayerCellChunk71.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk72_length :
    twentyEightLayerCellChunk72.length = 20 := by decide +kernel
theorem twentyEightCellsChunk72_positive_count :
    (twentyEightLayerCellChunk72.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk73_length :
    twentyEightLayerCellChunk73.length = 20 := by decide +kernel
theorem twentyEightCellsChunk73_positive_count :
    (twentyEightLayerCellChunk73.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk74_length :
    twentyEightLayerCellChunk74.length = 20 := by decide +kernel
theorem twentyEightCellsChunk74_positive_count :
    (twentyEightLayerCellChunk74.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk75_length :
    twentyEightLayerCellChunk75.length = 20 := by decide +kernel
theorem twentyEightCellsChunk75_positive_count :
    (twentyEightLayerCellChunk75.filter (fun c => 0 < c.value)).length = 19 := by decide +kernel

theorem twentyEightCellsChunk76_length :
    twentyEightLayerCellChunk76.length = 20 := by decide +kernel
theorem twentyEightCellsChunk76_positive_count :
    (twentyEightLayerCellChunk76.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk77_length :
    twentyEightLayerCellChunk77.length = 20 := by decide +kernel
theorem twentyEightCellsChunk77_positive_count :
    (twentyEightLayerCellChunk77.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk78_length :
    twentyEightLayerCellChunk78.length = 20 := by decide +kernel
theorem twentyEightCellsChunk78_positive_count :
    (twentyEightLayerCellChunk78.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk79_length :
    twentyEightLayerCellChunk79.length = 20 := by decide +kernel
theorem twentyEightCellsChunk79_positive_count :
    (twentyEightLayerCellChunk79.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk80_length :
    twentyEightLayerCellChunk80.length = 20 := by decide +kernel
theorem twentyEightCellsChunk80_positive_count :
    (twentyEightLayerCellChunk80.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk81_length :
    twentyEightLayerCellChunk81.length = 20 := by decide +kernel
theorem twentyEightCellsChunk81_positive_count :
    (twentyEightLayerCellChunk81.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk82_length :
    twentyEightLayerCellChunk82.length = 20 := by decide +kernel
theorem twentyEightCellsChunk82_positive_count :
    (twentyEightLayerCellChunk82.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk83_length :
    twentyEightLayerCellChunk83.length = 20 := by decide +kernel
theorem twentyEightCellsChunk83_positive_count :
    (twentyEightLayerCellChunk83.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk84_length :
    twentyEightLayerCellChunk84.length = 20 := by decide +kernel
theorem twentyEightCellsChunk84_positive_count :
    (twentyEightLayerCellChunk84.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk85_length :
    twentyEightLayerCellChunk85.length = 20 := by decide +kernel
theorem twentyEightCellsChunk85_positive_count :
    (twentyEightLayerCellChunk85.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk86_length :
    twentyEightLayerCellChunk86.length = 20 := by decide +kernel
theorem twentyEightCellsChunk86_positive_count :
    (twentyEightLayerCellChunk86.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk87_length :
    twentyEightLayerCellChunk87.length = 20 := by decide +kernel
theorem twentyEightCellsChunk87_positive_count :
    (twentyEightLayerCellChunk87.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk88_length :
    twentyEightLayerCellChunk88.length = 20 := by decide +kernel
theorem twentyEightCellsChunk88_positive_count :
    (twentyEightLayerCellChunk88.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk89_length :
    twentyEightLayerCellChunk89.length = 20 := by decide +kernel
theorem twentyEightCellsChunk89_positive_count :
    (twentyEightLayerCellChunk89.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk90_length :
    twentyEightLayerCellChunk90.length = 20 := by decide +kernel
theorem twentyEightCellsChunk90_positive_count :
    (twentyEightLayerCellChunk90.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk91_length :
    twentyEightLayerCellChunk91.length = 20 := by decide +kernel
theorem twentyEightCellsChunk91_positive_count :
    (twentyEightLayerCellChunk91.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk92_length :
    twentyEightLayerCellChunk92.length = 20 := by decide +kernel
theorem twentyEightCellsChunk92_positive_count :
    (twentyEightLayerCellChunk92.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk93_length :
    twentyEightLayerCellChunk93.length = 20 := by decide +kernel
theorem twentyEightCellsChunk93_positive_count :
    (twentyEightLayerCellChunk93.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk94_length :
    twentyEightLayerCellChunk94.length = 20 := by decide +kernel
theorem twentyEightCellsChunk94_positive_count :
    (twentyEightLayerCellChunk94.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk95_length :
    twentyEightLayerCellChunk95.length = 20 := by decide +kernel
theorem twentyEightCellsChunk95_positive_count :
    (twentyEightLayerCellChunk95.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk96_length :
    twentyEightLayerCellChunk96.length = 20 := by decide +kernel
theorem twentyEightCellsChunk96_positive_count :
    (twentyEightLayerCellChunk96.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk97_length :
    twentyEightLayerCellChunk97.length = 20 := by decide +kernel
theorem twentyEightCellsChunk97_positive_count :
    (twentyEightLayerCellChunk97.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk98_length :
    twentyEightLayerCellChunk98.length = 20 := by decide +kernel
theorem twentyEightCellsChunk98_positive_count :
    (twentyEightLayerCellChunk98.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk99_length :
    twentyEightLayerCellChunk99.length = 20 := by decide +kernel
theorem twentyEightCellsChunk99_positive_count :
    (twentyEightLayerCellChunk99.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk100_length :
    twentyEightLayerCellChunk100.length = 20 := by decide +kernel
theorem twentyEightCellsChunk100_positive_count :
    (twentyEightLayerCellChunk100.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk101_length :
    twentyEightLayerCellChunk101.length = 20 := by decide +kernel
theorem twentyEightCellsChunk101_positive_count :
    (twentyEightLayerCellChunk101.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk102_length :
    twentyEightLayerCellChunk102.length = 20 := by decide +kernel
theorem twentyEightCellsChunk102_positive_count :
    (twentyEightLayerCellChunk102.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk103_length :
    twentyEightLayerCellChunk103.length = 20 := by decide +kernel
theorem twentyEightCellsChunk103_positive_count :
    (twentyEightLayerCellChunk103.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk104_length :
    twentyEightLayerCellChunk104.length = 20 := by decide +kernel
theorem twentyEightCellsChunk104_positive_count :
    (twentyEightLayerCellChunk104.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk105_length :
    twentyEightLayerCellChunk105.length = 20 := by decide +kernel
theorem twentyEightCellsChunk105_positive_count :
    (twentyEightLayerCellChunk105.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk106_length :
    twentyEightLayerCellChunk106.length = 20 := by decide +kernel
theorem twentyEightCellsChunk106_positive_count :
    (twentyEightLayerCellChunk106.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk107_length :
    twentyEightLayerCellChunk107.length = 20 := by decide +kernel
theorem twentyEightCellsChunk107_positive_count :
    (twentyEightLayerCellChunk107.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk108_length :
    twentyEightLayerCellChunk108.length = 20 := by decide +kernel
theorem twentyEightCellsChunk108_positive_count :
    (twentyEightLayerCellChunk108.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk109_length :
    twentyEightLayerCellChunk109.length = 20 := by decide +kernel
theorem twentyEightCellsChunk109_positive_count :
    (twentyEightLayerCellChunk109.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk110_length :
    twentyEightLayerCellChunk110.length = 20 := by decide +kernel
theorem twentyEightCellsChunk110_positive_count :
    (twentyEightLayerCellChunk110.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk111_length :
    twentyEightLayerCellChunk111.length = 20 := by decide +kernel
theorem twentyEightCellsChunk111_positive_count :
    (twentyEightLayerCellChunk111.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk112_length :
    twentyEightLayerCellChunk112.length = 20 := by decide +kernel
theorem twentyEightCellsChunk112_positive_count :
    (twentyEightLayerCellChunk112.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk113_length :
    twentyEightLayerCellChunk113.length = 20 := by decide +kernel
theorem twentyEightCellsChunk113_positive_count :
    (twentyEightLayerCellChunk113.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk114_length :
    twentyEightLayerCellChunk114.length = 20 := by decide +kernel
theorem twentyEightCellsChunk114_positive_count :
    (twentyEightLayerCellChunk114.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk115_length :
    twentyEightLayerCellChunk115.length = 20 := by decide +kernel
theorem twentyEightCellsChunk115_positive_count :
    (twentyEightLayerCellChunk115.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk116_length :
    twentyEightLayerCellChunk116.length = 20 := by decide +kernel
theorem twentyEightCellsChunk116_positive_count :
    (twentyEightLayerCellChunk116.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk117_length :
    twentyEightLayerCellChunk117.length = 20 := by decide +kernel
theorem twentyEightCellsChunk117_positive_count :
    (twentyEightLayerCellChunk117.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk118_length :
    twentyEightLayerCellChunk118.length = 20 := by decide +kernel
theorem twentyEightCellsChunk118_positive_count :
    (twentyEightLayerCellChunk118.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk119_length :
    twentyEightLayerCellChunk119.length = 20 := by decide +kernel
theorem twentyEightCellsChunk119_positive_count :
    (twentyEightLayerCellChunk119.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk120_length :
    twentyEightLayerCellChunk120.length = 20 := by decide +kernel
theorem twentyEightCellsChunk120_positive_count :
    (twentyEightLayerCellChunk120.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk121_length :
    twentyEightLayerCellChunk121.length = 20 := by decide +kernel
theorem twentyEightCellsChunk121_positive_count :
    (twentyEightLayerCellChunk121.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk122_length :
    twentyEightLayerCellChunk122.length = 20 := by decide +kernel
theorem twentyEightCellsChunk122_positive_count :
    (twentyEightLayerCellChunk122.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk123_length :
    twentyEightLayerCellChunk123.length = 20 := by decide +kernel
theorem twentyEightCellsChunk123_positive_count :
    (twentyEightLayerCellChunk123.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk124_length :
    twentyEightLayerCellChunk124.length = 20 := by decide +kernel
theorem twentyEightCellsChunk124_positive_count :
    (twentyEightLayerCellChunk124.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk125_length :
    twentyEightLayerCellChunk125.length = 20 := by decide +kernel
theorem twentyEightCellsChunk125_positive_count :
    (twentyEightLayerCellChunk125.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk126_length :
    twentyEightLayerCellChunk126.length = 20 := by decide +kernel
theorem twentyEightCellsChunk126_positive_count :
    (twentyEightLayerCellChunk126.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk127_length :
    twentyEightLayerCellChunk127.length = 20 := by decide +kernel
theorem twentyEightCellsChunk127_positive_count :
    (twentyEightLayerCellChunk127.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk128_length :
    twentyEightLayerCellChunk128.length = 20 := by decide +kernel
theorem twentyEightCellsChunk128_positive_count :
    (twentyEightLayerCellChunk128.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk129_length :
    twentyEightLayerCellChunk129.length = 20 := by decide +kernel
theorem twentyEightCellsChunk129_positive_count :
    (twentyEightLayerCellChunk129.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk130_length :
    twentyEightLayerCellChunk130.length = 20 := by decide +kernel
theorem twentyEightCellsChunk130_positive_count :
    (twentyEightLayerCellChunk130.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk131_length :
    twentyEightLayerCellChunk131.length = 20 := by decide +kernel
theorem twentyEightCellsChunk131_positive_count :
    (twentyEightLayerCellChunk131.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk132_length :
    twentyEightLayerCellChunk132.length = 20 := by decide +kernel
theorem twentyEightCellsChunk132_positive_count :
    (twentyEightLayerCellChunk132.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk133_length :
    twentyEightLayerCellChunk133.length = 20 := by decide +kernel
theorem twentyEightCellsChunk133_positive_count :
    (twentyEightLayerCellChunk133.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk134_length :
    twentyEightLayerCellChunk134.length = 20 := by decide +kernel
theorem twentyEightCellsChunk134_positive_count :
    (twentyEightLayerCellChunk134.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk135_length :
    twentyEightLayerCellChunk135.length = 20 := by decide +kernel
theorem twentyEightCellsChunk135_positive_count :
    (twentyEightLayerCellChunk135.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk136_length :
    twentyEightLayerCellChunk136.length = 20 := by decide +kernel
theorem twentyEightCellsChunk136_positive_count :
    (twentyEightLayerCellChunk136.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk137_length :
    twentyEightLayerCellChunk137.length = 20 := by decide +kernel
theorem twentyEightCellsChunk137_positive_count :
    (twentyEightLayerCellChunk137.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk138_length :
    twentyEightLayerCellChunk138.length = 20 := by decide +kernel
theorem twentyEightCellsChunk138_positive_count :
    (twentyEightLayerCellChunk138.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk139_length :
    twentyEightLayerCellChunk139.length = 20 := by decide +kernel
theorem twentyEightCellsChunk139_positive_count :
    (twentyEightLayerCellChunk139.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk140_length :
    twentyEightLayerCellChunk140.length = 20 := by decide +kernel
theorem twentyEightCellsChunk140_positive_count :
    (twentyEightLayerCellChunk140.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk141_length :
    twentyEightLayerCellChunk141.length = 20 := by decide +kernel
theorem twentyEightCellsChunk141_positive_count :
    (twentyEightLayerCellChunk141.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk142_length :
    twentyEightLayerCellChunk142.length = 20 := by decide +kernel
theorem twentyEightCellsChunk142_positive_count :
    (twentyEightLayerCellChunk142.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk143_length :
    twentyEightLayerCellChunk143.length = 20 := by decide +kernel
theorem twentyEightCellsChunk143_positive_count :
    (twentyEightLayerCellChunk143.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk144_length :
    twentyEightLayerCellChunk144.length = 20 := by decide +kernel
theorem twentyEightCellsChunk144_positive_count :
    (twentyEightLayerCellChunk144.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk145_length :
    twentyEightLayerCellChunk145.length = 20 := by decide +kernel
theorem twentyEightCellsChunk145_positive_count :
    (twentyEightLayerCellChunk145.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk146_length :
    twentyEightLayerCellChunk146.length = 20 := by decide +kernel
theorem twentyEightCellsChunk146_positive_count :
    (twentyEightLayerCellChunk146.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk147_length :
    twentyEightLayerCellChunk147.length = 20 := by decide +kernel
theorem twentyEightCellsChunk147_positive_count :
    (twentyEightLayerCellChunk147.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk148_length :
    twentyEightLayerCellChunk148.length = 20 := by decide +kernel
theorem twentyEightCellsChunk148_positive_count :
    (twentyEightLayerCellChunk148.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk149_length :
    twentyEightLayerCellChunk149.length = 20 := by decide +kernel
theorem twentyEightCellsChunk149_positive_count :
    (twentyEightLayerCellChunk149.filter (fun c => 0 < c.value)).length = 20 := by decide +kernel

theorem twentyEightCellsChunk150_length :
    twentyEightLayerCellChunk150.length = 4 := by decide +kernel
theorem twentyEightCellsChunk150_positive_count :
    (twentyEightLayerCellChunk150.filter (fun c => 0 < c.value)).length = 2 := by decide +kernel

theorem twentyEightLayerCellTable_length : twentyEightLayerCellTable.length = 3004 := by
  unfold twentyEightLayerCellTable
  exact cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (cell_length_append (twentyEightCellsChunk0_length) twentyEightCellsChunk1_length) twentyEightCellsChunk2_length) twentyEightCellsChunk3_length) twentyEightCellsChunk4_length) twentyEightCellsChunk5_length) twentyEightCellsChunk6_length) twentyEightCellsChunk7_length) twentyEightCellsChunk8_length) twentyEightCellsChunk9_length) twentyEightCellsChunk10_length) twentyEightCellsChunk11_length) twentyEightCellsChunk12_length) twentyEightCellsChunk13_length) twentyEightCellsChunk14_length) twentyEightCellsChunk15_length) twentyEightCellsChunk16_length) twentyEightCellsChunk17_length) twentyEightCellsChunk18_length) twentyEightCellsChunk19_length) twentyEightCellsChunk20_length) twentyEightCellsChunk21_length) twentyEightCellsChunk22_length) twentyEightCellsChunk23_length) twentyEightCellsChunk24_length) twentyEightCellsChunk25_length) twentyEightCellsChunk26_length) twentyEightCellsChunk27_length) twentyEightCellsChunk28_length) twentyEightCellsChunk29_length) twentyEightCellsChunk30_length) twentyEightCellsChunk31_length) twentyEightCellsChunk32_length) twentyEightCellsChunk33_length) twentyEightCellsChunk34_length) twentyEightCellsChunk35_length) twentyEightCellsChunk36_length) twentyEightCellsChunk37_length) twentyEightCellsChunk38_length) twentyEightCellsChunk39_length) twentyEightCellsChunk40_length) twentyEightCellsChunk41_length) twentyEightCellsChunk42_length) twentyEightCellsChunk43_length) twentyEightCellsChunk44_length) twentyEightCellsChunk45_length) twentyEightCellsChunk46_length) twentyEightCellsChunk47_length) twentyEightCellsChunk48_length) twentyEightCellsChunk49_length) twentyEightCellsChunk50_length) twentyEightCellsChunk51_length) twentyEightCellsChunk52_length) twentyEightCellsChunk53_length) twentyEightCellsChunk54_length) twentyEightCellsChunk55_length) twentyEightCellsChunk56_length) twentyEightCellsChunk57_length) twentyEightCellsChunk58_length) twentyEightCellsChunk59_length) twentyEightCellsChunk60_length) twentyEightCellsChunk61_length) twentyEightCellsChunk62_length) twentyEightCellsChunk63_length) twentyEightCellsChunk64_length) twentyEightCellsChunk65_length) twentyEightCellsChunk66_length) twentyEightCellsChunk67_length) twentyEightCellsChunk68_length) twentyEightCellsChunk69_length) twentyEightCellsChunk70_length) twentyEightCellsChunk71_length) twentyEightCellsChunk72_length) twentyEightCellsChunk73_length) twentyEightCellsChunk74_length) twentyEightCellsChunk75_length) twentyEightCellsChunk76_length) twentyEightCellsChunk77_length) twentyEightCellsChunk78_length) twentyEightCellsChunk79_length) twentyEightCellsChunk80_length) twentyEightCellsChunk81_length) twentyEightCellsChunk82_length) twentyEightCellsChunk83_length) twentyEightCellsChunk84_length) twentyEightCellsChunk85_length) twentyEightCellsChunk86_length) twentyEightCellsChunk87_length) twentyEightCellsChunk88_length) twentyEightCellsChunk89_length) twentyEightCellsChunk90_length) twentyEightCellsChunk91_length) twentyEightCellsChunk92_length) twentyEightCellsChunk93_length) twentyEightCellsChunk94_length) twentyEightCellsChunk95_length) twentyEightCellsChunk96_length) twentyEightCellsChunk97_length) twentyEightCellsChunk98_length) twentyEightCellsChunk99_length) twentyEightCellsChunk100_length) twentyEightCellsChunk101_length) twentyEightCellsChunk102_length) twentyEightCellsChunk103_length) twentyEightCellsChunk104_length) twentyEightCellsChunk105_length) twentyEightCellsChunk106_length) twentyEightCellsChunk107_length) twentyEightCellsChunk108_length) twentyEightCellsChunk109_length) twentyEightCellsChunk110_length) twentyEightCellsChunk111_length) twentyEightCellsChunk112_length) twentyEightCellsChunk113_length) twentyEightCellsChunk114_length) twentyEightCellsChunk115_length) twentyEightCellsChunk116_length) twentyEightCellsChunk117_length) twentyEightCellsChunk118_length) twentyEightCellsChunk119_length) twentyEightCellsChunk120_length) twentyEightCellsChunk121_length) twentyEightCellsChunk122_length) twentyEightCellsChunk123_length) twentyEightCellsChunk124_length) twentyEightCellsChunk125_length) twentyEightCellsChunk126_length) twentyEightCellsChunk127_length) twentyEightCellsChunk128_length) twentyEightCellsChunk129_length) twentyEightCellsChunk130_length) twentyEightCellsChunk131_length) twentyEightCellsChunk132_length) twentyEightCellsChunk133_length) twentyEightCellsChunk134_length) twentyEightCellsChunk135_length) twentyEightCellsChunk136_length) twentyEightCellsChunk137_length) twentyEightCellsChunk138_length) twentyEightCellsChunk139_length) twentyEightCellsChunk140_length) twentyEightCellsChunk141_length) twentyEightCellsChunk142_length) twentyEightCellsChunk143_length) twentyEightCellsChunk144_length) twentyEightCellsChunk145_length) twentyEightCellsChunk146_length) twentyEightCellsChunk147_length) twentyEightCellsChunk148_length) twentyEightCellsChunk149_length) twentyEightCellsChunk150_length

theorem twentyEightLayerCellTable_positive_count : (twentyEightLayerCellTable.filter (fun c => 0 < c.value)).length = 3000 := by
  unfold twentyEightLayerCellTable
  exact cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (cell_positive_append (twentyEightCellsChunk0_positive_count) twentyEightCellsChunk1_positive_count) twentyEightCellsChunk2_positive_count) twentyEightCellsChunk3_positive_count) twentyEightCellsChunk4_positive_count) twentyEightCellsChunk5_positive_count) twentyEightCellsChunk6_positive_count) twentyEightCellsChunk7_positive_count) twentyEightCellsChunk8_positive_count) twentyEightCellsChunk9_positive_count) twentyEightCellsChunk10_positive_count) twentyEightCellsChunk11_positive_count) twentyEightCellsChunk12_positive_count) twentyEightCellsChunk13_positive_count) twentyEightCellsChunk14_positive_count) twentyEightCellsChunk15_positive_count) twentyEightCellsChunk16_positive_count) twentyEightCellsChunk17_positive_count) twentyEightCellsChunk18_positive_count) twentyEightCellsChunk19_positive_count) twentyEightCellsChunk20_positive_count) twentyEightCellsChunk21_positive_count) twentyEightCellsChunk22_positive_count) twentyEightCellsChunk23_positive_count) twentyEightCellsChunk24_positive_count) twentyEightCellsChunk25_positive_count) twentyEightCellsChunk26_positive_count) twentyEightCellsChunk27_positive_count) twentyEightCellsChunk28_positive_count) twentyEightCellsChunk29_positive_count) twentyEightCellsChunk30_positive_count) twentyEightCellsChunk31_positive_count) twentyEightCellsChunk32_positive_count) twentyEightCellsChunk33_positive_count) twentyEightCellsChunk34_positive_count) twentyEightCellsChunk35_positive_count) twentyEightCellsChunk36_positive_count) twentyEightCellsChunk37_positive_count) twentyEightCellsChunk38_positive_count) twentyEightCellsChunk39_positive_count) twentyEightCellsChunk40_positive_count) twentyEightCellsChunk41_positive_count) twentyEightCellsChunk42_positive_count) twentyEightCellsChunk43_positive_count) twentyEightCellsChunk44_positive_count) twentyEightCellsChunk45_positive_count) twentyEightCellsChunk46_positive_count) twentyEightCellsChunk47_positive_count) twentyEightCellsChunk48_positive_count) twentyEightCellsChunk49_positive_count) twentyEightCellsChunk50_positive_count) twentyEightCellsChunk51_positive_count) twentyEightCellsChunk52_positive_count) twentyEightCellsChunk53_positive_count) twentyEightCellsChunk54_positive_count) twentyEightCellsChunk55_positive_count) twentyEightCellsChunk56_positive_count) twentyEightCellsChunk57_positive_count) twentyEightCellsChunk58_positive_count) twentyEightCellsChunk59_positive_count) twentyEightCellsChunk60_positive_count) twentyEightCellsChunk61_positive_count) twentyEightCellsChunk62_positive_count) twentyEightCellsChunk63_positive_count) twentyEightCellsChunk64_positive_count) twentyEightCellsChunk65_positive_count) twentyEightCellsChunk66_positive_count) twentyEightCellsChunk67_positive_count) twentyEightCellsChunk68_positive_count) twentyEightCellsChunk69_positive_count) twentyEightCellsChunk70_positive_count) twentyEightCellsChunk71_positive_count) twentyEightCellsChunk72_positive_count) twentyEightCellsChunk73_positive_count) twentyEightCellsChunk74_positive_count) twentyEightCellsChunk75_positive_count) twentyEightCellsChunk76_positive_count) twentyEightCellsChunk77_positive_count) twentyEightCellsChunk78_positive_count) twentyEightCellsChunk79_positive_count) twentyEightCellsChunk80_positive_count) twentyEightCellsChunk81_positive_count) twentyEightCellsChunk82_positive_count) twentyEightCellsChunk83_positive_count) twentyEightCellsChunk84_positive_count) twentyEightCellsChunk85_positive_count) twentyEightCellsChunk86_positive_count) twentyEightCellsChunk87_positive_count) twentyEightCellsChunk88_positive_count) twentyEightCellsChunk89_positive_count) twentyEightCellsChunk90_positive_count) twentyEightCellsChunk91_positive_count) twentyEightCellsChunk92_positive_count) twentyEightCellsChunk93_positive_count) twentyEightCellsChunk94_positive_count) twentyEightCellsChunk95_positive_count) twentyEightCellsChunk96_positive_count) twentyEightCellsChunk97_positive_count) twentyEightCellsChunk98_positive_count) twentyEightCellsChunk99_positive_count) twentyEightCellsChunk100_positive_count) twentyEightCellsChunk101_positive_count) twentyEightCellsChunk102_positive_count) twentyEightCellsChunk103_positive_count) twentyEightCellsChunk104_positive_count) twentyEightCellsChunk105_positive_count) twentyEightCellsChunk106_positive_count) twentyEightCellsChunk107_positive_count) twentyEightCellsChunk108_positive_count) twentyEightCellsChunk109_positive_count) twentyEightCellsChunk110_positive_count) twentyEightCellsChunk111_positive_count) twentyEightCellsChunk112_positive_count) twentyEightCellsChunk113_positive_count) twentyEightCellsChunk114_positive_count) twentyEightCellsChunk115_positive_count) twentyEightCellsChunk116_positive_count) twentyEightCellsChunk117_positive_count) twentyEightCellsChunk118_positive_count) twentyEightCellsChunk119_positive_count) twentyEightCellsChunk120_positive_count) twentyEightCellsChunk121_positive_count) twentyEightCellsChunk122_positive_count) twentyEightCellsChunk123_positive_count) twentyEightCellsChunk124_positive_count) twentyEightCellsChunk125_positive_count) twentyEightCellsChunk126_positive_count) twentyEightCellsChunk127_positive_count) twentyEightCellsChunk128_positive_count) twentyEightCellsChunk129_positive_count) twentyEightCellsChunk130_positive_count) twentyEightCellsChunk131_positive_count) twentyEightCellsChunk132_positive_count) twentyEightCellsChunk133_positive_count) twentyEightCellsChunk134_positive_count) twentyEightCellsChunk135_positive_count) twentyEightCellsChunk136_positive_count) twentyEightCellsChunk137_positive_count) twentyEightCellsChunk138_positive_count) twentyEightCellsChunk139_positive_count) twentyEightCellsChunk140_positive_count) twentyEightCellsChunk141_positive_count) twentyEightCellsChunk142_positive_count) twentyEightCellsChunk143_positive_count) twentyEightCellsChunk144_positive_count) twentyEightCellsChunk145_positive_count) twentyEightCellsChunk146_positive_count) twentyEightCellsChunk147_positive_count) twentyEightCellsChunk148_positive_count) twentyEightCellsChunk149_positive_count) twentyEightCellsChunk150_positive_count

end OddPiPowers.L99
end
