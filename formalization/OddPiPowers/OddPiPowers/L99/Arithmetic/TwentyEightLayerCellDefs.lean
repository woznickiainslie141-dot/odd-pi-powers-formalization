module

public import OddPiPowers.Arithmetic.ContinuousCarry
public import OddPiPowers.L99.Arithmetic.TwentyEightLayerCellChunks

@[expose] public section

namespace OddPiPowers.L99

open scoped BigOperators

/-- The twentyEight-layer shape used by the arithmetic certificate. -/
def twentyEightLayerShape : CarryShape where
  L := 99
  J := 28
  offset := fun j => j.val
  weight := fun j => if j.val = 0 then 16 else 1
  twoOffset_lt := by
    intro j
    omega

@[simp] theorem twentyEightLayerShape_weight (j : Fin 28) :
    twentyEightLayerShape.weight j = if j.val = 0 then 16 else 1 := rfl

/-- Endpoint labels 0,...,27 denote the left branches and 28,...,55
denote the right branches, whose slopes are 58,...,99. -/
abbrev TwentyEightEndpoint := Fin 56

def twentyEightEndpointSlope (i : TwentyEightEndpoint) : ℕ :=
  if i.val < 28 then i.val else i.val + 44

def twentyEightAlpha (j : Fin 28) : TwentyEightEndpoint := ⟨j.val, by omega⟩

def twentyEightBeta (j : Fin 28) : TwentyEightEndpoint := ⟨55 - j.val, by omega⟩

@[simp] theorem twentyEightEndpointSlope_alpha (j : Fin 28) :
    twentyEightEndpointSlope (twentyEightAlpha j) = j.val := by
  simp [twentyEightEndpointSlope, twentyEightAlpha]

@[simp] theorem twentyEightEndpointSlope_beta (j : Fin 28) :
    twentyEightEndpointSlope (twentyEightBeta j) = 99 - j.val := by
  have hj : j.val < 28 := j.isLt
  simp [twentyEightEndpointSlope, twentyEightBeta, show ¬ 55 - j.val < 28 by omega]
  omega

theorem twentyEightEndpointSlope_injective : Function.Injective twentyEightEndpointSlope := by
  intro i j hij
  apply Fin.ext
  simp only [twentyEightEndpointSlope] at hij
  by_cases hi : i.val < 28 <;> by_cases hj : j.val < 28 <;> simp [hi, hj] at hij <;> omega

structure TwentyEightCellCertificate where
  leftNumerator : ℕ
  leftDenominator : ℕ
  rightNumerator : ℕ
  rightDenominator : ℕ
  rankCode : ℕ
  orderCode : ℕ
  floorCode : ℕ
  value : ℕ
  deriving DecidableEq, Repr

def TwentyEightCellCertificate.left (c : TwentyEightCellCertificate) : ℚ :=
  (c.leftNumerator : ℚ) / c.leftDenominator

def TwentyEightCellCertificate.right (c : TwentyEightCellCertificate) : ℚ :=
  (c.rightNumerator : ℚ) / c.rightDenominator


def twentyEightCellCertificateOfRaw (d : TwentyEightCellRawData) : TwentyEightCellCertificate where
  leftNumerator := d.leftNumerator
  leftDenominator := d.leftDenominator
  rightNumerator := d.rightNumerator
  rightDenominator := d.rightDenominator
  rankCode := d.rankCode
  orderCode := d.orderCode
  floorCode := d.floorCode
  value := d.value

def twentyEightLayerCellChunk0 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows0).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk1 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows1).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk2 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows2).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk3 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows3).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk4 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows4).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk5 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows5).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk6 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows6).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk7 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows7).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk8 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows8).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk9 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows9).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk10 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows10).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk11 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows11).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk12 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows12).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk13 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows13).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk14 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows14).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk15 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows15).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk16 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows16).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk17 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows17).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk18 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows18).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk19 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows19).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk20 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows20).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk21 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows21).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk22 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows22).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk23 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows23).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk24 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows24).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk25 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows25).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk26 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows26).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk27 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows27).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk28 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows28).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk29 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows29).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk30 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows30).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk31 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows31).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk32 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows32).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk33 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows33).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk34 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows34).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk35 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows35).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk36 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows36).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk37 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows37).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk38 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows38).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk39 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows39).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk40 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows40).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk41 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows41).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk42 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows42).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk43 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows43).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk44 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows44).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk45 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows45).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk46 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows46).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk47 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows47).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk48 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows48).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk49 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows49).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk50 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows50).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk51 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows51).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk52 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows52).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk53 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows53).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk54 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows54).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk55 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows55).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk56 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows56).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk57 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows57).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk58 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows58).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk59 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows59).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk60 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows60).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk61 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows61).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk62 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows62).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk63 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows63).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk64 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows64).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk65 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows65).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk66 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows66).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk67 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows67).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk68 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows68).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk69 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows69).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk70 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows70).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk71 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows71).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk72 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows72).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk73 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows73).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk74 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows74).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk75 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows75).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk76 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows76).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk77 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows77).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk78 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows78).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk79 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows79).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk80 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows80).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk81 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows81).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk82 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows82).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk83 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows83).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk84 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows84).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk85 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows85).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk86 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows86).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk87 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows87).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk88 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows88).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk89 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows89).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk90 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows90).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk91 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows91).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk92 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows92).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk93 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows93).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk94 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows94).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk95 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows95).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk96 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows96).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk97 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows97).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk98 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows98).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk99 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows99).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk100 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows100).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk101 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows101).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk102 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows102).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk103 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows103).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk104 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows104).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk105 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows105).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk106 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows106).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk107 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows107).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk108 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows108).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk109 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows109).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk110 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows110).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk111 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows111).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk112 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows112).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk113 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows113).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk114 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows114).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk115 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows115).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk116 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows116).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk117 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows117).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk118 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows118).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk119 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows119).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk120 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows120).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk121 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows121).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk122 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows122).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk123 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows123).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk124 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows124).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk125 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows125).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk126 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows126).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk127 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows127).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk128 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows128).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk129 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows129).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk130 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows130).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk131 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows131).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk132 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows132).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk133 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows133).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk134 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows134).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk135 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows135).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk136 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows136).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk137 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows137).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk138 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows138).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk139 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows139).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk140 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows140).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk141 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows141).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk142 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows142).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk143 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows143).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk144 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows144).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk145 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows145).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk146 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows146).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk147 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows147).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk148 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows148).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk149 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows149).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellChunk150 : List TwentyEightCellCertificate :=
  (twentyEightCellRawDataRows150).map twentyEightCellCertificateOfRaw

def twentyEightLayerCellTable : List TwentyEightCellCertificate :=
  twentyEightLayerCellChunk0 ++
  twentyEightLayerCellChunk1 ++
  twentyEightLayerCellChunk2 ++
  twentyEightLayerCellChunk3 ++
  twentyEightLayerCellChunk4 ++
  twentyEightLayerCellChunk5 ++
  twentyEightLayerCellChunk6 ++
  twentyEightLayerCellChunk7 ++
  twentyEightLayerCellChunk8 ++
  twentyEightLayerCellChunk9 ++
  twentyEightLayerCellChunk10 ++
  twentyEightLayerCellChunk11 ++
  twentyEightLayerCellChunk12 ++
  twentyEightLayerCellChunk13 ++
  twentyEightLayerCellChunk14 ++
  twentyEightLayerCellChunk15 ++
  twentyEightLayerCellChunk16 ++
  twentyEightLayerCellChunk17 ++
  twentyEightLayerCellChunk18 ++
  twentyEightLayerCellChunk19 ++
  twentyEightLayerCellChunk20 ++
  twentyEightLayerCellChunk21 ++
  twentyEightLayerCellChunk22 ++
  twentyEightLayerCellChunk23 ++
  twentyEightLayerCellChunk24 ++
  twentyEightLayerCellChunk25 ++
  twentyEightLayerCellChunk26 ++
  twentyEightLayerCellChunk27 ++
  twentyEightLayerCellChunk28 ++
  twentyEightLayerCellChunk29 ++
  twentyEightLayerCellChunk30 ++
  twentyEightLayerCellChunk31 ++
  twentyEightLayerCellChunk32 ++
  twentyEightLayerCellChunk33 ++
  twentyEightLayerCellChunk34 ++
  twentyEightLayerCellChunk35 ++
  twentyEightLayerCellChunk36 ++
  twentyEightLayerCellChunk37 ++
  twentyEightLayerCellChunk38 ++
  twentyEightLayerCellChunk39 ++
  twentyEightLayerCellChunk40 ++
  twentyEightLayerCellChunk41 ++
  twentyEightLayerCellChunk42 ++
  twentyEightLayerCellChunk43 ++
  twentyEightLayerCellChunk44 ++
  twentyEightLayerCellChunk45 ++
  twentyEightLayerCellChunk46 ++
  twentyEightLayerCellChunk47 ++
  twentyEightLayerCellChunk48 ++
  twentyEightLayerCellChunk49 ++
  twentyEightLayerCellChunk50 ++
  twentyEightLayerCellChunk51 ++
  twentyEightLayerCellChunk52 ++
  twentyEightLayerCellChunk53 ++
  twentyEightLayerCellChunk54 ++
  twentyEightLayerCellChunk55 ++
  twentyEightLayerCellChunk56 ++
  twentyEightLayerCellChunk57 ++
  twentyEightLayerCellChunk58 ++
  twentyEightLayerCellChunk59 ++
  twentyEightLayerCellChunk60 ++
  twentyEightLayerCellChunk61 ++
  twentyEightLayerCellChunk62 ++
  twentyEightLayerCellChunk63 ++
  twentyEightLayerCellChunk64 ++
  twentyEightLayerCellChunk65 ++
  twentyEightLayerCellChunk66 ++
  twentyEightLayerCellChunk67 ++
  twentyEightLayerCellChunk68 ++
  twentyEightLayerCellChunk69 ++
  twentyEightLayerCellChunk70 ++
  twentyEightLayerCellChunk71 ++
  twentyEightLayerCellChunk72 ++
  twentyEightLayerCellChunk73 ++
  twentyEightLayerCellChunk74 ++
  twentyEightLayerCellChunk75 ++
  twentyEightLayerCellChunk76 ++
  twentyEightLayerCellChunk77 ++
  twentyEightLayerCellChunk78 ++
  twentyEightLayerCellChunk79 ++
  twentyEightLayerCellChunk80 ++
  twentyEightLayerCellChunk81 ++
  twentyEightLayerCellChunk82 ++
  twentyEightLayerCellChunk83 ++
  twentyEightLayerCellChunk84 ++
  twentyEightLayerCellChunk85 ++
  twentyEightLayerCellChunk86 ++
  twentyEightLayerCellChunk87 ++
  twentyEightLayerCellChunk88 ++
  twentyEightLayerCellChunk89 ++
  twentyEightLayerCellChunk90 ++
  twentyEightLayerCellChunk91 ++
  twentyEightLayerCellChunk92 ++
  twentyEightLayerCellChunk93 ++
  twentyEightLayerCellChunk94 ++
  twentyEightLayerCellChunk95 ++
  twentyEightLayerCellChunk96 ++
  twentyEightLayerCellChunk97 ++
  twentyEightLayerCellChunk98 ++
  twentyEightLayerCellChunk99 ++
  twentyEightLayerCellChunk100 ++
  twentyEightLayerCellChunk101 ++
  twentyEightLayerCellChunk102 ++
  twentyEightLayerCellChunk103 ++
  twentyEightLayerCellChunk104 ++
  twentyEightLayerCellChunk105 ++
  twentyEightLayerCellChunk106 ++
  twentyEightLayerCellChunk107 ++
  twentyEightLayerCellChunk108 ++
  twentyEightLayerCellChunk109 ++
  twentyEightLayerCellChunk110 ++
  twentyEightLayerCellChunk111 ++
  twentyEightLayerCellChunk112 ++
  twentyEightLayerCellChunk113 ++
  twentyEightLayerCellChunk114 ++
  twentyEightLayerCellChunk115 ++
  twentyEightLayerCellChunk116 ++
  twentyEightLayerCellChunk117 ++
  twentyEightLayerCellChunk118 ++
  twentyEightLayerCellChunk119 ++
  twentyEightLayerCellChunk120 ++
  twentyEightLayerCellChunk121 ++
  twentyEightLayerCellChunk122 ++
  twentyEightLayerCellChunk123 ++
  twentyEightLayerCellChunk124 ++
  twentyEightLayerCellChunk125 ++
  twentyEightLayerCellChunk126 ++
  twentyEightLayerCellChunk127 ++
  twentyEightLayerCellChunk128 ++
  twentyEightLayerCellChunk129 ++
  twentyEightLayerCellChunk130 ++
  twentyEightLayerCellChunk131 ++
  twentyEightLayerCellChunk132 ++
  twentyEightLayerCellChunk133 ++
  twentyEightLayerCellChunk134 ++
  twentyEightLayerCellChunk135 ++
  twentyEightLayerCellChunk136 ++
  twentyEightLayerCellChunk137 ++
  twentyEightLayerCellChunk138 ++
  twentyEightLayerCellChunk139 ++
  twentyEightLayerCellChunk140 ++
  twentyEightLayerCellChunk141 ++
  twentyEightLayerCellChunk142 ++
  twentyEightLayerCellChunk143 ++
  twentyEightLayerCellChunk144 ++
  twentyEightLayerCellChunk145 ++
  twentyEightLayerCellChunk146 ++
  twentyEightLayerCellChunk147 ++
  twentyEightLayerCellChunk148 ++
  twentyEightLayerCellChunk149 ++
  twentyEightLayerCellChunk150

def twentyEightRank (code : ℕ) (i : TwentyEightEndpoint) : TwentyEightEndpoint :=
  ⟨(code / 56 ^ i.val) % 56, Nat.mod_lt _ (by decide)⟩

/-- Endpoint index at a given rank, decoded from the certified inverse rank
code. The validity proof checks that this code really is the inverse. -/
def twentyEightOrderEndpoint (code : ℕ) (r : TwentyEightEndpoint) : TwentyEightEndpoint :=
  ⟨(code / 56 ^ r.val) % 56, Nat.mod_lt _ (by decide)⟩

def twentyEightRankList (code : ℕ) : List TwentyEightEndpoint :=
  List.ofFn (twentyEightRank code)

def twentyEightCellMidpoint (c : TwentyEightCellCertificate) : ℚ :=
  (c.left + c.right) / 2

def twentyEightFloorDigit (code : ℕ) (i : TwentyEightEndpoint) : ℕ :=
  (code / 100 ^ i.val) % 100

def twentyEightCellFloor (c : TwentyEightCellCertificate) (i : TwentyEightEndpoint) : ℤ :=
  Int.ofNat (twentyEightFloorDigit c.floorCode i)

def twentyEightEndpointAffine (c : TwentyEightCellCertificate) (i : TwentyEightEndpoint)
    (x : ℚ) : ℚ :=
  (twentyEightEndpointSlope i : ℚ) * x - (twentyEightCellFloor c i : ℚ)

noncomputable def twentyEightEndpointReal (i : TwentyEightEndpoint) (z : ℝ) : ℝ :=
  Int.fract ((twentyEightEndpointSlope i : ℝ) * z)

def twentyEightGapLayer (code : ℕ) (k : TwentyEightEndpoint) (j : Fin 28) : ℕ :=
  let ra := (twentyEightRank code (twentyEightAlpha j)).val
  let rb := (twentyEightRank code (twentyEightBeta j)).val
  if rb < ra then
    if rb ≤ k.val ∧ k.val < ra then 1 else 0
  else if k.val < ra ∨ rb ≤ k.val then 1 else 0

def twentyEightPointLayer (code : ℕ) (q : TwentyEightEndpoint) (j : Fin 28) : ℕ :=
  let ra := (twentyEightRank code (twentyEightAlpha j)).val
  let rb := (twentyEightRank code (twentyEightBeta j)).val
  let rq := (twentyEightRank code q).val
  if rb < ra then
    if rb < rq ∧ rq < ra then 1 else 0
  else if rq < ra ∨ rb < rq then 1 else 0

def twentyEightGapCost (code : ℕ) (k : TwentyEightEndpoint) : ℕ :=
  (List.ofFn (fun j : Fin 28 => twentyEightLayerShape.weight j * twentyEightGapLayer code k j)).sum

def twentyEightPointCost (code : ℕ) (q : TwentyEightEndpoint) : ℕ :=
  (List.ofFn (fun j : Fin 28 => twentyEightLayerShape.weight j * twentyEightPointLayer code q j)).sum

def twentyEightCellMinGap (code : ℕ) : ℕ :=
  (List.ofFn (fun k : TwentyEightEndpoint => twentyEightGapCost code k)).foldl Nat.min 43

def TwentyEightCellCertificate.Valid (c : TwentyEightCellCertificate) : Prop :=
  0 < c.leftDenominator ∧ 0 < c.rightDenominator ∧
  c.leftNumerator * c.rightDenominator < c.rightNumerator * c.leftDenominator ∧
  c.rightNumerator ≤ c.rightDenominator ∧
  twentyEightRank c.rankCode ⟨0, by omega⟩ = ⟨0, by omega⟩ ∧
  (twentyEightRankList c.rankCode).Nodup ∧
  (∀ r : TwentyEightEndpoint,
    twentyEightRank c.rankCode (twentyEightOrderEndpoint c.orderCode r) = r) ∧
  (∀ i : TwentyEightEndpoint,
    twentyEightFloorDigit c.floorCode i * c.leftDenominator ≤
      twentyEightEndpointSlope i * c.leftNumerator ∧
    twentyEightEndpointSlope i * c.rightNumerator ≤
      (twentyEightFloorDigit c.floorCode i + 1) * c.rightDenominator) ∧
  (∀ k : Fin 55,
    twentyEightEndpointSlope (twentyEightOrderEndpoint c.orderCode k.castSucc) * c.leftNumerator +
        twentyEightFloorDigit c.floorCode (twentyEightOrderEndpoint c.orderCode k.succ) *
          c.leftDenominator ≤
      twentyEightEndpointSlope (twentyEightOrderEndpoint c.orderCode k.succ) * c.leftNumerator +
        twentyEightFloorDigit c.floorCode (twentyEightOrderEndpoint c.orderCode k.castSucc) *
          c.leftDenominator ∧
    twentyEightEndpointSlope (twentyEightOrderEndpoint c.orderCode k.castSucc) * c.rightNumerator +
        twentyEightFloorDigit c.floorCode (twentyEightOrderEndpoint c.orderCode k.succ) *
          c.rightDenominator ≤
      twentyEightEndpointSlope (twentyEightOrderEndpoint c.orderCode k.succ) * c.rightNumerator +
        twentyEightFloorDigit c.floorCode (twentyEightOrderEndpoint c.orderCode k.castSucc) *
          c.rightDenominator) ∧
  c.value = twentyEightCellMinGap c.rankCode ∧
  (∀ k : TwentyEightEndpoint, c.value ≤ twentyEightGapCost c.rankCode k) ∧
  (∀ q : TwentyEightEndpoint, c.value ≤ twentyEightPointCost c.rankCode q)

instance (c : TwentyEightCellCertificate) : Decidable c.Valid := by
  unfold TwentyEightCellCertificate.Valid
  infer_instance


theorem twentyEightCell_all_cons {c : TwentyEightCellCertificate} {cs : List TwentyEightCellCertificate}
    (hc : c.Valid) (hcs : cs.all (fun d => d.Valid) = true) :
    (c :: cs).all (fun d => d.Valid) = true := by
  simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hc, hcs⟩

end OddPiPowers.L99

end
