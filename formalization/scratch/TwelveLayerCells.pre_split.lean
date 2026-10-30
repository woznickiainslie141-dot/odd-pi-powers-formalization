module

public import Mathlib.Data.Finset.Sort
public import OddPiPowers.Arithmetic.ContinuousCarry
public import OddPiPowers.Arithmetic.TwelveLayerCellChunks

@[expose] public section

namespace OddPiPowers

open scoped BigOperators

/-- The twelve-layer shape used by the arithmetic certificate. -/
def twelveLayerShape : CarryShape where
  L := 69
  J := 12
  offset := fun j => j.val
  weight := fun j => if j.val = 0 then 6 else 1
  twoOffset_lt := by
    intro j
    omega

@[simp] theorem twelveLayerShape_weight (j : Fin 12) :
    twelveLayerShape.weight j = if j.val = 0 then 6 else 1 := rfl

/-- Endpoint labels 0,...,11 denote the left branches and 12,...,23
denote the right branches, whose slopes are 58,...,69. -/
abbrev TwelveEndpoint := Fin 24

def twelveEndpointSlope (i : TwelveEndpoint) : ℕ :=
  if i.val < 12 then i.val else i.val + 46

def twelveAlpha (j : Fin 12) : TwelveEndpoint := ⟨j.val, by omega⟩

def twelveBeta (j : Fin 12) : TwelveEndpoint := ⟨23 - j.val, by omega⟩

@[simp] theorem twelveEndpointSlope_alpha (j : Fin 12) :
    twelveEndpointSlope (twelveAlpha j) = j.val := by
  simp [twelveEndpointSlope, twelveAlpha]

@[simp] theorem twelveEndpointSlope_beta (j : Fin 12) :
    twelveEndpointSlope (twelveBeta j) = 69 - j.val := by
  have hj : j.val < 12 := j.isLt
  simp [twelveEndpointSlope, twelveBeta, show ¬ 23 - j.val < 12 by omega]
  omega

theorem twelveEndpointSlope_injective : Function.Injective twelveEndpointSlope := by
  intro i j hij
  apply Fin.ext
  simp only [twelveEndpointSlope] at hij
  by_cases hi : i.val < 12 <;> by_cases hj : j.val < 12 <;> simp [hi, hj] at hij <;> omega

structure TwelveCellCertificate where
  leftNumerator : ℕ
  leftDenominator : ℕ
  rightNumerator : ℕ
  rightDenominator : ℕ
  rankCode : ℕ
  orderCode : ℕ
  floorCode : ℕ
  value : ℕ
  deriving DecidableEq, Repr

def TwelveCellCertificate.left (c : TwelveCellCertificate) : ℚ :=
  (c.leftNumerator : ℚ) / c.leftDenominator

def TwelveCellCertificate.right (c : TwelveCellCertificate) : ℚ :=
  (c.rightNumerator : ℚ) / c.rightDenominator


def twelveCellCertificateOfRaw (d : TwelveCellRawData) : TwelveCellCertificate where
  leftNumerator := d.leftNumerator
  leftDenominator := d.leftDenominator
  rightNumerator := d.rightNumerator
  rightDenominator := d.rightDenominator
  rankCode := d.rankCode
  orderCode := d.orderCode
  floorCode := d.floorCode
  value := d.value

def twelveLayerCellChunk0 : List TwelveCellCertificate :=
  (twelveCellRawDataRows0).map twelveCellCertificateOfRaw

def twelveLayerCellChunk1 : List TwelveCellCertificate :=
  (twelveCellRawDataRows1).map twelveCellCertificateOfRaw

def twelveLayerCellChunk2 : List TwelveCellCertificate :=
  (twelveCellRawDataRows2).map twelveCellCertificateOfRaw

def twelveLayerCellChunk3 : List TwelveCellCertificate :=
  (twelveCellRawDataRows3).map twelveCellCertificateOfRaw

def twelveLayerCellChunk4 : List TwelveCellCertificate :=
  (twelveCellRawDataRows4).map twelveCellCertificateOfRaw

def twelveLayerCellChunk5 : List TwelveCellCertificate :=
  (twelveCellRawDataRows5).map twelveCellCertificateOfRaw

def twelveLayerCellChunk6 : List TwelveCellCertificate :=
  (twelveCellRawDataRows6).map twelveCellCertificateOfRaw

def twelveLayerCellChunk7 : List TwelveCellCertificate :=
  (twelveCellRawDataRows7).map twelveCellCertificateOfRaw

def twelveLayerCellChunk8 : List TwelveCellCertificate :=
  (twelveCellRawDataRows8).map twelveCellCertificateOfRaw

def twelveLayerCellChunk9 : List TwelveCellCertificate :=
  (twelveCellRawDataRows9).map twelveCellCertificateOfRaw

def twelveLayerCellChunk10 : List TwelveCellCertificate :=
  (twelveCellRawDataRows10).map twelveCellCertificateOfRaw

def twelveLayerCellChunk11 : List TwelveCellCertificate :=
  (twelveCellRawDataRows11).map twelveCellCertificateOfRaw

def twelveLayerCellChunk12 : List TwelveCellCertificate :=
  (twelveCellRawDataRows12).map twelveCellCertificateOfRaw

def twelveLayerCellChunk13 : List TwelveCellCertificate :=
  (twelveCellRawDataRows13).map twelveCellCertificateOfRaw

def twelveLayerCellChunk14 : List TwelveCellCertificate :=
  (twelveCellRawDataRows14).map twelveCellCertificateOfRaw

def twelveLayerCellChunk15 : List TwelveCellCertificate :=
  (twelveCellRawDataRows15).map twelveCellCertificateOfRaw

def twelveLayerCellChunk16 : List TwelveCellCertificate :=
  (twelveCellRawDataRows16).map twelveCellCertificateOfRaw

def twelveLayerCellChunk17 : List TwelveCellCertificate :=
  (twelveCellRawDataRows17).map twelveCellCertificateOfRaw

def twelveLayerCellChunk18 : List TwelveCellCertificate :=
  (twelveCellRawDataRows18).map twelveCellCertificateOfRaw

def twelveLayerCellChunk19 : List TwelveCellCertificate :=
  (twelveCellRawDataRows19).map twelveCellCertificateOfRaw

def twelveLayerCellChunk20 : List TwelveCellCertificate :=
  (twelveCellRawDataRows20).map twelveCellCertificateOfRaw

def twelveLayerCellChunk21 : List TwelveCellCertificate :=
  (twelveCellRawDataRows21).map twelveCellCertificateOfRaw

def twelveLayerCellChunk22 : List TwelveCellCertificate :=
  (twelveCellRawDataRows22).map twelveCellCertificateOfRaw

def twelveLayerCellChunk23 : List TwelveCellCertificate :=
  (twelveCellRawDataRows23).map twelveCellCertificateOfRaw

def twelveLayerCellChunk24 : List TwelveCellCertificate :=
  (twelveCellRawDataRows24).map twelveCellCertificateOfRaw

def twelveLayerCellChunk25 : List TwelveCellCertificate :=
  (twelveCellRawDataRows25).map twelveCellCertificateOfRaw

def twelveLayerCellChunk26 : List TwelveCellCertificate :=
  (twelveCellRawDataRows26).map twelveCellCertificateOfRaw

def twelveLayerCellChunk27 : List TwelveCellCertificate :=
  (twelveCellRawDataRows27).map twelveCellCertificateOfRaw

def twelveLayerCellChunk28 : List TwelveCellCertificate :=
  (twelveCellRawDataRows28).map twelveCellCertificateOfRaw

def twelveLayerCellChunk29 : List TwelveCellCertificate :=
  (twelveCellRawDataRows29).map twelveCellCertificateOfRaw

def twelveLayerCellTable : List TwelveCellCertificate :=
  twelveLayerCellChunk0 ++
  twelveLayerCellChunk1 ++
  twelveLayerCellChunk2 ++
  twelveLayerCellChunk3 ++
  twelveLayerCellChunk4 ++
  twelveLayerCellChunk5 ++
  twelveLayerCellChunk6 ++
  twelveLayerCellChunk7 ++
  twelveLayerCellChunk8 ++
  twelveLayerCellChunk9 ++
  twelveLayerCellChunk10 ++
  twelveLayerCellChunk11 ++
  twelveLayerCellChunk12 ++
  twelveLayerCellChunk13 ++
  twelveLayerCellChunk14 ++
  twelveLayerCellChunk15 ++
  twelveLayerCellChunk16 ++
  twelveLayerCellChunk17 ++
  twelveLayerCellChunk18 ++
  twelveLayerCellChunk19 ++
  twelveLayerCellChunk20 ++
  twelveLayerCellChunk21 ++
  twelveLayerCellChunk22 ++
  twelveLayerCellChunk23 ++
  twelveLayerCellChunk24 ++
  twelveLayerCellChunk25 ++
  twelveLayerCellChunk26 ++
  twelveLayerCellChunk27 ++
  twelveLayerCellChunk28 ++
  twelveLayerCellChunk29
def twelveRank (code : ℕ) (i : TwelveEndpoint) : TwelveEndpoint :=
  ⟨(code / 24 ^ i.val) % 24, Nat.mod_lt _ (by decide)⟩

/-- Endpoint index at a given rank, decoded from the certified inverse rank
code. The validity proof checks that this code really is the inverse. -/
def twelveOrderEndpoint (code : ℕ) (r : TwelveEndpoint) : TwelveEndpoint :=
  ⟨(code / 24 ^ r.val) % 24, Nat.mod_lt _ (by decide)⟩

def twelveRankList (code : ℕ) : List TwelveEndpoint :=
  List.ofFn (twelveRank code)

def twelveCellMidpoint (c : TwelveCellCertificate) : ℚ :=
  (c.left + c.right) / 2

def twelveFloorDigit (code : ℕ) (i : TwelveEndpoint) : ℕ :=
  (code / 70 ^ i.val) % 70

def twelveCellFloor (c : TwelveCellCertificate) (i : TwelveEndpoint) : ℤ :=
  Int.ofNat (twelveFloorDigit c.floorCode i)

def twelveEndpointAffine (c : TwelveCellCertificate) (i : TwelveEndpoint)
    (x : ℚ) : ℚ :=
  (twelveEndpointSlope i : ℚ) * x - (twelveCellFloor c i : ℚ)

noncomputable def twelveEndpointReal (i : TwelveEndpoint) (z : ℝ) : ℝ :=
  Int.fract ((twelveEndpointSlope i : ℝ) * z)

def twelveGapLayer (code : ℕ) (k : TwelveEndpoint) (j : Fin 12) : ℕ :=
  let ra := (twelveRank code (twelveAlpha j)).val
  let rb := (twelveRank code (twelveBeta j)).val
  if rb < ra then
    if rb ≤ k.val ∧ k.val < ra then 1 else 0
  else if k.val < ra ∨ rb ≤ k.val then 1 else 0

def twelvePointLayer (code : ℕ) (q : TwelveEndpoint) (j : Fin 12) : ℕ :=
  let ra := (twelveRank code (twelveAlpha j)).val
  let rb := (twelveRank code (twelveBeta j)).val
  let rq := (twelveRank code q).val
  if rb < ra then
    if rb < rq ∧ rq < ra then 1 else 0
  else if rq < ra ∨ rb < rq then 1 else 0

def twelveGapCost (code : ℕ) (k : TwelveEndpoint) : ℕ :=
  (List.ofFn (fun j : Fin 12 => twelveLayerShape.weight j * twelveGapLayer code k j)).sum

def twelvePointCost (code : ℕ) (q : TwelveEndpoint) : ℕ :=
  (List.ofFn (fun j : Fin 12 => twelveLayerShape.weight j * twelvePointLayer code q j)).sum

def twelveCellMinGap (code : ℕ) : ℕ :=
  (List.ofFn (fun k : TwelveEndpoint => twelveGapCost code k)).foldl Nat.min 17

def TwelveCellCertificate.Valid (c : TwelveCellCertificate) : Prop :=
  0 < c.leftDenominator ∧ 0 < c.rightDenominator ∧
  c.leftNumerator * c.rightDenominator < c.rightNumerator * c.leftDenominator ∧
  c.rightNumerator ≤ c.rightDenominator ∧
  twelveRank c.rankCode ⟨0, by omega⟩ = ⟨0, by omega⟩ ∧
  (twelveRankList c.rankCode).Nodup ∧
  (∀ r : TwelveEndpoint,
    twelveRank c.rankCode (twelveOrderEndpoint c.orderCode r) = r) ∧
  (∀ i : TwelveEndpoint,
    twelveFloorDigit c.floorCode i * c.leftDenominator ≤
      twelveEndpointSlope i * c.leftNumerator ∧
    twelveEndpointSlope i * c.rightNumerator ≤
      (twelveFloorDigit c.floorCode i + 1) * c.rightDenominator) ∧
  (∀ k : Fin 23,
    twelveEndpointSlope (twelveOrderEndpoint c.orderCode k.castSucc) * c.leftNumerator +
        twelveFloorDigit c.floorCode (twelveOrderEndpoint c.orderCode k.succ) *
          c.leftDenominator ≤
      twelveEndpointSlope (twelveOrderEndpoint c.orderCode k.succ) * c.leftNumerator +
        twelveFloorDigit c.floorCode (twelveOrderEndpoint c.orderCode k.castSucc) *
          c.leftDenominator ∧
    twelveEndpointSlope (twelveOrderEndpoint c.orderCode k.castSucc) * c.rightNumerator +
        twelveFloorDigit c.floorCode (twelveOrderEndpoint c.orderCode k.succ) *
          c.rightDenominator ≤
      twelveEndpointSlope (twelveOrderEndpoint c.orderCode k.succ) * c.rightNumerator +
        twelveFloorDigit c.floorCode (twelveOrderEndpoint c.orderCode k.castSucc) *
          c.rightDenominator) ∧
  c.value = twelveCellMinGap c.rankCode ∧
  (∀ k : TwelveEndpoint, c.value ≤ twelveGapCost c.rankCode k) ∧
  (∀ q : TwelveEndpoint, c.value ≤ twelvePointCost c.rankCode q)

instance (c : TwelveCellCertificate) : Decidable c.Valid := by
  unfold TwelveCellCertificate.Valid
  infer_instance

private def twelveFirstCell : TwelveCellCertificate :=
  { leftNumerator := 0, leftDenominator := 1,
    rightNumerator := 1, rightDenominator := 69,
    rankCode := 1331214537196502869015340298036888,
    orderCode := 1331214537196502869015340298036888,
    floorCode := 0, value := 0 }

private theorem twelveEndpointSlope_le_69 (i : TwelveEndpoint) :
    twelveEndpointSlope i ≤ 69 := by
  unfold twelveEndpointSlope
  split_ifs <;> omega

private theorem twelveEndpointSlope_succ (k : Fin 23) :
    twelveEndpointSlope k.castSucc ≤ twelveEndpointSlope k.succ := by
  change (if k.val < 12 then k.val else k.val + 46) ≤
    (if k.val + 1 < 12 then k.val + 1 else k.val + 1 + 46)
  by_cases h₁ : k.val < 12 <;> by_cases h₂ : k.val + 1 < 12 <;>
    simp [h₁, h₂] <;> omega

private theorem twelveFirstCellFloor_zero (i : TwelveEndpoint) :
    twelveCellFloor twelveFirstCell i = 0 := by
  norm_num [twelveCellFloor, twelveFloorDigit, twelveFirstCell]

theorem twelveLayerCellChunk0_length :
    twelveLayerCellChunk0.length = 40 := by
  set_option maxRecDepth 10000 in
  rfl

/- BEGIN superseded bulk list proofs
theorem twelveCellsChunk0_valid :
    twelveLayerCellChunk0.all (fun c => c.Valid) = true := by
  set_option maxRecDepth 100000 in
  set_option maxHeartbeats 0 in
  decide

theorem twelveLayerCellChunk1_length :
    twelveLayerCellChunk1.length = 40 := by
  set_option maxRecDepth 10000 in
  rfl

theorem twelveCellsChunk1_valid :
    twelveLayerCellChunk1.all (fun c => c.Valid) = true := by
  set_option maxRecDepth 100000 in
  set_option maxHeartbeats 0 in
  norm_num [twelveLayerCellChunk1, twelveCellCertificateOfRaw,
    twelveCellRawDataRows1] <;> decide

theorem twelveLayerCellChunk2_length :
    twelveLayerCellChunk2.length = 40 := by
  set_option maxRecDepth 10000 in
  rfl

theorem twelveCellsChunk2_valid :
    twelveLayerCellChunk2.all (fun c => c.Valid) = true := by
  set_option maxRecDepth 100000 in
  set_option maxHeartbeats 0 in
  norm_num [twelveLayerCellChunk2, twelveCellCertificateOfRaw,
    twelveCellRawDataRows2] <;> decide

theorem twelveLayerCellChunk3_length :
    twelveLayerCellChunk3.length = 40 := by
  set_option maxRecDepth 10000 in
  rfl

theorem twelveCellsChunk3_valid :
    twelveLayerCellChunk3.all (fun c => c.Valid) = true := by
  set_option maxRecDepth 100000 in
  set_option maxHeartbeats 0 in
  norm_num [twelveLayerCellChunk3, twelveCellCertificateOfRaw,
    twelveCellRawDataRows3] <;> decide

theorem twelveLayerCellChunk4_length :
    twelveLayerCellChunk4.length = 40 := by
  set_option maxRecDepth 10000 in
  rfl

theorem twelveCellsChunk4_valid :
    twelveLayerCellChunk4.all (fun c => c.Valid) = true := by
  set_option maxRecDepth 100000 in
  set_option maxHeartbeats 0 in
  norm_num [twelveLayerCellChunk4, twelveCellCertificateOfRaw,
    twelveCellRawDataRows4] <;> decide

theorem twelveLayerCellChunk5_length :
    twelveLayerCellChunk5.length = 40 := by
  set_option maxRecDepth 10000 in
  rfl

theorem twelveCellsChunk5_valid :
    twelveLayerCellChunk5.all (fun c => c.Valid) = true := by
  set_option maxRecDepth 100000 in
  set_option maxHeartbeats 0 in
  norm_num [twelveLayerCellChunk5, twelveCellCertificateOfRaw,
    twelveCellRawDataRows5] <;> decide

theorem twelveLayerCellChunk6_length :
    twelveLayerCellChunk6.length = 40 := by
  set_option maxRecDepth 10000 in
  rfl

theorem twelveCellsChunk6_valid :
    twelveLayerCellChunk6.all (fun c => c.Valid) = true := by
  set_option maxRecDepth 100000 in
  set_option maxHeartbeats 0 in
  norm_num [twelveLayerCellChunk6, twelveCellCertificateOfRaw,
    twelveCellRawDataRows6] <;> decide

theorem twelveLayerCellChunk7_length :
    twelveLayerCellChunk7.length = 40 := by
  set_option maxRecDepth 10000 in
  rfl

theorem twelveCellsChunk7_valid :
    twelveLayerCellChunk7.all (fun c => c.Valid) = true := by
  set_option maxRecDepth 100000 in
  set_option maxHeartbeats 0 in
  norm_num [twelveLayerCellChunk7, twelveCellCertificateOfRaw,
    twelveCellRawDataRows7] <;> decide

theorem twelveLayerCellChunk8_length :
    twelveLayerCellChunk8.length = 40 := by
  set_option maxRecDepth 10000 in
  rfl

theorem twelveCellsChunk8_valid :
    twelveLayerCellChunk8.all (fun c => c.Valid) = true := by
  set_option maxRecDepth 100000 in
  set_option maxHeartbeats 0 in
  norm_num [twelveLayerCellChunk8, twelveCellCertificateOfRaw,
    twelveCellRawDataRows8] <;> decide

theorem twelveLayerCellChunk9_length :
    twelveLayerCellChunk9.length = 40 := by
  set_option maxRecDepth 10000 in
  rfl

theorem twelveCellsChunk9_valid :
    twelveLayerCellChunk9.all (fun c => c.Valid) = true := by
  set_option maxRecDepth 100000 in
  set_option maxHeartbeats 0 in
  norm_num [twelveLayerCellChunk9, twelveCellCertificateOfRaw,
    twelveCellRawDataRows9] <;> decide

theorem twelveLayerCellChunk10_length :
    twelveLayerCellChunk10.length = 40 := by
  set_option maxRecDepth 10000 in
  rfl

theorem twelveCellsChunk10_valid :
    twelveLayerCellChunk10.all (fun c => c.Valid) = true := by
  set_option maxRecDepth 100000 in
  set_option maxHeartbeats 0 in
  norm_num [twelveLayerCellChunk10, twelveCellCertificateOfRaw,
    twelveCellRawDataRows10] <;> decide

theorem twelveLayerCellChunk11_length :
    twelveLayerCellChunk11.length = 40 := by
  set_option maxRecDepth 10000 in
  rfl

theorem twelveCellsChunk11_valid :
    twelveLayerCellChunk11.all (fun c => c.Valid) = true := by
  set_option maxRecDepth 100000 in
  set_option maxHeartbeats 0 in
  norm_num [twelveLayerCellChunk11, twelveCellCertificateOfRaw,
    twelveCellRawDataRows11] <;> decide

theorem twelveLayerCellChunk12_length :
    twelveLayerCellChunk12.length = 40 := by
  set_option maxRecDepth 10000 in
  rfl

theorem twelveCellsChunk12_valid :
    twelveLayerCellChunk12.all (fun c => c.Valid) = true := by
  set_option maxRecDepth 100000 in
  set_option maxHeartbeats 0 in
  norm_num [twelveLayerCellChunk12, twelveCellCertificateOfRaw,
    twelveCellRawDataRows12] <;> decide

theorem twelveLayerCellChunk13_length :
    twelveLayerCellChunk13.length = 40 := by
  set_option maxRecDepth 10000 in
  rfl

theorem twelveCellsChunk13_valid :
    twelveLayerCellChunk13.all (fun c => c.Valid) = true := by
  set_option maxRecDepth 100000 in
  set_option maxHeartbeats 0 in
  norm_num [twelveLayerCellChunk13, twelveCellCertificateOfRaw,
    twelveCellRawDataRows13] <;> decide

theorem twelveLayerCellChunk14_length :
    twelveLayerCellChunk14.length = 40 := by
  set_option maxRecDepth 10000 in
  rfl

theorem twelveCellsChunk14_valid :
    twelveLayerCellChunk14.all (fun c => c.Valid) = true := by
  set_option maxRecDepth 100000 in
  set_option maxHeartbeats 0 in
  norm_num [twelveLayerCellChunk14, twelveCellCertificateOfRaw,
    twelveCellRawDataRows14] <;> decide

theorem twelveLayerCellChunk15_length :
    twelveLayerCellChunk15.length = 40 := by
  set_option maxRecDepth 10000 in
  rfl

theorem twelveCellsChunk15_valid :
    twelveLayerCellChunk15.all (fun c => c.Valid) = true := by
  set_option maxRecDepth 100000 in
  set_option maxHeartbeats 0 in
  norm_num [twelveLayerCellChunk15, twelveCellCertificateOfRaw,
    twelveCellRawDataRows15] <;> decide

theorem twelveLayerCellChunk16_length :
    twelveLayerCellChunk16.length = 40 := by
  set_option maxRecDepth 10000 in
  rfl

theorem twelveCellsChunk16_valid :
    twelveLayerCellChunk16.all (fun c => c.Valid) = true := by
  set_option maxRecDepth 100000 in
  set_option maxHeartbeats 0 in
  norm_num [twelveLayerCellChunk16, twelveCellCertificateOfRaw,
    twelveCellRawDataRows16] <;> decide

theorem twelveLayerCellChunk17_length :
    twelveLayerCellChunk17.length = 40 := by
  set_option maxRecDepth 10000 in
  rfl

theorem twelveCellsChunk17_valid :
    twelveLayerCellChunk17.all (fun c => c.Valid) = true := by
  set_option maxRecDepth 100000 in
  set_option maxHeartbeats 0 in
  norm_num [twelveLayerCellChunk17, twelveCellCertificateOfRaw,
    twelveCellRawDataRows17] <;> decide

theorem twelveLayerCellChunk18_length :
    twelveLayerCellChunk18.length = 40 := by
  set_option maxRecDepth 10000 in
  rfl

theorem twelveCellsChunk18_valid :
    twelveLayerCellChunk18.all (fun c => c.Valid) = true := by
  set_option maxRecDepth 100000 in
  set_option maxHeartbeats 0 in
  norm_num [twelveLayerCellChunk18, twelveCellCertificateOfRaw,
    twelveCellRawDataRows18] <;> decide

theorem twelveLayerCellChunk19_length :
    twelveLayerCellChunk19.length = 40 := by
  set_option maxRecDepth 10000 in
  rfl

theorem twelveCellsChunk19_valid :
    twelveLayerCellChunk19.all (fun c => c.Valid) = true := by
  set_option maxRecDepth 100000 in
  set_option maxHeartbeats 0 in
  norm_num [twelveLayerCellChunk19, twelveCellCertificateOfRaw,
    twelveCellRawDataRows19] <;> decide

theorem twelveLayerCellChunk20_length :
    twelveLayerCellChunk20.length = 40 := by
  set_option maxRecDepth 10000 in
  rfl

theorem twelveCellsChunk20_valid :
    twelveLayerCellChunk20.all (fun c => c.Valid) = true := by
  set_option maxRecDepth 100000 in
  set_option maxHeartbeats 0 in
  norm_num [twelveLayerCellChunk20, twelveCellCertificateOfRaw,
    twelveCellRawDataRows20] <;> decide

theorem twelveLayerCellChunk21_length :
    twelveLayerCellChunk21.length = 40 := by
  set_option maxRecDepth 10000 in
  rfl

theorem twelveCellsChunk21_valid :
    twelveLayerCellChunk21.all (fun c => c.Valid) = true := by
  set_option maxRecDepth 100000 in
  set_option maxHeartbeats 0 in
  norm_num [twelveLayerCellChunk21, twelveCellCertificateOfRaw,
    twelveCellRawDataRows21] <;> decide

theorem twelveLayerCellChunk22_length :
    twelveLayerCellChunk22.length = 40 := by
  set_option maxRecDepth 10000 in
  rfl

theorem twelveCellsChunk22_valid :
    twelveLayerCellChunk22.all (fun c => c.Valid) = true := by
  set_option maxRecDepth 100000 in
  set_option maxHeartbeats 0 in
  norm_num [twelveLayerCellChunk22, twelveCellCertificateOfRaw,
    twelveCellRawDataRows22] <;> decide

theorem twelveLayerCellChunk23_length :
    twelveLayerCellChunk23.length = 40 := by
  set_option maxRecDepth 10000 in
  rfl

theorem twelveCellsChunk23_valid :
    twelveLayerCellChunk23.all (fun c => c.Valid) = true := by
  set_option maxRecDepth 100000 in
  set_option maxHeartbeats 0 in
  norm_num [twelveLayerCellChunk23, twelveCellCertificateOfRaw,
    twelveCellRawDataRows23] <;> decide

theorem twelveLayerCellChunk24_length :
    twelveLayerCellChunk24.length = 40 := by
  set_option maxRecDepth 10000 in
  rfl

theorem twelveCellsChunk24_valid :
    twelveLayerCellChunk24.all (fun c => c.Valid) = true := by
  set_option maxRecDepth 100000 in
  set_option maxHeartbeats 0 in
  norm_num [twelveLayerCellChunk24, twelveCellCertificateOfRaw,
    twelveCellRawDataRows24] <;> decide

theorem twelveLayerCellChunk25_length :
    twelveLayerCellChunk25.length = 40 := by
  set_option maxRecDepth 10000 in
  rfl

theorem twelveCellsChunk25_valid :
    twelveLayerCellChunk25.all (fun c => c.Valid) = true := by
  set_option maxRecDepth 100000 in
  set_option maxHeartbeats 0 in
  norm_num [twelveLayerCellChunk25, twelveCellCertificateOfRaw,
    twelveCellRawDataRows25] <;> decide

theorem twelveLayerCellChunk26_length :
    twelveLayerCellChunk26.length = 40 := by
  set_option maxRecDepth 10000 in
  rfl

theorem twelveCellsChunk26_valid :
    twelveLayerCellChunk26.all (fun c => c.Valid) = true := by
  set_option maxRecDepth 100000 in
  set_option maxHeartbeats 0 in
  norm_num [twelveLayerCellChunk26, twelveCellCertificateOfRaw,
    twelveCellRawDataRows26] <;> decide

theorem twelveLayerCellChunk27_length :
    twelveLayerCellChunk27.length = 40 := by
  set_option maxRecDepth 10000 in
  rfl

theorem twelveCellsChunk27_valid :
    twelveLayerCellChunk27.all (fun c => c.Valid) = true := by
  set_option maxRecDepth 100000 in
  set_option maxHeartbeats 0 in
  norm_num [twelveLayerCellChunk27, twelveCellCertificateOfRaw,
    twelveCellRawDataRows27] <;> decide

theorem twelveLayerCellChunk28_length :
    twelveLayerCellChunk28.length = 40 := by
  set_option maxRecDepth 10000 in
  rfl

theorem twelveCellsChunk28_valid :
    twelveLayerCellChunk28.all (fun c => c.Valid) = true := by
  set_option maxRecDepth 100000 in
  set_option maxHeartbeats 0 in
  norm_num [twelveLayerCellChunk28, twelveCellCertificateOfRaw,
    twelveCellRawDataRows28] <;> decide

theorem twelveLayerCellChunk29_length :
    twelveLayerCellChunk29.length = 40 := by
  set_option maxRecDepth 10000 in
  rfl

theorem twelveCellsChunk29_valid :
    twelveLayerCellChunk29.all (fun c => c.Valid) = true := by
  set_option maxRecDepth 100000 in
  set_option maxHeartbeats 0 in
  norm_num [twelveLayerCellChunk29, twelveCellCertificateOfRaw,
    twelveCellRawDataRows29] <;> decide

theorem twelveLayerCellTable_length : twelveLayerCellTable.length = 1180 := by
  simp [twelveLayerCellTable, twelveLayerCellChunk0_length,
    twelveLayerCellChunk1_length,
    twelveLayerCellChunk2_length,
    twelveLayerCellChunk3_length,
    twelveLayerCellChunk4_length,
    twelveLayerCellChunk5_length,
    twelveLayerCellChunk6_length,
    twelveLayerCellChunk7_length,
    twelveLayerCellChunk8_length,
    twelveLayerCellChunk9_length,
    twelveLayerCellChunk10_length,
    twelveLayerCellChunk11_length,
    twelveLayerCellChunk12_length,
    twelveLayerCellChunk13_length,
    twelveLayerCellChunk14_length,
    twelveLayerCellChunk15_length,
    twelveLayerCellChunk16_length,
    twelveLayerCellChunk17_length,
    twelveLayerCellChunk18_length,
    twelveLayerCellChunk19_length,
    twelveLayerCellChunk20_length,
    twelveLayerCellChunk21_length,
    twelveLayerCellChunk22_length,
    twelveLayerCellChunk23_length,
    twelveLayerCellChunk24_length,
    twelveLayerCellChunk25_length,
    twelveLayerCellChunk26_length,
    twelveLayerCellChunk27_length,
    twelveLayerCellChunk28_length,
    twelveLayerCellChunk29_length]

theorem twelveLayerCellTable_all_valid :
    ∀ c ∈ twelveLayerCellTable, c.Valid := by
  have hall : twelveLayerCellTable.all (fun c => c.Valid) = true := by
    simp [twelveLayerCellTable, twelveCellsChunk0_valid,
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
    twelveCellsChunk29_valid]
  intro c hc
  simpa using (List.all_eq_true.mp hall c hc)


/- theorem twelveLayerFirstCell_valid :
    (twelveLayerCellTable.getD 0 ⟨0, 1, 0, 0, 0, 0⟩).Valid := by
  have hfirst : twelveLayerCellTable.getD 0 ⟨0, 1, 0, 0, 0, 0⟩ = twelveFirstCell := by
    set_option maxRecDepth 10000 in
    norm_num [twelveFirstCell, twelveLayerCellTable,
      twelveCellTableRow,
      twelveAdjacentBounds, twelveCutValues,
      twelveCutWitnessRows, twelveCutWitnessRows0, twelveRankValueRows,
       twelveRankValueRows0, twelveOrderCodeRows, twelveOrderCodeRows0,
       twelveFloorCodeRows, twelveFloorCodeRows0]
  rw [hfirst]
  unfold TwelveCellCertificate.Valid
  refine ⟨by norm_num [twelveFirstCell], by norm_num [twelveFirstCell],
    by norm_num [twelveFirstCell], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · intro i
    have hfloor := twelveFirstCellFloor_zero i
    constructor
    · rw [hfloor]
      norm_num [twelveFirstCell]
    · rw [hfloor]
      have hs := twelveEndpointSlope_le_69 i
      have hsQ : (twelveEndpointSlope i : ℚ) ≤ 69 := by exact_mod_cast hs
      norm_num [twelveFirstCell]
      nlinarith
  · intro k
    have horder : ∀ r : TwelveEndpoint,
        twelveOrderEndpoint twelveFirstCell.orderCode r = r := by decide
    have hi := horder k.castSucc
    have hj := horder k.succ
    constructor
    · simp only [twelveEndpointAffine]
      rw [hi, hj, twelveFirstCellFloor_zero, twelveFirstCellFloor_zero]
      simp [twelveFirstCell]
    · simp only [twelveEndpointAffine]
      rw [hi, hj, twelveFirstCellFloor_zero, twelveFirstCellFloor_zero]
      have hslQ : (twelveEndpointSlope k.castSucc : ℚ) ≤
          twelveEndpointSlope k.succ := by
        exact_mod_cast twelveEndpointSlope_succ k
      have hmul := mul_le_mul_of_nonneg_right hslQ
        (by norm_num : (0 : ℚ) ≤ 1 / 69)
      simpa [twelveFirstCell] using hmul
  · decide
  · decide
  · decide
-/
-/

private theorem twelveList_all_true_of_get {α : Type} (l : List α)
    (p : α → Prop) [DecidablePred p]
    (h : ∀ i : Fin l.length, p (l.get i)) :
    l.all (fun a => p a) = true := by
  apply List.all_eq_true.mpr
  intro a ha
  rcases List.mem_iff_get.mp ha with ⟨i, hi⟩
  rw [← hi]
  simpa using h i

theorem twelveCellsChunk0_get_valid :
    ∀ j : Fin twelveLayerCellChunk0.length,
      (twelveLayerCellChunk0.get j).Valid := by
  set_option maxRecDepth 10000 in
  set_option maxHeartbeats 0 in
  intro j
  fin_cases j <;> decide

theorem twelveCellsChunk0_valid :
    twelveLayerCellChunk0.all (fun c => c.Valid) = true := by
  exact twelveList_all_true_of_get twelveLayerCellChunk0
    (fun c => c.Valid) twelveCellsChunk0_get_valid

theorem twelveCellsChunk1_get_valid :
    ∀ j : Fin twelveLayerCellChunk1.length,
      (twelveLayerCellChunk1.get j).Valid := by
  set_option maxRecDepth 10000 in
  set_option maxHeartbeats 0 in
  intro j
  fin_cases j <;> decide

theorem twelveCellsChunk1_valid :
    twelveLayerCellChunk1.all (fun c => c.Valid) = true := by
  exact twelveList_all_true_of_get twelveLayerCellChunk1
    (fun c => c.Valid) twelveCellsChunk1_get_valid

theorem twelveCellsChunk2_get_valid :
    ∀ j : Fin twelveLayerCellChunk2.length,
      (twelveLayerCellChunk2.get j).Valid := by
  set_option maxRecDepth 10000 in
  set_option maxHeartbeats 0 in
  intro j
  fin_cases j <;> decide

theorem twelveCellsChunk2_valid :
    twelveLayerCellChunk2.all (fun c => c.Valid) = true := by
  exact twelveList_all_true_of_get twelveLayerCellChunk2
    (fun c => c.Valid) twelveCellsChunk2_get_valid

theorem twelveCellsChunk3_get_valid :
    ∀ j : Fin twelveLayerCellChunk3.length,
      (twelveLayerCellChunk3.get j).Valid := by
  set_option maxRecDepth 10000 in
  set_option maxHeartbeats 0 in
  intro j
  fin_cases j <;> decide

theorem twelveCellsChunk3_valid :
    twelveLayerCellChunk3.all (fun c => c.Valid) = true := by
  exact twelveList_all_true_of_get twelveLayerCellChunk3
    (fun c => c.Valid) twelveCellsChunk3_get_valid

theorem twelveCellsChunk4_get_valid :
    ∀ j : Fin twelveLayerCellChunk4.length,
      (twelveLayerCellChunk4.get j).Valid := by
  set_option maxRecDepth 10000 in
  set_option maxHeartbeats 0 in
  intro j
  fin_cases j <;> decide

theorem twelveCellsChunk4_valid :
    twelveLayerCellChunk4.all (fun c => c.Valid) = true := by
  exact twelveList_all_true_of_get twelveLayerCellChunk4
    (fun c => c.Valid) twelveCellsChunk4_get_valid

theorem twelveCellsChunk5_get_valid :
    ∀ j : Fin twelveLayerCellChunk5.length,
      (twelveLayerCellChunk5.get j).Valid := by
  set_option maxRecDepth 10000 in
  set_option maxHeartbeats 0 in
  intro j
  fin_cases j <;> decide

theorem twelveCellsChunk5_valid :
    twelveLayerCellChunk5.all (fun c => c.Valid) = true := by
  exact twelveList_all_true_of_get twelveLayerCellChunk5
    (fun c => c.Valid) twelveCellsChunk5_get_valid

theorem twelveCellsChunk6_get_valid :
    ∀ j : Fin twelveLayerCellChunk6.length,
      (twelveLayerCellChunk6.get j).Valid := by
  set_option maxRecDepth 10000 in
  set_option maxHeartbeats 0 in
  intro j
  fin_cases j <;> decide

theorem twelveCellsChunk6_valid :
    twelveLayerCellChunk6.all (fun c => c.Valid) = true := by
  exact twelveList_all_true_of_get twelveLayerCellChunk6
    (fun c => c.Valid) twelveCellsChunk6_get_valid

theorem twelveCellsChunk7_get_valid :
    ∀ j : Fin twelveLayerCellChunk7.length,
      (twelveLayerCellChunk7.get j).Valid := by
  set_option maxRecDepth 10000 in
  set_option maxHeartbeats 0 in
  intro j
  fin_cases j <;> decide

theorem twelveCellsChunk7_valid :
    twelveLayerCellChunk7.all (fun c => c.Valid) = true := by
  exact twelveList_all_true_of_get twelveLayerCellChunk7
    (fun c => c.Valid) twelveCellsChunk7_get_valid

theorem twelveCellsChunk8_get_valid :
    ∀ j : Fin twelveLayerCellChunk8.length,
      (twelveLayerCellChunk8.get j).Valid := by
  set_option maxRecDepth 10000 in
  set_option maxHeartbeats 0 in
  intro j
  fin_cases j <;> decide

theorem twelveCellsChunk8_valid :
    twelveLayerCellChunk8.all (fun c => c.Valid) = true := by
  exact twelveList_all_true_of_get twelveLayerCellChunk8
    (fun c => c.Valid) twelveCellsChunk8_get_valid

theorem twelveCellsChunk9_get_valid :
    ∀ j : Fin twelveLayerCellChunk9.length,
      (twelveLayerCellChunk9.get j).Valid := by
  set_option maxRecDepth 10000 in
  set_option maxHeartbeats 0 in
  intro j
  fin_cases j <;> decide

theorem twelveCellsChunk9_valid :
    twelveLayerCellChunk9.all (fun c => c.Valid) = true := by
  exact twelveList_all_true_of_get twelveLayerCellChunk9
    (fun c => c.Valid) twelveCellsChunk9_get_valid

theorem twelveCellsChunk10_get_valid :
    ∀ j : Fin twelveLayerCellChunk10.length,
      (twelveLayerCellChunk10.get j).Valid := by
  set_option maxRecDepth 10000 in
  set_option maxHeartbeats 0 in
  intro j
  fin_cases j <;> decide

theorem twelveCellsChunk10_valid :
    twelveLayerCellChunk10.all (fun c => c.Valid) = true := by
  exact twelveList_all_true_of_get twelveLayerCellChunk10
    (fun c => c.Valid) twelveCellsChunk10_get_valid

theorem twelveCellsChunk11_get_valid :
    ∀ j : Fin twelveLayerCellChunk11.length,
      (twelveLayerCellChunk11.get j).Valid := by
  set_option maxRecDepth 10000 in
  set_option maxHeartbeats 0 in
  intro j
  fin_cases j <;> decide

theorem twelveCellsChunk11_valid :
    twelveLayerCellChunk11.all (fun c => c.Valid) = true := by
  exact twelveList_all_true_of_get twelveLayerCellChunk11
    (fun c => c.Valid) twelveCellsChunk11_get_valid

theorem twelveCellsChunk12_get_valid :
    ∀ j : Fin twelveLayerCellChunk12.length,
      (twelveLayerCellChunk12.get j).Valid := by
  set_option maxRecDepth 10000 in
  set_option maxHeartbeats 0 in
  intro j
  fin_cases j <;> decide

theorem twelveCellsChunk12_valid :
    twelveLayerCellChunk12.all (fun c => c.Valid) = true := by
  exact twelveList_all_true_of_get twelveLayerCellChunk12
    (fun c => c.Valid) twelveCellsChunk12_get_valid

theorem twelveCellsChunk13_get_valid :
    ∀ j : Fin twelveLayerCellChunk13.length,
      (twelveLayerCellChunk13.get j).Valid := by
  set_option maxRecDepth 10000 in
  set_option maxHeartbeats 0 in
  intro j
  fin_cases j <;> decide

theorem twelveCellsChunk13_valid :
    twelveLayerCellChunk13.all (fun c => c.Valid) = true := by
  exact twelveList_all_true_of_get twelveLayerCellChunk13
    (fun c => c.Valid) twelveCellsChunk13_get_valid

theorem twelveCellsChunk14_get_valid :
    ∀ j : Fin twelveLayerCellChunk14.length,
      (twelveLayerCellChunk14.get j).Valid := by
  set_option maxRecDepth 10000 in
  set_option maxHeartbeats 0 in
  intro j
  fin_cases j <;> decide

theorem twelveCellsChunk14_valid :
    twelveLayerCellChunk14.all (fun c => c.Valid) = true := by
  exact twelveList_all_true_of_get twelveLayerCellChunk14
    (fun c => c.Valid) twelveCellsChunk14_get_valid

theorem twelveCellsChunk15_get_valid :
    ∀ j : Fin twelveLayerCellChunk15.length,
      (twelveLayerCellChunk15.get j).Valid := by
  set_option maxRecDepth 10000 in
  set_option maxHeartbeats 0 in
  intro j
  fin_cases j <;> decide

theorem twelveCellsChunk15_valid :
    twelveLayerCellChunk15.all (fun c => c.Valid) = true := by
  exact twelveList_all_true_of_get twelveLayerCellChunk15
    (fun c => c.Valid) twelveCellsChunk15_get_valid

theorem twelveCellsChunk16_get_valid :
    ∀ j : Fin twelveLayerCellChunk16.length,
      (twelveLayerCellChunk16.get j).Valid := by
  set_option maxRecDepth 10000 in
  set_option maxHeartbeats 0 in
  intro j
  fin_cases j <;> decide

theorem twelveCellsChunk16_valid :
    twelveLayerCellChunk16.all (fun c => c.Valid) = true := by
  exact twelveList_all_true_of_get twelveLayerCellChunk16
    (fun c => c.Valid) twelveCellsChunk16_get_valid

theorem twelveCellsChunk17_get_valid :
    ∀ j : Fin twelveLayerCellChunk17.length,
      (twelveLayerCellChunk17.get j).Valid := by
  set_option maxRecDepth 10000 in
  set_option maxHeartbeats 0 in
  intro j
  fin_cases j <;> decide

theorem twelveCellsChunk17_valid :
    twelveLayerCellChunk17.all (fun c => c.Valid) = true := by
  exact twelveList_all_true_of_get twelveLayerCellChunk17
    (fun c => c.Valid) twelveCellsChunk17_get_valid

theorem twelveCellsChunk18_get_valid :
    ∀ j : Fin twelveLayerCellChunk18.length,
      (twelveLayerCellChunk18.get j).Valid := by
  set_option maxRecDepth 10000 in
  set_option maxHeartbeats 0 in
  intro j
  fin_cases j <;> decide

theorem twelveCellsChunk18_valid :
    twelveLayerCellChunk18.all (fun c => c.Valid) = true := by
  exact twelveList_all_true_of_get twelveLayerCellChunk18
    (fun c => c.Valid) twelveCellsChunk18_get_valid

theorem twelveCellsChunk19_get_valid :
    ∀ j : Fin twelveLayerCellChunk19.length,
      (twelveLayerCellChunk19.get j).Valid := by
  set_option maxRecDepth 10000 in
  set_option maxHeartbeats 0 in
  intro j
  fin_cases j <;> decide

theorem twelveCellsChunk19_valid :
    twelveLayerCellChunk19.all (fun c => c.Valid) = true := by
  exact twelveList_all_true_of_get twelveLayerCellChunk19
    (fun c => c.Valid) twelveCellsChunk19_get_valid

theorem twelveCellsChunk20_get_valid :
    ∀ j : Fin twelveLayerCellChunk20.length,
      (twelveLayerCellChunk20.get j).Valid := by
  set_option maxRecDepth 10000 in
  set_option maxHeartbeats 0 in
  intro j
  fin_cases j <;> decide

theorem twelveCellsChunk20_valid :
    twelveLayerCellChunk20.all (fun c => c.Valid) = true := by
  exact twelveList_all_true_of_get twelveLayerCellChunk20
    (fun c => c.Valid) twelveCellsChunk20_get_valid

theorem twelveCellsChunk21_get_valid :
    ∀ j : Fin twelveLayerCellChunk21.length,
      (twelveLayerCellChunk21.get j).Valid := by
  set_option maxRecDepth 10000 in
  set_option maxHeartbeats 0 in
  intro j
  fin_cases j <;> decide

theorem twelveCellsChunk21_valid :
    twelveLayerCellChunk21.all (fun c => c.Valid) = true := by
  exact twelveList_all_true_of_get twelveLayerCellChunk21
    (fun c => c.Valid) twelveCellsChunk21_get_valid

theorem twelveCellsChunk22_get_valid :
    ∀ j : Fin twelveLayerCellChunk22.length,
      (twelveLayerCellChunk22.get j).Valid := by
  set_option maxRecDepth 10000 in
  set_option maxHeartbeats 0 in
  intro j
  fin_cases j <;> decide

theorem twelveCellsChunk22_valid :
    twelveLayerCellChunk22.all (fun c => c.Valid) = true := by
  exact twelveList_all_true_of_get twelveLayerCellChunk22
    (fun c => c.Valid) twelveCellsChunk22_get_valid

theorem twelveCellsChunk23_get_valid :
    ∀ j : Fin twelveLayerCellChunk23.length,
      (twelveLayerCellChunk23.get j).Valid := by
  set_option maxRecDepth 10000 in
  set_option maxHeartbeats 0 in
  intro j
  fin_cases j <;> decide

theorem twelveCellsChunk23_valid :
    twelveLayerCellChunk23.all (fun c => c.Valid) = true := by
  exact twelveList_all_true_of_get twelveLayerCellChunk23
    (fun c => c.Valid) twelveCellsChunk23_get_valid

theorem twelveCellsChunk24_get_valid :
    ∀ j : Fin twelveLayerCellChunk24.length,
      (twelveLayerCellChunk24.get j).Valid := by
  set_option maxRecDepth 10000 in
  set_option maxHeartbeats 0 in
  intro j
  fin_cases j <;> decide

theorem twelveCellsChunk24_valid :
    twelveLayerCellChunk24.all (fun c => c.Valid) = true := by
  exact twelveList_all_true_of_get twelveLayerCellChunk24
    (fun c => c.Valid) twelveCellsChunk24_get_valid

theorem twelveCellsChunk25_get_valid :
    ∀ j : Fin twelveLayerCellChunk25.length,
      (twelveLayerCellChunk25.get j).Valid := by
  set_option maxRecDepth 10000 in
  set_option maxHeartbeats 0 in
  intro j
  fin_cases j <;> decide

theorem twelveCellsChunk25_valid :
    twelveLayerCellChunk25.all (fun c => c.Valid) = true := by
  exact twelveList_all_true_of_get twelveLayerCellChunk25
    (fun c => c.Valid) twelveCellsChunk25_get_valid

theorem twelveCellsChunk26_get_valid :
    ∀ j : Fin twelveLayerCellChunk26.length,
      (twelveLayerCellChunk26.get j).Valid := by
  set_option maxRecDepth 10000 in
  set_option maxHeartbeats 0 in
  intro j
  fin_cases j <;> decide

theorem twelveCellsChunk26_valid :
    twelveLayerCellChunk26.all (fun c => c.Valid) = true := by
  exact twelveList_all_true_of_get twelveLayerCellChunk26
    (fun c => c.Valid) twelveCellsChunk26_get_valid

theorem twelveCellsChunk27_get_valid :
    ∀ j : Fin twelveLayerCellChunk27.length,
      (twelveLayerCellChunk27.get j).Valid := by
  set_option maxRecDepth 10000 in
  set_option maxHeartbeats 0 in
  intro j
  fin_cases j <;> decide

theorem twelveCellsChunk27_valid :
    twelveLayerCellChunk27.all (fun c => c.Valid) = true := by
  exact twelveList_all_true_of_get twelveLayerCellChunk27
    (fun c => c.Valid) twelveCellsChunk27_get_valid

theorem twelveCellsChunk28_get_valid :
    ∀ j : Fin twelveLayerCellChunk28.length,
      (twelveLayerCellChunk28.get j).Valid := by
  set_option maxRecDepth 10000 in
  set_option maxHeartbeats 0 in
  intro j
  fin_cases j <;> decide

theorem twelveCellsChunk28_valid :
    twelveLayerCellChunk28.all (fun c => c.Valid) = true := by
  exact twelveList_all_true_of_get twelveLayerCellChunk28
    (fun c => c.Valid) twelveCellsChunk28_get_valid

theorem twelveCellsChunk29_get_valid :
    ∀ j : Fin twelveLayerCellChunk29.length,
      (twelveLayerCellChunk29.get j).Valid := by
  set_option maxRecDepth 10000 in
  set_option maxHeartbeats 0 in
  intro j
  fin_cases j <;> decide

theorem twelveCellsChunk29_valid :
    twelveLayerCellChunk29.all (fun c => c.Valid) = true := by
  exact twelveList_all_true_of_get twelveLayerCellChunk29
    (fun c => c.Valid) twelveCellsChunk29_get_valid

theorem twelveLayerCellTable_length : twelveLayerCellTable.length = 1180 := by
  simp [twelveLayerCellTable,
    twelveLayerCellChunk0_length,
    twelveLayerCellChunk1_length,
    twelveLayerCellChunk2_length,
    twelveLayerCellChunk3_length,
    twelveLayerCellChunk4_length,
    twelveLayerCellChunk5_length,
    twelveLayerCellChunk6_length,
    twelveLayerCellChunk7_length,
    twelveLayerCellChunk8_length,
    twelveLayerCellChunk9_length,
    twelveLayerCellChunk10_length,
    twelveLayerCellChunk11_length,
    twelveLayerCellChunk12_length,
    twelveLayerCellChunk13_length,
    twelveLayerCellChunk14_length,
    twelveLayerCellChunk15_length,
    twelveLayerCellChunk16_length,
    twelveLayerCellChunk17_length,
    twelveLayerCellChunk18_length,
    twelveLayerCellChunk19_length,
    twelveLayerCellChunk20_length,
    twelveLayerCellChunk21_length,
    twelveLayerCellChunk22_length,
    twelveLayerCellChunk23_length,
    twelveLayerCellChunk24_length,
    twelveLayerCellChunk25_length,
    twelveLayerCellChunk26_length,
    twelveLayerCellChunk27_length,
    twelveLayerCellChunk28_length,
    twelveLayerCellChunk29_length]

theorem twelveLayerCellTable_all_valid :
    ∀ c ∈ twelveLayerCellTable, c.Valid := by
  have hall : twelveLayerCellTable.all (fun c => c.Valid) = true := by
    simp [twelveLayerCellTable,
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
    twelveCellsChunk29_valid]
  intro c hc
  simpa using (List.all_eq_true.mp hall c hc)

theorem twelveLayerFirstCell_valid :
    (twelveLayerCellTable.getD 0
      { leftNumerator := 0, leftDenominator := 1,
        rightNumerator := 0, rightDenominator := 1,
        rankCode := 0, orderCode := 0, floorCode := 0, value := 0 }).Valid := by
  have hfirst : twelveLayerCellTable.getD 0
      { leftNumerator := 0, leftDenominator := 1,
        rightNumerator := 0, rightDenominator := 1,
        rankCode := 0, orderCode := 0, floorCode := 0, value := 0 } =
      twelveFirstCell := by
    norm_num [twelveFirstCell, twelveLayerCellTable, twelveLayerCellChunk0,
      twelveCellCertificateOfRaw, twelveCellRawDataRows0]
  rw [hfirst]
  set_option maxRecDepth 100000 in
  decide

private theorem monotone_fin24 {α : Type} [Preorder α] (f : Fin 24 → α)
    (hstep : ∀ k : Fin 23, f k.castSucc ≤ f k.succ) :
    ∀ a b : Fin 24, a.val ≤ b.val → f a ≤ f b := by
  intro a b hab
  let d := b.val - a.val
  have hd : b.val = a.val + d := by simp [d]; omega
  have aux : ∀ d (b : Fin 24), b.val = a.val + d → f a ≤ f b := by
    intro n
    induction n with
    | zero =>
      intro b hb
      have hEq : b = a := Fin.ext (by simpa using hb)
      subst b
      exact le_rfl
    | succ n ih =>
      intro b hb
      let mid : Fin 24 := ⟨a.val + n, by omega⟩
      have hmid : mid.val = a.val + n := by simp [mid]
      have hfirst := ih mid hmid
      have hlt : mid.val < 23 := by simp [mid]; omega
      let k : Fin 23 := ⟨mid.val, hlt⟩
      have hadj := hstep k
      have hleft : k.castSucc = mid := by apply Fin.ext; rfl
      have hright : k.succ = b := by apply Fin.ext; simp [k]; omega
      rw [hleft, hright] at hadj
      exact hfirst.trans hadj
  exact aux d b hd

namespace TwelveCellCertificate

theorem floor_eq_of_valid {c : TwelveCellCertificate} (hc : c.Valid)
    {z : ℝ} (hzl : (c.left : ℝ) < z) (hzr : z < (c.right : ℝ))
    (i : TwelveEndpoint) :
    Int.floor ((twelveEndpointSlope i : ℝ) * z) = twelveCellFloor c i := by
  rcases hc with ⟨_, _, _, _, _, _, hfloor, _, _, _, _⟩
  have hs0 : (0 : ℝ) ≤ (twelveEndpointSlope i : ℝ) := by positivity
  have hqlo : (twelveCellFloor c i : ℝ) ≤
      (twelveEndpointSlope i : ℝ) * (c.left : ℝ) := by
    exact_mod_cast (hfloor i).1
  have hqhi : (twelveEndpointSlope i : ℝ) * (c.right : ℝ) ≤
      (twelveCellFloor c i : ℝ) + 1 := by
    exact_mod_cast (hfloor i).2
  have hlo : (twelveCellFloor c i : ℝ) ≤
      (twelveEndpointSlope i : ℝ) * z := by
    exact hqlo.trans (mul_le_mul_of_nonneg_left (le_of_lt hzl) hs0)
  have hhi : (twelveEndpointSlope i : ℝ) * z <
      (twelveCellFloor c i : ℝ) + 1 := by
    by_cases hs : twelveEndpointSlope i = 0
    · have hq : twelveCellFloor c i = 0 := by
        have hqlo' : (twelveCellFloor c i : ℝ) ≤ 0 := by
          simpa [hs] using hqlo
        have hqnn : (0 : ℝ) ≤ (twelveCellFloor c i : ℝ) := by
          have hI : (0 : ℤ) ≤ twelveCellFloor c i := by
            unfold twelveCellFloor
            exact Int.natCast_nonneg _
          exact_mod_cast hI
        exact_mod_cast le_antisymm hqlo' hqnn
      rw [hs, hq]
      norm_num
    · have hspos : (0 : ℝ) < (twelveEndpointSlope i : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hs
      have hmul : (twelveEndpointSlope i : ℝ) * z <
          (twelveEndpointSlope i : ℝ) * (c.right : ℝ) :=
        mul_lt_mul_of_pos_left hzr hspos
      exact hmul.trans_le hqhi
  apply Int.floor_eq_iff.mpr
  exact ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩

theorem endpoint_eq_affine_of_valid {c : TwelveCellCertificate} (hc : c.Valid)
    {z : ℝ} (hzl : (c.left : ℝ) < z) (hzr : z < (c.right : ℝ))
    (i : TwelveEndpoint) :
    twelveEndpointReal i z =
      (twelveEndpointSlope i : ℝ) * z - (twelveCellFloor c i : ℝ) := by
  simp [twelveEndpointReal, Int.fract,
    floor_eq_of_valid hc hzl hzr i]

theorem endpoint_lt_of_rank_lt {c : TwelveCellCertificate} (hc : c.Valid)
    {z : ℝ} (hzl : (c.left : ℝ) < z) (hzr : z < (c.right : ℝ))
    {i j : TwelveEndpoint}
    (hij : (twelveRank c.rankCode i).val < (twelveRank c.rankCode j).val) :
    twelveEndpointReal i z < twelveEndpointReal j z := by
  have hei := endpoint_eq_affine_of_valid hc hzl hzr i
  have hej := endpoint_eq_affine_of_valid hc hzl hzr j
  rcases hc with ⟨_, _, _, _, hnodup, horderInv, _, hadj, _, _, _⟩
  have hinj : Function.Injective (twelveRank c.rankCode) := by
    exact List.nodup_ofFn.mp hnodup
  have hne : i ≠ j := by
    intro h
    subst j
    exact (Nat.lt_irrefl _ hij)
  have hsne : twelveEndpointSlope i ≠ twelveEndpointSlope j := by
    intro h
    exact hne (twelveEndpointSlope_injective h)
  have horderI : twelveOrderEndpoint c.orderCode (twelveRank c.rankCode i) = i :=
    hinj (horderInv (twelveRank c.rankCode i))
  have horderJ : twelveOrderEndpoint c.orderCode (twelveRank c.rankCode j) = j :=
    hinj (horderInv (twelveRank c.rankCode j))
  have hLeft := monotone_fin24
    (fun r => twelveEndpointAffine c (twelveOrderEndpoint c.orderCode r) c.left)
    (fun k => (hadj k).1) (twelveRank c.rankCode i) (twelveRank c.rankCode j)
    (Nat.le_of_lt hij)
  have hRight := monotone_fin24
    (fun r => twelveEndpointAffine c (twelveOrderEndpoint c.orderCode r) c.right)
    (fun k => (hadj k).2) (twelveRank c.rankCode i) (twelveRank c.rankCode j)
    (Nat.le_of_lt hij)
  rw [horderI, horderJ] at hLeft hRight
  have hLeftR : (twelveEndpointAffine c i c.left : ℝ) ≤
      (twelveEndpointAffine c j c.left : ℝ) := by exact_mod_cast hLeft
  have hRightR : (twelveEndpointAffine c i c.right : ℝ) ≤
      (twelveEndpointAffine c j c.right : ℝ) := by exact_mod_cast hRight
  have hLeftR' : (twelveEndpointSlope i : ℝ) * (c.left : ℝ) -
      (twelveCellFloor c i : ℝ) ≤
      (twelveEndpointSlope j : ℝ) * (c.left : ℝ) -
      (twelveCellFloor c j : ℝ) := by
    simpa [twelveEndpointAffine] using hLeftR
  have hRightR' : (twelveEndpointSlope i : ℝ) * (c.right : ℝ) -
      (twelveCellFloor c i : ℝ) ≤
      (twelveEndpointSlope j : ℝ) * (c.right : ℝ) -
      (twelveCellFloor c j : ℝ) := by
    simpa [twelveEndpointAffine] using hRightR
  rw [hei, hej]
  by_cases hs : twelveEndpointSlope i < twelveEndpointSlope j
  · have hsR : (twelveEndpointSlope i : ℝ) <
        (twelveEndpointSlope j : ℝ) := by exact_mod_cast hs
    have hpos : 0 < ((twelveEndpointSlope j : ℝ) -
        (twelveEndpointSlope i : ℝ)) * ((z - (c.left : ℝ))) :=
      mul_pos (sub_pos.mpr hsR) (sub_pos.mpr hzl)
    have hdiff :
        ((twelveEndpointSlope i : ℝ) * z - (twelveCellFloor c i : ℝ)) -
            ((twelveEndpointSlope j : ℝ) * z - (twelveCellFloor c j : ℝ)) <
        ((twelveEndpointSlope i : ℝ) * (c.left : ℝ) -
            (twelveCellFloor c i : ℝ)) -
            ((twelveEndpointSlope j : ℝ) * (c.left : ℝ) -
            (twelveCellFloor c j : ℝ)) := by
      have heq :
          ((twelveEndpointSlope i : ℝ) * z - (twelveCellFloor c i : ℝ)) -
              ((twelveEndpointSlope j : ℝ) * z - (twelveCellFloor c j : ℝ)) =
            (((twelveEndpointSlope i : ℝ) * (c.left : ℝ) -
              (twelveCellFloor c i : ℝ)) -
              ((twelveEndpointSlope j : ℝ) * (c.left : ℝ) -
              (twelveCellFloor c j : ℝ))) -
              ((twelveEndpointSlope j : ℝ) -
                (twelveEndpointSlope i : ℝ)) * (z - (c.left : ℝ)) := by ring
      rw [heq]
      linarith
    linarith [hLeftR']
  · have hgt : twelveEndpointSlope j < twelveEndpointSlope i := by
      rcases lt_or_gt_of_ne hsne with h | h
      · exact (False.elim (hs h))
      · exact h
    have hgtR : (twelveEndpointSlope j : ℝ) <
        (twelveEndpointSlope i : ℝ) := by exact_mod_cast hgt
    have hpos : 0 < ((twelveEndpointSlope i : ℝ) -
        (twelveEndpointSlope j : ℝ)) * ((c.right : ℝ) - z) :=
      mul_pos (sub_pos.mpr hgtR) (sub_pos.mpr hzr)
    have hdiff :
        ((twelveEndpointSlope i : ℝ) * z - (twelveCellFloor c i : ℝ)) -
            ((twelveEndpointSlope j : ℝ) * z - (twelveCellFloor c j : ℝ)) <
        ((twelveEndpointSlope i : ℝ) * (c.right : ℝ) -
            (twelveCellFloor c i : ℝ)) -
            ((twelveEndpointSlope j : ℝ) * (c.right : ℝ) -
            (twelveCellFloor c j : ℝ)) := by
      have heq :
          ((twelveEndpointSlope i : ℝ) * z - (twelveCellFloor c i : ℝ)) -
              ((twelveEndpointSlope j : ℝ) * z - (twelveCellFloor c j : ℝ)) =
            (((twelveEndpointSlope i : ℝ) * (c.right : ℝ) -
              (twelveCellFloor c i : ℝ)) -
              ((twelveEndpointSlope j : ℝ) * (c.right : ℝ) -
              (twelveCellFloor c j : ℝ))) -
              ((twelveEndpointSlope i : ℝ) -
                (twelveEndpointSlope j : ℝ)) * ((c.right : ℝ) - z) := by ring
      rw [heq]
      linarith
    linarith [hRightR']

theorem endpoint_lt_iff_rank_lt {c : TwelveCellCertificate} (hc : c.Valid)
    {z : ℝ} (hzl : (c.left : ℝ) < z) (hzr : z < (c.right : ℝ))
    (i j : TwelveEndpoint) :
    twelveEndpointReal i z < twelveEndpointReal j z ↔
      (twelveRank c.rankCode i).val < (twelveRank c.rankCode j).val := by
  constructor
  · intro h
    by_contra hn
    have hinj : Function.Injective (twelveRank c.rankCode) := by
      rcases hc with ⟨_, _, _, _, h, _, _, _, _, _, _⟩
      exact List.nodup_ofFn.mp h
    by_cases heq : (twelveRank c.rankCode i).val =
        (twelveRank c.rankCode j).val
    · have hij : i = j := by
        apply hinj
        exact Fin.ext heq
      subst j
      exact (lt_irrefl _ h)
    · have hji : (twelveRank c.rankCode j).val <
          (twelveRank c.rankCode i).val := by omega
      exact (not_lt_of_ge (le_of_lt (endpoint_lt_of_rank_lt hc hzl hzr hji))) h
  · exact endpoint_lt_of_rank_lt hc hzl hzr

end TwelveCellCertificate

theorem twelveLayerShape_cost_scale (s : ℕ) (z y : ℝ) :
    (twelveLayerShape.scaleWeights s).cost z y = s * twelveLayerShape.cost z y :=
  twelveLayerShape.cost_scaleWeights s z y

end OddPiPowers

end
