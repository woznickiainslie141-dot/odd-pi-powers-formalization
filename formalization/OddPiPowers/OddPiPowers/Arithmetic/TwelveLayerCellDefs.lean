module

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


theorem twelveCell_all_cons {c : TwelveCellCertificate} {cs : List TwelveCellCertificate}
    (hc : c.Valid) (hcs : cs.all (fun d => d.Valid) = true) :
    (c :: cs).all (fun d => d.Valid) = true := by
  simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hc, hcs⟩

end OddPiPowers

end
