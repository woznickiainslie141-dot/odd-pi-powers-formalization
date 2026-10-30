module

public import OddPiPowers.L99.Arithmetic.TwentyEightLayerCells
public import Mathlib.Data.List.Chain
public import Mathlib.Data.List.Pairwise

@[expose] public section

namespace OddPiPowers.L99

def twentyEightCellsNext (a b : TwentyEightCellCertificate) : Prop :=
  a.rightNumerator = b.leftNumerator ∧ a.rightDenominator = b.leftDenominator

instance (a b : TwentyEightCellCertificate) : Decidable (twentyEightCellsNext a b) := by
  unfold twentyEightCellsNext
  infer_instance



set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

private def ChainSummary (xs : List TwentyEightCellCertificate) (a b c d : ℕ) : Prop :=
  xs.IsChain twentyEightCellsNext ∧
  xs.head?.map (fun x => (x.leftNumerator, x.leftDenominator)) = some (a,b) ∧
  xs.getLast?.map (fun x => (x.rightNumerator, x.rightDenominator)) = some (c,d)

private instance (xs : List TwentyEightCellCertificate) (a b c d : ℕ) :
    Decidable (ChainSummary xs a b c d) := by unfold ChainSummary; infer_instance

private theorem option_pair_of_mem {o : Option TwentyEightCellCertificate}
    {f : TwentyEightCellCertificate → ℕ × ℕ} {p : ℕ × ℕ} {x : TwentyEightCellCertificate}
    (h : o.map f = some p) (hx : x ∈ o) : f x = p := by
  cases o with
  | none => simp at hx
  | some y =>
    have hxy : y = x := by simpa using hx
    subst y
    simpa using h

private theorem chain_summary_append {xs ys : List TwentyEightCellCertificate}
    {a b c d e f : ℕ} (hx : ChainSummary xs a b c d) (hy : ChainSummary ys c d e f) :
    ChainSummary (xs ++ ys) a b e f := by
  have hxs : xs ≠ [] := by intro h; simp [ChainSummary, h] at hx
  have hys : ys ≠ [] := by intro h; simp [ChainSummary, h] at hy
  refine ⟨hx.1.append hy.1 ?_, ?_, ?_⟩
  · intro x hxm y hym
    have hp := option_pair_of_mem hx.2.2 hxm
    have hq := option_pair_of_mem hy.2.1 hym
    exact ⟨(congrArg Prod.fst hp).trans (congrArg Prod.fst hq).symm,
      (congrArg Prod.snd hp).trans (congrArg Prod.snd hq).symm⟩
  · rw [List.head?_append_of_ne_nil _ hxs]
    exact hx.2.1
  · rw [List.getLast?_append_of_ne_nil _ hys]
    exact hy.2.2


attribute [local irreducible] twentyEightLayerCellTable
attribute [local irreducible] twentyEightLayerCellChunk0 twentyEightLayerCellChunk1 twentyEightLayerCellChunk2 twentyEightLayerCellChunk3 twentyEightLayerCellChunk4 twentyEightLayerCellChunk5 twentyEightLayerCellChunk6 twentyEightLayerCellChunk7 twentyEightLayerCellChunk8 twentyEightLayerCellChunk9 twentyEightLayerCellChunk10 twentyEightLayerCellChunk11 twentyEightLayerCellChunk12 twentyEightLayerCellChunk13 twentyEightLayerCellChunk14 twentyEightLayerCellChunk15 twentyEightLayerCellChunk16 twentyEightLayerCellChunk17 twentyEightLayerCellChunk18 twentyEightLayerCellChunk19 twentyEightLayerCellChunk20 twentyEightLayerCellChunk21 twentyEightLayerCellChunk22 twentyEightLayerCellChunk23 twentyEightLayerCellChunk24 twentyEightLayerCellChunk25 twentyEightLayerCellChunk26 twentyEightLayerCellChunk27 twentyEightLayerCellChunk28 twentyEightLayerCellChunk29 twentyEightLayerCellChunk30 twentyEightLayerCellChunk31 twentyEightLayerCellChunk32 twentyEightLayerCellChunk33 twentyEightLayerCellChunk34 twentyEightLayerCellChunk35 twentyEightLayerCellChunk36 twentyEightLayerCellChunk37 twentyEightLayerCellChunk38 twentyEightLayerCellChunk39 twentyEightLayerCellChunk40 twentyEightLayerCellChunk41 twentyEightLayerCellChunk42 twentyEightLayerCellChunk43 twentyEightLayerCellChunk44 twentyEightLayerCellChunk45 twentyEightLayerCellChunk46 twentyEightLayerCellChunk47 twentyEightLayerCellChunk48 twentyEightLayerCellChunk49 twentyEightLayerCellChunk50 twentyEightLayerCellChunk51 twentyEightLayerCellChunk52 twentyEightLayerCellChunk53 twentyEightLayerCellChunk54 twentyEightLayerCellChunk55 twentyEightLayerCellChunk56 twentyEightLayerCellChunk57 twentyEightLayerCellChunk58 twentyEightLayerCellChunk59 twentyEightLayerCellChunk60 twentyEightLayerCellChunk61 twentyEightLayerCellChunk62 twentyEightLayerCellChunk63 twentyEightLayerCellChunk64 twentyEightLayerCellChunk65 twentyEightLayerCellChunk66 twentyEightLayerCellChunk67 twentyEightLayerCellChunk68 twentyEightLayerCellChunk69 twentyEightLayerCellChunk70 twentyEightLayerCellChunk71 twentyEightLayerCellChunk72 twentyEightLayerCellChunk73 twentyEightLayerCellChunk74 twentyEightLayerCellChunk75 twentyEightLayerCellChunk76 twentyEightLayerCellChunk77 twentyEightLayerCellChunk78 twentyEightLayerCellChunk79 twentyEightLayerCellChunk80 twentyEightLayerCellChunk81 twentyEightLayerCellChunk82 twentyEightLayerCellChunk83 twentyEightLayerCellChunk84 twentyEightLayerCellChunk85 twentyEightLayerCellChunk86 twentyEightLayerCellChunk87 twentyEightLayerCellChunk88 twentyEightLayerCellChunk89 twentyEightLayerCellChunk90 twentyEightLayerCellChunk91 twentyEightLayerCellChunk92 twentyEightLayerCellChunk93 twentyEightLayerCellChunk94 twentyEightLayerCellChunk95 twentyEightLayerCellChunk96 twentyEightLayerCellChunk97 twentyEightLayerCellChunk98 twentyEightLayerCellChunk99 twentyEightLayerCellChunk100 twentyEightLayerCellChunk101 twentyEightLayerCellChunk102 twentyEightLayerCellChunk103 twentyEightLayerCellChunk104 twentyEightLayerCellChunk105 twentyEightLayerCellChunk106 twentyEightLayerCellChunk107 twentyEightLayerCellChunk108 twentyEightLayerCellChunk109 twentyEightLayerCellChunk110 twentyEightLayerCellChunk111 twentyEightLayerCellChunk112 twentyEightLayerCellChunk113 twentyEightLayerCellChunk114 twentyEightLayerCellChunk115 twentyEightLayerCellChunk116 twentyEightLayerCellChunk117 twentyEightLayerCellChunk118 twentyEightLayerCellChunk119 twentyEightLayerCellChunk120 twentyEightLayerCellChunk121 twentyEightLayerCellChunk122 twentyEightLayerCellChunk123 twentyEightLayerCellChunk124 twentyEightLayerCellChunk125 twentyEightLayerCellChunk126 twentyEightLayerCellChunk127 twentyEightLayerCellChunk128 twentyEightLayerCellChunk129 twentyEightLayerCellChunk130 twentyEightLayerCellChunk131 twentyEightLayerCellChunk132 twentyEightLayerCellChunk133 twentyEightLayerCellChunk134 twentyEightLayerCellChunk135 twentyEightLayerCellChunk136 twentyEightLayerCellChunk137 twentyEightLayerCellChunk138 twentyEightLayerCellChunk139 twentyEightLayerCellChunk140 twentyEightLayerCellChunk141 twentyEightLayerCellChunk142 twentyEightLayerCellChunk143 twentyEightLayerCellChunk144 twentyEightLayerCellChunk145 twentyEightLayerCellChunk146 twentyEightLayerCellChunk147 twentyEightLayerCellChunk148 twentyEightLayerCellChunk149 twentyEightLayerCellChunk150

private theorem cell_chain_chunk_0 : ChainSummary twentyEightLayerCellChunk0 0 1 1 80 := by decide +kernel

private theorem cell_chain_chunk_1 : ChainSummary twentyEightLayerCellChunk1 1 80 1 60 := by decide +kernel

private theorem cell_chain_chunk_2 : ChainSummary twentyEightLayerCellChunk2 1 60 1 45 := by decide +kernel

private theorem cell_chain_chunk_3 : ChainSummary twentyEightLayerCellChunk3 1 45 1 35 := by decide +kernel

private theorem cell_chain_chunk_4 : ChainSummary twentyEightLayerCellChunk4 1 35 1 29 := by decide +kernel

private theorem cell_chain_chunk_5 : ChainSummary twentyEightLayerCellChunk5 1 29 3 73 := by decide +kernel

private theorem cell_chain_chunk_6 : ChainSummary twentyEightLayerCellChunk6 3 73 1 21 := by decide +kernel

private theorem cell_chain_chunk_7 : ChainSummary twentyEightLayerCellChunk7 1 21 5 93 := by decide +kernel

private theorem cell_chain_chunk_8 : ChainSummary twentyEightLayerCellChunk8 5 93 5 83 := by decide +kernel

private theorem cell_chain_chunk_9 : ChainSummary twentyEightLayerCellChunk9 5 83 6 89 := by decide +kernel

private theorem cell_chain_chunk_10 : ChainSummary twentyEightLayerCellChunk10 6 89 7 95 := by decide +kernel

private theorem cell_chain_chunk_11 : ChainSummary twentyEightLayerCellChunk11 7 95 7 87 := by decide +kernel

private theorem cell_chain_chunk_12 : ChainSummary twentyEightLayerCellChunk12 7 87 7 81 := by decide +kernel

private theorem cell_chain_chunk_13 : ChainSummary twentyEightLayerCellChunk13 7 81 7 75 := by decide +kernel

private theorem cell_chain_chunk_14 : ChainSummary twentyEightLayerCellChunk14 7 75 1 10 := by decide +kernel

private theorem cell_chain_chunk_15 : ChainSummary twentyEightLayerCellChunk15 1 10 8 75 := by decide +kernel

private theorem cell_chain_chunk_16 : ChainSummary twentyEightLayerCellChunk16 8 75 5 44 := by decide +kernel

private theorem cell_chain_chunk_17 : ChainSummary twentyEightLayerCellChunk17 5 44 3 25 := by decide +kernel

private theorem cell_chain_chunk_18 : ChainSummary twentyEightLayerCellChunk18 3 25 8 63 := by decide +kernel

private theorem cell_chain_chunk_19 : ChainSummary twentyEightLayerCellChunk19 8 63 2 15 := by decide +kernel

private theorem cell_chain_chunk_20 : ChainSummary twentyEightLayerCellChunk20 2 15 6 43 := by decide +kernel

private theorem cell_chain_chunk_21 : ChainSummary twentyEightLayerCellChunk21 6 43 6 41 := by decide +kernel

private theorem cell_chain_chunk_22 : ChainSummary twentyEightLayerCellChunk22 6 41 11 72 := by decide +kernel

private theorem cell_chain_chunk_23 : ChainSummary twentyEightLayerCellChunk23 11 72 15 94 := by decide +kernel

private theorem cell_chain_chunk_24 : ChainSummary twentyEightLayerCellChunk24 15 94 16 97 := by decide +kernel

private theorem cell_chain_chunk_25 : ChainSummary twentyEightLayerCellChunk25 16 97 9 52 := by decide +kernel

private theorem cell_chain_chunk_26 : ChainSummary twentyEightLayerCellChunk26 9 52 7 39 := by decide +kernel

private theorem cell_chain_chunk_27 : ChainSummary twentyEightLayerCellChunk27 7 39 8 43 := by decide +kernel

private theorem cell_chain_chunk_28 : ChainSummary twentyEightLayerCellChunk28 8 43 16 83 := by decide +kernel

private theorem cell_chain_chunk_29 : ChainSummary twentyEightLayerCellChunk29 16 83 18 91 := by decide +kernel

private theorem cell_chain_chunk_30 : ChainSummary twentyEightLayerCellChunk30 18 91 20 97 := by decide +kernel

private theorem cell_chain_chunk_31 : ChainSummary twentyEightLayerCellChunk31 20 97 10 47 := by decide +kernel

private theorem cell_chain_chunk_32 : ChainSummary twentyEightLayerCellChunk32 10 47 9 41 := by decide +kernel

private theorem cell_chain_chunk_33 : ChainSummary twentyEightLayerCellChunk33 9 41 12 53 := by decide +kernel

private theorem cell_chain_chunk_34 : ChainSummary twentyEightLayerCellChunk34 12 53 17 73 := by decide +kernel

private theorem cell_chain_chunk_35 : ChainSummary twentyEightLayerCellChunk35 17 73 17 71 := by decide +kernel

private theorem cell_chain_chunk_36 : ChainSummary twentyEightLayerCellChunk36 17 71 14 57 := by decide +kernel

private theorem cell_chain_chunk_37 : ChainSummary twentyEightLayerCellChunk37 14 57 17 67 := by decide +kernel

private theorem cell_chain_chunk_38 : ChainSummary twentyEightLayerCellChunk38 17 67 20 77 := by decide +kernel

private theorem cell_chain_chunk_39 : ChainSummary twentyEightLayerCellChunk39 20 77 21 79 := by decide +kernel

private theorem cell_chain_chunk_40 : ChainSummary twentyEightLayerCellChunk40 21 79 3 11 := by decide +kernel

private theorem cell_chain_chunk_41 : ChainSummary twentyEightLayerCellChunk41 3 11 19 68 := by decide +kernel

private theorem cell_chain_chunk_42 : ChainSummary twentyEightLayerCellChunk42 19 68 27 94 := by decide +kernel

private theorem cell_chain_chunk_43 : ChainSummary twentyEightLayerCellChunk43 27 94 29 99 := by decide +kernel

private theorem cell_chain_chunk_44 : ChainSummary twentyEightLayerCellChunk44 29 99 26 87 := by decide +kernel

private theorem cell_chain_chunk_45 : ChainSummary twentyEightLayerCellChunk45 26 87 26 85 := by decide +kernel

private theorem cell_chain_chunk_46 : ChainSummary twentyEightLayerCellChunk46 26 85 31 99 := by decide +kernel

private theorem cell_chain_chunk_47 : ChainSummary twentyEightLayerCellChunk47 31 99 15 47 := by decide +kernel

private theorem cell_chain_chunk_48 : ChainSummary twentyEightLayerCellChunk48 15 47 27 83 := by decide +kernel

private theorem cell_chain_chunk_49 : ChainSummary twentyEightLayerCellChunk49 27 83 31 94 := by decide +kernel

private theorem cell_chain_chunk_50 : ChainSummary twentyEightLayerCellChunk50 31 94 33 97 := by decide +kernel

private theorem cell_chain_chunk_51 : ChainSummary twentyEightLayerCellChunk51 33 97 9 26 := by decide +kernel

private theorem cell_chain_chunk_52 : ChainSummary twentyEightLayerCellChunk52 9 26 31 88 := by decide +kernel

private theorem cell_chain_chunk_53 : ChainSummary twentyEightLayerCellChunk53 31 88 23 64 := by decide +kernel

private theorem cell_chain_chunk_54 : ChainSummary twentyEightLayerCellChunk54 23 64 15 41 := by decide +kernel

private theorem cell_chain_chunk_55 : ChainSummary twentyEightLayerCellChunk55 15 41 19 51 := by decide +kernel

private theorem cell_chain_chunk_56 : ChainSummary twentyEightLayerCellChunk56 19 51 11 29 := by decide +kernel

private theorem cell_chain_chunk_57 : ChainSummary twentyEightLayerCellChunk57 11 29 27 70 := by decide +kernel

private theorem cell_chain_chunk_58 : ChainSummary twentyEightLayerCellChunk58 27 70 31 79 := by decide +kernel

private theorem cell_chain_chunk_59 : ChainSummary twentyEightLayerCellChunk59 31 79 37 93 := by decide +kernel

private theorem cell_chain_chunk_60 : ChainSummary twentyEightLayerCellChunk60 37 93 13 32 := by decide +kernel

private theorem cell_chain_chunk_61 : ChainSummary twentyEightLayerCellChunk61 13 32 26 63 := by decide +kernel

private theorem cell_chain_chunk_62 : ChainSummary twentyEightLayerCellChunk62 26 63 13 31 := by decide +kernel

private theorem cell_chain_chunk_63 : ChainSummary twentyEightLayerCellChunk63 13 31 23 54 := by decide +kernel

private theorem cell_chain_chunk_64 : ChainSummary twentyEightLayerCellChunk64 23 54 42 97 := by decide +kernel

private theorem cell_chain_chunk_65 : ChainSummary twentyEightLayerCellChunk65 42 97 29 66 := by decide +kernel

private theorem cell_chain_chunk_66 : ChainSummary twentyEightLayerCellChunk66 29 66 29 65 := by decide +kernel

private theorem cell_chain_chunk_67 : ChainSummary twentyEightLayerCellChunk67 29 65 43 95 := by decide +kernel

private theorem cell_chain_chunk_68 : ChainSummary twentyEightLayerCellChunk68 43 95 45 98 := by decide +kernel

private theorem cell_chain_chunk_69 : ChainSummary twentyEightLayerCellChunk69 45 98 27 58 := by decide +kernel

private theorem cell_chain_chunk_70 : ChainSummary twentyEightLayerCellChunk70 27 58 43 91 := by decide +kernel

private theorem cell_chain_chunk_71 : ChainSummary twentyEightLayerCellChunk71 43 91 34 71 := by decide +kernel

private theorem cell_chain_chunk_72 : ChainSummary twentyEightLayerCellChunk72 34 71 16 33 := by decide +kernel

private theorem cell_chain_chunk_73 : ChainSummary twentyEightLayerCellChunk73 16 33 28 57 := by decide +kernel

private theorem cell_chain_chunk_74 : ChainSummary twentyEightLayerCellChunk74 28 57 48 97 := by decide +kernel

private theorem cell_chain_chunk_75 : ChainSummary twentyEightLayerCellChunk75 48 97 33 65 := by decide +kernel

private theorem cell_chain_chunk_76 : ChainSummary twentyEightLayerCellChunk76 33 65 19 37 := by decide +kernel

private theorem cell_chain_chunk_77 : ChainSummary twentyEightLayerCellChunk77 19 37 13 25 := by decide +kernel

private theorem cell_chain_chunk_78 : ChainSummary twentyEightLayerCellChunk78 13 25 10 19 := by decide +kernel

private theorem cell_chain_chunk_79 : ChainSummary twentyEightLayerCellChunk79 10 19 49 92 := by decide +kernel

private theorem cell_chain_chunk_80 : ChainSummary twentyEightLayerCellChunk80 49 92 34 63 := by decide +kernel

private theorem cell_chain_chunk_81 : ChainSummary twentyEightLayerCellChunk81 34 63 47 86 := by decide +kernel

private theorem cell_chain_chunk_82 : ChainSummary twentyEightLayerCellChunk82 47 86 21 38 := by decide +kernel

private theorem cell_chain_chunk_83 : ChainSummary twentyEightLayerCellChunk83 21 38 33 59 := by decide +kernel

private theorem cell_chain_chunk_84 : ChainSummary twentyEightLayerCellChunk84 33 59 43 76 := by decide +kernel

private theorem cell_chain_chunk_85 : ChainSummary twentyEightLayerCellChunk85 43 76 47 82 := by decide +kernel

private theorem cell_chain_chunk_86 : ChainSummary twentyEightLayerCellChunk86 47 82 51 88 := by decide +kernel

private theorem cell_chain_chunk_87 : ChainSummary twentyEightLayerCellChunk87 51 88 58 99 := by decide +kernel

private theorem cell_chain_chunk_88 : ChainSummary twentyEightLayerCellChunk88 58 99 16 27 := by decide +kernel

private theorem cell_chain_chunk_89 : ChainSummary twentyEightLayerCellChunk89 16 27 55 92 := by decide +kernel

private theorem cell_chain_chunk_90 : ChainSummary twentyEightLayerCellChunk90 55 92 57 94 := by decide +kernel

private theorem cell_chain_chunk_91 : ChainSummary twentyEightLayerCellChunk91 57 94 19 31 := by decide +kernel

private theorem cell_chain_chunk_92 : ChainSummary twentyEightLayerCellChunk92 19 31 57 92 := by decide +kernel

private theorem cell_chain_chunk_93 : ChainSummary twentyEightLayerCellChunk93 57 92 52 83 := by decide +kernel

private theorem cell_chain_chunk_94 : ChainSummary twentyEightLayerCellChunk94 52 83 31 49 := by decide +kernel

private theorem cell_chain_chunk_95 : ChainSummary twentyEightLayerCellChunk95 31 49 39 61 := by decide +kernel

private theorem cell_chain_chunk_96 : ChainSummary twentyEightLayerCellChunk96 39 61 42 65 := by decide +kernel

private theorem cell_chain_chunk_97 : ChainSummary twentyEightLayerCellChunk97 42 65 62 95 := by decide +kernel

private theorem cell_chain_chunk_98 : ChainSummary twentyEightLayerCellChunk98 62 95 56 85 := by decide +kernel

private theorem cell_chain_chunk_99 : ChainSummary twentyEightLayerCellChunk99 56 85 63 95 := by decide +kernel

private theorem cell_chain_chunk_100 : ChainSummary twentyEightLayerCellChunk100 63 95 64 95 := by decide +kernel

private theorem cell_chain_chunk_101 : ChainSummary twentyEightLayerCellChunk101 64 95 53 78 := by decide +kernel

private theorem cell_chain_chunk_102 : ChainSummary twentyEightLayerCellChunk102 53 78 59 86 := by decide +kernel

private theorem cell_chain_chunk_103 : ChainSummary twentyEightLayerCellChunk103 59 86 61 88 := by decide +kernel

private theorem cell_chain_chunk_104 : ChainSummary twentyEightLayerCellChunk104 61 88 58 83 := by decide +kernel

private theorem cell_chain_chunk_105 : ChainSummary twentyEightLayerCellChunk105 58 83 12 17 := by decide +kernel

private theorem cell_chain_chunk_106 : ChainSummary twentyEightLayerCellChunk106 12 17 47 66 := by decide +kernel

private theorem cell_chain_chunk_107 : ChainSummary twentyEightLayerCellChunk107 47 66 41 57 := by decide +kernel

private theorem cell_chain_chunk_108 : ChainSummary twentyEightLayerCellChunk108 41 57 45 62 := by decide +kernel

private theorem cell_chain_chunk_109 : ChainSummary twentyEightLayerCellChunk109 45 62 52 71 := by decide +kernel

private theorem cell_chain_chunk_110 : ChainSummary twentyEightLayerCellChunk110 52 71 17 23 := by decide +kernel

private theorem cell_chain_chunk_111 : ChainSummary twentyEightLayerCellChunk111 17 23 38 51 := by decide +kernel

private theorem cell_chain_chunk_112 : ChainSummary twentyEightLayerCellChunk112 38 51 55 73 := by decide +kernel

private theorem cell_chain_chunk_113 : ChainSummary twentyEightLayerCellChunk113 55 73 41 54 := by decide +kernel

private theorem cell_chain_chunk_114 : ChainSummary twentyEightLayerCellChunk114 41 54 49 64 := by decide +kernel

private theorem cell_chain_chunk_115 : ChainSummary twentyEightLayerCellChunk115 49 64 61 79 := by decide +kernel

private theorem cell_chain_chunk_116 : ChainSummary twentyEightLayerCellChunk116 61 79 53 68 := by decide +kernel

private theorem cell_chain_chunk_117 : ChainSummary twentyEightLayerCellChunk117 53 68 11 14 := by decide +kernel

private theorem cell_chain_chunk_118 : ChainSummary twentyEightLayerCellChunk118 11 14 65 82 := by decide +kernel

private theorem cell_chain_chunk_119 : ChainSummary twentyEightLayerCellChunk119 65 82 75 94 := by decide +kernel

private theorem cell_chain_chunk_120 : ChainSummary twentyEightLayerCellChunk120 75 94 79 98 := by decide +kernel

private theorem cell_chain_chunk_121 : ChainSummary twentyEightLayerCellChunk121 79 98 13 16 := by decide +kernel

private theorem cell_chain_chunk_122 : ChainSummary twentyEightLayerCellChunk122 13 16 59 72 := by decide +kernel

private theorem cell_chain_chunk_123 : ChainSummary twentyEightLayerCellChunk123 59 72 71 86 := by decide +kernel

private theorem cell_chain_chunk_124 : ChainSummary twentyEightLayerCellChunk124 71 86 69 83 := by decide +kernel

private theorem cell_chain_chunk_125 : ChainSummary twentyEightLayerCellChunk125 69 83 73 87 := by decide +kernel

private theorem cell_chain_chunk_126 : ChainSummary twentyEightLayerCellChunk126 73 87 82 97 := by decide +kernel

private theorem cell_chain_chunk_127 : ChainSummary twentyEightLayerCellChunk127 82 97 52 61 := by decide +kernel

private theorem cell_chain_chunk_128 : ChainSummary twentyEightLayerCellChunk128 52 61 55 64 := by decide +kernel

private theorem cell_chain_chunk_129 : ChainSummary twentyEightLayerCellChunk129 55 64 45 52 := by decide +kernel

private theorem cell_chain_chunk_130 : ChainSummary twentyEightLayerCellChunk130 45 52 34 39 := by decide +kernel

private theorem cell_chain_chunk_131 : ChainSummary twentyEightLayerCellChunk131 34 39 29 33 := by decide +kernel

private theorem cell_chain_chunk_132 : ChainSummary twentyEightLayerCellChunk132 29 33 54 61 := by decide +kernel

private theorem cell_chain_chunk_133 : ChainSummary twentyEightLayerCellChunk133 54 61 33 37 := by decide +kernel

private theorem cell_chain_chunk_134 : ChainSummary twentyEightLayerCellChunk134 33 37 62 69 := by decide +kernel

private theorem cell_chain_chunk_135 : ChainSummary twentyEightLayerCellChunk135 62 69 67 74 := by decide +kernel

private theorem cell_chain_chunk_136 : ChainSummary twentyEightLayerCellChunk136 67 74 83 91 := by decide +kernel

private theorem cell_chain_chunk_137 : ChainSummary twentyEightLayerCellChunk137 83 91 79 86 := by decide +kernel

private theorem cell_chain_chunk_138 : ChainSummary twentyEightLayerCellChunk138 79 86 37 40 := by decide +kernel

private theorem cell_chain_chunk_139 : ChainSummary twentyEightLayerCellChunk139 37 40 68 73 := by decide +kernel

private theorem cell_chain_chunk_140 : ChainSummary twentyEightLayerCellChunk140 68 73 61 65 := by decide +kernel

private theorem cell_chain_chunk_141 : ChainSummary twentyEightLayerCellChunk141 61 65 69 73 := by decide +kernel

private theorem cell_chain_chunk_142 : ChainSummary twentyEightLayerCellChunk142 69 73 58 61 := by decide +kernel

private theorem cell_chain_chunk_143 : ChainSummary twentyEightLayerCellChunk143 58 61 68 71 := by decide +kernel

private theorem cell_chain_chunk_144 : ChainSummary twentyEightLayerCellChunk144 68 71 27 28 := by decide +kernel

private theorem cell_chain_chunk_145 : ChainSummary twentyEightLayerCellChunk145 27 28 32 33 := by decide +kernel

private theorem cell_chain_chunk_146 : ChainSummary twentyEightLayerCellChunk146 32 33 42 43 := by decide +kernel

private theorem cell_chain_chunk_147 : ChainSummary twentyEightLayerCellChunk147 42 43 55 56 := by decide +kernel

private theorem cell_chain_chunk_148 : ChainSummary twentyEightLayerCellChunk148 55 56 75 76 := by decide +kernel

private theorem cell_chain_chunk_149 : ChainSummary twentyEightLayerCellChunk149 75 76 95 96 := by decide +kernel

private theorem cell_chain_chunk_150 : ChainSummary twentyEightLayerCellChunk150 95 96 1 1 := by decide +kernel

private theorem whole_chain_summary : ChainSummary twentyEightLayerCellTable 0 1 1 1 := by
  unfold twentyEightLayerCellTable
  exact chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (chain_summary_append (cell_chain_chunk_0) cell_chain_chunk_1) cell_chain_chunk_2) cell_chain_chunk_3) cell_chain_chunk_4) cell_chain_chunk_5) cell_chain_chunk_6) cell_chain_chunk_7) cell_chain_chunk_8) cell_chain_chunk_9) cell_chain_chunk_10) cell_chain_chunk_11) cell_chain_chunk_12) cell_chain_chunk_13) cell_chain_chunk_14) cell_chain_chunk_15) cell_chain_chunk_16) cell_chain_chunk_17) cell_chain_chunk_18) cell_chain_chunk_19) cell_chain_chunk_20) cell_chain_chunk_21) cell_chain_chunk_22) cell_chain_chunk_23) cell_chain_chunk_24) cell_chain_chunk_25) cell_chain_chunk_26) cell_chain_chunk_27) cell_chain_chunk_28) cell_chain_chunk_29) cell_chain_chunk_30) cell_chain_chunk_31) cell_chain_chunk_32) cell_chain_chunk_33) cell_chain_chunk_34) cell_chain_chunk_35) cell_chain_chunk_36) cell_chain_chunk_37) cell_chain_chunk_38) cell_chain_chunk_39) cell_chain_chunk_40) cell_chain_chunk_41) cell_chain_chunk_42) cell_chain_chunk_43) cell_chain_chunk_44) cell_chain_chunk_45) cell_chain_chunk_46) cell_chain_chunk_47) cell_chain_chunk_48) cell_chain_chunk_49) cell_chain_chunk_50) cell_chain_chunk_51) cell_chain_chunk_52) cell_chain_chunk_53) cell_chain_chunk_54) cell_chain_chunk_55) cell_chain_chunk_56) cell_chain_chunk_57) cell_chain_chunk_58) cell_chain_chunk_59) cell_chain_chunk_60) cell_chain_chunk_61) cell_chain_chunk_62) cell_chain_chunk_63) cell_chain_chunk_64) cell_chain_chunk_65) cell_chain_chunk_66) cell_chain_chunk_67) cell_chain_chunk_68) cell_chain_chunk_69) cell_chain_chunk_70) cell_chain_chunk_71) cell_chain_chunk_72) cell_chain_chunk_73) cell_chain_chunk_74) cell_chain_chunk_75) cell_chain_chunk_76) cell_chain_chunk_77) cell_chain_chunk_78) cell_chain_chunk_79) cell_chain_chunk_80) cell_chain_chunk_81) cell_chain_chunk_82) cell_chain_chunk_83) cell_chain_chunk_84) cell_chain_chunk_85) cell_chain_chunk_86) cell_chain_chunk_87) cell_chain_chunk_88) cell_chain_chunk_89) cell_chain_chunk_90) cell_chain_chunk_91) cell_chain_chunk_92) cell_chain_chunk_93) cell_chain_chunk_94) cell_chain_chunk_95) cell_chain_chunk_96) cell_chain_chunk_97) cell_chain_chunk_98) cell_chain_chunk_99) cell_chain_chunk_100) cell_chain_chunk_101) cell_chain_chunk_102) cell_chain_chunk_103) cell_chain_chunk_104) cell_chain_chunk_105) cell_chain_chunk_106) cell_chain_chunk_107) cell_chain_chunk_108) cell_chain_chunk_109) cell_chain_chunk_110) cell_chain_chunk_111) cell_chain_chunk_112) cell_chain_chunk_113) cell_chain_chunk_114) cell_chain_chunk_115) cell_chain_chunk_116) cell_chain_chunk_117) cell_chain_chunk_118) cell_chain_chunk_119) cell_chain_chunk_120) cell_chain_chunk_121) cell_chain_chunk_122) cell_chain_chunk_123) cell_chain_chunk_124) cell_chain_chunk_125) cell_chain_chunk_126) cell_chain_chunk_127) cell_chain_chunk_128) cell_chain_chunk_129) cell_chain_chunk_130) cell_chain_chunk_131) cell_chain_chunk_132) cell_chain_chunk_133) cell_chain_chunk_134) cell_chain_chunk_135) cell_chain_chunk_136) cell_chain_chunk_137) cell_chain_chunk_138) cell_chain_chunk_139) cell_chain_chunk_140) cell_chain_chunk_141) cell_chain_chunk_142) cell_chain_chunk_143) cell_chain_chunk_144) cell_chain_chunk_145) cell_chain_chunk_146) cell_chain_chunk_147) cell_chain_chunk_148) cell_chain_chunk_149) cell_chain_chunk_150

theorem twentyEightLayerCellTable_next : twentyEightLayerCellTable.IsChain twentyEightCellsNext :=
  whole_chain_summary.1

theorem twentyEightLayerCellTable_touching :
    twentyEightLayerCellTable.IsChain (fun a b => a.right = b.left) := by
  refine List.IsChain.imp_of_mem_imp ?_ twentyEightLayerCellTable_next
  intro a b _ _ h
  rcases h with ⟨hn, hd⟩
  simp only [TwentyEightCellCertificate.right, TwentyEightCellCertificate.left, hn, hd]

private theorem twentyEightPairwise_of_touching (cs : List TwentyEightCellCertificate) :
    (∀ c ∈ cs, c.left < c.right) →
    cs.IsChain (fun a b => a.right = b.left) →
    cs.Pairwise (fun a b => a.right ≤ b.left) := by
  induction cs with
  | nil => intro _ _; simp
  | cons a cs ih =>
    intro hv hc
    cases cs with
    | nil => simp
    | cons b rest =>
      have hlink := (List.isChain_cons_cons.mp hc).1
      have hchain := (List.isChain_cons_cons.mp hc).2
      have htail := ih (fun c h => hv c (List.mem_cons_of_mem a h)) hchain
      apply List.pairwise_cons.mpr
      refine ⟨?_, htail⟩
      intro x hx
      rcases List.mem_cons.mp hx with hxb | hrest
      · subst x
        exact hlink.le
      · calc
          a.right = b.left := hlink
          _ ≤ b.right := (hv b (by simp)).le
          _ ≤ x.left := (List.pairwise_cons.mp htail).1 x hrest

theorem twentyEightLayerCellTable_pairwise_disjoint :
    twentyEightLayerCellTable.Pairwise (fun a b => a.right ≤ b.left) :=
  twentyEightPairwise_of_touching twentyEightLayerCellTable
    (fun c hc => (TwentyEightCellCertificate.unit_interval_of_valid
      (twentyEightLayerCellTable_all_valid c hc)).2.1)
    twentyEightLayerCellTable_touching

theorem twentyEightLayerCellTable_compare {a b : TwentyEightCellCertificate}
    (ha : a ∈ twentyEightLayerCellTable) (hb : b ∈ twentyEightLayerCellTable) :
    a = b ∨ a.right ≤ b.left ∨ b.right ≤ a.left := by
  rcases List.mem_iff_get.mp ha with ⟨i, hi⟩
  rcases List.mem_iff_get.mp hb with ⟨j, hj⟩
  rcases lt_trichotomy i.val j.val with h | h | h
  · right; left
    have hij : i < j := h
    simpa only [hi, hj] using twentyEightLayerCellTable_pairwise_disjoint.rel_get_of_lt hij
  · left
    have hij : i = j := Fin.ext h
    rw [← hi, ← hj, hij]
  · right; right
    have hji : j < i := h
    simpa only [hi, hj] using twentyEightLayerCellTable_pairwise_disjoint.rel_get_of_lt hji

end OddPiPowers.L99

end
