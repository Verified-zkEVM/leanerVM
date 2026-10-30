/-
  LeanVM.Guest.B1.KeccakGkr.LayerRmfe

  The instance weights in `keccak_layer` (G:2514-2613): the powers of `s`, the RMFE embeddings
  evaluated at `s` through compile-time relations, their sum, and their stores in the next claim.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.Mask
public import LeanVM.Protocol.Keccak.LayerSum

/-!
# The instance weights

The four specializations of `keccak_layer` share this block (statements `887 .. 1029`, `s` the
value `1089`, `out` the parameter `12`). Its values are binary polynomials in `s` (`Mask`); by
kernel evaluation (`rmfeCheck`) the sixteen stored at `out[6 + i]` are the embeddings
`RMFE_EMBED[i]` and the one stored at `out[1]` their sum, which `rmfeBlock_holds` turns into
`keccakInstanceWeights s` (V:1960) and its sum.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr Finset

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-- The block, `keccak_layer`'s statements `887 .. 1029`. -/
def rmfeBlockT : List Stmt :=
  [.atom (.const (.n 1090) (word 1 0 0)),
    .atom (.mul (.n 1091) (.n 1090) (.n 1089)),
    .atom (.mul (.n 1092) (.n 1091) (.n 1089)),
    .atom (.mul (.n 1093) (.n 1092) (.n 1089)),
    .atom (.mul (.n 1094) (.n 1093) (.n 1089)),
    .atom (.mul (.n 1095) (.n 1094) (.n 1089)),
    .atom (.mul (.n 1096) (.n 1095) (.n 1089)),
    .atom (.mul (.n 1097) (.n 1096) (.n 1089)),
    .atom (.mul (.n 1098) (.n 1097) (.n 1089)),
    .atom (.mul (.n 1099) (.n 1098) (.n 1089)),
    .atom (.mul (.n 1100) (.n 1099) (.n 1089)),
    .atom (.mul (.n 1101) (.n 1100) (.n 1089)),
    .atom (.mul (.n 1102) (.n 1101) (.n 1089)),
    .atom (.mul (.n 1103) (.n 1102) (.n 1089)),
    .atom (.mul (.n 1104) (.n 1103) (.n 1089)),
    .atom (.mul (.n 1105) (.n 1104) (.n 1089)),
    .atom (.mul (.n 1106) (.n 1105) (.n 1089)),
    .atom (.mul (.n 1107) (.n 1106) (.n 1089)),
    .atom (.mul (.n 1108) (.n 1107) (.n 1089)),
    .atom (.mul (.n 1109) (.n 1108) (.n 1089)),
    .atom (.mul (.n 1110) (.n 1109) (.n 1089)),
    .atom (.mul (.n 1111) (.n 1110) (.n 1089)),
    .atom (.mul (.n 1112) (.n 1111) (.n 1089)),
    .atom (.mul (.n 1113) (.n 1112) (.n 1089)),
    .atom (.add (.n 1114) (.n 1091) (.n 1092)),
    .atom (.add (.n 1115) (.n 1114) (.n 1094)),
    .atom (.add (.n 1116) (.n 1115) (.n 1099)),
    .atom (.add (.n 1117) (.n 1116) (.n 1101)),
    .atom (.add (.n 1118) (.n 1117) (.n 1105)),
    .atom (.add (.n 1119) (.n 1118) (.n 1106)),
    .atom (.add (.n 1120) (.n 1119) (.n 1113)),
    .atom (.copy (.n 1121) (.n 1120)),
    .atom (.add (.n 1122) (.n 1090) (.n 1093)),
    .atom (.add (.n 1123) (.n 1122) (.n 1094)),
    .atom (.add (.n 1124) (.n 1123) (.n 1095)),
    .atom (.add (.n 1125) (.n 1124) (.n 1096)),
    .atom (.add (.n 1126) (.n 1125) (.n 1097)),
    .atom (.add (.n 1127) (.n 1126) (.n 1100)),
    .atom (.add (.n 1128) (.n 1127) (.n 1101)),
    .atom (.add (.n 1129) (.n 1128) (.n 1102)),
    .atom (.add (.n 1130) (.n 1129) (.n 1103)),
    .atom (.add (.n 1131) (.n 1130) (.n 1105)),
    .atom (.add (.n 1132) (.n 1131) (.n 1106)),
    .atom (.add (.n 1133) (.n 1132) (.n 1107)),
    .atom (.add (.n 1134) (.n 1133) (.n 1108)),
    .atom (.add (.n 1135) (.n 1134) (.n 1109)),
    .atom (.add (.n 1136) (.n 1135) (.n 1110)),
    .atom (.add (.n 1137) (.n 1136) (.n 1111)),
    .atom (.mul (.n 1138) (.n 1089) (.n 1137)),
    .atom (.add (.n 1139) (.n 1137) (.n 1138)),
    .atom (.add (.n 1140) (.n 1120) (.n 1137)),
    .atom (.add (.n 1141) (.n 1091) (.n 1092)),
    .atom (.add (.n 1142) (.n 1141) (.n 1099)),
    .atom (.add (.n 1143) (.n 1142) (.n 1101)),
    .atom (.add (.n 1144) (.n 1143) (.n 1102)),
    .atom (.add (.n 1145) (.n 1144) (.n 1103)),
    .atom (.add (.n 1146) (.n 1145) (.n 1106)),
    .atom (.add (.n 1147) (.n 1146) (.n 1109)),
    .atom (.add (.n 1148) (.n 1147) (.n 1110)),
    .atom (.add (.n 1149) (.n 1148) (.n 1111)),
    .atom (.mul (.n 1150) (.n 1089) (.n 1149)),
    .atom (.add (.n 1151) (.n 1149) (.n 1150)),
    .atom (.add (.n 1152) (.n 1140) (.n 1149)),
    .atom (.add (.n 1153) (.n 1092) (.n 1096)),
    .atom (.add (.n 1154) (.n 1153) (.n 1098)),
    .atom (.add (.n 1155) (.n 1154) (.n 1099)),
    .atom (.add (.n 1156) (.n 1155) (.n 1101)),
    .atom (.add (.n 1157) (.n 1156) (.n 1104)),
    .atom (.add (.n 1158) (.n 1157) (.n 1107)),
    .atom (.add (.n 1159) (.n 1158) (.n 1108)),
    .atom (.add (.n 1160) (.n 1159) (.n 1109)),
    .atom (.add (.n 1161) (.n 1160) (.n 1112)),
    .atom (.mul (.n 1162) (.n 1089) (.n 1161)),
    .atom (.add (.n 1163) (.n 1162) (.n 1120)),
    .atom (.add (.n 1164) (.n 1161) (.n 1163)),
    .atom (.add (.n 1165) (.n 1152) (.n 1161)),
    .atom (.add (.n 1166) (.n 1093) (.n 1095)),
    .atom (.add (.n 1167) (.n 1166) (.n 1100)),
    .atom (.add (.n 1168) (.n 1167) (.n 1101)),
    .atom (.add (.n 1169) (.n 1168) (.n 1103)),
    .atom (.add (.n 1170) (.n 1169) (.n 1104)),
    .atom (.add (.n 1171) (.n 1170) (.n 1105)),
    .atom (.add (.n 1172) (.n 1171) (.n 1108)),
    .atom (.add (.n 1173) (.n 1172) (.n 1109)),
    .atom (.add (.n 1174) (.n 1173) (.n 1110)),
    .atom (.add (.n 1175) (.n 1174) (.n 1111)),
    .atom (.add (.n 1176) (.n 1175) (.n 1112)),
    .atom (.mul (.n 1177) (.n 1089) (.n 1176)),
    .atom (.add (.n 1178) (.n 1177) (.n 1120)),
    .atom (.add (.n 1179) (.n 1176) (.n 1178)),
    .atom (.add (.n 1180) (.n 1165) (.n 1176)),
    .atom (.mul (.n 1181) (.n 1089) (.n 1179)),
    .atom (.add (.n 1182) (.n 1180) (.n 1181)),
    .atom (.add (.n 1183) (.n 1091) (.n 1093)),
    .atom (.add (.n 1184) (.n 1183) (.n 1095)),
    .atom (.add (.n 1185) (.n 1184) (.n 1099)),
    .atom (.add (.n 1186) (.n 1185) (.n 1101)),
    .atom (.add (.n 1187) (.n 1186) (.n 1105)),
    .atom (.add (.n 1188) (.n 1187) (.n 1106)),
    .atom (.add (.n 1189) (.n 1188) (.n 1107)),
    .atom (.add (.n 1190) (.n 1189) (.n 1108)),
    .atom (.add (.n 1191) (.n 1190) (.n 1109)),
    .atom (.mul (.n 1192) (.n 1089) (.n 1191)),
    .atom (.add (.n 1193) (.n 1191) (.n 1192)),
    .atom (.add (.n 1194) (.n 1182) (.n 1191)),
    .atom (.mul (.n 1195) (.n 1089) (.n 1193)),
    .atom (.add (.n 1196) (.n 1194) (.n 1195)),
    .atom (.add (.n 1197) (.n 1093) (.n 1094)),
    .atom (.add (.n 1198) (.n 1197) (.n 1095)),
    .atom (.add (.n 1199) (.n 1198) (.n 1097)),
    .atom (.add (.n 1200) (.n 1199) (.n 1098)),
    .atom (.add (.n 1201) (.n 1200) (.n 1099)),
    .atom (.add (.n 1202) (.n 1201) (.n 1101)),
    .atom (.add (.n 1203) (.n 1202) (.n 1103)),
    .atom (.add (.n 1204) (.n 1203) (.n 1105)),
    .atom (.add (.n 1205) (.n 1204) (.n 1106)),
    .atom (.add (.n 1206) (.n 1205) (.n 1107)),
    .atom (.add (.n 1207) (.n 1206) (.n 1109)),
    .atom (.add (.n 1208) (.n 1207) (.n 1110)),
    .atom (.add (.n 1209) (.n 1208) (.n 1111)),
    .atom (.mul (.n 1210) (.n 1089) (.n 1209)),
    .atom (.add (.n 1211) (.n 1209) (.n 1210)),
    .atom (.add (.n 1212) (.n 1196) (.n 1209)),
    .atom (.mul (.n 1213) (.n 1089) (.n 1211)),
    .atom (.add (.n 1214) (.n 1213) (.n 1120)),
    .atom (.add (.n 1215) (.n 1212) (.n 1214)),
    .atom (.load (.n 1139) (.n 12) 6),
    .atom (.load (.n 1138) (.n 12) 7),
    .atom (.load (.n 1151) (.n 12) 8),
    .atom (.load (.n 1150) (.n 12) 9),
    .atom (.load (.n 1164) (.n 12) 10),
    .atom (.load (.n 1163) (.n 12) 11),
    .atom (.load (.n 1179) (.n 12) 12),
    .atom (.load (.n 1178) (.n 12) 13),
    .atom (.load (.n 1181) (.n 12) 14),
    .atom (.load (.n 1193) (.n 12) 15),
    .atom (.load (.n 1192) (.n 12) 16),
    .atom (.load (.n 1195) (.n 12) 17),
    .atom (.load (.n 1211) (.n 12) 18),
    .atom (.load (.n 1210) (.n 12) 19),
    .atom (.load (.n 1214) (.n 12) 20),
    .atom (.load (.n 1121) (.n 12) 21),
    .atom (.load (.n 1215) (.n 12) 1)]


/-- The values stored at `out[6 + i]`. -/
def rmfeStores : List ℕ :=
  [1139, 1138, 1151, 1150, 1164, 1163, 1179, 1178, 1181, 1193, 1192, 1195, 1211, 1210, 1214, 1121]

/-- The sum of the embeddings, as a mask. -/
def embedXor : ℕ := embedLit.foldl (· ^^^ ·) 0

/-- The block's masks, checked. -/
def rmfeCheck : Bool :=
  match maskRun (.n 1089) [(.n 1089, 2)] rmfeBlockT with
  | some st => (List.range 16).all (fun i ↦ st.lookup (.n (rmfeStores.getD i 0)) ==
      some (embedLit.getD i 0)) && st.lookup (.n 1215) == some embedXor
  | none => false

theorem rmfeCheck_true : rmfeCheck = true := by decide +kernel

theorem rmfeBlock_atoms : rmfeBlockT.all isAtom = true := by decide +kernel

theorem rmfeBlock_stores : ∀ i < 16, rmfeBlockT.any (fun s ↦ stmtEqb s
    (.atom (.load (.n (rmfeStores.getD i 0)) (.n 12) (6 + i)))) = true := by decide +kernel

theorem rmfeBlock_kappa : rmfeBlockT.any (fun s ↦ stmtEqb s (.atom (.load (.n 1215) (.n 12) 1))) =
    true := by decide +kernel

/-! ## The weights as masks -/

theorem pe_zero (x : E) : pe 0 x = 0 := by simp [pe]

theorem pe_two (x : E) : pe 2 x = x := by
  rw [show (2 : ℕ) = 1 <<< 1 from rfl, pe_shl 1 (by norm_num), pe_one, mul_one]

theorem pe_of_lt (m : ℕ) (hm : m < 2 ^ 24) (x : E) :
    pe m x = ∑ b ∈ range 24, if m.testBit b then x ^ b else 0 := by
  unfold pe
  refine (Finset.sum_subset (fun b hb ↦ by simp at hb ⊢; omega) fun b _ hb ↦ ?_).symm
  have h24 : 24 ≤ b := by simpa using hb
  rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) h24))]
  simp

theorem embedLit_lt : ∀ e ∈ embedLit, e < 2 ^ 24 := by decide +kernel

/-- The instance weights at `s` are the embeddings' masks at `s`. -/
theorem keccakInstanceWeights_pe (s : E) :
    keccakInstanceWeights s = embedLit.map (fun e ↦ pe e s) := by
  simp only [keccakInstanceWeights]
  rw [rmfeEmbed_eq]
  refine List.map_congr_left fun e he ↦ ?_
  rw [sumE_filterMap_range, show embedBits = 24 from rfl, pe_of_lt e (embedLit_lt e he)]
  refine Finset.sum_congr rfl fun b hb ↦ ?_
  rw [powers_getD s (Finset.mem_range.1 hb)]

theorem keccakInstanceWeights_getD_pe (s : E) {i : ℕ} (hi : i < 16) :
    (keccakInstanceWeights s).getD i 0 = pe (embedLit.getD i 0) s := by
  have hl : i < embedLit.length := hi
  rw [keccakInstanceWeights_pe, List.getD_eq_getElem _ _ (by simpa using hl),
    List.getD_eq_getElem _ _ hl, List.getElem_map]

theorem pe_foldl_xor (x : E) :
    ∀ (l : List ℕ) (a : ℕ), pe (l.foldl (· ^^^ ·) a) x = pe a x + (l.map (pe · x)).sum
  | [], a => by simp
  | e :: l, a => by
    rw [List.foldl_cons, pe_foldl_xor x l, pe_xor, List.map_cons, List.sum_cons, add_assoc]

theorem sumE_keccakInstanceWeights (s : E) :
    sumE (keccakInstanceWeights s) = pe embedXor s := by
  rw [keccakInstanceWeights_pe, LeanVM.Protocol.KeccakGkr.sumE_eq_sum, embedXor, pe_foldl_xor,
    pe_zero, zero_add]

/-- **The instance weights, stored** (G:2514-2613 against V:1960): if the block holds, the next
claim's record holds `keccakInstanceWeights s` at `out[6 + i]` and their sum at `out[1]`. -/
theorem rmfeBlock_holds {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ rmfeBlockT next kret) :
    (∀ i < 16, LoadHolds rd (σ (.n 12)) (6 + i)
      ((keccakInstanceWeights (σ (.n 1089))).getD i 0)) ∧
    LoadHolds rd (σ (.n 12)) 1 (sumE (keccakInstanceWeights (σ (.n 1089)))) := by
  have hc := rmfeCheck_true
  unfold rmfeCheck at hc
  split at hc
  · rename_i st hst
    have hok0 : MaskOk σ (σ (.n 1089)) [(.n 1089, 2)] := by
      intro p hp
      rw [List.mem_singleton] at hp
      subst hp
      exact (pe_two _).symm
    obtain ⟨hok, -⟩ := maskRun_sound hst hok0 h
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at hc
    obtain ⟨hst16, hk⟩ := hc
    refine ⟨fun i hi ↦ ?_, ?_⟩
    · have hl := atom_of_block rmfeBlock_atoms h _ (rmfeBlock_stores i hi)
      simp only [Atom.Holds] at hl
      rwa [hok.lookup (hst16 i hi), ← keccakInstanceWeights_getD_pe _ hi] at hl
    · have hl := atom_of_block rmfeBlock_atoms h _ rmfeBlock_kappa
      simp only [Atom.Holds] at hl
      rwa [hok.lookup hk, ← sumE_keccakInstanceWeights] at hl
  · cases hc

end
end LeanVM.Guest.B1.VerifySub
