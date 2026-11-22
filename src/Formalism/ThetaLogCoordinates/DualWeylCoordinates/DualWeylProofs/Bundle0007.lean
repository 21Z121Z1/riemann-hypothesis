import Formalism.ThetaLogCoordinates.DualWeylCoordinates.Bundle0002
import Formalism.ThetaLogCoordinates.JacobiPathWeights.FinalP
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.Bundle0006

-- bundled from Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.ExtendedColumns
section
noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

open Formalism.InvariantFactorPaths.GelfandTsetlinBases (dGT colHeight)
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch (TabP Dom cnt)

lemma qk_colH_low {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) {c : ℤ} (hc : c ≤ mu (lastIdx n)) :
    colH mu c = n := by
  unfold colH
  rw [filter_true_of_mem, card_univ, Fintype.card_fin]
  intro m _
  refine hc.trans (hmu ?_)
  show m.1 ≤ n - 1
  have := m.2
  omega

lemma qk_colH_high {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) {c : ℤ} (hc : mu 0 < c) :
    colH mu c = 0 := by
  unfold colH
  rw [filter_false_of_mem, card_empty]
  intro m _
  have : mu m ≤ mu 0 := hmu (Fin.zero_le m)
  omega

def extendedColumns {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) : ℤ → Finset (Fin n) :=
  fun c => if h : c ∈ TCols mu then (I ⟨c, h⟩).1 else if c ≤ mu (lastIdx n) then univ else ∅

lemma qk_dom_univ {n : ℕ} (B : Finset (Fin n)) : Dom univ B := by
  intro x
  exact card_le_card (filter_subset_filter _ (subset_univ _))

lemma qk_dom_empty {n : ℕ} (A : Finset (Fin n)) : Dom A ∅ := by
  intro x
  simp [cnt]

lemma qk_dom_iff {n : ℕ} [NeZero n] (A B : Finset (Fin n)) :
    Dom A B ↔ ∀ t : Fin n, (B.filter (· ≤ t)).card ≤ (A.filter (· ≤ t)).card := by
  have key : ∀ (C : Finset (Fin n)) (t : Fin n), (C.filter (· ≤ t)).card = cnt C (t.1 + 1) := by
    intro C t
    unfold cnt
    congr 1
    ext a
    simp only [mem_filter, Fin.le_def, Nat.lt_succ_iff]
  constructor
  · intro h t
    rw [key, key]
    exact h _
  · intro h x
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · simp [cnt]
    · by_cases hxn : x ≤ n
      · have := h ⟨x - 1, by omega⟩
        rw [key, key] at this
        have e : x - 1 + 1 = x := by omega
        simpa only [e] using this
      · have hn : 0 < n := NeZero.pos n
        have := h ⟨n - 1, by omega⟩
        rw [key, key] at this
        have e : n - 1 + 1 = n := by omega
        simp only [e] at this
        rw [Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.cnt_of_le A (by omega), Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.cnt_of_le B (by omega),
          ← Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.cnt_of_le A le_rfl, ← Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.cnt_of_le B le_rfl]
        exact this

lemma qk_T_tab {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) (I : TIdx mu) (hI : StdT I) :
    TabP mu (extendedColumns I) := by
  refine ⟨fun c => ?_, fun c => ?_⟩
  · unfold extendedColumns
    split_ifs with h h2
    · exact (I ⟨c, h⟩).2
    · rw [card_univ, Fintype.card_fin]
      exact (qk_colH_low hmu h2).symm
    · rw [card_empty]
      refine (qk_colH_high hmu ?_).symm
      simp only [TCols, mem_Ioc, not_and, not_le] at h
      exact h (not_le.1 h2)
  · by_cases h1 : c ≤ mu (lastIdx n)
    · have : extendedColumns I c = univ := by
        unfold extendedColumns
        rw [dif_neg (by simp only [TCols, mem_Ioc]; omega), if_pos h1]
      rw [this]
      exact qk_dom_univ _
    · by_cases h2 : c + 1 ≤ mu 0
      · have hc : c ∈ TCols mu := by simp only [TCols, mem_Ioc]; omega
        have hc' : c + 1 ∈ TCols mu := by simp only [TCols, mem_Ioc]; omega
        have e1 : extendedColumns I c = (I ⟨c, hc⟩).1 := by unfold extendedColumns; rw [dif_pos hc]
        have e2 : extendedColumns I (c + 1) = (I ⟨c + 1, hc'⟩).1 := by unfold extendedColumns; rw [dif_pos hc']
        rw [e1, e2, qk_dom_iff]
        exact hI ⟨c, hc⟩ hc'
      · have : extendedColumns I (c + 1) = ∅ := by
          unfold extendedColumns
          rw [dif_neg (by simp only [TCols, mem_Ioc]; omega), if_neg (by omega)]
        rw [this]
        exact qk_dom_empty _

def qk_tabEquiv {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) :
    {I : TIdx mu // StdT I} ≃ {T : ℤ → Finset (Fin n) // TabP mu T} where
  toFun I := ⟨extendedColumns I.1, qk_T_tab hmu I.1 I.2⟩
  invFun T := ⟨fun c => ⟨T.1 c, T.2.1 c⟩, fun c hc => (qk_dom_iff _ _).1 (T.2.2 c)⟩
  left_inv I := by
    apply Subtype.ext
    funext c
    apply Subtype.ext
    show extendedColumns I.1 c = _
    unfold extendedColumns
    rw [dif_pos c.2]
  right_inv T := by
    apply Subtype.ext
    funext c
    show extendedColumns _ c = _
    unfold extendedColumns
    split_ifs with h h2
    · rfl
    · symm
      rw [← card_eq_iff_eq_univ, Fintype.card_fin, T.2.1 c]
      exact qk_colH_low hmu h2
    · symm
      rw [← card_eq_zero, T.2.1 c]
      refine qk_colH_high hmu ?_
      simp only [TCols, mem_Ioc, not_and, not_le] at h
      exact h (not_le.1 h2)

theorem qk_dMu_eq_dGT : ∀ (n : ℕ) [NeZero n] (mu : Fin n → ℤ), Dominant mu → dMu mu = dGT n mu := by
  intro n _ mu hmu
  unfold dMu
  rw [Nat.card_congr (qk_tabEquiv hmu)]
  exact (Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.tab_count n mu hmu).2

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

-- bundled from Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.KStableHighestWeightVector
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

lemma qr_det_full {m : ℕ} {R : Type} [CommRing R] (A : Matrix (Fin m) (Fin m) R) {k : ℕ} (hk : k = m)
    (S : Finset (Fin m)) (hS : S.card = k) :
    (A.submatrix (S.orderEmbOfFin hS) (S.orderEmbOfFin hS)).det = A.det := by
  subst hk
  exact Matrix.det_submatrix_equiv_self
    (Equiv.ofBijective _ (Finite.injective_iff_bijective.1 (S.orderEmbOfFin hS).injective)) A

lemma qr_det_empty {m : ℕ} {R : Type} [CommRing R] (A : Matrix (Fin m) (Fin m) R) {k : ℕ} (hk : k = 0)
    (r c : Fin k → Fin m) : (A.submatrix r c).det = 1 := by
  subst hk
  exact Matrix.det_fin_zero

section TM

variable {m : ℕ} [NeZero m] {lam : Fin (m + 1) → ℤ} {nu : Fin m → ℤ} {R : Type} [CommRing R]
  {h : GL (Fin (m + 1)) R} {g1 : GL (Fin m) R} {t : Rˣ}

lemma qr_dU_block (hb : IsBlock h g1 t) : qc_dU h = t * qc_dU g1 := by
  apply Units.ext
  rw [Units.val_mul, qc_dU_coe, qc_dU_coe, qr_det_block hb]

lemma qr_TMat_zero (hb : IsBlock h g1 t) (hn : Dominant nu) (hi : Interl lam nu) (K : TIdx lam) (I' : TIdx nu)
    (hK : ∀ K', qr_j hi K' ≠ K) : evGL h (TMat lam K (qr_j hi I')) = 0 := by
  have h1 : ∃ c : ↥(TCols lam), ¬ (Fin.last m ∈ (K c).1 ↔ colH lam c = colH nu c + 1) := by
    by_contra hcon
    obtain ⟨K', hK'⟩ := qr_j_surj hn hi K (fun c => by
      by_contra h2; exact hcon ⟨c, h2⟩)
    exact hK K' hK'
  obtain ⟨c, hc⟩ := h1
  simp only [TMat, map_mul, map_prod, qc_evGL_minorC]
  rw [Finset.prod_eq_zero (Finset.mem_univ c), mul_zero]
  exact qr_minor_zero hb _ _ _ _ _ hc

def qr_mn (g1 : GL (Fin m) R) {k : ℕ} (x y : {S : Finset (Fin m) // S.card = k}) : R :=
  (g1.val.submatrix (x.1.orderEmbOfFin x.2) (y.1.orderEmbOfFin y.2)).det

def qr_G (g1 : GL (Fin m) R) (K' I' : TIdx nu) (c : ℤ) : R := qr_mn g1 (qr_base K' c) (qr_base I' c)

lemma qr_G_low (hn : Dominant nu) (K' I' : TIdx nu) {c : ℤ} (hc : c ≤ nu (lastIdx m)) :
    qr_G g1 K' I' c = g1.val.det := by
  have h1 : c ∉ TCols nu := by
    simp only [TCols, Finset.mem_Ioc, not_and_or, not_lt]; exact Or.inl hc
  have := qr_subsing hn h1
  rw [qr_G, Subsingleton.elim (qr_base K' c) (qr_base I' c)]
  exact qr_det_full _ (qr_colH_low hn hc) _ _

lemma qr_G_high (hn : Dominant nu) (K' I' : TIdx nu) {c : ℤ} (hc : nu 0 < c) :
    qr_G g1 K' I' c = 1 :=
  qr_det_empty _ (qr_colH_high hn hc) _ _

lemma qr_prod_G (hn : Dominant nu) (hi : Interl lam nu) (K' I' : TIdx nu) :
    ∏ c ∈ TCols lam, qr_G g1 K' I' c =
      g1.val.det ^ (nu (lastIdx m) - lam (Fin.last m)).toNat *
        ∏ c : ↥(TCols nu), (g1.val.submatrix ((K' c).1.orderEmbOfFin (K' c).2)
          ((I' c).1.orderEmbOfFin (I' c).2)).det := by
  have h1 := qr_lam_last_le hi
  have h2 : nu (lastIdx m) ≤ nu 0 := qr_le_last hn 0
  have h3 := qr_nu_zero_le hi
  rw [TCols, qr_lastIdx, ← Finset.Ioc_union_Ioc_eq_Ioc h1 (h2.trans h3),
    Finset.prod_union (Finset.Ioc_disjoint_Ioc_of_le le_rfl), ← Finset.Ioc_union_Ioc_eq_Ioc h2 h3,
    Finset.prod_union (Finset.Ioc_disjoint_Ioc_of_le le_rfl)]
  rw [Finset.prod_congr rfl (fun c hc => qr_G_low hn K' I' (Finset.mem_Ioc.1 hc).2), Finset.prod_const,
    Int.card_Ioc,
    Finset.prod_congr (s₁ := Finset.Ioc (nu 0) (lam 0)) rfl (fun c hc => qr_G_high hn K' I' (Finset.mem_Ioc.1 hc).1),
    Finset.prod_const_one, mul_one]
  congr 1
  rw [← Finset.prod_coe_sort]
  refine Finset.prod_congr rfl fun c _ => ?_
  have e1 := qr_base_mem K' c
  have e2 := qr_base_mem I' c
  rw [qr_G, e1, e2]
  rfl

lemma qr_card_C (hl : Dominant lam) (hn : Dominant nu) (hi : Interl lam nu) :
    (((TCols lam).filter fun c => colH lam c = colH nu c + 1).card : ℤ) =
      ∑ a, lam a - ∑ a, nu a - lam (Fin.last m) := by
  have h1 : ∀ c, ((if colH lam c = colH nu c + 1 then 1 else 0 : ℕ) : ℤ) = (colH lam c : ℤ) - colH nu c := by
    intro c
    have := qr_colH_eq hi c
    omega
  rw [Finset.card_filter]
  simp only [Nat.cast_sum, h1]
  rw [Finset.sum_sub_distrib, TCols, qr_lastIdx,
    qr_sum_colH lam _ _ (fun a => ⟨hl (Fin.le_last a), qr_le_zero hl a⟩),
    qr_sum_colH nu _ _ (fun a => ⟨(qr_lam_last_le hi).trans (qr_le_last hn a),
      (qr_le_zero hn a).trans (qr_nu_zero_le hi)⟩)]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

theorem qr_TMat_j (hb : IsBlock h g1 t) (hl : Dominant lam) (hn : Dominant nu) (hi : Interl lam nu)
    (K' I' : TIdx nu) :
    evGL h (TMat lam (qr_j hi K') (qr_j hi I')) =
      ((t ^ (∑ a, lam a - ∑ a, nu a) : Rˣ) : R) * evGL g1 (TMat nu K' I') := by
  simp only [TMat, map_mul, map_prod, qc_evGL_detU_zpow, qc_evGL_minorC]
  have h1 : ∀ c : ↥(TCols lam),
      (h.val.submatrix ((qr_j hi K' c).1.orderEmbOfFin (qr_j hi K' c).2)
        ((qr_j hi I' c).1.orderEmbOfFin (qr_j hi I' c).2)).det =
      (if colH lam c = colH nu c + 1 then (t : R) else 1) * qr_G g1 K' I' c := fun c =>
    qr_minor_ext hb _ _ _ (qr_base K' c).2 (qr_base I' c).2 _ _
  rw [Finset.prod_congr rfl (fun c _ => h1 c), Finset.prod_mul_distrib,
    Finset.prod_coe_sort (TCols lam) (fun c => if colH lam c = colH nu c + 1 then (t : R) else 1),
    Finset.prod_coe_sort (TCols lam) (fun c => qr_G g1 K' I' c), qr_prod_G hn hi, Finset.prod_ite,
    Finset.prod_const, Finset.prod_const_one, mul_one, qr_dU_block hb, qr_lastIdx]
  have hC := qr_card_C hl hn hi
  set N := ((TCols lam).filter fun c => colH lam c = colH nu c + 1).card
  set P := (nu (lastIdx m) - lam (Fin.last m)).toNat with hP
  have hP' : (P : ℤ) = nu (lastIdx m) - lam (Fin.last m) :=
    Int.toNat_of_nonneg (sub_nonneg.2 (qr_lam_last_le hi))
  have e1 : t ^ (∑ a, lam a - ∑ a, nu a) = t ^ lam (Fin.last m) * t ^ N := by
    rw [← zpow_natCast, ← zpow_add, hC]; congr 1; ring
  have e2 : qc_dU g1 ^ nu (lastIdx m) = qc_dU g1 ^ lam (Fin.last m) * qc_dU g1 ^ P := by
    rw [← zpow_natCast, ← zpow_add, hP']; congr 1; ring
  rw [e1, e2, mul_zpow]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, qc_dU_coe]
  ring

end TM

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

-- bundled from Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.MemSpanStandardIffProjZero
section
noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ} [NeZero n]

lemma qb_ev_zero_of_mem {M : GLMod n} (CF : ColFam M) (F : Type) [CommRing F] {pi : Set (Fin n → ℤ)}
    (hpi : DomLowerSet pi) {j : CF.J} (hj : CF.mu j ∈ pi) (I : TIdx (CF.mu j)) {mu : Fin n → ℤ}
    (hmu : Dominant mu) (hout : mu ∉ pi) : qb_ev M F mu (fun i => (CF.vec j I i : F)) = 0 :=
  qb_key_zero CF F j I mu fun hle => hout (hpi.2 _ hj _ hmu hle)

lemma qb_exists_coeff (hA : LemmaA) {M : GLMod n} (CF : ColFam M) (R : Type) [CommRing R] (x : M.ι → R) :
    ∃ a : qb_Idx CF → R, x = ∑ y, a y • qb_vecF CF R y := by
  refine ⟨fun y => (qb_basis hA CF R).repr x y, ?_⟩
  conv_lhs => rw [← (qb_basis hA CF R).sum_repr x]
  simp only [qb_basis_apply]

theorem mem_span_standard_iff_proj_zero (hA : LemmaA) {M : GLMod n} (CF : ColFam M) (pi : Set (Fin n → ℤ)) (hpi : DomLowerSet pi)
    (F : Type) [Field F] (x : M.ι → F) :
    x ∈ Submodule.span F {y | ∃ j, CF.mu j ∈ pi ∧ ∃ I : TIdx (CF.mu j), StdT I ∧ y = fun i => (CF.vec j I i : F)} ↔
      ∀ mu, Dominant mu → mu ∉ pi → qb_ev M F mu x = 0 := by
  constructor
  · intro hx mu hmu hout
    have : Submodule.span F {y | ∃ j, CF.mu j ∈ pi ∧ ∃ I : TIdx (CF.mu j), StdT I ∧
        y = fun i => (CF.vec j I i : F)} ≤ LinearMap.ker (qb_evL M F mu) := by
      rw [Submodule.span_le]
      rintro y ⟨j, hj, I, -, rfl⟩
      exact qb_ev_zero_of_mem CF F hpi hj I hmu hout
    exact this hx
  · intro h
    obtain ⟨a, rfl⟩ := qb_exists_coeff hA CF F x
    have hs := qb_supp_in hA CF F a pi hpi h
    refine Submodule.sum_mem _ fun y _ => ?_
    by_cases hy : a y = 0
    · rw [hy, zero_smul]; exact zero_mem _
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨y.1, hs y hy, y.2.1, y.2.2, rfl⟩)

theorem qb_mem_std (hA : LemmaA) {M : GLMod n} (CF : ColFam M) (pi : Set (Fin n → ℤ)) (hpi : DomLowerSet pi)
    (x : M.ι → ℤ) (h : ∀ mu, Dominant mu → mu ∉ pi → qb_ev M ℚ mu (fun i => (x i : ℚ)) = 0) :
    x ∈ Submodule.span ℤ {x | ∃ j, CF.mu j ∈ pi ∧ ∃ I : TIdx (CF.mu j), StdT I ∧ x = CF.vec j I} := by
  obtain ⟨a, rfl⟩ := qb_exists_coeff hA CF ℤ x
  have hc : (fun i => (((∑ y, a y • qb_vecF CF ℤ y) i : ℤ) : ℚ)) = ∑ y, (a y : ℚ) • qb_vecF CF ℚ y := by
    funext i
    simp [qb_vecF, Finset.sum_apply]
  rw [hc] at h
  have hs := qb_supp_in hA CF ℚ (fun y => (a y : ℚ)) pi hpi h
  refine Submodule.sum_mem _ fun y _ => ?_
  by_cases hy : a y = 0
  · rw [hy, zero_smul]; exact zero_mem _
  · exact Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨y.1, hs y (by exact_mod_cast hy), y.2.1, y.2.2, by rw [qb_vecF_int]⟩)

theorem qb_Mpi_eq (hA : LemmaA) {M : GLMod n} (CF : ColFam M) (pi : Set (Fin n → ℤ)) (hpi : DomLowerSet pi) :
    CF.Mpi pi = Submodule.span ℤ {x | ∃ j, CF.mu j ∈ pi ∧ ∃ I : TIdx (CF.mu j), StdT I ∧ x = CF.vec j I} := by
  apply le_antisymm
  · unfold ColFam.Mpi
    rw [Submodule.span_le]
    rintro x ⟨j, hj, I, rfl⟩
    exact qb_mem_std hA CF pi hpi _ fun mu hmu hout => qb_ev_zero_of_mem CF ℚ hpi hj I hmu hout
  · apply Submodule.span_mono
    rintro x ⟨j, hj, I, -, rfl⟩
    exact ⟨j, hj, I, rfl⟩

theorem qb_Mpi_eq_image (hA : LemmaA) {M : GLMod n} (CF : ColFam M) (pi : Set (Fin n → ℤ)) (hpi : DomLowerSet pi) :
    CF.Mpi pi = Submodule.span ℤ (qb_basis hA CF ℤ '' {y | CF.mu y.1 ∈ pi}) := by
  rw [qb_Mpi_eq hA CF pi hpi]
  congr 1
  ext x
  constructor
  · rintro ⟨j, hj, I, hI, rfl⟩
    exact ⟨⟨j, I, hI⟩, hj, by rw [qb_basis_apply, qb_vecF_int]⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.1, hy, y.2.1, y.2.2, by rw [qb_basis_apply, qb_vecF_int]⟩

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

-- bundled from Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QxFstInj
section
noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ} [NeZero n] {κ : Type} [Fintype κ] [DecidableEq κ] {B : Matrix κ κ (GLCoord ℤ n)}
  {be : κ → Fin n → ℤ} {Str : (Fin n → ℤ) → Finset (Fin n → ℤ)}
  {ps : (mu nu : Fin n → ℤ) → Matrix (TIdx mu × κ) (TIdx nu) ℤ} {M M' : GLMod n}

lemma qx_fst_inj (CF : ColFam M) (nu0 : Fin n → ℤ) (x y : {x : qx_J Str CF // (x.2 : Fin n → ℤ) = nu0})
    (h : x.1.1 = y.1.1) : x = y := by
  obtain ⟨⟨j, nu, hnu⟩, hx⟩ := x
  obtain ⟨⟨j', nu', hnu'⟩, hy⟩ := y
  simp only at h hx hy
  subst h
  subst hx
  subst hy
  rfl

theorem qx_indep (hd : IsStripData B be Str ps) (e : M'.ι ≃ M.ι × κ) (CF : ColFam M) (F : Type) [Field F]
    (nu0 : Fin n → ℤ) :
    LinearIndependent F (fun x : {x : qx_J Str CF // (x.2 : Fin n → ℤ) = nu0} =>
      fun i => ((qx_ph ps e CF x.1 i (canT (x.1.2 : Fin n → ℤ)) : ℤ) : F)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  by_contra hcon
  push Not at hcon
  obtain ⟨x1, hx1⟩ := hcon
  let s : Finset (Fin n → ℤ) := (univ.filter fun x => g x ≠ 0).image fun x => CF.mu x.1.1
  obtain ⟨mu0, hmu0, hmax⟩ := qb_exists_max s ⟨_, mem_image.2 ⟨x1, by simp [hx1], rfl⟩⟩
  obtain ⟨x0, hx0, rfl⟩ := mem_image.1 hmu0
  replace hx0 : g x0 ≠ 0 := by simpa using hx0
  obtain ⟨k0, hk0, heps⟩ := hd.2.2.2.2.1 (CF.mu x0.1.1) (CF.dom _) x0.1.2 x0.1.2.2
  have hK : ∀ x, g x ≠ 0 → ∀ K, ps (CF.mu x.1.1) x.1.2 (K, k0) (canT (x.1.2 : Fin n → ℤ)) ≠ 0 →
      CF.mu x.1.1 = CF.mu x0.1.1 ∧ K = canT (CF.mu x.1.1) := by
    intro x hgx K hne
    have h1 := qx_wt_can hd (CF.dom _) x.1.2.2 K k0 hne
    have h2 : qb_wtT (CF.mu x.1.1) K = CF.mu x0.1.1 := by
      rw [h1, hk0, x.2, x0.2, sub_sub_cancel]
    have h3 : DomLE (CF.mu x0.1.1) (CF.mu x.1.1) := h2 ▸ qb_wtT_le (CF.dom _) K
    have h4 := hmax _ (mem_image.2 ⟨x, by simp [hgx], rfl⟩) h3
    exact ⟨h4, (qb_wtT_eq_iff (CF.dom _) K).1 (h2.trans h4.symm)⟩
  have hterm : ∀ x (i : M.ι),
      g x * ((qx_ph ps e CF x.1 (e.symm (i, k0)) (canT (x.1.2 : Fin n → ℤ)) : ℤ) : F) =
      if CF.mu x.1.1 = CF.mu x0.1.1 then
        (g x * ((ps (CF.mu x.1.1) x.1.2 (canT (CF.mu x.1.1), k0) (canT (x.1.2 : Fin n → ℤ)) : ℤ) : F)) *
          ((CF.ph x.1.1 i (canT (CF.mu x.1.1)) : ℤ) : F) else 0 := by
    intro x i
    by_cases hgx : g x = 0
    · simp [hgx]
    rw [qx_ph_apply]
    simp only [Equiv.apply_symm_apply]
    split_ifs with hm
    · rw [Finset.sum_eq_single (canT (CF.mu x.1.1))]
      · push_cast; ring
      · intro K _ hKne
        exact mul_eq_zero_of_right _ (by_contra fun h => hKne (hK x hgx K h).2)
      · intro h; exact absurd (mem_univ _) h
    · rw [Finset.sum_eq_zero, Int.cast_zero, mul_zero]
      intro K _
      exact mul_eq_zero_of_right _ (by_contra fun h => hm (hK x hgx K h).1)
  have hrel : ∀ i : M.ι, ∑ x, g x *
      ((qx_ph ps e CF x.1 (e.symm (i, k0)) (canT (x.1.2 : Fin n → ℤ)) : ℤ) : F) = 0 := by
    intro i
    have := congrFun hg (e.symm (i, k0))
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using this
  simp only [hterm] at hrel
  have hli := (qb_indepF CF F (CF.mu x0.1.1)).comp
    (fun x : {x : {x : qx_J Str CF // (x.2 : Fin n → ℤ) = nu0} // CF.mu x.1.1 = CF.mu x0.1.1} =>
      (⟨x.1.1.1, x.2⟩ : {j : CF.J // CF.mu j = CF.mu x0.1.1}))
    (fun x y h => Subtype.ext (qx_fst_inj CF nu0 x.1 y.1 (congrArg Subtype.val h)))
  have h0 := Fintype.linearIndependent_iff.1 hli
    (fun x => g x.1 * ((ps (CF.mu x.1.1.1) x.1.1.2 (canT (CF.mu x.1.1.1), k0)
      (canT (x.1.1.2 : Fin n → ℤ)) : ℤ) : F)) ?_ ⟨x0, rfl⟩
  · simp only at h0
    rcases heps with h | h <;> rw [h] at h0 <;> simp at h0 <;> exact hx0 h0
  · funext i
    have := hrel i
    rw [← Finset.sum_filter, Finset.sum_subtype (p := fun x => CF.mu x.1.1 = CF.mu x0.1.1) _ (by simp)] at this
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Function.comp] using this

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

-- bundled from Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.WindowBoundOddCases
section
noncomputable section

namespace Formalism.InvariantFactorPaths.ColumnFamilies

theorem filtration_theorem_one_of : LemmaA → ColumnFamilyStandardVectorsBasis := by
  intro hA n _ M CF
  refine ⟨?_, fun R _ => qb_basisR hA CF R⟩
  have := qb_basisR hA CF ℤ
  rw [qb_vecF_int] at this
  exact this

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

