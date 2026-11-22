import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.Bundle0009
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QkDetExpand
import Formalism.ThetaLogCoordinates.ResidueClassEstimates.VandermondeRankEstimates.Branch
import Formalism.ThetaLogCoordinates.ResidueClassEstimates.VandermondeRankEstimates.WeylGT
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.Bundle0010

-- bundled from Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.CntLam
section
noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

open Formalism.InvariantFactorPaths.GelfandTsetlinBases (dGT)

lemma qk_prod_conv (n : ℕ) (F : ℕ → ℕ → ℝ) :
    ∏ j ∈ range n, ∏ i ∈ range j, F i j = ∏ i : Fin n, ∏ j ∈ Ioi i, F i j := by
  have h1 : ∀ i : Fin n, ∏ j ∈ Ioi i, F i j = ∏ j : Fin n, if i < j then F i j else 1 := by
    intro i
    rw [← prod_filter]
    congr 1
    ext j
    simp
  simp_rw [h1]
  rw [prod_comm, ← Fin.prod_univ_eq_prod_range (fun j => ∏ i ∈ range j, F i j) n]
  refine prod_congr rfl fun j _ => ?_
  have h2 : ∏ i : Fin n, (if i < j then F i j else 1) = ∏ i ∈ range n, if i < j.1 then F i j else 1 := by
    rw [← Fin.prod_univ_eq_prod_range (fun i => if i < j.1 then F i j else 1) n]
    refine prod_congr rfl fun i _ => ?_
    simp only [Fin.lt_def]
  rw [h2, ← prod_filter]
  congr 1
  ext i
  have := j.2
  simp only [mem_range, mem_filter]
  omega

def qk_v {n : ℕ} (mu : Fin n → ℤ) : Fin n → ℝ := fun i => (i.1 : ℝ) - (mu i : ℝ)

def vandermondeDenominator (n : ℕ) : ℝ := ∏ j ∈ range n, ∏ i ∈ range j, ((j : ℝ) - (i : ℝ))

lemma qk_W_ne (n : ℕ) : vandermondeDenominator n ≠ 0 := by
  unfold vandermondeDenominator
  refine prod_ne_zero_iff.2 fun j _ => prod_ne_zero_iff.2 fun i hi => ?_
  have : (i : ℝ) < (j : ℝ) := by exact_mod_cast mem_range.1 hi
  exact sub_ne_zero.2 (ne_of_gt this)

lemma qk_weyl {n : ℕ} (mu : Fin n → ℤ) :
    Formalism.InvariantFactorPaths.BranchingDimensions.weylDim n (Formalism.InvariantFactorPaths.BranchingDimensions.extW mu) * vandermondeDenominator n = qk_D (qk_v mu) := by
  unfold Formalism.InvariantFactorPaths.BranchingDimensions.weylDim
  simp_rw [prod_div_distrib]
  rw [show (∏ j ∈ range n, ∏ i ∈ range j, ((j : ℝ) - (i : ℝ))) = vandermondeDenominator n from rfl, div_mul_cancel₀ _ (qk_W_ne n),
    qk_prod_conv n (fun i j => ((Formalism.InvariantFactorPaths.BranchingDimensions.extW mu i - Formalism.InvariantFactorPaths.BranchingDimensions.extW mu j : ℤ) : ℝ) + ((j : ℝ) - (i : ℝ)))]
  unfold qk_D qk_v
  refine prod_congr rfl fun i _ => prod_congr rfl fun j _ => ?_
  rw [Formalism.InvariantFactorPaths.BranchingDimensions.WGT.extW_val, Formalism.InvariantFactorPaths.BranchingDimensions.WGT.extW_val]
  push_cast
  ring

lemma qk_D_dom {n : ℕ} {mu : Fin n → ℤ} (h : Dominant mu) : qk_D (qk_v mu) = (dGT n mu : ℝ) * vandermondeDenominator n := by
  rw [← qk_weyl, Formalism.InvariantFactorPaths.BranchingDimensions.weyl_dim_eq_gelfand_tsetlin Formalism.InvariantFactorPaths.BranchingDimensions.branchingDimensionFormula n mu h]

lemma qk_D_zero {n : ℕ} {v : Fin n → ℝ} {i j : Fin n} (hij : i < j) (h : v i = v j) : qk_D v = 0 := by
  unfold qk_D
  refine prod_eq_zero (mem_univ i) (prod_eq_zero (mem_Ioi.2 hij) ?_)
  rw [h, sub_self]

def qk_add {n : ℕ} (mu : Fin n → ℤ) (s : Finset (Fin n)) : Fin n → ℤ := fun a => if a ∈ s then mu a + 1 else mu a

lemma qk_v_add {n : ℕ} (mu : Fin n → ℤ) (s : Finset (Fin n)) :
    qk_v (qk_add mu s) = s.piecewise (fun i => qk_v mu i - 1) (qk_v mu) := by
  funext i
  unfold qk_v qk_add
  by_cases hi : i ∈ s
  · simp only [hi, if_true, piecewise_eq_of_mem]
    push_cast
    ring
  · simp only [hi, if_false, piecewise_eq_of_notMem, not_false_eq_true]

lemma qk_D_nondom {n : ℕ} {mu : Fin n → ℤ} (hmu : Dominant mu) (s : Finset (Fin n))
    (h : ¬ Dominant (qk_add mu s)) : qk_D (qk_v (qk_add mu s)) = 0 := by
  have h1 : ∃ a : Fin n, ∃ ha : a.1 + 1 < n, qk_add mu s a < qk_add mu s ⟨a.1 + 1, ha⟩ := by
    by_contra hc
    push Not at hc
    exact h (qk_antitone_of_step hc)
  obtain ⟨a, ha, hlt⟩ := h1
  have hle : mu ⟨a.1 + 1, ha⟩ ≤ mu a := hmu (by rw [Fin.le_def]; simp)
  have h2 : qk_add mu s ⟨a.1 + 1, ha⟩ = qk_add mu s a + 1 := by
    unfold qk_add at hlt ⊢
    split_ifs at hlt ⊢ <;> omega
  refine qk_D_zero (i := a) (j := ⟨a.1 + 1, ha⟩) (by rw [Fin.lt_def]; simp) ?_
  unfold qk_v
  rw [h2]
  push_cast
  ring

lemma qk_mem_strVert {n : ℕ} {mu nu : Fin n → ℤ} {b : ℕ} : nu ∈ strVert mu b ↔
    (∀ a, mu a ≤ nu a ∧ nu a ≤ mu a + 1) ∧ Dominant nu ∧ ∑ a, (nu a - mu a) = (b : ℤ) := by
  unfold strVert
  simp only [mem_filter, Fintype.mem_piFinset, mem_Icc]

lemma qk_add_sum {n : ℕ} (mu : Fin n → ℤ) (s : Finset (Fin n)) : ∑ a, (qk_add mu s a - mu a) = (s.card : ℤ) := by
  have : ∀ a, qk_add mu s a - mu a = if a ∈ s then 1 else 0 := by
    intro a
    unfold qk_add
    split_ifs <;> ring
  simp only [this]
  simp

lemma qk_add_sel {n : ℕ} {mu nu : Fin n → ℤ} (h : ∀ a, mu a ≤ nu a ∧ nu a ≤ mu a + 1) :
    qk_add mu (univ.filter fun a => nu a = mu a + 1) = nu := by
  funext a
  unfold qk_add
  simp only [mem_filter, mem_univ, true_and]
  split_ifs with h1
  · exact h1.symm
  · have := h a
    omega

lemma qk_sel_add {n : ℕ} (mu : Fin n → ℤ) (s : Finset (Fin n)) :
    (univ.filter fun a => qk_add mu s a = mu a + 1) = s := by
  ext a
  by_cases ha : a ∈ s <;> simp [qk_add, ha]

theorem exterior_power_count_holds : CntLam := by
  classical
  intro n _ mu b hmu
  have hcard : Fintype.card (LamIdx n b) = n.choose b := by
    rw [Fintype.card_finset_len, Fintype.card_fin]
  rw [hcard]
  have hW := qk_W_ne n
  have key : ((dMu mu * n.choose b : ℕ) : ℝ) * vandermondeDenominator n = ((∑ nu ∈ strVert mu b, dMu nu : ℕ) : ℝ) * vandermondeDenominator n := by
    push_cast
    rw [sum_mul]
    have e1 : ∑ nu ∈ strVert mu b, (dMu nu : ℝ) * vandermondeDenominator n = ∑ nu ∈ strVert mu b, qk_D (qk_v nu) := by
      refine sum_congr rfl fun nu hnu => ?_
      have hd := (qk_mem_strVert.1 hnu).2.1
      rw [qk_D_dom hd, qk_dMu_eq_dGT n nu hd]
    have e2 : ∑ s ∈ (powersetCard b (univ : Finset (Fin n))).filter (fun s => Dominant (qk_add mu s)),
        qk_D (qk_v (qk_add mu s)) = ∑ nu ∈ strVert mu b, qk_D (qk_v nu) := by
      refine sum_nbij' (qk_add mu) (fun nu => univ.filter fun a => nu a = mu a + 1) ?_ ?_ ?_ ?_ ?_
      · intro s hs
        rw [mem_filter, mem_powersetCard] at hs
        refine qk_mem_strVert.2 ⟨fun a => ?_, hs.2, ?_⟩
        · unfold qk_add
          split_ifs <;> omega
        · rw [qk_add_sum, hs.1.2]
      · intro nu hnu
        have h := qk_mem_strVert.1 hnu
        rw [mem_filter, mem_powersetCard, qk_add_sel h.1]
        refine ⟨⟨subset_univ _, ?_⟩, h.2.1⟩
        have h3 := qk_add_sum mu (univ.filter fun a => nu a = mu a + 1)
        rw [qk_add_sel h.1, h.2.2] at h3
        exact_mod_cast h3.symm
      · intro s _
        exact qk_sel_add mu s
      · intro nu hnu
        exact qk_add_sel (qk_mem_strVert.1 hnu).1
      · intro s _
        rfl
    have e3 : ∑ s ∈ (powersetCard b (univ : Finset (Fin n))).filter (fun s => Dominant (qk_add mu s)),
        qk_D (qk_v (qk_add mu s)) = ∑ s ∈ powersetCard b (univ : Finset (Fin n)), qk_D (qk_v (qk_add mu s)) := by
      refine sum_filter_of_ne fun s _ hne => ?_
      by_contra hc
      exact hne (qk_D_nondom hmu s hc)
    rw [e1, ← e2, e3]
    simp only [qk_v_add]
    rw [qk_D_shift, qk_D_dom hmu, qk_dMu_eq_dGT n mu hmu]
    ring
  exact_mod_cast mul_right_cancel₀ hW key

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

-- bundled from Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.SymDStrip
section
noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ} [NeZero n]

open Classical in

def qs_psD (b : ℕ) (mu nu : Fin n → ℤ) : Matrix (TIdx mu × SymIdx n b) (TIdx nu) ℤ := fun y K =>
  ∑ m : ↥(qs_D nu mu) → Fin n,
    if (∀ c : ↥(qs_D nu mu), m c ∉ qs_ext nu K c.1) ∧ qs_ext mu y.1 = qs_add (qs_D nu mu) (qs_ext nu K) m then
      (if ∀ x, qs_cnt m x = (y.2.1 x : ℕ) then
        ∏ c : ↥(qs_D nu mu), qs_sg (qs_ext nu K c.1) (m c) else 0)
    else 0

open Classical in

def qs_midD (b : ℕ) (mu nu : Fin n → ℤ) (J : TIdx mu) (α : SymIdx n b) (K : TIdx nu) : GLCoord ℤ n :=
  ∑ a : ↥(qs_D nu mu) → Fin n, if (∀ x, qs_cnt a x = (α.1 x : ℕ)) then
    ((detU n ^ nu (lastIdx n) : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) *
      (if ∀ c : ↥(qs_D nu mu), a c ∈ qs_ext mu J c.1 then
        (∏ c : ↥(qs_D nu mu), ((qs_sg ((qs_ext mu J c.1).erase (a c)) (a c) : ℤ) : GLCoord ℤ n)) *
          ∏ c ∈ Finset.Ioc (nu (lastIdx n)) (mu 0),
            qs_mn (qs_gC n) (qs_rem (qs_D nu mu) (qs_ext mu J) a c) (qs_ext nu K c) else 0)
  else 0

open Classical in
theorem qs_psD_left (b : ℕ) {mu nu : Fin n → ℤ} (hmu : Dominant mu) (hnu : Dominant nu) (hs : HStrip nu mu b)
    (J : TIdx mu) (α : SymIdx n b) (K : TIdx nu) :
    ∑ y : TIdx mu × SymIdx n b, TMat mu J y.1 * SymDMat n b α y.2 * ((qs_psD b mu nu y K : ℤ) : GLCoord ℤ n) =
      qs_midD b mu nu J α K := by
  have hT : ∀ I, TMat mu J I =
      qs_TM (nu (lastIdx n)) (Finset.Ioc (nu (lastIdx n)) (mu 0)) (qs_ext mu J) (qs_ext mu I) :=
    fun I => qs_TMat_eq hmu _ _ (hs.1 _) le_rfl J I
  have hm : ∀ m : ↥(qs_D nu mu) → Fin n,
      ∑ y : TIdx mu × SymIdx n b, TMat mu J y.1 * SymDMat n b α y.2 *
        (((if (∀ c : ↥(qs_D nu mu), m c ∉ qs_ext nu K c.1) ∧
            qs_ext mu y.1 = qs_add (qs_D nu mu) (qs_ext nu K) m then
          (if ∀ x, qs_cnt m x = (y.2.1 x : ℕ) then
            ∏ c : ↥(qs_D nu mu), qs_sg (qs_ext nu K c.1) (m c) else 0) else 0 : ℤ)) : GLCoord ℤ n) =
      ∑ a : ↥(qs_D nu mu) → Fin n, if (∀ x, qs_cnt a x = (α.1 x : ℕ)) then
        ((detU n ^ nu (lastIdx n) : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) *
          (if ∀ c : ↥(qs_D nu mu), m c ∉ qs_ext nu K c.1 then
            (∏ c : ↥(qs_D nu mu), ((qs_sg (qs_ext nu K c.1) (m c) : ℤ) : GLCoord ℤ n)) *
              (∏ c ∈ Finset.Ioc (nu (lastIdx n)) (mu 0),
                qs_mn (qs_gC n) (qs_ext mu J c) (qs_add (qs_D nu mu) (qs_ext nu K) m c)) *
              ∏ c : ↥(qs_D nu mu), qs_gI n (m c) (a c) else 0) else 0 := by
    intro m
    rw [Fintype.sum_prod_type]
    obtain ⟨f, hf⟩ : ∃ f : (ℤ → Finset (Fin n)) → GLCoord ℤ n, f =
        fun E => qs_TM (nu (lastIdx n)) (Finset.Ioc (nu (lastIdx n)) (mu 0)) (qs_ext mu J) E *
          ∑ β : SymIdx n b, qs_SM (qs_gI n).transpose b α β *
            (if ∀ x, qs_cnt m x = (β.1 x : ℕ) then
              (∏ c : ↥(qs_D nu mu), ((qs_sg (qs_ext nu K c.1) (m c) : ℤ) : GLCoord ℤ n)) else 0) :=
      ⟨_, rfl⟩
    have h1 : ∀ I : TIdx mu, (∑ β : SymIdx n b, TMat mu J I * SymDMat n b α β *
        (((if (∀ c : ↥(qs_D nu mu), m c ∉ qs_ext nu K c.1) ∧
            qs_ext mu I = qs_add (qs_D nu mu) (qs_ext nu K) m then
          (if ∀ x, qs_cnt m x = (β.1 x : ℕ) then
            ∏ c : ↥(qs_D nu mu), qs_sg (qs_ext nu K c.1) (m c) else 0) else 0 : ℤ)) : GLCoord ℤ n)) =
        if (∀ c : ↥(qs_D nu mu), m c ∉ qs_ext nu K c.1) ∧ qs_ext mu I = qs_add (qs_D nu mu) (qs_ext nu K) m then
          f (qs_ext mu I)
        else 0 := by
      intro I
      rw [hf]
      split_ifs with h
      · simp only [hT, Finset.mul_sum, qs_SymDMat_eq]
        refine Finset.sum_congr rfl fun β _ => ?_
        split_ifs
        · push_cast; ring
        · simp
      · simp
    rw [Finset.sum_congr rfl (fun I _ => h1 I),
      qs_collapse hmu _ _ (fun h => qs_add_card hnu hmu hs _ (qs_ext_card hnu K) m h), hf]
    split_ifs with h
    · simp only [qs_sum_sym (qs_gI n).transpose (qs_card_D hnu hmu hs) m α]
      rw [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      split_ifs
      · rw [qs_TM]; simp only [Matrix.transpose_apply]; ring
      · simp
    · simp
  have h2 : ∀ y : TIdx mu × SymIdx n b,
      TMat mu J y.1 * SymDMat n b α y.2 * ((qs_psD b mu nu y K : ℤ) : GLCoord ℤ n) =
      ∑ m : ↥(qs_D nu mu) → Fin n, TMat mu J y.1 * SymDMat n b α y.2 *
        (((if (∀ c : ↥(qs_D nu mu), m c ∉ qs_ext nu K c.1) ∧
            qs_ext mu y.1 = qs_add (qs_D nu mu) (qs_ext nu K) m then
          (if ∀ x, qs_cnt m x = (y.2.1 x : ℕ) then
            ∏ c : ↥(qs_D nu mu), qs_sg (qs_ext nu K c.1) (m c) else 0) else 0 : ℤ)) : GLCoord ℤ n) := by
    intro y
    rw [qs_psD, Int.cast_sum, Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun y _ => h2 y), Finset.sum_comm, Finset.sum_congr rfl (fun m _ => hm m),
    Finset.sum_comm, qs_midD]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : ∀ x, qs_cnt a x = (α.1 x : ℕ)
  · simp only [if_pos h]
    rw [← Finset.mul_sum, qs_core_inv (qs_gC n) (qs_gI n) (qs_gC_mul_gI n) _ _ (qs_D_sub nu mu)]
  · simp only [if_neg h, Finset.sum_const_zero]

open Classical in
theorem qs_psD_right (b : ℕ) {mu nu : Fin n → ℤ} (hmu : Dominant mu) (hnu : Dominant nu) (hs : HStrip nu mu b)
    (J : TIdx mu) (α : SymIdx n b) (K : TIdx nu) :
    ∑ K' : TIdx nu, ((qs_psD b mu nu (J, α) K' : ℤ) : GLCoord ℤ n) * TMat nu K' K = qs_midD b mu nu J α K := by
  have hT : ∀ K', TMat nu K' K =
      qs_TM (nu (lastIdx n)) (Finset.Ioc (nu (lastIdx n)) (mu 0)) (qs_ext nu K') (qs_ext nu K) :=
    fun K' => qs_TMat_eq hnu _ _ le_rfl (hs.1 0) K' K
  obtain ⟨f, hf⟩ : ∃ f : (↥(qs_D nu mu) → Fin n) → (ℤ → Finset (Fin n)) → GLCoord ℤ n, f =
      fun a E => (if ∀ x, qs_cnt a x = (α.1 x : ℕ) then
            (∏ c : ↥(qs_D nu mu), ((qs_sg (E c.1) (a c) : ℤ) : GLCoord ℤ n)) *
              qs_TM (nu (lastIdx n)) (Finset.Ioc (nu (lastIdx n)) (mu 0)) E (qs_ext nu K) else 0) := ⟨_, rfl⟩
  have h2 : ∀ K' : TIdx nu, ((qs_psD b mu nu (J, α) K' : ℤ) : GLCoord ℤ n) * TMat nu K' K =
      ∑ a : ↥(qs_D nu mu) → Fin n,
        if (∀ c : ↥(qs_D nu mu), a c ∈ qs_ext mu J c.1) ∧ qs_ext nu K' = qs_rem (qs_D nu mu) (qs_ext mu J) a then
          f a (qs_ext nu K')
        else 0 := by
    intro K'
    rw [qs_psD, Int.cast_sum, Finset.sum_mul, hf]
    refine Finset.sum_congr rfl fun a _ => ?_
    have := qs_rem_iff_add (qs_D nu mu) (qs_ext nu K') (qs_ext mu J) a
    by_cases h : (∀ c : ↥(qs_D nu mu), a c ∉ qs_ext nu K' c.1) ∧
        qs_ext mu J = qs_add (qs_D nu mu) (qs_ext nu K') a
    · rw [if_pos h, if_pos (this.2 h)]
      simp only [hT]
      split_ifs
      · push_cast; ring
      · simp
    · rw [if_neg h, if_neg (fun h' => h (this.1 h'))]; simp
  rw [Finset.sum_congr rfl (fun K' _ => h2 K'), Finset.sum_comm, qs_midD]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [qs_collapse hnu _ _ (fun h => qs_rem_card hnu hmu hs _ (qs_ext_card hmu J) a h), hf]
  by_cases h : ∀ c : ↥(qs_D nu mu), a c ∈ qs_ext mu J c.1
  · rw [if_pos h, if_pos h]
    simp only [qs_rem_mem]
    split_ifs
    · rw [qs_TM]; ring
    · rfl
  · rw [if_neg h, if_neg h]; simp

theorem qs_psD_lead (b : ℕ) {mu nu : Fin n → ℤ} (hmu : Dominant mu) (hnu : Dominant nu) (hs : HStrip nu mu b) :
    qs_psD b mu nu (canT mu, qs_mon (qs_card_D hnu hmu hs) (qs_mc nu mu)) (canT nu) = 1 := by
  have hiff : ∀ m : ↥(qs_D nu mu) → Fin n, ((∀ c : ↥(qs_D nu mu), m c ∉ qs_ext nu (canT nu) c.1) ∧
      qs_ext mu (canT mu) = qs_add (qs_D nu mu) (qs_ext nu (canT nu)) m) ↔ m = qs_mc nu mu := fun m =>
    (qs_rem_iff_add _ _ _ m).symm.trans (qs_can_iff hnu hmu hs m)
  rw [qs_psD, Finset.sum_eq_single (qs_mc nu mu)]
  · rw [if_pos ((hiff _).2 rfl), if_pos]
    swap
    · intro x; rfl
    refine Finset.prod_eq_one fun c _ => ?_
    rw [qs_ext_can hnu]
    exact qs_sg_ini _ _
  · intro m _ hm
    rw [if_neg (fun h => hm ((hiff _).1 h))]
  · intro h; exact absurd (Finset.mem_univ _) h

omit [NeZero n] in
lemma qs_gI_torus : (qs_gI n).transpose.map (evGL (torusPt n)) =
    Matrix.diagonal fun a => AddMonoidAlgebra.single (Pi.single a (-1 : ℤ)) (1 : ℤ) := by
  have h1 : (qs_gC n).map (evGL (torusPt n)) * (qs_gI n).map (evGL (torusPt n)) = 1 := by
    rw [← Matrix.map_mul, qs_gC_mul_gI]; simp
  have h2 : (qs_gC n).map (evGL (torusPt n)) = (torusPt n).val := qs_gC_torus
  have h3 : (qs_gI n).map (evGL (torusPt n)) = (torusPt n).inv := by
    calc (qs_gI n).map (evGL (torusPt n)) = ((torusPt n).inv * (torusPt n).val) * (qs_gI n).map (evGL (torusPt n)) := by
          rw [(torusPt n).inv_val, Matrix.one_mul]
      _ = (torusPt n).inv := by rw [Matrix.mul_assoc, ← h2, h1, Matrix.mul_one]
  rw [Matrix.transpose_map, h3]
  exact Matrix.diagonal_transpose _

omit [NeZero n] in
open Classical in
lemma qs_mem_strDown {mu nu : Fin n → ℤ} {b : ℕ} (h : nu ∈ strDown mu b) : HStrip nu mu b :=
  (Finset.mem_filter.1 h).2

theorem symDStrip_of : CntSymD → SymDStrip := by
  intro hc n _ b
  refine ⟨fun α x => -((α.1 x : ℕ) : ℤ), qs_psD b, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro α β h
    exact Subtype.ext (funext fun x => Fin.ext (by
      have := congrFun h x; simp only [neg_inj] at this; exact_mod_cast this))
  · intro k l
    rw [qs_SymDMat_eq, qs_SM_map, qs_gI_torus, qs_SM_diag]
    split_ifs with h
    · subst h
      rw [qs_prod_torus]; simp
    · rfl
  · intro mu hmu nu hnu
    exact qs_dom_down hmu (qs_mem_strDown hnu)
  · intro mu hmu nu hnu
    have hs := qs_mem_strDown hnu
    have hnu' := qs_dom_down hmu hs
    ext ⟨J, α⟩ K
    exact (qs_psD_left b hmu hnu' hs J α K).trans (qs_psD_right b hmu hnu' hs J α K).symm
  · intro mu hmu nu hnu
    have hs := qs_mem_strDown hnu
    have hnu' := qs_dom_down hmu hs
    refine ⟨qs_mon (qs_card_D hnu' hmu hs) (qs_mc nu mu), ?_, Or.inl (qs_psD_lead b hmu hnu' hs)⟩
    funext x
    have := qs_cnt_mc hnu' hmu hs x
    show -((qs_cnt (qs_mc nu mu) x : ℕ) : ℤ) = nu x - mu x
    omega
  · intro mu hmu
    exact hc n mu b hmu

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

