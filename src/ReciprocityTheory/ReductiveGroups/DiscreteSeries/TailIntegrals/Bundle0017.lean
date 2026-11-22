import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.Bundle0016
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.Bundle0013
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.HpkNegMp
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.Bundle0011

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.BStepSuccOf
section
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 BL

theorem bStepBase_of (hB2 : InductiveHeisenbergInputs) : BStepBase := by
  obtain ⟨-, -, -, -, hNB, -⟩ := hB2
  intro k _ δ _
  refine ⟨1, one_pos, fun s _ z _ _ μN hμ => ?_⟩
  set o : Mt k 0 := ((1 : Mat k 0) : Mt k 0) with ho
  have hc : μN ({o}ᶜ : Set (Mt k 0)) = 0 := by
    have h := hμ.conc; rw [hNB k] at h; exact h
  have hr : μN.restrict {o} = μN :=
    Measure.restrict_eq_self_of_ae_mem (ae_iff.2 (by simpa [Set.compl_def] using hc))
  unfold IInt
  rw [← hr, lintegral_singleton]
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
    (hμ.finite_compact _ isCompact_singleton)

theorem bStepSucc_of (hB2 : InductiveHeisenbergInputs) (hIW : IW) (hF : FormulaF) (hOS : OS) : BStepSucc := by
  obtain ⟨-, -, -, hNR, -, hHC, -, -, -, -, -, hHH, -, -, -, -, hHU, -, -, -, hCN, -, -, -, hHN, -, hHA⟩ := hB2
  intro k r r' hr hk δ hδ hδ2 hB'
  subst hr
  obtain ⟨e', he', hB'⟩ := hB'
  obtain ⟨γ, hγd⟩ : ∃ γ : ℝ, γ = min (δ / 8) (e' / 2) := ⟨_, rfl⟩
  have hγ : 0 < γ := by rw [hγd]; exact lt_min (by positivity) (by positivity)
  have hγ8 : γ ≤ δ / 8 := by rw [hγd]; exact min_le_left _ _
  have hγe : γ ≤ e' / 2 := by rw [hγd]; exact min_le_right _ _
  have hD : (0 : ℝ) < 4 * (1 + r') + 4 := by positivity
  refine ⟨min (e' / 2) (γ / (4 * (1 + r') + 4)), lt_min (by positivity) (div_pos hγ hD), ?_⟩
  intro s hs z hzW hzT μN hμN
  have he0 : ∀ l, 0 < s0 k (1 + r') l - s l := fun l => (hs l).1
  have heS : ∀ l, s0 k (1 + r') l - s l ≤ γ / (4 * (1 + r') + 4) := fun l => le_trans (hs l).2 (min_le_right _ _)
  have heS' : ∀ l, s0 k (1 + r') l - s l ≤ e' / 2 := fun l => le_trans (hs l).2 (min_le_left _ _)
  have hs0 : ∀ l, s0N (1 + r') (k - 1) l = s0 k (1 + r') l := by
    intro l; unfold s0N s0; split_ifs
    · rfl
    · push_cast [Nat.cast_sub hk]; ring
  have hsum : (s0 k (1 + r') 0 - s 0) + 2 * ∑ i : Fin (1 + r'), (s0 k (1 + r') i.succ - s i.succ) < γ / 2 := by
    have h1 : ∑ i : Fin (1 + r'), (s0 k (1 + r') i.succ - s i.succ) ≤ (1 + r') * (γ / (4 * (1 + r') + 4)) := by
      calc _ ≤ ∑ _i : Fin (1 + r'), γ / (4 * (1 + r') + 4) := Finset.sum_le_sum fun i _ => heS _
        _ = _ := by simp [Finset.sum_const, Finset.card_univ]
    have key : (3 + 2 * (r' : ℝ)) * (γ / (4 * (1 + r') + 4)) < γ / 2 := by
      rw [mul_div_assoc', div_lt_div_iff₀ hD (by norm_num)]; nlinarith
    linarith [heS 0]
  obtain ⟨C, hC⟩ := os_q hOS (1 + r') r' (k - 1) (by omega) δ γ (fun l => s0 k (1 + r') l - s l) hδ hδ2 hγ hγ8 he0 hsum
  have hC' : ∀ (η η' : Fin (1 + r') → ℂ) (ζ : Fin (k - 1) → ℂ) (c₀ : ℝ), η' ⟨0, by omega⟩ ≠ 0 →
      ∫⁻ x, GI s δ η η' ζ c₀ x ≤ ENNReal.ofReal (C * ‖η' ⟨0, by omega⟩‖ ^ (-γ) * (1 + |c₀|) ^ (-δ / 4)) := by
    intro η η' ζ c₀ h
    have hse : s = fun l => s0N (1 + r') (k - 1) l - (s0 k (1 + r') l - s l) := by funext l; rw [hs0]; ring
    rw [hse]; exact hC η η' ζ c₀ h
  obtain ⟨z1, hz1W, rfl⟩ : ∃ z1, inWb k r' z1 ∧ z = liftVec k 1 r' z1 := ⟨_, shifted_mem_weightSpace z hzW, z_lift z hzW⟩
  have hz1T : 0 < Tz k r' z1 := by rw [← tz_lift]; exact hzT
  have hcz := cz_ne hk z1 hz1T
  have hsP : ∀ a : Fin (r' + 1), 0 < s0 k r' a - (s (su a) - if a = 0 then γ else 0) ∧
      s0 k r' a - (s (su a) - if a = 0 then γ else 0) ≤ e' := by
    intro a
    have hs0a : s0 k r' a = s0 k (1 + r') (su a) := by
      unfold s0
      by_cases h : a.val < r'
      · rw [if_pos h, if_pos (show (su a).val < 1 + r' by rw [su_val]; omega)]
      · rw [if_neg h, if_neg (show ¬ (su a).val < 1 + r' by rw [su_val]; omega)]
    rw [hs0a]
    have h1 := he0 (su a); have h2 := heS' (su a)
    split_ifs <;> constructor <;> linarith
  obtain ⟨μ', hμ'⟩ := hHN k r'
  have hfin := hB' _ hsP z1 hz1W hz1T μ' hμ'
  obtain ⟨c, hc⟩ := hHU k (1 + r') (Nset k (1 + r')) _ μN (hCN k (1 + r')) (hNR k r' μ' hμ') hμN.conc hμN.left
    hμN.finite_compact
  rw [hc]; unfold IInt; rw [lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
  refine ENNReal.mul_lt_top ENNReal.coe_lt_top ?_
  have : IsFiniteMeasureOnCompacts μ' := ⟨fun ⦃K⦄ hK => hμ'.finite_compact K hK⟩
  have : IsFiniteMeasureOnCompacts (μHeis k r') := ⟨fun ⦃K⦄ hK => (hHH k r').finite_compact K hK⟩
  set F : Mt k (1 + r') → ℝ≥0∞ := fun n => ENNReal.ofReal (xiR k (1 + r') s (Matrix.of n)) *
    ENNReal.ofReal ((1 + |lam k (1 + r') (liftVec k 1 r' z1) (Matrix.of n)|) ^ (-δ)) with hFd
  have hsw : (μHeis k r').prod (μ'.map (levM k r')) = ((μ'.map (levM k r')).prod (μHeis k r')).map Prod.swap :=
    (Measure.prod_swap).symm
  have hae : ∀ᵐ m ∂μ', m ∈ Nset k r' := ae_iff.2 hμ'.conc
  have hpt : ∀ m ∈ Nset k r', ∫⁻ h, F (mulM (h, levM k r' m)) ∂(μHeis k r') ≤
      ENNReal.ofReal (C * ‖herm (Hpk k r') (phiV k r' ⟨0, by omega⟩) (fvec k r' z1 ⟨0, by omega⟩)‖ ^ (-γ)) *
        (ENNReal.ofReal (xiR k r' (fun a => s (su a) - if a = 0 then γ else 0) (Matrix.of m)) *
          ENNReal.ofReal ((1 + |lam k r' z1 (Matrix.of m)|) ^ (-(δ / 4)))) := by
    intro m hm
    calc _ ≤ ∫⁻ X, F (mulM (heis0 k r' X, levM k r' m)) ∂volume := by unfold μHeis; exact lintegral_map_le _ _
      _ ≤ _ := by rw [hFd]; exact inner_bound hIW hF hHC hHA hk s δ γ C z1 hC' hcz (Matrix.of m) hm.1
  calc ∫⁻ n, F n ∂(((μHeis k r').prod (μ'.map (levM k r'))).map mulM)
      ≤ ∫⁻ q, F (mulM q) ∂((μHeis k r').prod (μ'.map (levM k r'))) := lintegral_map_le _ _
    _ = ∫⁻ q, F (mulM q) ∂(((μ'.map (levM k r')).prod (μHeis k r')).map Prod.swap) := by rw [hsw]
    _ ≤ ∫⁻ q, F (mulM q.swap) ∂((μ'.map (levM k r')).prod (μHeis k r')) := lintegral_map_le _ _
    _ ≤ ∫⁻ n', ∫⁻ h, F (mulM (h, n')) ∂(μHeis k r') ∂(μ'.map (levM k r')) := lintegral_prod_le _
    _ ≤ ∫⁻ m, ∫⁻ h, F (mulM (h, levM k r' m)) ∂(μHeis k r') ∂μ' := lintegral_map_le _ _
    _ ≤ ∫⁻ m, ENNReal.ofReal (C * ‖herm (Hpk k r') (phiV k r' ⟨0, by omega⟩) (fvec k r' z1 ⟨0, by omega⟩)‖ ^ (-γ)) *
          (ENNReal.ofReal (xiR k r' (fun a => s (su a) - if a = 0 then γ else 0) (Matrix.of m)) *
            ENNReal.ofReal ((1 + |lam k r' z1 (Matrix.of m)|) ^ (-(δ / 4)))) ∂μ' := lintegral_mono_ae (hae.mono hpt)
    _ = ENNReal.ofReal (C * ‖herm (Hpk k r') (phiV k r' ⟨0, by omega⟩) (fvec k r' z1 ⟨0, by omega⟩)‖ ^ (-γ)) *
          ∫⁻ m, ENNReal.ofReal (xiR k r' (fun a => s (su a) - if a = 0 then γ else 0) (Matrix.of m)) *
            ENNReal.ofReal ((1 + |lam k r' z1 (Matrix.of m)|) ^ (-(δ / 4))) ∂μ' :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.HeisenbergFactsOfInductiveInput
section
noncomputable section

open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem heisenbergFacts_of_inductiveInput (h : InductiveHeisenbergInputs) : OneStepInt ∧ OneStepCoord ∧ HeisConjLev ∧ HeisInv ∧ HeisMem ∧ HeisHaar ∧
    HaarGExists ∧ HeisAct ∧ GNLower ∧ HeisClosed ∧ HeisConjLevMeas := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22,
    h23, h24, h25, h26, h27⟩ := h
  exact ⟨h1, h2, h6, h8, h10, h12, h26, h27, h16, h11, h7⟩

section cont
variable (k r' : ℕ)

theorem lift_cont : Continuous (liftVec k 1 r') := by
  refine continuous_pi fun p => ?_
  unfold liftVec
  by_cases hp : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1
  · simp only [dif_pos hp]; exact continuous_apply _
  · simp only [dif_neg hp]; exact continuous_const

theorem heisenberg_map_continuous : Continuous (heis0 k r') := by
  have h1 : Continuous fun x : HPar k r' => liftVec k 1 r' x.1 := (lift_cont k r').comp continuous_fst
  unfold heis0 heisG hb herm
  fun_prop

theorem lev_cont : Continuous (fun g : Mat k r' => ιLev k 1 r' g) := by
  refine continuous_matrix fun p q => ?_
  unfold ιLev
  by_cases hp : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1
  · by_cases hq : 1 ≤ q.val ∧ q.val < 2 * r' + k + 1 + 1
    · simp only [dif_pos hp, dif_pos hq]; exact continuous_id.matrix_elem _ _
    · simp only [dif_pos hp, dif_neg hq]; exact continuous_const
  · simp only [dif_neg hp]; exact continuous_const

theorem Dl_cont (r : ℕ) (l : Fin (r + 1)) : Continuous (fun g : Mt k r => Dl k r l (Matrix.of g)) := by
  unfold Dl herm
  fun_prop

theorem FsE_meas (r : ℕ) (s : Fin (r + 1) → ℝ) : Measurable (fun g : Mt k r => FsE k r s (Matrix.of g)) := by
  unfold FsE
  exact Finset.measurable_prod _ fun l _ =>
    ((Dl_cont k r l).measurable.nnnorm.coe_nnreal_ennreal).pow_const _

theorem EInt_meas (A : ℝ) (c : ℂ) : Measurable (fun g : Mt k r' => EInt k r' A c (Matrix.of g)) := by
  unfold EInt
  have h1 := heisenberg_map_continuous k r'
  have h2 := lev_cont k r'
  have h3 := gN_cont k (1 + r')
  refine Measurable.lintegral_prod_right'
    (f := fun p : Mt k r' × HPar k r' =>
      ENNReal.ofReal (gN (w0 k r' c * ιLev k 1 r' (Matrix.of p.1) * heis0 k r' p.2) ^ (-A))) ?_
  exact ((by fun_prop : Continuous fun p : Mt k r' × HPar k r' =>
    gN (w0 k r' c * ιLev k 1 r' (Matrix.of p.1) * heis0 k r' p.2)).measurable.pow_const _).ennreal_ofReal

theorem heis_left (hHH : HeisHaar) (F : Mt k (1 + r') → ℝ≥0∞) (hF : Measurable F) (z : HPar k r') :
    ∫⁻ x, F (heis0 k r' z * heis0 k r' x) = ∫⁻ x, F (heis0 k r' x) := by
  have hc : @Continuous (HPar k r') (Mt k (1 + r')) _ _ (fun x => heis0 k r' x) := heisenberg_map_continuous k r'
  have hm : @Measurable (HPar k r') (Mt k (1 + r')) _ _ (fun x => heis0 k r' x) := hc.measurable
  have hl : Measurable (lmulM (heis0 k r' z) : Mt k (1 + r') → Mt k (1 + r')) :=
    (by unfold lmulM; fun_prop : Continuous (lmulM (heis0 k r' z) : Mt k (1 + r') → Mt k (1 + r'))).measurable
  calc ∫⁻ x, F (heis0 k r' z * heis0 k r' x) = ∫⁻ n, F (lmulM (heis0 k r' z) n) ∂(μHeis k r') := by
        rw [μHeis]; exact (lintegral_map (hF.comp hl) hm).symm
    _ = ∫⁻ n, F n ∂((μHeis k r').map (lmulM (heis0 k r' z))) := (lintegral_map hF hl).symm
    _ = ∫⁻ n, F n ∂(μHeis k r') := by rw [(hHH k r').left _ ⟨z, rfl⟩]
    _ = ∫⁻ x, F (heis0 k r' x) := by rw [μHeis]; exact lintegral_map hF hm

theorem EInt_K (A : ℝ) (c : ℂ) {κ : Mat k r'} (hκ : κ ∈ Kset k r') (g : Mat k r') :
    EInt k r' A c (κ * g) = EInt k r' A c g := by
  unfold EInt
  refine lintegral_congr fun x => ?_
  have e : w0 k r' c * ιLev k 1 r' (κ * g) * heis0 k r' x =
      ιLev k 1 r' κ * (w0 k r' c * ιLev k 1 r' g * heis0 k r' x) := by
    rw [lev_mul, ← Matrix.mul_assoc (w0 k r' c), rankOne_levi_comm]; simp only [Matrix.mul_assoc]
  rw [e, gN_unitary k (1 + r') (lev_K k r' hκ).2]

end cont

section inner
variable (k r' : ℕ)

def Dx (x : HPar k r') : ℝ := Real.sqrt (Ga k (1 + r') 0 (Yx k r' x))

def Psi (s : Fin (1 + r' + 1) → ℝ) (x : HPar k r') : ℝ :=
  ∏ l : Fin (r' + 1), (Ga k (1 + r') (sc r' l) (Yx k r' x) / Ga k (1 + r') 0 (Yx k r' x)) ^ (-s (sc r' l) / 2)

def Qf (A : ℝ) (s1 : Fin (r' + 1) → ℝ) (μ₁ : Measure (Mt k r')) (c : ℂ) : ℝ≥0∞ :=
  ∫⁻ g, EInt k r' A c (Matrix.of g) * FsE k r' s1 (Matrix.of g) ∂μ₁

theorem inner_eq (hB2 : InductiveHeisenbergInputs) (hIW : IW) (hT : TLeft) (hk : 1 ≤ k) (A : ℝ) (s : Fin (1 + r' + 1) → ℝ)
    (μ₁ : Measure (Mt k r')) (hμ₁ : IsHaarOn (GV k r') μ₁) (x : HPar k r') (c : ℂ) (hc : c ≠ 0) :
    ∫⁻ g, (∫⁻ x', ENNReal.ofReal (gN (oneStep k r' x c (Matrix.of g) x') ^ (-A))) *
        FsE k r' (fun l => s (sc r' l)) (Matrix.of g) ∂μ₁ =
      ENNReal.ofReal (Psi k r' s x) * Qf k r' A (fun l => s (sc r' l)) μ₁ (c * (Dx k r' x : ℂ)) := by
  obtain ⟨-, -, hHCL, -, -, hHH, -, -, -, -, -⟩ := heisenbergFacts_of_inductiveInput hB2
  obtain ⟨κ, hκ, m, hm, z, hdec, hga⟩ := heisenberg_rankOne_decomposition hB2 hIW k r' hk x c hc
  have hG0 := (yx_ga hB2 hIW k r' hk x).1
  have hdec' : (heis0 k r' x)⁻¹ * w0 k r' c =
      κ * w0 k r' (c * (Dx k r' x : ℂ)) * ιLev k 1 r' m * heis0 k r' z := hdec
  have hpt : ∀ g : Mt k r', Matrix.of g ∈ GV k r' →
      ∫⁻ x', ENNReal.ofReal (gN (oneStep k r' x c (Matrix.of g) x') ^ (-A)) =
        EInt k r' A (c * (Dx k r' x : ℂ)) (m * Matrix.of g) := by
    intro g hg
    obtain ⟨z2, hz2⟩ : ∃ z2 : HPar k r', z2 = ((Matrix.of g)⁻¹ *ᵥ z.1, z.2) := ⟨_, rfl⟩
    have hcomm : heis0 k r' z * ιLev k 1 r' (Matrix.of g) = ιLev k 1 r' (Matrix.of g) * heis0 k r' z2 := by
      have h1 := hHCL k r' (Matrix.of g) hg z2
      have h2 : ((Matrix.of g *ᵥ z2.1, z2.2) : HPar k r') = z := by
        rw [hz2]; dsimp only; rw [mulVec_mulVec, UH_mul_inv k r' hg, one_mulVec]
      rw [h2] at h1
      rw [← h1, Matrix.mul_assoc, UH_inv_mul k (1 + r') (lev_mem k r' hg), Matrix.mul_one]
    have hmat : ∀ x', oneStep k r' x c (Matrix.of g) x' =
        κ * (w0 k r' (c * (Dx k r' x : ℂ)) * ιLev k 1 r' (m * Matrix.of g) * (heis0 k r' z2 * heis0 k r' x')) := by
      intro x'
      unfold oneStep
      rw [hdec', Matrix.mul_assoc (κ * w0 k r' (c * (Dx k r' x : ℂ)) * ιLev k 1 r' m) (heis0 k r' z)
        (ιLev k 1 r' (Matrix.of g)), hcomm, lev_mul]
      simp only [Matrix.mul_assoc]
    simp only [hmat, gN_unitary k (1 + r') hκ.2]
    have h3 := gN_cont k (1 + r')
    have hF : Measurable fun n : Mt k (1 + r') =>
        ENNReal.ofReal (gN (w0 k r' (c * (Dx k r' x : ℂ)) * ιLev k 1 r' (m * Matrix.of g) * Matrix.of n) ^ (-A)) :=
      ((by fun_prop : Continuous fun n : Mt k (1 + r') =>
        gN (w0 k r' (c * (Dx k r' x : ℂ)) * ιLev k 1 r' (m * Matrix.of g) * Matrix.of n)).measurable.pow_const
          _).ennreal_ofReal
    exact heis_left k r' hHH _ hF z2
  have hconc : ∀ᵐ g ∂μ₁, Matrix.of g ∈ GV k r' := by
    rw [ae_iff]; exact hμ₁.conc
  have hl : Measurable (lmulM m : Mt k r' → Mt k r') :=
    (by unfold lmulM; fun_prop : Continuous (lmulM m : Mt k r' → Mt k r')).measurable
  have hli : Measurable (lmulM m⁻¹ : Mt k r' → Mt k r') :=
    (by unfold lmulM; fun_prop : Continuous (lmulM m⁻¹ : Mt k r' → Mt k r')).measurable
  have hG : Measurable (fun g : Mt k r' => EInt k r' A (c * (Dx k r' x : ℂ)) (Matrix.of g) *
      FsE k r' (fun l => s (sc r' l)) (m⁻¹ * Matrix.of g)) :=
    (EInt_meas k r' A _).mul ((FsE_meas k r' (fun l => s (sc r' l))).comp hli)
  have e : ∀ g : Mt k r', m⁻¹ * (m * Matrix.of g) = Matrix.of g := fun g => by
    rw [← Matrix.mul_assoc, UH_inv_mul k r' hm, Matrix.one_mul]
  calc ∫⁻ g, (∫⁻ x', ENNReal.ofReal (gN (oneStep k r' x c (Matrix.of g) x') ^ (-A))) *
        FsE k r' (fun l => s (sc r' l)) (Matrix.of g) ∂μ₁
      = ∫⁻ g, EInt k r' A (c * (Dx k r' x : ℂ)) (Matrix.of (lmulM m g)) *
          FsE k r' (fun l => s (sc r' l)) (m⁻¹ * Matrix.of (lmulM m g)) ∂μ₁ := by
        refine lintegral_congr_ae ?_
        filter_upwards [hconc] with g hg
        rw [hpt g hg]
        show _ = EInt k r' A (c * (Dx k r' x : ℂ)) (m * Matrix.of g) *
          FsE k r' (fun l => s (sc r' l)) (m⁻¹ * (m * Matrix.of g))
        rw [e]
    _ = ∫⁻ g, EInt k r' A (c * (Dx k r' x : ℂ)) (Matrix.of g) *
          FsE k r' (fun l => s (sc r' l)) (m⁻¹ * Matrix.of g) ∂(μ₁.map (lmulM m)) := (lintegral_map hG hl).symm
    _ = ∫⁻ g, EInt k r' A (c * (Dx k r' x : ℂ)) (Matrix.of g) *
          FsE k r' (fun l => s (sc r' l)) (m⁻¹ * Matrix.of g) ∂μ₁ := by rw [hμ₁.left m hm]
    _ = ENNReal.ofReal (fsR k r' (fun l => s (sc r' l)) m) *
          Qf k r' A (fun l => s (sc r' l)) μ₁ (c * (Dx k r' x : ℂ)) :=
        hT k r' (fun l => s (sc r' l)) μ₁ (fun g => EInt k r' A (c * (Dx k r' x : ℂ)) (Matrix.of g)) hk hμ₁
          (EInt_meas k r' A _) (fun κ' hκ' g => EInt_K k r' A _ hκ' (Matrix.of g)) m hm
    _ = ENNReal.ofReal (Psi k r' s x) * Qf k r' A (fun l => s (sc r' l)) μ₁ (c * (Dx k r' x : ℂ)) := by
        congr 1; congr 1
        unfold fsR Psi
        refine Finset.prod_congr rfl fun l _ => ?_
        rw [eq_div_of_mul_eq hG0.ne' (hga l)]

end inner

end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.XiRNonneg
section
noncomputable section

open Matrix MeasureTheory
open scoped ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS.Xi.CB

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Xi.GS

variable {k r : ℕ}

theorem hpk_conjT : (Hpk k r)ᴴ = Hpk k r := by
  ext i j
  simp only [conjTranspose_apply, hpk_apply]
  by_cases h : j = sigI k r i
  · subst h; rw [if_pos (sig_sig i).symm, if_pos rfl, sgn_sig, star_sgn]
  · have h' : ¬ i = sigI k r j := fun h2 => h (by rw [h2, sig_sig])
    rw [if_neg h', if_neg h, star_zero]

theorem hpk_K : Hpk k r ∈ Kset k r := by
  have h2 := HermitianLiftIdentities.hpk_sq (k := k) (r := r)
  refine ⟨?_, ?_⟩
  · show (Hpk k r)ᴴ * Hpk k r * Hpk k r = Hpk k r
    rw [hpk_conjT, Matrix.mul_assoc, h2, Matrix.mul_one]
  · rw [hpk_conjT, h2]

theorem gN_sq (g : Mat k r) : (∑ i, ∑ j, Complex.normSq (g i j)) = (trace (gᴴ * g)).re := by
  simp only [trace, diag, mul_apply, conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.normSq_apply, Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]; ring

theorem gN_left {κ : Mat k r} (g : Mat k r) (hκ : κᴴ * κ = 1) : gN (κ * g) = gN g := by
  unfold gN
  rw [gN_sq, gN_sq, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc κᴴ, hκ, Matrix.one_mul]

theorem gN_right {κ : Mat k r} (g : Mat k r) (hκ : κᴴ * κ = 1) : gN (g * κ) = gN g := by
  have hκ' : κ * κᴴ = 1 := mul_eq_one_comm.mp hκ
  unfold gN
  rw [gN_sq, gN_sq, conjTranspose_mul, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc,
    Matrix.mul_assoc, hκ', Matrix.mul_one]

theorem conjH_mul (a b : Mat k r) :
    Hpk k r * a * Hpk k r * (Hpk k r * b * Hpk k r) = Hpk k r * (a * b) * Hpk k r := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Hpk k r) (Hpk k r), HermitianLiftIdentities.hpk_sq, Matrix.one_mul]

theorem dot_H (v w : Fin (2 * r + k + 1) → ℂ) :
    star (Hpk k r *ᵥ v) ⬝ᵥ (Hpk k r *ᵥ w) = star v ⬝ᵥ w := by
  have h := HE_adj (HE k r (WithLp.toLp 2 v)) (WithLp.toLp 2 w)
  rw [HE_HE] at h
  simp only [HE_apply, EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp] at h
  rw [dotProduct_comm (star (Hpk k r *ᵥ v)), ← h, dotProduct_comm]

theorem ga_H (l : Fin (r + 1)) (Y : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ) :
    Ga k r l (fun a => Hpk k r *ᵥ Y a) = Ga k r l Y := by
  unfold Ga; simp only [dot_H]

theorem fsR_conj (s : Fin (r + 1) → ℝ) (x : Mat k r) :
    fsR k r s (Hpk k r * x * Hpk k r) = xiR k r s x := by
  unfold fsR xiR Del
  refine Finset.prod_congr rfl fun l _ => ?_
  have e : (fun a => (Hpk k r * x * Hpk k r) *ᵥ phiV' k r a) = fun a => Hpk k r *ᵥ (x *ᵥ phiV k r a) := by
    funext a
    rw [phiV', mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc (Hpk k r * x), HermitianLiftIdentities.hpk_sq, Matrix.mul_one]
  rw [e, ga_H, Real.sqrt_eq_rpow, ← Real.rpow_mul (XI.ga_nonneg _ _ _ _)]
  congr 1; ring

theorem xiR_nonneg (s : Fin (r + 1) → ℝ) (x : Mat k r) : 0 ≤ xiR k r s x :=
  Finset.prod_nonneg fun _ _ => Real.rpow_nonneg (Real.sqrt_nonneg _) _

theorem norm_bd {E : Type*} [NormedAddCommGroup E] (hGN : GNLower) (F : Mat k r → E) (c A : ℝ)
    (hF : ∀ g ∈ GV k r, gN g ^ A * ‖F g‖ ≤ c) (h : Mat k r) (hh : h ∈ GV k r) :
    ‖F h‖ₑ ≤ ENNReal.ofReal c * ENNReal.ofReal (gN h ^ (-A)) := by
  have h1 : 1 ≤ gN h := hGN k r h hh
  have hp : 0 < gN h ^ A := Real.rpow_pos_of_pos (by linarith) A
  have hc0 : 0 ≤ c := le_trans (mul_nonneg hp.le (norm_nonneg _)) (hF h hh)
  have h2 : ‖F h‖ ≤ c * gN h ^ (-A) := by
    rw [Real.rpow_neg (by linarith), ← div_eq_mul_inv, le_div_iff₀ hp, mul_comm]; exact hF h hh
  rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul hc0]
  exact ENNReal.ofReal_le_ofReal h2

theorem c_nonneg {E : Type*} [NormedAddCommGroup E] (hGN : GNLower) (F : Mat k r → E) (c A : ℝ)
    (hF : ∀ g ∈ GV k r, gN g ^ A * ‖F g‖ ≤ c) (h1 : (1 : Mat k r) ∈ GV k r) : 0 ≤ c := by
  have : 0 < gN (1 : Mat k r) ^ A := Real.rpow_pos_of_pos (by linarith [hGN k r 1 h1]) A
  exact le_trans (mul_nonneg this.le (norm_nonneg _)) (hF 1 h1)

theorem sum_le (hk : 1 ≤ k) (s : Fin (r + 1) → ℝ) (hs : SAdm k r s) (A : ℝ) (hA : AB k r ≤ A) :
    ∑ l : Fin (r + 1), ((l.val : ℝ) + 1) * s l ≤ A := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h1 : ∑ l : Fin (r + 1), ((l.val : ℝ) + 1) * s l ≤ ∑ l : Fin (r + 1), ((l.val : ℝ) + 1) * s0 k r l :=
    Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (by linarith [(hs l).1]) (by positivity)
  have h2 : ∑ l : Fin (r + 1), ((l.val : ℝ) + 1) * s0 k r l ≤ 2 * (r : ℝ) * r + ((r : ℝ) + 1) * k := by
    rw [Fin.sum_univ_castSucc]
    simp only [s0, Fin.coe_castSucc, Fin.is_lt, ite_true, Fin.val_last, lt_self_iff_false, ite_false]
    have h3 : ∑ i : Fin r, ((i.val : ℝ) + 1) * 2 ≤ ∑ i : Fin r, (r : ℝ) * 2 := Finset.sum_le_sum fun i _ => by
      have h := Nat.succ_le_of_lt i.isLt
      have : (i.val : ℝ) + 1 ≤ r := by exact_mod_cast h
      linarith
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h3
    linarith
  have hr : (0 : ℝ) ≤ r := by positivity
  have h4 : 2 * (r : ℝ) * r + ((r : ℝ) + 1) * k ≤ AB k r := by unfold AB; nlinarith
  linarith

theorem s_nonneg (hk : 1 ≤ k) (s : Fin (r + 1) → ℝ) (hs : SAdm k r s) (l : Fin (r + 1)) : 0 ≤ s l := by
  have h1 := (hs l).2
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  unfold s0 at h1; split_ifs at h1 <;> linarith

theorem coefStepC (hB2 : InductiveHeisenbergInputs) (hT : TBoth) (hD : DET) : CoefStep := by
  intro k r Wp Wq _ _ _ _ _ _ D A s hs hA hJ
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hGN, -, -, -, hCG', -⟩ := hB2
  have hCG := hCG' k r
  have hk := D.k_pos
  have hμ := D.haarG
  have hHK : Hpk k r ∈ Kset k r := hpk_K
  have hHG : Hpk k r ∈ GV k r := hHK.1
  have hH2 : Hpk k r * Hpk k r = 1 := HermitianLiftIdentities.hpk_sq k r
  obtain ⟨CD, hCD⟩ := hD k r s A hk (s_nonneg hk s hs) (sum_le hk s hs A hA)
  have hgc : Continuous fun g : Mt k r => gN (Matrix.of g) := by
    unfold gN
    simp only [Matrix.of_apply]
    exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      Complex.continuous_normSq.comp ((continuous_apply j).comp (continuous_apply i)))
  have hΦm : Measurable fun g : Mt k r => ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) :=
    (hgc.measurable.pow_const (-A)).ennreal_ofReal
  have hΦinv : ∀ κ ∈ Kset k r, ∀ g : Mt k r,
      ENNReal.ofReal (gN (Matrix.of (lmulM κ g)) ^ (-A)) = ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) ∧
      ENNReal.ofReal (gN (Matrix.of (rmulF κ g)) ^ (-A)) = ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) :=
    fun κ hκ g => ⟨by rw [show Matrix.of (lmulM κ g) = κ * Matrix.of g from rfl, gN_left _ hκ.2],
      by rw [show Matrix.of (rmulF κ g) = Matrix.of g * κ from rfl, gN_right _ hκ.2]⟩
  refine ⟨CD * (JInt D.μG A s).toReal, fun F F' c c' _ _ hF hF' x hx y hy => ?_⟩
  have hc0 : 0 ≤ c := c_nonneg hGN F c A hF hCG.one_mem
  have hc0' : 0 ≤ c' := c_nonneg hGN F' c' A hF' hCG.one_mem
  have hx' : Hpk k r * x * Hpk k r ∈ GV k r := hCG.mul_mem _ (hCG.mul_mem _ hHG _ hx) _ hHG
  have hy' : Hpk k r * y * Hpk k r ∈ GV k r := hCG.mul_mem _ (hCG.mul_mem _ hHG _ hy) _ hHG
  have hxinv : (Hpk k r * x * Hpk k r)⁻¹ = Hpk k r * x⁻¹ * Hpk k r :=
    Matrix.inv_eq_left_inv (by rw [conjH_mul, HermitianLiftIdentities.uh_inv_mul hx, Matrix.mul_one, hH2])
  have hae : ∀ᵐ g ∂D.μG, Matrix.of g ∈ GV k r := by rw [ae_iff]; exact hμ.conc
  set K : ℝ≥0∞ := ENNReal.ofReal c * ENNReal.ofReal c' * (CD : ℝ≥0∞) with hK
  have hKt : K ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
    ENNReal.coe_ne_top
  have hpt : ∀ᵐ g ∂D.μG, ‖F (x⁻¹ * Matrix.of g * y)‖ₑ * ‖F' (Matrix.of g)‖ₑ ≤
      K * (ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) * FsE k r s ((Hpk k r * x * Hpk k r)⁻¹ *
        (Hpk k r * Matrix.of g * Hpk k r) * (Hpk k r * y * Hpk k r))) := by
    filter_upwards [hae] with g hg
    have hh : x⁻¹ * Matrix.of g * y ∈ GV k r := hCG.mul_mem _ (hCG.mul_mem _ (hCG.inv_mem _ hx) _ hg) _ hy
    have e1 : Hpk k r * (x⁻¹ * Matrix.of g * y) * Hpk k r = (Hpk k r * x * Hpk k r)⁻¹ *
        (Hpk k r * Matrix.of g * Hpk k r) * (Hpk k r * y * Hpk k r) := by
      rw [hxinv, conjH_mul, conjH_mul]
    have hhH : Hpk k r * (x⁻¹ * Matrix.of g * y) * Hpk k r ∈ GV k r :=
      hCG.mul_mem _ (hCG.mul_mem _ hHG _ hh) _ hHG
    have gNe : gN (x⁻¹ * Matrix.of g * y) = gN (Hpk k r * (x⁻¹ * Matrix.of g * y) * Hpk k r) := by
      rw [gN_right _ hHK.2, gN_left _ hHK.2]
    have b1 := norm_bd hGN F c A hF _ hh
    have b2 : ENNReal.ofReal (gN (x⁻¹ * Matrix.of g * y) ^ (-A)) ≤ (CD : ℝ≥0∞) * FsE k r s
        ((Hpk k r * x * Hpk k r)⁻¹ * (Hpk k r * Matrix.of g * Hpk k r) * (Hpk k r * y * Hpk k r)) := by
      rw [gNe, ← e1]; exact hCD _ hhH
    have b3 := norm_bd hGN F' c' A hF' _ hg
    calc ‖F (x⁻¹ * Matrix.of g * y)‖ₑ * ‖F' (Matrix.of g)‖ₑ
        ≤ (ENNReal.ofReal c * ENNReal.ofReal (gN (x⁻¹ * Matrix.of g * y) ^ (-A))) *
          (ENNReal.ofReal c' * ENNReal.ofReal (gN (Matrix.of g) ^ (-A))) := mul_le_mul' b1 b3
      _ ≤ (ENNReal.ofReal c * ((CD : ℝ≥0∞) * FsE k r s ((Hpk k r * x * Hpk k r)⁻¹ *
            (Hpk k r * Matrix.of g * Hpk k r) * (Hpk k r * y * Hpk k r)))) *
          (ENNReal.ofReal c' * ENNReal.ofReal (gN (Matrix.of g) ^ (-A))) :=
        mul_le_mul' (mul_le_mul' le_rfl b2) le_rfl
      _ = _ := by rw [hK]; ring
  have hsub : (∫⁻ g, ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) * FsE k r s ((Hpk k r * x * Hpk k r)⁻¹ *
        (Hpk k r * Matrix.of g * Hpk k r) * (Hpk k r * y * Hpk k r)) ∂D.μG) =
      ∫⁻ g, ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) * FsE k r s ((Hpk k r * x * Hpk k r)⁻¹ *
        Matrix.of g * (Hpk k r * y * Hpk k r)) ∂D.μG := by
    rw [← HermitianLiftIdentities.rmul_int hHG hμ (fun g => ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) *
        FsE k r s ((Hpk k r * x * Hpk k r)⁻¹ * Matrix.of g * (Hpk k r * y * Hpk k r))),
      ← HermitianLiftIdentities.lmul_int hHG hμ (fun g => ENNReal.ofReal (gN (Matrix.of (rmulF (Hpk k r) g)) ^ (-A)) *
        FsE k r s ((Hpk k r * x * Hpk k r)⁻¹ * Matrix.of (rmulF (Hpk k r) g) * (Hpk k r * y * Hpk k r)))]
    refine lintegral_congr fun g => ?_
    show _ = ENNReal.ofReal (gN (Matrix.of (rmulF (Hpk k r) (lmulM (Hpk k r) g))) ^ (-A)) *
        FsE k r s ((Hpk k r * x * Hpk k r)⁻¹ * Matrix.of (rmulF (Hpk k r) (lmulM (Hpk k r) g)) *
          (Hpk k r * y * Hpk k r))
    rw [(hΦinv _ hHK _).2, (hΦinv _ hHK _).1]
    rfl
  have hTb := hT k r s D.μG (fun g => ENNReal.ofReal (gN (Matrix.of g) ^ (-A))) hk hμ hΦm hΦinv _ hx' _ hy'
  calc (∫⁻ g, ‖F (x⁻¹ * Matrix.of g * y)‖ₑ * ‖F' (Matrix.of g)‖ₑ ∂D.μG)
      ≤ ∫⁻ g, K * (ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) * FsE k r s ((Hpk k r * x * Hpk k r)⁻¹ *
        (Hpk k r * Matrix.of g * Hpk k r) * (Hpk k r * y * Hpk k r))) ∂D.μG := lintegral_mono_ae hpt
    _ = K * ∫⁻ g, ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) * FsE k r s ((Hpk k r * x * Hpk k r)⁻¹ *
        (Hpk k r * Matrix.of g * Hpk k r) * (Hpk k r * y * Hpk k r)) ∂D.μG := lintegral_const_mul' _ _ hKt
    _ = K * (ENNReal.ofReal (fsR k r s (Hpk k r * x * Hpk k r) * fsR k r s (Hpk k r * y * Hpk k r)) *
        JInt D.μG A s) := by rw [hsub, hTb]; rfl
    _ = ENNReal.ofReal (CD * (JInt D.μG A s).toReal * c * c') * (xiN k r s x : ℝ≥0∞) *
        (xiN k r s y : ℝ≥0∞) := by
      rw [fsR_conj, fsR_conj, ENNReal.ofReal_mul (xiR_nonneg s x)]
      rw [show (xiN k r s x : ℝ≥0∞) = ENNReal.ofReal (xiR k r s x) from rfl,
        show (xiN k r s y : ℝ≥0∞) = ENNReal.ofReal (xiR k r s y) from rfl]
      rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (NNReal.coe_nonneg CD) ENNReal.toReal_nonneg) hc0),
        ENNReal.ofReal_mul (mul_nonneg (NNReal.coe_nonneg CD) ENNReal.toReal_nonneg), ENNReal.ofReal_mul (NNReal.coe_nonneg CD),
        ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_toReal hJ.ne, hK]
      ring

end ReciprocityTheory.ChartRestriction.DS.Xi.CB
end
end

