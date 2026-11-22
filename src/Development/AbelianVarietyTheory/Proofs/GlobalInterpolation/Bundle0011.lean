import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EnormPowLeInvMeasureMulLintegralBall
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0001
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0001
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsInterpolationExteriorSmallCoeffs
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LFunctionEqTsumOfOneLt
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0004
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0005
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0006
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EnormSqLeLintegralDisc
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory

namespace GlobalTheory

noncomputable def euclideanLineIsometry : EuclideanSpace ℂ (Fin 1) ≃ₗᵢ[ℝ] ℂ where
  toFun z := z 0
  invFun w := WithLp.toLp 2 (fun _ => w)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv z := by
    ext i
    rw [Subsingleton.elim i 0]
  right_inv _ := rfl
  norm_map' z := by
    show ‖z 0‖ = ‖z‖
    rw [EuclideanSpace.norm_eq]
    simp

theorem norm_sq_le_integral_square :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℂ → ℂ) (ρ : ℂ) (r : ℝ), Differentiable ℂ f → 0 < r →
      ‖f ρ‖ ^ 2 ≤ C / r ^ 2 * ∫ σ in (ρ.re - r)..(ρ.re + r), ∫ t in (ρ.im - r)..(ρ.im + r),
        ‖f (σ + t * I)‖ ^ 2 := by
  refine ⟨Real.pi⁻¹, inv_pos.mpr Real.pi_pos, fun f ρ r hf hr => ?_⟩
  set S : Set ℂ := Set.Ioc (ρ.re - r) (ρ.re + r) ×ℂ Set.Ioc (ρ.im - r) (ρ.im + r) with hS
  have hcont : Continuous fun z => ‖f z‖ ^ 2 := hf.continuous.norm.pow 2
  have hSsub : S ⊆ Metric.closedBall ρ (2 * r) := by
    intro z hz
    simp only [hS, Complex.mem_reProdIm, Set.mem_Ioc] at hz
    rw [Metric.mem_closedBall, dist_eq_norm]
    have h := Complex.norm_le_abs_re_add_abs_im (z - ρ)
    simp only [Complex.sub_re, Complex.sub_im] at h
    have h1 : |z.re - ρ.re| ≤ r := abs_le.mpr ⟨by linarith, by linarith⟩
    have h2 : |z.im - ρ.im| ≤ r := abs_le.mpr ⟨by linarith, by linarith⟩
    linarith
  have hint : IntegrableOn (fun z => ‖f z‖ ^ 2) S :=
    (hcont.continuousOn.integrableOn_compact (isCompact_closedBall ρ (2 * r))).mono_set hSsub
  have hball : Metric.ball ρ r ⊆ S := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have h1 := Complex.abs_re_le_norm (z - ρ)
    have h2 := Complex.abs_im_le_norm (z - ρ)
    simp only [Complex.sub_re, Complex.sub_im] at h1 h2
    have a1 := abs_lt.mp (lt_of_le_of_lt h1 hz)
    have a2 := abs_lt.mp (lt_of_le_of_lt h2 hz)
    simp only [hS, Complex.mem_reProdIm, Set.mem_Ioc]
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  have hv := volume_ball_complex ρ hr
  simp only [Module.finrank_self, pow_one, mul_one, Nat.factorial_one, Nat.cast_one,
    div_one] at hv
  have hvr : volume.real (Metric.ball ρ r) = Real.pi * r ^ 2 := by
    rw [measureReal_def, hv, ENNReal.toReal_ofReal (by positivity)]
  have key := norm_pow_le_inv_measure_mul_integral_ball volume (a := ρ) hr hf.differentiableOn 2
    (integrableOn_norm_pow_ball volume (a := ρ) hf.continuous.continuousOn 2)
  rw [hvr] at key
  have hmono : ∫ z in Metric.ball ρ r, ‖f z‖ ^ 2 ≤ ∫ z in S, ‖f z‖ ^ 2 :=
    setIntegral_mono_set hint (Filter.Eventually.of_forall fun z => by positivity)
      hball.eventuallyLE
  have hp := Complex.volume_preserving_equiv_real_prod.symm
  have he := Complex.measurableEquivRealProd.symm.measurableEmbedding
  have hpre : Complex.measurableEquivRealProd.symm ⁻¹' S =
      Set.Ioc (ρ.re - r) (ρ.re + r) ×ˢ Set.Ioc (ρ.im - r) (ρ.im + r) := by
    ext p
    simp [hS, Complex.measurableEquivRealProd_symm_apply, Complex.mem_reProdIm]
  have hint' := (hp.integrableOn_comp_preimage he).mpr hint
  rw [hpre, Measure.volume_eq_prod] at hint'
  have hiter : ∫ z in S, ‖f z‖ ^ 2 = ∫ σ in (ρ.re - r)..(ρ.re + r),
      ∫ t in (ρ.im - r)..(ρ.im + r), ‖f (σ + t * I)‖ ^ 2 := by
    rw [← hp.setIntegral_preimage_emb he (fun z => ‖f z‖ ^ 2) S, hpre, Measure.volume_eq_prod,
      setIntegral_prod (fun x => ‖f (Complex.measurableEquivRealProd.symm x)‖ ^ 2) hint', intervalIntegral.integral_of_le (by linarith)]
    refine setIntegral_congr_fun measurableSet_Ioc fun σ _ => ?_
    rw [intervalIntegral.integral_of_le (by linarith)]
    simp [Complex.measurableEquivRealProd_symm_apply, Complex.mk_eq_add_mul_I]
  calc ‖f ρ‖ ^ 2 ≤ (Real.pi * r ^ 2)⁻¹ * ∫ z in Metric.ball ρ r, ‖f z‖ ^ 2 := key
    _ ≤ (Real.pi * r ^ 2)⁻¹ * ∫ z in S, ‖f z‖ ^ 2 := by gcongr
    _ = _ := by rw [hiter, mul_inv, div_eq_mul_inv]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsBruhatFunctionClosedSubgroup
section
open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal

namespace GlobalTheory

open MeasureTheory Topology in
open scoped ENNReal Pointwise in
private theorem exists_normalized_weight_of_closedEmbedding
    {T T' : Type} [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T]
    [SecondCountableTopology T] [T2Space T] [MeasurableSpace T] [BorelSpace T]
    [Group T'] [TopologicalSpace T'] [IsTopologicalGroup T'] [MeasurableSpace T'] [BorelSpace T']
    (j : T' →* T) (hj : IsClosedEmbedding j) (ν : Measure T') [ν.IsHaarMeasure] :
    ∃ φ : T → ℝ≥0∞, Measurable φ ∧ (∀ g, ∫⁻ s, φ (g * j s) ∂ν = 1) ∧
      ∀ K : Set T, IsCompact K → ∃ (K' : Set T) (C : ℝ≥0∞), IsCompact K' ∧ C < ⊤ ∧
        ∀ k ∈ K, ∀ s : T', φ (k * j s) ≤ C ∧ (φ (k * j s) ≠ 0 → k * j s ∈ K') := by
  classical
  haveI : LocallyCompactSpace T' := hj.locallyCompactSpace
  haveI : SecondCountableTopology T' := hj.isEmbedding.secondCountableTopology
  haveI : T2Space T' := hj.isEmbedding.t2Space
  have hjm : Measurable j := hj.continuous.measurable
  let E := CompactExhaustion.choice T
  obtain ⟨A, hA⟩ : ∃ A : ℕ → Set T, ∀ n x, x ∈ A n ↔ ∃ s : T', x * j s ∈ E n :=
    ⟨fun n => {x | ∃ s : T', x * j s ∈ E n}, fun _ _ => Iff.rfl⟩
  have hA_mono : ∀ {m n}, m ≤ n → A m ⊆ A n := fun hmn x hx => by
    obtain ⟨s, hs⟩ := (hA _ x).1 hx
    exact (hA _ x).2 ⟨s, E.subset hmn hs⟩
  have hA_mul : ∀ n x (s : T'), x * j s ∈ A n ↔ x ∈ A n := by
    intro n x s
    rw [hA, hA]
    constructor
    · rintro ⟨s', hs'⟩
      exact ⟨s * s', by simpa [mul_assoc] using hs'⟩
    · rintro ⟨s', hs'⟩
      exact ⟨s⁻¹ * s', by simpa [mul_assoc] using hs'⟩
  have hE_A : ∀ n, E n ⊆ A n := fun n x hx => (hA n x).2 ⟨1, by simpa using hx⟩
  have hA_meas : ∀ n, MeasurableSet (A n) := by
    intro n
    have hAn : A n = E n * Set.range j := by
      ext x
      rw [hA, Set.mem_mul]
      constructor
      · rintro ⟨s, hs⟩
        exact ⟨_, hs, j s⁻¹, ⟨s⁻¹, rfl⟩, by simp [mul_assoc]⟩
      · rintro ⟨k, hk, _, ⟨s, rfl⟩, rfl⟩
        exact ⟨s⁻¹, by simpa [mul_assoc] using hk⟩
    rw [hAn]
    exact (hj.isClosed_range.mul_left_of_isCompact (E.isCompact n)).measurableSet
  have hex : ∀ x, ∃ n, x ∈ A n := fun x => ⟨E.find x, hE_A _ (E.mem_find x)⟩
  obtain ⟨N, hNm, hN⟩ : ∃ N : T → ℕ, Measurable N ∧ ∀ x n, N x ≤ n ↔ x ∈ A n := by
    refine ⟨fun x => Nat.find (hex x), measurable_find hex hA_meas, fun x n => ?_⟩
    rw [Nat.find_le_iff]
    exact ⟨fun ⟨m, hm, hx⟩ => hA_mono hm hx, fun hx => ⟨n, le_rfl, hx⟩⟩
  have hN_mem : ∀ x, x ∈ A (N x) := fun x => (hN x _).1 le_rfl
  have hN_mul : ∀ x (s : T'), N (x * j s) = N x := fun x s =>
    le_antisymm ((hN _ _).2 ((hA_mul _ _ _).2 (hN_mem x)))
      ((hN _ _).2 ((hA_mul _ _ _).1 (hN_mem _)))
  obtain ⟨S, hS⟩ : ∃ S : Set T, ∀ x, x ∈ S ↔ x ∈ E (N x + 1) :=
    ⟨{x | x ∈ E (N x + 1)}, fun _ => Iff.rfl⟩
  have hS_meas : MeasurableSet S := by
    have hSU : S = ⋃ n, N ⁻¹' {n} ∩ E (n + 1) := by
      ext x
      rw [hS]
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun hx => ⟨_, rfl, hx⟩, by rintro ⟨n, rfl, hx⟩; exact hx⟩
    rw [hSU]
    exact MeasurableSet.iUnion fun n =>
      (hNm (measurableSet_singleton n)).inter (E.isCompact _).isClosed.measurableSet
  obtain ⟨ψ, hψm, hψle, hψS, hψ1⟩ : ∃ ψ : T → ℝ≥0∞, Measurable ψ ∧ (∀ x, ψ x ≤ 1) ∧
      (∀ x, ψ x ≠ 0 → x ∈ S) ∧ (∀ x, x ∈ S → ψ x = 1) := by
    refine ⟨S.indicator fun _ => 1, measurable_const.indicator hS_meas, fun x => ?_,
      fun x hx => ?_, fun x hx => Set.indicator_of_mem hx _⟩
    · by_cases hx : x ∈ S <;> simp [hx]
    · by_contra hxS
      exact hx (by simp [hxS])
  obtain ⟨F, hFm, hF⟩ : ∃ F : T → ℝ≥0∞, Measurable F ∧ ∀ x, F x = ∫⁻ s, ψ (x * j s) ∂ν :=
    ⟨fun x => ∫⁻ s, ψ (x * j s) ∂ν,
      (hψm.comp (measurable_fst.mul (hjm.comp measurable_snd))).lintegral_prod_right',
      fun _ => rfl⟩
  have hF_mul : ∀ x (s : T'), F (x * j s) = F x := by
    intro x s
    rw [hF, hF]
    simpa [mul_assoc] using lintegral_mul_left_eq_self (μ := ν) (fun t => ψ (x * j t)) s
  have hF_pos : ∀ n, ∃ c : ℝ≥0∞, 0 < c ∧ ∀ x, N x = n → c ≤ F x := by
    intro n
    obtain ⟨V, hV, hKV⟩ :=
      compact_open_separated_mul_right (E.isCompact n) isOpen_interior (E.subset_interior_succ n)
    have hVo : IsOpen (j ⁻¹' interior V) := isOpen_interior.preimage hj.continuous
    have hV1 : (1 : T') ∈ j ⁻¹' interior V := by
      simpa using mem_interior_iff_mem_nhds.2 hV
    refine ⟨ν (j ⁻¹' interior V), hVo.measure_pos ν ⟨1, hV1⟩, fun x hx => ?_⟩
    obtain ⟨s₀, hs₀⟩ := (hA n x).1 (hx ▸ hN_mem x)
    calc ν (j ⁻¹' interior V) = ∫⁻ s, (j ⁻¹' interior V).indicator 1 s ∂ν :=
          (lintegral_indicator_one hVo.measurableSet).symm
      _ ≤ ∫⁻ s, ψ (x * j s₀ * j s) ∂ν := by
          refine lintegral_mono fun s => ?_
          by_cases hs : s ∈ j ⁻¹' interior V
          · rw [Set.indicator_of_mem hs, Pi.one_apply, hψ1]
            rw [hS, hN_mul, hN_mul, hx]
            exact interior_subset (hKV (Set.mul_mem_mul hs₀ (interior_subset hs)))
          · simp [hs]
      _ = F x := by rw [← hF, hF_mul]
  choose c hc_pos hc using hF_pos
  have hF_ne : ∀ x, F x ≠ 0 := fun x => ((hc_pos (N x)).trans_le (hc _ x rfl)).ne'
  have hF_fin : ∀ x, F x ≠ ⊤ := by
    intro x
    have hK : IsCompact ((fun s : T' => x * j s) ⁻¹' E (N x + 1)) :=
      ((Homeomorph.mulLeft x).isClosedEmbedding.comp hj).isCompact_preimage (E.isCompact _)
    refine (lt_of_le_of_lt ?_ (hK.measure_lt_top (μ := ν))).ne
    calc F x = ∫⁻ s, ψ (x * j s) ∂ν := hF x
      _ ≤ ∫⁻ s, ((fun s : T' => x * j s) ⁻¹' E (N x + 1)).indicator 1 s ∂ν := by
          refine lintegral_mono fun s => ?_
          by_cases hs : s ∈ (fun s : T' => x * j s) ⁻¹' E (N x + 1)
          · rw [Set.indicator_of_mem hs]
            exact hψle _
          · rw [Set.indicator_of_notMem hs]
            refine le_of_eq (by_contra fun hψs => ?_)
            have hmem := (hS _).1 (hψS _ hψs)
            rw [hN_mul] at hmem
            exact hs hmem
      _ = ν ((fun s : T' => x * j s) ⁻¹' E (N x + 1)) :=
          lintegral_indicator_one hK.isClosed.measurableSet
  refine ⟨fun x => ψ x * (F x)⁻¹, hψm.mul hFm.inv, fun g => ?_, fun K hK => ?_⟩
  · calc ∫⁻ s, ψ (g * j s) * (F (g * j s))⁻¹ ∂ν = ∫⁻ s, ψ (g * j s) * (F g)⁻¹ ∂ν := by
          simp_rw [hF_mul]
      _ = (∫⁻ s, ψ (g * j s) ∂ν) * (F g)⁻¹ :=
          lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 (hF_ne g))
      _ = 1 := by rw [← hF, ENNReal.mul_inv_cancel (hF_ne g) (hF_fin g)]
  · obtain ⟨M, hM⟩ := E.exists_superset_of_isCompact hK
    refine ⟨E (M + 1), ∑ n ∈ Finset.range (M + 1), (c n)⁻¹, E.isCompact _,
      ENNReal.sum_lt_top.2 fun n _ => ENNReal.inv_lt_top.2 (hc_pos n), fun k hk s => ⟨?_, ?_⟩⟩
    · have hNk : N k ≤ M := (hN k M).2 (hE_A M (hM hk))
      calc ψ (k * j s) * (F (k * j s))⁻¹ ≤ 1 * (c (N k))⁻¹ :=
            mul_le_mul' (hψle _) (ENNReal.inv_le_inv.2 (hc _ _ (hN_mul k s)))
        _ = (c (N k))⁻¹ := one_mul _
        _ ≤ ∑ n ∈ Finset.range (M + 1), (c n)⁻¹ :=
            Finset.single_le_sum (f := fun n => (c n)⁻¹) (fun _ _ => bot_le)
              (Finset.mem_range.2 (Nat.lt_succ_of_le hNk))
    · intro hne
      have hNk : N k ≤ M := (hN k M).2 (hE_A M (hM hk))
      have hmem := (hS _).1 (hψS _ (left_ne_zero_of_mul hne))
      rw [hN_mul] at hmem
      exact E.subset (Nat.succ_le_succ hNk) hmem

open MeasureTheory in
open scoped ENNReal in

theorem _root_.GlobalTheory.exists_bruhat_function_closed_subgroup
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G)
    (hH : IsClosed (H : Set G)) (ν : Measure H) [ν.IsHaarMeasure] :
    ∃ φ : G → ℝ≥0∞, Measurable φ ∧ (∀ g : G, ∫⁻ h : H, φ (g * h) ∂ν = 1) ∧
      ∀ K : Set G, IsCompact K → ∃ (K' : Set G) (C : ℝ≥0∞), IsCompact K' ∧ C < ⊤ ∧
        ∀ k ∈ K, ∀ h : H, φ (k * h) ≤ C ∧ (φ (k * h) ≠ 0 → k * h ∈ K') := by
  obtain ⟨φ, hφm, hφ, hφK⟩ :=
    exists_normalized_weight_of_closedEmbedding H.subtype hH.isClosedEmbedding_subtypeVal ν
  exact ⟨φ, hφm, hφ, hφK⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsEquivariantProjOfLeSumIrreducible
section
open GlobalTheory.BorelCoh CategoryTheory
open scoped ContDiff Matrix

namespace GlobalTheory.BorelCoh

theorem exists_equivariant_proj_of_le_sum_irreducible {M O : Type} [AddCommGroup M] [Module ℂ M]
    (act : O → Module.End ℂ M) (V : Submodule ℂ M) (hVst : ∀ o, ∀ x ∈ V, act o x ∈ V)
    (hV : V ≤ ⨆ (W : Submodule ℂ M) (_ : (∀ o, ∀ x ∈ W, act o x ∈ W) ∧ W ≠ ⊥ ∧
      ∀ W' ≤ W, (∀ o, ∀ x ∈ W', act o x ∈ W') → W' = ⊥ ∨ W' = W), W) :
    ∃ p : M →ₗ[ℂ] M, (∀ o, ∀ x ∈ (⨆ (W : Submodule ℂ M) (_ : (∀ o, ∀ x ∈ W, act o x ∈ W) ∧ W ≠ ⊥ ∧
      ∀ W' ≤ W, (∀ o, ∀ x ∈ W', act o x ∈ W') → W' = ⊥ ∨ W' = W), W), p (act o x) = act o (p x)) ∧
      (∀ x, p x ∈ V) ∧ (∀ x ∈ V, p x = x) := by
  set Wt := ⨆ (W : Submodule ℂ M) (_ : (∀ o, ∀ x ∈ W, act o x ∈ W) ∧ W ≠ ⊥ ∧
      ∀ W' ≤ W, (∀ o, ∀ x ∈ W', act o x ∈ W') → W' = ⊥ ∨ W' = W), W with hWt
  have hst_sup : ∀ A B : Submodule ℂ M, (∀ o, ∀ x ∈ A, act o x ∈ A) → (∀ o, ∀ x ∈ B, act o x ∈ B) →
      ∀ o, ∀ x ∈ A ⊔ B, act o x ∈ A ⊔ B := by
    intro A B hA hB o x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add]
    exact Submodule.add_mem_sup (hA o y hy) (hB o z hz)

  let s : Set (Submodule ℂ M) := {C | (∀ o, ∀ x ∈ C, act o x ∈ C) ∧ C ≤ Wt ∧ Disjoint V C}
  obtain ⟨C, -, ⟨hCst, hCW, hCd⟩, hCmax⟩ := zorn_le_nonempty₀ s (by
    intro c hcs hc y hy
    have hne : c.Nonempty := ⟨y, hy⟩
    have hdir : DirectedOn (· ≤ ·) c := hc.directedOn
    refine ⟨sSup c, ⟨?_, sSup_le fun z hz => (hcs hz).2.1, ?_⟩, fun z hz => le_sSup hz⟩
    · intro o x hx
      obtain ⟨z, hz, hxz⟩ := (Submodule.mem_sSup_of_directed hne hdir).1 hx
      exact (Submodule.mem_sSup_of_directed hne hdir).2 ⟨z, hz, (hcs hz).1 o x hxz⟩
    · rw [Submodule.disjoint_def]
      intro x hxV hx
      obtain ⟨z, hz, hxz⟩ := (Submodule.mem_sSup_of_directed hne hdir).1 hx
      exact (Submodule.disjoint_def.1 (hcs hz).2.2) x hxV hxz) ⊥
    ⟨fun o x hx => by rw [Submodule.mem_bot] at hx ⊢; rw [hx, map_zero], bot_le, disjoint_bot_right⟩

  have hWle : Wt ≤ V ⊔ C := by
    refine iSup₂_le fun S hS => ?_
    obtain ⟨hSst, hSne, hSmin⟩ := hS
    have hinst : ∀ o, ∀ x ∈ S ⊓ (V ⊔ C), act o x ∈ S ⊓ (V ⊔ C) := fun o x hx =>
      ⟨hSst o x hx.1, hst_sup V C hVst hCst o x hx.2⟩
    rcases hSmin _ inf_le_left hinst with h | h
    · have hSW : S ≤ Wt := le_iSup₂_of_le S ⟨hSst, hSne, hSmin⟩ le_rfl
      have hmem : C ⊔ S ∈ s := ⟨hst_sup C S hCst hSst, sup_le hCW hSW,
        Disjoint.disjoint_sup_right_of_disjoint_sup_left hCd (by rw [disjoint_comm, disjoint_iff]; exact h)⟩
      exact (le_sup_right.trans (hCmax hmem le_sup_left)).trans le_sup_right
    · exact h ▸ inf_le_right
  have hW : Wt = V ⊔ C := le_antisymm hWle (sup_le hV hCW)
  obtain ⟨D, hD⟩ := Submodule.exists_isCompl Wt
  have hc : IsCompl V (C ⊔ D) := by
    constructor
    · exact Disjoint.disjoint_sup_right_of_disjoint_sup_left hCd (hW ▸ hD.disjoint)
    · rw [codisjoint_iff, ← sup_assoc, ← hW, hD.sup_eq_top]
  have hl : ∀ v ∈ V, (V.linearProjOfIsCompl (C ⊔ D) hc v : M) = v := fun v hv =>
    congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hc ⟨v, hv⟩)
  have hr : ∀ w ∈ C ⊔ D, V.linearProjOfIsCompl (C ⊔ D) hc w = 0 := fun w hw =>
    Submodule.linearProjOfIsCompl_apply_right hc ⟨w, hw⟩
  refine ⟨V.subtype ∘ₗ V.linearProjOfIsCompl (C ⊔ D) hc, ?_, fun x => (V.linearProjOfIsCompl _ hc x).2, hl⟩
  intro o x hx
  rw [hW] at hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
  have hz' : z ∈ C ⊔ D := Submodule.mem_sup_left hz
  have hz'' : act o z ∈ C ⊔ D := Submodule.mem_sup_left (hCst o z hz)
  show (V.linearProjOfIsCompl _ hc (act o (y + z)) : M) = act o (V.linearProjOfIsCompl _ hc (y + z))
  rw [map_add, map_add, map_add, hr _ hz'', hr _ hz', add_zero, add_zero, hl _ (hVst o y hy), hl _ hy]

theorem exists_equivariant_proj_of_irreducible_family : ∀ (M O ι : Type) [AddCommGroup M] [Module ℂ M] [Fintype ι] [DecidableEq ι] (act : O → Module.End ℂ M) (V : ι → Submodule ℂ M), (∀ i o, ∀ x ∈ V i, act o x ∈ V i) → (∀ i, V i ≠ ⊥) → (∀ i (W : Submodule ℂ M), W ≤ V i → (∀ o, ∀ x ∈ W, act o x ∈ W) → W = ⊥ ∨ W = V i) → (∀ i j, i ≠ j → ∀ f : M →ₗ[ℂ] M, (∀ o, ∀ x ∈ V i, f (act o x) = act o (f x)) → (∀ x ∈ V i, f x ∈ V j) → ∀ x ∈ V i, f x = 0) → ∀ i, ∃ p : M →ₗ[ℂ] M, (∀ o, ∀ x ∈ (⨆ (W : Submodule ℂ M) (_ : (∀ o, ∀ x ∈ W, act o x ∈ W) ∧ W ≠ ⊥ ∧ ∀ W' ≤ W, (∀ o, ∀ x ∈ W', act o x ∈ W') → W' = ⊥ ∨ W' = W), W), p (act o x) = act o (p x)) ∧ (∀ x ∈ (⨆ (W : Submodule ℂ M) (_ : (∀ o, ∀ x ∈ W, act o x ∈ W) ∧ W ≠ ⊥ ∧ ∀ W' ≤ W, (∀ o, ∀ x ∈ W', act o x ∈ W') → W' = ⊥ ∨ W' = W), W), p x ∈ V i) ∧ (∀ x ∈ V i, p x = x) ∧ ∀ j, j ≠ i → ∀ x ∈ V j, p x = 0 := by
  intro M O ι _ _ _ _ act V h1 h2 h3 h4 i
  have hirr : ∀ j, V j ≤ (⨆ (W : Submodule ℂ M) (_ : (∀ o, ∀ x ∈ W, act o x ∈ W) ∧ W ≠ ⊥ ∧ ∀ W' ≤ W, (∀ o, ∀ x ∈ W', act o x ∈ W') → W' = ⊥ ∨ W' = W), W) := fun j =>
    le_iSup₂_of_le (f := fun (W : Submodule ℂ M) (_ : (∀ o, ∀ x ∈ W, act o x ∈ W) ∧ W ≠ ⊥ ∧
      ∀ W' ≤ W, (∀ o, ∀ x ∈ W', act o x ∈ W') → W' = ⊥ ∨ W' = W) => W) (V j) ⟨h1 j, h2 j, h3 j⟩ le_rfl
  obtain ⟨p, hpe, hpV, hpid⟩ := exists_equivariant_proj_of_le_sum_irreducible act (V i) (h1 i) (hirr i)
  exact ⟨p, hpe, fun x _ => hpV x, hpid,
    fun j hji x hx => h4 j i hji p (fun o y hy => hpe o y (hirr j hy)) (fun y _ => hpV y) x hx⟩

end GlobalTheory.BorelCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsInterpolationExteriorSmallCoeffsStatement
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_interpolation_exterior_small_coeffs : ∀ (l : ℕ) (z : Fin l → ℂ) (g : ℂ → ℂ) (r G : ℝ), 0 < r → r ≤ 1 → (∀ i, r < ‖z i‖ ∧ ‖z i‖ ≤ 1) → DifferentiableOn ℂ g {w | r ≤ ‖w‖} → Tendsto g (Filter.cocompact ℂ) (𝓝 0) → (∀ w : ℂ, ‖w‖ = r → ‖g w‖ ≤ G * ‖∏ i, (w - z i)‖) → ∃ c : Fin l → ℂ, (∀ i, ∑ j, c j * z i ^ (j : ℕ) = g (z i)) ∧ ∑ j, ‖c j‖ ≤ 4 ^ l * r * G := by
  first | exact @GlobalTheory.ExteriorInterpolation.interpolation | exact GlobalTheory.ExteriorInterpolation.interpolation | (intros; apply GlobalTheory.ExteriorInterpolation.interpolation <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsNormDerivLFunctionLe
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory

namespace GlobalTheory.DirichletDeriv

theorem rpow_neg_le {q n : ℕ} (hn : 1 ≤ n) (hnq : n ≤ q) {x : ℝ}
    (hx : 1 - 2 / Real.log (3 * q) ≤ x) : (n : ℝ) ^ (-x) ≤ Real.exp 2 * (n : ℝ)⁻¹ := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnq' : (n : ℝ) ≤ q := by exact_mod_cast hnq
  have hL : 0 < Real.log (3 * q) := Real.log_pos (by linarith)
  have hl : Real.log n ≤ Real.log (3 * q) := Real.log_le_log (by linarith) (by linarith)
  have h1 : (n : ℝ) ^ (-x) ≤ (n : ℝ) ^ (2 / Real.log (3 * q) + (-1)) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  refine h1.trans ?_
  rw [Real.rpow_add (by linarith), Real.rpow_neg_one]
  gcongr
  rw [Real.rpow_def_of_pos (by linarith)]
  apply Real.exp_le_exp.mpr
  rw [← mul_div_assoc, div_le_iff₀ hL]
  linarith

theorem norm_LFunction_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {s : ℂ}
    (h1 : 1 - 2 / Real.log (3 * q) ≤ s.re) (h2 : 1 / 20 ≤ s.re) (h3 : ‖s‖ ≤ 2) :
    ‖LFunction χ s‖ ≤ 84 * Real.exp 2 * Real.log (3 * q) := by
  have hq : 1 ≤ q := NeZero.pos q
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hs : 0 < s.re := by linarith
  have hL : 1 ≤ Real.log (3 * q) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hl : Real.log q ≤ Real.log (3 * q) := Real.log_le_log (by linarith) (by linarith)
  have hE : 0 < Real.exp 2 := Real.exp_pos 2
  have ht := GlobalTheory.DirichletTail.norm_LFunction_sub_sum_le q χ hχ s hs q hq
  have hd : ‖s‖ / s.re ≤ 40 := by rw [div_le_iff₀ hs]; linarith
  have ht2 : 2 * q * (1 + ‖s‖ / s.re) * (q : ℝ) ^ (-s.re) ≤ 82 * Real.exp 2 := by
    calc 2 * q * (1 + ‖s‖ / s.re) * (q : ℝ) ^ (-s.re)
        ≤ 2 * q * (1 + 40) * (Real.exp 2 * (q : ℝ)⁻¹) := by
          gcongr
          exact rpow_neg_le hq le_rfl h1
      _ = 82 * Real.exp 2 := by field_simp; ring
  have hsum : ‖∑ n ∈ Finset.Icc 1 q, χ (n : ZMod q) * (n : ℂ) ^ (-s)‖
      ≤ Real.exp 2 * (1 + Real.log q) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ n ∈ Finset.Icc 1 q, ‖χ (n : ZMod q) * (n : ℂ) ^ (-s)‖
        ≤ ∑ n ∈ Finset.Icc 1 q, Real.exp 2 * (n : ℝ)⁻¹ := by
          refine Finset.sum_le_sum (fun n hn => ?_)
          rw [Finset.mem_Icc] at hn
          rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
          exact (mul_le_of_le_one_left (by positivity) (χ.norm_le_one _)).trans
            (rpow_neg_le hn.1 hn.2 h1)
      _ = Real.exp 2 * (harmonic q : ℝ) := by
          rw [← Finset.mul_sum, harmonic_eq_sum_Icc]; push_cast; rfl
      _ ≤ Real.exp 2 * (1 + Real.log q) := by
          gcongr
          exact harmonic_le_one_add_log q
  have h4 := norm_le_norm_sub_add (LFunction χ s)
    (∑ n ∈ Finset.Icc 1 q, χ (n : ZMod q) * (n : ℂ) ^ (-s))
  nlinarith

theorem exists_norm_deriv_LFunction_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ σ : ℝ,
      1 - 1 / Real.log (3 * q) ≤ σ → σ ≤ 1 →
        ‖deriv (LFunction χ) σ‖ ≤ C * Real.log (3 * q) ^ 2 := by
  refine ⟨336 * Real.exp 2, by positivity, fun q _ χ hχ σ h1 h2 => ?_⟩
  have hq : 2 ≤ q := by
    have h0 := NeZero.pos q
    by_contra h
    obtain rfl : q = 1 := by omega
    exact hχ (DirichletCharacter.level_one χ)
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hL : 1.38 ≤ Real.log (3 * q) := by
    have h4 : Real.log (2 ^ 2) ≤ Real.log (3 * q) := Real.log_le_log (by norm_num) (by linarith)
    rw [Real.log_pow] at h4
    push_cast at h4
    linarith [Real.log_two_gt_d9]
  set L := Real.log (3 * q) with hLdef
  have hL0 : 0 < L := by linarith
  have hinv : 1 / L ≤ 3 / 4 := by rw [div_le_iff₀ hL0]; linarith
  have hinv0 : 0 < 1 / L := by positivity
  have hr : 0 < 1 / L / 4 := by positivity
  have key := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (f := LFunction χ) (c := (σ : ℂ))
    (C := 84 * Real.exp 2 * L) hr (differentiable_LFunction hχ).diffContOnCl (fun z hz => by
      rw [mem_sphere_iff_norm] at hz
      have hre := Complex.abs_re_le_norm (z - σ)
      rw [hz, Complex.sub_re, Complex.ofReal_re, abs_le] at hre
      have h2L : 2 / L = 2 * (1 / L) := by ring
      refine norm_LFunction_le χ hχ (by rw [← hLdef, h2L]; linarith [hre.1]) (by linarith [hre.1]) ?_
      have h5 := norm_le_norm_sub_add z (σ : ℂ)
      rw [hz, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)] at h5
      linarith)
  refine key.trans (le_of_eq ?_)
  field_simp
  ring

end GlobalTheory.DirichletDeriv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FourierInversionHaarSymmFormStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_inversion_haar_symm_form_alt : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ), (∀ x y, B x y = B y x) → (∀ x, (∀ y, B x y = 0) → x = 0) → ∀ μ : Measure V, μ.IsAddHaarMeasure → (∃ c : ℝ, 0 < c ∧ ∀ Φ : V → ℂ, Continuous Φ → Integrable Φ μ → Integrable (fun y => ∫ x, Φ x * Complex.exp (2 * Real.pi * Complex.I * ((B x y : ℝ) : ℂ)) ∂μ) μ → ∀ z, ∫ y, (∫ x, Φ x * Complex.exp (2 * Real.pi * Complex.I * ((B x y : ℝ) : ℂ)) ∂μ) * Complex.exp (2 * Real.pi * Complex.I * ((B y z : ℝ) : ℂ)) ∂μ = (c : ℂ) * Φ (-z)) ∧ ∀ Φ : SchwartzMap V ℂ, Integrable (⇑Φ) μ ∧ Integrable (fun y => ∫ x, Φ x * Complex.exp (2 * Real.pi * Complex.I * ((B x y : ℝ) : ℂ)) ∂μ) μ := by
  first | exact @GlobalTheory.fourier_inversion_haar_symm_form | exact GlobalTheory.fourier_inversion_haar_symm_form | (intros; apply GlobalTheory.fourier_inversion_haar_symm_form <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LinearEquivDescendsOfPreservesImageStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linearEquiv_descends_det_of_preserves_image : ∀ {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (f : K →+* ℂ) (u : (ι → ℂ) ≃ₗ[ℂ] (ι → ℂ)), (∀ v : ι → K, ∃ v' : ι → K, u (fun i => f (v i)) = fun i => f (v' i)) → ∃ g : (ι → K) ≃ₗ[K] (ι → K), (∀ v, u (fun i => f (v i)) = fun i => f (g v i)) ∧ LinearMap.det (u : (ι → ℂ) →ₗ[ℂ] (ι → ℂ)) = f (LinearMap.det (g : (ι → K) →ₗ[K] (ι → K))) := by
  first | exact @GlobalTheory.linearEquiv_descends_of_preserves_image | exact GlobalTheory.linearEquiv_descends_of_preserves_image | (intros; apply GlobalTheory.linearEquiv_descends_of_preserves_image <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LintegralTsumOrbitUnfoldStatement
section
open MeasureTheory Topology
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_tsum_orbit_unfold_alt : ∀ (G G' V X : Type) [Group G] [Group G'] [MeasurableSpace G] [MeasurableSpace G'] [MeasurableMul₂ G] [MeasurableInv G] [MeasurableMul G'] [MulAction G V] (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant] (μ' : Measure G') [SFinite μ'] [μ'.IsMulLeftInvariant] (Γ : Subgroup G) (Γ' : Subgroup G') [Countable Γ] [Countable Γ'] (𝓕 : Set G) (𝓕' : Set G'), IsFundamentalDomain Γ 𝓕 μ → IsFundamentalDomain Γ' 𝓕' μ' → ∀ (φ : G' →* G), Measurable φ → Function.Injective φ → (∀ g, φ g ∈ Γ ↔ g ∈ Γ') → ∀ (x : V), φ.range = MulAction.stabilizer G x → ∀ (c : X → V), Function.Injective c → (∀ y, y ∈ Set.range c ↔ ∃ γ ∈ Γ, γ • x = y) → ∀ (u : G → ℝ≥0∞), Measurable u → ∀ (Φ : V → ℝ≥0∞), (∀ h : G, Φ (h⁻¹ • x) = ∫⁻ g, u ((φ g)⁻¹ * h) ∂μ') → ∫⁻ h in 𝓕, ∑' i, Φ (h⁻¹ • c i) ∂μ = μ' 𝓕' * ∫⁻ h, u h ∂μ := by
  first | exact @GlobalTheory.lintegral_tsum_orbit_unfold | exact GlobalTheory.lintegral_tsum_orbit_unfold | (intros; apply GlobalTheory.lintegral_tsum_orbit_unfold <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MeasureEqZeroOfFiniteInterLinesStatement
section
open MeasureTheory Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measure_eq_zero_of_finite_inter_lines' : ∀ (K V : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K] [MeasurableSpace K] [BorelSpace K] [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul K V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (Z : Set V), MeasurableSet Z → ∀ y : V, (∀ x : V, {t : K | x + t • y ∈ Z}.Finite) → μ Z = 0 := by
  first | exact @GlobalTheory.measure_eq_zero_of_finite_inter_lines | exact GlobalTheory.measure_eq_zero_of_finite_inter_lines | (intros; apply GlobalTheory.measure_eq_zero_of_finite_inter_lines <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuadraticAtMostTwoPrimesOverStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadratic_field_at_most_two_primes_over_prime : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (q : ℕ), q.Prime → ∀ P₁ P₂ P₃ : HeightOneSpectrum (𝓞 K), ((q : ℕ) : 𝓞 K) ∈ P₁.asIdeal → ((q : ℕ) : 𝓞 K) ∈ P₂.asIdeal → ((q : ℕ) : 𝓞 K) ∈ P₃.asIdeal → P₁ = P₂ ∨ P₁ = P₃ ∨ P₂ = P₃ := by
  first | exact @GlobalTheory.quadratic_at_most_two_primes_over | exact GlobalTheory.quadratic_at_most_two_primes_over | (intros; apply GlobalTheory.quadratic_at_most_two_primes_over <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuadraticUnramifiedIffInertOrSplitStatement
section
open scoped TensorProduct
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadratic_unramified_iff_isPrime_map_or_ncard_primesOver_two : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Module.finrank F E = 2 → ∀ v : HeightOneSpectrum (𝓞 F), ((∀ w : HeightOneSpectrum (𝓞 E), w.asIdeal.LiesOver v.asIdeal → Algebra.IsUnramifiedAt (𝓞 F) w.asIdeal) ↔ ((v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E))).IsPrime ∨ (v.asIdeal.primesOver (𝓞 E)).ncard = 2)) := by
  first | exact @GlobalTheory.quadratic_unramified_iff_inert_or_split | exact GlobalTheory.quadratic_unramified_iff_inert_or_split | (intros; apply GlobalTheory.quadratic_unramified_iff_inert_or_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ValuationOfGeneratorOfPowStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_eq_exp_neg_of_pow_eq_span_singleton : ∀ (K : Type) [Field K] [NumberField K] (𝔭 : HeightOneSpectrum (𝓞 K)) (n : ℕ) (π : 𝓞 K), 𝔭.asIdeal ^ n = Ideal.span {π} → 𝔭.valuation K (π : K) = WithZero.exp (-(n : ℤ)) := by
  first | exact @GlobalTheory.valuation_of_generator_of_pow | exact GlobalTheory.valuation_of_generator_of_pow | (intros; apply GlobalTheory.valuation_of_generator_of_pow <;> assumption)
end

