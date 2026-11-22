import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoLintegralPoissonKernelBoundary
section
open MeasureTheory

namespace GlobalTheory

theorem lintegral_concKernel_le_one {t : ℝ} (ht : 0 < t) :
    ∫⁻ s in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (t / (1 - s + t) ^ 2) ≤ 1 := by
  have hpos : ∀ s ∈ Set.uIcc (0 : ℝ) 1, 1 - s + t ≠ 0 := by
    intro s hs
    rw [Set.uIcc_of_le zero_le_one] at hs
    have := hs.2
    linarith
  have hc : ContinuousOn (fun s : ℝ => t / (1 - s + t) ^ 2) (Set.uIcc (0 : ℝ) 1) :=
    ContinuousOn.div continuousOn_const (by fun_prop) (fun s hs => pow_ne_zero 2 (hpos s hs))
  have hint : ∫ s in (0 : ℝ)..1, t / (1 - s + t) ^ 2 = t / (1 - 1 + t) - t / (1 - 0 + t) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s => t / (1 - s + t)) ?_
      hc.intervalIntegrable
    intro s hs
    have h1 : HasDerivAt (fun s : ℝ => 1 - s + t) (-1) s := by
      simpa using ((hasDerivAt_id s).const_sub 1).add_const t
    have h2 := (hasDerivAt_const s t).fun_div h1 (hpos s hs)
    have h3 : (0 * (1 - s + t) - t * -1) / (1 - s + t) ^ 2 = t / (1 - s + t) ^ 2 := by ring
    exact h3 ▸ h2
  rw [Set.uIcc_of_le zero_le_one] at hc
  rw [← ofReal_integral_eq_lintegral_ofReal (hc.integrableOn_compact isCompact_Icc)
    (Filter.Eventually.of_forall fun s => by positivity), integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le zero_le_one, hint]
  apply ENNReal.ofReal_le_one.2
  have : 0 ≤ t / (1 - 0 + t) := by positivity
  have h3 : t / (1 - 1 + t) = 1 := by
    rw [sub_self, zero_add, div_self ht.ne']
  linarith

theorem tendsto_lintegral_concKernel_mul_zero :
    ∀ (M : Type) [TopologicalSpace M] [T2Space M] [MeasurableSpace M] [BorelSpace M] (ν : Measure M) (K : Set M) (v D : M → ℝ) (C : ENNReal),
    IsCompact K → ContinuousOn v K → ContinuousOn D K → (∀ z ∈ K, v z = 1 → D z = 0) → C ≠ ⊤ →
    Measure.map v (ν.restrict K) ≤ C • volume.restrict (Set.Icc (0 : ℝ) 1) →
    Filter.Tendsto (fun t : ℝ => ∫⁻ z in K, ENNReal.ofReal (t / (1 - v z + t) ^ 2 * D z) ∂ν) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  intro M _ _ _ _ ν K v D C hK hv hD h0 hC hle
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hvm : AEMeasurable v (ν.restrict K) := hv.aemeasurable hKm
  have hmap : ∀ f : ℝ → ENNReal, Measurable f →
      ∫⁻ z in K, f (v z) ∂ν ≤ C * ∫⁻ s in Set.Icc (0 : ℝ) 1, f s := by
    intro f hf
    rw [← lintegral_map' hf.aemeasurable hvm]
    refine (lintegral_mono' hle le_rfl).trans ?_
    rw [lintegral_smul_measure, smul_eq_mul]
  have hone : ∫⁻ _z in K, (1 : ENNReal) ∂ν ≤ C := by
    have := hmap (fun _ => 1) measurable_const
    simpa using this
  have hae : ∀ᵐ z ∂(ν.restrict K), v z ∈ Set.Icc (0 : ℝ) 1 := by
    apply ae_of_ae_map hvm (p := fun s => s ∈ Set.Icc (0 : ℝ) 1)
    apply Measure.AbsolutelyContinuous.ae_le (Measure.absolutelyContinuous_of_le_smul hle)
    exact ae_restrict_mem measurableSet_Icc
  obtain ⟨Mx, hMx⟩ := hK.exists_bound_of_continuousOn hD
  have key : ∀ δ : ℝ, 0 < δ → ∃ B : ℝ, ∀ t : ℝ, 0 < t →
      ∫⁻ z in K, ENNReal.ofReal (t / (1 - v z + t) ^ 2 * D z) ∂ν ≤
        ENNReal.ofReal (δ + B * t) * C := by
    intro δ hδ
    have hS : IsCompact (K ∩ D ⁻¹' Set.Ici δ) :=
      hK.of_isClosed_subset (hD.preimage_isClosed_of_isClosed hK.isClosed isClosed_Ici)
        Set.inter_subset_left
    obtain ⟨η, hη, hηS⟩ : ∃ η : ℝ, 0 < η ∧ ∀ z ∈ K ∩ D ⁻¹' Set.Ici δ, η ≤ |1 - v z| := by
      apply hS.exists_forall_le' (f := fun z => |1 - v z|)
      · exact (continuousOn_const.sub (hv.mono Set.inter_subset_left)).abs
      · rintro z ⟨hz, hz'⟩
        refine abs_pos.2 fun h => ?_
        have := h0 z hz (by linarith)
        simp only [Set.mem_preimage, Set.mem_Ici] at hz'
        linarith
    refine ⟨|Mx| / η ^ 2, fun t ht => ?_⟩
    have hB : 0 ≤ |Mx| / η ^ 2 * t := by positivity
    have hf : Measurable fun s : ℝ => ENNReal.ofReal (t / (1 - s + t) ^ 2) := by fun_prop
    calc ∫⁻ z in K, ENNReal.ofReal (t / (1 - v z + t) ^ 2 * D z) ∂ν
        ≤ ∫⁻ z in K, (ENNReal.ofReal (|Mx| / η ^ 2 * t) * 1 +
            ENNReal.ofReal δ * ENNReal.ofReal (t / (1 - v z + t) ^ 2)) ∂ν := by
          refine lintegral_mono_ae ?_
          filter_upwards [hae, ae_restrict_mem hKm] with z hz hzK
          have hk : 0 ≤ t / (1 - v z + t) ^ 2 := by positivity
          rw [mul_one, ← ENNReal.ofReal_mul hδ.le, ← ENNReal.ofReal_add hB (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          by_cases hd : δ ≤ D z
          · have h1 := hηS z ⟨hzK, hd⟩
            rw [abs_of_nonneg (by linarith [hz.2])] at h1
            have h2 : t / (1 - v z + t) ^ 2 ≤ t / η ^ 2 := by
              gcongr
              linarith
            have h3 : D z ≤ |Mx| := (le_abs_self _).trans ((hMx z hzK).trans (le_abs_self _))
            have h4 : t / (1 - v z + t) ^ 2 * D z ≤ t / η ^ 2 * |Mx| :=
              mul_le_mul h2 h3 (by linarith) (by positivity)
            have h5 : t / η ^ 2 * |Mx| = |Mx| / η ^ 2 * t := by ring
            have h6 : 0 ≤ δ * (t / (1 - v z + t) ^ 2) := by positivity
            linarith
          · push_neg at hd
            nlinarith
      _ = ENNReal.ofReal (|Mx| / η ^ 2 * t) * ∫⁻ _z in K, (1 : ENNReal) ∂ν +
            ENNReal.ofReal δ * ∫⁻ z in K, ENNReal.ofReal (t / (1 - v z + t) ^ 2) ∂ν := by
          rw [lintegral_add_left measurable_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal (|Mx| / η ^ 2 * t) * C + ENNReal.ofReal δ * C := by
          gcongr
          refine (hmap _ hf).trans ?_
          calc _ ≤ C * 1 := by gcongr; exact lintegral_concKernel_le_one ht
            _ = C := mul_one C
      _ = _ := by
          rw [ENNReal.ofReal_add hδ.le hB]; ring
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hT : Filter.Tendsto (fun x : ℝ => ENNReal.ofReal x * C) (nhds 0) (nhds 0) := by
    have h1 : Filter.Tendsto (fun x : ℝ => ENNReal.ofReal x) (nhds 0) (nhds 0) := by
      simpa using ENNReal.continuous_ofReal.tendsto 0
    simpa using ENNReal.Tendsto.mul_const h1 (Or.inr hC)
  have hev := hT.eventually (gt_mem_nhds hε)
  obtain ⟨r, hr, hrb⟩ := Metric.eventually_nhds_iff.1 hev
  obtain ⟨B, hB⟩ := key (r / 2) (by positivity)
  have hT2 : Filter.Tendsto (fun t : ℝ => r / 2 + B * t) (nhdsWithin 0 (Set.Ioi 0)) (nhds (r / 2)) := by
    apply Filter.Tendsto.mono_left _ nhdsWithin_le_nhds
    have : Continuous (fun t : ℝ => r / 2 + B * t) := by fun_prop
    simpa using this.tendsto 0
  have hmem : Metric.ball (0 : ℝ) r ∈ nhds (r / 2) := by
    apply Metric.isOpen_ball.mem_nhds
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
    linarith
  filter_upwards [hT2.eventually hmem, self_mem_nhdsWithin] with t h1 h2
  exact (hB t h2).trans (hrb h1).le

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoRankDivPowOfChooseBounds
section
open Filter Topology

namespace GlobalTheory

theorem tendsto_div_add_const_pow_div_pow (e K : ℝ) (he : e ≠ 0) (D : ℕ) :
    Tendsto (fun m : ℕ => ((m : ℝ) / e + K) ^ D / (m : ℝ) ^ D) atTop (𝓝 ((1 / e) ^ D)) := by
  have h1 : Tendsto (fun m : ℕ => (1 / e + K / (m : ℝ)) ^ D) atTop (𝓝 ((1 / e) ^ D)) := by
    have := ((tendsto_const_div_atTop_nhds_zero_nat K).const_add (1 / e)).pow D
    simpa using this
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with m hm
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [← div_pow]
  congr 1
  field_simp

theorem tendsto_rank_div_pow_of_choose_bounds (D e δ : ℕ) (r : ℕ → ℕ) (he : 0 < e)
    (h : ∀ s : ℕ, s < e → ∃ c c' : ℕ, ∀ q : ℕ,
      δ * (q + D).choose D ≤ r (e * (q + c) + s) ∧ r (e * q + s) ≤ δ * (q + c' + D).choose D) :
    Tendsto (fun m : ℕ => (r m : ℝ) / (m : ℝ) ^ D) atTop
      (𝓝 (δ / ((e : ℝ) ^ D * D.factorial))) := by
  choose! c c' hc using h
  set C := ∑ s ∈ Finset.range e, c s with hC
  set C' := ∑ s ∈ Finset.range e, c' s with hC'
  have hcC : ∀ s, s < e → c s ≤ C := fun s hs =>
    Finset.single_le_sum (f := c) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hs)
  have hcC' : ∀ s, s < e → c' s ≤ C' := fun s hs =>
    Finset.single_le_sum (f := c') (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hs)
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have hDf : (0 : ℝ) < D.factorial := by exact_mod_cast D.factorial_pos
  have hlim : ∀ K : ℝ, Tendsto (fun m : ℕ => (δ : ℝ) / D.factorial *
      (((m : ℝ) / e + K) ^ D / (m : ℝ) ^ D)) atTop (𝓝 (δ / ((e : ℝ) ^ D * D.factorial))) := by
    intro K
    have := (tendsto_div_add_const_pow_div_pow e K heR.ne' D).const_mul ((δ : ℝ) / D.factorial)
    convert this using 2
    rw [div_pow, one_pow]
    field_simp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (hlim (-(C : ℝ))) (hlim ((C' + D : ℕ) : ℝ)) ?_ ?_
  · filter_upwards [eventually_ge_atTop (e * C + 1)] with m hm
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have hs : m % e < e := Nat.mod_lt _ he
    have hm_eq : e * (m / e) + m % e = m := Nat.div_add_mod m e
    have hqC : C ≤ m / e := (Nat.le_div_iff_mul_le he).2 (by nlinarith)
    have hcs := hcC (m % e) hs
    have h1 := (hc (m % e) hs (m / e - c (m % e))).1
    rw [Nat.sub_add_cancel (by omega : c (m % e) ≤ m / e), hm_eq] at h1
    have h2 := Nat.pow_le_choose (α := ℝ) D (m / e - c (m % e) + D)
    have h3 : m / e - c (m % e) + D + 1 - D = m / e - c (m % e) + 1 := by omega
    rw [h3] at h2
    have hmR : (m : ℝ) = e * ((m / e : ℕ) : ℝ) + ((m % e : ℕ) : ℝ) := by exact_mod_cast hm_eq.symm
    have hsR : ((m % e : ℕ) : ℝ) < e := by exact_mod_cast hs
    have hlt : (m : ℝ) / e < ((m / e : ℕ) : ℝ) + 1 := by
      rw [div_lt_iff₀ heR]; nlinarith
    have hge : (C : ℝ) ≤ (m : ℝ) / e := by
      rw [le_div_iff₀ heR]
      have : ((e * C : ℕ) : ℝ) ≤ m := by exact_mod_cast (show e * C ≤ m by omega)
      push_cast at this; linarith
    have hcsR : (c (m % e) : ℝ) ≤ C := by exact_mod_cast hcs
    have hx : (m : ℝ) / e + -(C : ℝ) ≤ ((m / e - c (m % e) + 1 : ℕ) : ℝ) := by
      rw [Nat.cast_add, Nat.cast_sub (by omega), Nat.cast_one]; linarith
    have hx0 : 0 ≤ (m : ℝ) / e + -(C : ℝ) := by linarith
    have hA : (δ : ℝ) / D.factorial * ((m : ℝ) / e + -(C : ℝ)) ^ D ≤ r m := by
      calc (δ : ℝ) / D.factorial * ((m : ℝ) / e + -(C : ℝ)) ^ D
          ≤ (δ : ℝ) / D.factorial * (((m / e - c (m % e) + 1 : ℕ) : ℝ)) ^ D := by gcongr
        _ = (δ : ℝ) * ((((m / e - c (m % e) + 1 : ℕ) : ℝ)) ^ D / D.factorial) := by ring
        _ ≤ (δ : ℝ) * ((m / e - c (m % e) + D).choose D : ℝ) := by gcongr
        _ ≤ r m := by exact_mod_cast h1
    calc (δ : ℝ) / D.factorial * (((m : ℝ) / e + -(C : ℝ)) ^ D / (m : ℝ) ^ D)
        = (δ : ℝ) / D.factorial * ((m : ℝ) / e + -(C : ℝ)) ^ D / (m : ℝ) ^ D := by ring
      _ ≤ (r m : ℝ) / (m : ℝ) ^ D := by gcongr
  · filter_upwards [eventually_ge_atTop 1] with m hm
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have hs : m % e < e := Nat.mod_lt _ he
    have hm_eq : e * (m / e) + m % e = m := Nat.div_add_mod m e
    have h1 := (hc (m % e) hs (m / e)).2
    rw [hm_eq] at h1
    have h2 := Nat.choose_le_pow_div (α := ℝ) D (m / e + c' (m % e) + D)
    have hmR : (m : ℝ) = e * ((m / e : ℕ) : ℝ) + ((m % e : ℕ) : ℝ) := by exact_mod_cast hm_eq.symm
    have hs0 : (0 : ℝ) ≤ ((m % e : ℕ) : ℝ) := Nat.cast_nonneg _
    have hle : ((m / e : ℕ) : ℝ) ≤ (m : ℝ) / e := by
      rw [le_div_iff₀ heR]; nlinarith
    have hcsR : (c' (m % e) : ℝ) ≤ C' := by exact_mod_cast hcC' (m % e) hs
    have hx : ((m / e + c' (m % e) + D : ℕ) : ℝ) ≤ (m : ℝ) / e + ((C' + D : ℕ) : ℝ) := by
      push_cast; linarith
    have hA : (r m : ℝ) ≤ (δ : ℝ) / D.factorial * ((m : ℝ) / e + ((C' + D : ℕ) : ℝ)) ^ D := by
      calc (r m : ℝ) ≤ (δ : ℝ) * ((m / e + c' (m % e) + D).choose D : ℝ) := by exact_mod_cast h1
        _ ≤ (δ : ℝ) * (((m / e + c' (m % e) + D : ℕ) : ℝ) ^ D / D.factorial) := by gcongr
        _ = (δ : ℝ) / D.factorial * (((m / e + c' (m % e) + D : ℕ) : ℝ)) ^ D := by ring
        _ ≤ _ := by gcongr
    calc (r m : ℝ) / (m : ℝ) ^ D
        ≤ (δ : ℝ) / D.factorial * ((m : ℝ) / e + ((C' + D : ℕ) : ℝ)) ^ D / (m : ℝ) ^ D := by gcongr
      _ = _ := by ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorCentralizerInjectiveCommutantEq
section
open scoped TensorProduct Classical

namespace GlobalTheory

theorem tensor_centralizer_flat : ∀ (K : Type) [Field K] [Algebra ℚ K] (C : Type) [Ring C] [Algebra ℚ C] (y : C),
    Function.Injective (Algebra.TensorProduct.map (AlgHom.id K K) (Subalgebra.centralizer ℚ ({y} : Set C)).val) ∧
    ∀ w : K ⊗[ℚ] C, Commute w ((1 : K) ⊗ₜ[ℚ] y) → ∃ w' : K ⊗[ℚ] (Subalgebra.centralizer ℚ ({y} : Set C)),
      Algebra.TensorProduct.map (AlgHom.id K K) (Subalgebra.centralizer ℚ ({y} : Set C)).val w' = w := by
  intro K _ _ C _ _ y
  set Z := Subalgebra.centralizer ℚ ({y} : Set C) with hZ
  have hmap : ∀ w', Algebra.TensorProduct.map (AlgHom.id K K) Z.val w'
      = LinearMap.lTensor K Z.val.toLinearMap w' := by
    intro w'
    induction w' using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add a b ha hb => simp only [map_add, ha, hb]
  let ad : C →ₗ[ℚ] C := LinearMap.mulRight ℚ y - LinearMap.mulLeft ℚ y
  have hex : Function.Exact Z.val.toLinearMap ad := by
    intro x
    constructor
    · intro hx
      refine ⟨⟨x, ?_⟩, rfl⟩
      rw [Subalgebra.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      subst hg
      have : x * g - g * x = 0 := by simpa [ad] using hx
      exact (sub_eq_zero.mp this).symm
    · rintro ⟨z, rfl⟩
      have hz := z.2
      rw [Subalgebra.mem_centralizer_iff] at hz
      have := hz y (Set.mem_singleton y)
      simp [ad, this]
  have hexK := Module.Flat.lTensor_exact K hex
  have hadK : ∀ w : K ⊗[ℚ] C, LinearMap.lTensor K ad w = w * ((1 : K) ⊗ₜ[ℚ] y) - ((1 : K) ⊗ₜ[ℚ] y) * w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [ad, TensorProduct.tmul_sub]
    | add a b ha hb => rw [map_add, ha, hb, add_mul, mul_add]; abel
  refine ⟨?_, ?_⟩
  · intro a b hab
    rw [hmap, hmap] at hab
    exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective hab
  · intro w hw
    have h0 : LinearMap.lTensor K ad w = 0 := by
      rw [hadK, hw.eq, sub_self]
    obtain ⟨w', hw'⟩ := (hexK w).mp h0
    exact ⟨w', by rw [hmap]; exact hw'⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorQuotientOntoAndInjectiveModIdealPow
section
namespace GlobalTheory

open TensorProduct

set_option maxHeartbeats 1000000 in

theorem quot_tensor_level : ∀ (R : Type) [CommRing R] (I : Ideal R) (R' : Type) [CommRing R'] [Algebra R R'] (C' : Type) [CommRing C'] [Algebra R C'] [Algebra R' C'] [IsScalarTower R R' C'] (O : Type) [CommRing O] [Algebra R O] (i : ∀ e : ℕ, O →ₐ[R] C' ⧸ (I ^ (e + 1)).map (algebraMap R C')), (∀ e, Function.Surjective (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) ∧ RingHom.ker (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) = (I ^ (e + 1)).map (algebraMap R (TensorProduct R O R'))) → ∀ (C : Subalgebra R C') (gm : ∀ e : ℕ, (O ⧸ (I ^ (e + 1)).map (algebraMap R O)) ≃ₐ[R] (C ⧸ (I ^ (e + 1)).map (algebraMap R C))), (∀ e (x : O) (c : C), gm e (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ c → Ideal.Quotient.mk ((I ^ (e + 1)).map (algebraMap R C')) (c : C') = i e x) → (∀ y : C', ∃ t : TensorProduct R C R', y - Algebra.TensorProduct.lift (Algebra.ofId C C') (IsScalarTower.toAlgHom R R' C') (fun _ _ => Commute.all _ _) t ∈ (I.map (algebraMap R C)).map (algebraMap C C')) ∧ ∀ (n : ℕ) (t : TensorProduct R C R'), Algebra.TensorProduct.lift (Algebra.ofId C C') (IsScalarTower.toAlgHom R R' C') (fun _ _ => Commute.all _ _) t ∈ ((I.map (algebraMap R C)) ^ n).map (algebraMap C C') → t ∈ ((I.map (algebraMap R C)) ^ n).map (algebraMap C (TensorProduct R C R')) := by
  intro R _ I R' _ _ C' _ _ _ _ O _ _ i hi C gm hcomp

  have hJ : ∀ k : ℕ, ((I.map (algebraMap R C)) ^ k).map (algebraMap C C') =
      (I ^ k).map (algebraMap R C') := by
    intro k
    rw [← Ideal.map_pow, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  set φ := Algebra.TensorProduct.lift (Algebra.ofId C C') (IsScalarTower.toAlgHom R R' C')
    (fun _ _ => Commute.all _ _) with hφ
  have hφt : ∀ (c : C) (r : R'), φ (c ⊗ₜ r) = (c : C') * algebraMap R' C' r := by
    intro c r
    simp [φ, Algebra.TensorProduct.lift_tmul]
  refine ⟨?_, ?_⟩
  · intro y
    have key : ∀ s : O ⊗[R] R', ∃ t : C ⊗[R] R',
        Algebra.TensorProduct.lift (i 0) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C'))
          (fun _ _ => Commute.all _ _) s = Ideal.Quotient.mk _ (φ t) := by
      intro s
      induction s using TensorProduct.induction_on with
      | zero => exact ⟨0, by simp⟩
      | tmul x r =>
        obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (gm 0 (Ideal.Quotient.mk _ x))
        refine ⟨c ⊗ₜ r, ?_⟩
        rw [Algebra.TensorProduct.lift_tmul, hφt, ← hcomp 0 x c hc.symm]
        simp [map_mul]
      | add a b ha hb =>
        obtain ⟨ta, hta⟩ := ha
        obtain ⟨tb, htb⟩ := hb
        exact ⟨ta + tb, by rw [map_add, hta, htb, map_add, map_add]⟩
    obtain ⟨s, hs⟩ := (hi 0).1 (Ideal.Quotient.mk _ y)
    obtain ⟨t, ht⟩ := key s
    refine ⟨t, ?_⟩
    have h1 := (Ideal.Quotient.eq).1 (hs.symm.trans ht)
    have h2 := hJ 1
    rw [pow_one] at h2
    rw [h2]
    simpa using h1
  · intro n t ht
    cases n with
    | zero =>
      rw [pow_zero, Ideal.one_eq_top, Ideal.map_top]
      exact Submodule.mem_top
    | succ e =>
    rw [← Ideal.map_pow] at ht ⊢
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq] at ht
    set K := (I ^ (e + 1)).map (algebraMap R C) with hK
    set πC : C ⊗[R] R' →ₐ[R] (C ⧸ K) ⊗[R] R' :=
      Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R K) (AlgHom.id R R') with hπC
    have hker : RingHom.ker πC = K.map (Algebra.TensorProduct.includeLeft : C →ₐ[R] C ⊗[R] R') := by
      rw [Algebra.TensorProduct.rTensor_ker _ (Ideal.Quotient.mkₐ_surjective R K)]
      congr 1
      ext a
      simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
    have hinc : K.map (Algebra.TensorProduct.includeLeft : C →ₐ[R] C ⊗[R] R') =
        K.map (algebraMap C (C ⊗[R] R')) := by
      have : ((Algebra.TensorProduct.includeLeft : C →ₐ[R] C ⊗[R] R') : C →+* C ⊗[R] R') =
          algebraMap C (C ⊗[R] R') := by
        ext c
        simp [Algebra.TensorProduct.algebraMap_apply]
      rw [← this]
      rfl
    have hvan : ∀ a ∈ K, ((Ideal.Quotient.mkₐ R ((I ^ (e + 1)).map (algebraMap R C'))).comp C.val) a = 0 := by
      intro a ha
      rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
      have : (a : C') ∈ K.map (algebraMap C C') := Ideal.mem_map_of_mem _ ha
      rwa [hK, Ideal.map_map, ← IsScalarTower.algebraMap_eq] at this
    set Λ : (C ⧸ K) ⊗[R] R' →ₐ[R] C' ⧸ (I ^ (e + 1)).map (algebraMap R C') :=
      Algebra.TensorProduct.lift (Ideal.Quotient.liftₐ K _ hvan)
        ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) (fun _ _ => Commute.all _ _) with hΛ
    have hL : ∀ c : C, Ideal.Quotient.liftₐ K _ hvan (Ideal.Quotient.mk K c) =
        Ideal.Quotient.mk ((I ^ (e + 1)).map (algebraMap R C')) (c : C') := fun c => rfl
    set G : O ⊗[R] R' →ₐ[R] (C ⧸ K) ⊗[R] R' :=
      Algebra.TensorProduct.map ((gm e).toAlgHom.comp (Ideal.Quotient.mkₐ R _)) (AlgHom.id R R') with hG
    have hGs : Function.Surjective G :=
      Algebra.TensorProduct.map_surjective _ _
        ((gm e).surjective.comp (Ideal.Quotient.mkₐ_surjective R _)) Function.surjective_id
    have hΛG : ∀ s, Λ (G s) = Algebra.TensorProduct.lift (i e)
        ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) (fun _ _ => Commute.all _ _) s := by
      intro s
      induction s using TensorProduct.induction_on with
      | zero => simp
      | tmul x r =>
        obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (gm e (Ideal.Quotient.mk _ x))
        have hc' := hcomp e x c hc.symm
        simp only [G, Λ, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul]
        show Ideal.Quotient.liftₐ K _ hvan (gm e (Ideal.Quotient.mk _ x)) * _ = _
        rw [← hc, ← hc']
        congr 1
      | add a b ha hb => rw [map_add, map_add, ha, hb, map_add]
    have hΛπ' : Λ.comp πC = (Ideal.Quotient.mkₐ R _).comp (φ.restrictScalars R) := by
      refine Algebra.TensorProduct.ext' fun c r => ?_
      simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, πC, Λ, Algebra.TensorProduct.map_tmul,
        Algebra.TensorProduct.lift_tmul, hφt]
      rw [map_mul]
      congr 1
    have hΛπ : ∀ u, Λ (πC u) = Ideal.Quotient.mk _ (φ u) := fun u => by
      have := congrArg (fun f => f u) hΛπ'
      simpa using this
    obtain ⟨s, hs⟩ := hGs (πC t)
    have hs0 : s ∈ RingHom.ker (Algebra.TensorProduct.lift (i e)
        ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) (fun _ _ => Commute.all _ _)) := by
      rw [RingHom.mem_ker, ← hΛG, hs, hΛπ, Ideal.Quotient.eq_zero_iff_mem]
      exact ht
    rw [(hi e).2] at hs0
    have hGz : G s = 0 := by
      have hle : (I ^ (e + 1)).map (algebraMap R (O ⊗[R] R')) ≤ RingHom.ker G.toRingHom := by
        rw [Ideal.map_le_iff_le_comap]
        intro a ha
        rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes,
          IsScalarTower.algebraMap_apply R (C ⧸ K) ((C ⧸ K) ⊗[R] R'), ← Ideal.Quotient.mk_algebraMap,
          Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ ha), map_zero]
      exact hle hs0
    rw [← hinc, ← hker, RingHom.mem_ker, ← hs, hGz]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorRatAlgebraDecompFactorwise
section
open scoped TensorProduct

namespace GlobalTheory

theorem tensor_decomp_factorwise : ∀ (S F B : Type) [Field S] [CharZero S] [Field F] [Algebra ℚ F] [FiniteDimensional ℚ F] [Ring B]
    [Algebra F B] [Algebra ℚ B] [IsScalarTower ℚ F B],
    ∃ (ι : Type) (_ : Fintype ι) (L : ι → Type) (_ : ∀ i, Field (L i)) (_ : ∀ i, CharZero (L i))
      (_ : ∀ i, Algebra F (L i)) (Φ : S ⊗[ℚ] B ≃+* ((i : ι) → L i ⊗[F] B)) (ψ : S ⊗[ℚ] F ≃+* ((i : ι) → L i)),
      (∀ b : B, Φ ((1 : S) ⊗ₜ[ℚ] b) = fun i => (1 : L i) ⊗ₜ[F] b) ∧
      (∀ z : S ⊗[ℚ] F, Φ (Algebra.TensorProduct.map (AlgHom.id S S) (IsScalarTower.toAlgHom ℚ F B) z) =
        fun i => algebraMap (L i) (L i ⊗[F] B) (ψ z i)) := by
  intro S F B _ _ _ _ _ _ _ _ _
  haveI hEt : Algebra.Etale ℚ F := by
    haveI : Algebra.IsSeparable ℚ F := inferInstance
    haveI : Algebra.FormallyEtale ℚ F := Algebra.FormallyEtale.of_isSeparable ℚ F
    haveI : Algebra.FinitePresentation ℚ F := Algebra.FinitePresentation.of_finiteType.mp inferInstance
    constructor <;> infer_instance
  haveI : Algebra.Etale S (S ⊗[ℚ] F) := Algebra.Etale.baseChange ℚ F S
  obtain ⟨I, hI, L, hL, hAL, e, -⟩ := (Algebra.Etale.iff_exists_algEquiv_prod S (S ⊗[ℚ] F)).mp this
  letI : Fintype I := Fintype.ofFinite I
  classical
  let ψ : S ⊗[ℚ] F ≃+* ((i : I) → L i) := e.toRingEquiv
  letI instF : ∀ i, Algebra F (L i) := fun i =>
    ((Pi.evalRingHom L i).comp (ψ.toRingHom.comp
      (Algebra.TensorProduct.includeRight : F →ₐ[ℚ] S ⊗[ℚ] F).toRingHom)).toAlgebra
  have hchar : ∀ i, CharZero (L i) := fun i =>
    charZero_of_injective_algebraMap (R := S) (algebraMap S (L i)).injective
  let φ : F ⊗[ℚ] S ≃ₐ[F] ((i : I) → L i) :=
    AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm ℚ F S).toRingEquiv.trans ψ) (fun x => by
      funext i
      rfl)
  let c : B ⊗[ℚ] S ≃ₐ[F] B ⊗[F] (F ⊗[ℚ] S) :=
    AlgEquiv.ofLinearEquiv (TensorProduct.AlgebraTensorModule.cancelBaseChange ℚ F F B S).symm
      (by simp [Algebra.TensorProduct.one_def])
      (LinearMap.map_mul_of_map_mul_tmul (fun _ _ _ _ ↦ by simp))
  let Φ : S ⊗[ℚ] B ≃+* ((i : I) → L i ⊗[F] B) :=
    (Algebra.TensorProduct.comm ℚ S B).toRingEquiv.trans <| c.toRingEquiv.trans <|
      (Algebra.TensorProduct.congr (AlgEquiv.refl : B ≃ₐ[F] B) φ).toRingEquiv.trans <|
      (Algebra.TensorProduct.piRight F F B L).toRingEquiv.trans
      (AlgEquiv.piCongrRight fun i => Algebra.TensorProduct.comm F B (L i)).toRingEquiv
  have hΦ : ∀ (s : S) (b : B), Φ (s ⊗ₜ b) = fun i => ψ (s ⊗ₜ 1) i ⊗ₜ[F] b := by
    intro s b
    have hc : c (b ⊗ₜ s) = b ⊗ₜ ((1 : F) ⊗ₜ s) :=
      TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul ℚ F F b s
    show (AlgEquiv.piCongrRight fun i => Algebra.TensorProduct.comm F B (L i))
      ((Algebra.TensorProduct.piRight F F B L)
        ((Algebra.TensorProduct.congr (AlgEquiv.refl : B ≃ₐ[F] B) φ) (c (b ⊗ₜ s)))) = _
    rw [hc]
    rfl
  refine ⟨I, inferInstance, L, hL, hchar, instF, Φ, ψ, ?_, ?_⟩
  · intro b
    rw [hΦ]
    funext i
    rw [← Algebra.TensorProduct.one_def, map_one, Pi.one_apply]
  · intro z
    induction z using TensorProduct.induction_on with
    | zero => funext i; simp
    | add x y hx hy =>
      rw [map_add, map_add, hx, hy]
      funext i
      simp only [Pi.add_apply, map_add]
    | tmul s f =>
      have key : ∀ i, (algebraMap F (L i) f) * ψ (s ⊗ₜ 1) i = ψ (s ⊗ₜ f) i := by
        intro i
        show ψ (1 ⊗ₜ f) i * ψ (s ⊗ₜ 1) i = _
        rw [← Pi.mul_apply, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, IsScalarTower.coe_toAlgHom', hΦ]
      funext i
      rw [Algebra.algebraMap_eq_smul_one f, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
        Algebra.smul_def, key, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
        RingHom.id_apply]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhiskerLeftLeftIsPullbackSnd
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem whiskerLeft_left_isPullback_snd (S : Scheme.{0}) (U T T' : Over S) (f : T' ⟶ T) :
    IsPullback (U ◁ f).left (snd U T').left (snd U T).left f.left := by
  have hw : (U ◁ f).left ≫ (snd U T).left = (snd U T').left ≫ f.left := by
    rw [← Over.comp_left, ← Over.comp_left, whiskerLeft_snd]
  refine IsPullback.of_right (h₁₂ := (fst U T).left) (h₂₂ := T.hom) (v₁₃ := U.hom) ?_ hw ?_
  · have h1 : (U ◁ f).left ≫ (fst U T).left = (fst U T').left := by
      rw [← Over.comp_left, whiskerLeft_fst]
    have h2 : f.left ≫ T.hom = T'.hom := Over.w f
    rw [h1, h2, Over.fst_left, Over.snd_left]
    exact IsPullback.of_hasPullback U.hom T'.hom
  · rw [Over.fst_left, Over.snd_left]
    exact IsPullback.of_hasPullback U.hom T.hom

end GlobalTheory
end

