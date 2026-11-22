import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0845
import Formalism.LocalToGlobal.ProjectiveLattices.SatLeaves
import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0040
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0029
import GroundTheory.GlobalFields.Adele.Bundle0001
import GroundTheory.GlobalFields.Adele.Approximation
import Formalism.LocalToGlobal.InertKernelTheory.StatementAlg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0847
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0777
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0764
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkGLOneCorner
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0848
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeHomEqOfTangentEqStatement
section
open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_hom_eq_of_tangent_eq : ∀ (k : Type) [Field k] [CharZero k] (A B : Over (Sp k)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B], IsAbelianScheme A → IsAbelianScheme B → ∀ (f f' : A ⟶ B) [IsMonHom f] [IsMonHom f'], (∀ v : overAt (𝟙 (Sp k)) (DualNumber k) ⟶ A, smT (𝟙 (Sp k)) 0 v = 1 → v ≫ f = v ≫ f') → f = f' := by
  first | exact @GlobalTheory.LieFaithful.hom_eq_of_tangent_eq | exact GlobalTheory.LieFaithful.hom_eq_of_tangent_eq | (intros; apply GlobalTheory.LieFaithful.hom_eq_of_tangent_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveStrongApproximationAvoidingFinset
section
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct
open Filter

namespace GlobalTheory.AddApproxPlaces

open NumberField.mixedEmbedding MeasureTheory in

theorem exists_small_of_infinitePlace (F : Type) [Field F] [NumberField F] (w₀ : InfinitePlace F)
    (f : InfinitePlace F → NNReal) (hf : ∀ w, f w ≠ 0) :
    ∃ g : F, g ≠ 0 ∧ (∀ w : InfinitePlace F, w ≠ w₀ → w g < f w) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F g ≤ 1 := by
  classical
  obtain ⟨g, hg, hB⟩ := adjust_f F (f := f) (w₁ := w₀) ((minkowskiBound F 1).toNNReal + 1) (fun w _ => hf w)
  have h : minkowskiBound F 1 < volume (convexBodyLT F g) := by
    rw [convexBodyLT_volume, hB, ← ENNReal.coe_toNNReal (minkowskiBound_lt_top F 1).ne, ← ENNReal.coe_mul,
      ENNReal.coe_lt_coe, ENNReal.toNNReal_coe]
    exact (lt_add_one _).trans_le (le_mul_of_one_le_left zero_le (one_le_convexBodyLTFactor F))
  obtain ⟨a, ha, hlt⟩ := exists_ne_zero_mem_ringOfIntegers_lt F h
  refine ⟨a, RingOfIntegers.coe_ne_zero_iff.2 ha, fun w hw => ?_, fun v => v.valuation_le_one a⟩
  rw [← hg w hw]; exact hlt w

open NumberField.mixedEmbedding MeasureTheory nonZeroDivisors in

theorem exists_small_of_finitePlace (F : Type) [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F))
    (f : InfinitePlace F → NNReal) (hf : ∀ w, f w ≠ 0) :
    ∃ g : F, g ≠ 0 ∧ (∀ w : InfinitePlace F, w g < f w) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), v ≠ p → v.valuation F g ≤ 1 := by
  classical
  set P : NNReal := convexBodyLTFactor F * ∏ w, (f w) ^ (w.mult) with hP
  have hP0 : 0 < P := pos_iff_ne_zero.2 (mul_ne_zero (convexBodyLTFactor_ne_zero F)
    (Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ (hf w)))
  set B : NNReal := (minkowskiBound F 1).toNNReal with hB
  have hN : (1 : ℝ) < (Ideal.absNorm p.asIdeal : ℝ) := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm p
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ((B : ℝ) / P) hN
  have hJ : ((p.asIdeal ^ k : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (pow_ne_zero _ p.ne_bot)
  let I : (FractionalIdeal (𝓞 F)⁰ F)ˣ := (Units.mk0 _ hJ)⁻¹
  have hI : minkowskiBound F I = ENNReal.ofReal (((Ideal.absNorm p.asIdeal : ℝ) ^ k)⁻¹) * minkowskiBound F 1 := by
    unfold minkowskiBound
    rw [volume_fundamentalDomain_fractionalIdealLatticeBasis F 1]
    simp only [volume_fundamentalDomain_fractionalIdealLatticeBasis, I, Units.val_inv_eq_inv_val,
      Units.val_mk0, map_inv₀, FractionalIdeal.coeIdeal_absNorm, Units.val_one, map_one, map_pow]
    simp [mul_assoc]
  have h : minkowskiBound F I < volume (convexBodyLT F f) := by
    have hpos : (0 : ℝ) < (Ideal.absNorm p.asIdeal : ℝ) ^ k := by positivity
    rw [hI, convexBodyLT_volume, ← ENNReal.coe_toNNReal (minkowskiBound_lt_top F 1).ne, ← hB, ← ENNReal.coe_mul, ← hP,
      ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_lt_ofReal_iff (by exact_mod_cast hP0), inv_mul_lt_iff₀ hpos]
    exact (div_lt_iff₀ (by exact_mod_cast hP0)).1 hk
  obtain ⟨a, ha, ha0, hlt⟩ := exists_ne_zero_mem_ideal_lt F I h
  refine ⟨a, ha0, hlt, fun v hv => ?_⟩
  have hnle : ¬ p.asIdeal ^ k ≤ v.asIdeal := fun hle =>
    hv (HeightOneSpectrum.ext (p.isMaximal.eq_of_le v.isPrime.ne_top (v.isPrime.le_of_pow_le hle)).symm)
  obtain ⟨b, hb, hbv⟩ := SetLike.not_le_iff_exists.1 hnle
  have ha' : a ∈ ((p.asIdeal ^ k : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)⁻¹ := by
    simpa [I] using ha
  have hab := (FractionalIdeal.mem_inv_iff hJ).1 ha' (algebraMap (𝓞 F) F b)
    (FractionalIdeal.mem_coeIdeal_of_mem _ hb)
  obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff _).1 hab
  have h1 : v.valuation F (algebraMap (𝓞 F) F b) = 1 :=
    le_antisymm (v.valuation_le_one b) (not_lt.1 fun h => hbv ((v.valuation_lt_one_iff_mem b).1 h))
  have h2 : v.valuation F (algebraMap (𝓞 F) F c) ≤ 1 := v.valuation_le_one c
  rwa [hc, map_mul, h1, mul_one] at h2

theorem exists_int_nhds_finite (F : Type) [Field F] [NumberField F] (N : Set (Af F)) (hN : N ∈ 𝓝 (0 : Af F)) :
    ∃ m : 𝓞 F, m ≠ 0 ∧ ∀ y : Af F,
      (∀ v, Valued.v (evalV F v y) ≤ v.valuation F (algebraMap (𝓞 F) F m)) → y ∈ N := by
  have hM : ∀ᶠ a in 𝓝 (0 : Af F), ∀ c ∈ {a : Af F | ∀ v, a v ∈ v.adicCompletionIntegers F}, a * c ∈ N := by
    refine (GlobalTheory.AdeleCocompact.isCompact_integral F).eventually_forall_of_forall_eventually fun c _ => ?_
    have hcont : Continuous (fun p : Af F × Af F => p.1 * p.2) := by fun_prop
    exact hcont.continuousAt.eventually_mem (by simpa using hN)
  obtain ⟨n, hn⟩ := ((GlobalTheory.AdelicFactorial.tendsto_factorial_finiteAdele F).eventually hM).exists
  have h0 : ((n.factorial : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.2 n.factorial_ne_zero
  refine ⟨(n.factorial : ℕ), Nat.cast_ne_zero.2 n.factorial_ne_zero, fun y hy => ?_⟩
  have e : y = ((n.factorial : ℕ) : Af F) * (algebraMap F (Af F) ((n.factorial : ℕ) : F)⁻¹ * y) := by
    rw [← mul_assoc, ← map_natCast (algebraMap F (Af F)), ← map_mul, mul_inv_cancel₀ h0, map_one, one_mul]
  rw [e]
  refine hn _ fun v => ?_
  have e' : (algebraMap F (Af F) ((n.factorial : ℕ) : F)⁻¹ * y) v =
      (((((n.factorial : ℕ) : F)⁻¹ : F)) : v.adicCompletion F) * evalV F v y := rfl
  rw [e', HeightOneSpectrum.mem_adicCompletionIntegers, map_mul,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_inv₀]
  have h1 := hy v
  rw [map_natCast] at h1
  have h2 : v.valuation F ((n.factorial : ℕ) : F) ≠ 0 := (Valuation.ne_zero_iff _).2 h0
  exact (inv_mul_le_one₀ (pos_iff_ne_zero.2 h2)).2 h1

theorem exists_delta_nhds_infinite (F : Type) [Field F] [NumberField F] (N : Set (Ainf F))
    (hN : N ∈ 𝓝 (0 : Ainf F)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y : Ainf F, (∀ w, ‖y w‖ < δ) → y ∈ N := by
  have hN' : N ∈ 𝓝 (0 : (w : InfinitePlace F) → w.Completion) := hN
  obtain ⟨δ, hδ, h⟩ := Metric.mem_nhds_iff.1 hN'
  exact ⟨δ, hδ, fun y hy => h (mem_ball_zero_iff.2 ((pi_norm_lt_iff hδ).2 hy))⟩

theorem exists_small (F : Type) [Field F] [NumberField F] (S₁ : Finset (InfinitePlace F))
    (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (hS : S₁.Nonempty ∨ S₂.Nonempty)
    (m : 𝓞 F) (hm : m ≠ 0) (δ : ℝ) (hδ : 0 < δ) :
    ∃ g : F, g ≠ 0 ∧ (∀ w, w ∉ S₁ → w g < δ) ∧
      ∀ v, v ∉ S₂ → v.valuation F g ≤ v.valuation F (algebraMap (𝓞 F) F m) := by
  have hm' : algebraMap (𝓞 F) F m ≠ 0 := RingOfIntegers.coe_ne_zero_iff.2 hm
  have hw : ∀ w : InfinitePlace F, 0 < w (algebraMap (𝓞 F) F m) := fun w => InfinitePlace.pos_iff.2 hm'
  let f : InfinitePlace F → NNReal := fun w => ⟨δ / w (algebraMap (𝓞 F) F m), (div_pos hδ (hw w)).le⟩
  have hf : ∀ w, f w ≠ 0 := fun w => NNReal.coe_ne_zero.1 (div_pos hδ (hw w)).ne'
  obtain ⟨g, hg, h1, h2⟩ : ∃ g : F, g ≠ 0 ∧ (∀ w, w ∉ S₁ → w g < f w) ∧ ∀ v, v ∉ S₂ → v.valuation F g ≤ 1 := by
    rcases hS with ⟨w₀, hw₀⟩ | ⟨p, hp⟩
    · obtain ⟨g, hg, h1, h2⟩ := exists_small_of_infinitePlace F w₀ f hf
      exact ⟨g, hg, fun w hw => h1 w (fun h => hw (h ▸ hw₀)), fun v _ => h2 v⟩
    · obtain ⟨g, hg, h1, h2⟩ := exists_small_of_finitePlace F p f hf
      exact ⟨g, hg, fun w _ => h1 w, fun v hv => h2 v (fun h => hv (h ▸ hp))⟩
  refine ⟨g * algebraMap (𝓞 F) F m, mul_ne_zero hg hm', fun w hw' => ?_, fun v hv => ?_⟩
  · rw [map_mul]
    exact (lt_div_iff₀ (hw w)).1 (h1 w hw')
  · rw [map_mul]
    exact mul_le_of_le_one_left' (h2 v hv)

theorem exists_small_adele (F : Type) [Field F] [NumberField F] (S₁ : Finset (InfinitePlace F))
    (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F) (hε : IsPlacesIdem S₁ S₂ ε)
    (hS : S₁.Nonempty ∨ S₂.Nonempty) (N : Set (AF F)) (hN : N ∈ 𝓝 (0 : AF F)) :
    ∃ f : F, f ≠ 0 ∧ (1 - ε) * algebraMap F (AF F) f ∈ N := by
  have hN' : N ∈ 𝓝 ((0 : Ainf F), (0 : Af F)) := hN
  obtain ⟨N₁, hN₁, N₂, hN₂, hsub⟩ := mem_nhds_prod_iff.1 hN'
  obtain ⟨δ, hδ, hδN⟩ := exists_delta_nhds_infinite F N₁ hN₁
  obtain ⟨m, hm, hmN⟩ := exists_int_nhds_finite F N₂ hN₂
  obtain ⟨g, hg, h1, h2⟩ := exists_small F S₁ S₂ hS m hm δ hδ
  refine ⟨g, hg, hsub ⟨?_, ?_⟩⟩
  · apply hδN
    intro w
    have e : ((1 - ε) * algebraMap F (AF F) g).1 w = (1 - fstA F ε w) * (g : w.Completion) := by
      change (fstA F ((1 - ε) * algebraMap F (AF F) g)) w = _
      rw [map_mul, map_sub, map_one, AlgHom.commutes]
      rfl
    rw [e]
    by_cases hw : w ∈ S₁
    · rw [hε.1 w hw, sub_self, zero_mul, norm_zero]; exact hδ
    · rw [hε.2.1 w hw, sub_zero, one_mul]
      have := GroundTheory.Global.norm_algebraMap_apply (K := F) g w
      exact (this.trans_lt (h1 w hw))
  · apply hmN
    intro v
    have e : evalV F v ((1 - ε) * algebraMap F (AF F) g).2 =
        (1 - evalV F v (sndA F ε)) * (g : v.adicCompletion F) := by
      change evalV F v (sndA F ((1 - ε) * algebraMap F (AF F) g)) = _
      rw [map_mul, map_mul, map_sub, map_sub, map_one, map_one, AlgHom.commutes, AlgHom.commutes]
      rfl
    rw [e]
    by_cases hv : v ∈ S₂
    · rw [hε.2.2.1 v hv, sub_self, zero_mul, map_zero]; exact zero_le'
    · rw [hε.2.2.2 v hv, sub_zero, one_mul, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      exact h2 v hv

theorem exists_approx_notMem : ∀ (F : Type) [Field F] [NumberField F], ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → ∀ (x : AF F) (U : Set (AF F)), U ∈ 𝓝 x → ∀ Z : Finset F, ∃ t : F, t ∉ Z ∧ ∃ s : AF F, algebraMap F (AF F) t + ε * s ∈ U := by
  intro F _ _ S₁ S₂ ε hε hS x U hU Z
  have hc : Tendsto (fun p : AF F × AF F => x + (p.1 + p.2)) (𝓝 ((0 : AF F), (0 : AF F))) (𝓝 x) := by
    have : Continuous (fun p : AF F × AF F => x + (p.1 + p.2)) := by fun_prop
    simpa using this.tendsto ((0 : AF F), (0 : AF F))
  obtain ⟨V₁, hV₁, V₂, hV₂, hV⟩ := mem_nhds_prod_iff.1 (hc hU)
  obtain ⟨C, hC, hCF⟩ := GlobalTheory.AdeleCocompact.exists_compact_adele F
  have hM : ∀ᶠ a in 𝓝 (0 : AF F), ∀ c ∈ C, -(a * c) ∈ V₁ := by
    refine hC.eventually_forall_of_forall_eventually fun c _ => ?_
    have hcont : Continuous (fun p : AF F × AF F => -(p.1 * p.2)) := by fun_prop
    exact hcont.continuousAt.eventually_mem (by simpa using hV₁)
  obtain ⟨f, hf, hfM⟩ := exists_small_adele F S₁ S₂ ε hε hS _ hM
  obtain ⟨t₀, ht₀⟩ := hCF (algebraMap F (AF F) f⁻¹ * x)
  set c := algebraMap F (AF F) f⁻¹ * x - algebraMap F (AF F) t₀ with hc_def
  have hd₁ : -((1 - ε) * algebraMap F (AF F) f * c) ∈ V₁ := hfM c ht₀
  have hff : algebraMap F (AF F) f * algebraMap F (AF F) f⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hf, map_one]
  have e₁ : algebraMap F (AF F) (f * t₀) + ε * (algebraMap F (AF F) f * c) =
      x + -((1 - ε) * algebraMap F (AF F) f * c) := by
    rw [hc_def, map_mul]
    linear_combination x * hff

  set n := Z.card with hn
  have hM₂ : ∀ᶠ a in 𝓝 (0 : AF F), ∀ q ∈ Finset.range (n + 1), ((q : ℕ) : AF F) * a ∈ V₂ := by
    refine (Filter.eventually_all_finset _).2 fun q _ => ?_
    have hcont : Continuous (fun a : AF F => ((q : ℕ) : AF F) * a) := by fun_prop
    exact hcont.continuousAt.eventually_mem (by simpa using hV₂)
  obtain ⟨f₂, hf₂, hf₂M⟩ := exists_small_adele F S₁ S₂ ε hε hS _ hM₂
  obtain ⟨q, hq, hqZ⟩ : ∃ q ∈ Finset.range (n + 1), f * t₀ + (q : F) * f₂ ∉ Z := by
    by_contra hcon
    push_neg at hcon
    have hinj : Set.InjOn (fun q : ℕ => f * t₀ + (q : F) * f₂) (Finset.range (n + 1) : Set ℕ) := by
      intro a _ b _ hab
      have : (a : F) * f₂ = (b : F) * f₂ := add_left_cancel hab
      exact_mod_cast mul_right_cancel₀ hf₂ this
    have := Finset.card_le_card_of_injOn _ (fun a ha => hcon a ha) hinj
    simp [hn] at this
  refine ⟨f * t₀ + (q : F) * f₂, hqZ, algebraMap F (AF F) f * c - algebraMap F (AF F) ((q : F) * f₂), ?_⟩
  have e₂ : algebraMap F (AF F) (f * t₀ + (q : F) * f₂) +
      ε * (algebraMap F (AF F) f * c - algebraMap F (AF F) ((q : F) * f₂)) =
      x + (-((1 - ε) * algebraMap F (AF F) f * c) + ((q : ℕ) : AF F) * ((1 - ε) * algebraMap F (AF F) f₂)) := by
    rw [map_add, map_mul (algebraMap F (AF F)) (q : F) f₂, map_natCast]
    linear_combination e₁
  rw [e₂]
  exact hV (Set.mk_mem_prod hd₁ (hf₂M q hq))

end GlobalTheory.AddApproxPlaces

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLatticeEqComapBlockwiseLattice
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.BaseVacuum
open Classical

namespace GlobalTheory.BaseVacuum

theorem baseLattice_eq_comap_blockwise_lattice : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (n n' : ℕ),
    TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (StandardLatticesGL3.stdL D (n * 2)) (StandardLatticesGL3.stdL D (n' * 2)) =
      (blkLat (ι := Fin n' × Fin n) (imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ))
        (pow4 B.lamM))).comap (phi B n n' : TaylorLogMetric.VC D (n * 2) (n' * 2) →ₗ[ℂ] (Ix D n n' → ℂ)).toAddMonoidHom := by
  intro D cc δ B n n'
  have h0 : TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (StandardLatticesGL3.stdL D (n * 2)) (StandardLatticesGL3.stdL D (n' * 2)) = powLat B.lamM (n * 2) (n' * 2) :=
    Lat0 D cc δ
  rw [h0]

  have himg : ∀ x : Fin 4 × D.what₂.Tau → ℂ,
      B.gC x ∈ imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM) ↔
        x ∈ pow4 B.lamM := by
    intro x
    constructor
    · rintro ⟨y, hy, hxy⟩
      have : y = x := B.gC.injective hxy
      exact this ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  ext z
  simp only [AddSubgroup.mem_comap]
  show (∀ i j, (fun τ => z τ i j) ∈ B.lamM) ↔ ∀ k, (fun w => phi B n n' z (k, w)) ∈ _
  have e : ∀ k, (fun w => phi B n n' z (k, w)) = B.gC (blk D k z) := fun k => rfl
  simp only [e, himg]
  constructor
  · intro h k a
    exact h (posE n n' (k, a)).1 (posE n n' (k, a)).2
  · intro h i j
    have := h ((posE n n').symm (i, j)).1 ((posE n n').symm (i, j)).2
    have e2 : slice ((posE n n').symm (i, j)).2 (blk D ((posE n n').symm (i, j)).1 z) = fun τ => z τ i j := by
      funext τ
      show z τ (posE n n' (((posE n n').symm (i, j)).1, ((posE n n').symm (i, j)).2)).1
        (posE n n' (((posE n n').symm (i, j)).1, ((posE n n').symm (i, j)).2)).2 = z τ i j
      simp only [Prod.mk.eta, Equiv.apply_symm_apply]
    rw [← e2]; exact this

end GlobalTheory.BaseVacuum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockVacuumCoordinateEquivIsometry
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.BaseVacuum
open Classical

open scoped BigOperators ComplexConjugate

namespace GlobalTheory.BaseVacuum

theorem gC_sum_conj {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (x y : Fin 4 × D.what₂.Tau → ℂ) :
    ∑ w, B.gC x w * conj (B.gC y w) = ∑ w, x w * conj (y w) := by
  have hA : ((Formalism.L2.Th1.F.area B.L : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Formalism.L2.Th1.F.areaPos_thm B.L).ne'
  have h := B.isomOK x y
  rw [blockFourfold_hOne_eq_hOne] at h
  have e : Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau) = matH (hOne B.L (Fin 4 × D.what₂.Tau)) := rfl
  rw [e] at h
  have h' := h
  simp only [LinearEquiv.coe_coe] at h'
  rw [matH_hOne, matH_hOne] at h'
  exact (div_left_inj' hA).1 h'

theorem phi_isom : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (n n' : ℕ)
    (z z' : TaylorLogMetric.VC D (n * 2) (n' * 2)),
    TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) z z' = stdH B.L (Ix D n n') (phi B n n' z) (phi B n n' z') := by
  intro D cc δ B n n' z z'
  have eR : Formalism.L2.Th1.H.stdH B.L (Ix D n n') (phi B n n' z) (phi B n n' z')
      = (∑ p, phi B n n' z p * conj (phi B n n' z' p)) / ((Formalism.L2.Th1.F.area B.L : ℝ) : ℂ) := by
    show matH (hOne B.L (Ix D n n')) _ _ = _
    exact matH_hOne _ _ _
  rw [eR]
  have eL : TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) z z'
      = (∑ τ, ∑ i, ∑ j, z τ i j * conj (z' τ i j)) / ((TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ) : ℝ) : ℂ) := rfl
  rw [eL, show TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ) = Formalism.L2.Th1.F.area B.L from B.areaOK]
  congr 1
  symm
  calc (∑ p, phi B n n' z p * conj (phi B n n' z' p))
      = ∑ k : Fin n' × Fin n, ∑ w, B.gC (blk D k z) w * conj (B.gC (blk D k z') w) := by
        rw [Fintype.sum_prod_type]; rfl
    _ = ∑ k : Fin n' × Fin n, ∑ w, blk D k z w * conj (blk D k z' w) :=
        Finset.sum_congr rfl (fun k _ => gC_sum_conj B (blk D k z) (blk D k z'))
    _ = ∑ p : Ix D n n', blk D p.1 z p.2 * conj (blk D p.1 z' p.2) := (Fintype.sum_prod_type' _).symm
    _ = ∑ τ, ∑ i, ∑ j, z τ i j * conj (z' τ i j) := ?_
  let e : Ix D n n' ≃ D.what₂.Tau × (Fin (n' * 2) × Fin (n * 2)) :=
    ((Equiv.prodAssoc _ _ _).symm.trans ((posE n n').prodCongr (Equiv.refl _))).trans (Equiv.prodComm _ _)
  rw [Fintype.sum_equiv e (fun p => blk D p.1 z p.2 * conj (blk D p.1 z' p.2))
    (fun q => z q.1 q.2.1 q.2.2 * conj (z' q.1 q.2.1 q.2.2)) (fun p => rfl)]
  simp only [Fintype.sum_prod_type]

end GlobalTheory.BaseVacuum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockVacuumLatticeBasisCoordinateEqCoordinateEqu
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.BaseVacuum
open Classical

noncomputable section
namespace GlobalTheory.BaseVacuum
open scoped BigOperators

theorem sum_putB_embT (D : D7) {n n' : ℕ} (k : Fin n' × Fin n) (x : Fin 4 → D.host.E) (τ : D.what₂.Tau)
    (z : TaylorLogMetric.VC D (n * 2) (n' * 2)) :
    (∑ a, ∑ c, z τ a c * (starRingEnd ℂ) (TaylorLogMetric.embT D τ (putB D k x a c)))
      = ∑ b : Fin 4, blk D k z (b, τ) * (starRingEnd ℂ) (emb4 D x (b, τ)) := by
  rw [← Fintype.sum_prod_type' (f := fun a c => z τ a c * (starRingEnd ℂ) (TaylorLogMetric.embT D τ (putB D k x a c)))]
  rw [← (posE n n').sum_comp]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single k]
  · refine Finset.sum_congr rfl fun b _ => ?_
    simp [putB, blk, emb4]
  · intro k' _ hk'
    refine Finset.sum_eq_zero fun b _ => ?_
    simp [putB, hk']
  · simp

theorem blockVacuum_coordinate_eq_coordinateEquiv_numbering (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (n n' : ℕ)
    (j : Fin (TaylorLogMetric.fF D * (n * 2) * (n' * 2))) (z : TaylorLogMetric.VC D (n * 2) (n' * 2)) :
    StandardLatticesGL3.coordB D (TaylorLogMetric.tor0 D cc δ) (bas B n n') j z = phi B n n' z (ixE D n n' j) := by
  set k := (ixE D n n' j).1
  set w := (ixE D n n' j).2
  have h1 : StandardLatticesGL3.coordB D (TaylorLogMetric.tor0 D cc δ) (bas B n n') j z
      = ∑ w', blk D k z w' * (starRingEnd ℂ) (emb4 D (xv B w) w') := by
    unfold StandardLatticesGL3.coordB
    rw [Fintype.sum_prod_type_right (f := fun w' : Fin 4 × D.what₂.Tau => blk D k z w' * (starRingEnd ℂ) (emb4 D (xv B w) w'))]
    refine Finset.sum_congr rfl fun τ _ => ?_
    exact sum_putB_embT D k (xv B w) τ z
  have hg : B.gC (emb4 D (xv B w)) = Pi.single w 1 := by
    rw [show B.gC (emb4 D (xv B w)) = _ from B.gC_spec (xv B w)]
    funext w'
    simp only [xv, LinearEquiv.apply_symm_apply]
    by_cases h : w' = w
    · subst h; simp
    · simp [Pi.single_apply, h]
  have hA : ((Formalism.L2.Th1.F.area B.L : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Formalism.L2.Th1.F.areaPos_thm B.L).ne'
  have hI := B.isomOK (blk D k z) (emb4 D (xv B w))
  rw [blockFourfold_hOne_eq_hOne] at hI
  change (matH (hOne B.L (Fin 4 × D.what₂.Tau))) (B.gC (blk D k z)) (B.gC (emb4 D (xv B w))) = _ at hI
  rw [matH_hOne, matH_hOne, div_left_inj' hA, hg] at hI
  rw [h1, ← hI, phi_apply]
  simp [Pi.single_apply]
  rfl

theorem coordB_bas_eq_phi : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (n n' : ℕ) (j : Fin (TaylorLogMetric.fF D * (n * 2) * (n' * 2))) (z : TaylorLogMetric.VC D (n * 2) (n' * 2)), StandardLatticesGL3.coordB D (TaylorLogMetric.tor0 D cc δ) (bas B n n') j z = phi B n n' z (ixE D n n' j) :=
  blockVacuum_coordinate_eq_coordinateEquiv_numbering

end GlobalTheory.BaseVacuum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockVacuumLatticeEqComapStandardLattice
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.BaseVacuum
open Classical

namespace GlobalTheory.BaseVacuum

theorem gC_xv {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (w : Fin 4 × D.what₂.Tau) :
    B.gC (fun w' => TaylorLogMetric.embT D w'.2 (xv B w w'.1)) = Pi.single w 1 := by
  rw [B.gC_spec]
  funext w'
  simp only [xv, LinearEquiv.apply_symm_apply]
  by_cases h : w' = w
  · subst h; simp
  · simp [h]

theorem blk_embV_putB (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {n n' : ℕ} (k k' : Fin n' × Fin n)
    (x : Fin 4 → D.host.E) :
    blk D k' (TaylorLogMetric.embV D (TaylorLogMetric.tor0 D cc δ) (putB D k x) : TaylorLogMetric.VC D (n * 2) (n' * 2)) =
      if k' = k then (fun w => TaylorLogMetric.embT D w.2 (x w.1)) else (0 : Fin 4 × D.what₂.Tau → ℂ) := by
  funext w
  simp only [blk, TaylorLogMetric.embV, TaylorLogMetric.tor0, putB, Prod.mk.eta, Equiv.symm_apply_apply]
  by_cases h : k' = k
  · simp [h]
  · simp [h]

theorem phi_embV_bas {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (n n' : ℕ)
    (j : Fin (TaylorLogMetric.fF D * (n * 2) * (n' * 2))) :
    phi B n n' (TaylorLogMetric.embV D (TaylorLogMetric.tor0 D cc δ) (bas B n n' j)) = Pi.single (ixE D n n' j) 1 := by
  funext p
  rw [phi_apply, bas, blk_embV_putB]
  by_cases h : p.1 = (ixE D n n' j).1
  · rw [if_pos h, gC_xv]
    by_cases h2 : p.2 = (ixE D n n' j).2
    · have : p = ixE D n n' j := Prod.ext h h2
      subst this; simp
    · have : p ≠ ixE D n n' j := fun e => h2 (by rw [e])
      simp [h2, this]
  · rw [if_neg h, B.gC.map_zero]
    have : p ≠ ixE D n n' j := fun e => h (by rw [e])
    simp [this]

theorem laB_eq_comap : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (n n' : ℕ),
    StandardLatticesGL3.LaB D (TaylorLogMetric.tor0 D cc δ) (bas B n n') =
      (stdLat B.L (Ix D n n')).comap (phi B n n' : TaylorLogMetric.VC D (n * 2) (n' * 2) →ₗ[ℂ] (Ix D n n' → ℂ)).toAddMonoidHom := by
  intro D cc δ B n n'
  apply le_antisymm
  · unfold StandardLatticesGL3.LaB
    rw [AddSubgroup.closure_le]
    rintro z ⟨w, hw, j, rfl⟩
    show phi B n n' (w • TaylorLogMetric.embV D (TaylorLogMetric.tor0 D cc δ) (bas B n n' j)) ∈ stdLat B.L (Ix D n n')
    rw [map_smul, phi_embV_bas]
    have hw' : w ∈ B.L.lattice.toAddSubgroup := by rw [B.lat]; exact hw
    simp only [stdLat, AddSubgroup.mem_pi, Set.mem_univ, true_implies]
    intro p
    by_cases h : p = ixE D n n' j
    · subst h; simpa using hw'
    · simp [h]
  · intro x hx
    have hx' : phi B n n' x ∈ stdLat B.L (Ix D n n') := hx
    simp only [stdLat, AddSubgroup.mem_pi, Set.mem_univ, true_implies] at hx'
    have hsum : phi B n n' x = ∑ p, phi B n n' x p • (Pi.single p 1 : Ix D n n' → ℂ) := by
      funext q
      simp [Finset.sum_apply, Pi.single_apply]
    have hsing : ∀ p, (phi B n n').symm (Pi.single p 1) =
        TaylorLogMetric.embV D (TaylorLogMetric.tor0 D cc δ) (bas B n n' ((ixE D n n').symm p)) := by
      intro p
      rw [LinearEquiv.symm_apply_eq, phi_embV_bas, Equiv.apply_symm_apply]
    have hxe : x = ∑ p, phi B n n' x p • TaylorLogMetric.embV D (TaylorLogMetric.tor0 D cc δ) (bas B n n' ((ixE D n n').symm p)) := by
      conv_lhs => rw [← (phi B n n').symm_apply_apply x, hsum]
      rw [map_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [map_smul, hsing]
    rw [hxe]
    refine AddSubgroup.sum_mem _ fun p _ => AddSubgroup.subset_closure ?_
    refine ⟨phi B n n' x p, ?_, (ixE D n n').symm p, rfl⟩
    have := hx' p
    rw [B.lat] at this
    exact this

end GlobalTheory.BaseVacuum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantTenthStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_sum_local_constant_tenth : ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), Hyp N s W Ch G sel mu cst I dl χ cD pl u δ → (∀ j ≤ N.R.m, ∀ b : I.β j, (Nat.card ((chF W sel mu I u j).mem b).Cl : ℝ) ≤ Real.exp (C * errUnit N (Pr.T u))) ∧ (Nat.card (evGSD W Ch sel mu (rPsymF Ch) u).Cl : ℝ) ≤ Real.exp (C * errUnit N (Pr.T u)) ∧ (topClassNumber Ch sel mu u : ℝ) ≤ Real.exp (C * errUnit N (Pr.T u)) := by
  first | exact @GlobalTheory.ChainClassNumbers.classNumbers_le | exact GlobalTheory.ChainClassNumbers.classNumbers_le | (intros; apply GlobalTheory.ChainClassNumbers.classNumbers_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermSliceContinuousInvariantStatement
section
open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_term_slice_continuous_invariant : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ) (hr : r ≤ a) [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 → ∀ φ : GA E a → ℂ, Continuous φ → (∀ γ g, φ (ratGL E a γ * g) = φ g) → ∀ (m₁ : GA E r) (t : GL (Fin a) (Af E)) (κ : Kinf E a) (γ : GL (Fin (a - r)) E) (g : GA E (a - r)), GlobalTheory.SliceTwo.slice E μ 𝓕 hr φ m₁ t κ (ratGL E (a - r) γ * g) = GlobalTheory.SliceTwo.slice E μ 𝓕 hr φ m₁ t κ g := by
  first | exact @GlobalTheory.SliceTwo.slice_ratGL_mul | exact GlobalTheory.SliceTwo.slice_ratGL_mul | (intros; apply GlobalTheory.SliceTwo.slice_ratGL_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegAddLeDegOfIdealSmulLeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions GlobalTheory.AllWt GlobalTheory.FlatLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deg_add_le_deg_of_ideal_smul_le_alt : ∀ (K V : Type) [Field K] [NumberField K] [IsTotallyComplex K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (W : Type) [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (N : (K →+* ℂ) → V → ℝ) (N' : (K →+* ℂ) → W → ℝ) (φ : V →ₗ[K] W) (t : (K →+* ℂ) → ℝ) (L : Submodule (𝓞 K) V) (L' : Submodule (𝓞 K) W) (𝔞 : Ideal (𝓞 K)), HasGram N → HasGram N' → Function.Injective φ → (∀ σ, 0 < t σ) → (∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) → (∀ σ x, N' σ (φ x) ≤ t σ * N σ x) → L.FG → L'.FG → 𝔞 ≠ ⊥ → 𝔞 • L.map (φ.restrictScalars (𝓞 K)) ≤ L' → Formalism.HN.rkK L' = Formalism.HN.rkK L → deg N L + (Formalism.HN.rkK L : ℝ) * (-((∑ σ : K →+* ℂ, Real.log (t σ)) / (Module.finrank ℚ K : ℝ)) - Real.log (Ideal.absNorm 𝔞 : ℝ) / (Module.finrank ℚ K : ℝ)) ≤ deg N' L' := by
  first | exact @GlobalTheory.TwistIdeal.deg_add_le_deg_of_ideal_smul_le | exact GlobalTheory.TwistIdeal.deg_add_le_deg_of_ideal_smul_le | (intros; apply GlobalTheory.TwistIdeal.deg_add_le_deg_of_ideal_smul_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrAlgClosureOverFiniteDvrExtensionStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dvr_algClosure_over_finite_dvr_extension : ∀ (V W : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr V → GlobalTheory.LN.CDvr W → ∀ io : V →+* W, io.Finite → Function.Injective io → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] [Algebra (FractionRing W) F], (∀ v, algebraMap (FractionRing W) F (algebraMap W _ (io v)) = algebraMap (FractionRing V) F (algebraMap V _ v)) → ∃ N : ℕ, ∀ (T' : Subring F) (_ : IsDiscreteValuationRing T') (f : V →+* T'), (∀ v, (f v : F) = algebraMap (FractionRing V) F (algebraMap V _ v)) → (∀ π, Irreducible π → Irreducible (f π)) → ∃ (T'' : Subring F) (_ : IsDiscreteValuationRing T'') (g : W →+* T'') (e : ℕ), T' ≤ T'' ∧ (∀ w, (g w : F) = algebraMap (FractionRing W) F (algebraMap W _ w)) ∧ 1 ≤ e ∧ e ≤ N ∧ ∀ π, Irreducible π → ∃ ϖ : T'', Irreducible ϖ ∧ Associated (g π) (ϖ ^ e) := by
  first | exact @GlobalTheory.exists_dvr_over_finite_ext | exact GlobalTheory.exists_dvr_over_finite_ext | (intros; apply GlobalTheory.exists_dvr_over_finite_ext <;> assumption)
end

