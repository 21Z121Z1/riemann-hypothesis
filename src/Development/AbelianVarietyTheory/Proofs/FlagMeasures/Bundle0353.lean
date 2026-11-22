import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0225
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0203
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0222
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0136
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0024
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0131
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StabTransitiveOfLemmas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0243
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantFlagLengthsInvarianceTorusPositivity
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0134

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralHermitianOrbitSumFixedLengthLtTop
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open scoped TensorProduct ENNReal Pointwise

noncomputable section

namespace GlobalTheory.OrbitSumInt

theorem exists_compact_reach {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SigmaCompactSpace G] [MulAction G X] [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [ContinuousSMul G X] (x0 : X) (hcl : IsClosed (MulAction.orbit G x0))
    (K : Set X) (hK : IsCompact K) :
    ∃ C : Set G, IsCompact C ∧ ∀ g : G, g • x0 ∈ K → ∃ c ∈ C, c • x0 = g • x0 := by
  let O := MulAction.orbit G x0
  have : LocallyCompactSpace O := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : ContinuousSMul G O := ⟨continuous_induced_rng.2
    (continuous_smul.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))⟩
  let o0 : O := ⟨x0, MulAction.mem_orbit_self x0⟩
  have hopen : IsOpenMap (fun g : G => g • o0) := isOpenMap_smul_of_sigmaCompact o0
  have hK' : IsCompact (Subtype.val ⁻¹' K : Set O) :=
    hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  have key : ∃ C : Set G, IsCompact C ∧ (Subtype.val ⁻¹' K : Set O) ⊆ (fun g : G => g • o0) '' C := by
    refine hK'.induction_on (p := fun s => ∃ C : Set G, IsCompact C ∧ s ⊆ (fun g : G => g • o0) '' C)
      ⟨∅, isCompact_empty, Set.empty_subset _⟩ (fun s t hst ⟨C, hC, h⟩ => ⟨C, hC, hst.trans h⟩) ?_ ?_
    · rintro s t ⟨C, hC, h⟩ ⟨D, hD, h'⟩
      exact ⟨C ∪ D, hC.union hD, by rw [Set.image_union]; exact Set.union_subset_union h h'⟩
    · rintro ⟨_, g, rfl⟩ -
      obtain ⟨C, hC, hg⟩ := exists_compact_mem_nhds g
      exact ⟨_, mem_nhdsWithin_of_mem_nhds (hopen.image_mem_nhds hg), C, hC, subset_rfl⟩
  obtain ⟨C, hC, h⟩ := key
  refine ⟨C, hC, fun g hg => ?_⟩
  obtain ⟨c, hc, e⟩ := h (a := g • o0) hg
  exact ⟨c, hc, congrArg Subtype.val e⟩

theorem lintegral_count_lt_top {G H X S : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [SecondCountableTopology G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] [MulAction G X]
    (μ : Measure G) [μ.IsHaarMeasure] (ν : Measure H) [ν.IsHaarMeasure]
    (Γ : Subgroup G) [Countable Γ] (Δ : Subgroup H) [Countable Δ] (𝓕 : Set G) (𝓖 : Set H)
    (hF : IsFundamentalDomain Γ 𝓕 μ) (hG : IsFundamentalDomain Δ 𝓖 ν) (hfin : ν 𝓖 < ⊤)
    (φ : H →* G) (hφ : Continuous φ) (hinj : Function.Injective φ) (x0 : X)
    (hr : φ.range = MulAction.stabilizer G x0) (hΔ : ∀ δ ∈ Δ, φ δ ∈ Γ)
    (ι : S → X) (hι : Function.Injective ι) (γ : S → Γ) (hγ : ∀ s, (γ s : G) • x0 = ι s)
    (K : Set X) (C : Set G) (hC : IsCompact C) (hKC : ∀ g : G, g • x0 ∈ K → ∃ c ∈ C, c • x0 = g • x0) :
    ∫⁻ h in 𝓕, ∑' s, K.indicator (1 : X → ℝ≥0∞) (h⁻¹ • ι s) ∂μ < ⊤ := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup Γ
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup Γ μ
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup Δ
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup Δ ν
  obtain ⟨U, hU, hU1⟩ := exists_compact_mem_nhds (1 : H)
  have hU0 : ν U ≠ 0 := (Measure.measure_pos_of_mem_nhds ν hU1).ne'
  set D : Set G := (φ '' U)⁻¹ * C⁻¹ with hD
  have hDc : IsCompact D := (hU.image hφ).inv.mul hC.inv
  let f : G → ℝ≥0∞ := D.indicator 1
  have hf : Measurable f := measurable_one.indicator hDc.measurableSet
  let T : G → ℝ≥0∞ := fun g => ∫⁻ k in 𝓖, f ((φ k)⁻¹ * g) ∂ν
  have hm : Measurable fun p : G × H => f ((φ p.2)⁻¹ * p.1) :=
    hf.comp ((hφ.comp continuous_snd).inv.mul continuous_fst).measurable
  have hT : Measurable T := hm.lintegral_prod_right'
  have hfix : ∀ k, φ k • x0 = x0 := fun k => by
    have : φ k ∈ MulAction.stabilizer G x0 := hr ▸ ⟨k, rfl⟩
    exact this
  let j : S × Δ → Γ := fun p => γ p.1 * ⟨φ p.2, hΔ _ p.2.2⟩
  have hj : Function.Injective j := by
    rintro ⟨s, a⟩ ⟨t, b⟩ h
    have h1 : (γ s : G) * φ a = γ t * φ b := congrArg Subtype.val h
    have h2 : s = t := hι (by rw [← hγ, ← hγ, ← hfix a, ← mul_smul, h1, mul_smul, hfix, hfix])
    subst h2
    rw [Subtype.ext (hinj (mul_left_cancel h1))]
  have step : ∀ (h : G) (s : S), ν U * K.indicator (1 : X → ℝ≥0∞) (h⁻¹ • ι s) ≤
      ∑' δ : Δ, T ((j (s, δ))⁻¹ • h) := by
    intro h s
    by_cases hK : h⁻¹ • ι s ∈ K
    swap
    · simp [Set.indicator_of_notMem hK]
    rw [Set.indicator_of_mem hK, Pi.one_apply, mul_one]
    rw [← hγ, ← mul_smul] at hK
    obtain ⟨c, hc, e⟩ := hKC _ hK
    obtain ⟨k, hk⟩ : c⁻¹ * (h⁻¹ * γ s) ∈ φ.range := by
      rw [hr, MulAction.mem_stabilizer_iff, mul_smul, ← e, inv_smul_smul]
    have e1 := hG.lintegral_eq_tsum'' fun k' => f ((φ k')⁻¹ * ((γ s : G)⁻¹ * h))
    have e2 : ∀ δ : Δ, T ((j (s, δ))⁻¹ • h) =
        ∫⁻ k' in 𝓖, f ((φ (δ • k'))⁻¹ * ((γ s : G)⁻¹ * h)) ∂ν := fun δ => by
      refine lintegral_congr fun k' => ?_
      congr 1
      simp [j, Subgroup.smul_def, mul_assoc]
    simp only [e2]
    rw [← e1, ← measure_preimage_mul ν k U, ← lintegral_indicator_one
      ((measurable_const_mul k) hU.measurableSet)]
    refine lintegral_mono fun k' => ?_
    by_cases hk' : k' ∈ (fun x => k * x) ⁻¹' U
    swap
    · simp [Set.indicator_of_notMem hk']
    have : (φ k')⁻¹ * ((γ s : G)⁻¹ * h) ∈ D := by
      refine ⟨(φ (k * k'))⁻¹, Set.inv_mem_inv.2 ⟨_, hk', rfl⟩, c⁻¹, Set.inv_mem_inv.2 hc, ?_⟩
      simp [hk, mul_assoc]
    simp [f, Set.indicator_of_mem hk', Set.indicator_of_mem this]
  have main : ν U * ∫⁻ h in 𝓕, ∑' s, K.indicator (1 : X → ℝ≥0∞) (h⁻¹ • ι s) ∂μ ≤ μ D * ν 𝓖 := by
    rw [← lintegral_const_mul' _ _ hU.measure_lt_top.ne]
    calc _ ≤ ∫⁻ h in 𝓕, ∑' g : Γ, T (g⁻¹ • h) ∂μ := by
          refine lintegral_mono fun h => ?_
          rw [← ENNReal.tsum_mul_left]
          refine (ENNReal.tsum_le_tsum (step h)).trans ?_
          rw [← ENNReal.tsum_prod (f := fun s δ => T ((j (s, δ))⁻¹ • h))]
          exact ENNReal.tsum_comp_le_tsum_of_injective hj fun g => T (g⁻¹ • h)
      _ = ∫⁻ g, T g ∂μ := by
          rw [hF.lintegral_eq_tsum']
          exact lintegral_tsum fun g => (hT.comp (measurable_const_smul g⁻¹)).aemeasurable
      _ = ∫⁻ k in 𝓖, μ D ∂ν := by
          rw [lintegral_lintegral_swap hm.aemeasurable]
          refine lintegral_congr fun k => ?_
          rw [lintegral_mul_left_eq_self f, lintegral_indicator_one hDc.measurableSet]
      _ = μ D * ν 𝓖 := by simp
  by_contra htop
  rw [not_lt_top_iff.1 htop, ENNReal.mul_top hU0] at main
  exact (ENNReal.mul_lt_top hDc.measure_lt_top hfin).not_ge main

open GlobalTheory.GaugeEx in

theorem lintegral_orbitSum_lt_top : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (β : F), β ≠ 0 → ∀ Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℂ, Continuous Φ → HasCompactSupport Φ → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), μ.IsHaarMeasure → IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 μ → ∫⁻ h in 𝓕, ∑' x : {x : Fin 1 → Fin M → E | hE σ J (x 0) (x 0) = algebraMap F E β}, ‖Φ (h⁻¹ • ratTup (F := F) (AF F) (x : Fin 1 → Fin M → E))‖ₑ ∂μ < ⊤ := by
  intro F E _ _ _ _ _ σ hCM M J hJ β hβ Φ hΦ hK μ 𝓕 hμ h𝓕
  rcases isEmpty_or_nonempty {x : Fin 1 → Fin M → E | hE σ J (x 0) (x 0) = algebraMap F E β} with he | ⟨⟨x0, hx0⟩⟩
  · simp
  have hx0 : hE σ J (x0 0) (x0 0) = algebraMap F E β := hx0
  have hβ' : algebraMap F E β ≠ 0 := by simpa using hβ
  have hxx : hE σ J (x0 0) (x0 0) ≠ 0 := hx0 ▸ hβ'
  obtain _ | M := M
  · exact (hxx (by simp [hE, Formalism.UG.hform])).elim
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hσ : ∀ y, σ (σ y) = y := by
    intro y
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hCM.2.2.2, hCM.2.2.2, star_star]
  have hθ : ∃ θ : E, IsUnit (θ - (σ : E →+* E) θ) := by
    by_contra hc
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have := hCM.2.1
    refine IsTotallyComplex.complexEmbedding_not_isReal τ ?_
    rw [ComplexEmbedding.isReal_iff]
    ext z
    have hz : σ z = z := by
      by_contra hz
      exact hc ⟨z, (sub_ne_zero.2 (Ne.symm hz)).isUnit⟩
    have := hCM.2.2.2 τ z
    rw [hz] at this
    exact this.symm
  obtain ⟨a, B, J', -, -, -, hxB, hBB, hJ'⟩ := GlobalTheory.AdelicStabUnimod.exists_stepData hCM hJ x0 hxx
  obtain ⟨φ, hφ, hinj, hr, -, hrat⟩ := GlobalTheory.StabiliserOfVector.exists_hom_range_stabiliser F E σ hCM (M + 1) M
    J J' B x0 rfl hJ hJ' hBB.symm hxB hxx
  let ν : Measure (HA (AF F) σ J') := Measure.haar
  have hν : ν.IsHaarMeasure := inferInstance
  obtain ⟨𝓖, h𝓖⟩ := (GlobalTheory.Mem.Vol.fundamentalDomain_adelicUnitary F E σ M J' ν hν).1
  have hfin : ν 𝓖 < ⊤ := GlobalTheory.Mem.VolFin.finVol F E σ hCM M J' hJ' ν hν 𝓖 h𝓖
  let b : Module.Basis (Fin 2) F E := Module.finBasisOfFinrankEq F E hCM.2.2.1
  have horb : MulAction.orbit (HA (AF F) σ J) (ratTup (F := F) (AF F) x0) =
      {y | qR (AF F) σ J (y 0) = algebraMap F (AF F) β} := by
    ext y
    refine ⟨?_, fun hy => GlobalTheory.AdelicWitt.witt_adelic F E σ hCM _ J x0 β hJ hβ hx0 y hy⟩
    rintro ⟨g, rfl⟩
    rw [Set.mem_setOf_eq, ← GlobalTheory.AdelicWitt.qR_ratTup b (AF F) σ J x0 β hx0]
    exact congrArg (fun z => algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E) z)
      (GlobalTheory.StabOrbit.hR_act (AF F) σ J g _ _)
  have hcl : IsClosed (MulAction.orbit (HA (AF F) σ J) (ratTup (F := F) (AF F) x0)) := by
    rw [horb]
    refine isClosed_eq ?_ continuous_const
    have h1 : Continuous (Algebra.trace (AF F) (AF F ⊗[F] E)) :=
      IsModuleTopology.continuous_of_linearMap _
    have h2 := GlobalTheory.AdelicUnitaryTop.continuous_sigR (AF F) σ
    unfold qR hR Formalism.UG.hform
    refine continuous_const.mul (h1.comp ?_)
    fun_prop
  obtain ⟨C, hC, hKC⟩ := exists_compact_reach _ hcl _ hK
  let Γ : Subgroup (HA (AF F) σ J) := HFinIn (AF F) σ J
  let Δ : Subgroup (HA (AF F) σ J') := HFinIn (AF F) σ J'
  have : Countable Γ := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma σ J
  have : Countable Δ := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma σ J'
  have hγ : ∀ s : {x : Fin 1 → Fin (M + 1) → E | hE σ J (x 0) (x 0) = algebraMap F E β},
      ∃ γ : Γ, (γ : HA (AF F) σ J) • ratTup (F := F) (AF F) x0 = ratTup (F := F) (AF F) s.1 := by
    rintro ⟨x, hx⟩
    obtain ⟨g, hg, e⟩ := GlobalTheory.WittTransitivity.witt_transitive E (σ : E →+* E) hσ
      (fun a _ ha => ha.isUnit) two_ne_zero.isUnit three_ne_zero hθ _ J hJ.1 hJ.2.isUnit (x0 0) (x 0)
      (hx0.trans (Eq.symm hx)) hxx.isUnit
    have hm : Formalism.UG.bc (inclR (F := F) (AF F)) g ∈ HR (AF F) σ J := by
      have hg' : Formalism.UG.cT (σ : E →+* E) g.1 * J * g.1 = J := hg
      have h1 := congrArg (·.map (inclR (F := F) (AF F))) hg'
      simp only [Matrix.map_mul] at h1
      exact h1
    refine ⟨⟨(⟨_, hm⟩ : HR (AF F) σ J), ⟨g, hg, rfl⟩⟩, ?_⟩
    funext k i
    obtain rfl : k = 0 := Subsingleton.elim _ _
    change _ = inclR (F := F) (AF F) (x 0 i)
    rw [← e, RingHom.map_mulVec]
    rfl
  choose γ hγ using hγ
  have : Nontrivial (AF F) := inferInstanceAs (Nontrivial (InfiniteAdeleRing F × _))
  have hι : Function.Injective fun s : {x : Fin 1 → Fin (M + 1) → E | hE σ J (x 0) (x 0) = algebraMap F E β} =>
      ratTup (F := F) (AF F) s.1 := fun s t h => Subtype.ext (funext fun k => funext fun i =>
    (inclR (F := F) (E := E) (AF F)).injective (congrFun (congrFun h k) i))
  have key := lintegral_count_lt_top μ ν Γ Δ 𝓕 𝓖 h𝓕 h𝓖 hfin φ hφ hinj (ratTup (F := F) (AF F) x0) hr
    (fun δ hδ => (hrat δ).2 hδ) _ hι γ hγ (tsupport Φ) C hC hKC
  obtain ⟨A, hA⟩ := hΦ.bounded_above_of_compact_support hK
  refine lt_of_le_of_lt ?_ (ENNReal.mul_lt_top (ENNReal.ofReal_lt_top (r := A)) key)
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun h => ?_
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun s => ?_
  by_cases hs : h⁻¹ • ratTup (F := F) (AF F) s.1 ∈ tsupport Φ
  · rw [Set.indicator_of_mem hs, Pi.one_apply, mul_one, ← ofReal_norm_eq_enorm]
    exact ENNReal.ofReal_le_ofReal (hA _)
  · simp [image_eq_zero_of_notMem_tsupport hs]

end GlobalTheory.OrbitSumInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SobolevValueAtOneFixedCompactDiagSignUnitary
section
open MeasureTheory Matrix Formalism.MainNotions.S
open scoped ENNReal

namespace GlobalTheory.SobolevHaar

theorem ofReal_list_sum_le {α : Type} (S : List α) (f : α → ℝ) :
    ENNReal.ofReal (S.map f).sum ≤ (S.map fun a => ENNReal.ofReal (f a)).sum := by
  induction S with
  | nil => simp
  | cons a S ih =>
    simp only [List.map_cons, List.sum_cons]
    exact ENNReal.ofReal_add_le.trans (add_le_add le_rfl ih)

private theorem ofReal_integral_le_lintegral_ofReal {X : Type} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ)
    (hf : ∀ x, 0 ≤ f x) : ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  by_cases hi : Integrable f μ
  · exact (ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hf)).le
  · rw [integral_undef hi]
    simp

theorem sobolev_at_one_compact : ∀ (n : ℕ) (ε : Fin n → Bool), ∃ (S : List (List (Matrix (Fin n) (Fin n) ℂ))) (C : ℝ) (Q : Set (Formalism.REAL.UJ ε)), IsCompact Q ∧ (∀ l ∈ S, ∀ X ∈ l, Formalism.REAL.inG ε X) ∧ 0 ≤ C ∧ ∀ F : List (Matrix (Fin n) (Fin n) ℂ) → Matrix (Fin n) (Fin n) ℂ → ℂ, (∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ Y ∈ l, Formalism.REAL.inG ε Y) → ContinuousOn (F l) (UJset ε)) → (∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ Y ∈ l, Formalism.REAL.inG ε Y) → ∀ X, Formalism.REAL.inG ε X → ∀ g ∈ UJset ε, HasDerivAt (fun t : ℝ => F l (g * NormedSpace.exp ((t : ℂ) • X))) (F (X :: l) g) 0) → ENNReal.ofReal (‖F [] 1‖ ^ 2) ≤ ENNReal.ofReal C * (S.map fun l => ∫⁻ y in Q, ENNReal.ofReal (‖F l (umat y)‖ ^ 2) ∂(Formalism.REAL.muG ε)).sum := by
  intro n ε

  obtain ⟨E, hE, hON, -⟩ := GlobalTheory.LieONB.exists_orthonormal_basis n ε
  obtain ⟨s, hs, hsmall⟩ := exists_small n
  obtain ⟨c, -, hc, -⟩ := GlobalTheory.GaugeConst.exists_unique_isGauge n ε
  have hEl : ∀ i, E i ∈ GlobalTheory.GaugeConst.lieJ ε := fun i => GlobalTheory.GaugeConst.mem_lieJ.2 (hE i).1
  have hsm : ∀ (t : ℝ) (X : Matrix (Fin n) (Fin n) ℂ), (t : ℂ) • X = t • X := by
    intro t X
    ext a b
    simp [Complex.real_smul]

  obtain ⟨cu, hcuM, hcuc⟩ : ∃ cu : Fin (n ^ 2) → ℝ → Formalism.REAL.UJ ε,
      (∀ i t, umat (cu i t) = NormedSpace.exp ((t : ℂ) • E i)) ∧ ∀ i, Continuous (cu i) := by
    refine ⟨fun i t => GlobalTheory.GaugeConst.expJ ε (t • ⟨E i, hEl i⟩), fun i t => ?_, fun i => ?_⟩
    · rw [hsm]
      exact GlobalTheory.GaugeConst.uMat_expJ ε (t • ⟨E i, hEl i⟩)
    · exact (GlobalTheory.GaugeConst.continuous_expJ ε).comp (continuous_id.smul continuous_const)
  have hu1 : umat (1 : Formalism.REAL.UJ ε) = 1 := rfl
  have humul : ∀ x y : Formalism.REAL.UJ ε, umat (x * y) = umat x * umat y := fun _ _ => rfl
  have hinj : Function.Injective (fun x : Formalism.REAL.UJ ε => umat x) :=
    GlobalTheory.GaugeConst.uMat_injective ε
  have hcu0 : ∀ i, cu i 0 = 1 := by
    intro i
    apply hinj
    show umat (cu i 0) = umat 1
    rw [hcuM, hu1]
    simp
  have hcuadd : ∀ i a b, cu i (a + b) = cu i a * cu i b := by
    intro i a b
    apply hinj
    show umat (cu i (a + b)) = umat (cu i a * cu i b)
    rw [humul, hcuM, hcuM, hcuM, Complex.ofReal_add, add_smul]
    exact Matrix.exp_add_of_commute _ _ (((Commute.refl (E i)).smul_left _).smul_right _)

  have hlist : ∀ l : List (Formalism.REAL.UJ ε), umat l.prod = (l.map fun x => umat x).prod := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih => rw [List.prod_cons, humul, ih, List.map_cons, List.prod_cons]
  have hΘ : ∀ t : Fin (n ^ 2) → ℝ, umat ((List.ofFn fun i => cu i (t i)).prod) =
      (List.ofFn fun i => NormedSpace.exp ((t i : ℂ) • E i)).prod := by
    intro t
    rw [hlist, List.map_ofFn]
    simp only [Function.comp_def, hcuM]
  have hΘc : Continuous fun t : Fin (n ^ 2) → ℝ => (List.ofFn fun i => cu i (t i)).prod :=
    GlobalTheory.continuous_prod_ofFn_curves (n ^ 2) cu hcuc
  obtain ⟨K, hchart⟩ : ∃ K : ℝ, ∀ Φ : Formalism.REAL.UJ ε → ENNReal, Measurable Φ →
      ∫⁻ t in Set.pi Set.univ (fun _ : Fin (n ^ 2) => Set.Icc (0 : ℝ) s),
          Φ ((List.ofFn fun i => cu i (t i)).prod) ≤
        ENNReal.ofReal K * ∫⁻ y in (fun t : Fin (n ^ 2) → ℝ => (List.ofFn fun i => cu i (t i)).prod) ''
          Set.pi Set.univ (fun _ : Fin (n ^ 2) => Set.Icc (0 : ℝ) s), Φ y ∂(Formalism.REAL.muG ε) :=
    ⟨_, GlobalTheory.ProductChart.lintegral_chart_le n ε c s E
      (fun t => (List.ofFn fun i => cu i (t i)).prod) hc (fun i => (hE i).1) hON hs hsmall hΘ⟩

  have hD : ∀ i, ∀ v ∈ {l : List (Matrix (Fin n) (Fin n) ℂ) | ∀ Y ∈ l, Formalism.REAL.inG ε Y},
      E i :: v ∈ {l : List (Matrix (Fin n) (Fin n) ℂ) | ∀ Y ∈ l, Formalism.REAL.inG ε Y} := by
    intro i v hv
    simp only [Set.mem_ofPred_eq] at hv ⊢
    intro Y hY
    rcases List.mem_cons.1 hY with rfl | hY
    · exact (hE i).1
    · exact hv Y hY
  obtain ⟨S, C0, hSA, hC0, hbound⟩ :=
    cube_sum {l : List (Matrix (Fin n) (Fin n) ℂ) | ∀ Y ∈ l, Formalism.REAL.inG ε Y} [] (by simp) s hs
      (n ^ 2) cu (fun i v => E i :: v) (fun i => ⟨hcuc i, hcu0 i, hcuadd i⟩) hD
  refine ⟨S, C0 * max K 0,
    (fun t : Fin (n ^ 2) → ℝ => (List.ofFn fun i => cu i (t i)).prod) ''
      Set.pi Set.univ (fun _ : Fin (n ^ 2) => Set.Icc (0 : ℝ) s),
    (isCompact_univ_pi fun _ => isCompact_Icc).image hΘc,
    fun l hl => (hSA l hl : ∀ Y ∈ l, Formalism.REAL.inG ε Y),
    mul_nonneg hC0 (le_max_right _ _), ?_⟩
  intro F hFc hFd
  have hmem : ∀ x : Formalism.REAL.UJ ε, umat x ∈ UJset ε := fun x => x.2
  have hFrc : ∀ v : List (Matrix (Fin n) (Fin n) ℂ), (∀ Y ∈ v, Formalism.REAL.inG ε Y) →
      Continuous fun x : Formalism.REAL.UJ ε => F v (umat x) := fun v hv =>
    (hFc v hv).comp_continuous (GlobalTheory.GaugeConst.continuous_uMat ε) hmem
  have hFrd : ∀ v : List (Matrix (Fin n) (Fin n) ℂ), (∀ Y ∈ v, Formalism.REAL.inG ε Y) →
      ∀ (i : Fin (n ^ 2)) (x : Formalism.REAL.UJ ε),
        HasDerivAt (fun t => F v (umat (x * cu i t))) (F (E i :: v) (umat x)) 0 := by
    intro v hv i x
    have h := hFd v hv (E i) (hE i).1 (umat x) (hmem x)
    have he : (fun t : ℝ => F v (umat (x * cu i t))) =
        fun t : ℝ => F v (umat x * NormedSpace.exp ((t : ℂ) • E i)) := by
      funext t
      rw [humul, hcuM]
    rw [he]
    exact h
  have hb : ‖F [] 1‖ ^ 2 ≤ C0 * (S.map fun v =>
      ∫ t in Set.pi Set.univ (fun _ : Fin (n ^ 2) => Set.Icc (0 : ℝ) s),
        ‖F v (umat ((List.ofFn fun i => cu i (t i)).prod))‖ ^ 2).sum :=
    hbound (fun v x => F v (umat x)) hFrc hFrd
  have hpt : ∀ v ∈ S,
      ENNReal.ofReal (∫ t in Set.pi Set.univ (fun _ : Fin (n ^ 2) => Set.Icc (0 : ℝ) s),
        ‖F v (umat ((List.ofFn fun i => cu i (t i)).prod))‖ ^ 2) ≤
      ENNReal.ofReal K * ∫⁻ y in (fun t : Fin (n ^ 2) → ℝ => (List.ofFn fun i => cu i (t i)).prod) ''
          Set.pi Set.univ (fun _ : Fin (n ^ 2) => Set.Icc (0 : ℝ) s),
        ENNReal.ofReal (‖F v (umat y)‖ ^ 2) ∂(Formalism.REAL.muG ε) := by
    intro v hv
    have hcont := hFrc v (hSA v hv)
    have hmeas : Measurable fun y : Formalism.REAL.UJ ε => ENNReal.ofReal (‖F v (umat y)‖ ^ 2) :=
      (ENNReal.continuous_ofReal.comp (hcont.norm.pow 2)).measurable
    have h1 := ofReal_integral_le_lintegral_ofReal
      (volume.restrict (Set.pi Set.univ (fun _ : Fin (n ^ 2) => Set.Icc (0 : ℝ) s)))
      (fun t => ‖F v (umat ((List.ofFn fun i => cu i (t i)).prod))‖ ^ 2) (fun t => sq_nonneg _)
    have h2 := hchart (fun y => ENNReal.ofReal (‖F v (umat y)‖ ^ 2)) hmeas
    exact h1.trans h2
  calc ENNReal.ofReal (‖F [] 1‖ ^ 2)
      ≤ ENNReal.ofReal (C0 * (S.map fun v =>
          ∫ t in Set.pi Set.univ (fun _ : Fin (n ^ 2) => Set.Icc (0 : ℝ) s),
            ‖F v (umat ((List.ofFn fun i => cu i (t i)).prod))‖ ^ 2).sum) :=
        ENNReal.ofReal_le_ofReal hb
    _ = ENNReal.ofReal C0 * ENNReal.ofReal (S.map fun v =>
          ∫ t in Set.pi Set.univ (fun _ : Fin (n ^ 2) => Set.Icc (0 : ℝ) s),
            ‖F v (umat ((List.ofFn fun i => cu i (t i)).prod))‖ ^ 2).sum :=
        ENNReal.ofReal_mul hC0
    _ ≤ ENNReal.ofReal C0 * (S.map fun v => ENNReal.ofReal K *
          ∫⁻ y in (fun t : Fin (n ^ 2) → ℝ => (List.ofFn fun i => cu i (t i)).prod) ''
            Set.pi Set.univ (fun _ : Fin (n ^ 2) => Set.Icc (0 : ℝ) s),
          ENNReal.ofReal (‖F v (umat y)‖ ^ 2) ∂(Formalism.REAL.muG ε)).sum := by
        gcongr
        exact (ofReal_list_sum_le _ _).trans (List.sum_le_sum hpt)
    _ = ENNReal.ofReal C0 * ENNReal.ofReal K * (S.map fun v =>
          ∫⁻ y in (fun t : Fin (n ^ 2) → ℝ => (List.ofFn fun i => cu i (t i)).prod) ''
            Set.pi Set.univ (fun _ : Fin (n ^ 2) => Set.Icc (0 : ℝ) s),
          ENNReal.ofReal (‖F v (umat y)‖ ^ 2) ∂(Formalism.REAL.muG ε)).sum := by
        rw [List.sum_map_mul_left, mul_assoc]
    _ ≤ ENNReal.ofReal (C0 * max K 0) * (S.map fun v =>
          ∫⁻ y in (fun t : Fin (n ^ 2) → ℝ => (List.ofFn fun i => cu i (t i)).prod) ''
            Set.pi Set.univ (fun _ : Fin (n ^ 2) => Set.Icc (0 : ℝ) s),
          ENNReal.ofReal (‖F v (umat y)‖ ^ 2) ∂(Formalism.REAL.muG ε)).sum := by
        rw [ENNReal.ofReal_mul hC0]
        gcongr
        exact le_max_left _ _

end GlobalTheory.SobolevHaar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TwoSidedSizeFunctionPosInvariantContinuous
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.TwoSided

open GlobalTheory.Mom.LowVec

theorem exists_coord {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) (a : Fin (r + 1)) :
    ∃ i : Fin (2 * r + k + 1), a.val ≤ i.val ∧ fvec k r z a i ≠ 0 := by
  by_cases ha : a.val < r
  · refine ⟨eI k r ⟨a.val, ha⟩, le_of_eq rfl, ?_⟩
    simp only [fvec, dif_pos ha, bvec, Pi.single_eq_same]
    exact one_ne_zero
  ·
    have hz0 : ∃ i, z i ≠ 0 := by
      by_contra h
      push_neg at h
      have : z = 0 := funext h
      subst this
      simp [Tz, herm] at hT
    obtain ⟨i, hi⟩ := hz0
    have hri : r ≤ i.val := by
      by_contra h
      exact hi (hz i (Or.inl (Nat.lt_of_not_le h)))
    refine ⟨i, le_trans (Nat.le_of_lt_succ a.isLt) hri, ?_⟩
    simp only [fvec, dif_neg ha]
    exact hi

theorem lA_pos {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z)
    {x : Mat k r} (hx : x ∈ GG k r) (a : Fin (r + 1)) : 0 < lA k r z x a := by
  obtain ⟨i, hai, hi⟩ := exists_coord hz hT a
  have hu : IsUnit x.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hx
  have hc : 0 < ∑ j, ‖x i j‖ + 1 := by positivity

  have key : ∀ y ∈ Submodule.span ℂ (Set.range fun b : {b : Fin r // b.val < a.val} =>
      Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r b.1)),
      ‖fvec k r z a i‖ / (∑ j, ‖x i j‖ + 1) ≤ eucl (x⁻¹ *ᵥ (fvec k r z a - y)) := by
    intro y hy
    have hy' : y ∈ GlobalTheory.Mom.LowVec.flagSpan k r a := hy
    have hyi : y i = 0 := (GlobalTheory.Mom.LowVec.mem_flagSpan.1 hy') i hai
    set w := x⁻¹ *ᵥ (fvec k r z a - y) with hw
    have hv : fvec k r z a - y = x *ᵥ w := by
      rw [hw, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv x hu, Matrix.one_mulVec]
    have hvi : fvec k r z a i = ∑ j, x i j * w j := by
      have := congrFun hv i
      simp only [Pi.sub_apply, hyi, sub_zero] at this
      rw [this]
      rfl
    have hwe : 0 ≤ eucl w := Real.sqrt_nonneg _
    have hle : ‖fvec k r z a i‖ ≤ (∑ j, ‖x i j‖ + 1) * eucl w := by
      rw [hvi]
      calc ‖∑ j, x i j * w j‖ ≤ ∑ j, ‖x i j * w j‖ := norm_sum_le _ _
        _ = ∑ j, ‖x i j‖ * ‖w j‖ := by simp only [norm_mul]
        _ ≤ ∑ j, ‖x i j‖ * eucl w := by
          gcongr with j
          exact GlobalTheory.Amp.LInv.norm_le_eucl w j
        _ = (∑ j, ‖x i j‖) * eucl w := by rw [Finset.sum_mul]
        _ ≤ (∑ j, ‖x i j‖ + 1) * eucl w := by nlinarith
    rw [div_le_iff₀ hc]
    linarith
  unfold lA
  refine lt_of_lt_of_le (div_pos (norm_pos_iff.mpr hi) hc) ?_
  refine le_csInf ⟨_, 0, Submodule.zero_mem _, rfl⟩ ?_
  rintro t ⟨y, hy, rfl⟩
  exact key y hy

theorem Sg2_invariant_continuousOn_one_le_bounds : ∀ (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)), inWb k r z → 0 < Tz k r z → (∀ x ∈ GG k r, ∀ a, 0 < lA k r z x a) ∧ (∀ x ∈ GG k r, ∀ s ∈ Sset k r z, ∀ κ ∈ (GG k r ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set (Mat k r))), Sg2 k r z (s * x * κ) = Sg2 k r z x) ∧ ContinuousOn (Sg2 k r z) (GG k r) ∧ ∀ x, 1 ≤ Sg2 k r z x ∧ Sg k r z x ≤ Sg2 k r z x ∧ (∀ a, lA k r z x a ≤ Sg2 k r z x ∧ (lA k r z x a)⁻¹ ≤ Sg2 k r z x) ∧ (Sg2 k r z x = 1 ∨ ∃ a, Sg2 k r z x = max (lA k r z x a) (lA k r z x a)⁻¹) := by
  intro k r z hz hT
  have hpos : ∀ x ∈ GG k r, ∀ a, 0 < lA k r z x a := fun x hx a => lA_pos hz hT hx a
  obtain ⟨hinv, -, hSg⟩ := GlobalTheory.Amp.LInv.lengths_basic k r z hz
  refine ⟨hpos, ?_, ?_, ?_⟩
  · intro x hx s hs κ hκ
    have h := (hinv x hx s hs κ hκ).1
    simp only [Sg2, h]
  · have hc := (GlobalTheory.Amp.LenCont.lA_Sg_continuousOn k r z).1
    exact GlobalTheory.Amp.LenCont.fold_continuousOn (GG k r) (fun a x => max (lA k r z x a) (lA k r z x a)⁻¹)
      (fun a => continuous_max.comp_continuousOn (ContinuousOn.prodMk (hc a) (ContinuousOn.inv₀ (hc a) fun x hx => (hpos x hx a).ne'))) Finset.univ
  · intro x
    have hle : ∀ a, max (lA k r z x a) (lA k r z x a)⁻¹ ≤ Sg2 k r z x := fun a =>
      (Finset.le_fold_max _).2 (Or.inr ⟨a, Finset.mem_univ _, le_rfl⟩)
    have h1 : 1 ≤ Sg2 k r z x := (Finset.le_fold_max _).2 (Or.inl le_rfl)
    refine ⟨h1, ?_, fun a => ⟨(le_max_left _ _).trans (hle a), (le_max_right _ _).trans (hle a)⟩, ?_⟩
    · exact (Finset.fold_max_le _).2 ⟨h1, fun a _ => (le_max_left _ _).trans (hle a)⟩
    ·
      have key : ∀ s : Finset (Fin (r + 1)), s.fold max 1 (fun a => max (lA k r z x a) (lA k r z x a)⁻¹) = 1 ∨
          ∃ a, s.fold max 1 (fun a => max (lA k r z x a) (lA k r z x a)⁻¹) = max (lA k r z x a) (lA k r z x a)⁻¹ := by
        intro s
        refine Finset.induction_on s ?_ ?_
        · left
          simp
        · intro a s ha ih
          rw [Finset.fold_insert ha]
          rcases max_choice (max (lA k r z x a) (lA k r z x a)⁻¹)
              (s.fold max 1 (fun a => max (lA k r z x a) (lA k r z x a)⁻¹)) with h | h
          · exact Or.inr ⟨a, h⟩
          · rw [h]
            exact ih
      exact key Finset.univ

end GlobalTheory.Amp.TwoSided
end
end

