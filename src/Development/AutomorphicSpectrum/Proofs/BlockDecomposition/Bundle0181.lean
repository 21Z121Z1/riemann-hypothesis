import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0178
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0166
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalGramFiberRankOneSetFormula
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0026
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0141
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0139
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0140
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusMonomialEvalCompat
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.CapOComp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0146
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0167
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0176
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0120

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeDpowClosedOfHyp
section
open DividedPowers CrystallineSemistableComparison.Pb

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.LatDP

variable {B : Type} [CommRing B] [Algebra ℚ B]

theorem inv_fact_smul_add_pow_mem (S : Subring B) {z w : B}
    (hz : ∀ k : ℕ, ((k.factorial : ℚ))⁻¹ • z ^ k ∈ S) (hw : ∀ k : ℕ, ((k.factorial : ℚ))⁻¹ • w ^ k ∈ S)
    (k : ℕ) : ((k.factorial : ℚ))⁻¹ • (z + w) ^ k ∈ S := by
  have e : ((k.factorial : ℚ))⁻¹ • (z + w) ^ k =
      ∑ i ∈ Finset.range (k + 1), (((i.factorial : ℚ))⁻¹ • z ^ i) * ((((k - i).factorial : ℚ))⁻¹ • w ^ (k - i)) := by
    rw [add_pow, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hik : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have hc : ((k.choose i : ℕ) : B) = ((k.choose i : ℕ) : ℚ) • (1 : B) := by
      rw [Algebra.smul_def, mul_one, map_natCast]
    rw [hc, mul_smul_comm, mul_one, smul_smul, smul_mul_smul_comm, Nat.cast_choose ℚ hik]
    congr 1
    have h1 : (k.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 k.factorial_ne_zero
    have h2 : (i.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 i.factorial_ne_zero
    have h3 : ((k - i).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (k - i).factorial_ne_zero
    field_simp
  rw [e]
  exact S.sum_mem fun i _ => S.mul_mem (hz i) (hw _)

variable {W : Type} [CommRing W] (f : W →+* B) (ξ : W) (l M : ℕ)

theorem inv_fact_smul_dpE_pow (j k : ℕ) (hj : j ≠ 0) :
    ((k.factorial : ℚ))⁻¹ • Lat.dpE f ξ l M j ^ k =
      ((k.uniformBell j : ℕ) : B) * Lat.dpE f ξ l M (k * j) := by
  have hU : ((k.uniformBell j : ℕ) : ℚ) * (j.factorial : ℚ) ^ k * (k.factorial : ℚ) = ((k * j).factorial : ℚ) := by
    exact_mod_cast Nat.uniformBell_mul_eq k hj
  have hc : ((k.uniformBell j : ℕ) : B) = ((k.uniformBell j : ℕ) : ℚ) • (1 : B) := by
    rw [Algebra.smul_def, mul_one, map_natCast]
  have h1 : (k.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 k.factorial_ne_zero
  have h2 : (j.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 j.factorial_ne_zero
  have h3 : ((k * j).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (k * j).factorial_ne_zero
  rw [Lat.dpE, Lat.dpE, smul_pow, ← pow_mul, smul_smul, hc, smul_mul_assoc, one_mul, smul_smul, mul_comm j k]
  congr 1
  have h4 : (j.factorial : ℚ) ^ k ≠ 0 := pow_ne_zero _ h2
  rw [eq_mul_inv_iff_mul_eq₀ h3, ← hU, inv_pow]
  field_simp

theorem inv_fact_smul_term_mem (c : W) (j k : ℕ) (hj : j ≠ 0) :
    ((k.factorial : ℚ))⁻¹ • (f c * Lat.dpE f ξ l M j) ^ k ∈ Lat.sub f ξ l M := by
  have e : ((k.factorial : ℚ))⁻¹ • (f c * Lat.dpE f ξ l M j) ^ k =
      f c ^ k * (((k.uniformBell j : ℕ) : B) * Lat.dpE f ξ l M (k * j)) := by
    rw [mul_pow, ← mul_smul_comm, inv_fact_smul_dpE_pow f ξ l M j k hj]
  rw [e]
  have hf : f c ∈ Lat.sub f ξ l M := Subring.subset_closure (Or.inl ⟨c, rfl⟩)
  have hd : Lat.dpE f ξ l M (k * j) ∈ Lat.sub f ξ l M := Subring.subset_closure (Or.inr ⟨_, rfl⟩)
  exact mul_mem (pow_mem hf _) (mul_mem (natCast_mem _ _) hd)

theorem inv_fact_smul_sum_mem {n : ℕ} (c : Fin n → W) (s : Finset (Fin n)) (k : ℕ) :
    ((k.factorial : ℚ))⁻¹ • (∑ i ∈ s, f (c i) * Lat.dpE f ξ l M (i + 1)) ^ k ∈ Lat.sub f ξ l M := by
  classical
  induction s using Finset.induction_on generalizing k with
  | empty =>
    rcases k with _ | k
    · simpa using (Lat.sub f ξ l M).one_mem
    · simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact inv_fact_smul_add_pow_mem _ (fun k => inv_fact_smul_term_mem f ξ l M _ _ k (Nat.succ_ne_zero _)) ih k

theorem dpClosed {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ) (m : ℕ)
    (h : Lat.Hyp f ξ l m) : Lat.DPClosed (Lat.ι f ξ l M) (Lat.γB f ξ) := by
  intro x hx k
  obtain ⟨n, c, e⟩ := (GlobalTheory.T.mem_lattice_ideal_iff_sum f ξ l M m h x).1 hx
  refine ⟨⟨_, inv_fact_smul_sum_mem f ξ l M c Finset.univ k⟩, ?_⟩
  rw [RatAlgebra.dpow_eq_inv_fact_smul _ (Lat.γB f ξ) hx, e, Ring.inverse_eq_inv']
  rfl

end GlobalTheory.CompanionTheory.LatDP
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeFiltrationLTorsionFreeStatement
section
open DividedPowers CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_filtration_l_torsion_free : ∀ {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ) (m : ℕ), Lat.Hyp f ξ l m → ∀ hc : Lat.DPClosed (Lat.ι f ξ l M) (Lat.γB f ξ), ∀ (r : ℕ) (x : Lat.A f ξ l M), (l : Lat.A f ξ l M) * x ∈ pdP (Lat.γ f ξ l M hc) r → x ∈ pdP (Lat.γ f ξ l M hc) r := by
  first | exact @GlobalTheory.CompanionTheory.Lat.quot_pdP_no_torsion | exact GlobalTheory.CompanionTheory.Lat.quot_pdP_no_torsion | (intros; apply GlobalTheory.CompanionTheory.Lat.quot_pdP_no_torsion <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeLPowMemSpanOfNotMem
section
set_option autoImplicit false

open DividedPowers CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.Lat

private theorem exists_sub_iota_mem_of_sub_involution_mem {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W)
    (l M : ℕ) (b : B) (hb : b ∈ Lat.sub f ξ l M) : ∃ w : W, f w - b ∈ Lat.IB f ξ := by
  have hη : Lat.η f ξ l M ∈ Lat.IB f ξ := by
    rw [Lat.η, Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  have hle : Lat.sub f ξ l M ≤
      (((Ideal.Quotient.mk (Lat.IB f ξ)).comp f).range).comap (Ideal.Quotient.mk (Lat.IB f ξ)) := by
    show Subring.closure _ ≤ _
    rw [Subring.closure_le]
    rintro y (⟨w, rfl⟩ | ⟨i, rfl⟩)
    · exact Subring.mem_comap.2 (RingHom.mem_range.2 ⟨w, rfl⟩)
    · cases i with
      | zero => exact Subring.mem_comap.2 (RingHom.mem_range.2 ⟨1, by simp [Lat.dpE]⟩)
      | succ i =>
        have hd : Lat.dpE f ξ l M (i + 1) ∈ Lat.IB f ξ := by
          rw [Lat.dpE, Algebra.smul_def, pow_succ']
          exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ hη)
        refine Subring.mem_comap.2 (RingHom.mem_range.2 ⟨0, ?_⟩)
        rw [map_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem]
        exact hd
  obtain ⟨w, hw⟩ := RingHom.mem_range.1 (Subring.mem_comap.1 (hle hb))
  exact ⟨w, Ideal.Quotient.eq.1 hw⟩

theorem pow_mem_span_sup_I : ∀ {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W)
    (l M : ℕ) (m : ℕ), Lat.Hyp f ξ l m → ∀ x : Lat.A f ξ l M, x ∉ Lat.I f ξ l M →
      ∃ n : ℕ, (l : Lat.A f ξ l M) ^ n ∈ Ideal.span {x} ⊔ Lat.I f ξ l M := by
  intro W B _ _ _ f ξ l M m hH x hx
  have hxmem : Lat.ι f ξ l M x ∈ Lat.sub f ξ l M := (show ↥(Lat.sub f ξ l M) from x).2
  obtain ⟨w, hw⟩ := exists_sub_iota_mem_of_sub_involution_mem f ξ l M _ hxmem
  have hxw : Lat.ofW f ξ l M w - x ∈ Lat.I f ξ l M := by
    show Lat.ι f ξ l M (Lat.ofW f ξ l M w - x) ∈ Lat.IB f ξ
    rw [map_sub, Lat.ι_ofW]
    exact hw
  have hξI : Lat.ofW f ξ l M ξ ∈ Lat.I f ξ l M := by
    show Lat.ι f ξ l M (Lat.ofW f ξ l M ξ) ∈ Lat.IB f ξ
    rw [Lat.ι_ofW]
    exact Ideal.mem_span_singleton_self _
  have hwnot : ¬ ξ ∣ w := by
    rintro ⟨v, rfl⟩
    apply hx
    have h1 : Lat.ofW f ξ l M (ξ * v) ∈ Lat.I f ξ l M := by
      rw [map_mul]
      exact Ideal.mul_mem_right _ _ hξI
    have h2 := (Lat.I f ξ l M).sub_mem h1 hxw
    simpa using h2
  have hq : Ideal.Quotient.mk (Ideal.span {ξ}) w ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    exact hwnot
  obtain ⟨n, c, hc⟩ := hH.dv _ hq
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective c
  have hmem : (l : W) ^ n - w * u ∈ Ideal.span {ξ} := by
    rw [← Ideal.Quotient.eq]
    simpa using hc
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1 hmem
  refine ⟨n, ?_⟩
  have e : (l : Lat.A f ξ l M) ^ n = Lat.ofW f ξ l M ((l : W) ^ n) := by
    rw [map_pow, map_natCast]
  rw [e, show (l : W) ^ n = w * u + v * ξ by rw [hv]; ring, map_add, map_mul, map_mul]
  refine Ideal.add_mem _ ?_ (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ hξI))
  have e2 : Lat.ofW f ξ l M w * Lat.ofW f ξ l M u =
      x * Lat.ofW f ξ l M u + (Lat.ofW f ξ l M w - x) * Lat.ofW f ξ l M u := by ring
  rw [e2]
  exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self x)))
    (Ideal.mem_sup_right (Ideal.mul_mem_right _ _ hxw))

end GlobalTheory.CompanionTheory.Lat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalBinaryGramIntegral
section
open PositivityTheory.Rg.Mass
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped TensorProduct ENNReal NNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.FibreCpt

open GlobalTheory.CompanionTheory.SW.FibreRatio

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E}

theorem masses_field (R : Type) [Field R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R]
    [BorelSpace R] (hloc : IsLocR R) (h : IsCMExt F E σ) (hJ : IsHermND σ J)
    {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R) (hlam : lam.IsAddHaarMeasure)
    (m : HermR R σ 1 → Measure (Fin 1 → Fin M → R ⊗[F] E))
    (hfib : IsGramFib R σ J 1 (coordW R b lam 1 M) (coordHerm R σ b lam 1) m)
    (A : Set (Fin 1 → Fin M → R ⊗[F] E)) (hAc : IsCompact A) (hAo : IsOpen A)
    (hAU : A ⊆ {X | IsUnit (gramR R σ J X).det}) :
    Continuous (fun s : R => (m (hermScal R σ s) A).toReal) ∧
    HasCompactSupport (fun s : R => (m (hermScal R σ s) A).toReal) ∧
    ENNReal.ofReal (∫ s, (m (hermScal R σ s) A).toReal ∂lam) = coordW R b lam 1 M A := by
  obtain ⟨h1, h2, h3, h4, -⟩ := id hloc
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  obtain ⟨-, -, -, hT2, -, htr, -, hBor, -, hgr⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ h R
  haveI := hT2
  haveI := hBor 1 M
  haveI : BorelSpace (HermR R σ 1) := ⟨rfl⟩
  have hHaar := GlobalTheory.T.coordinate_haar_measure F E σ h R d b lam hlam
  have hμ := hHaar.2.1 1 M
  have hν := hHaar.2.2 1
  have hAm : MeasurableSet A := hAo.measurableSet
  set φ : (Fin 1 → Fin M → R ⊗[F] E) → ℂ := A.indicator fun _ => 1 with hφ
  have hAclopen : IsClopen A := ⟨hAc.isClosed, hAo⟩
  have hφc : Continuous φ :=
    continuous_indicator (by simp [hAclopen.frontier_eq]) continuousOn_const
  have hφs : HasCompactSupport φ :=
    HasCompactSupport.intro hAc fun x hx => Set.indicator_of_notMem hx _
  obtain ⟨⟨hg, -⟩, -⟩ := GlobalTheory.T.gram_fiber_integral_isContDensityOn F E σ h M J hJ R hloc 1 _ _ m hμ hν hfib φ hφc hφs
  have hfin : ∀ S, m S A < ⊤ := fun S => by
    haveI := (GlobalTheory.T.gram_fiber_measure_locallyFinite_and_ne_zero_of_isOpen F E σ h M J hJ R hloc 1 _ _ m hμ hν hfib S).1
    exact hAc.measure_lt_top
  have hint : ∀ S, ∫ X, φ X ∂(m S) = (((m S A).toReal : ℝ) : ℂ) := fun S => by
    rw [hφ, integral_indicator_const _ hAm]
    simp [Measure.real]
  have hcs : Continuous (hermScal R σ (F := F) (E := E)) := continuous_hermScal R

  have hqc : Continuous fun X : Fin 1 → Fin M → R ⊗[F] E =>
      algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (gramR R σ J X 0 0) :=
    continuous_const.mul (htr.comp ((hgr 1 M J).matrix_elem 0 0))
  set K : Set R := (fun X : Fin 1 → Fin M → R ⊗[F] E =>
      algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (gramR R σ J X 0 0)) '' A with hKdef
  have hKc : IsCompact K := hAc.image hqc
  haveI : Nontrivial (R ⊗[F] E) := ⟨1, 0, fun e => by
    have h3 := GlobalTheory.CompanionTheory.SW.FibreRatio.half_trace_tmul (F := F) (E := E) R h (1 : R)
    rw [← Algebra.TensorProduct.one_def, e, map_zero, mul_zero] at h3
    exact zero_ne_one h3⟩
  have hK0 : (0 : R) ∉ K := by
    rintro ⟨X, hX, h0⟩
    have hu : IsUnit (gramR R σ J X).det := hAU hX
    rw [Matrix.det_fin_one, gram_entry R h hJ X] at hu
    simp only at h0
    rw [h0, TensorProduct.zero_tmul] at hu
    exact not_isUnit_zero hu
  have hzero : ∀ s, s ∉ K → m (hermScal R σ s) A = 0 := by
    intro s hs
    refine measure_mono_null ?_ (hfib.1 (hermScal R σ s))
    intro X hX hXG
    apply hs
    refine ⟨X, hX, ?_⟩
    have e : gramR R σ J X = (hermScal R σ s : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) := hXG.1
    show algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (gramR R σ J X 0 0) = s
    rw [e]
    exact qS_hermScal R h s
  have hcont : Continuous (fun s : R => (m (hermScal R σ s) A).toReal) := by
    rw [continuous_iff_continuousAt]
    intro s
    by_cases hs : s = 0
    · subst hs
      have hev : (fun _ : R => (0 : ℝ)) =ᶠ[𝓝 0] fun t : R => (m (hermScal R σ t) A).toReal := by
        filter_upwards [hKc.isClosed.isOpen_compl.mem_nhds hK0] with t ht
        simp [hzero t ht]
      exact continuousAt_const.congr hev
    · have hunit : hermScal R σ s ∈
          {S : HermR R σ 1 | IsUnit (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)).det} := by
        show IsUnit (Matrix.det _)
        rw [Matrix.det_fin_one]
        exact isUnit_tmul R hs
      have hne : ∀ᶠ t in 𝓝 s, t ≠ 0 := isOpen_ne.mem_nhds hs
      have htend : Filter.Tendsto (hermScal R σ) (𝓝 s)
          (𝓝[{S : HermR R σ 1 | IsUnit (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)).det}]
            (hermScal R σ s)) := by
        refine tendsto_nhdsWithin_iff.mpr ⟨hcs.tendsto s, hne.mono fun t ht => ?_⟩
        show IsUnit (Matrix.det _)
        rw [Matrix.det_fin_one]
        exact isUnit_tmul R ht
      have := (Complex.continuous_re.tendsto _).comp ((hg _ hunit).tendsto.comp htend)
      simpa [ContinuousAt, Function.comp_def, hint] using this
  have hsupp : HasCompactSupport (fun s : R => (m (hermScal R σ s) A).toReal) :=
    HasCompactSupport.intro hKc fun s hs => by simp [hzero s hs]
  refine ⟨hcont, hsupp, ?_⟩
  have hνeq : coordHerm R σ b lam 1 = Measure.map (hermScal R σ) lam := by
    ext T hT
    rw [Measure.map_apply hcs.measurable hT,
      ← coordHerm_qS R h htr b lam (hcs.measurable hT : MeasurableSet (hermScal R σ ⁻¹' T))]
    congr 1
    ext S
    simp [hermScal_qS R h S]
  have hgS : ∀ S, m S A = ENNReal.ofReal ((m (hermScal R σ (qS R σ S)) A).toReal) := fun S => by
    rw [hermScal_qS R h S, ENNReal.ofReal_toReal (hfin S).ne]
  have hgm : Measurable fun S : HermR R σ 1 => m S A := by
    have e : (fun S : HermR R σ 1 => m S A) =
        fun S => ENNReal.ofReal ((m (hermScal R σ (qS R σ S)) A).toReal) := funext hgS
    rw [e]
    exact ENNReal.measurable_ofReal.comp (hcont.comp (continuous_qS R htr)).measurable
  have hV : MeasurableSet ({0}ᶜ : Set R) := (measurableSet_singleton 0).compl
  have hP : MeasurableSet {S : HermR R σ 1 | qS R σ S ∈ ({0}ᶜ : Set R)} :=
    (continuous_qS R htr).measurable hV
  have hQ : MeasurableSet {X : Fin 1 → Fin M → R ⊗[F] E |
      algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (gramR R σ J X 0 0) ∈ ({0}ᶜ : Set R)} :=
    hqc.measurable hV
  have heq := mass_eq_lintegral R h hJ hfib hAm (V := {0}ᶜ) (by simp) hQ hP
  have hAQ : A ∩ {X : Fin 1 → Fin M → R ⊗[F] E |
      algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (gramR R σ J X 0 0) ∈ ({0}ᶜ : Set R)} = A := by
    refine Set.inter_eq_left.mpr fun X hX e => hK0 ⟨X, hX, e⟩
  rw [hAQ, ← lintegral_indicator hP] at heq
  have hind : {S : HermR R σ 1 | qS R σ S ∈ ({0}ᶜ : Set R)}.indicator (fun S => m S A) =
      fun S => m S A := by
    funext S
    by_cases hS : S ∈ {S : HermR R σ 1 | qS R σ S ∈ ({0}ᶜ : Set R)}
    · exact Set.indicator_of_mem hS _
    · rw [Set.indicator_of_notMem hS]
      have h0 : qS R σ S = 0 := by simpa using hS
      have e : S = hermScal R σ 0 := by rw [← h0, hermScal_qS R h S]
      rw [e, hzero 0 hK0]
  rw [hind, hνeq, lintegral_map hgm hcs.measurable] at heq
  rw [ofReal_integral_eq_lintegral_ofReal (hcont.integrable_of_hasCompactSupport hsupp)
    (ae_of_all _ fun _ => ENNReal.toReal_nonneg), heq]
  exact lintegral_congr fun s => ENNReal.ofReal_toReal (hfin _).ne

theorem fibre_masses : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (J : Matrix (Fin 2) (Fin 2) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
  (lam : Measure (Fv F v)), IsStdV v lam → ∀ (m : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin 2 → Fv F v ⊗[F] E)),
  IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 2) (coordHerm (Fv F v) σ b lam 1) m →
  ∀ A : Set (Fin 1 → Fin 2 → Fv F v ⊗[F] E), IsCompact A → IsOpen A → A ⊆ {X | IsUnit (gramR (Fv F v) σ J X).det} →
  Continuous (fun s : Fv F v => (m (hermScal (Fv F v) σ s) A).toReal) ∧
  HasCompactSupport (fun s : Fv F v => (m (hermScal (Fv F v) σ s) A).toReal) ∧
  ENNReal.ofReal (∫ s, (m (hermScal (Fv F v) σ s) A).toReal ∂lam) = coordW (Fv F v) b lam 1 2 A := by
  intro F E _ _ _ _ _ σ hσ J hJ d b v lam hlam m hfib A hAc hAo hAU
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  exact masses_field (Fv F v) (GlobalTheory.T.completion_is_local_ring F v) hσ hJ b lam hlam.1 m hfib A hAc hAo hAU

end GlobalTheory.CompanionTheory.SW.FibreCpt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NoetherNormalizationFinite
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace GlobalTheory.CompanionTheory.GeoInteg

theorem away_val_mk {K : Type} [Field K] {N : ℕ} {g : MvPolynomial (Fin (N + 1)) K} {D : ℕ}
    (hg : g ∈ grK K N D) (n : ℕ) (x : MvPolynomial (Fin (N + 1)) K) (hx : x ∈ grK K N (n • D)) :
    (HomogeneousLocalization.Away.mk (grK K N) hg n x hx).val =
      algebraMap _ (Localization.Away g) x * (IsLocalization.Away.invSelf g : Localization.Away g) ^ n := by
  rw [HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk']
  rw [IsLocalization.mk'_eq_iff_eq_mul]
  have h : algebraMap _ (Localization.Away g) g * IsLocalization.Away.invSelf g = 1 :=
    IsLocalization.Away.mul_invSelf g
  simp only [map_pow]
  rw [mul_assoc, ← mul_pow, mul_comm _ (algebraMap _ _ g), h, one_pow, mul_one]

theorem away_relation {K : Type} [Field K] {N : ℕ} {g : MvPolynomial (Fin (N + 1)) K} {D : ℕ}
    (hg : g ∈ grK K N D) (r s : ℕ) (f : MvPolynomial (Fin (N + 1)) K) (hf : f ∈ grK K N (r • D))
    (c : ℕ → MvPolynomial (Fin (N + 1)) K) (hc : ∀ l, c l ∈ grK K N (((s - l) * r) • D))
    (F : MvPolynomial (Fin (N + 1)) K) (hF : F ∈ grK K N ((s * r) • D))
    (hFe : F = f ^ s + ∑ l ∈ Finset.range s, c l * f ^ l) :
    HomogeneousLocalization.Away.mk (grK K N) hg r f hf ^ s +
      ∑ l ∈ Finset.range s, HomogeneousLocalization.Away.mk (grK K N) hg _ (c l) (hc l) *
        HomogeneousLocalization.Away.mk (grK K N) hg r f hf ^ l =
      HomogeneousLocalization.Away.mk (grK K N) hg _ F hF := by
  have val_sum : ∀ (t : Finset ℕ) (u : ℕ → HomogeneousLocalization.Away (grK K N) g),
      (∑ l ∈ t, u l).val = ∑ l ∈ t, (u l).val := fun t u =>
    map_sum (algebraMap (HomogeneousLocalization.Away (grK K N) g) (Localization.Away g)) u t
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_add, HomogeneousLocalization.val_pow,
    HomogeneousLocalization.val_mul, val_sum, away_val_mk]
  rw [hFe]
  simp only [map_add, map_sum, map_mul, map_pow, add_mul, Finset.sum_mul]
  congr 1
  · rw [mul_pow, ← pow_mul, mul_comm s r]
  · refine Finset.sum_congr rfl fun l hl => ?_
    have hl' : l ≤ s := (Finset.mem_range.1 hl).le
    have : s * r = (s - l) * r + r * l := by
      obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le hl'
      simp only [Nat.add_sub_cancel_left]
      ring
    rw [this, pow_add, mul_pow, ← pow_mul]
    ring

theorem rel_mem {K : Type} [Field K] {N : ℕ} {D : ℕ} (r s : ℕ) (f : MvPolynomial (Fin (N + 1)) K)
    (hf : f ∈ grK K N (r • D)) (c : ℕ → MvPolynomial (Fin (N + 1)) K)
    (hc : ∀ l, c l ∈ grK K N (((s - l) * r) • D)) :
    f ^ s + ∑ l ∈ Finset.range s, c l * f ^ l ∈ grK K N ((s * r) • D) := by
  have hf' : f.IsHomogeneous (r • D) := (MvPolynomial.mem_homogeneousSubmodule _ _).1 hf
  refine add_mem ?_ (sum_mem fun l hl => ?_)
  · rw [MvPolynomial.mem_homogeneousSubmodule]
    convert hf'.pow s using 1
    simp only [smul_eq_mul]
    ring
  · have hl' : l ≤ s := (Finset.mem_range.1 hl).le
    rw [MvPolynomial.mem_homogeneousSubmodule]
    convert ((MvPolynomial.mem_homogeneousSubmodule _ _).1 (hc l)).mul (hf'.pow l) using 1
    obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le hl'
    simp only [Nat.add_sub_cancel_left, smul_eq_mul]
    ring

theorem isIntegral_torusS : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N d e : ℕ} (i : X ⟶ PSpace K N) (y : Fin (d + 1) → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) {V : X.Opens} (hV : V ≤ ⨅ k, i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k)), 0 < e → ∀ (q : X ⟶ Spec (CommRingCat.of K)), i ≫ PSpace.str K N = q → Module.Finite (Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk (homIdeal i) (y k))) (MvPolynomial (Fin (N + 1)) K ⧸ homIdeal i) → ∀ (S : Finset (Fin (d + 1))) (hS : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (yS y S)) (ht : ∀ k, IsUnit (tV i y hy V hV k)), letI := (strV q V).toAlgebra; ∀ a, IsIntegral (torusS K (fun k => (ht k).unit) S) (evV i (yS y S) V hS a) := by
  intro K _ X N d e i y hy V hV he q hq hfin S hS ht
  letI := (strV q V).toAlgebra
  intro a
  have hg := yS_mem y hy S
  obtain ⟨r, f, hf, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (grK K N) hg a
  by_cases hS0 : S.card = 0
  ·
    have hf0 : f.IsHomogeneous 0 := by
      have := (MvPolynomial.mem_homogeneousSubmodule _ _).1 hf
      simpa [hS0] using this
    have hfC : f = MvPolynomial.C (MvPolynomial.coeff 0 f) :=
      MvPolynomial.totalDegree_eq_zero_iff_eq_C.1 (Nat.le_zero.1 hf0.totalDegree_le)
    have hc : (MvPolynomial.C (MvPolynomial.coeff 0 f) : MvPolynomial (Fin (d + 1)) K).IsHomogeneous (r * S.card) := by
      rw [hS0, Nat.mul_zero]
      exact MvPolynomial.isHomogeneous_C _ _
    have hmem := GlobalTheory.CompanionTheory.GeoTorus.aeval_mem_torusS i y hy hV he q hq S hS ht _ hc
    have hfe : MvPolynomial.aeval y (MvPolynomial.C (MvPolynomial.coeff 0 f) : MvPolynomial (Fin (d + 1)) K) = f := by
      rw [MvPolynomial.aeval_C]
      exact hfC.symm
    have heq : HomogeneousLocalization.Away.mk (grK K N) hg r (MvPolynomial.aeval y (MvPolynomial.C (MvPolynomial.coeff 0 f) : MvPolynomial (Fin (d + 1)) K)) (aeval_mem y hy S _ hc) = HomogeneousLocalization.Away.mk (grK K N) hg r f hf := by
      simp only [hfe]
    rw [heq] at hmem
    exact isIntegral_algebraMap (R := torusS K (fun k => (ht k).unit) S) (x := ⟨_, hmem⟩)
  · have hD : 0 < S.card * e := Nat.mul_pos (Nat.pos_of_ne_zero hS0) he
    have hfh : f.IsHomogeneous (e * (r * S.card)) := by
      have := (MvPolynomial.mem_homogeneousSubmodule _ _).1 hf
      convert this using 1
      simp only [smul_eq_mul]
      ring
    obtain ⟨s, c, -, hc, hrel⟩ := GlobalTheory.CompanionTheory.Geo.exists_hom_relation (homIdeal i) (GlobalTheory.CompanionTheory.Geo.homIdeal_homog i) e he y hy hfin (r * S.card) f hfh
    have hc' : ∀ l, (c l).IsHomogeneous (((s - l) * r) * S.card) := fun l => by
      rw [mul_assoc]
      exact hc l
    have hcm := fun l => aeval_mem y hy S (c l) (hc' l)
    have hF := rel_mem r s f hf (fun l => MvPolynomial.aeval y (c l)) hcm
    have hid := away_relation hg r s f hf (fun l => MvPolynomial.aeval y (c l)) hcm _ hF rfl
    have hzero := GlobalTheory.CompanionTheory.GeoVanish.homIdeal_vanish i hD hg hF hrel V hS
    rw [← hid] at hzero
    rw [map_add, map_sum] at hzero
    simp only [map_mul, map_pow] at hzero
    have hco := fun l => GlobalTheory.CompanionTheory.GeoTorus.aeval_mem_torusS i y hy hV he q hq S hS ht (c l) (hc' l)
    refine ⟨Polynomial.X ^ s + ∑ l ∈ Finset.range s,
      Polynomial.C (⟨_, hco l⟩ : torusS K (fun k => (ht k).unit) S) * Polynomial.X ^ l, ?_, ?_⟩
    · refine Polynomial.monic_X_pow_add ?_
      rw [← Polynomial.mem_degreeLT]
      refine Submodule.sum_mem _ fun l hl => ?_
      rw [Polynomial.mem_degreeLT]
      refine (Polynomial.degree_C_mul_X_pow_le l _).trans_lt ?_
      exact_mod_cast Finset.mem_range.1 hl
    · simp only [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_finset_sum, Polynomial.eval₂_mul, Polynomial.eval₂_C]
      exact hzero

end GlobalTheory.CompanionTheory.GeoInteg
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfUpwardClosedCover
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.CosieveRel

theorem serre_of_equiv {R : Type} [CommRing R] (𝒮 : Serre.{1} R) {M N : Type 1} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) (h : 𝒮.P M) : 𝒮.P N := by
  refine 𝒮.mid M N PUnit.{2} e.toLinearMap 0 ?_ h (𝒮.zero PUnit.{2} inferInstance)
  intro y
  exact iff_of_true (Subsingleton.elim _ _) ⟨e.symm y, e.apply_symm_apply y⟩

theorem serre_union : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R) {ι : Type}
    (W : ι → ObjectProperty C) (hW : ∀ α ⦃T T' : C⦄, (T ⟶ T') → W α T → (∃ β, W β T') → W α T') (𝒮 : Serre.{1} R) (n : ℕ),
    (∀ p q, p + q = n → 𝒮.P ((cechH F W q).cx.H p)) → 𝒮.P (HU F (fun T => ∃ α, W α T) n) := by
  intro R _ C _ F ι W hW 𝒮 n h
  have hle : ∀ α, W α ≤ (fun T => ∃ β, W β T : ObjectProperty C) := fun α T hT => ⟨α, hT⟩
  refine GlobalTheory.T.serre_class_of_cech_spectral_sequence ((ObjectProperty.ι (fun T => ∃ β, W β T : ObjectProperty C)) ⋙ F)
    (fun α T => W α T.obj) (fun α => by
      intro T T' f hT
      exact hW α f.hom hT T'.property) (fun T => T.property) 𝒮 n ?_
  intro p q hpq
  obtain ⟨e⟩ := GlobalTheory.T.cech_cohomology_full_subcategory_iso F (fun T => ∃ β, W β T : ObjectProperty C) W hle q p
  exact serre_of_equiv 𝒮 e.symm (h p q hpq)

end GlobalTheory.CompanionTheory.CosieveRel
end

