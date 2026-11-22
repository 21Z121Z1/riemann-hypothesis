import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableHermC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0030
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0032
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0034
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.OneSTr
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0035
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle0001

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetWBlockMatrixFormula
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

open MeasureTheory Matrix

theorem one_add_I_blkM_eq {n : ℕ} (b : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → ℂ) (d : ℝ) :
    (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) + Complex.I • blkM b u d =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (1 + Complex.I • b) (Complex.I • Matrix.replicateCol (Fin 1) u)
          (Complex.I • Matrix.replicateRow (Fin 1) (star u))
          (Matrix.of fun _ _ => 1 + Complex.I * (d : ℂ))) := by
  ext i j
  obtain ⟨i', rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j', rfl⟩ := finSumFinEquiv.surjective j
  rcases i' with i' | i' <;> rcases j' with j' | j'
  · simp [blkM, Matrix.one_apply]
  · have h : ¬Fin.castAdd 1 i' = Fin.natAdd n j' := by
      rw [Fin.ext_iff]; simp; omega
    simp [blkM, Matrix.one_apply, h]
  · have h : ¬Fin.natAdd n i' = Fin.castAdd 1 j' := by
      rw [Fin.ext_iff]; simp; omega
    simp [blkM, Matrix.one_apply, h]
  · obtain rfl := Subsingleton.elim i' j'
    simp [blkM]

theorem det_one_add_I_blkM {n : ℕ} (b : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) (d : ℝ) :
    Matrix.det (1 + Complex.I • blkM b ((1 + Complex.I • b) *ᵥ v) d) =
      Matrix.det (1 + Complex.I • b) *
        (1 + Complex.I * (d : ℂ) + star ((1 + Complex.I • b) *ᵥ v) ⬝ᵥ v) := by
  rw [one_add_I_blkM_eq, Matrix.det_reindex_self]
  set D : Matrix (Fin n) (Fin n) ℂ := 1 + Complex.I • b with hD
  set u : Fin n → ℂ := D *ᵥ v with hu
  have hcol : D * Matrix.replicateCol (Fin 1) v = Matrix.replicateCol (Fin 1) u := by
    ext i j
    simp [hu, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  have hmul :
      Matrix.fromBlocks D (Complex.I • Matrix.replicateCol (Fin 1) u)
          (Complex.I • Matrix.replicateRow (Fin 1) (star u))
          (Matrix.of fun _ _ => 1 + Complex.I * (d : ℂ)) *
        Matrix.fromBlocks 1 (-Complex.I • Matrix.replicateCol (Fin 1) v) 0
          (1 : Matrix (Fin 1) (Fin 1) ℂ) =
      Matrix.fromBlocks D 0 (Complex.I • Matrix.replicateRow (Fin 1) (star u))
        (Matrix.of fun _ _ => 1 + Complex.I * (d : ℂ) + star u ⬝ᵥ v) := by
    rw [Matrix.fromBlocks_multiply]
    congr 1
    · simp
    · simp [Matrix.mul_smul, hcol]
    · simp
    · ext i j
      have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
      simp [Matrix.mul_apply, dotProduct, Finset.mul_sum, mul_assoc, mul_left_comm]
      simp only [← mul_assoc, hI, neg_mul, one_mul, Finset.sum_neg_distrib, neg_neg]
      ring
  have hdet := congrArg Matrix.det hmul
  rw [Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₁₂] at hdet
  simpa using hdet

theorem quad_real {n : ℕ} {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian) (v : Fin n → ℂ) :
    ((star v ⬝ᵥ (b *ᵥ v)).re : ℂ) = star v ⬝ᵥ (b *ᵥ v) := by
  have h : star (star v ⬝ᵥ (b *ᵥ v)) = star v ⬝ᵥ (b *ᵥ v) := by
    rw [← Matrix.star_dotProduct, Matrix.star_mulVec, hb.eq, Matrix.dotProduct_mulVec]
  exact Complex.conj_eq_iff_re.1 h

theorem star_mulVec_dot {n : ℕ} {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian)
    (v : Fin n → ℂ) :
    star ((1 + Complex.I • b) *ᵥ v) ⬝ᵥ v =
      ((∑ i, Complex.normSq (v i) : ℝ) : ℂ) - Complex.I * ((star v ⬝ᵥ (b *ᵥ v)).re : ℂ) := by
  rw [quad_real hb, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
  have hH : (1 + Complex.I • b)ᴴ = 1 - Complex.I • b := by
    simp [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hb.eq, sub_eq_add_neg]
  rw [hH, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, dotProduct_sub,
    dotProduct_smul, smul_eq_mul]
  congr 1
  simp [dotProduct, Complex.normSq_eq_conj_mul_self]

theorem normSq_det_one_add_I_blkM (n : ℕ) (b : Matrix (Fin n) (Fin n) ℂ) (hb : b.IsHermitian)
    (_hdet : Matrix.det (1 + Complex.I • b) ≠ 0) (v : Fin n → ℂ) (d : ℝ) :
    Complex.normSq (Matrix.det (1 + Complex.I • blkM b ((1 + Complex.I • b) *ᵥ v) d)) =
      Complex.normSq (Matrix.det (1 + Complex.I • b)) *
        ((1 + ∑ i, Complex.normSq (v i)) ^ 2 + (d - (star v ⬝ᵥ (b *ᵥ v)).re) ^ 2) := by
  rw [det_one_add_I_blkM, map_mul, star_mulVec_dot hb]
  congr 1
  set r : ℝ := ∑ i, Complex.normSq (v i)
  set m : ℝ := (star v ⬝ᵥ (b *ᵥ v)).re
  have : (1 + Complex.I * (d : ℂ) + ((r : ℂ) - Complex.I * (m : ℂ))) =
      (((1 + r : ℝ) : ℂ)) + (((d - m : ℝ) : ℂ)) * Complex.I := by
    push_cast; ring
  rw [this, Complex.normSq_add_mul_I]

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DichotomyOfComparableModSquare
section
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.DichMod

variable {S : Type} [CommRing S]

theorem isUnit_one_sub_mul {ϖ : S} (hJ : ϖ ∈ (⊥ : Ideal S).jacobson) (w : S) :
    IsUnit (1 - w * ϖ) := by
  have h := Ideal.mem_jacobson_bot.mp hJ (-w)
  have e : ϖ * -w + 1 = 1 - w * ϖ := by ring
  rwa [e] at h

theorem dvd_or_dvd {ϖ : S} (hJ : ϖ ∈ (⊥ : Ideal S).jacobson)
    (hc : ∀ f g : S, f ∈ Ideal.span {g, ϖ ^ 2} ∨ g ∈ Ideal.span {f, ϖ ^ 2}) (f : S) :
    ϖ ∣ f ∨ f ∣ ϖ := by
  rcases hc f ϖ with h | h
  · left
    obtain ⟨c, d, e⟩ := Ideal.mem_span_pair.mp h
    exact ⟨c + d * ϖ, by rw [← e]; ring⟩
  · right
    obtain ⟨c, w, e⟩ := Ideal.mem_span_pair.mp h
    have hu := isUnit_one_sub_mul hJ w
    have key : (1 - w * ϖ) * ϖ = c * f := by
      have : c * f = ϖ - w * ϖ ^ 2 := by linear_combination e
      rw [this]; ring
    exact hu.dvd_mul_left.mp (key ▸ dvd_mul_left f c)

theorem comparable {ϖ : S}
    (hc : ∀ f g : S, f ∈ Ideal.span {g, ϖ ^ 2} ∨ g ∈ Ideal.span {f, ϖ ^ 2}) {f g : S}
    (hf : f ∣ ϖ) (hg : g ∣ ϖ) : g ∣ f ∨ f ∣ g := by
  rcases hc f g with h | h
  · left
    obtain ⟨c, d, e⟩ := Ideal.mem_span_pair.mp h
    rw [← e]
    exact dvd_add (dvd_mul_left g c) ((hg.trans (dvd_pow_self ϖ two_ne_zero)).mul_left d)
  · right
    obtain ⟨c, d, e⟩ := Ideal.mem_span_pair.mp h
    rw [← e]
    exact dvd_add (dvd_mul_left f c) ((hf.trans (dvd_pow_self ϖ two_ne_zero)).mul_left d)

theorem dvd_of_high {ϖ : S} (hJ : ϖ ∈ (⊥ : Ideal S).jacobson) {f g a b : S} {N : ℕ}
    (e : a * f + b * g = ϖ ^ N) (h : ϖ ^ (N + 1) ∣ f) : g ∣ f := by
  obtain ⟨t, ht⟩ := h
  have hu := isUnit_one_sub_mul hJ (a * t)
  have key : (1 - a * t * ϖ) * ϖ ^ N = b * g := by
    have : b * g = ϖ ^ N - a * f := by linear_combination e
    rw [this, ht]; ring
  have hg : g ∣ ϖ ^ N := hu.dvd_mul_left.mp (key ▸ dvd_mul_left g b)
  exact hg.trans ⟨ϖ * t, by rw [ht]; ring⟩

theorem dvd_of_lt {ϖ f g f' g' : S} {i j : ℕ} (hf : f = ϖ ^ i * f') (hg : g = ϖ ^ j * g')
    (hf' : f' ∣ ϖ) (hij : i < j) : f ∣ g := by
  have h1 : f ∣ ϖ ^ (i + 1) := by
    rw [hf, pow_succ]
    exact mul_dvd_mul_left _ hf'
  have h2 : ϖ ^ (i + 1) ∣ g := by
    rw [hg]
    exact (pow_dvd_pow ϖ hij).mul_right g'
  exact h1.trans h2

theorem dich_of_mod : ∀ {S : Type} [CommRing S] (ϖ : S), ϖ ∈ (⊥ : Ideal S).jacobson →
    (∀ f g : S, f ∈ Ideal.span {g, ϖ ^ 2} ∨ g ∈ Ideal.span {f, ϖ ^ 2}) → Dich ϖ := by
  intro S _ ϖ hJ hc f g hN
  obtain ⟨N, hN⟩ := hN
  obtain ⟨a, b, e⟩ := Ideal.mem_span_pair.mp hN
  have hd := dvd_or_dvd hJ hc
  rcases GlobalTheory.CompanionTheory.NormalForm.normal_form_of_dichotomy ϖ hd f (N + 1) with hf | ⟨i, f', hf, hf'⟩
  · exact Or.inl (dvd_of_high hJ e hf)
  rcases GlobalTheory.CompanionTheory.NormalForm.normal_form_of_dichotomy ϖ hd g (N + 1) with hg | ⟨j, g', hg, hg'⟩
  · exact Or.inr (dvd_of_high hJ (by rw [add_comm]; exact e) hg)
  rcases lt_trichotomy i j with hij | hij | hij
  · exact Or.inr (dvd_of_lt hf hg hf' hij)
  · subst hij
    rw [hf, hg]
    rcases comparable hc hf' hg' with h | h
    · exact Or.inl (mul_dvd_mul_left _ h)
    · exact Or.inr (mul_dvd_mul_left _ h)
  · exact Or.inl (dvd_of_lt hg hf hg' hij)

end GlobalTheory.CompanionTheory.DichMod
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DisintegrationInjectiveOpenMap
section
open MeasureTheory Topology
open scoped ENNReal NNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.FibreDensityLimit

open Set

theorem ofReal_le_of_forall_compact {X : Type} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (ν : Measure X) [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure]
    {a b : X → ℝ} (ha : Continuous a) (hb : Continuous b) (c : ℝ)
    (h : ∀ A : Set X, IsCompact A → ∫⁻ s in A, ENNReal.ofReal (a s) ∂ν ≤
      ∫⁻ s in A, ENNReal.ofReal (b s) ∂ν + ENNReal.ofReal c * ν A) (s₀ : X) :
    ENNReal.ofReal (a s₀) ≤ ENNReal.ofReal (b s₀) + ENNReal.ofReal c := by
  by_contra hlt
  rw [not_le] at hlt
  have hFc : Continuous fun s => ENNReal.ofReal (a s) := ENNReal.continuous_ofReal.comp ha
  have hGc : Continuous fun s => ENNReal.ofReal (b s) + ENNReal.ofReal c :=
    (ENNReal.continuous_ofReal.comp hb).add continuous_const
  have hopen : IsOpen {s | ENNReal.ofReal (b s) + ENNReal.ofReal c < ENNReal.ofReal (a s)} :=
    isOpen_lt hGc hFc
  obtain ⟨A, hAn, hAW, hAc⟩ := local_compact_nhds (hopen.mem_nhds hlt)
  have hAm : MeasurableSet A := hAc.measurableSet
  have hpos : ν A ≠ 0 := (MeasureTheory.Measure.measure_pos_of_mem_nhds ν hAn).ne'
  have hsplit : ∫⁻ s in A, (ENNReal.ofReal (b s) + ENNReal.ofReal c) ∂ν =
      ∫⁻ s in A, ENNReal.ofReal (b s) ∂ν + ENNReal.ofReal c * ν A := by
    rw [lintegral_add_right _ measurable_const, setLIntegral_const]
  have hfin : ∫⁻ s in A, (ENNReal.ofReal (b s) + ENNReal.ofReal c) ∂ν ≠ ∞ := by
    have hbi : IntegrableOn b A ν := hb.continuousOn.integrableOn_compact hAc
    rw [hsplit]
    exact ENNReal.add_ne_top.mpr ⟨hbi.lintegral_lt_top.ne,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hAc.measure_lt_top.ne⟩
  have hstrict := setLIntegral_strict_mono hAm hpos hFc.measurable hfin
    (Filter.Eventually.of_forall fun s hs => hAW hs)
  rw [hsplit] at hstrict
  exact absurd (h A hAc) (not_le.mpr hstrict)

private lemma exists_continuous_compactSupport_eq_one_on_compact {V : Type} [TopologicalSpace V] [LocallyCompactSpace V] [T2Space V]
    {K U : Set V} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ ψ : V → ℝ, Continuous ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ U ∧
      (∀ v, 0 ≤ ψ v ∧ ψ v ≤ 1) ∧ ∀ v ∈ K, ψ v = 1 := by
  obtain ⟨L, -, hLc, hKL, hLU⟩ := exists_compact_closed_between hK hU hKU
  obtain ⟨φ, hφ1, hφ0, hφs, hφb⟩ := exists_continuous_one_zero_of_isCompact hK
    isOpen_interior.isClosed_compl (disjoint_compl_right_iff_subset.mpr hKL)
  refine ⟨φ, φ.continuous, hφs, ?_, fun v => hφb v, fun v hv => hφ1 hv⟩
  refine (closure_minimal ?_ hLc).trans hLU
  intro v hv
  by_contra hvL
  exact hv (hφ0 (fun hi => hvL (interior_subset hi)))

theorem exists_cutoffs {V : Type} [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V]
    [T2Space V] {U : Set V} (hU : IsOpen U) :
    ∃ χ : ℕ → V → ℝ, (∀ n, Continuous (χ n)) ∧ (∀ n, HasCompactSupport (χ n)) ∧
      (∀ n, tsupport (χ n) ⊆ U) ∧ (∀ n v, 0 ≤ χ n v ∧ χ n v ≤ 1) ∧
      (∀ v, Monotone fun n => χ n v) ∧ ∀ v ∈ U, ∃ n, χ n v = 1 := by
  classical
  have : LocallyCompactSpace U := hU.locallyCompactSpace
  let Kn : ℕ → Set V := fun n => Subtype.val '' compactCovering U n
  have hKc : ∀ n, IsCompact (Kn n) := fun n =>
    (isCompact_compactCovering U n).image continuous_subtype_val
  have hKU : ∀ n, Kn n ⊆ U := by
    rintro n _ ⟨x, -, rfl⟩
    exact x.2
  have hcov : ∀ v ∈ U, ∃ n, v ∈ Kn n := by
    intro v hv
    have hmem : (⟨v, hv⟩ : U) ∈ ⋃ n, compactCovering U n := by
      rw [iUnion_compactCovering]
      trivial
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hmem
    exact ⟨n, ⟨v, hv⟩, hn, rfl⟩
  choose ψ hψc hψs hψU hψb hψ1 using fun n => exists_continuous_compactSupport_eq_one_on_compact (hKc n) hU (hKU n)
  have hsup : ∀ a b : V → ℝ, HasCompactSupport a → HasCompactSupport b →
      tsupport (a ⊔ b) ⊆ tsupport a ∪ tsupport b := by
    intro a b _ _
    refine closure_minimal ?_ ((isClosed_tsupport a).union (isClosed_tsupport b))
    intro v hv
    by_contra hc
    simp only [Set.mem_union, not_or] at hc
    apply hv
    simp [image_eq_zero_of_notMem_tsupport hc.1, image_eq_zero_of_notMem_tsupport hc.2]
  have hP : ∀ n, Continuous (partialSups ψ n) ∧ HasCompactSupport (partialSups ψ n) ∧
      tsupport (partialSups ψ n) ⊆ U ∧ ∀ v, 0 ≤ partialSups ψ n v ∧ partialSups ψ n v ≤ 1 := by
    intro n
    induction n with
    | zero =>
      rw [partialSups_zero]
      exact ⟨hψc 0, hψs 0, hψU 0, hψb 0⟩
    | succ n ih =>
      obtain ⟨h1, h2, h3, h4⟩ := ih
      have hs : partialSups ψ (n + 1) = partialSups ψ n ⊔ ψ (n + 1) := partialSups_succ ψ n
      rw [hs]
      refine ⟨h1.sup (hψc (n + 1)), ?_, ?_, fun v => ?_⟩
      · exact (h2.union (hψs (n + 1))).of_isClosed_subset (isClosed_tsupport _)
          (hsup _ _ h2 (hψs (n + 1)))
      · exact (hsup _ _ h2 (hψs (n + 1))).trans (Set.union_subset h3 (hψU (n + 1)))
      · exact ⟨le_sup_of_le_left (h4 v).1, sup_le (h4 v).2 (hψb (n + 1) v).2⟩
  refine ⟨fun n => partialSups ψ n, fun n => (hP n).1, fun n => (hP n).2.1, fun n => (hP n).2.2.1,
    fun n => (hP n).2.2.2, fun v m n hmn => (partialSups ψ).monotone hmn v, fun v hv => ?_⟩
  obtain ⟨n, hn⟩ := hcov v hv
  refine ⟨n, le_antisymm ((hP n).2.2.2 v).2 ?_⟩
  rw [← hψ1 n v hn]
  exact le_partialSups ψ n v

section Family

variable {V X Y : Type} [MeasurableSpace V] [TopologicalSpace V] [TopologicalSpace X] [MeasurableSpace X]
  {μ : Measure V} {ν : Measure X} {f : V → Y} {g : V → X} {ι : X → Y} {U : Set V} {fib : X → Measure V}

theorem lintegral_slice (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν univ fib) (hUm : MeasurableSet U)
    (hι : Function.Injective ι) (hg : Measurable g) (hfg : ∀ v, f v = ι (g v)) {w : V → ℝ≥0∞}
    (hw : Measurable w) (hw0 : ∀ v, v ∉ U → w v = 0) {A : Set X} (hA : MeasurableSet A) :
    ∫⁻ v in f ⁻¹' (ι '' A), w v ∂μ = ∫⁻ s in A, ∫⁻ v, w v ∂(fib s) ∂ν := by
  have hpre : f ⁻¹' (ι '' A) = g ⁻¹' A := by
    ext v
    simp only [Set.mem_preimage, Set.mem_image, hfg]
    exact ⟨fun ⟨x, hx, he⟩ => hι he ▸ hx, fun hv => ⟨g v, hv, rfl⟩⟩
  rw [hpre]
  have hgA : MeasurableSet (g ⁻¹' A) := hg hA
  rw [← lintegral_indicator hgA, ← lintegral_indicator hA]
  have hsupp : Function.support ((g ⁻¹' A).indicator w) ⊆ U := by
    intro v hv
    by_contra hU
    apply hv
    simp [Set.indicator, hw0 v hU]
  rw [← setLIntegral_eq_of_support_subset hsupp, h.2.1 _ (hw.indicator hgA)]
  refine lintegral_congr fun s => ?_
  have hae : ∀ᵐ v ∂(fib s), v ∈ f ⁻¹' {ι s} ∩ U := (MeasureTheory.mem_ae_iff).mpr (h.1 s)
  by_cases hs : s ∈ A
  · rw [Set.indicator_of_mem hs]
    refine lintegral_congr_ae (hae.mono fun v hv => ?_)
    have hgv : g v = s := hι (by rw [← hfg]; exact hv.1)
    rw [Set.indicator_of_mem (show v ∈ g ⁻¹' A by rw [Set.mem_preimage, hgv]; exact hs)]
  · rw [Set.indicator_of_notMem hs]
    refine (lintegral_congr_ae (hae.mono fun v hv => ?_)).trans lintegral_zero
    have hgv : g v = s := hι (by rw [← hfg]; exact hv.1)
    rw [Set.indicator_of_notMem (show v ∉ g ⁻¹' A by rw [Set.mem_preimage, hgv]; exact hs)]

theorem lintegral_slice_test (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν univ fib)
    [BorelSpace V] (hUm : MeasurableSet U)
    (hι : Function.Injective ι) (hg : Measurable g) (hfg : ∀ v, f v = ι (g v)) {ψ : V → ℝ}
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ U) (hψ0 : ∀ v, 0 ≤ ψ v)
    {A : Set X} (hA : MeasurableSet A) :
    ∫⁻ v in f ⁻¹' (ι '' A), ENNReal.ofReal (ψ v) ∂μ =
      ∫⁻ s in A, ENNReal.ofReal (∫ v, ψ v ∂(fib s)) ∂ν := by
  have hw0 : ∀ v, v ∉ U → ENNReal.ofReal (ψ v) = 0 := by
    intro v hv
    rw [image_eq_zero_of_notMem_tsupport (fun h' => hv (hψU h')), ENNReal.ofReal_zero]
  rw [lintegral_slice (w := fun v => ENNReal.ofReal (ψ v)) h hUm hι hg hfg
    (ENNReal.measurable_ofReal.comp hψ.measurable) hw0 hA]
  refine lintegral_congr fun s => ?_
  rw [ofReal_integral_eq_lintegral_ofReal ((h.2.2 ψ hψ hψc hψU).1 s (Set.mem_univ s))
    (Filter.Eventually.of_forall hψ0)]

end Family

theorem fibre_lintegral_eq_density : ∀ (V X Y : Type) [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X) [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure] (f : V → Y) (g : V → X) (ι : X → Y), Function.Injective ι → Continuous g → (∀ v, f v = ι (g v)) → ∀ (U : Set V) (fib : X → Measure V), IsOpen U → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν Set.univ fib → ∀ φ : V → ℝ, Continuous φ → (∀ v, 0 ≤ φ v) → ∀ D : X → ℝ, Continuous D → (∀ A : Set X, MeasurableSet A → ∫⁻ v in f ⁻¹' (ι '' A), ENNReal.ofReal (φ v) ∂μ = ∫⁻ s in A, ENNReal.ofReal (D s) ∂ν) → (∀ ε : ℝ, 0 < ε → ∃ K : Set V, IsCompact K ∧ K ⊆ U ∧ ∀ A : Set X, MeasurableSet A → ∫⁻ v in f ⁻¹' (ι '' A) ∩ Kᶜ, ENNReal.ofReal (φ v) ∂μ ≤ ENNReal.ofReal ε * ν A) → ∀ s₀ : X, ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib s₀) = ENNReal.ofReal (D s₀) := by
  intro V X Y _ _ _ _ _ _ _ _ _ _ _ _ μ ν _ _ f g ι hι hgc hfg U fib hUo h φ hφ hφ0 D hD hDA hK s0
  have hg : Measurable g := hgc.measurable
  have hUm : MeasurableSet U := hUo.measurableSet
  have htest : ∀ ψ : V → ℝ, Continuous ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      (∀ v, 0 ≤ ψ v) → (∀ v, ψ v ≤ φ v) →
      ENNReal.ofReal (∫ v, ψ v ∂(fib s0)) ≤ ENNReal.ofReal (D s0) := by
    intro ψ hψ hψc hψU hψ0 hψφ
    have hcont : Continuous fun s => ∫ v, ψ v ∂(fib s) :=
      continuousOn_univ.mp (h.2.2 ψ hψ hψc hψU).2
    have hcmp : ∀ A : Set X, IsCompact A →
        ∫⁻ s in A, ENNReal.ofReal (∫ v, ψ v ∂(fib s)) ∂ν ≤
          ∫⁻ s in A, ENNReal.ofReal (D s) ∂ν + ENNReal.ofReal 0 * ν A := by
      intro A hA
      rw [ENNReal.ofReal_zero, zero_mul, add_zero,
        ← lintegral_slice_test h hUm hι hg hfg hψ hψc hψU hψ0 hA.measurableSet,
        ← hDA A hA.measurableSet]
      exact lintegral_mono fun v => ENNReal.ofReal_le_ofReal (hψφ v)
    simpa using ofReal_le_of_forall_compact ν hcont hD 0 hcmp s0
  have hae : ∀ᵐ v ∂(fib s0), v ∈ f ⁻¹' {ι s0} ∩ U := (MeasureTheory.mem_ae_iff).mpr (h.1 s0)
  have hint : ∀ θ : V → ℝ, Continuous θ → HasCompactSupport θ → tsupport θ ⊆ U → (∀ v, 0 ≤ θ v) →
      ENNReal.ofReal (∫ v, θ v ∂(fib s0)) = ∫⁻ v, ENNReal.ofReal (θ v) ∂(fib s0) :=
    fun θ hθ hθc hθU hθ0 => ofReal_integral_eq_lintegral_ofReal
      ((h.2.2 θ hθ hθc hθU).1 s0 (Set.mem_univ _)) (Filter.Eventually.of_forall hθ0)
  obtain ⟨χ, hχc, hχs, hχU, hχb, hχm, hχ1⟩ := exists_cutoffs hUo
  have hψn : ∀ n, ∫⁻ v, ENNReal.ofReal (χ n v * φ v) ∂(fib s0) ≤ ENNReal.ofReal (D s0) := by
    intro n
    have hc : Continuous fun v => χ n v * φ v := (hχc n).mul hφ
    have hs : HasCompactSupport fun v => χ n v * φ v := (hχs n).mul_right
    have hsU : tsupport (fun v => χ n v * φ v) ⊆ U := tsupport_mul_subset_left.trans (hχU n)
    have h0 : ∀ v, 0 ≤ χ n v * φ v := fun v => mul_nonneg (hχb n v).1 (hφ0 v)
    rw [← hint _ hc hs hsU h0]
    exact htest _ hc hs hsU h0 fun v => mul_le_of_le_one_left (hφ0 v) (hχb n v).2
  have hX : ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib s0) ≤ ENNReal.ofReal (D s0) := by
    have heq : ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib s0) =
        ∫⁻ v, ⨆ n, ENNReal.ofReal (χ n v * φ v) ∂(fib s0) := by
      refine lintegral_congr_ae (hae.mono fun v hv => ?_)
      obtain ⟨n, hn⟩ := hχ1 v hv.2
      refine le_antisymm (le_iSup_of_le n (by rw [hn, one_mul])) (iSup_le fun m => ?_)
      exact ENNReal.ofReal_le_ofReal (mul_le_of_le_one_left (hφ0 v) (hχb m v).2)
    rw [heq, lintegral_iSup (f := fun n v => ENNReal.ofReal (χ n v * φ v)) (fun n => ENNReal.measurable_ofReal.comp ((hχc n).mul hφ).measurable)
      (fun m n hmn v => ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hχm v hmn) (hφ0 v)))]
    exact iSup_le hψn
  refine le_antisymm hX (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_)
  obtain ⟨K, hKc, hKU, hKε⟩ := hK ε (NNReal.coe_pos.mpr hε)
  obtain ⟨L, -, hLc, hKL, hLU⟩ := exists_compact_closed_between hKc hUo hKU
  obtain ⟨ψ, hψ1, hψ0', hψs, hψb⟩ := exists_continuous_one_zero_of_isCompact hKc
    isOpen_interior.isClosed_compl (disjoint_compl_right_iff_subset.mpr hKL)
  have hψU : tsupport ψ ⊆ U := by
    refine (closure_minimal ?_ hLc).trans hLU
    intro v hv
    by_contra hvL
    exact hv (hψ0' (fun hi => hvL (interior_subset hi)))
  have hc : Continuous fun v => ψ v * φ v := ψ.continuous.mul hφ
  have hs : HasCompactSupport fun v => ψ v * φ v := hψs.mul_right
  have hsU : tsupport (fun v => ψ v * φ v) ⊆ U := tsupport_mul_subset_left.trans hψU
  have h0 : ∀ v, 0 ≤ ψ v * φ v := fun v => mul_nonneg (hψb v).1 (hφ0 v)
  have hcont : Continuous fun s => ∫ v, ψ v * φ v ∂(fib s) :=
    continuousOn_univ.mp (h.2.2 _ hc hs hsU).2
  have hcmp : ∀ A : Set X, IsCompact A →
      ∫⁻ s in A, ENNReal.ofReal (D s) ∂ν ≤
        ∫⁻ s in A, ENNReal.ofReal (∫ v, ψ v * φ v ∂(fib s)) ∂ν + ENNReal.ofReal ε * ν A := by
    intro A hA
    have hAm := hA.measurableSet
    rw [← hDA A hAm, ← lintegral_slice_test h hUm hι hg hfg hc hs hsU h0 hAm]
    calc ∫⁻ v in f ⁻¹' (ι '' A), ENNReal.ofReal (φ v) ∂μ
        ≤ ∫⁻ v in f ⁻¹' (ι '' A), (ENNReal.ofReal (ψ v * φ v) +
            Kᶜ.indicator (fun v => ENNReal.ofReal (φ v)) v) ∂μ := by
          refine lintegral_mono fun v => ?_
          by_cases hv : v ∈ K
          · rw [Set.indicator_of_notMem (show v ∉ Kᶜ from fun h' => h' hv), add_zero, hψ1 hv, Pi.one_apply, one_mul]
          · rw [Set.indicator_of_mem hv]
            exact le_add_self
      _ = ∫⁻ v in f ⁻¹' (ι '' A), ENNReal.ofReal (ψ v * φ v) ∂μ +
            ∫⁻ v in f ⁻¹' (ι '' A) ∩ Kᶜ, ENNReal.ofReal (φ v) ∂μ := by
          rw [lintegral_add_left (f := fun v => ENNReal.ofReal (ψ v * φ v))
              (ENNReal.measurable_ofReal.comp hc.measurable),
            setLIntegral_indicator hKc.measurableSet.compl, Set.inter_comm]
      _ ≤ ∫⁻ v in f ⁻¹' (ι '' A), ENNReal.ofReal (ψ v * φ v) ∂μ + ENNReal.ofReal ε * ν A := by
          gcongr
          exact hKε A hAm
  have hmain := ofReal_le_of_forall_compact ν hD hcont ε hcmp s0
  rw [hint _ hc hs hsU h0, ENNReal.ofReal_coe_nnreal] at hmain
  refine hmain.trans (add_le_add ?_ le_rfl)
  exact lintegral_mono fun v => ENNReal.ofReal_le_ofReal (mul_le_of_le_one_left (hφ0 v) (hψb v).2)

end GlobalTheory.CompanionTheory.FibreDensityLimit
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerQuotientExists
section
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.PdTF

theorem exists_dividedPowers_map_quotient {S : Type} [CommRing S] (hS : TF S) (I J : Ideal S)
    (hI : PdI I)
    (hJ : ∀ x ∈ I, x ∈ J → ∀ k : ℕ, k ≠ 0 → ∀ y : S, (k.factorial : S) * y = x ^ k → y ∈ J) :
    ∃ δ : DividedPowers (I.map (Ideal.Quotient.mk J)), IsPd (Ideal.Quotient.mk J) I δ := by
  obtain ⟨δ₀, -, hδ₀⟩ := exists_dividedPowers hS I hI
  have hsub : DividedPowers.IsSubDPIdeal δ₀ (J ⊓ I) :=
    { isSubideal := inf_le_right
      dpow_mem := fun n hn j hj =>
        ⟨hJ j hj.2 hj.1 n hn _ (δ₀.factorial_mul_dpow_eq_pow hj.2),
          δ₀.dpow_mem hn hj.2⟩ }
  refine ⟨DividedPowers.Quotient.dividedPowers δ₀ hsub, rfl, fun k x y hx e => ?_⟩
  rw [DividedPowers.Quotient.dpow_apply δ₀ hsub hx]
  exact congrArg _ (hδ₀ k x y hx e)

end GlobalTheory.CompanionTheory.PdTF
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsBaseChangeEquiv
section
open TensorProduct

namespace GlobalTheory.CompanionTheory.ExteriorBase

theorem exists_baseChange_equiv (A R M : Type) [CommRing A] [CommRing R] [Algebra A R]
    [AddCommGroup M] [Module A M] (a : ℕ) :
    ∃ e : R ⊗[A] (⋀[A]^a M) ≃ₗ[R] ⋀[R]^a (R ⊗[A] M), ∀ (r : R) (m : Fin a → M),
      e (r ⊗ₜ exteriorPower.ιMulti A a m) =
        r • exteriorPower.ιMulti R a (fun k => (1 : R) ⊗ₜ[A] m k) := by
  have h := GlobalTheory.TopForm.isBaseChange_exteriorPower (TensorProduct.isBaseChange A M R) a
  refine ⟨h.equiv, fun r m => ?_⟩
  rw [h.equiv_tmul, GlobalTheory.exteriorPowerMapOver_ιMulti]
  rfl

end GlobalTheory.CompanionTheory.ExteriorBase
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRealizationOfCompatibleStatement
section
open CrystallineSemistableComparison.Pb.Kap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_realization_of_compatible : ∀ {Λ A B K : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K] (C : Chain.{1} Λ A B K) (hC : C.Good) {j : ℕ} (x : ∀ n, C.S n j), C.Comp x → ∃ f : Module.Dual K (C.V j) →+ B, C.Rho x f := by
  first | exact @GlobalTheory.CompanionTheory.KapRho.exists_rho | exact GlobalTheory.CompanionTheory.KapRho.exists_rho | (intros; apply GlobalTheory.CompanionTheory.KapRho.exists_rho <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrobeniusPowerSolutionLiftStatement
section
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_power_solution_lift : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](S : Type) [CommRing S] [Algebra A S] (B : Type) [CommRing B] [Algebra A B] (i : S →ₐ[A] B) (I : Ideal S) (m n : ℕ) (a : Fin m → Fin n → A) (c : Fin m → A), (p : A) = 0 → PQ p (i : S →+* B) I → Solv B a c → ∃ (k : ℕ) (s : Fin n → S), ∀ t, ∑ j, a t j ^ p ^ k • s j - algebraMap A S (c t ^ p ^ k) ∈ I := by
  first | exact @GlobalTheory.CompanionTheory.PerfectQuotient.solv_pow | exact GlobalTheory.CompanionTheory.PerfectQuotient.solv_pow | (intros; apply GlobalTheory.CompanionTheory.PerfectQuotient.solv_pow <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainFibrationVolumeStatement
section
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fundamental_domain_fibration_volume : ∀ (N : Type) [Group N] [TopologicalSpace N] [IsTopologicalGroup N] [LocallyCompactSpace N] [SecondCountableTopology N] [T2Space N] [MeasurableSpace N] [BorelSpace N] (ν : Measure N) [ν.IsHaarMeasure] (Γ : Subgroup N) [Countable Γ] (𝓕N : Set N), IsFundamentalDomain Γ 𝓕N ν → ν 𝓕N < ⊤ → ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (dA : Measure V) [dA.IsAddHaarMeasure] (Λ : AddSubgroup V) [Countable Λ] (D : Set V), IsAddFundamentalDomain Λ D dA → dA D = 1 → ∀ l : N → V, Continuous l → (∀ x y, l (x * y) = l x + l y) → Function.Surjective l → (∀ γ ∈ Γ, l γ ∈ Λ) → ∀ f : V → ℝ≥0∞, Measurable f → ∫⁻ m in 𝓕N, ∑' a : Λ, f ((a : V) + l m⁻¹) ∂ν = ν 𝓕N * ∫⁻ x, f x ∂dA := by
  first | exact @GlobalTheory.CompanionTheory.SW.PeriodisedMean.setLIntegral_tsum_comp_inv_eq | exact GlobalTheory.CompanionTheory.SW.PeriodisedMean.setLIntegral_tsum_comp_inv_eq | (intros; apply GlobalTheory.CompanionTheory.SW.PeriodisedMean.setLIntegral_tsum_comp_inv_eq <;> assumption)
end

