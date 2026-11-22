import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsHalfPtIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0006
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalStarComplexMultiplicationPoints
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0296
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0233
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaNormUnimodularLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0239
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0014
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemStabGLAdeleIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0025
import Formalism.LocalRingCardinality.DataTheta
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0173
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0164
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0004
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0036
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Formalism.LocalToGlobal.UnitaryNorms.MemFIffReal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPeriodPairBaseLat
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric NumberField GlobalTheory.Mem.Per
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.Per.ConjCM

open GlobalTheory.ConjPoint

theorem transfer {L L' : PeriodPair} (σ : ℂ ≃+* ℂ)
    (hj : σ (1728 * L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) = 1728 * L'.g₂ ^ 3 / (L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2))
    {α : ℂ} (hα : ∀ l ∈ L.lattice, α * l ∈ L.lattice) {t : ℂ} (h2 : 2 * t ∈ L.lattice)
    (ha : α * t ∉ L.lattice) (hb : (1 - α) * t ∉ L.lattice) :
    (∀ l ∈ L'.lattice, σ α * l ∈ L'.lattice) ∧
      ∃ t', 2 * t' ∈ L'.lattice ∧ σ α * t' ∉ L'.lattice ∧ (1 - σ α) * t' ∉ L'.lattice := by
  have h0 := GlobalTheory.g₂_cube_sub_g₃_sq_ne_zero L
  have h0' := GlobalTheory.g₂_cube_sub_g₃_sq_ne_zero L'
  have hσ0 : σ L.g₂ ^ 3 - 27 * σ L.g₃ ^ 2 ≠ 0 := by
    have := (map_ne_zero σ).2 h0
    simpa [map_ofNat] using this
  obtain ⟨M, m₂, m₃⟩ := GlobalTheory.LatticeInvariants.exists_periodPair_of_invariants hσ0
  simp only [map_div₀, map_mul, map_sub, map_pow, map_ofNat] at hj
  rw [div_eq_div_iff hσ0 h0'] at hj
  obtain ⟨c, hc⟩ := GlobalTheory.exists_isHomothetic_of_j_eq (L := M) (L' := L')
    (by rw [m₂, m₃]; linear_combination hj / 1728)
  have hc0 := hc.ne_zero
  obtain ⟨s, -, hs⟩ := exists_conjEquiv m₂ m₃
  obtain ⟨u, hu⟩ := GlobalTheory.latticePoint_surjective M (s (GlobalTheory.latticePoint L t))
  have hu' : IsConj L M σ t u := (hs _ _).2 hu.symm
  have hβ : ∀ l ∈ L.lattice, (1 - α) * l ∈ L.lattice := fun l hl => by
    rw [sub_mul, one_mul]; exact sub_mem hl (hα l hl)
  refine ⟨fun l hl => ?_, c * u, ?_, ?_, ?_⟩
  · have h1 : c⁻¹ * l ∈ M.lattice := (hc _).1 (by simpa [hc0] using hl)
    have h3 := IsConj.mul m₂ m₃ hα (t := 0) (t' := c⁻¹ * l) (.inl ⟨zero_mem _, h1⟩)
    rcases h3 with h | h
    · have := (hc _).2 h.2
      rwa [show c * (σ α * (c⁻¹ * l)) = σ α * l by field_simp] at this
    · exact absurd (by simp) h.1
  · have := (hc _).2 ((hu'.nsmul_mem_iff m₂ m₃ 2).1 (by exact_mod_cast h2))
    rwa [show c * (((2 : ℕ) : ℂ) * u) = 2 * (c * u) by push_cast; ring] at this
  · rw [mul_left_comm, hc]
    exact ((IsConj.mul m₂ m₃ hα hu').resolve_left fun h => ha h.1).2.1
  · rw [mul_left_comm, hc]
    have := ((IsConj.mul m₂ m₃ hβ hu').resolve_left fun h => hb h.1).2.1
    rwa [map_sub, map_one] at this

variable {R : Ranks} (H : Host R)

theorem mem_baseLat (w : ℂ) :
    w ∈ baseLat H ↔ ∃ c ∈ H.ccK, w = H.φ₀ (((c : H.K) : H.E)) := by
  constructor
  · intro hw
    induction hw using AddSubgroup.closure_induction with
    | mem x hx => exact hx
    | zero => exact ⟨0, H.ccK.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, rfl⟩ := hx
      obtain ⟨c', hc', rfl⟩ := hy
      exact ⟨c + c', H.ccK.add_mem hc hc', by simp⟩
    | neg x _ hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      exact ⟨-c, H.ccK.neg_mem hc, by simp⟩
  · exact fun hw => AddSubgroup.subset_closure hw

theorem exists_periodPair_baseLat : ∃ L : PeriodPair, ∀ z, z ∈ baseLat H ↔ z ∈ L.lattice := by
  have hr : Module.finrank ℚ H.K = 2 :=
    Formalism.FrobeniusOrbits.SplitK.finrank_K H.hyp.2.1.pos (H.sqd_sq)
  have hd : NumberField.discr H.K = -(H.d : ℤ) :=
    GlobalTheory.discr_eq_neg_of_sq_eq hr H.hyp.2.1.squarefree
      (by have := H.hyp.2.2.2.1; omega)
      (Formalism.FrobeniusOrbits.SplitK.bK_sq (H.sqd_sq))
  let σ : H.K →+* ℂ := H.φ₀.comp H.K.val.toRingHom
  let I : (Ideal (𝓞 H.K))⁰ := ⟨H.ccK, mem_nonZeroDivisors_of_ne_zero H.ccK_ne_bot⟩
  obtain ⟨L, hL⟩ := GlobalTheory.QuadraticZeta.exists_periodPair hr hd σ (FractionalIdeal.mk0 H.K I)
  refine ⟨L, fun z => ?_⟩
  rw [mem_baseLat, ← SetLike.mem_coe (p := L.lattice), hL]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨(c : H.K), FractionalIdeal.mem_coeIdeal_of_mem _ hc, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨c, hc, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
    exact ⟨c, hc, rfl⟩

theorem exists_int_root : ∃ a : 𝓞 H.K, (2 * H.φ₀ (((a : H.K) : H.E)) - 1) ^ 2 = -(H.d : ℂ) := by
  have hsq := H.sqd_sq
  let b : H.K := ⟨H.sqd, IntermediateField.mem_adjoin_simple_self ℚ _⟩
  have hb' : b ^ 2 = -(H.d : H.K) := by
    apply Subtype.ext
    simpa using hsq
  refine ⟨⟨(1 + b) / 2, GlobalTheory.NormSum.isIntegral_half_one_add _ H.hyp.2.2.2.1 b hb'⟩, ?_⟩
  change (2 * H.φ₀ (algebraMap H.K H.E ((1 + b) / 2)) - 1) ^ 2 = _
  have := congrArg (fun x => H.φ₀ (algebraMap H.K H.E x)) hb'
  simp only [map_pow, map_neg, map_natCast] at this
  rw [map_div₀, map_add, map_one, map_ofNat, map_div₀, map_add, map_one, map_ofNat, ← this]
  ring

theorem root_cases {d : ℕ} {α : ℂ} (h : (2 * α - 1) ^ 2 = -(d : ℂ)) :
    (α = (1 + Complex.I * (Real.sqrt d : ℂ)) / 2 ∧ 1 - α = (1 - Complex.I * (Real.sqrt d : ℂ)) / 2) ∨
    (1 - α = (1 + Complex.I * (Real.sqrt d : ℂ)) / 2 ∧ α = (1 - Complex.I * (Real.sqrt d : ℂ)) / 2) := by
  have h1 : (2 * α - 1) ^ 2 = (Complex.I * (Real.sqrt d : ℂ)) ^ 2 := by
    rw [h, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with e | e
  · exact .inl ⟨by linear_combination e / 2, by linear_combination -e / 2⟩
  · exact .inr ⟨by linear_combination -e / 2, by linear_combination e / 2⟩

theorem isHalfPt_baseLat : IsHalfPt H.d (baseLat H) ((Ideal.absNorm H.ccK : ℕ) / 2) := by
  have hN : Odd (Ideal.absNorm H.ccK) := Nat.coprime_two_right.1 (H.ccK_coprime 2 (by simp))
  have hint : ∀ w ∈ baseLat H, IsIntegral ℤ w := fun w hw => by
    obtain ⟨c, -, rfl⟩ := (mem_baseLat H w).1 hw
    have h0 : IsIntegral ℤ (c : H.K) := c.2
    exact h0.map (H.φ₀.comp (algebraMap H.K H.E)).toIntAlgHom
  refine ⟨?_, fun h => ?_, fun h => ?_⟩
  · refine (mem_baseLat H _).2 ⟨((Ideal.absNorm H.ccK : ℕ) : 𝓞 H.K), Ideal.absNorm_mem _, ?_⟩
    simp
    ring
  · refine GlobalTheory.TwoTorsionPt.not_integral_half hN (hint _ h) ?_
    simp only [map_mul, map_div₀, map_add, map_one, Complex.conj_I, Complex.conj_ofReal,
      map_natCast, map_ofNat]
    ring
  · refine GlobalTheory.TwoTorsionPt.not_integral_half hN (hint _ h) ?_
    simp only [map_mul, map_div₀, map_sub, map_one, Complex.conj_I, Complex.conj_ofReal,
      map_natCast, map_ofNat]
    ring

theorem cm_of_isConjLat {LL : Type} [Field LL] [NumberField LL] {emb s : LL →+* ℂ} {Λ : AddSubgroup ℂ}
    (h : IsConjLat emb s (baseLat H) Λ) :
    (∀ z ∈ Λ, ((1 + Complex.I * (Real.sqrt H.d : ℂ)) / 2) * z ∈ Λ) ∧ ∃ t, IsHalfPt H.d Λ t := by
  obtain ⟨L, hL⟩ := exists_periodPair_baseLat H
  obtain ⟨⟨L', hL'⟩, -⟩ := Model.area_pos_of_isConjLat h
  obtain ⟨-, a, ha, ha'⟩ := h
  haveI : Countable LL := Countable.of_equiv _ (Module.finBasis ℚ LL).equivFun.toEquiv.symm
  obtain ⟨σ, hσ⟩ := GlobalTheory.GaloisDescent.exists_complex_ringEquiv_comp_eq emb s
  obtain ⟨c, hc⟩ := exists_int_root H
  set α := H.φ₀ (((c : H.K) : H.E)) with hα
  have hst : ∀ l ∈ L.lattice, α * l ∈ L.lattice := fun l hl => by
    obtain ⟨e, he, rfl⟩ := (mem_baseLat H l).1 ((hL l).2 hl)
    exact (hL _).1 ((mem_baseLat H _).2 ⟨c * e, H.ccK.mul_mem_left c he, by simp [hα]⟩)
  obtain ⟨p2, pa, pb⟩ := isHalfPt_baseLat H
  rw [hL] at p2 pa pb
  have hj : σ (1728 * L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) =
      1728 * L'.g₂ ^ 3 / (L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2) := by
    unfold jLat TaylorLogMetric.discr at ha ha'
    rw [GlobalTheory.LatticeInvariants.g2_eq hL, GlobalTheory.LatticeInvariants.lattice_invariant_g3_eq hL] at ha
    rw [GlobalTheory.LatticeInvariants.g2_eq hL', GlobalTheory.LatticeInvariants.lattice_invariant_g3_eq hL'] at ha'
    rw [← ha, ← ha', hσ]
  obtain ⟨q, t, q2, qa, qb⟩ := transfer σ hj hst p2
    (by rcases root_cases hc with e | e
        · rw [e.1]; exact pa
        · rw [e.2]; exact pb)
    (by rcases root_cases hc with e | e
        · rw [e.2]; exact pb
        · rw [e.1]; exact pa)
  have hc' : (2 * σ α - 1) ^ 2 = -(H.d : ℂ) := by
    simpa [map_ofNat] using congrArg σ hc
  unfold IsHalfPt
  simp only [hL']
  rcases root_cases hc' with e | e
  · exact ⟨e.1 ▸ q, t, q2, e.1 ▸ qa, e.2 ▸ qb⟩
  · refine ⟨fun z hz => ?_, t, q2, e.1 ▸ qb, e.2 ▸ qa⟩
    rw [← e.1, sub_mul, one_mul]
    exact sub_mem hz (q z hz)

end GlobalTheory.Mem.Per.ConjCM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSetPosFinite
section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.VolUnique

theorem haar_eq_of_eq_on_set {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ μ' : Measure G) [μ.IsHaarMeasure] [μ'.IsHaarMeasure] (S : Set G) (h : μ S = μ' S)
    (h0 : μ' S ≠ 0) (ht : μ' S ≠ ⊤) : μ = μ' := by
  have hμ := Measure.isMulLeftInvariant_eq_smul μ μ'
  have hc : ((Measure.haarScalarFactor μ μ' : NNReal) : ENNReal) = 1 := by
    have h1 : μ S = (Measure.haarScalarFactor μ μ' : ENNReal) * μ' S := by
      conv_lhs => rw [hμ]
      simp
    rw [h] at h1
    exact ((ENNReal.mul_left_inj h0 ht).1 (by rw [one_mul]; exact h1)).symm
  have hc' : Measure.haarScalarFactor μ μ' = 1 := by exact_mod_cast hc
  rw [hμ, hc', one_smul]

theorem exists_set_pos_finite (cd : CDHaar) (P Q : ℕ) :
    ∃ B : Set (UpqT P Q), MeasurableSet B ∧ cd.cd P Q B ≠ 0 ∧ cd.cd P Q B ≠ ⊤ := by
  obtain ⟨_, _, _, _, _, _⟩ := GlobalTheory.UpqTopology.upq_lcsc P Q
  haveI := cd.haar P Q
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : UpqT P Q)
  exact ⟨K, hK.measurableSet, (Measure.measure_pos_of_mem_nhds _ hK1).ne', hK.measure_lt_top.ne⟩

theorem volMeas_unique : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (I : Type) [Fintype I] (τ : I → (E →+* ℂ)) (cd : CDHaar) (W : HSpace E), IsCMFam τ → W.SigOK → ∀ μ μ', IsVolMeasF cm τ cd W (fun ρ => (W.sig (τ ρ)).1) (fun ρ => (W.sig (τ ρ)).2) μ → IsVolMeasF cm τ cd W (fun ρ => (W.sig (τ ρ)).1) (fun ρ => (W.sig (τ ρ)).2) μ' → μ = μ' := by
  intro F E _ _ _ _ _ _ cm I _ τ cd W _ _ μ μ' hμ hμ'
  obtain ⟨hH, ⟨θ, hθ⟩, hall⟩ := hμ
  obtain ⟨hH', -, hall'⟩ := hμ'
  obtain ⟨⟨A, hA⟩, hB⟩ := hall θ hθ
  have hB' := (hall' θ hθ).2 A hA
  have hB := hB A hA
  choose B hBm hB0 hBt using fun ρ : I => exists_set_pos_finite cd (W.sig (τ ρ)).1 (W.sig (τ ρ)).2
  obtain ⟨_, _, _⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary F E cm.sig W.rank W.gram
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : IsTopologicalGroup (HA (AF F) cm.sig W.gram) :=
    inferInstanceAs (IsTopologicalGroup (HR (AF F) cm.sig W.gram))
  haveI : BorelSpace (HA (AF F) cm.sig W.gram) := ⟨rfl⟩
  refine haar_eq_of_eq_on_set μ μ' _ ((hB B hBm).trans (hB' B hBm).symm) ?_ ?_
  · rw [hB' B hBm]
    exact Finset.prod_ne_zero_iff.2 fun ρ _ => hB0 ρ
  · rw [hB' B hBm]
    exact ENNReal.prod_ne_top fun ρ _ => hBt ρ

end GlobalTheory.Mem.VolUnique
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSmulMemLatticeOfMemCompletion
section
open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

namespace GlobalTheory.LatticeDescent

theorem exists_rational_solution {F K V : Type} [Field F] [Field K] [Algebra F K]
    [TopologicalSpace K] [IsTopologicalRing K] (hd : DenseRange (algebraMap F K))
    [AddCommGroup V] [Module F V] {k : ℕ} (s : Fin k → V) (z : V) (a : Fin k → K)
    (U : Set K) (hU : IsOpen U) (ha : ∀ j, a j ∈ U)
    (h : ∀ l : V →ₗ[F] F, algebraMap F K (l z) = ∑ j, algebraMap F K (l (s j)) * a j) :
    ∃ c : Fin k → F, (∀ j, algebraMap F K (c j) ∈ U) ∧ ∑ j, c j • s j = z := by
  classical
  let S : (Fin k → F) →ₗ[F] V := Fintype.linearCombination F s
  have hS : ∀ c, S c = ∑ j, c j • s j := fun c => Fintype.linearCombination_apply F s c
  have hs : ∀ j, s j ∈ LinearMap.range S := fun j => ⟨Pi.single j 1, by
    simp [S]⟩
  have hz : z ∈ LinearMap.range S := by
    by_contra hz
    obtain ⟨f, hf, hm⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hz inferInstance
    have h0 : ∀ j, f (s j) = 0 := fun j => by
      have : f (s j) ∈ Submodule.map f (LinearMap.range S) := Submodule.mem_map_of_mem (hs j)
      rwa [hm] at this
    have := h f
    simp only [h0, map_zero, zero_mul, Finset.sum_const_zero] at this
    exact hf ((algebraMap F K).injective (by rw [this, map_zero]))
  obtain ⟨T0, hT0⟩ := S.rangeRestrict.exists_rightInverse_of_surjective S.range_rangeRestrict
  obtain ⟨T, hT⟩ := LinearMap.exists_extend T0
  have hST : ∀ y ∈ LinearMap.range S, S (T y) = y := fun y hy => by
    have e1 : T y = T0 ⟨y, hy⟩ := LinearMap.congr_fun hT ⟨y, hy⟩
    have e2 := congrArg Subtype.val (LinearMap.congr_fun hT0 ⟨y, hy⟩)
    rw [e1]
    exact e2
  let φ : (Fin k → K) → (Fin k → K) := fun x i =>
    x i - ∑ j, algebraMap F K (T (s j) i) * x j + algebraMap F K (T z i)
  have hφ : Continuous φ := by
    refine continuous_pi fun i => ?_
    simp only [φ]
    fun_prop
  have hφa : φ a = a := by
    funext i
    have := h ((LinearMap.proj i).comp T)
    simp only [LinearMap.comp_apply, LinearMap.proj_apply] at this
    simp only [φ, this]
    ring
  have hopen : IsOpen (φ ⁻¹' Set.pi Set.univ fun _ => U) :=
    (isOpen_set_pi Set.finite_univ fun _ _ => hU).preimage hφ
  obtain ⟨b, hb⟩ := (DenseRange.piMap (fun _ : Fin k => hd)).exists_mem_open hopen
    ⟨a, by rw [Set.mem_preimage, hφa]; exact fun j _ => ha j⟩
  refine ⟨b - T (S b) + T z, fun i => ?_, ?_⟩
  · have := hb i trivial
    convert this using 1
    simp only [φ, Pi.map_apply, hS, map_sum, map_smul, Pi.add_apply, Pi.sub_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_add, map_sub, map_mul, mul_comm]
  · rw [← hS, map_add, map_sub, hST _ ⟨b, rfl⟩, hST _ hz, sub_self, zero_add]

theorem functional_of_tmul {F E K : Type} [Field F] [Field E] [Field K] [Algebra F E] [Algebra F K]
    {n k : ℕ} (s : Fin k → Fin n → E) (z : Fin n → E) (a : Fin k → K)
    (h : ∀ i, z i ⊗ₜ[F] (1 : K) = ∑ j, s j i ⊗ₜ[F] a j) (l : (Fin n → E) →ₗ[F] F) :
    algebraMap F K (l z) = ∑ j, algebraMap F K (l (s j)) * a j := by
  classical
  have hl : ∀ y : Fin n → E, l y = ∑ i, l (Pi.single i (y i)) := fun y => by
    rw [← map_sum, Finset.univ_sum_single]
  have hi : ∀ i, l (Pi.single i (z i)) • (1 : K) = ∑ j, l (Pi.single i (s j i)) • a j := fun i => by
    have := congrArg (fun t => TensorProduct.lid F K
      (LinearMap.rTensor K (l.comp (LinearMap.single F (fun _ : Fin n => E) i)) t)) (h i)
    simpa only [map_sum, LinearMap.rTensor_tmul, TensorProduct.lid_tmul, LinearMap.comp_apply,
      LinearMap.single_apply] using this
  rw [hl z, Algebra.algebraMap_eq_smul_one, Finset.sum_smul]
  simp only [hi]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_smul, ← hl, Algebra.smul_def]

theorem exists_smul_mem_of_mem_latS : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (M : Submodule (𝓞 E) (Fin n → E)), Submodule.IsLattice E M → ∀ z : Fin n → E, (fun a => inclE (F := F) (v.adicCompletion F) (z a)) ∈ latS (F := F) (v.adicCompletion F) (intV E v) M → ∃ r : 𝓞 F, r ∉ v.asIdeal ∧ algebraMap (𝓞 F) (𝓞 E) r • z ∈ M := by
  intro F E _ _ _ _ _ v n M hM z hz
  classical
  have : Module.Finite (𝓞 E) M := Module.Finite.iff_fg.2 hM.fg
  have : Module.Finite ℤ M := Module.Finite.trans (𝓞 E) M
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := M)
  obtain ⟨a, ha, ea⟩ := (GlobalTheory.LatticeStabLocal.mem_latS_iff_isComb hs _).1 hz
  obtain ⟨c, hc, ec⟩ := exists_rational_solution (HeightOneSpectrum.denseRange_algebraMap F v)
    (fun j => (s j : Fin n → E)) z a (v.adicCompletionIntegers F)
    (Valued.isOpen_valuationSubring _) ha
    (functional_of_tmul (fun j => (s j : Fin n → E)) z a ea)
  have hv : ∀ j, v.valuation F (c j) ≤ 1 := fun j => by
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (c j)]
    exact hc j
  choose m d hmd using fun j => v.exists_primeCompl_mul_eq_of_integer (c j) (hv j)
  refine ⟨∏ j, (d j : 𝓞 F), (prod_mem fun j _ => (d j).2 : _ ∈ v.asIdeal.primeCompl), ?_⟩
  rw [← ec, Finset.smul_sum]
  refine sum_mem fun j _ => ?_
  have e : algebraMap (𝓞 F) (𝓞 E) (∏ j, (d j : 𝓞 F)) • c j • (s j : Fin n → E) =
      algebraMap (𝓞 F) (𝓞 E) ((∏ i ∈ Finset.univ.erase j, (d i : 𝓞 F)) * m j) •
        (s j : Fin n → E) := by
    have key : ∀ (x : 𝓞 F) (y : Fin n → E),
        algebraMap (𝓞 F) (𝓞 E) x • y = algebraMap (𝓞 F) F x • y := fun x y => by
      funext i
      simp only [Pi.smul_apply, Algebra.smul_def]
      rfl
    rw [key, key, smul_smul, map_mul, ← hmd j, ← Finset.prod_erase_mul _ _ (Finset.mem_univ j),
      map_mul]
    congr 1
    ring
  rw [e]
  exact M.smul_mem _ (s j).2

end GlobalTheory.LatticeDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinsumPairsAboveEqAffineHyperplane
section
open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

namespace GlobalTheory.LevelHecke.AboveSum

variable {R V k : Type} [CommRing R] [AddCommGroup V] [Module R V] [Field k]

theorem mem_of_one {res : R →+* k} {q : Pr R V k} (h : q.Ok res) {e : V} (he : q.f e = 1) : e ∈ q.L := by
  by_contra hn
  rw [h.off e hn] at he
  exact zero_ne_one he

theorem smul_mem_ker {res : R →+* k} {q : Pr R V k} {Λ : Submodule R V} (h : q.Ok res) (hk : q.IsKer Λ) {t : R}
    (ht : res t = 0) {e : V} (he : q.f e = 1) : t • e ∈ Λ :=
  (hk _).2 ⟨q.L.smul_mem _ (mem_of_one h he), by rw [h.smul _ _ (mem_of_one h he), ht, zero_mul]⟩

theorem sub_mem_ker {res : R →+* k} {q : Pr R V k} {Λ : Submodule R V} (h : q.Ok res) (hk : q.IsKer Λ)
    {e : V} (he : q.f e = 1) {y : V} (hy : y ∈ q.L) {a : R} (ha : res a = q.f y) : y + (-a) • e ∈ Λ := by
  have he' := mem_of_one h he
  refine (hk _).2 ⟨q.L.add_mem hy (q.L.smul_mem _ he'), ?_⟩
  rw [h.add _ hy _ (q.L.smul_mem _ he'), h.smul _ _ he', he, map_neg, ha]
  ring

theorem le_of_ker {res : R →+* k} (hres : Function.Surjective res) {q q' : Pr R V k} {Λ : Submodule R V}
    (h : q.Ok res) (hk : q.IsKer Λ) (h' : q'.Ok res) (hk' : q'.IsKer Λ) {e e' : V} (he : q.f e = 1)
    (he' : q'.f e' = 1) (hd : e - e' ∈ Λ) {y : V} (hy : y ∈ q.L) : y ∈ q'.L ∧ q'.f y = q.f y := by
  obtain ⟨a, ha⟩ := hres (q.f y)
  have h1 := sub_mem_ker h hk he hy ha
  have h2 := (hk' _).1 (Λ.add_mem h1 (Λ.smul_mem a hd))
  have h3 := mem_of_one h' he'
  have e0 : y = (y + (-a) • e + a • (e - e')) + a • e' := by
    rw [smul_sub, neg_smul]; abel
  have h4 := q'.L.smul_mem a h3
  constructor
  · rw [e0]; exact q'.L.add_mem h2.1 h4
  · have h5 := h'.add _ h2.1 _ h4
    rw [← e0, h2.2, h'.smul _ _ h3, he', ha] at h5
    rw [h5]; ring

theorem eq_of_ker {res : R →+* k} (hres : Function.Surjective res) {q q' : Pr R V k} {Λ : Submodule R V}
    (h : q.Ok res) (hk : q.IsKer Λ) (h' : q'.Ok res) (hk' : q'.IsKer Λ) {e e' : V} (he : q.f e = 1)
    (he' : q'.f e' = 1) (hd : e - e' ∈ Λ) : q = q' := by
  have hd' : e' - e ∈ Λ := by rw [← neg_sub]; exact Λ.neg_mem hd
  ext y
  · exact ⟨fun hy => (le_of_ker hres h hk h' hk' he he' hd hy).1,
      fun hy => (le_of_ker hres h' hk' h hk he' he hd' hy).1⟩
  · by_cases hy : y ∈ q.L
    · exact (le_of_ker hres h hk h' hk' he he' hd hy).2.symm
    · rw [h.off y hy, h'.off y (fun hy' => hy (le_of_ker hres h' hk' h hk he' he hd' hy').1)]

theorem finsum_above : ∀ (R V k W M : Type) [CommRing R] [AddCommGroup V] [Module R V] [Field k] [AddCommGroup W] [Module k W] [AddCommMonoid M] (res : R →+* k) (t : R) (p : Pr R V k) (π : V → W) (φ : Module.Dual k W) (q : W → Pr R V k) (Φ : Pr R V k → M), Function.Surjective res → res t = 0 → (∀ x : V, t • x = 0 → x = 0) → (∀ s x, res s ≠ 0 → s • x ∈ p.L → x ∈ p.L) → Red res t p.L π → (∀ x ∈ p.L, p.f x = φ (π x)) → (∀ w, φ w = 1 → (q w).Ok res ∧ (q w).IsKer p.L ∧ ∃ e, (q w).f e = 1 ∧ π (t • e) = w) → ∑ᶠ q' ∈ {q' | Pr.Inc res t p q'}, Φ q' = ∑ᶠ w ∈ {w | φ w = 1}, Φ (q w) := by
  intro R V k W M _ _ _ _ _ _ _ res t p π φ q Φ hres ht htf hsat hred hf hq
  symm
  refine finsum_mem_eq_of_bijOn q ⟨?_, ?_, ?_⟩ (fun _ _ => rfl)
  · intro w hw
    obtain ⟨h1, h2, e, h3, h4⟩ := hq w hw
    refine ⟨h1, h2, e, h3, ?_⟩
    rw [hf _ (smul_mem_ker h1 h2 ht h3), h4]
    exact hw
  · intro w hw w' hw' hww
    obtain ⟨h1, h2, e, h3, h4⟩ := hq w hw
    obtain ⟨-, -, e', h3', h4'⟩ := hq w' hw'
    rw [← hww] at h3'
    have hd : e + (-1 : R) • e' ∈ p.L :=
      sub_mem_ker h1 h2 h3' (mem_of_one h1 h3) (by rw [map_one, h3])
    have e0 : t • e = t • e' + t • (e + (-1 : R) • e') := by
      rw [neg_smul, one_smul, smul_add, smul_neg]; abel
    rw [← h4, ← h4', e0, hred.add _ (smul_mem_ker h1 h2 ht h3') _ (p.L.smul_mem _ hd), hred.smul _ _ hd, ht,
      zero_smul, add_zero]
  · rintro q' ⟨h1', h2', e', h3', h4'⟩
    have hm' := smul_mem_ker h1' h2' ht h3'
    have hw : φ (π (t • e')) = 1 := by rw [← hf _ hm', h4']
    refine ⟨π (t • e'), hw, ?_⟩
    obtain ⟨h1, h2, e, h3, h4⟩ := hq _ hw
    have hm := smul_mem_ker h1 h2 ht h3
    have h0 : π (t • e + (-1 : R) • t • e') = 0 := by
      rw [hred.add _ hm _ (p.L.smul_mem _ hm'), hred.smul _ _ hm', h4, map_neg, map_one, neg_smul, one_smul,
        add_neg_cancel]
    obtain ⟨y, hy, s, hs, hsy⟩ := (hred.ker _ (p.L.add_mem hm (p.L.smul_mem _ hm'))).1 h0
    have h5 : s • (e - e') - y = 0 := by
      apply htf
      rw [smul_sub, ← hsy, smul_comm t s, neg_smul, one_smul, smul_sub t, sub_eq_add_neg (t • e), sub_self]
    refine eq_of_ker hres h1 h2 h1' h2' h3 h3' (hsat s _ hs ?_)
    rw [sub_eq_zero.1 h5]; exact hy

end GlobalTheory.LevelHecke.AboveSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDerivAtInvDetAndInvAtIdentityStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDerivAt_inv_det_and_inv_at_identity : ∀ (n : ℕ) (M : ℝ → Matrix (Fin n) (Fin n) ℂ) (M' : Matrix (Fin n) (Fin n) ℂ), M 0 = 1 → (∀ i j, HasDerivAt (fun t => M t i j) (M' i j) 0) → HasDerivAt (fun t => ((M t).det)⁻¹) (-M'.trace) 0 ∧ ∀ i j, HasDerivAt (fun t => (M t)⁻¹ i j) (-M' i j) 0 := by
  first | exact @GlobalTheory.Mem.InvDer.hasDerivAt_inv_det_and_inv | exact GlobalTheory.Mem.InvDer.hasDerivAt_inv_det_and_inv | (intros; apply GlobalTheory.Mem.InvDer.hasDerivAt_inv_det_and_inv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasLatticeNormalFormOfBetweenStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasLatticeNormalForm_of_between : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), P ∉ Pr.vGs → ∀ (h ρ : AutY X R j) (e : Fin (cOf R j) → ℤ) (z : Sp X.E (R.N j)), ρ ∈ Loc.R1 X.E (R.N j) (cOf R j) → Between j P h → (ρ * h) '' {v | IntV P v} = GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm.nfLat P (R.N j) (cOf R j) e z → GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm.NF Pr j P (ρ * h) := by
  first | exact @GlobalTheory.Proof.hasLatticeNormalForm_of_between.nf_of_between | exact GlobalTheory.Proof.hasLatticeNormalForm_of_between.nf_of_between | (intros; apply GlobalTheory.Proof.hasLatticeNormalForm_of_between.nf_of_between <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianCodeWordStagesRingOfIntegersFull
section
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open Formalism.L2.Pj

namespace GlobalTheory.Mem

theorem Base.OtoLL_injective' (B : Base) : Function.Injective B.OtoLL := by
  intro x y h
  apply RingOfIntegers.ext
  exact Subtype.ext h

theorem hermitianCodeWordStages_ringOfIntegers_full : ∀ X : Stages, OFull X.toD7 := by
  intro X
  refine ⟨X.B.OtoLL_injective', ?_⟩
  let f : X.B.Ks →+* ℂ := X.B.embLL.comp (algebraMap X.B.Ks X.B.LL)
  have hle : FO X.toD7 ≤ f.toRatAlgHom.fieldRange := by
    rw [FO, IntermediateField.adjoin_le_iff]
    rintro _ ⟨y, rfl⟩
    exact ⟨algebraMap (𝓞 X.B.Ks) X.B.Ks y, rfl⟩
  intro z hz hint
  obtain ⟨x, rfl⟩ := hle hz
  have hx : IsIntegral ℤ x := (isIntegral_algHom_iff f.toIntAlgHom f.injective).1 hint
  exact ⟨(⟨x, hx⟩ : 𝓞 X.B.Ks), rfl⟩

end GlobalTheory.Mem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNormalMvPolynomialOfIsNormalStatement
section
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNormal_mvPolynomial_of_isNormal : ∀ (R : Type) [CommRing R] (r : ℕ), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp R) → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp (MvPolynomial (Fin r) R)) := by
  first | exact @GlobalTheory.isNormalScheme_sp_mvPolynomial | exact GlobalTheory.isNormalScheme_sp_mvPolynomial | (intros; apply GlobalTheory.isNormalScheme_sp_mvPolynomial <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSchemeTheoreticallyDominantComplEffCartierStatement
section
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.ProjBlowup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSchemeTheoreticallyDominant_compl_effCartier : ∀ (W : Scheme.{0}) (I : W.IdealSheafData), FinalTheorems.EffCartier I → IsSchemeTheoreticallyDominant (Scheme.Opens.ι (X := W) I.support.compl) := by
  first | exact @GlobalTheory.ProjBlowup.isSchemeTheoreticallyDominant_compl_of_effCartier | exact GlobalTheory.ProjBlowup.isSchemeTheoreticallyDominant_compl_of_effCartier | (intros; apply GlobalTheory.ProjBlowup.isSchemeTheoreticallyDominant_compl_of_effCartier <;> assumption)
end

