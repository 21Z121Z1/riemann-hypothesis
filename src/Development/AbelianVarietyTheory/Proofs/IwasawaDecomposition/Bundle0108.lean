import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0004
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DuStarPos
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SpreadLe
import Formalism.SharpRestriction.InertJacobiLevels.HostFam
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0087
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.Divisibility.Tuples
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0099
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0101
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0097
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0102
import Formalism.QuotientMetricDivisors.Statement
import Formalism.HermitianLattices.StatementLat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0104
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharpoly
section
noncomputable section
open Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.MemN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
namespace GlobalTheory.MemN.SerInhab

theorem trace_mulLeft {G : Type} [Group G] [Fintype G] (a : MonoidAlgebra ℂ G) :
    LinearMap.trace ℂ _ (LinearMap.mulLeft ℂ a) = (Fintype.card G : ℂ) * a.coeff 1 := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℂ (MonoidAlgebra.basis G ℂ), Matrix.trace]
  have : ∀ x : G, (LinearMap.toMatrix (MonoidAlgebra.basis G ℂ) (MonoidAlgebra.basis G ℂ)
      (LinearMap.mulLeft ℂ a)).diag x = a.coeff 1 := by
    intro x
    simp [Matrix.diag, LinearMap.toMatrix_apply, MonoidAlgebra.basis]
  rw [Finset.sum_congr rfl fun x _ => this x]
  simp

theorem coeff_mem {G : Type} [Group G] [Finite G] {N : ℕ} (hN : 0 < N) (hG : Nat.card G ∣ N)
    (e : MonoidAlgebra ℂ G) (he : e * e = e) (hc : ∀ a, e * a = a * e) (x : G) :
    e.coeff x ∈ IntermediateField.adjoin ℚ {Complex.exp (2 * Real.pi * Complex.I / (N : ℕ))} := by
  classical
  haveI := Fintype.ofFinite G
  set K := IntermediateField.adjoin ℚ {Complex.exp (2 * Real.pi * Complex.I / (N : ℕ))} with hK
  set s : MonoidAlgebra ℂ G := MonoidAlgebra.single x⁻¹ 1 with hs
  have hsN : s ^ N = 1 := by
    rw [hs, MonoidAlgebra.single_pow, one_pow,
      orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_natCard x⁻¹).trans hG)]
    rfl
  have hpow : (e * s) ^ (N + 1) = e * s := by
    rw [Commute.mul_pow (hc s), IsIdempotentElem.pow_succ_eq N he, pow_succ, hsN, one_mul]
  have hζ := Complex.isPrimitiveRoot_exp N hN.ne'
  have hζK : Complex.exp (2 * Real.pi * Complex.I / (N : ℕ)) ∈ K :=
    IntermediateField.mem_adjoin_simple_self _ _
  have htr : LinearMap.trace ℂ _ (LinearMap.mulLeft ℂ (e * s)) ∈ K := by
    rw [Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _)]
    refine multiset_sum_mem _ fun μ hμ => ?_
    have hroot := isRoot_of_mem_roots hμ
    have h1 := (Module.End.hasEigenvalue_iff_isRoot_charpoly _ μ).mpr hroot
    obtain ⟨v, hv⟩ := h1.exists_hasEigenvector
    have h2 := hv.pow_apply (N + 1)
    rw [LinearMap.pow_mulLeft, hpow, hv.apply_eq_smul] at h2
    have h3 : μ = μ ^ (N + 1) := smul_left_injective ℂ hv.2 h2
    by_cases h0 : μ = 0
    · rw [h0]; exact zero_mem _
    · have h4 : μ ^ N = 1 := by
        rw [pow_succ] at h3
        exact mul_right_cancel₀ h0 (by rw [one_mul]; exact h3.symm)
      haveI : NeZero N := ⟨hN.ne'⟩
      obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one h4
      rw [← hi]; exact pow_mem hζK i
  rw [trace_mulLeft] at htr
  have h5 : (e * s).coeff 1 = e.coeff x := by simp [hs]
  rw [h5] at htr
  have h6 : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have := mul_mem (inv_mem (natCast_mem K (Fintype.card G))) htr
  rwa [← mul_assoc, inv_mul_cancel₀ h6, one_mul] at this

theorem exists_primitive (G : Type) [Group G] [Finite G] :
    ∃ (n : ℕ) (p : Fin n → MonoidAlgebra ℂ G), (∀ i, p i * p i = p i) ∧ (∀ i a, p i * a = a * p i) ∧
      (∀ i j, i ≠ j → p i * p j = 0) ∧ (∀ i, p i ≠ 0) ∧ ∑ i, p i = 1 ∧
      ∀ z, (∀ a, z * a = a * z) → z ∈ Submodule.span ℂ (Set.range p) := by
  classical
  have : NeZero (Nat.card G : ℂ) := ⟨by exact_mod_cast Nat.card_pos.ne'⟩
  obtain ⟨n, d, hd, ⟨φ⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ (MonoidAlgebra ℂ G)
  refine ⟨n, fun i => φ.symm (Pi.single i 1), fun i => ?_, fun i a => ?_, fun i j hij => ?_, fun i => ?_, ?_,
    fun z hz => ?_⟩
  · rw [← map_mul, ← Pi.single_mul, one_mul]
  · apply φ.injective
    simp only [map_mul, AlgEquiv.apply_symm_apply]
    funext j
    by_cases h : j = i
    · subst h; simp
    · simp [h]
  · rw [← map_mul, map_eq_zero_iff _ φ.symm.injective]
    funext k
    by_cases h : k = i
    · subst h; simp [hij]
    · simp [h]
  · rw [ne_eq, map_eq_zero_iff _ φ.symm.injective]
    intro h
    haveI := hd i
    have h' := congrFun h i
    rw [Pi.single_eq_same] at h'
    exact one_ne_zero h'
  · rw [← map_sum, Finset.univ_sum_single, ← map_one φ.symm]; rfl
  · have hc : ∀ y, φ z * y = y * φ z := by
      intro y
      obtain ⟨x, rfl⟩ := φ.surjective y
      rw [← map_mul, ← map_mul, hz]
    have h1 : ∀ i, ∃ c : ℂ, φ z i = c • 1 := by
      intro i
      have hci : ∀ M : Matrix (Fin (d i)) (Fin (d i)) ℂ, φ z i * M = M * φ z i := by
        intro M
        have := congrFun (hc (Pi.single i M)) i
        simpa using this
      obtain ⟨c, hcc⟩ := Matrix.mem_range_scalar_of_commute_single (M := φ z i) (fun a b _ => (hci _).symm)
      exact ⟨c, by rw [← hcc, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]⟩
    choose c hc' using h1
    have h2 : z = ∑ i, c i • φ.symm (Pi.single i 1) := by
      apply φ.injective
      simp only [map_sum, map_smul, AlgEquiv.apply_symm_apply]
      funext j
      rw [hc', Finset.sum_apply, Finset.sum_eq_single j]
      · simp
      · intro b _ hb; simp [hb.symm]
      · simp
    rw [h2]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem exists_family {G S : Type} [Group G] [Finite G] (c : G → S) (hc : Function.Surjective c)
    (hconj : ∀ x y, c (x * y) = c (y * x)) [Fintype S] :
    ∃ (q : S → MonoidAlgebra ℂ G), (∀ i, q i * q i = q i) ∧ (∀ i a, q i * a = a * q i) ∧
      (∀ i j, i ≠ j → q i * q j = 0) ∧ (∀ i, q i ≠ 0) ∧ ∑ i, q i = 1 := by
  classical
  obtain ⟨n, p, h1, h2, h3, h4, h5, h6⟩ := exists_primitive G
  let z : S → MonoidAlgebra ℂ G := fun s =>
    .ofCoeff (Finsupp.equivFunOnFinite.symm fun x => if c x = s then 1 else 0)
  have hz : ∀ s x, (z s).coeff x = if c x = s then 1 else 0 := fun s x => rfl
  have hzc : ∀ s a, z s * a = a * z s := by
    intro s a
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => rw [mul_add, add_mul, ha, hb]
    | single x r =>
      ext y
      simp [hz, hconj y, mul_comm]
  have hli : LinearIndependent ℂ z := by
    rw [Fintype.linearIndependent_iff]
    intro a ha s
    obtain ⟨x, rfl⟩ := hc s
    have := congrArg (fun w : MonoidAlgebra ℂ G => w.coeff x) ha
    simpa [hz, Finsupp.finset_sum_apply] using this
  have hcard : Fintype.card S ≤ Fintype.card (Fin n) := by
    have := linearIndependent_le_span_aux' z hli (Set.range p) (by rintro _ ⟨s, rfl⟩; exact h6 _ (hzc s))
    exact this.trans (Fintype.card_range_le p)
  obtain ⟨ι⟩ := Function.Embedding.nonempty_of_card_le hcard
  haveI : Nonempty S := ⟨c 1⟩
  obtain ⟨π, hπ⟩ : ∃ π : Fin n → S, Function.Surjective π :=
    ⟨Function.invFun ι, Function.invFun_surjective ι.injective⟩
  let q : S → MonoidAlgebra ℂ G := fun s => ∑ i ∈ Finset.univ.filter (fun i => π i = s), p i
  have hpq : ∀ i s, p i * q s = if π i = s then p i else 0 := by
    intro i s
    simp only [q, Finset.mul_sum]
    rw [Finset.sum_filter, Finset.sum_eq_single i]
    · rw [h1]
    · intro b _ hb; rw [h3 i b hb.symm]; simp
    · simp
  refine ⟨q, fun s => ?_, fun s a => ?_, fun s t hst => ?_, fun s h => ?_, ?_⟩
  · conv_lhs => enter [1]; simp only [q]
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i hi => by rw [hpq, if_pos (by simpa using hi)]
  · simp only [q, Finset.sum_mul, Finset.mul_sum, h2]
  · conv_lhs => enter [1]; simp only [q]
    rw [Finset.sum_mul]
    refine Finset.sum_eq_zero fun i hi => ?_
    have : π i = s := by simpa using hi
    rw [hpq, if_neg (this ▸ hst)]
  · obtain ⟨i, rfl⟩ := hπ s
    have := hpq i (π i)
    rw [h, mul_zero, if_pos rfl] at this
    exact h4 i this.symm
  · rw [← h5]; exact Finset.sum_fiberwise _ _ _

theorem exists_charpoly {F : Type} [Field F] {r : ℕ} (f : F[X]) (hm : f.Monic) (hd : f.natDegree = r)
    (h0 : f.coeff 0 ≠ 0) : ∃ x : GL (Fin r) F, (x : Matrix (Fin r) (Fin r) F).charpoly = f := by
  subst hd
  let pb := AdjoinRoot.powerBasis' hm
  have h : (Algebra.leftMulMatrix pb.basis pb.gen).charpoly = f := by
    rw [charpoly_leftMulMatrix]
    exact AdjoinRoot.minpoly_powerBasis_gen_of_monic hm
  let M : Matrix (Fin f.natDegree) (Fin f.natDegree) F := Algebra.leftMulMatrix pb.basis pb.gen
  have hM : M.charpoly = f := h
  have hdet : M.det ≠ 0 := by
    rw [Matrix.det_eq_sign_charpoly_coeff, hM]
    exact mul_ne_zero (pow_ne_zero _ (by simp)) h0
  exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M hdet, hM⟩

theorem exists_isSer : ∀ (r g N : ℕ), g.Prime → 0 < N → Nat.card (GL (Fin r) (ZMod g)) ∣ N →
    ∃ e, IsSer r g N e := by
  intro r g N hg hN hG
  classical
  haveI : Fact g.Prime := ⟨hg⟩
  let P : (ZMod g)[X] → Prop := fun f => f.Monic ∧ f.natDegree = r ∧ f.coeff 0 ≠ 0
  let c : GL (Fin r) (ZMod g) → {f // P f} := fun x =>
    ⟨(x : Matrix (Fin r) (Fin r) (ZMod g)).charpoly, Matrix.charpoly_monic _, by simp, by
      intro h
      have h2 := Matrix.det_eq_sign_charpoly_coeff (x : Matrix (Fin r) (Fin r) (ZMod g))
      rw [h, mul_zero] at h2
      exact x.det_ne_zero h2⟩
  have hc : Function.Surjective c := by
    rintro ⟨f, h1, h2, h3⟩
    obtain ⟨x, hx⟩ := exists_charpoly f h1 h2 h3
    exact ⟨x, Subtype.ext hx⟩
  haveI : Finite {f // P f} := Finite.of_surjective c hc
  haveI := Fintype.ofFinite {f // P f}
  obtain ⟨q, h1, h2, h3, h4, h5⟩ := exists_family c hc (fun x y => Subtype.ext (by
    simp only [c, Units.val_mul]; exact Matrix.charpoly_mul_comm _ _))
  let e : (ZMod g)[X] → MonoidAlgebra ℂ (GL (Fin r) (ZMod g)) := fun f => if h : P f then q ⟨f, h⟩ else 0
  have hi : ∀ f, e f * e f = e f := by
    intro f; by_cases h : P f <;> simp [e, h, h1]
  have hce : ∀ f a, e f * a = a * e f := by
    intro f a; by_cases h : P f <;> simp [e, h, h2]
  refine ⟨e, hi, hce, fun f f' hf => ?_, fun f => ?_, ⟨Finset.univ.map (Function.Embedding.subtype P), fun f => ?_, ?_⟩,
    fun f x => coeff_mem hN hG _ (hi f) (hce f) x⟩
  · by_cases h : P f
    · by_cases h' : P f'
      · simp only [e, dif_pos h, dif_pos h']
        exact h3 _ _ (fun hh => hf (congrArg Subtype.val hh))
      · simp [e, h']
    · simp [e, h]
  · change e f = 0 ↔ ¬ P f
    by_cases h : P f <;> simp [e, h, h4]
  · change _ ↔ P f
    simp
  · rw [Finset.sum_map, ← h5]
    exact Finset.sum_congr rfl fun s _ => by simp [e, s.2]

end GlobalTheory.MemN.SerInhab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelCharactersLarge
section
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct

namespace GlobalTheory.Mem.LevelPrime

theorem window_low {x T : ℝ} (hx : 0 < x) (hT : 0 ≤ T) :
    (4 * T ^ x / ((1 : ℕ) : ℝ)) ^ ((1 : ℝ) / x) * (2 : ℝ) ^ (-(2 : ℝ) / x) = T := by
  have h4 : (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) := by norm_num
  rw [Nat.cast_one, div_one, Real.mul_rpow (by norm_num) (Real.rpow_nonneg hT _), ← Real.rpow_mul hT,
    mul_one_div_cancel hx.ne', Real.rpow_one, h4, ← Real.rpow_mul (by norm_num), mul_right_comm,
    ← Real.rpow_add (by norm_num)]
  have h0 : (2 : ℝ) * (1 / x) + -2 / x = 0 := by ring
  rw [h0, Real.rpow_zero, one_mul]

theorem exists_levCh_gt : ∀ (P : PreCh) (N : ℕ), ∃ L : LevCh P, ∀ u, N < L.T u := by
  intro P N
  have hq8 : P.H.q % 8 = 3 := P.H.hyp.2.2.1
  have hd16 : P.H.d % 16 = 7 := P.H.hyp.2.2.2.1
  have hn : 0 < P.R.n := Nat.pos_of_ne_zero (by unfold Ranks.n; positivity)
  have hq : 0 < P.H.q := by omega
  have hd : 0 < P.H.d := by omega
  have hQ : 0 < P.H.QS := P.H.QS_pos
  have hg0 : 0 < P.H.g 0 := (P.level_cond _ (P.H.g_level 0)).1.pos
  have hg1 : 0 < P.H.g 1 := (P.level_cond _ (P.H.g_level 1)).1.pos
  have hc : 1 < P.H.QS * P.H.q * P.H.d := by
    have h1 : 0 < P.H.QS * P.H.q := Nat.mul_pos hQ hq
    have h2 : P.H.d ≤ P.H.QS * P.H.q * P.H.d := Nat.le_mul_of_pos_left _ h1
    omega
  have hM : P.H.QS * P.H.q * P.H.d * (P.H.g 0 * P.H.g 1) ^ 2 ≠ 0 := by positivity
  obtain ⟨π, p, hp, hN, hK, hnorm, hcong, hmod⟩ := exists_norm_prime P.R P.H _ 1
    (N + P.H.pde + P.H.pde') hM (Nat.coprime_one_left _)
  have hmod' : p % (P.H.QS * P.H.q * P.H.d) = 1 := by
    have h := hmod.of_mul_right _
    rw [one_pow] at h
    exact Eq.trans h (Nat.mod_eq_of_lt hc)
  have hx : (0 : ℝ) < (P.R.f : ℝ) * P.R.k := by
    have hf : 0 < P.R.f := by unfold Ranks.f; omega
    have hk : 0 < P.R.k := by have := P.R.m_add_three_le_k; omega
    positivity
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  refine ⟨{ T := fun _ => p
            T_prime := fun _ => hp
            T_cond := fun _ => hmod'
            piT := fun _ => π
            piT_K := fun _ => hK
            piT_norm := fun _ => hnorm
            piT_cong := fun _ => by simpa only [Nat.cast_one] using hcong
            T_ne_pde := fun _ => ⟨by omega, by omega⟩
            duStar := fun _ => 1
            duStar_pos := fun _ => one_pos
            Dstar := 4 * (p : ℝ) ^ ((P.R.f : ℝ) * P.R.k)
            Dstar_pos := by positivity
            GamP := 2
            one_lt_gammaP := by norm_num
            T_win := fun _ => ?_ }, fun _ => by show N < p; omega⟩
  rw [window_low hx hp0.le]
  refine ⟨le_rfl, ?_⟩
  have h1 : (0 : ℝ) ≤ 1 / ((P.R.f : ℝ) * P.R.k) := by positivity
  nlinarith

end GlobalTheory.Mem.LevelPrime
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsProdInfMulFinPart
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.Chr.Determ

variable {L : Type} [Field L] [NumberField L]

theorem continuous_finSingle (v : HeightOneSpectrum (𝓞 L)) : Continuous (finiteSingle L v) := by
  classical
  have hle : (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 L))) ≤ Filter.principal ({v}ᶜ : Set _) := by
    rw [Filter.le_principal_iff]
    exact (Set.finite_singleton v).compl_mem_cofinite
  let f : v.adicCompletion L → RestrictedProduct (fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L)
      (fun w => (w.adicCompletionIntegers L : Set (w.adicCompletion L))) (Filter.principal ({v}ᶜ : Set _)) :=
    fun x => ⟨Pi.mulSingle v x, by
      rw [Filter.eventually_principal]
      intro w hw
      have h' : w ≠ v := hw
      rw [Pi.mulSingle_eq_of_ne h']
      exact one_mem _⟩
  have hf : Continuous f := by
    rw [RestrictedProduct.continuous_rng_of_principal]
    exact continuous_mulSingle (A := fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L) v
  have := (RestrictedProduct.continuous_inclusion hle).comp hf
  exact this

theorem continuous_localIdele (v : HeightOneSpectrum (𝓞 L)) : Continuous (localIdele L v) := by
  apply Continuous.units_map
  exact Continuous.prodMk continuous_const (continuous_finSingle v)

theorem denseRange_atFin (v : HeightOneSpectrum (𝓞 L)) : DenseRange (atFin v) := by
  have hg : Topology.IsOpenEmbedding (Units.val : (v.adicCompletion L)ˣ → v.adicCompletion L) := by
    refine ⟨Units.isEmbedding_val₀, ?_⟩
    have : Set.range (Units.val : (v.adicCompletion L)ˣ → v.adicCompletion L) = {0}ᶜ := by
      ext z
      constructor
      · rintro ⟨u, rfl⟩
        exact u.ne_zero
      · intro hz
        exact ⟨Units.mk0 z hz, rfl⟩
    rw [this]
    exact isOpen_compl_singleton
  rw [DenseRange, dense_iff_inter_open]
  rintro U hU ⟨u, hu⟩
  obtain ⟨k, x, hx, hk⟩ := (HeightOneSpectrum.denseRange_algebraMap L v).exists_mem_open (hg.isOpenMap U hU) ⟨_, u, hu, rfl⟩
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [map_zero] at hk
    exact x.ne_zero hk
  exact ⟨x, hx, Units.mk0 k hk0, Units.ext hk.symm⟩

theorem exists_prod_inf_mul_finPart (a : Ideles L) :
    ∃ y : ∀ w : InfinitePlace L, (w.Completion)ˣ, (∏ w, infIdele L w (y w)) * finPartI L a = a := by
  classical
  let p : ∀ w : InfinitePlace L, AdeleRing (𝓞 L) L →* w.Completion := fun w =>
    { toFun := fun x => x.1 w, map_one' := rfl, map_mul' := fun _ _ => rfl }
  refine ⟨fun w => Units.map (p w) a, ?_⟩
  have h : ((∏ w, infIdele L w (Units.map (p w) a) : Ideles L) : AdeleRing (𝓞 L) L) = ((a : AdeleRing (𝓞 L) L).1, 1) := by
    rw [Units.coe_prod]
    let ι : (∀ w : InfinitePlace L, w.Completion) →* AdeleRing (𝓞 L) L :=
      MonoidHom.inl (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)
    change ∏ w : InfinitePlace L, ι (Pi.mulSingle w ((a : AdeleRing (𝓞 L) L).1 w)) = ι (fun w => (a : AdeleRing (𝓞 L) L).1 w)
    rw [← map_prod]
    exact congrArg ι (Finset.univ_prod_mulSingle (fun w : InfinitePlace L => ((a : AdeleRing (𝓞 L) L).1 w : w.Completion)))
  apply Units.ext
  rw [Units.val_mul, h]
  exact Prod.ext (mul_one _) (one_mul _)

theorem loc_eq_one {ψ : Ideles L →* ℂˣ} (hψ : Continuous ψ) (v : HeightOneSpectrum (𝓞 L))
    (h : ∀ k, ψ (localIdele L v (atFin v k)) = 1) (x : (v.adicCompletion L)ˣ) : ψ (localIdele L v x) = 1 :=
  congrFun ((denseRange_atFin v).equalizer (g := fun x => ψ (localIdele L v x)) (h := fun _ => 1)
    (hψ.comp (continuous_localIdele v)) continuous_const (funext h)) x

theorem inf_eq_one {ψ : Ideles L →* ℂˣ} (hψ : Continuous ψ) (h : ∀ k, ψ (infDiag k) = 1)
    (y : ∀ w : InfinitePlace L, (w.Completion)ˣ) : ψ (∏ w, infIdele L w (y w)) = 1 := by
  refine congrFun ((GlobalTheory.InfTypeLocal.denseRange_atInf L).equalizer
    (g := fun y : ∀ w : InfinitePlace L, (w.Completion)ˣ => ψ (∏ w, infIdele L w (y w))) (h := fun _ => 1)
    (hψ.comp (continuous_finsetProd _ fun w _ =>
      (GlobalTheory.InfTypeLocal.continuous_infIdele L w).comp (continuous_apply w))) continuous_const (funext fun k => ?_)) y
  have h1 := h k
  unfold infDiag at h1
  rw [MonoidHom.finsetProd_apply] at h1
  exact h1

theorem eq_one_of_components {ψ : Ideles L →* ℂˣ} (hψ : Continuous ψ)
    (hf : ∀ v k, ψ (localIdele L v (atFin v k)) = 1) (hi : ∀ k, ψ (infDiag k) = 1) (a : Ideles L) : ψ a = 1 := by
  obtain ⟨S, n, u, hu, rfl, -⟩ := exists_prod_unif_mul_unitIdl L a
  obtain ⟨y, hy⟩ := exists_prod_inf_mul_finPart u
  have h1 : ψ (finPartI L u) = 1 :=
    GlobalTheory.Mem.LocTriv.eq_one_of_local L ψ hψ _ (finPartI_mem_unitIdl.2 hu) (fun _ => rfl) fun v x _ => loc_eq_one hψ v (hf v) x
  rw [← hy, map_mul, map_mul, h1, inf_eq_one hψ hi, map_prod, mul_one, mul_one]
  exact Finset.prod_eq_one fun v _ => by rw [map_zpow, hf, one_zpow]

end GlobalTheory.Mem.Chr.Determ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteResidueField
section
open Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.MemN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

namespace GlobalTheory.CoefInt

open IsLocalRing Topology

variable {l : ℕ} [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l))
  [FiniteDimensional ℚ_[l] K]

omit [FiniteDimensional ℚ_[l] K] in

theorem dvd_iff_norm_le {a : integralClosure ℤ_[l] K} (ha : a ≠ 0) (x : integralClosure ℤ_[l] K) :
    a ∣ x ↔ ‖((x : K) : PadicAlgCl l)‖ ≤ ‖((a : K) : PadicAlgCl l)‖ := by
  constructor
  · rintro ⟨y, rfl⟩
    have hy := (GlobalTheory.mem_integralClosure_padicInt_iff K y).mp y.2
    push_cast
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) hy
  · intro h
    have h0 : (a : K) ≠ 0 := fun h0 => ha (Subtype.ext h0)
    have h1 : ((a : K) : PadicAlgCl l) ≠ 0 := fun h1 => h0 (Subtype.ext h1)
    have hm : (x : K) / (a : K) ∈ integralClosure ℤ_[l] K := by
      rw [GlobalTheory.mem_integralClosure_padicInt_iff, IntermediateField.coe_div, norm_div]
      exact div_le_one_of_le₀ h (norm_nonneg _)
    exact ⟨⟨_, hm⟩, Subtype.ext (mul_div_cancel₀ _ h0).symm⟩

theorem isAdic_maximalIdeal : IsAdic (maximalIdeal (integralClosure ℤ_[l] K)) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (integralClosure ℤ_[l] K)
  have hind : IsInducing (fun x : integralClosure ℤ_[l] K => ((x : K) : PadicAlgCl l)) :=
    IsInducing.subtypeVal.comp IsInducing.subtypeVal
  have hlt : ‖((π : K) : PadicAlgCl l)‖ < 1 :=
    (GlobalTheory.mem_maximalIdeal_integralClosure_iff K π).1 hπ.not_isUnit
  have hpos : 0 < ‖((π : K) : PadicAlgCl l)‖ :=
    norm_pos_iff.2 fun h => hπ.ne_zero (Subtype.ext (Subtype.ext h))
  have hmem : ∀ (n : ℕ) (x : integralClosure ℤ_[l] K),
      x ∈ maximalIdeal (integralClosure ℤ_[l] K) ^ n ↔
        ‖((x : K) : PadicAlgCl l)‖ ≤ ‖((π : K) : PadicAlgCl l)‖ ^ n := fun n x => by
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
      dvd_iff_norm_le K (pow_ne_zero n hπ.ne_zero)]
    push_cast
    rw [norm_pow]
  have hn : ∀ s : Set (integralClosure ℤ_[l] K), s ∈ 𝓝 (0 : integralClosure ℤ_[l] K) ↔
      ∃ ε > 0, ∀ x : integralClosure ℤ_[l] K, ‖((x : K) : PadicAlgCl l)‖ < ε → x ∈ s := fun s => by
    rw [hind.nhds_eq_comap, ((Metric.nhds_basis_ball).comap _).mem_iff]
    refine exists_congr fun ε => and_congr_right fun _ => ?_
    simp [Set.subset_def]
  rw [isAdic_iff]
  refine ⟨fun n => ?_, fun s hs => ?_⟩
  · refine AddSubgroup.isOpen_of_mem_nhds
      (maximalIdeal (integralClosure ℤ_[l] K) ^ n).toAddSubgroup (g := 0) ?_
    exact (hn _).2 ⟨_, pow_pos hpos n, fun x hx => (hmem n x).2 hx.le⟩
  · obtain ⟨ε, hε, h⟩ := (hn s).1 hs
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hlt
    exact ⟨n, fun x hx => h x (((hmem n x).1 hx).trans_lt hn)⟩

theorem finite_residueField : Finite (ResidueField (integralClosure ℤ_[l] K)) := by
  have := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_faithful ℤ_[l] ℚ_[l] K
  have := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_isLocalHom ℤ_[l] K
  have : Finite (ResidueField ℤ_[l]) := Finite.of_equiv _ (PadicInt.residueField).symm.toEquiv
  exact Module.finite_of_finite (ResidueField ℤ_[l])

theorem integers_laws : ∀ (l : ℕ) [Fact l.Prime] (LL : Loc.FinExt l), ∃ (_ : IsDiscreteValuationRing ↥(Loc.OL LL)), Module.Finite ℤ_[l] ↥(Loc.OL LL) ∧ IsAdic (IsLocalRing.maximalIdeal ↥(Loc.OL LL)) ∧ IsAdicComplete (IsLocalRing.maximalIdeal ↥(Loc.OL LL)) ↥(Loc.OL LL) ∧ Finite (IsLocalRing.ResidueField ↥(Loc.OL LL)) ∧ IsFractionRing ↥(Loc.OL LL) ↥LL.1 := by
  intro l _ LL
  have := LL.2
  exact ⟨GlobalTheory.isDiscreteValuationRing_integralClosure_padicInt l LL.1,
    GlobalTheory.finite_integralClosure_padicInt l LL.1, isAdic_maximalIdeal LL.1,
    GlobalTheory.CompleteFiniteExtension.isAdicComplete_of_finite_local ℤ_[l] (integralClosure ℤ_[l] LL.1),
    finite_residueField LL.1, GlobalTheory.isFractionRing_integralClosure_padicInt l LL.1⟩

end GlobalTheory.CoefInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeIndexNonzeroIffUnderFieldMapStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_index_nonzero_iff_under_field_map : ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] (φ : K →+* K') (d d' : ℕ) (G : Matrix (Fin d') (Fin d) K'),
  Function.Bijective G.mulVec → ∀ (P : HeightOneSpectrum (𝓞 K)) (P' : HeightOneSpectrum (𝓞 K')),
  (∀ (x : 𝓞 K) (x' : 𝓞 K'), φ (x : K) = (x' : K') → (x ∈ P.asIdeal ↔ x' ∈ P'.asIdeal)) →
  ∀ A B : Submodule (𝓞 K) (Fin d → K), A.FG → B.FG →
    (Formalism.HermitianLatticesTheory.lidx P.asIdeal A B ≠ 0 ↔ Formalism.HermitianLatticesTheory.lidx P'.asIdeal
      (Submodule.span (𝓞 K') ((fun x : Fin d → K => Matrix.mulVec G fun k => φ (x k)) '' (A : Set (Fin d → K))))
      (Submodule.span (𝓞 K') ((fun x : Fin d → K => Matrix.mulVec G fun k => φ (x k)) '' (B : Set (Fin d → K)))) ≠ 0) := by
  first | exact @GlobalTheory.LidxBaseChange.lidx_ne_zero_iff | exact GlobalTheory.LidxBaseChange.lidx_ne_zero_iff | (intros; apply GlobalTheory.LidxBaseChange.lidx_ne_zero_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyThetaDeRhamFilZeroConcretePeriodStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_theta_deRhamFil_zero_concretePeriod : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → Nonempty (Formalism.MainNotions.LocalSituation.ThetaL P AI) := by
  first | exact @GlobalTheory.MemLoc.TiedTheta.nonempty_thetaL | exact GlobalTheory.MemLoc.TiedTheta.nonempty_thetaL | (intros; apply GlobalTheory.MemLoc.TiedTheta.nonempty_thetaL <;> assumption)
end

