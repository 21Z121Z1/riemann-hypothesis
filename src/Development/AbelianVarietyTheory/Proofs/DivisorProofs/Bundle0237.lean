import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0158
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0182
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0183
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0082
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0144
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0029
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0180
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0184
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0077

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QExpansionsCoeffwiseConjugateRingClosure
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators

namespace GlobalTheory.QFam

variable {g : ℂ ≃+* ℂ} {N : ℕ}

theorem QConj.const (g : ℂ ≃+* ℂ) (N : ℕ) (c : ℂ) : QConj g N (fun _ => c) fun _ => g c := by
  refine ⟨fun n => if n = 0 then c else 0, HasQ.const N c, ?_⟩
  have e : (fun n : ℕ => g (if n = 0 then c else 0)) = fun n => if n = 0 then g c else 0 := by
    funext n
    split_ifs <;> simp
  rw [e]
  exact HasQ.const N (g c)

theorem QConj.add {f f' h h' : ℍ → ℂ} (hf : QConj g N f f') (hh : QConj g N h h') :
    QConj g N (fun τ => f τ + h τ) fun τ => f' τ + h' τ := by
  obtain ⟨a, ha, ha'⟩ := hf
  obtain ⟨b, hb, hb'⟩ := hh
  refine ⟨fun n => a n + b n, ha.add hb, ?_⟩
  simpa only [map_add] using ha'.add hb'

theorem QConj.sub {f f' h h' : ℍ → ℂ} (hf : QConj g N f f') (hh : QConj g N h h') :
    QConj g N (fun τ => f τ - h τ) fun τ => f' τ - h' τ := by
  obtain ⟨a, ha, ha'⟩ := hf
  obtain ⟨b, hb, hb'⟩ := hh
  refine ⟨fun n => a n - b n, ha.sub hb, ?_⟩
  simpa only [map_sub] using ha'.sub hb'

theorem map_conv (g : ℂ ≃+* ℂ) (a b : ℕ → ℂ) (n : ℕ) :
    g (conv a b n) = conv (fun n => g (a n)) (fun n => g (b n)) n := by
  simp only [conv, map_sum, map_mul]

theorem QConj.mul (hN : 0 < N) {f f' h h' : ℍ → ℂ} (hf : QConj g N f f') (hh : QConj g N h h') :
    QConj g N (fun τ => f τ * h τ) fun τ => f' τ * h' τ := by
  obtain ⟨a, ha, ha'⟩ := hf
  obtain ⟨b, hb, hb'⟩ := hh
  refine ⟨conv a b, ha.mul_conv hb, ?_⟩
  have e : (fun n => g (conv a b n)) = conv (fun n => g (a n)) (fun n => g (b n)) :=
    funext (map_conv g a b)
  rw [e]
  exact ha'.mul_conv hb'

theorem QConj.pow (hN : 0 < N) {f f' : ℍ → ℂ} (k : ℕ) (hf : QConj g N f f') :
    QConj g N (fun τ => f τ ^ k) fun τ => f' τ ^ k := by
  induction k with
  | zero =>
    simp only [pow_zero]
    simpa using QConj.const g N 1
  | succ k ih =>
    simp only [pow_succ]
    exact QConj.mul hN ih hf

theorem QConj.sum {κ : Type} (s : Finset κ) {f f' : κ → ℍ → ℂ}
    (h : ∀ k ∈ s, QConj g N (f k) (f' k)) :
    QConj g N (fun τ => ∑ k ∈ s, f k τ) fun τ => ∑ k ∈ s, f' k τ := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp only [Finset.sum_empty]
    simpa using QConj.const g N 0
  · intro j s hj ih h
    simp only [Finset.sum_insert hj]
    exact QConj.add (h j (Finset.mem_insert_self j s))
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

theorem QConj.prod (hN : 0 < N) {κ : Type} (s : Finset κ) {f f' : κ → ℍ → ℂ}
    (h : ∀ k ∈ s, QConj g N (f k) (f' k)) :
    QConj g N (fun τ => ∏ k ∈ s, f k τ) fun τ => ∏ k ∈ s, f' k τ := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp only [Finset.prod_empty]
    simpa using QConj.const g N 1
  · intro j s hj ih h
    simp only [Finset.prod_insert hj]
    exact QConj.mul hN (h j (Finset.mem_insert_self j s))
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

theorem qConj_ring : ∀ (g : ℂ ≃+* ℂ) (N : ℕ), 0 < N → (∀ c : ℂ, QConj g N (fun _ => c) fun _ => g c) ∧ (∀ f f' h h', QConj g N f f' → QConj g N h h' → QConj g N (fun τ => f τ + h τ) fun τ => f' τ + h' τ) ∧ (∀ f f' h h', QConj g N f f' → QConj g N h h' → QConj g N (fun τ => f τ - h τ) fun τ => f' τ - h' τ) ∧ (∀ f f' h h', QConj g N f f' → QConj g N h h' → QConj g N (fun τ => f τ * h τ) fun τ => f' τ * h' τ) ∧ (∀ f f' (k : ℕ), QConj g N f f' → QConj g N (fun τ => f τ ^ k) fun τ => f' τ ^ k) ∧ (∀ (κ : Type) (s : Finset κ) (f f' : κ → ℍ → ℂ), (∀ k ∈ s, QConj g N (f k) (f' k)) → (QConj g N (fun τ => ∑ k ∈ s, f k τ) fun τ => ∑ k ∈ s, f' k τ) ∧ QConj g N (fun τ => ∏ k ∈ s, f k τ) fun τ => ∏ k ∈ s, f' k τ) := by
  intro g N hN
  exact ⟨fun c => QConj.const g N c,
    fun _ _ _ _ hf hh => QConj.add hf hh,
    fun _ _ _ _ hf hh => QConj.sub hf hh,
    fun _ _ _ _ hf hh => QConj.mul hN hf hh,
    fun _ _ k hf => QConj.pow hN k hf,
    fun _ s _ _ h => ⟨QConj.sum s h, QConj.prod hN s h⟩⟩

end GlobalTheory.QFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOneLatticeSpanSingleton
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem finGen_line_span_principal (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O]
    [Algebra O C] (V : Type) [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
    (I : Type) [Finite I] (u : I → V) (hv : v.Integers O) (h1 : Module.finrank C V = 1)
    (hu : ∃ i, u i ≠ 0) :
    ∃ w : V, w ≠ 0 ∧ Submodule.span O (Set.range u) = Submodule.span O {w} := by
  obtain ⟨e, -, he⟩ := finrank_eq_one_iff'.mp h1
  choose c hc using fun i => he (u i)
  obtain ⟨j, hj⟩ := hu
  haveI : Nonempty I := ⟨j⟩
  obtain ⟨i0, hi0⟩ := Finite.exists_max (fun i => v (c i))
  have hcj : c j ≠ 0 := by
    rintro h; apply hj; rw [← hc j, h, zero_smul]
  have hc0 : c i0 ≠ 0 := by
    intro h
    have := hi0 j
    rw [h, map_zero] at this
    exact hcj ((Valuation.zero_iff v).mp (le_antisymm this zero_le'))
  have key : ∀ i, ∃ t : O, u i = t • u i0 := by
    intro i
    have hle : v (c i / c i0) ≤ 1 := by
      rw [map_div₀, div_le_one₀ ((Valuation.pos_iff v).mpr hc0)]
      exact hi0 i
    obtain ⟨t, ht⟩ := hv.exists_of_le_one hle
    refine ⟨t, ?_⟩
    rw [← algebraMap_smul C t (u i0), ht, ← hc i, ← hc i0, smul_smul, div_mul_cancel₀ _ hc0]
  refine ⟨u i0, ?_, ?_⟩
  · rw [← hc i0]; exact smul_ne_zero hc0 (by rintro rfl; apply hj; rw [← hc j, smul_zero])
  · apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      obtain ⟨t, ht⟩ := key i
      rw [ht]; exact Submodule.smul_mem _ t (Submodule.subset_span rfl)
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact Submodule.subset_span ⟨i0, rfl⟩

theorem finGen_line_span_principal_target : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (V : Type) [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V] (I : Type) [Finite I] (u : I → V), v.Integers O → Module.finrank C V = 1 → (∃ i, u i ≠ 0) → ∃ w : V, w ≠ 0 ∧ Submodule.span O (Set.range u) = Submodule.span O {w} :=
  fun C _ v O _ _ V _ _ _ _ I _ u hv h1 hu => finGen_line_span_principal C v O V I u hv h1 hu
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatFiniteAdelesSplitAwayFromPrimePadicStatement
section
open IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ratFiniteAdeles_split_awayFromPrime_padic : ∀ (p : ℕ) [Fact p.Prime], ∃ π : FiniteAdeleRing ℤ ℚ →ₐ[ℚ] ℚ_[p], Continuous π ∧ Function.Bijective (fun a => (GlobalTheory.LKTrip.AfP.restr p a, π a)) := by
  first | (exact @GlobalTheory.AdeleSplitP.finiteAdele_split) | (exact GlobalTheory.AdeleSplitP.finiteAdele_split) | (intros; apply GlobalTheory.AdeleSplitP.finiteAdele_split  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalMatrixEigenspaceImageSpannedRationalStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_matrix_eigenspace_image_spanned_rational : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (n : ℕ) (ι : Type) (A : ι → Matrix (Fin n) (Fin n) K) (lam : ι → K) (e : Matrix (Fin n) (Fin n) K), (∀ y : Fin n → L, (∀ p, ((A p).map (algebraMap K L)).mulVec y = algebraMap K L (lam p) • y) ↔ y ∈ Submodule.span L ((fun x i => algebraMap K L (x i)) '' {x : Fin n → K | ∀ p, (A p).mulVec x = lam p • x})) ∧ ∀ y : Fin n → L, y ∈ LinearMap.range (e.map (algebraMap K L)).mulVecLin ↔ y ∈ Submodule.span L ((fun x i => algebraMap K L (x i)) '' (LinearMap.range e.mulVecLin : Set (Fin n → K))) := by
  first | exact @GlobalTheory.rational_eigen_image_span | exact GlobalTheory.rational_eigen_image_span | (intros; apply GlobalTheory.rational_eigen_image_span <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealIndependentSkewMatricesStatement
section
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_independent_skew_matrices : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r n : ℕ} (G : Matrix (Fin r) (Fin r) E), G.det ≠ 0 → ∀ e : Fin n → Matrix (Fin r) (Fin r) E, (∀ i, (e i)ᵀ * G + G * (e i).map cc = 0) → LinearIndependent (maximalRealSubfield E) e → LinearIndependent E e := by
  first | exact @GlobalTheory.linearIndependent_of_skew_of_real | exact GlobalTheory.linearIndependent_of_skew_of_real | (intros; apply GlobalTheory.linearIndependent_of_skew_of_real <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularLocalDifferentialsBasis
section
open scoped TensorProduct Polynomial
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem linearIndependent_tmul_D_of_regular_system :
    ∀ (k A : Type) [Field k] [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Algebra k A] [Algebra.FormallySmooth k (IsLocalRing.ResidueField A)] (n : ℕ) (t : Fin n → A), Ideal.span (Set.range t) = IsLocalRing.maximalIdeal A → (n : WithBot ℕ∞) = ringKrullDim A → LinearIndependent (IsLocalRing.ResidueField A) (fun a => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (t a)) := by
  intro k A _ _ _ _ _ _ n t hspan hdim
  classical
  have htm : ∀ i, t i ∈ maximalIdeal A := fun i => hspan ▸ Ideal.subset_span ⟨i, rfl⟩
  have hn : n = (maximalIdeal A).spanFinrank := by
    apply le_antisymm
    · have h := ringKrullDim_le_spanFinrank_maximalIdeal A
      rw [← hdim] at h
      exact_mod_cast h
    · rw [← hspan]
      refine (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range t)).trans ?_
      rw [← Set.image_univ]
      refine (Set.ncard_image_le Set.finite_univ).trans ?_
      simp
  have hker : RingHom.ker (algebraMap A (ResidueField A)) = maximalIdeal A := ker_residue
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  choose b hb using fun j => residue_surjective (R := A) (g j)
  have hx : ∑ j, b j * t j ∈ RingHom.ker (algebraMap A (ResidueField A)) := by
    rw [hker]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (htm j)
  have htk : ∀ j, algebraMap A (ResidueField A) (t j) = 0 := fun j => by
    rw [← RingHom.mem_ker, hker]; exact htm j
  have h0 : KaehlerDifferential.kerCotangentToTensor k A (ResidueField A)
      ((RingHom.ker (algebraMap A (ResidueField A))).toCotangent ⟨_, hx⟩) = 0 := by
    rw [KaehlerDifferential.kerCotangentToTensor_toCotangent, map_sum, tmul_sum, ← hg]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Derivation.leibniz, tmul_add, ← smul_tmul, ← smul_tmul, Algebra.smul_def, mul_one,
      Algebra.smul_def, mul_one, htk, zero_tmul, add_zero, smul_tmul', smul_eq_mul, mul_one]
    rw [← hb j]; rfl
  have hinj := kerCotangentToTensor_injective_of_formallySmooth k A (ResidueField A)
    residue_surjective
  have h2 : ∑ j, b j * t j ∈ RingHom.ker (algebraMap A (ResidueField A)) ^ 2 :=
    (Ideal.toCotangent_eq_zero _ _).mp (hinj (h0.trans (map_zero _).symm))
  rw [hker] at h2
  have := coeffs_mem_maximalIdeal_of_sum_mem_sq t hspan hn b h2 i
  rw [← hb i]
  exact (residue_eq_zero_iff _).2 this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularQuotientPrimeElement
section
namespace GlobalTheory

theorem prime_algebraMap_localization_of_isRegularRing_quotient :
    ∀ (A : Type) [CommRing A] [IsDomain A] (P : Ideal A) [P.IsPrime] (x : A), x ≠ 0 → x ∈ P →
      IsRegularRing (A ⧸ Ideal.span {x}) → Prime (algebraMap A (Localization.AtPrime P) x) := by
  intro A _ _ P _ x hx hxP hreg
  set R := Localization.AtPrime P
  set J : Ideal A := Ideal.span {x} with hJdef
  have hJP : RingHom.ker (Ideal.Quotient.mk J) ≤ P := by
    rw [Ideal.mk_ker, hJdef, Ideal.span_le, Set.singleton_subset_iff]; exact hxP
  have hle : J ≤ (J.map (algebraMap A R)).comap (algebraMap A R) := Ideal.le_comap_map
  letI : Algebra (A ⧸ J) (R ⧸ J.map (algebraMap A R)) := (Ideal.quotientMap _ _ hle).toAlgebra
  have hl := IsLocalization.of_surjective P.primeCompl R (S' := R ⧸ J.map (algebraMap A R))
    (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective rfl
    (by rw [Ideal.mk_ker, Ideal.mk_ker])
  have hm : (P.map (Ideal.Quotient.mk J)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hJP
  have e : P.primeCompl.map (Ideal.Quotient.mk J) = (P.map (Ideal.Quotient.mk J)).primeCompl := by
    have hc : (P.map (Ideal.Quotient.mk J)).comap (Ideal.Quotient.mk J) = P := by
      rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, sup_eq_left.2 hJP]
    ext y
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    constructor
    · rintro ⟨z', hz', e⟩ hz
      exact hz' (hc.le (show Ideal.Quotient.mk J z' ∈ _ from e ▸ hz))
    · exact fun hz => ⟨z, fun h => hz (Ideal.mem_map_of_mem _ h), rfl⟩
  rw [e] at hl
  have := IsRegularRing.isRegularLocalRing_localization (P.map (Ideal.Quotient.mk J))
  haveI : IsRegularLocalRing (R ⧸ J.map (algebraMap A R)) :=
    IsRegularLocalRing.of_ringEquiv (IsLocalization.algEquiv (P.map (Ideal.Quotient.mk J)).primeCompl
      (Localization.AtPrime (P.map (Ideal.Quotient.mk J))) _).toRingEquiv
  have hdom : IsDomain (R ⧸ J.map (algebraMap A R)) :=
    (isDomain_and_isIntegrallyClosed_of_isRegularLocalRing _).1
  have hmap : J.map (algebraMap A R) = Ideal.span {algebraMap A R x} := by
    rw [hJdef, Ideal.map_span, Set.image_singleton]
  rw [hmap] at hdom
  have hprime : (Ideal.span {algebraMap A R x}).IsPrime := (Ideal.Quotient.isDomain_iff_prime _).1 hdom
  have hne : algebraMap A R x ≠ 0 := by
    intro h0
    apply hx
    exact IsLocalization.injective R (P.primeCompl_le_nonZeroDivisors) (by simpa using h0)
  exact (Ideal.span_singleton_prime hne).1 hprime

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelLenChainAdd
section
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module

namespace GlobalTheory

theorem relLen_chain_add : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (M : Type)
    [AddCommGroup M] [Module (Int0 v) M] (X'' X' X : Submodule (Int0 v) M) (r₁ r₂ : ℝ),
    RelLen v X'' X' r₂ → RelLen v X' X r₁ → RelLen v X'' X (r₁ + r₂) := by
  intro C _ v M _ _ X'' X' X r₁ r₂ h₂ h₁
  obtain ⟨n, b, b', A, hA, hr₂⟩ := h₂
  obtain ⟨m, c, c', B, hB, hr₁⟩ := h₁
  have hnm : n = m := by simpa using Fintype.card_congr (b.indexEquiv c')
  subst hnm
  have hU : ∀ i, (b i : M) = ∑ j, c'.toMatrix b j i • (c' j : M) := by
    intro i
    have := congrArg X'.subtype (c'.sum_repr (b i))
    simp only [map_sum, map_smul, Submodule.subtype_apply] at this
    simp only [Basis.toMatrix_apply]
    exact this.symm
  have u : IsUnit (c'.toMatrix b).det := by
    let _ := c'.invertibleToMatrix b
    exact Matrix.isUnit_det_of_invertible _
  refine ⟨n, c, b', B * c'.toMatrix b * A, fun k => ?_, ?_⟩
  · rw [hA k]
    simp_rw [hU, hB, Finset.smul_sum, smul_smul]
    simp_rw [Matrix.mul_apply, Finset.sum_mul, Finset.sum_smul]
    refine (Finset.sum_congr rfl fun a _ => Finset.sum_comm).trans ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ =>
      Finset.sum_congr rfl fun b _ => ?_
    congr 1
    ring
  · rw [Matrix.det_mul, Matrix.det_mul, Subring.coe_mul, Subring.coe_mul, v.map_mul, v.map_mul,
      v_unit v u, add_zero, hr₁, hr₂]
    rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentationsEqualTracesConjugateStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.representations_equal_traces_conjugate : ∀ (I : Type) [Fintype I] [DecidableEq I] (m g : ℕ), 0 < m → ∀ (σ σ' : (I → Matrix (Fin m) (Fin m) ℂ) →ₐ[ℂ] Matrix (Fin g) (Fin g) ℂ), (∀ τ, (σ (Pi.single τ 1)).trace = (σ' (Pi.single τ 1)).trace) → ∃ h : Matrix (Fin g) (Fin g) ℂ, IsUnit h ∧ ∀ x, σ' x * h = h * σ x := by
  first | exact @GlobalTheory.conj_of_trace_central_idem_eq | exact GlobalTheory.conj_of_trace_central_idem_eq | (intros; apply GlobalTheory.conj_of_trace_central_idem_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentativeParametricIntegralContinuousFamilyStatement
section
open MeasureTheory
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.representative_parametric_integral_continuous_family : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (ι : K → G → ℂ), (∀ C, IsCompact C → ∃ M : ℝ, ∀ v, IntegrableOn (ι v) C μ ∧ ∫ x in C, ‖ι v x‖ ∂μ ≤ M * ‖v‖) → (∀ (a : ℂ) v w, ι (a • v + w) =ᵐ[μ] fun x => a * ι v x + ι w x) → ∀ (T : Type) [TopologicalSpace T] [SecondCountableTopology T] [T2Space T] [MeasurableSpace T] [BorelSpace T] (ν : Measure T) [IsLocallyFiniteMeasure ν] (Q : Set T) (w : T → K) (φ : T → G → ℂ), IsCompact Q → Continuous w → Continuous (Function.uncurry φ) → (∀ t, ι (w t) =ᵐ[μ] φ t) → (Continuous fun x => ∫ t in Q, φ t x ∂ν) ∧ ι (∫ t in Q, w t ∂ν) =ᵐ[μ] fun x => ∫ t in Q, φ t x ∂ν := by
  first | exact @GlobalTheory.LocRep.rep_parametric_integral | exact GlobalTheory.LocRep.rep_parametric_integral | (intros; apply GlobalTheory.LocRep.rep_parametric_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomFromPadicUniqueOfSep
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem padicInt_ringHom_ext_of_separated (p : ℕ) [Fact p.Prime] (R : Type) [Ring R]
    (hsep : ∀ x : R, (∀ n : ℕ, ∃ y : R, x = (p : R) ^ n * y) → x = 0) :
    ∀ f g : ℤ_[p] →+* R, f = g := by
  intro f g
  ext c
  have key : f c - g c = 0 := by
    apply hsep
    intro n
    have h := PadicInt.appr_spec n c
    rw [Ideal.mem_span_singleton'] at h
    obtain ⟨c', hc'⟩ := h
    refine ⟨f c' - g c', ?_⟩
    have hc : c = (c.appr n : ℤ_[p]) + c' * (p : ℤ_[p]) ^ n := by rw [hc']; ring
    rw [hc, map_add, map_add, map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast,
      map_natCast, map_natCast]
    have hcomm1 : f c' * (p : R) ^ n = (p : R) ^ n * f c' := ((Nat.cast_commute p (f c')).pow_left n).symm
    have hcomm2 : g c' * (p : R) ^ n = (p : R) ^ n * g c' := ((Nat.cast_commute p (g c')).pow_left n).symm
    rw [hcomm1, hcomm2, mul_sub]
    abel
  exact sub_eq_zero.mp key

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomsLinearlyIndependent
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem ringHom_independent_via_algebraMap :
    ∀ (C : Type) [Field C] (O : Type) [CommRing O] [Algebra O C] (Λ : Type) [CommRing Λ],
      Function.Injective (algebraMap O C) → ∀ (S : Finset (Λ →+* O)) (c : (Λ →+* O) → C),
        (∀ a : Λ, ∑ σ ∈ S, c σ * algebraMap O C (σ a) = 0) → ∀ σ ∈ S, c σ = 0 := by
  intro C _ O _ _ Λ _ hinj S c hsum
  classical
  let φ : (Λ →+* O) → (Λ →* C) := fun σ => ((algebraMap O C).comp σ).toMonoidHom
  have hφ : Function.Injective φ := by
    intro σ τ h
    ext a
    apply hinj
    have := congrArg (fun f : Λ →* C => f a) h
    simpa [φ] using this
  have hli := (linearIndependent_monoidHom Λ C).comp φ hφ
  rw [linearIndependent_iff'] at hli
  intro σ hσ
  apply hli S c _ σ hσ
  funext a
  simpa [φ, Finset.sum_apply] using hsum a

end GlobalTheory
end

