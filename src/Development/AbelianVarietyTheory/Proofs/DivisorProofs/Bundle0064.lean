import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveOfMapPderivEqAndMapOneNeZero
section
namespace GlobalTheory.FockAlg

open MvPolynomial in

theorem injective_of_pderiv {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type}
    (Φ₀ : MvPolynomial ι ℂ →ₗ[ℂ] V) (d : ι → Module.End ℂ V)
    (hd : ∀ (i : ι) (p : MvPolynomial ι ℂ), Φ₀ (MvPolynomial.pderiv i p) = d i (Φ₀ p))
    (h1 : Φ₀ 1 ≠ 0) : Function.Injective Φ₀ := by
  classical
  have hC : ∀ p : MvPolynomial ι ℂ, Φ₀ p = 0 → (∀ m ∈ p.support, m = 0) → p = 0 := by
    intro p hp hs
    have e : p = (coeff 0 p) • (1 : MvPolynomial ι ℂ) := by
      ext m
      by_cases hm : m = 0
      · subst hm; simp
      · have : coeff m p = 0 := by
          by_contra h
          exact hm (hs m (mem_support_iff.2 h))
        rw [this, coeff_smul, coeff_one, if_neg (Ne.symm hm), smul_zero]
    rw [e, map_smul, smul_eq_zero] at hp
    rcases hp with hp | hp
    · rw [e, hp, zero_smul]
    · exact absurd hp h1
  have key : ∀ n : ℕ, ∀ p : MvPolynomial ι ℂ, (∀ m ∈ p.support, m.degree ≤ n) →
      Φ₀ p = 0 → p = 0 := by
    intro n
    induction n with
    | zero =>
      intro p hs hp
      exact hC p hp (fun m hm => (Finsupp.degree_eq_zero_iff m).1 (Nat.le_zero.1 (hs m hm)))
    | succ n ih =>
      intro p hs hp
      have hz : ∀ i, pderiv i p = 0 := by
        intro i
        apply ih
        · intro m hm
          rw [mem_support_iff, coeff_pderiv] at hm
          have h2 := hs _ (mem_support_iff.2 (left_ne_zero_of_mul hm))
          rw [map_add, Finsupp.degree_single] at h2
          omega
        · rw [hd, hp, map_zero]
      apply hC p hp
      intro m hm
      by_contra hm0
      obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
        by_contra h
        push Not at h
        exact hm0 (Finsupp.ext h)
      have hle : Finsupp.single i 1 ≤ m := by
        rw [Finsupp.single_le_iff]; omega
      have hc := congrArg (coeff (m - Finsupp.single i 1)) (hz i)
      rw [coeff_pderiv, tsub_add_cancel_of_le hle, coeff_zero, mul_eq_zero] at hc
      rcases hc with hc | hc
      · exact (mem_support_iff.1 hm) hc
      · exact (Nat.cast_add_one_ne_zero _) hc
  rw [injective_iff_map_eq_zero]
  intro p hp
  exact key (p.support.sup fun m => m.degree) p
    (fun m hm => Finset.le_sup (f := fun m : ι →₀ ℕ => m.degree) hm) hp

end GlobalTheory.FockAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableSqPowMulIteratedFDerivSchwartz
section
open MeasureTheory Filter Topology Set Module
open scoped ENNReal

namespace GlobalTheory

theorem integrable_sq_pow_mul_iteratedFDeriv_schwartz
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : SchwartzMap E F) (i j : ℕ) :
    Integrable (fun z => (‖z‖ ^ i * ‖iteratedFDeriv ℝ j f z‖) ^ 2) μ := by
  have hint : Integrable (fun z => ‖z‖ ^ i * ‖iteratedFDeriv ℝ j f z‖) μ :=
    SchwartzMap.integrable_pow_mul_iteratedFDeriv μ f i j
  set C := SchwartzMap.seminorm ℝ i j f
  refine (hint.const_mul C).mono' ?_ ?_
  · exact (hint.aestronglyMeasurable.aemeasurable.pow_const 2).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun z => ?_)
    have h0 : 0 ≤ ‖z‖ ^ i * ‖iteratedFDeriv ℝ j f z‖ := by positivity
    have hC : ‖z‖ ^ i * ‖iteratedFDeriv ℝ j f z‖ ≤ C := SchwartzMap.le_seminorm ℝ i j f z
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), sq]
    exact mul_le_mul_of_nonneg_right hC h0

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralBasisChangeDeterminant
section
namespace GlobalTheory

open Matrix

theorem matrix_exists_rightInverse_of_saturated_rows {O : Type} [CommRing O] [IsDomain O]
    [IsPrincipalIdealRing O] {m n : ℕ} (N : Matrix (Fin m) (Fin n) O)
    (hinj : ∀ b, Matrix.vecMul b N = 0 → b = 0)
    (hsat : ∀ (r : O) (x : Fin n → O) (b : Fin m → O), r ≠ 0 → r • x = Matrix.vecMul b N →
      ∃ b', x = Matrix.vecMul b' N) :
    ∃ Q : Matrix (Fin n) (Fin m) O, N * Q = 1 := by
  let g : (Fin m → O) →ₗ[O] (Fin n → O) := Matrix.vecMulLinear N
  have hg : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro b hb
    exact hinj b hb
  haveI : Module.IsTorsionFree O ((Fin n → O) ⧸ LinearMap.range g) := by
    refine Module.IsTorsionFree.of_smul_eq_zero ?_
    intro r x h
    by_cases hr : r = 0
    · exact Or.inl hr
    right
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h
    obtain ⟨b, hb⟩ := h
    obtain ⟨b', hb'⟩ := hsat r x b hr hb.symm
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨b', hb'.symm⟩
  haveI : Module.Free O ((Fin n → O) ⧸ LinearMap.range g) := inferInstance
  have hex : Function.Exact g (LinearMap.range g).mkQ := LinearMap.exact_map_mkQ_range g
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective (LinearMap.range g).mkQ
    (Submodule.range_mkQ _)
  have hs' : ∃ s, (LinearMap.range g).mkQ ∘ₗ s = LinearMap.id := ⟨s, hs⟩
  have hl' : ∃ l, l ∘ₗ g = LinearMap.id :=
    ((hex.split_tfae hg (Submodule.mkQ_surjective _)).out 0 1).mp hs'
  obtain ⟨l, hl⟩ := hl'
  refine ⟨LinearMap.toMatrixRight' l, ?_⟩
  ext i j
  have h1 : ∀ x, Matrix.vecMul x (LinearMap.toMatrixRight' l) = l x := by
    intro x
    have := LinearMap.toMatrixRight'.symm_apply_apply l
    conv_rhs => rw [← this]
    rfl
  have h2 : Matrix.vecMul (Pi.single i 1) (N * LinearMap.toMatrixRight' l) = Pi.single i 1 := by
    rw [← Matrix.vecMul_vecMul, h1]
    exact LinearMap.congr_fun hl _
  have := congrFun h2 j
  rw [Matrix.single_one_vecMul] at this
  simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using this

theorem det_saturated_lattice_baseChange : ∀ (O k V K : Type) [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field k] [Algebra O k] [IsFractionRing O k] [CommRing V] [Field K] [Algebra V K] [IsFractionRing V K] (f : O →+* V) (em : k →+* K), (∀ a, algebraMap V K (f a) = em (algebraMap O k a)) → ∀ (m n : ℕ) (P : Matrix (Fin m) (Fin n) k) (M : Matrix (Fin m) (Fin m) k) (C : Matrix (Fin m) (Fin m) K), (∀ c, Matrix.vecMul c P = 0 → c = 0) → M.det ≠ 0 → (∀ c : Fin m → k, (∃ a : Fin n → O, Matrix.vecMul c P = fun j => algebraMap O k (a j)) ↔ ∃ b : Fin m → O, c = Matrix.vecMul (fun i => algebraMap O k (b i)) M) → (∀ c : Fin m → K, (∃ a : Fin n → V, Matrix.vecMul c (P.map em) = fun j => algebraMap V K (a j)) ↔ ∃ b : Fin m → V, c = Matrix.vecMul (fun i => algebraMap V K (b i)) C) → ∃ u : Vˣ, C.det = algebraMap V K u * em M.det := by
  intro O k V K _ _ _ _ _ _ _ _ _ _ f em hf m n P M C hP hM hO hV
  have iO : Function.Injective (algebraMap O k) := IsFractionRing.injective O k
  have iV : Function.Injective (algebraMap V K) := IsFractionRing.injective V K

  have hN : ∃ N : Matrix (Fin m) (Fin n) O, M * P = N.map (algebraMap O k) := by
    have : ∀ i, ∃ a : Fin n → O, Matrix.vecMul (M i) P = fun j => algebraMap O k (a j) := by
      intro i
      refine (hO _).mpr ⟨Pi.single i 1, ?_⟩
      have : (fun j => algebraMap O k ((Pi.single i 1 : Fin m → O) j)) = Pi.single i 1 := by
        ext j; by_cases h : j = i <;> simp [Pi.single_apply, h]
      rw [this, Matrix.single_one_vecMul]; rfl
    choose a ha using this
    refine ⟨Matrix.of a, ?_⟩
    ext i j
    exact congrFun (ha i) j
  obtain ⟨N, hN⟩ := hN
  have hmap : ∀ b : Fin m → O, Matrix.vecMul (Matrix.vecMul (fun i => algebraMap O k (b i)) M) P
      = fun j => algebraMap O k (Matrix.vecMul b N j) := by
    intro b
    rw [Matrix.vecMul_vecMul, hN]
    ext j
    simp [Matrix.vecMul, dotProduct]
  obtain ⟨Q, hQ⟩ := matrix_exists_rightInverse_of_saturated_rows N (by
      intro b hb
      have h1 := hmap b
      rw [hb] at h1
      have h2 := hP _ (h1.trans (by ext j; simp))
      have h3 := Matrix.eq_zero_of_vecMul_eq_zero hM h2
      ext i
      apply iO
      simpa using congrFun h3 i) (by
      intro r x b hr hx
      have hr' : algebraMap O k r ≠ 0 := fun h => hr (iO (by simpa using h))
      obtain ⟨b', hb'⟩ := (hO ((algebraMap O k r)⁻¹ •
        Matrix.vecMul (fun i => algebraMap O k (b i)) M)).mp ⟨x, by
          rw [Matrix.smul_vecMul, hmap, ← hx]
          ext j
          simp only [Pi.smul_apply, smul_eq_mul, map_mul]
          field_simp⟩
      refine ⟨b', ?_⟩
      have h1 := hmap b'
      rw [← hb', Matrix.smul_vecMul, hmap, ← hx] at h1
      ext j
      apply iO
      rw [← congrFun h1 j]
      simp only [Pi.smul_apply, smul_eq_mul, map_mul]
      field_simp)
  have hcomp : (algebraMap V K).comp f = em.comp (algebraMap O k) := RingHom.ext hf
  set M' := M.map em with hM'
  set P' := P.map em with hP'
  set Q' := (Q.map f).map (algebraMap V K) with hQ'
  have hMP : M' * P' = (N.map f).map (algebraMap V K) := by
    rw [hM', hP', ← Matrix.map_mul, hN]
    ext i j
    simp [hf]
  have h1 : M' * (P' * Q') = 1 := by
    rw [← Matrix.mul_assoc, hMP, hQ', ← Matrix.map_mul, ← Matrix.map_mul, hQ]
    simp
  have h2 : (P' * Q') * M' = 1 := mul_eq_one_comm.mp h1
  have hsingle : ∀ i : Fin m, (fun j => algebraMap V K ((Pi.single i 1 : Fin m → V) j)) = Pi.single i 1 := by
    intro i
    ext j; by_cases h : j = i <;> simp [Pi.single_apply, h]
  have hU : ∃ U : Matrix (Fin m) (Fin m) V, C = U.map (algebraMap V K) * M' := by
    have : ∀ i, ∃ a : Fin n → V, Matrix.vecMul (C i) P' = fun j => algebraMap V K (a j) := by
      intro i
      refine (hV _).mpr ⟨Pi.single i 1, ?_⟩
      rw [hsingle, Matrix.single_one_vecMul]; rfl
    choose a ha using this
    have hA : C * P' = (Matrix.of a).map (algebraMap V K) := by
      ext i j
      exact congrFun (ha i) j
    refine ⟨Matrix.of a * Q.map f, ?_⟩
    rw [Matrix.map_mul, ← hA, ← hQ', Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc P', h2,
      Matrix.mul_one]
  have hU' : ∃ U' : Matrix (Fin m) (Fin m) V, M' = U'.map (algebraMap V K) * C := by
    have : ∀ i, ∃ b : Fin m → V, M' i = Matrix.vecMul (fun i => algebraMap V K (b i)) C := by
      intro i
      refine (hV _).mp ⟨(N.map f) i, ?_⟩
      ext j
      exact congrFun (congrFun hMP i) j
    choose b hb using this
    refine ⟨Matrix.of b, ?_⟩
    ext i j
    exact congrFun (hb i) j
  obtain ⟨U, hU⟩ := hU
  obtain ⟨U', hU'⟩ := hU'
  have hd : M'.det = em M.det := by rw [hM', RingHom.map_det]; rfl
  have hd0 : em M.det ≠ 0 := by simpa using hM
  have e1 : C.det = algebraMap V K U.det * em M.det := by
    rw [hU, Matrix.det_mul, hd, RingHom.map_det (algebraMap V K)]; rfl
  have e2 : em M.det = algebraMap V K U'.det * C.det := by
    have := congrArg Matrix.det hU'
    rw [Matrix.det_mul, hd] at this
    rw [this, RingHom.map_det (algebraMap V K)]; rfl
  have e3 : U.det * U'.det = 1 := by
    apply iV
    rw [map_mul, map_one]
    apply mul_right_cancel₀ hd0
    rw [one_mul]
    conv_rhs => rw [e2, e1]
    ring
  exact ⟨Units.mkOfMulEqOne _ _ e3, e1⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCoefficients
section
namespace GlobalTheory.NonzeroDeterminantIntegrality

open Matrix

theorem exists_det_ne_zero {K I Λ : Type} [Field K] [Fintype Λ] [DecidableEq Λ] (v : I → Λ → K)
    (h : ∀ c : Λ → K, (∀ i, ∑ l, c l * v i l = 0) → c = 0) :
    ∃ f : Λ → I, (Matrix.of fun a l => v (f a) l).det ≠ 0 := by
  have hspan : Submodule.span K (Set.range v) = ⊤ := by
    by_contra hne
    obtain ⟨φ, hφ, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
    have hexp : ∀ x : Λ → K, φ x = ∑ l, φ (Pi.single l 1) * x l := by
      intro x
      conv_lhs => rw [pi_eq_sum_univ' x]
      rw [map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_smul, smul_eq_mul, mul_comm]
    have hc := h (fun l => φ (Pi.single l 1)) (fun i => by
      rw [← hexp]
      exact hle (Submodule.subset_span ⟨i, rfl⟩))
    apply hφ
    refine LinearMap.ext fun x => ?_
    rw [hexp]
    refine Finset.sum_eq_zero fun l _ => ?_
    have := congrFun hc l
    simp only [Pi.zero_apply] at this
    rw [this, zero_mul]
  obtain ⟨κ, a, -, hsp, hli⟩ := exists_linearIndependent' K v
  let b : Module.Basis κ K (Λ → K) := Module.Basis.mk hli (by rw [hsp, hspan])
  let e : Λ ≃ κ := (Pi.basisFun K Λ).indexEquiv b
  refine ⟨fun l => a (e l), ?_⟩
  have hli' : LinearIndependent K (Matrix.of fun x l => v (a (e x)) l).row :=
    hli.comp e e.injective
  have := Matrix.linearIndependent_rows_iff_isUnit.mp hli'
  exact ((Matrix.isUnit_iff_isUnit_det _).mp this).ne_zero

theorem integral_coefficients : ∀ (W : Type) [CommRing W] [IsDomain W] (K₀ K₁ : Type) [Field K₀] [Field K₁]
    (i₀ : W →+* K₀) (i₁ : W →+* K₁), Function.Injective i₀ → (∀ a : W, i₁ a ≠ 0 → IsUnit a) →
    ∀ (I Λ : Type) [Fintype Λ] (u : I → Λ → W),
    (∀ c : Λ → K₁, (∀ i : I, ∑ l : Λ, c l * i₁ (u i l) = 0) → c = 0) →
    ∀ (w : I → W) (z : Λ → K₀), (∀ i : I, i₀ (w i) = ∑ l : Λ, z l * i₀ (u i l)) →
    ∃ z₀ : Λ → W, (∀ l : Λ, i₀ (z₀ l) = z l) ∧ ∀ i : I, w i = ∑ l : Λ, z₀ l * u i l := by
  intro W _ _ K₀ K₁ _ _ i₀ i₁ hinj hunit I Λ _ u hu w z hz
  classical
  obtain ⟨f, hf⟩ := exists_det_ne_zero (fun i l => i₁ (u i l)) hu
  let M : Matrix Λ Λ W := Matrix.of fun a l => u (f a) l
  have hdet : IsUnit M.det := by
    apply hunit
    rw [RingHom.map_det]
    exact hf
  let z₀ : Λ → W := M⁻¹ *ᵥ (fun a => w (f a))
  have hM : M *ᵥ z₀ = fun a => w (f a) := by
    simp only [z₀]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hdet₀ : IsUnit (i₀.mapMatrix M).det := by
    rw [← RingHom.map_det]
    exact hdet.map i₀
  have key : (fun l => i₀ (z₀ l)) = z := by
    apply Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).mpr hdet₀)
    funext a
    have h1 := congrArg i₀ (congrFun hM a)
    rw [hz] at h1
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul] at h1 ⊢
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [h1]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [mul_comm]
    rfl
  refine ⟨z₀, fun l => congrFun key l, fun i => hinj ?_⟩
  rw [hz, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul, ← congrFun key l]

end GlobalTheory.NonzeroDeterminantIntegrality
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFlagLiftOfResidue
section
open Polynomial

namespace GlobalTheory

theorem integral_flag_lift_of_residue : ∀ (O Γ : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Group Γ] (n a t : ℕ) (r : Γ →* GL (Fin n) O) (ρ : Γ →* GL (Fin a) O) (ψ : Fin t → Γ →* Oˣ) (ϖ : O), Irreducible ϖ → a + t = n → (∀ g m, ((r g : Matrix (Fin n) (Fin n) O).charpoly - (ρ g : Matrix (Fin a) (Fin a) O).charpoly * ∏ s, (Polynomial.X - Polynomial.C ((ψ s g : Oˣ) : O))).coeff m ∈ IsLocalRing.maximalIdeal O) → (∀ (k Γ : Type) [Field k] [Group Γ] (n a t : ℕ) (r : Γ →* GL (Fin n) k) (ρ : Γ →* GL (Fin a) k) (ψ : Fin t → Γ →* kˣ), a + t = n → (∀ g, (r g : Matrix (Fin n) (Fin n) k).charpoly = (ρ g : Matrix (Fin a) (Fin a) k).charpoly * ∏ s, (Polynomial.X - Polynomial.C ((ψ s g : kˣ) : k))) → ∃ (R : ℕ) (V : Fin (R + 1) → Submodule k (Fin n → k)) (rs : Fin t → Fin R), V 0 = ⊥ ∧ V (Fin.last R) = ⊤ ∧ Monotone V ∧ (∀ g j x, x ∈ V j → (r g : Matrix (Fin n) (Fin n) k).mulVec x ∈ V j) ∧ Function.Injective rs ∧ ∀ s, ∃ x ∈ V (rs s).succ, x ∉ V (rs s).castSucc ∧ V (rs s).succ = V (rs s).castSucc ⊔ Submodule.span k {x} ∧ ∀ g, (r g : Matrix (Fin n) (Fin n) k).mulVec x - ((ψ s g : kˣ) : k) • x ∈ V (rs s).castSucc) → ∃ (R : ℕ) (M : Fin (R + 1) → Submodule O (Fin n → O)) (rs : Fin t → Fin R), (∀ x, x ∈ M 0 ↔ ∃ y : Fin n → O, x = fun i => ϖ * y i) ∧ M (Fin.last R) = ⊤ ∧ Monotone M ∧ (∀ g j x, x ∈ M j → (r g : Matrix (Fin n) (Fin n) O).mulVec x ∈ M j) ∧ Function.Injective rs ∧ ∀ s, ∃ x ∈ M (rs s).succ, x ∉ M (rs s).castSucc ∧ M (rs s).succ = M (rs s).castSucc ⊔ Submodule.span O {x} ∧ ∀ g, (r g : Matrix (Fin n) (Fin n) O).mulVec x - (fun i => ((ψ s g : Oˣ) : O) * x i) ∈ M (rs s).castSucc := by
  intro O Γ _ _ _ _ n a t r ρ ψ ϖ hϖ hat hcong hfield
  let k := IsLocalRing.ResidueField O
  let f : O →+* k := IsLocalRing.residue O
  let rk : Γ →* GL (Fin n) k := (Matrix.GeneralLinearGroup.map f).comp r
  let ρk : Γ →* GL (Fin a) k := (Matrix.GeneralLinearGroup.map f).comp ρ
  let ψk : Fin t → Γ →* kˣ := fun s => (Units.map f.toMonoidHom).comp (ψ s)
  have hrk : ∀ g, (rk g : Matrix (Fin n) (Fin n) k) = (r g : Matrix (Fin n) (Fin n) O).map f :=
    fun g => Matrix.GeneralLinearGroup.val_map_apply f (r g)
  have hρk : ∀ g, (ρk g : Matrix (Fin a) (Fin a) k) = (ρ g : Matrix (Fin a) (Fin a) O).map f :=
    fun g => Matrix.GeneralLinearGroup.val_map_apply f (ρ g)
  have hψk : ∀ s g, ((ψk s g : kˣ) : k) = f ((ψ s g : Oˣ) : O) := fun s g => rfl
  have hchar : ∀ g, (rk g : Matrix (Fin n) (Fin n) k).charpoly
      = (ρk g : Matrix (Fin a) (Fin a) k).charpoly * ∏ s, (X - C ((ψk s g : kˣ) : k)) := by
    intro g
    rw [hrk, hρk, Matrix.charpoly_map, Matrix.charpoly_map]
    simp_rw [hψk]
    have hp : ∏ s, (X - C (f ((ψ s g : Oˣ) : O)))
        = (∏ s, (X - C ((ψ s g : Oˣ) : O))).map f := by
      simp [Polynomial.map_prod]
    rw [hp, ← Polynomial.map_mul, ← sub_eq_zero, ← Polynomial.map_sub]
    ext m
    rw [coeff_map, coeff_zero]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr (hcong g m)
  obtain ⟨R, V, rs, hV0, hVtop, hVmono, hVstab, hrs, hstep⟩ :=
    hfield k Γ n a t rk ρk ψk hat hchar
  let π : (Fin n → O) →ₗ[O] (Fin n → k) := (Algebra.linearMap O k).compLeft (Fin n)
  have hπ : ∀ x i, π x i = f (x i) := fun x i => rfl
  have hπsurj : ∀ y : Fin n → k, ∃ x, π x = y := by
    intro y
    choose x hx using fun i => IsLocalRing.residue_surjective (y i)
    exact ⟨x, funext hx⟩
  have hπmul : ∀ g x, π ((r g : Matrix (Fin n) (Fin n) O).mulVec x)
      = (rk g : Matrix (Fin n) (Fin n) k).mulVec (π x) := by
    intro g x; funext i; rw [hπ, RingHom.map_mulVec, hrk]; rfl
  let M : Fin (R + 1) → Submodule O (Fin n → O) := fun j => ((V j).restrictScalars O).comap π
  have hM : ∀ j x, x ∈ M j ↔ π x ∈ V j := fun j x => Iff.rfl
  have hMmono : Monotone M := fun i j hij x hx => hVmono hij hx
  have hmax : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  refine ⟨R, M, rs, ?_, ?_, hMmono, ?_, hrs, ?_⟩
  · intro x
    rw [hM, hV0, Submodule.mem_bot]
    constructor
    · intro hx
      have : ∀ i, ∃ y, x i = ϖ * y := by
        intro i
        have h1 : x i ∈ IsLocalRing.maximalIdeal O := by
          rw [← IsLocalRing.residue_eq_zero_iff]; exact congr_fun hx i
        rw [hmax, Ideal.mem_span_singleton] at h1
        obtain ⟨y, hy⟩ := h1
        exact ⟨y, hy⟩
      choose y hy using this
      exact ⟨y, funext hy⟩
    · rintro ⟨y, rfl⟩
      funext i
      show f (ϖ * y i) = 0
      rw [map_mul, (IsLocalRing.residue_eq_zero_iff ϖ).mpr (by rw [hmax]; exact Ideal.mem_span_singleton_self ϖ), zero_mul]
  · ext x
    simp only [hM, hVtop, Submodule.mem_top]
  · intro g j x hx
    rw [hM, hπmul]
    exact hVstab g j _ hx
  · intro s
    obtain ⟨xb, hxb, hxbn, hsup, hchi⟩ := hstep s
    obtain ⟨x, rfl⟩ := hπsurj xb
    refine ⟨x, hxb, hxbn, ?_, ?_⟩
    · apply le_antisymm
      · intro y hy
        rw [hM, hsup, Submodule.mem_sup] at hy
        obtain ⟨v, hv, w, hw, hvw⟩ := hy
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
        obtain ⟨c', rfl⟩ := IsLocalRing.residue_surjective c
        rw [Submodule.mem_sup]
        refine ⟨y - c' • x, ?_, c' • x, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x),
          sub_add_cancel _ _⟩
        rw [hM, map_sub, map_smul, ← hvw]
        convert hv using 1
        funext i
        simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Algebra.smul_def]
        simp [k, f]
      · refine sup_le (hMmono (Fin.castSucc_le_succ _)) ?_
        rw [Submodule.span_le, Set.singleton_subset_iff]
        exact hxb
    · intro g
      rw [hM, map_sub, hπmul]
      convert hchi g using 2
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, hπ, map_mul, hψk]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralHasSumEqIntegralIndicatorHasSum
section
open MeasureTheory

namespace GlobalTheory

theorem integral_hasSum_eq_integral_indicator_hasSum :
    ∀ {X ι : Type} [MeasurableSpace X] [Countable ι] (μ : Measure X) (k : ι → X → ℂ),
      (∀ i, Integrable (k i) μ) → {i | ∫ x, ‖k i x‖ ∂μ ≠ 0}.Finite →
      ∀ (p : Set ι) (K Kp : X → ℂ), (∀ x, HasSum (fun i => k i x) (K x)) →
      (∀ x, HasSum (fun i => p.indicator (fun i => k i x) i) (Kp x)) →
      (∀ i ∉ p, ∫ x, k i x ∂μ = 0) → ∫ x, K x ∂μ = ∫ x, Kp x ∂μ := by
  intro X ι _ _ μ k hk hfin p K Kp hK hKp h0
  classical
  set s := hfin.toFinset with hs
  have hnull : ∀ i ∉ s, k i =ᵐ[μ] 0 := by
    intro i hi
    have hi' : ∫ x, ‖k i x‖ ∂μ = 0 := by
      by_contra h
      exact hi (by simpa [hs] using h)
    have := (integral_eq_zero_iff_of_nonneg (fun x => norm_nonneg (k i x)) (hk i).norm).1 hi'
    filter_upwards [this] with x hx
    simpa using hx
  have hall : ∀ᵐ x ∂μ, ∀ i, i ∉ s → k i x = 0 := by
    rw [ae_all_iff]
    intro i
    by_cases hi : i ∈ s
    · exact Filter.Eventually.of_forall (fun x h => absurd hi h)
    · filter_upwards [hnull i hi] with x hx _
      exact hx
  have hKae : K =ᵐ[μ] fun x => ∑ i ∈ s, k i x := by
    filter_upwards [hall] with x hx
    exact (hK x).unique (hasSum_sum_of_ne_finset_zero (fun i hi => hx i hi))
  have hKpae : Kp =ᵐ[μ] fun x => ∑ i ∈ s, p.indicator (fun i => k i x) i := by
    filter_upwards [hall] with x hx
    refine (hKp x).unique (hasSum_sum_of_ne_finset_zero (fun i hi => ?_))
    by_cases hp : i ∈ p
    · simp [Set.indicator_of_mem hp, hx i hi]
    · simp [Set.indicator_of_notMem hp]
  have hind : ∀ i, (fun x => p.indicator (fun i => k i x) i) =
      if i ∈ p then k i else fun _ => 0 := by
    intro i
    by_cases hp : i ∈ p
    · funext x; simp [Set.indicator_of_mem hp, hp]
    · funext x; simp [Set.indicator_of_notMem hp, hp]
  rw [integral_congr_ae hKae, integral_congr_ae hKpae,
    integral_finset_sum s (fun i _ => hk i),
    integral_finset_sum s (fun i _ => by
      rw [hind i]; split_ifs
      · exact hk i
      · exact integrable_zero _ _ _)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hind i]
  split_ifs with hp
  · rfl
  · simp [h0 i hp]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvDer
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace GlobalTheory.LawDer

variable {R : Type} [CommRing R] {d : ℕ}

def atZero (H : MvPowerSeries (Fin d ⊕ Fin d) R) : MvPowerSeries (Fin d) R :=
  subst (Sum.elim (fun i => (X i : MvPowerSeries (Fin d) R)) fun _ => 0) H

def invDer (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (u : Fin d → R)
    (F : MvPowerSeries (Fin d) R) : MvPowerSeries (Fin d) R :=
  ∑ i, u i • atZero (pderiv R (Sum.inr i) (subst μ F))

end GlobalTheory.LawDer
end
end

