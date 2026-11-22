import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0101
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0102
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightInvariantGLOfUpperTriangularRightInvariantStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rightInvariant_GL_of_upperTriangular_rightInvariant : ∀ {k : Type} [Field k] [Infinite k] {m : ℕ} (ψ Φ : Matrix (Fin m) (Fin m) k → k) (r : k → k), (∀ A₀ D : Matrix (Fin m) (Fin m) k, ∃ p : Polynomial k, ∀ x : k, Φ (A₀ + x • D) = p.eval x) → (∀ A : Matrix (Fin m) (Fin m) k, A.det ≠ 0 → ψ A = r A.det * Φ A) → (∀ A T : Matrix (Fin m) (Fin m) k, A.det ≠ 0 → T.det ≠ 0 → T.BlockTriangular id → ψ (A * T) = ψ A) → ∀ A B : Matrix (Fin m) (Fin m) k, A.det ≠ 0 → B.det ≠ 0 → ψ (A * B) = ψ A := by
  first | exact @GlobalTheory.rightInv_of_upperTriangular_rightInv | exact GlobalTheory.rightInv_of_upperTriangular_rightInv | (intros; apply GlobalTheory.rightInv_of_upperTriangular_rightInv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomDualNumberSndEqZeroStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringHom_numberField_dualNumber_snd_eq_zero : ∀ (F : IntermediateField ℚ ℂ) [FiniteDimensional ℚ F] {R : Type} [CommRing R] (φ : F →+* DualNumber R) (a : F), (φ a).snd = 0 := by
  first | exact @GlobalTheory.ringHom_dualNumber_snd_eq_zero | exact GlobalTheory.ringHom_dualNumber_snd_eq_zero | (intros; apply GlobalTheory.ringHom_dualNumber_snd_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomExtendOfIsIntegralIsAlgClosedStatement
section
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ringHom_extend_of_isIntegral_of_isAlgClosed : ∀ (A C K : Type) [CommRing A] [CommRing C] [Algebra A C] [Algebra.IsIntegral A C] [Field K] [IsAlgClosed K] (h : A →+* K), RingHom.ker (algebraMap A C) ≤ RingHom.ker h → ∃ ψ : C →+* K, ψ.comp (algebraMap A C) = h := by
  first | exact @GlobalTheory.ringHom_extend_of_isIntegral_isAlgClosed | exact GlobalTheory.ringHom_extend_of_isIntegral_isAlgClosed | (intros; apply GlobalTheory.ringHom_extend_of_isIntegral_isAlgClosed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomExtendsAlgHomOfSpanOfFinrankEqStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algHom_extend_ringHom_of_span_eq_top_of_finrank_eq : ∀ (O : Type) [Ring O] [Module.Free ℤ O] [Module.Finite ℤ O] (A : Type) [Ring A] [Algebra ℂ A] [FiniteDimensional ℂ A] (B : Type) [Ring B] [Algebra ℂ B] (φ : O →+* A) (ρ : O →+* B), Submodule.span ℂ (Set.range φ) = ⊤ → Module.finrank ℂ A = Module.finrank ℤ O → ∃ σ : A →ₐ[ℂ] B, ∀ x, σ (φ x) = ρ x := by
  first | exact @GlobalTheory.ringHom_extends_algHom_of_span_of_finrank_eq | exact GlobalTheory.ringHom_extends_algHom_of_span_of_finrank_eq | (intros; apply GlobalTheory.ringHom_extends_algHom_of_span_of_finrank_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingKrullDimFiberStalkEqQuotientStatement
section
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringKrullDim_fiber_stalk_eq_quotient : ∀ (B Y : Scheme.{0}) (π : Y ⟶ B) (b : B) (z : π.fiber b), ringKrullDim ((π.fiber b).presheaf.stalk z) = ringKrullDim (Y.presheaf.stalk (π.fiberι b z) ⧸ (IsLocalRing.maximalIdeal (B.presheaf.stalk (π (π.fiberι b z)))).map (π.stalkMap (π.fiberι b z)).hom) := by
  first | exact @GlobalTheory.FibreStalk.ringKrullDim_stalk_fiber | exact GlobalTheory.FibreStalk.ringKrullDim_stalk_fiber | (intros; apply GlobalTheory.FibreStalk.ringKrullDim_stalk_fiber <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingOfIntegersTraceMulLeftNondegenerateStatement
section
open NumberField
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringOfIntegers_eq_zero_of_trace_mulLeft_eq_zero : ∀ (K : Type) [Field K] [NumberField K] (x : 𝓞 K), (∀ y : 𝓞 K, LinearMap.trace ℤ (𝓞 K) (LinearMap.mulLeft ℤ (x * y)) = 0) → x = 0 := by
  first | (exact @GlobalTheory.ringOfIntegers_trace_mulLeft_nondegenerate) | (exact GlobalTheory.ringOfIntegers_trace_mulLeft_nondegenerate) | (intros; apply GlobalTheory.ringOfIntegers_trace_mulLeft_nondegenerate  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalarOfBorelMovesOpenFrames
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD Matrix

namespace GlobalTheory

theorem scalar_of_triangular_moves_open :
  ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (m : GL (Fin r) E) (W : Set (Frame X.Ψ r)), IsOpen W → W.Nonempty → W ⊆ X.dom → (∀ x ∈ W, ∃ b ∈ Bor X.Ψ r, lact m x = rmul x b) → ∃ s : E, (m : Matrix (Fin r) (Fin r) E) = Matrix.scalar (Fin r) s := by
  intro E _ _ _ r X m W hW hne _ hact
  classical
  cases r with
  | zero => exact ⟨0, by ext i; exact i.elim0⟩
  | succ n =>
  obtain ⟨σ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hτ : ∃ τ, τ ∈ X.Ψ := by
    by_cases h : σ ∈ X.Ψ
    · exact ⟨σ, h⟩
    · refine ⟨ComplexEmbedding.conjugate σ, ?_⟩
      by_contra h'
      exact h ((X.cmType σ).2 h')
  obtain ⟨τ0, hτ0⟩ := hτ
  let τ : X.Ψ := ⟨τ0, hτ0⟩
  let M : Matrix (Fin (n+1)) (Fin (n+1)) ℂ := (m : Matrix (Fin (n+1)) (Fin (n+1)) E).map τ0
  have key : ∀ y ∈ W, ∀ i j : Fin (n+1),
      (M *ᵥ (fun k => y τ k 0)) i * y τ j 0 = (M *ᵥ (fun k => y τ k 0)) j * y τ i 0 := by
    intro y hy i j
    obtain ⟨b, hb, he⟩ := hact y hy
    have hcol : ∀ a : Fin (n+1), (M *ᵥ (fun k => y τ k 0)) a = y τ a 0 * b τ 0 0 := by
      intro a
      have := congrFun (congrFun (congrFun he τ) a) 0
      simp only [lact, rmul, mat, Matrix.mul_apply, Matrix.of_apply] at this
      have hs : ∑ k, y τ a k * b τ k 0 = y τ a 0 * b τ 0 0 := by
        rw [Finset.sum_eq_single (0 : Fin (n+1))]
        · intro k _ hk
          rw [(hb τ).2 k 0 (Fin.pos_of_ne_zero hk), mul_zero]
        · simp
      rw [hs] at this
      simp only [Matrix.mulVec, dotProduct]
      exact this
    rw [hcol i, hcol j]; ring
  obtain ⟨x0, hx0⟩ := hne
  have hq : ∀ w : Fin (n+1) → ℂ, ∀ i j : Fin (n+1), (M *ᵥ w) i * w j = (M *ᵥ w) j * w i := by
    intro w i j
    let pert : ℂ → Frame X.Ψ (n+1) := fun t σ a c => x0 σ a c + if σ = τ ∧ c = 0 then t * w a else 0
    have hc : Continuous pert := by
      apply continuous_pi; intro σ; apply continuous_pi; intro a; apply continuous_pi; intro c
      by_cases h : σ = τ ∧ c = 0
      · simp only [pert, h, and_self, if_true]; fun_prop
      · simp only [pert, h, if_false]; fun_prop
    have h0 : pert 0 = x0 := by funext σ a c; simp [pert]
    have hO : IsOpen (pert ⁻¹' W) := hW.preimage hc
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hO 0 (by simp [h0, hx0])
    set t : ℂ := ((ε / 2 : ℝ) : ℂ) with ht_def
    have htn : t ≠ 0 := by
      rw [ht_def]; exact_mod_cast (by positivity : ε / 2 ≠ 0)
    have hnorm : ‖t‖ < ε := by
      rw [ht_def, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]; linarith
    have h1 : pert t ∈ W := hball (by simpa using hnorm)
    have h2 : pert (-t) ∈ W := hball (by simpa using hnorm)
    have hcolp : ∀ s : ℂ, (fun k => pert s τ k 0) = (fun k => x0 τ k 0) + s • w := by
      intro s; funext k; simp [pert]
    have e1 := key _ h1 i j
    have e2 := key _ h2 i j
    have e0 := key _ hx0 i j
    have hpt : ∀ s : ℂ, ∀ k, pert s τ k 0 = x0 τ k 0 + s * w k := by
      intro s k; simp [pert]
    rw [hcolp] at e1 e2
    simp only [hpt, Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e1 e2
    have : t ^ 2 * ((M *ᵥ w) i * w j - (M *ᵥ w) j * w i) = 0 := by
      linear_combination (1/2 : ℂ) * e1 + (1/2 : ℂ) * e2 - e0
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (pow_eq_zero_iff (by norm_num) |>.mp h) htn
    · exact sub_eq_zero.mp h
  have hoff : ∀ i j : Fin (n+1), i ≠ j → M i j = 0 := by
    intro i j hij
    have := hq (Pi.single j 1) i j
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply, hij] using this
  have hsv : ∀ j k : Fin (n+1), (M *ᵥ Pi.single j (1:ℂ)) k = M k j := by
    intro j k; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hdiag : ∀ i j : Fin (n+1), M i i = M j j := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    have := hq (Pi.single i 1 + Pi.single j 1) i j
    have hji : j ≠ i := Ne.symm hij
    rw [Matrix.mulVec_add] at this
    simp only [Pi.add_apply, hsv, Pi.single_apply, hij, hji, if_true, if_false, mul_one, add_zero, zero_add, hoff i j hij, hoff j i hji] at this
    exact this
  refine ⟨(m : Matrix (Fin (n+1)) (Fin (n+1)) E) 0 0, ?_⟩
  ext i j
  rw [Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs with hij
  · subst hij
    apply τ0.injective
    have := hdiag i 0
    simpa [M] using this
  · apply τ0.injective
    have := hoff i j hij
    simpa [M] using this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledKoszulTestFamilyHasDerivAtScale
section
open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A

noncomputable section

namespace GlobalTheory.PsCo.HomotDeriv

theorem ev_rP {n : ℕ} (ε : Fin n → Bool) (g : Mat n) : ev g (rP ε) = ((rM ε g : ℝ) : ℂ) := by
  simp only [rP, rM, map_sum, map_mul, ev, MvPolynomial.eval_X, Sum.elim_inl, Sum.elim_inr]
  push_cast
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

theorem hasDerivAt_scale (G : ℝ → ℝ) (hG : ContDiff ℝ (⊤ : ℕ∞) G) (k : ℕ) (r t : ℝ) (ht : t ≠ 0) :
    HasDerivAt (fun s : ℝ => iteratedDeriv k (fun y => G (s * y)) r)
      (t⁻¹ * (k * iteratedDeriv k (fun y => G (t * y)) r + r * iteratedDeriv (k + 1) (fun y => G (t * y)) r)) t := by
  have hc : ∀ m : ℕ, ContDiff ℝ m G := fun m => hG.of_le (by exact_mod_cast le_top)
  have e : ∀ (m : ℕ) (s : ℝ), iteratedDeriv m (fun y => G (s * y)) r = s ^ m * iteratedDeriv m G (s * r) :=
    fun m s => congrFun (iteratedDeriv_comp_const_mul (hc m) s) r
  simp only [e]
  have hD : HasDerivAt (iteratedDeriv k G) (iteratedDeriv (k + 1) G (t * r)) (t * r) := by
    rw [iteratedDeriv_succ]
    exact ((hc (k + 1)).differentiable_iteratedDeriv k (by exact_mod_cast Nat.lt_succ_self k)).differentiableAt.hasDerivAt
  have h1 : HasDerivAt (fun s : ℝ => s * r) r t := by simpa using (hasDerivAt_id t).mul_const r
  have h2 : HasDerivAt (fun s : ℝ => s ^ k * iteratedDeriv k G (s * r))
      (k * t ^ (k - 1) * iteratedDeriv k G (t * r) + t ^ k * (iteratedDeriv (k + 1) G (t * r) * r)) t :=
    by
    have h3 := (hasDerivAt_pow k t).mul (hD.comp t h1)
    exact h3
  refine h2.congr_deriv ?_
  rcases k with _ | k
  · simp only [Nat.cast_zero, zero_mul, zero_add, pow_zero, pow_one]
    field_simp
  · simp only [Nat.add_sub_cancel]
    push_cast
    field_simp
    ring

theorem sum_shift (N : ℕ) (a e : ℕ → ℂ) (r : ℂ) (he : e (N + 1) = 0) :
    ∑ k ∈ Finset.range (N + 1), ((k : ℂ) * a k + r * a (k + 1)) * e k =
      ∑ k ∈ Finset.range (N + 1), a (k + 1) * (((k : ℂ) + 1) * e (k + 1) + r * e k) := by
  have h1 : ∑ k ∈ Finset.range (N + 1), (k : ℂ) * a k * e k =
      ∑ k ∈ Finset.range (N + 1), a (k + 1) * (((k : ℂ) + 1) * e (k + 1)) := by
    rw [Finset.sum_range_succ', Finset.sum_range_succ (n := N), he]
    simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero]
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast
    ring
  simp only [add_mul (_ * a _), mul_add (a _), Finset.sum_add_distrib, h1]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

theorem sum_prev {n : ℕ} (g : Mat n) (N : ℕ) (a : ℕ → ℂ) (q : ℕ → Poly n) (hq : q N = 0) (R : ℂ) :
    ∑ k ∈ Finset.range (N + 1), a (k + 1) * (R * ev g (prev q k)) =
      ∑ k ∈ Finset.range (N + 1), a (k + 1 + 1) * (R * ev g (q k)) := by
  rw [Finset.sum_range_succ', Finset.sum_range_succ (n := N), hq]
  simp [prev]

theorem famF_hasDerivAt : ∀ {n : ℕ} (ε : Fin n → Bool) (G : ℝ → ℝ) (p : ℕ → GlobalTheory.PsCo.Pc1.Poly n) (q : GlobalTheory.PsCo.Pc1.Mode ε → ℕ → GlobalTheory.PsCo.Pc1.Poly n), ContDiff ℝ (⊤ : ℕ∞) G → GlobalTheory.PsCo.Pc1.IsKoszul ε p q → ∀ t : ℝ, 0 < t → ∀ g : GlobalTheory.PsCo.Pc1.Mat n, HasDerivAt (fun s : ℝ => GlobalTheory.PsCo.Pc1.famF ε G p s g) (((t⁻¹ : ℝ) : ℂ) * ∑ x : GlobalTheory.PsCo.Pc1.Mode ε, ∑ j ∈ Finset.range (GlobalTheory.PsCo.Pc1.nMode ε + 1), GlobalTheory.PsCo.Pc1.adBas ε (Matrix.single x.1.2 x.1.1 1) (iteratedDeriv (j + 1) (fun y => G (t * y))) (q x j) g) t := by
  intro n ε G p q hG hK t ht g
  obtain ⟨hrec, hp, hq⟩ := hK
  let a : ℕ → ℂ := fun j => ((iteratedDeriv j (fun y => G (t * y)) (rM ε g) : ℝ) : ℂ)
  have hd : ∀ k ∈ Finset.range (nMode ε + 1),
      HasDerivAt (fun s : ℝ => bas ε (iteratedDeriv k fun x => G (s * x)) (p k) g)
        (((t⁻¹ : ℝ) : ℂ) * (((k : ℂ) * a k + (rM ε g : ℂ) * a (k + 1)) * ev g (p k))) t := by
    intro k _
    refine (((hasDerivAt_scale G hG k (rM ε g) t ht.ne').ofReal_comp).mul_const (ev g (p k))).congr_deriv ?_
    simp only [a]
    push_cast
    ring
  refine (HasDerivAt.fun_sum hd).congr_deriv ?_
  rw [← Finset.mul_sum]
  congr 1
  have hA : ∀ (x : Mode ε) (j : ℕ),
      adBas ε (Matrix.single x.1.2 x.1.1 1) (iteratedDeriv (j + 1) (fun y => G (t * y))) (q x j) g =
        a (j + 1) * ev g (dM ε x (q x j)) + a (j + 1 + 1) * (ev g (dM ε x (rP ε)) * ev g (q x j)) := by
    intro x j
    simp only [adBas, bas, dM, ← iteratedDeriv_succ, map_mul, a]
    ring
  have hR : ∀ j : ℕ, ((j : ℂ) + 1) * ev g (p (j + 1)) + (rM ε g : ℂ) * ev g (p j) =
      ∑ x, (ev g (dM ε x (q x j)) + ev g (dM ε x (rP ε)) * ev g (prev (q x) j)) := by
    intro j
    have := congrArg (ev g) (hrec j)
    simpa only [map_sum, map_add, map_mul, ev_rP, map_natCast, map_one] using this
  rw [sum_shift (nMode ε) a (fun k => ev g (p k)) (rM ε g : ℂ) (by simp [hp (nMode ε + 1) (Nat.lt_succ_self _)])]
  simp only [hA, hR, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [mul_add, Finset.sum_add_distrib]
  rw [sum_prev g (nMode ε) a (q x) (hq x _ le_rfl)]

end GlobalTheory.PsCo.HomotDeriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchemeHomExtOfJointlyInjectiveStatement
section
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scheme_hom_ext_of_jointly_surjective_of_app_injective : ∀ (Z Z₁ Z₂ X : Scheme.{0}) (e₁ : Z₁ ⟶ Z) (e₂ : Z₂ ⟶ Z), (∀ z : Z, (∃ z₁, e₁ z₁ = z) ∨ ∃ z₂, e₂ z₂ = z) → (∀ (W : Z.Opens) (a b : Γ(Z, W)), e₁.app W a = e₁.app W b → e₂.app W a = e₂.app W b → a = b) → ∀ f g : Z ⟶ X, e₁ ≫ f = e₁ ≫ g → e₂ ≫ f = e₂ ≫ g → f = g := by
  first | exact @GlobalTheory.scheme_hom_ext_of_jointly_injective | exact GlobalTheory.scheme_hom_ext_of_jointly_injective | (intros; apply GlobalTheory.scheme_hom_ext_of_jointly_injective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchemeTheoreticallyDominantOfGermInjectiveStatement
section
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schemeTheoreticallyDominant_of_germ_injective : ∀ (X T : Scheme.{0}) (p : X ⟶ T) (W : X.Opens),
    (∀ (U : X.Opens) (V : T.Opens), IsAffineOpen U → IsAffineOpen V → U ≤ p ⁻¹ᵁ V →
      ∀ b : Γ(X, U), (∀ (x : X) (hx : x ∈ U), x ∈ W → X.presheaf.germ U x hx b = 0) → b = 0) →
    IsSchemeTheoreticallyDominant W.ι := by
  first | exact @GlobalTheory.isSchemeTheoreticallyDominant_ι_of_germ_eq_zero_over_affine | exact GlobalTheory.isSchemeTheoreticallyDominant_ι_of_germ_eq_zero_over_affine | (intros; apply GlobalTheory.isSchemeTheoreticallyDominant_ι_of_germ_eq_zero_over_affine <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerRepUnitary
section
open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap

namespace GlobalTheory.RealWeil

theorem integral_rhoFun_mul_conj (n : ℕ) (w : Fin n ⊕ Fin n → ℝ) (u v : EuclideanSpace ℝ (Fin n) → ℂ) :
    ∫ x, rhoFun w u x * starRingEnd ℂ (rhoFun w v x) = ∫ x, u x * starRingEnd ℂ (v x) := by
  have h : ∀ x, rhoFun w u x * starRingEnd ℂ (rhoFun w v x) =
      u (x + pPart w) * starRingEnd ℂ (v (x + pPart w)) := by
    intro x
    have hp : phase w x * starRingEnd ℂ (phase w x) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_phase]
      simp
    simp only [rhoFun, map_mul]
    calc _ = (phase w x * starRingEnd ℂ (phase w x)) * (u (x + pPart w) * starRingEnd ℂ (v (x + pPart w))) := by
          ring
      _ = _ := by rw [hp, one_mul]
  simp_rw [h]
  exact integral_add_right_eq_self (fun x => u x * starRingEnd ℂ (v x)) (pPart w)

end GlobalTheory.RealWeil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzClosureStableLinearFormFourierStatement
section
open FourierTransform MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topologicalClosure_stable_linearForm_mul_and_fourier : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (W : Submodule ℂ (SchwartzMap E ℂ)),
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ W → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ W) →
    (∀ f ∈ W, 𝓕 f ∈ W) →
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ W.topologicalClosure → (∀ x, f₁ x = (ℓ x : ℂ) * f x) →
      f₁ ∈ W.topologicalClosure) ∧
    (∀ f ∈ W.topologicalClosure, 𝓕 f ∈ W.topologicalClosure) := by
  first | exact @GlobalTheory.schwartz_closure_stable_linearForm_fourier | exact GlobalTheory.schwartz_closure_stable_linearForm_fourier | (intros; apply GlobalTheory.schwartz_closure_stable_linearForm_fourier <;> assumption)
end

