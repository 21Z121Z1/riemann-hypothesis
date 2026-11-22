import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0020
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0015
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0017
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0018
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import GroundTheory.HeightsAndTheta.Heights.Intersections.ProjLineRankTwoPushforwardHypotheses

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.IsAlgebraicMapAdjoin
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

variable {Ω Φ : Type*} [Field Ω] [Field Φ] [Algebra Ω Φ]

theorem RatioField.map_mem [CharZero Ω] [CharZero Φ] {S : Set Ω} {L : IntermediateField ℚ Φ}
    (hS : ∀ w ∈ S, algebraMap Ω Φ w ∈ L) {z : Ω} (hz : z ∈ IntermediateField.adjoin ℚ S) :
    algebraMap Ω Φ z ∈ L := by
  have hle : (IntermediateField.adjoin ℚ S).map (algebraMap Ω Φ).toRatAlgHom ≤ L := by
    rw [IntermediateField.adjoin_map, IntermediateField.adjoin_le_iff]
    rintro _ ⟨w, hw, rfl⟩
    exact hS w hw
  exact hle ((IntermediateField.mem_map _).mpr ⟨z, hz, rfl⟩)

theorem RatioField.isAlgebraic_map [CharZero Ω] [CharZero Φ] {d : ℕ} {t : Fin d → Ω}
    (ht : AlgebraicIndependent ℚ t) {z : Ω} (hz : IsAlgebraic (IntermediateField.adjoin ℚ (Set.range t)) z)
    {s : Set Φ} (hs : ∀ n, algebraMap Ω Φ (t n) ∈ s) :
    IsAlgebraic (IntermediateField.adjoin ℚ s) (algebraMap Ω Φ z) := by
  let ψ := (algebraMap Ω Φ).toRatAlgHom
  have ht' : AlgebraicIndependent ℚ (ψ ∘ t) := ht.map' (algebraMap Ω Φ).injective
  have h4 : IsAlgebraic (Algebra.adjoin ℚ (Set.range (ψ ∘ t))) (ψ z) := by
    by_contra h
    have h3 : AlgebraicIndependent ℚ (fun o : Option (Fin d) => o.elim z t) := by
      refine AlgebraicIndependent.of_comp ψ ?_
      convert (ht'.option_iff_transcendental (ψ z)).mpr h using 1
      funext o
      cases o <;> rfl
    exact (ht.option_iff_transcendental z).mp h3 (IntermediateField.isAlgebraic_adjoin_iff.mp hz)
  have hsub : Set.range (ψ ∘ t) ⊆ s := by
    rintro _ ⟨n, rfl⟩
    exact hs n
  exact IntermediateField.isAlgebraic_adjoin_iff.mpr (h4.tower_top_of_subalgebra_le (Algebra.adjoin_mono hsub))

theorem RatioField.isAlgebraic_map_adjoin [CharZero Ω] [CharZero Φ] {d : ℕ} {t : Fin d → Ω}
    (ht : AlgebraicIndependent ℚ t) {S : Set Ω}
    (hS : ∀ w ∈ S, IsAlgebraic (IntermediateField.adjoin ℚ (Set.range t)) w) {s : Set Φ}
    (hs : ∀ n, algebraMap Ω Φ (t n) ∈ s) {z : Ω} (hz : z ∈ IntermediateField.adjoin ℚ S) :
    IsAlgebraic (IntermediateField.adjoin ℚ s) (algebraMap Ω Φ z) := by
  have h := RatioField.map_mem (L := (algebraicClosure (IntermediateField.adjoin ℚ s) Φ).restrictScalars ℚ)
    (fun w hw => (IntermediateField.mem_restrictScalars ℚ).mpr
      (mem_algebraicClosure_iff.mpr (RatioField.isAlgebraic_map ht (hS w hw) hs))) hz
  exact mem_algebraicClosure_iff.mp ((IntermediateField.mem_restrictScalars ℚ).mp h)

variable {E κ : Type*} [AddCommGroup E] [Module Ω E]

theorem RatioField.lineVal_cramer (e b : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (g : κ → Fin 2 → Ω)
    (X : Ω) (k₀ k₁ k : κ) (hφ : ∀ k q, φ k (b q) = X * g k q)
    (hg : g k₀ 0 * g k₁ 1 - g k₀ 1 * g k₁ 0 ≠ 0) (a : Φ) :
    T.lineVal e (φ k) a =
      algebraMap Ω Φ ((g k 0 * g k₁ 1 - g k 1 * g k₁ 0) / (g k₀ 0 * g k₁ 1 - g k₀ 1 * g k₁ 0)) *
          T.lineVal e (φ k₀) a +
        algebraMap Ω Φ ((g k₀ 0 * g k 1 - g k₀ 1 * g k 0) / (g k₀ 0 * g k₁ 1 - g k₀ 1 * g k₁ 0)) *
          T.lineVal e (φ k₁) a := by
  have hlin : φ k = ((g k 0 * g k₁ 1 - g k 1 * g k₁ 0) / (g k₀ 0 * g k₁ 1 - g k₀ 1 * g k₁ 0)) • φ k₀ +
      ((g k₀ 0 * g k 1 - g k₀ 1 * g k 0) / (g k₀ 0 * g k₁ 1 - g k₀ 1 * g k₁ 0)) • φ k₁ := by
    refine b.ext fun q => ?_
    simp only [LinearMap.add_apply, LinearMap.smul_apply, hφ, smul_eq_mul]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hg]
    fin_cases q <;> simp <;> ring
  rw [hlin]
  simp only [T.lineVal, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, map_add, map_mul]
  ring

theorem RatioField.det_ne_zero (e b : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (g : κ → Fin 2 → Ω)
    (X : Ω) (hX : X ≠ 0) (k₀ k₁ : κ) (hφ : ∀ k q, φ k (b q) = X * g k q)
    (hg : g k₀ 0 * g k₁ 1 - g k₀ 1 * g k₁ 0 ≠ 0) :
    φ k₁ (e 0) * φ k₀ (e 1) - φ k₁ (e 1) * φ k₀ (e 0) ≠ 0 := by
  have hval : ∀ k q, φ k (b q) = e.repr (b q) 0 * φ k (e 0) + e.repr (b q) 1 * φ k (e 1) := by
    intro k q
    conv_lhs => rw [← e.sum_repr (b q)]
    simp only [Fin.sum_univ_two, map_add, map_smul, smul_eq_mul]
  intro h
  apply hg
  have hX2 : X * X ≠ 0 := mul_ne_zero hX hX
  apply (mul_right_injective₀ hX2).eq_iff.mp
  have h00 := hval k₀ 0
  have h01 := hval k₀ 1
  have h10 := hval k₁ 0
  have h11 := hval k₁ 1
  rw [hφ] at h00 h01 h10 h11
  linear_combination (X * g k₀ 0) * h11 + (e.repr (b 1) 1 * φ k₁ (e 1) + e.repr (b 1) 0 * φ k₁ (e 0)) * h00 -
    (X * g k₀ 1) * h10 - (e.repr (b 0) 1 * φ k₁ (e 1) + e.repr (b 0) 0 * φ k₁ (e 0)) * h01 +
    -(e.repr (b 0) 0 * e.repr (b 1) 1 - e.repr (b 0) 1 * e.repr (b 1) 0) * h

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.IsSmoothHermTensor
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem isSmoothHerm_tensor {A B : HermLine ι} (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) :
    IsSmoothHerm (A.tensor B) :=
  ContDiffOn.mul hA hB

theorem allSmooth_update {n : ℕ} {L : Fin n → HermLine ι} (hL : AllSmooth L) (j : Fin n)
    {X : HermLine ι} (hX : IsSmoothHerm X) : AllSmooth (Function.update L j X) := by
  intro i
  rcases eq_or_ne i j with rfl | h
  · simpa using hX
  · simpa [Function.update_of_ne h] using hL i

theorem allSmooth_snoc {n : ℕ} {L : Fin n → HermLine ι} (hL : ∀ j, IsSmoothHerm (L j))
    {A : HermLine ι} (hA : IsSmoothHerm A) : AllSmooth (Fin.snoc L A : Fin (n + 1) → HermLine ι) := by
  intro i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simpa using hA
  · simpa using hL i

theorem isSec_iff (P : Ideal (MRing ι)) (A : HermLine ι) (s : MRing ι) :
    IsSec P A s ↔ ∃ a : K → ℕ, (∀ k, A.a k = a k) ∧ IsMultiHomog s a ∧ s ∉ P := by
  constructor
  · rintro ⟨a, hs, ha, hP⟩
    exact ⟨a, fun k => (ha k).symm, hs, hP⟩
  · rintro ⟨a, ha, hs, hP⟩
    exact ⟨a, hs, fun k => (ha k).symm, hP⟩

theorem IsFamily.equiv_of_rhsR (I : Family ι)
    (hR : ∀ (P : Ideal (MRing ι)) (n : ℕ) (L : Fin n → HermLine ι) (A : HermLine ι) (s : MRing ι),
      rhsR I P L A s = recR I P L A s) :
    IsFamily I ↔ IsIntersectionFamily I := by
  constructor
  · rintro ⟨hsym, hadd, hrec⟩
    refine ⟨fun P n L σ hP hL => hsym P n L σ trivial hP hL, ?_, ?_⟩
    · intro P n L A B hP hL hA hB
      have hLA : AllSmooth (Fin.snoc L A : Fin (n + 1) → HermLine ι) := allSmooth_snoc hL hA
      have h := hadd P (n + 1) (Fin.snoc L A) (Fin.last n) A B trivial hP hLA hA hB
      simpa only [Fin.update_snoc_last] using h
    · intro P n L A s a hP hL hA ha hs hsP
      have h := hrec P n (Fin.snoc L A) s trivial hP (allSmooth_snoc hL hA)
        (by simpa only [Fin.snoc_last] using (isSec_iff P A s).2 ⟨a, ha, hs, hsP⟩)
      rw [h, Fin.init_snoc, Fin.snoc_last, hR]
  · rintro ⟨hsym, hadd, hrec⟩
    refine ⟨fun P n L σ _ hP hL => hsym P n L σ hP hL, ?_, ?_⟩
    · intro P n L j A B _ hP hL hA hB
      cases n with
      | zero => exact j.elim0
      | succ m =>
        set σ : Equiv.Perm (Fin (m + 1)) := Equiv.swap j (Fin.last m) with hσ
        have key : ∀ X : HermLine ι, IsSmoothHerm X →
            I P (m + 1) (Function.update L j X) = I P (m + 1) (Fin.snoc (Fin.init (L ∘ σ)) X) := by
          intro X hX
          have e : Function.update L j X ∘ σ = Fin.snoc (Fin.init (L ∘ σ)) X := by
            rw [Function.update_comp_equiv, hσ, Equiv.symm_swap, Equiv.swap_apply_left]
            conv_lhs => rw [← Fin.snoc_init_self (L ∘ ⇑(Equiv.swap j (Fin.last m)))]
            exact Fin.update_snoc_last _ _ _
          rw [← e, hsym P (m + 1) _ σ hP (allSmooth_update hL j hX)]
        have hL' : ∀ i, IsSmoothHerm (Fin.init (L ∘ σ) i) := fun i => hL _
        rw [key _ (isSmoothHerm_tensor hA hB), key A hA, key B hB]
        exact hadd P m _ A B hP hL' hA hB
    · intro P n L s _ hP hL hs
      obtain ⟨a, ha, hsm, hsP⟩ := (isSec_iff P _ s).1 hs
      have h := hrec P n (Fin.init L) (L (Fin.last n)) s a hP (fun i => hL _) (hL _) ha hsm hsP
      rw [Fin.snoc_init_self] at h
      rw [h, hR]

theorem IsFamily.equiv (I : Family ι) : IsFamily I ↔ IsIntersectionFamily I :=
  IsFamily.equiv_of_rhsR I fun P _ L A s => rhsR.equiv I P L A s

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.LeOfHeightMapEqZero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem RegularityDivisorSupportClosed.le_of_height_map_eq_zero {A : Type*} [CommRing A] {P Q : Ideal A} [P.IsPrime]
    (h : (Q.map (Ideal.Quotient.mk P)).height = 0) : Q ≤ P := by
  intro x hx
  rw [Ideal.height_eq_zero_iff_eq_bot] at h
  have : Ideal.Quotient.mk P x ∈ Q.map (Ideal.Quotient.mk P) := Ideal.mem_map_of_mem _ hx
  rwa [h, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at this

theorem RegularityDivisorSupportClosed.not_add_add {m : ℕ} {a b : ℕ∞} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ((m : WithBot ℕ∞) + (a : WithBot ℕ∞)) + (b : WithBot ℕ∞) = ((m + 1 : ℕ) : WithBot ℕ∞)) :
    False := by
  have h' : (m : ℕ∞) + a + b = ((m + 1 : ℕ) : ℕ∞) := by exact_mod_cast h
  induction a using ENat.recTopCoe with
  | top => simp at h'; exact ENat.natCast_ne_top (m + 1) (by exact_mod_cast h'.symm)
  | coe a =>
    induction b using ENat.recTopCoe with
    | top => simp at h'; exact ENat.natCast_ne_top (m + 1) (by exact_mod_cast h'.symm)
    | coe b =>
      have : m + a + b = m + 1 := by exact_mod_cast h'
      have : a ≠ 0 := by exact_mod_cast ha
      have : b ≠ 0 := by exact_mod_cast hb
      omega

theorem RegularityDivisorSupportClosed.proof : RegularityDivisorSupportClosed.Statement := by
  intro K _ ι _ P s a W hP hs hsP
  obtain ⟨-, ⟨hPp, hPh, -⟩, -, hPdim⟩ := hP
  have := hPp
  have hsW' : ∀ {Q : Ideal (MRing ι)}, P ⊔ Ideal.span {s} ≤ Q → s ∈ Q := fun h =>
    h (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
  constructor
  · rintro ⟨hWmin, hWrel⟩
    have h1 := dim_quot_minimal_add_one P W s hsP hWmin
    rw [hPdim] at h1
    refine ⟨⟨⟨hWmin.1.1, isMultiHomogIdeal_of_mem_minimalPrimes hPh hs hWmin, hWrel⟩,
      withBot_eq_of_add_one (by rw [h1, Nat.add_comm])⟩, le_sup_left.trans hWmin.1.2, hsW' hWmin.1.2⟩
  · rintro ⟨⟨⟨hWp, -, hWrel⟩, hWdim⟩, hPW, hsW⟩
    have hle : P ⊔ Ideal.span {s} ≤ W := sup_le hPW ((Ideal.span_singleton_le_iff_mem _).mpr hsW)
    refine ⟨⟨⟨hWp, hle⟩, fun Q hQ hQW => ?_⟩, hWrel⟩
    have := hQ.1
    have hPQ : P ≤ Q := le_sup_left.trans hQ.2
    have e1 := mvPolynomialInt_dimFormula P Q hPQ
    have e2 := mvPolynomialInt_dimFormula Q W hQW
    rw [hPdim] at e1
    rw [hWdim] at e2
    by_contra hWQ
    have ha : (W.map (Ideal.Quotient.mk Q)).height ≠ 0 := fun h0 =>
      hWQ (RegularityDivisorSupportClosed.le_of_height_map_eq_zero h0)
    have hb : (Q.map (Ideal.Quotient.mk P)).height ≠ 0 := fun h0 =>
      hsP (RegularityDivisorSupportClosed.le_of_height_map_eq_zero h0 (hsW' hQ.2))
    rw [← e2] at e1
    exact RegularityDivisorSupportClosed.not_add_add ha hb (by rw [e1, Nat.add_comm])

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.LeviOfRealSmulRight
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open Matrix Filter Topology ReciprocityTheory.ChartRestriction.G.Geo

namespace pointFormEuler_holds

section Levi

variable {n : ℕ}

def leviOf (H : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ) (u v : Fin n → ℂ) : ℂ :=
  ((H u v + H (Complex.I • u) (Complex.I • v) : ℝ) +
    Complex.I * ((H u (Complex.I • v) - H (Complex.I • u) v : ℝ))) / 4

theorem leviOf_add_right (H : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ) (u v w : Fin n → ℂ) :
    leviOf H u (v + w) = leviOf H u v + leviOf H u w := by
  simp only [leviOf, smul_add, map_add]
  push_cast
  ring

theorem leviOf_real_smul_right (H : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ) (u v : Fin n → ℂ) (r : ℝ) :
    leviOf H u (r • v) = r * leviOf H u v := by
  simp only [leviOf, smul_comm Complex.I r v, map_smul, smul_eq_mul]
  push_cast
  ring

theorem leviOf_I_smul_right (H : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ) (u v : Fin n → ℂ) :
    leviOf H u (Complex.I • v) = -Complex.I * leviOf H u v := by
  have h : Complex.I • Complex.I • v = -v := by rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  simp only [leviOf, h, map_neg]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

theorem leviOf_sum_right (H : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ) (u : Fin n → ℂ) (v : Fin n → Fin n → ℂ) :
    leviOf H u (∑ j, v j) = ∑ j, leviOf H u (v j) := by
  classical
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty =>
    have h0 : leviOf H u 0 = 0 := by simp [leviOf]
    simpa using h0
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, leviOf_add_right, ih]

theorem cxHessian_mulVec_star (f : (Fin n → ℂ) → ℝ) (y x : Fin n → ℂ) (i : Fin n) :
    (cxHessian f y *ᵥ star x) i = leviOf (fderiv ℝ (fderiv ℝ f) y) (Pi.single i 1) x := by
  set H := fderiv ℝ (fderiv ℝ f) y
  have hx : x = ∑ j, ((x j).re • (Pi.single j 1 : Fin n → ℂ) +
      (x j).im • (Complex.I • (Pi.single j 1 : Fin n → ℂ))) := by
    funext p
    simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, Pi.single_apply, Complex.real_smul, smul_eq_mul,
      mul_ite, mul_one, mul_zero, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    conv_lhs => rw [← Complex.re_add_im (x p)]
  have hent : ∀ j, cxHessian f y i j = leviOf H (Pi.single i 1) (Pi.single j 1) := fun j => rfl
  conv_rhs => rw [hx]
  rw [leviOf_sum_right]
  simp only [mulVec, dotProduct, hent]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [leviOf_add_right, leviOf_real_smul_right, leviOf_real_smul_right, leviOf_I_smul_right]
  have hs : star (x j) = ((x j).re : ℂ) - (x j).im * Complex.I := by
    apply Complex.ext <;> simp
  simp only [Pi.star_apply, hs]
  ring

end Levi

section Ambient

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem logh_contDiffAt {A : HermLine ι} (hA : IsSmoothHerm A) {z : (Σ k, ι k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : ContDiffAt ℝ 2 (fun z' => Real.log (A.h z')) z :=
  ((hA.contDiffAt (isOpen_blockNonzero.mem_nhds hz)).of_le (WithTop.coe_le_coe.mpr le_top)).log
    (A.pos z hz).ne'

def bsmulCLM (d : K → ℂ) : ((Σ k, ι k) → ℂ) →L[ℂ] ((Σ k, ι k) → ℂ) :=
  ContinuousLinearMap.pi fun p => d p.1 • ContinuousLinearMap.proj p

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem bsmulCLM_apply (d : K → ℂ) (z : (Σ k, ι k) → ℂ) : bsmulCLM d z = bsmul d z := by
  funext p
  simp [bsmulCLM, bsmul]

theorem fderiv_logh_bsmul (A : HermLine ι) (hA : IsSmoothHerm A) (d : K → ℂ) {z : (Σ k, ι k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    fderiv ℝ (fun z' => Real.log (A.h z')) z (bsmul d z) =
      deriv (fun s : ℝ => Real.log (∏ k, ‖1 + (s : ℂ) * d k‖ ^ A.a k)) 0 := by
  set φ : ((Σ k, ι k) → ℂ) → ℝ := fun z' => Real.log (A.h z')
  have hφ : HasFDerivAt φ (fderiv ℝ φ z) z :=
    ((logh_contDiffAt hA hz).differentiableAt (by norm_num)).hasFDerivAt
  have hpath : HasDerivAt (fun s : ℝ => z + s • bsmul d z) (bsmul d z) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (bsmul d z)).const_add z
  have h1 : HasDerivAt (fun s : ℝ => φ (z + s • bsmul d z)) (fderiv ℝ φ z (bsmul d z)) 0 := by
    exact hφ.comp_hasDerivAt_of_eq (0 : ℝ) hpath (by simp)
  have hne : ∀ᶠ s : ℝ in 𝓝 0, ∀ k, 1 + (s : ℂ) * d k ≠ 0 :=
    eventually_all.mpr fun k => ContinuousAt.eventually_ne (by fun_prop) (by simp)
  have heq : (fun s : ℝ => φ (z + s • bsmul d z)) =ᶠ[𝓝 0]
      fun s : ℝ => Real.log (∏ k, ‖1 + (s : ℂ) * d k‖ ^ A.a k) + φ z := by
    filter_upwards [hne] with s hs
    have hp : z + s • bsmul d z = fun p => (1 + (s : ℂ) * d p.1) * z p := by
      funext p
      simp only [Pi.add_apply, Pi.smul_apply, bsmul, Complex.real_smul]
      ring
    have hpos : 0 < ∏ k, ‖1 + (s : ℂ) * d k‖ ^ A.a k :=
      Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.mpr (hs k)) _
    simp only [φ]
    rw [hp, A.smul (fun k => 1 + (s : ℂ) * d k) z hs, Real.log_mul hpos.ne' (A.pos z hz).ne']
  rw [(h1.congr_of_eventuallyEq heq.symm).deriv.symm, deriv_add_const]

theorem hess_logh_bsmul (A : HermLine ι) (hA : IsSmoothHerm A) (d : K → ℂ) {z : (Σ k, ι k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (w : (Σ k, ι k) → ℂ) :
    fderiv ℝ (fderiv ℝ (fun z' => Real.log (A.h z'))) z w (bsmul d z) =
      -fderiv ℝ (fun z' => Real.log (A.h z')) z (bsmul d w) := by
  set φ : ((Σ k, ι k) → ℂ) → ℝ := fun z' => Real.log (A.h z')
  set L : ((Σ k, ι k) → ℂ) →L[ℝ] ((Σ k, ι k) → ℂ) := (bsmulCLM d).restrictScalars ℝ
  have hL : ∀ v, L v = bsmul d v := fun v => bsmulCLM_apply d v
  have hconst : (fun z' => fderiv ℝ φ z' (L z')) =ᶠ[𝓝 z]
      fun _ => deriv (fun s : ℝ => Real.log (∏ k, ‖1 + (s : ℂ) * d k‖ ^ A.a k)) 0 := by
    filter_upwards [isOpen_blockNonzero.mem_nhds hz] with z' hz'
    rw [hL]
    exact fderiv_logh_bsmul A hA d hz'
  have hd1 : DifferentiableAt ℝ (fderiv ℝ φ) z :=
    ((logh_contDiffAt hA hz).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h0 : fderiv ℝ (fun z' => fderiv ℝ φ z' (L z')) z w = 0 := by
    rw [hconst.fderiv_eq]
    simp
  rw [fderiv_clm_apply hd1 L.differentiableAt, L.fderiv] at h0
  simp only [_root_.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, hL] at h0
  linarith

end Ambient

section Chain

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {n : ℕ}

theorem hess_comp_holo {φ : ((Σ k, ι k) → ℂ) → ℝ} {F : (Fin n → ℂ) → (Σ k, ι k) → ℂ} {y : Fin n → ℂ}
    (hφ : ContDiffAt ℝ 2 φ (F y)) (hF : AnalyticAt ℂ F y) (u v : Fin n → ℂ) :
    fderiv ℝ (fderiv ℝ (fun y' => φ (F y'))) y u v =
      fderiv ℝ (fderiv ℝ φ) (F y) (fderiv ℂ F y u) (fderiv ℂ F y v) +
        fderiv ℝ φ (F y) (fderiv ℂ (fun y' => fderiv ℂ F y' v) y u) := by
  have hψ : ContDiffAt ℝ 2 (fun y' => φ (F y')) y := hφ.comp y (hF.contDiffAt.restrict_scalars ℝ)
  have hψ1 : DifferentiableAt ℝ (fderiv ℝ (fun y' => φ (F y'))) y :=
    (hψ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hφev : ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 φ (F y') :=
    hF.continuousAt.tendsto.eventually (hφ.eventually (by simp))
  have hFev := hF.eventually_analyticAt
  have hcw : fderiv ℝ (fderiv ℝ (fun y' => φ (F y'))) y u v =
      fderiv ℝ (fun y' => fderiv ℝ (fun y'' => φ (F y'')) y' v) y u := by
    rw [fderiv_clm_apply hψ1 (differentiableAt_const v)]
    simp
  have hev : (fun y' => fderiv ℝ (fun y'' => φ (F y'')) y' v) =ᶠ[𝓝 y]
      fun y' => fderiv ℝ φ (F y') (fderiv ℂ F y' v) := by
    filter_upwards [hφev, hFev] with y' h1 h2
    rw [fderiv_fun_comp y' (h1.differentiableAt (by norm_num)) (h2.differentiableAt.restrictScalars ℝ),
      h2.differentiableAt.fderiv_restrictScalars ℝ]
    rfl
  have hd1 : DifferentiableAt ℝ (fderiv ℝ φ) (F y) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hc : DifferentiableAt ℝ (fun y' => fderiv ℝ φ (F y')) y :=
    hd1.comp y (hF.differentiableAt.restrictScalars ℝ)
  have hG : DifferentiableAt ℂ (fun y' => fderiv ℂ F y' v) y :=
    hF.fderiv.differentiableAt.clm_apply (differentiableAt_const v)
  rw [hcw, hev.fderiv_eq, fderiv_clm_apply hc (hG.restrictScalars ℝ),
    fderiv_fun_comp y hd1 (hF.differentiableAt.restrictScalars ℝ),
    hG.fderiv_restrictScalars ℝ, hF.differentiableAt.fderiv_restrictScalars ℝ]
  simp only [_root_.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.coe_restrictScalars']
  ring

end Chain

theorem proof : pointFormEuler_holds.Statement := by
  intro K _ ι _ A n F y x c hA hF hblk hx
  have hφ : ContDiffAt ℝ 2 (fun z' => Real.log (A.h z')) (F y) := logh_contDiffAt hA hblk
  have hchain : ∀ u v, fderiv ℝ (fderiv ℝ (fun y' => Real.log (A.h (F y')))) y u v =
      fderiv ℝ (fderiv ℝ (fun z' => Real.log (A.h z'))) (F y) (fderiv ℂ F y u) (fderiv ℂ F y v) +
        fderiv ℝ (fun z' => Real.log (A.h z')) (F y) (fderiv ℂ (fun y' => fderiv ℂ F y' v) y u) :=
    fun u v => hess_comp_holo (φ := fun z' => Real.log (A.h z')) hφ hF u v
  have hG : DifferentiableAt ℂ (fun y' => fderiv ℂ F y' x) y :=
    hF.fderiv.differentiableAt.clm_apply (differentiableAt_const x)
  have hGI : fderiv ℂ (fun y' => fderiv ℂ F y' (Complex.I • x)) y =
      Complex.I • fderiv ℂ (fun y' => fderiv ℂ F y' x) y := by
    have : (fun y' => fderiv ℂ F y' (Complex.I • x)) = fun y' => Complex.I • fderiv ℂ F y' x := by
      funext y'
      exact map_smul _ _ _
    rw [this, fderiv_fun_const_smul hG]
  have hJIx : fderiv ℂ F y (Complex.I • x) = bsmul (fun k => Complex.I * c k) (F y) := by
    rw [map_smul, hx]
    funext p
    simp only [Pi.smul_apply, bsmul, smul_eq_mul]
    ring
  have hbI : ∀ (d : K → ℂ) (w : (Σ k, ι k) → ℂ),
      bsmul d (Complex.I • w) = bsmul (fun k => Complex.I * d k) w := by
    intro d w
    funext p
    simp only [Pi.smul_apply, bsmul, smul_eq_mul]
    ring
  have hbII : ∀ (d : K → ℂ) (w : (Σ k, ι k) → ℂ),
      bsmul (fun k => Complex.I * d k) (Complex.I • w) = -bsmul d w := by
    intro d w
    funext p
    simp only [Pi.smul_apply, Pi.neg_apply, bsmul, smul_eq_mul]
    linear_combination (d p.1 * w p) * Complex.I_sq
  have hII : ∀ w : (Σ k, ι k) → ℂ, Complex.I • Complex.I • w = -w := fun w => by
    rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  have heul := fun d w => hess_logh_bsmul A hA d hblk w
  funext i
  rw [cxHessian_mulVec_star, Pi.zero_apply]
  unfold leviOf
  rw [hchain, hchain, hchain, hchain, hJIx, hx, hGI]
  simp only [map_smul, _root_.smul_apply]
  rw [heul, heul, heul, heul, hbII, hbI, hII]
  simp only [map_neg]
  push_cast
  ring

end pointFormEuler_holds

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StFlagMinorsBaseChange
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial

def FlagMinorsBaseChange.Statement : Prop :=
  ∀ (F : Type) [Field F] (n N1 : ℕ) (B : Matrix (Fin n) (Fin N1) F), LinearIndependent F B →
    Algebra.adjoin F (Set.range fun q : Σ j, PluckerBlocks N1 n j => flagMinor (genMat F n * B.map C) q.1 q.2) =
      Algebra.adjoin F (Set.range fun q : Σ j, PluckerBlocks n n j => flagMinor (genMat F n) q.1 q.2)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

