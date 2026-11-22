import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0014
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthNormLogBoundIffOrthBound
section
open scoped ComplexOrder Matrix
open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col

noncomputable section

namespace GlobalTheory.BrNormCompare

open GlobalTheory.IndefiniteRowSideFullHecke

theorem gramSum_eq_sumGram {K : Type} [Field K] {N n : ℕ} (hN : N = n + 1) (G' : Matrix (Fin n) (Fin n) K) (g : K) :
    OrthogonalNormSquareSum.gramSum hN G' g = ScaledCoisometryNorms.sumGram N G' g := by
  ext a b
  simp only [OrthogonalNormSquareSum.gramSum, ScaledCoisometryNorms.sumGram, Matrix.of_apply]
  by_cases ha : a.1 < n
  · simp [ha]
  · by_cases hb : b.1 < n
    · simp [ha, hb]
    · have h1 : a = Br.iL hN := Fin.ext (by have := a.2; simp only [Br.iL]; omega)
      have h2 : b = Br.iL hN := Fin.ext (by have := b.2; simp only [Br.iL]; omega)
      rw [dif_neg ha, dif_neg ha, if_neg hb, if_neg hb, if_pos ⟨h1, h2⟩]

theorem length_eq {K : Type} [Field K] [StarRing K] (s : K →+* ℂ) (hs : ∀ x : K, s (star x) = star (s x)) (g t : K) :
    s (star t * g * t) = ((‖s t‖ ^ 2 : ℝ) : ℂ) * s g := by
  rw [map_mul, map_mul, hs, ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  simp only [Complex.star_def]
  ring

section

variable {K : Type} [Field K] [StarRing K] {ι : Type} [Fintype ι] {N n : ℕ}

theorem isScaledCoisometry_iff (s : K →+* ℂ) (lam : ι → DomWeight N) (G : ι → Matrix (Fin N) (Fin N) K)
    (sg : ι → DomWeight n) (G' : ι → Matrix (Fin n) (Fin n) K) (P : VV K lam →ₗ[K] VV K sg) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    OrthogonalNormSquareSum.IsScaledCoisometry s lam G sg G' P ρ ↔ 0 < ρ ^ 2 ∧ ScaledCoisometryNorms.IsScaledCoisometry s lam sg G G' P (ρ ^ 2) := by
  unfold OrthogonalNormSquareSum.IsScaledCoisometry ScaledCoisometryNorms.IsScaledCoisometry
  refine and_congr_left' ⟨fun h => pow_pos h 2, fun h => lt_of_le_of_ne hρ ?_⟩
  rintro rfl
  simp at h

theorem factor_nonneg (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n) {T : ℝ} (hT : 0 < T) :
    0 ≤ OrthogonalNormSquareSum.factor hN lam sg T :=
  mul_nonneg (mul_nonneg (Real.rpow_nonneg hT.le _) (abs_nonneg _)) (Real.sqrt_nonneg _)

theorem prod_factor_sq (hN : N = n + 1) (lam : ι → DomWeight N) (sg : ι → DomWeight n) {T : ℝ} (hT : 0 < T) :
    (∏ τ, OrthogonalNormSquareSum.factor hN (lam τ) (sg τ) T) ^ 2 = ScaledCoisometryNorms.brSq hN lam sg T := by
  rw [← Finset.prod_pow]
  exact Finset.prod_congr rfl fun τ _ => OrthogonalNormSquareSum.factor_sq hN _ _ hT

theorem const_eq (hN : N = n + 1) (lam : ι → DomWeight N) (sg : ι → DomWeight n) {T : ℝ} (hT : 0 < T) :
    T ^ (-∑ τ, Br.nBr (lam τ) (sg τ)) * OrthogonalNormSquareSum.orthNormSq hN lam sg = ScaledCoisometryNorms.brSq hN lam sg T :=
  (ScaledCoisometryNorms.brSq_eq hN lam sg hT).symm

theorem whole_iff (s : K →+* ℂ) (hN : N = n + 1) (lam : ι → DomWeight N) (sg : ι → DomWeight n)
    (G : ι → Matrix (Fin N) (Fin N) K) (G' : ι → Matrix (Fin n) (Fin n) K) (t : ι → K) {T : ℝ} (hT : 0 < T) :
    (OrthogonalNormSquareSum.IsScaledCoisometry s lam G sg G' (Br.brAt hN lam sg t) (∏ τ, OrthogonalNormSquareSum.factor hN (lam τ) (sg τ) T) ∧
      OrthogonalNormSquareSum.HasOpNormSq s lam G sg G' (Br.brAt hN lam sg t)
        (T ^ (-∑ τ, Br.nBr (lam τ) (sg τ)) * OrthogonalNormSquareSum.orthNormSq hN lam sg)) ↔
    ScaledCoisometryNorms.NormConcl s hN lam sg G G' t T := by
  rw [isScaledCoisometry_iff s lam G sg G' _ (Finset.prod_nonneg fun τ _ => factor_nonneg hN _ _ hT),
    prod_factor_sq hN lam sg hT, const_eq hN lam sg hT, and_assoc]
  rfl

theorem single_iff (s : K →+* ℂ) (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n)
    (G : Matrix (Fin N) (Fin N) K) (G' : Matrix (Fin n) (Fin n) K) (t : K) {T : ℝ} (hT : 0 < T) :
    OrthogonalNormSquareSum.IsScaledCoisometry s (fun _ : Unit => lam) (fun _ => G) (fun _ : Unit => sg) (fun _ => G')
        (Br.brAt hN (fun _ : Unit => lam) (fun _ : Unit => sg) fun _ => t) (OrthogonalNormSquareSum.factor hN lam sg T) ↔
      0 < ScaledCoisometryNorms.brSq hN (fun _ : Unit => lam) (fun _ : Unit => sg) T ∧
        ScaledCoisometryNorms.IsScaledCoisometry s (fun _ : Unit => lam) (fun _ : Unit => sg) (fun _ => G) (fun _ => G')
          (Br.brAt hN (fun _ : Unit => lam) (fun _ : Unit => sg) fun _ => t)
          (ScaledCoisometryNorms.brSq hN (fun _ : Unit => lam) (fun _ : Unit => sg) T) := by
  rw [isScaledCoisometry_iff _ _ _ _ _ _ (factor_nonneg hN lam sg hT), ← prod_factor_sq hN _ _ hT]
  simp

end

theorem lastMapNorm_iff_brNorm : OrthogonalNormSquareSum.LastMapNorm ↔ ScaledCoisometryNorms.BrNorm := by
  constructor
  · intro h K _ _ s hs ι _ N n hN lam sg h1 h2 G' hG g t T hT ht
    have := (h K s hs ι N n hN lam sg h1 h2 G' hG T hT g t fun τ => by rw [length_eq s hs, ht τ]).2
    rw [whole_iff s hN lam sg _ G' t hT] at this
    simpa only [gramSum_eq_sumGram] using this
  · intro h K _ _ s hs ι _ N n hN lam sg h1 h2 G' hG T hT g t ht
    have ht' : ∀ τ, ((‖s (t τ)‖ ^ 2 : ℝ) : ℂ) * s (g τ) = (T : ℂ) := fun τ => by rw [← length_eq s hs, ht τ]
    refine ⟨fun τ => ?_, ?_⟩
    · have := h K s hs Unit N n hN (fun _ => lam τ) (fun _ => sg τ) (fun _ => h1 τ) (fun _ => h2 τ) (fun _ => G' τ)
        (fun _ => hG τ) (fun _ => g τ) (fun _ => t τ) T hT (fun _ => ht' τ)
      rw [single_iff s hN _ _ _ _ _ hT, gramSum_eq_sumGram]
      exact ⟨this.1, this.2.1⟩
    · rw [whole_iff s hN lam sg _ G' t hT]
      simpa only [gramSum_eq_sumGram] using h K s hs ι N n hN lam sg h1 h2 G' hG g t T hT ht'

theorem last_ineq {ι : Type} [Fintype ι] {N n : ℕ} (hN : N = n + 1) (lam : ι → DomWeight N) (sg : ι → DomWeight n)
    (h1 : ∀ τ, Br.Interlace hN (lam τ) (sg τ)) (a : ℝ) (ha : ∀ τ, (((lam τ).spread : ℤ) : ℝ) ≤ 2 * a) :
    ∑ τ, (2 * ((N : ℝ) - 1) * ((OrthogonalNormSquareSum.dOne hN (lam τ) (sg τ) : ℤ) : ℝ) + (N : ℝ) * ((N : ℝ) - 1) / 2) * Real.log (2 * a) ≤
      2 * ∑ τ, ((N : ℝ) * ((OrthogonalNormSquareSum.dOne hN (lam τ) (sg τ) : ℤ) : ℝ) + (N : ℝ) ^ 2) * Real.log (2 * a) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun τ _ => ?_
  have hd : (0 : ℤ) ≤ OrthogonalNormSquareSum.dOne hN (lam τ) (sg τ) := by
    refine Finset.sum_nonneg fun i _ => le_min ?_ (Finset.sum_nonneg fun j _ => (h1 τ j).1)
    have := h1 τ i
    simp only [Br.aBr, Br.bBr] at this
    omega
  have hs : (1 : ℤ) ≤ (lam τ).spread := by
    have hpos : 0 < N := by omega
    have := (lam τ).anti (show (⟨0, hpos⟩ : Fin N) ≤ ⟨N - 1, by omega⟩ from Fin.mk_le_mk.mpr (Nat.zero_le _))
    simp only [DomWeight.spread, dif_pos hpos]
    omega
  have hd' : (0 : ℝ) ≤ ((OrthogonalNormSquareSum.dOne hN (lam τ) (sg τ) : ℤ) : ℝ) := by exact_mod_cast hd
  have hs' : (1 : ℝ) ≤ (((lam τ).spread : ℤ) : ℝ) := by exact_mod_cast hs
  have hl : 0 ≤ Real.log (2 * a) := Real.log_nonneg (hs'.trans (ha τ))
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  rw [← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ hl
  nlinarith [sq_nonneg (N : ℝ)]

end GlobalTheory.BrNormCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousEvaluationExistsUniqueSubstNatura
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.CEval

section Adic

variable {A : Type} [CommRing A] (p : ℕ)

theorem smodEq_of_dvd (m : ℕ) {y z : A} (h : (p : A) ^ m ∣ y - z) :
    y ≡ z [SMOD ((Ideal.span {(p : A)}) ^ m • ⊤ : Submodule A A)] := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
  exact Ideal.mem_span_singleton.2 h

theorem dvd_of_smodEq (m : ℕ) {y z : A}
    (h : y ≡ z [SMOD ((Ideal.span {(p : A)}) ^ m • ⊤ : Submodule A A)]) :
    (p : A) ^ m ∣ y - z := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow] at h
  exact Ideal.mem_span_singleton.1 h

theorem eq_of_forall_dvd [IsHausdorff (Ideal.span {(p : A)}) A] {y z : A}
    (h : ∀ m : ℕ, (p : A) ^ m ∣ y - z) : y = z :=
  sub_eq_zero.1 (IsHausdorff.haus ‹_› _ fun m =>
    smodEq_of_dvd p m (by rw [sub_zero]; exact h m))

end Adic

section Ext

variable {σ R A : Type} [Fintype σ] [CommRing R] [CommRing A]

theorem eq_on_poly (φ ψ : MvPowerSeries σ R →+* A) (hC : ∀ c, φ (C c) = ψ (C c))
    (hX : ∀ i, φ (X i) = ψ (X i)) (P : MvPolynomial σ R) : φ P = ψ P := by
  induction P using MvPolynomial.induction_on with
  | C c => rw [MvPolynomial.coe_C, hC]
  | add P Q hP hQ => rw [MvPolynomial.coe_add, map_add, map_add, hP, hQ]
  | mul_X P i hP => rw [MvPolynomial.coe_mul, map_mul, map_mul, hP, MvPolynomial.coe_X, hX]

theorem ext_of_cont (p : ℕ) [IsHausdorff (Ideal.span {(p : A)}) A] (φ ψ : MvPowerSeries σ R →+* A)
    (hC : ∀ c, φ (C c) = ψ (C c)) (hX : ∀ i, φ (X i) = ψ (X i))
    (hφ : ∀ m : ℕ, ∃ N : ℕ, ∀ f, (∀ α : σ →₀ ℕ, α.degree < N → coeff α f = 0) → (p : A) ^ m ∣ φ f)
    (hψ : ∀ m : ℕ, ∃ N : ℕ, ∀ f, (∀ α : σ →₀ ℕ, α.degree < N → coeff α f = 0) → (p : A) ^ m ∣ ψ f)
    (f : MvPowerSeries σ R) : φ f = ψ f := by
  classical
  refine eq_of_forall_dvd p fun m => ?_
  obtain ⟨N₁, h₁⟩ := hφ m
  obtain ⟨N₂, h₂⟩ := hψ m
  have hP := eq_on_poly φ ψ hC hX (trunc' R (Finsupp.equivFunOnFinite.symm fun _ : σ => N₁ + N₂) f)
  set P : MvPowerSeries σ R := ↑(trunc' R (Finsupp.equivFunOnFinite.symm fun _ : σ => N₁ + N₂) f) with hPdef
  have hg : ∀ α : σ →₀ ℕ, α.degree < N₁ + N₂ → coeff α (f - P) = 0 := by
    intro α hα
    have hle : α ≤ Finsupp.equivFunOnFinite.symm fun _ : σ => N₁ + N₂ := Finsupp.le_def.2 fun i => by
      have := Finsupp.le_degree i α
      show α i ≤ N₁ + N₂
      omega
    rw [map_sub, hPdef, MvPolynomial.coeff_coe, coeff_trunc', if_pos hle, sub_self]
  have e : φ f - ψ f = φ (f - P) - ψ (f - P) := by
    rw [map_sub, map_sub, hP]; ring
  rw [e]
  exact dvd_sub (h₁ _ fun α hα => hg α (by omega)) (h₂ _ fun α hα => hg α (by omega))

end Ext

section Exist

variable {σ R A : Type} [Fintype σ] [CommRing R] [CommRing A] [Algebra R A]

theorem dvd_aeval_of_coeff (p : ℕ) (x : σ → A) (S : ℕ) (hS : ∀ i, (p : A) ∣ x i ^ S) (m : ℕ)
    (P : MvPolynomial σ R) (hP : ∀ α : σ →₀ ℕ, (∀ i, α i ≤ m * S) → P.coeff α = 0) :
    (p : A) ^ m ∣ MvPolynomial.aeval x P := by
  classical
  conv_rhs => rw [P.as_sum]
  rw [map_sum]
  refine Finset.dvd_sum fun α hα => ?_
  rw [MvPolynomial.aeval_monomial]
  obtain ⟨i, hi⟩ : ∃ i, m * S < α i := by
    by_contra h
    push_neg at h
    exact (MvPolynomial.mem_support_iff.1 hα) (hP α h)
  refine Dvd.dvd.mul_left ?_ _
  have hmem : i ∈ α.support := Finsupp.mem_support_iff.2 (by omega)
  refine Dvd.dvd.trans ?_ (Finset.dvd_prod_of_mem (fun j => x j ^ α j) hmem)
  calc (p : A) ^ m ∣ (x i ^ S) ^ m := pow_dvd_pow_of_dvd (hS i) m
    _ = x i ^ (m * S) := by rw [← pow_mul, mul_comm]
    _ ∣ x i ^ α i := pow_dvd_pow _ hi.le

theorem exists_isEval (p : ℕ) [IsAdicComplete (Ideal.span {(p : A)}) A] (x : σ → A)
    (hx : ∀ i, ∃ N : ℕ, (p : A) ∣ x i ^ N) :
    ∃ E : MvPowerSeries σ R →ₐ[R] A, IsEval p x E := by
  classical
  choose N hN using hx
  set S := ∑ i, N i
  have hS : ∀ i, (p : A) ∣ x i ^ S := fun i => (hN i).trans (pow_dvd_pow _
    (Finset.single_le_sum (fun j _ => Nat.zero_le (N j)) (Finset.mem_univ i)))
  let bx : ℕ → σ →₀ ℕ := fun K => Finsupp.equivFunOnFinite.symm fun _ => K
  have hbx : ∀ K (α : σ →₀ ℕ), α ≤ bx K ↔ ∀ i, α i ≤ K := fun K α => Finsupp.le_def
  let s : ℕ → MvPowerSeries σ R → A := fun m f => MvPolynomial.aeval x (trunc' R (bx (m * S)) f)
  have key := dvd_aeval_of_coeff (R := R) p x S hS
  have hcau : ∀ f m n, m ≤ n → (p : A) ^ m ∣ s m f - s n f := by
    intro f m n hmn
    simp only [s, ← map_sub]
    refine key m _ fun α hα => ?_
    have h1 : α ≤ bx (m * S) := (hbx _ _).2 hα
    have h2 : α ≤ bx (n * S) := (hbx _ _).2 fun i => (hα i).trans (Nat.mul_le_mul_right _ hmn)
    rw [MvPolynomial.coeff_sub, coeff_trunc', coeff_trunc', if_pos h1, if_pos h2, sub_self]
  have hL : ∀ f, ∃ L : A, ∀ m, (p : A) ^ m ∣ s m f - L := by
    intro f
    obtain ⟨L, hL⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete (Ideal.span {(p : A)}) A)
      (f := fun m => s m f) (fun {m n} hmn => smodEq_of_dvd p m (hcau f m n hmn))
    exact ⟨L, fun m => dvd_of_smodEq p m (hL m)⟩
  choose L hL using hL
  have huniq : ∀ f y, (∀ m, (p : A) ^ m ∣ s m f - y) → L f = y := fun f y h =>
    eq_of_forall_dvd p fun m => by
      have := dvd_sub (h m) (hL f m)
      rwa [sub_sub_sub_cancel_left] at this
  have hpoly : ∀ P : MvPolynomial σ R, L P = MvPolynomial.aeval x P := by
    intro P
    refine huniq _ _ fun m => ?_
    simp only [s, ← map_sub]
    refine key m _ fun α hα => ?_
    rw [MvPolynomial.coeff_sub, coeff_trunc', if_pos ((hbx _ _).2 hα), MvPolynomial.coeff_coe,
      sub_self]
  have hadd : ∀ f g, L (f + g) = L f + L g := by
    intro f g
    refine huniq _ _ fun m => ?_
    have e : s m (f + g) - (L f + L g) = (s m f - L f) + (s m g - L g) := by
      simp only [s, map_add]; ring
    rw [e]
    exact dvd_add (hL f m) (hL g m)
  have hmul : ∀ f g, L (f * g) = L f * L g := by
    intro f g
    refine huniq _ _ fun m => ?_
    have e : s m (f * g) - L f * L g = (s m (f * g) - s m f * s m g) + (s m f - L f) * s m g +
        L f * (s m g - L g) := by ring
    have h1 : (p : A) ^ m ∣ s m (f * g) - s m f * s m g := by
      simp only [s, ← map_mul, ← map_sub]
      refine key m _ fun α hα => ?_
      have h1 : α ≤ bx (m * S) := (hbx _ _).2 hα
      rw [MvPolynomial.coeff_sub, coeff_trunc', if_pos h1,
        coeff_trunc'_mul_trunc'_eq_coeff_mul _ _ _ h1, sub_self]
    rw [e]
    exact dvd_add (dvd_add h1 (Dvd.dvd.mul_right (hL f m) _)) (Dvd.dvd.mul_left (hL g m) _)
  let E : MvPowerSeries σ R →ₐ[R] A :=
    { toFun := L
      map_one' := by rw [← MvPolynomial.coe_one, hpoly, map_one]
      map_mul' := hmul
      map_zero' := by rw [← MvPolynomial.coe_zero, hpoly, map_zero]
      map_add' := hadd
      commutes' := fun c => by
        rw [← c_eq_algebraMap, ← MvPolynomial.coe_C, hpoly, MvPolynomial.aeval_C] }
  refine ⟨E, fun i => ?_, fun m => ⟨Fintype.card σ * (m * S) + 1, fun f hf => ?_⟩⟩
  · show L (X i) = x i
    rw [← MvPolynomial.coe_X, hpoly, MvPolynomial.aeval_X]
  · show (p : A) ^ m ∣ L f
    have h0 : trunc' R (bx (m * S)) f = 0 := by
      ext α
      rw [coeff_trunc', MvPolynomial.coeff_zero]
      split_ifs with h
      · refine hf α ?_
        rw [Finsupp.degree_eq_sum]
        have := Finset.sum_le_sum (s := Finset.univ) fun i _ => (hbx _ _).1 h i
        simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at this
        omega
      · rfl
    have := hL f m
    simp only [s, h0, map_zero, zero_sub, dvd_neg] at this
    exact this

end Exist

theorem eval_unique {σ R A : Type} [Fintype σ] [CommRing R] [CommRing A] [Algebra R A] (p : ℕ)
    [IsHausdorff (Ideal.span {(p : A)}) A] (x : σ → A) (E₁ E₂ : MvPowerSeries σ R →ₐ[R] A)
    (h₁ : IsEval p x E₁) (h₂ : IsEval p x E₂) : E₁ = E₂ := by
  ext f
  exact ext_of_cont p E₁.toRingHom E₂.toRingHom
    (fun c => by
      show E₁ (C c) = E₂ (C c)
      rw [c_eq_algebraMap, AlgHom.commutes, AlgHom.commutes])
    (fun i => by
      show E₁ (X i) = E₂ (X i)
      rw [h₁.1, h₂.1])
    h₁.2 h₂.2 f

theorem continuous_eval : ∀ (p : ℕ) (R A σ : Type) [CommRing R] [CommRing A] [Algebra R A] [Fintype σ] [IsAdicComplete (Ideal.span {(p : A)}) A] (x : σ → A), (∀ i, ∃ N : ℕ, (p : A) ∣ x i ^ N) → (∃! E : MvPowerSeries σ R →ₐ[R] A, IsEval p x E) ∧ ∀ E : MvPowerSeries σ R →ₐ[R] A, IsEval p x E → (∀ (τ : Type) [Fintype τ] (u : τ → MvPowerSeries σ R) (E' : MvPowerSeries τ R →ₐ[R] A), (∀ j, constantCoeff (u j) = 0) → IsEval p (fun j => E (u j)) E' → ∀ f, E (subst u f) = E' f) ∧ (∀ f, constantCoeff f = 0 → ∃ N : ℕ, (p : A) ∣ E f ^ N) ∧ ∀ (R' A' : Type) [CommRing R'] [CommRing A'] [Algebra R' A'] [IsHausdorff (Ideal.span {(p : A')}) A'] (r : R →+* R') (g : A →+* A') (E' : MvPowerSeries σ R' →ₐ[R'] A'), (∀ c, g (algebraMap R A c) = algebraMap R' A' (r c)) → IsEval p (fun i => g (x i)) E' → ∀ f, g (E f) = E' (map r f) := by
  intro p R A σ _ _ _ _ _ x hx
  refine ⟨?_, fun E hE => ⟨?_, ?_, ?_⟩⟩
  · obtain ⟨E, hE⟩ := exists_isEval (R := R) p x hx
    exact ⟨E, hE, fun E' hE' => eval_unique p x E' E hE' hE⟩
  · intro τ _ u E' hu hE' f
    have hs : HasSubst u := hasSubst_of_constantCoeff_zero hu
    rw [← coe_substAlgHom hs]
    exact ext_of_cont p ((E.comp (substAlgHom hs)).toRingHom) E'.toRingHom
      (fun c => by
        show E (substAlgHom hs (C c)) = E' (C c)
        rw [c_eq_algebraMap, AlgHom.commutes, AlgHom.commutes, AlgHom.commutes])
      (fun j => by
        show E (substAlgHom hs (X j)) = E' (X j)
        rw [substAlgHom_X, hE'.1])
      (fun m => by
        obtain ⟨N, hN⟩ := hE.2 m
        refine ⟨N, fun f hf => ?_⟩
        show (p : A) ^ m ∣ E (substAlgHom hs f)
        rw [coe_substAlgHom]
        refine hN _ fun α hα => coeff_of_lt_order ?_
        have h1 : (1 : ℕ∞) ≤ ⨅ j, (u j).order :=
          le_iInf fun j => one_le_order_iff_constCoeff_eq_zero.2 (hu j)
        have h2 : (N : ℕ∞) ≤ f.order := nat_le_order hf
        calc (α.degree : ℕ∞) < N := by exact_mod_cast hα
          _ = 1 * N := (one_mul _).symm
          _ ≤ (⨅ j, (u j).order) * f.order := mul_le_mul' h1 h2
          _ ≤ (subst u f).order := le_order_subst hs f)
      hE'.2 f
  · intro f hf
    obtain ⟨N, hN⟩ := hE.2 1
    refine ⟨N, ?_⟩
    rw [← map_pow]
    have := hN (f ^ N) fun α hα => coeff_of_lt_order
      ((by exact_mod_cast hα : (α.degree : ℕ∞) < N).trans_le
        (le_order_pow_of_constantCoeff_eq_zero N hf))
    rwa [pow_one] at this
  · intro R' A' _ _ _ _ r g E' hg hE' f
    exact ext_of_cont p (g.comp E.toRingHom) (E'.toRingHom.comp (map r))
      (fun c => by
        show g (E (C c)) = E' (map r (C c))
        rw [map_C, c_eq_algebraMap, c_eq_algebraMap, AlgHom.commutes, AlgHom.commutes, hg])
      (fun i => by
        show g (E (X i)) = E' (map r (X i))
        rw [map_X, hE.1, hE'.1])
      (fun m => by
        obtain ⟨N, hN⟩ := hE.2 m
        exact ⟨N, fun f hf => by
          show (p : A') ^ m ∣ g (E f)
          have := map_dvd g (hN f hf)
          rwa [map_pow, map_natCast] at this⟩)
      (fun m => by
        obtain ⟨N, hN⟩ := hE'.2 m
        exact ⟨N, fun f hf => hN _ fun α hα => by rw [coeff_map, hf α hα, map_zero]⟩)
      f

end GlobalTheory.CEval
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousMvPowerSeriesAlgHomExt
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.PadicMvPowerSeriesExt

theorem eq_zero_of_forall_pow_dvd (p : ℕ) (O : Type) [CommRing O]
    [IsHausdorff (Ideal.span {(p : O)}) O] (A : Type) [CommRing A] [Algebra O A]
    [Module.Projective O A] (x : A) (hx : ∀ m : ℕ, (p : A) ^ m ∣ x) : x = 0 := by
  obtain ⟨s, hs⟩ := Module.projective_def'.1 (inferInstance : Module.Projective O A)
  have h0 : s x = 0 := by
    ext a
    refine IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {(p : O)}) O) _ fun n => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
    obtain ⟨y, hy⟩ := hx n
    have hxy : x = ((p : O) ^ n) • y := by
      rw [Algebra.smul_def, map_pow, map_natCast, hy]
    rw [hxy, map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact dvd_mul_right _ _
  have h1 := LinearMap.congr_fun hs x
  rw [LinearMap.comp_apply, h0, map_zero, LinearMap.id_apply] at h1
  exact h1.symm

theorem algHom_ext : ∀ (p : ℕ) (O : Type) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O] (σ : Type) [Finite σ] (A : Type) [CommRing A] [Algebra O A] [Module.Finite O A] [Module.Projective O A] (F F' : MvPowerSeries σ O →ₐ[O] A), (∀ i, F (X i) = F' (X i)) → (∀ m : ℕ, ∃ N : ℕ, ∀ f, (∀ α : σ →₀ ℕ, α.degree < N → coeff α f = 0) → (p : A) ^ m ∣ F f) → (∀ m : ℕ, ∃ N : ℕ, ∀ f, (∀ α : σ →₀ ℕ, α.degree < N → coeff α f = 0) → (p : A) ^ m ∣ F' f) → F = F' := by
  classical
  intro p O _ _ σ _ A _ _ _ _ F F' hX hF hF'
  apply AlgHom.ext
  intro f
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_pow_dvd p O A _ fun m => ?_
  obtain ⟨N₁, hN₁⟩ := hF m
  obtain ⟨N₂, hN₂⟩ := hF' m
  set g := MvPowerSeries.trunc' O (Finsupp.equivFunOnFinite.symm fun _ : σ => max N₁ N₂) f with hg
  have hpoly : F.comp (MvPolynomial.coeToMvPowerSeries.algHom O) =
      F'.comp (MvPolynomial.coeToMvPowerSeries.algHom O) :=
    MvPolynomial.algHom_ext fun i => by simpa using hX i
  have hg' : F (g : MvPowerSeries σ O) = F' (g : MvPowerSeries σ O) := by
    simpa using DFunLike.congr_fun hpoly g
  have hlow : ∀ α : σ →₀ ℕ, α.degree < max N₁ N₂ →
      MvPowerSeries.coeff α (f - (g : MvPowerSeries σ O)) = 0 := by
    intro α hα
    rw [map_sub, MvPolynomial.coeff_coe, hg, MvPowerSeries.coeff_trunc', if_pos, sub_self]
    intro i
    exact (Finsupp.le_degree i α).trans (by simpa using hα.le)
  have hdiff : F f - F' f = F (f - (g : MvPowerSeries σ O)) - F' (f - (g : MvPowerSeries σ O)) := by
    rw [map_sub, map_sub, hg']
    ring
  rw [hdiff]
  exact dvd_sub (hN₁ _ fun α h => hlow α (lt_of_lt_of_le h (le_max_left _ _)))
    (hN₂ _ fun α h => hlow α (lt_of_lt_of_le h (le_max_right _ _)))

end GlobalTheory.PadicMvPowerSeriesExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PderivSubstChainRule
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace GlobalTheory.PSChain

open scoped MvPowerSeries.WithPiTopology in

theorem continuous_pderiv_discrete {σ R : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
    (i : σ) : Continuous (fun f : MvPowerSeries σ R => pderiv R i f) := by
  classical
  apply continuous_pi
  intro n
  have e : (fun f : MvPowerSeries σ R => (pderiv R i f) n) =
      (fun r : R => r * (n i + 1)) ∘ (fun f : MvPowerSeries σ R => coeff (n + Finsupp.single i 1) f) := by
    funext f
    exact coeff_pderiv f n
  rw [e]
  exact continuous_of_discreteTopology.comp (MvPowerSeries.WithPiTopology.continuous_coeff R _)

open scoped MvPowerSeries.WithPiTopology in

theorem pderiv_subst_chain {R σ τ : Type} [CommRing R] [Fintype σ] [Fintype τ]
    (a : σ → MvPowerSeries τ R) (ha0 : ∀ s, constantCoeff (a s) = 0) (f : MvPowerSeries σ R) (k : τ) :
    pderiv R k (subst a f) = ∑ j, subst a (pderiv R j f) * pderiv R k (a j) := by
  classical
  have ha : HasSubst a := hasSubst_of_constantCoeff_zero ha0
  let _ : UniformSpace R := ⊥
  have _ : DiscreteUniformity R := ⟨rfl⟩
  have hcs : Continuous (subst a : MvPowerSeries σ R → MvPowerSeries τ R) := continuous_subst ha
  have hs0 : subst a (0 : MvPowerSeries σ R) = 0 := by rw [← coe_substAlgHom ha, map_zero]
  have hs1 : subst a (1 : MvPowerSeries σ R) = 1 := by rw [← coe_substAlgHom ha, map_one]
  let D1 : MvPowerSeries σ R → MvPowerSeries τ R := fun g => pderiv R k (subst a g)
  let D2 : MvPowerSeries σ R → MvPowerSeries τ R := fun g =>
    ∑ s, subst a (pderiv R s g) * pderiv R k (a s)
  have c1 : Continuous D1 := (continuous_pderiv_discrete _).comp hcs
  have c2 : Continuous D2 :=
    continuous_finsetSum _ fun i _ => (hcs.comp (continuous_pderiv_discrete _)).mul continuous_const
  have hpoly : ∀ p : MvPolynomial σ R, D1 (p : MvPowerSeries σ R) = D2 (p : MvPowerSeries σ R) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C r => simp [D1, D2, subst_C, hs0]
    | add p q hp hq =>
      simp only [D1, D2, MvPolynomial.coe_add, subst_add ha, map_add] at hp hq ⊢
      rw [hp, hq, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    | mul_X p s2 hp =>
      simp only [D1, D2, MvPolynomial.coe_mul, MvPolynomial.coe_X] at hp ⊢
      rw [subst_mul ha, subst_X ha, Derivation.leibniz, smul_eq_mul, smul_eq_mul, hp]
      have hX : ∀ i : σ, pderiv R i (X s2 : MvPowerSeries σ R) = if i = s2 then 1 else 0 := by
        intro i
        by_cases h : i = s2
        · subst h; simp
        · rw [if_neg h, pderiv_X_of_ne (Ne.symm h)]
      have hterm : ∀ i : σ, subst a (pderiv R i ((p : MvPowerSeries σ R) * X s2)) * pderiv R k (a i) =
          (if i = s2 then subst a (p : MvPowerSeries σ R) * pderiv R k (a i) else 0) +
            a s2 * (subst a (pderiv R i (p : MvPowerSeries σ R)) * pderiv R k (a i)) := by
        intro i
        rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, hX i, subst_add ha, subst_mul ha,
          subst_mul ha, subst_X ha]
        split_ifs with h
        · rw [hs1]; ring
        · rw [hs0]; ring
      rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib, Finset.sum_ite_eq',
        if_pos (Finset.mem_univ _), ← Finset.mul_sum]
  have := (MvPowerSeries.WithPiTopology.denseRange_toMvPowerSeries).equalizer c1 c2 (funext hpoly)
  exact congrFun this f

end GlobalTheory.PSChain
end
end

