import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsHorizontalTwist
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0011
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwLineSmoothConjInvariantGlue
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Tw.Lines

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem conj_contDiff {T : Type} [Fintype T] :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : T → ℂ => fun q => starRingEnd ℂ (z q)) :=
  contDiff_pi.2 fun q => Complex.conjCLE.contDiff.comp (contDiff_apply ℝ ℂ q)

theorem oldPart_contDiff :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (basePart₂ : ((Σ o, Tb ι o) → ℂ) → (Σ k, ι k) → ℂ) :=
  contDiff_pi.2 fun _ => contDiff_apply ℝ ℂ _

theorem chi_contDiffOn (p : ℕ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (chi (ι := ι) p) {u | ∀ o, ∃ i, u ⟨o, i⟩ ≠ 0} := by
  have hx : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : (Σ o, Tb ι o) → ℂ => u ⟨none, (0 : Fin 2)⟩) := contDiff_apply ℝ ℂ _
  have hy : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : (Σ o, Tb ι o) → ℂ => u ⟨none, (1 : Fin 2)⟩) := contDiff_apply ℝ ℂ _
  have hnum : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : (Σ o, Tb ι o) → ℂ =>
      (u ⟨none, (0 : Fin 2)⟩ * (starRingEnd ℂ) (u ⟨none, (1 : Fin 2)⟩)).im) :=
    Complex.imCLM.contDiff.comp (hx.mul (Complex.conjCLE.contDiff.comp hy))
  have hden : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : (Σ o, Tb ι o) → ℂ =>
      ‖u ⟨none, (0 : Fin 2)⟩‖ ^ 2 + ‖u ⟨none, (1 : Fin 2)⟩‖ ^ 2) :=
    (hx.norm_sq ℝ).add (hy.norm_sq ℝ)
  have hq : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : (Σ o, Tb ι o) → ℂ =>
      (u ⟨none, (0 : Fin 2)⟩ * (starRingEnd ℂ) (u ⟨none, (1 : Fin 2)⟩)).im /
        (‖u ⟨none, (0 : Fin 2)⟩‖ ^ 2 + ‖u ⟨none, (1 : Fin 2)⟩‖ ^ 2))
      {u | ∀ o, ∃ i, u ⟨o, i⟩ ≠ 0} := by
    refine hnum.contDiffOn.div hden.contDiffOn fun u hu => ?_
    have h0 : 0 ≤ ‖u ⟨none, (0 : Fin 2)⟩‖ ^ 2 := by positivity
    have h1 : 0 ≤ ‖u ⟨none, (1 : Fin 2)⟩‖ ^ 2 := by positivity
    have key : ∀ j : Fin 2, u ⟨none, j⟩ ≠ 0 →
        ‖u ⟨none, (0 : Fin 2)⟩‖ ^ 2 + ‖u ⟨none, (1 : Fin 2)⟩‖ ^ 2 ≠ 0 := by
      intro j hj
      have hpos : 0 < ‖u ⟨none, j⟩‖ ^ 2 := by positivity
      have hj2 : j = 0 ∨ j = 1 := by fin_cases j <;> simp
      rcases hj2 with rfl | rfl <;> exact ne_of_gt (by linarith)
    obtain ⟨i, hi⟩ := hu none
    exact key i hi
  exact (contDiffOn_const.add (contDiffOn_const.mul hq))

theorem chi_conj (p : ℕ) (u : (Σ o, Tb ι o) → ℂ) :
    chi p (fun q => starRingEnd ℂ (u q)) = 1 - chi p u := by
  have him : ((starRingEnd ℂ) (u ⟨none, (0 : Fin 2)⟩) *
      (starRingEnd ℂ) ((starRingEnd ℂ) (u ⟨none, (1 : Fin 2)⟩))).im =
      -(u ⟨none, (0 : Fin 2)⟩ * (starRingEnd ℂ) (u ⟨none, (1 : Fin 2)⟩)).im := by
    rw [Complex.conj_conj, ← Complex.conj_im, map_mul, Complex.conj_conj]
  simp only [chi, RCLike.norm_conj, him]
  ring

theorem chi_vPlus (p : ℕ) (hp : p ≠ 0) (z : (Σ k, ι k) → ℂ) : chi p (glue z (vPlus p)) = 1 := by
  have hs : 0 < Real.sqrt p := Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero hp)
  have hsq : Real.sqrt p ^ 2 = p := Real.sq_sqrt (Nat.cast_nonneg p)
  have e0 : glue z (vPlus p) ⟨none, (0 : Fin 2)⟩ = cRoot p := rfl
  have e1 : glue z (vPlus p) ⟨none, (1 : Fin 2)⟩ = 1 := rfl
  have hn : ‖cRoot p‖ ^ 2 = p := by
    rw [cRoot, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs, hsq]
  have him : (cRoot p).im = Real.sqrt p := by simp [cRoot]
  rw [chi, e0, e1]
  simp only [map_one, mul_one, norm_one, one_pow, hn, him]
  have : ((p : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

theorem chi_vMinus (p : ℕ) (hp : p ≠ 0) (z : (Σ k, ι k) → ℂ) : chi p (glue z (vMinus p)) = 0 := by
  have hs : 0 < Real.sqrt p := Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero hp)
  have hsq : Real.sqrt p ^ 2 = p := Real.sq_sqrt (Nat.cast_nonneg p)
  have e0 : glue z (vMinus p) ⟨none, (0 : Fin 2)⟩ = -cRoot p := rfl
  have e1 : glue z (vMinus p) ⟨none, (1 : Fin 2)⟩ = 1 := rfl
  have hn : ‖cRoot p‖ ^ 2 = p := by
    rw [cRoot, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs, hsq]
  have him : (cRoot p).im = Real.sqrt p := by simp [cRoot]
  rw [chi, e0, e1]
  simp only [map_one, mul_one, norm_one, one_pow, norm_neg, hn, Complex.neg_im, him]
  have : ((p : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

theorem conj_ne {T : Type} {B : T → Type} {u : (Σ o, B o) → ℂ} {o : T} (h : ∃ i, u ⟨o, i⟩ ≠ 0) :
    ∃ i, (fun q => starRingEnd ℂ (u q)) ⟨o, i⟩ ≠ 0 := by
  obtain ⟨i, hi⟩ := h
  exact ⟨i, by simpa using hi⟩

theorem conjLine_smooth (A : HermLine ι) (hA : IsSmoothHerm A) : IsSmoothHerm (conjLine A) := by
  have hA' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A.h
      {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := hA
  exact hA'.comp (s := {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0})
    (conj_contDiff (T := Σ k, ι k)).contDiffOn fun z hz k => conj_ne (hz k)

theorem twLine_smooth (p : ℕ) (A : HermLine ι) (hA : IsSmoothHerm A) :
    IsSmoothHerm (twLine p A) := by
  have hA' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A.h
      {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := hA
  have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : (Σ o, Tb ι o) → ℂ => A.h (basePart₂ u)) {u | ∀ o, ∃ i, u ⟨o, i⟩ ≠ 0} :=
    ContDiffOn.comp (t := {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}) hA' oldPart_contDiff.contDiffOn
      fun _ hu k => oldPart_ne hu k
  have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : (Σ o, Tb ι o) → ℂ => A.h fun q => starRingEnd ℂ (basePart₂ u q))
      {u | ∀ o, ∃ i, u ⟨o, i⟩ ≠ 0} :=
    ContDiffOn.comp (t := {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}) hA'
      (conj_contDiff.comp oldPart_contDiff).contDiffOn
      fun _ hu k => conj_ne (oldPart_ne hu k)
  have l1 := h1.log fun u hu => (A.pos _ (oldPart_ne hu)).ne'
  have l2 := h2.log fun u hu => (A.pos _ fun k => conj_ne (oldPart_ne hu k)).ne'
  have hc := chi_contDiffOn (ι := ι) p
  have hE := (((hc.mul l1).add (((contDiffOn_const (c := (1 : ℝ))).sub hc).mul l2))).exp
  refine ContDiffOn.congr hE fun u hu => ?_
  change twH p A u = _
  have hu' : ∀ o, ∃ i, u ⟨o, i⟩ ≠ 0 := hu
  rw [twH, if_pos hu']

theorem twLine_conj (p : ℕ) (A : HermLine ι) : IsConjInvariantH (twLine p A) := by
  intro u
  change twH p A (fun q => starRingEnd ℂ (u q)) = twH p A u
  have hsame : (∀ o, ∃ i, (fun q => starRingEnd ℂ (u q)) ⟨o, i⟩ ≠ 0) ↔ ∀ o, ∃ i, u ⟨o, i⟩ ≠ 0 :=
    forall_congr' fun o => exists_congr fun i => by simp
  by_cases hu : ∀ o, ∃ i, u ⟨o, i⟩ ≠ 0
  · rw [twH, twH, if_pos (hsame.mpr hu), if_pos hu, chi_conj]
    have e1 : basePart₂ (fun q => starRingEnd ℂ (u q)) = fun q => starRingEnd ℂ (basePart₂ u q) := rfl
    have e2 : (fun q => starRingEnd ℂ (basePart₂ (fun q => starRingEnd ℂ (u q)) q)) = basePart₂ u := by
      funext q; simp [basePart₂]
    rw [e2, e1]
    congr 1
    ring
  · rw [twH, twH, if_neg (fun h => hu (hsame.mp h)), if_neg hu]

theorem glue_block {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) {v : Fin 2 → ℂ}
    (hv : v 1 ≠ 0) : ∀ o, ∃ i, glue z v ⟨o, i⟩ ≠ 0 := by
  intro o
  cases o with
  | none => exact ⟨(1 : Fin 2), hv⟩
  | some k => exact hz k

theorem twLine_vPlus (p : ℕ) (hp : p ≠ 0) (A : HermLine ι) (z : (Σ k, ι k) → ℂ)
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : (twLine p A).h (glue z (vPlus p)) = A.h z := by
  change twH p A _ = _
  have hv : vPlus p 1 ≠ 0 := by simp [vPlus]
  have ho : basePart₂ (glue z (vPlus p)) = z := rfl
  rw [twH, if_pos (glue_block hz hv), chi_vPlus p hp, ho]
  simp only [one_mul, sub_self, zero_mul, add_zero]
  exact Real.exp_log (A.pos z hz)

theorem twLine_vMinus (p : ℕ) (hp : p ≠ 0) (A : HermLine ι) (z : (Σ k, ι k) → ℂ)
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : (twLine p A).h (glue z (vMinus p)) = (conjLine A).h z := by
  change twH p A _ = A.h fun q => starRingEnd ℂ (z q)
  have hv : vMinus p 1 ≠ 0 := by simp [vMinus]
  have ho : basePart₂ (glue z (vMinus p)) = z := rfl
  rw [twH, if_pos (glue_block hz hv), chi_vMinus p hp, ho]
  simp only [zero_mul, sub_zero, one_mul, zero_add]
  exact Real.exp_log (A.pos _ fun k => conj_ne (hz k))

theorem twLine_main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ) (A : HermLine ι), p ≠ 0 → (IsSmoothHerm A → IsSmoothHerm (twLine p A)) ∧ (IsSmoothHerm A → IsSmoothHerm (conjLine A)) ∧ IsConjInvariantH (twLine p A) ∧ (∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → (twLine p A).h (glue z (vPlus p)) = A.h z) ∧ (∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → (twLine p A).h (glue z (vMinus p)) = (conjLine A).h z) :=
  fun _ _ _ _ p A hp => ⟨twLine_smooth p A, conjLine_smooth A, twLine_conj p A,
    twLine_vPlus p hp A, twLine_vMinus p hp A⟩

end GlobalTheory.CompanionTheory.Ar.Tw.Lines
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistIsPrime
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw

namespace GlobalTheory.CompanionTheory.Ar.Tw

theorem exists_root_field {D : Type} [CommRing D] [IsDomain D] (p : ℕ)
    (h : ∀ a b : D, a ^ 2 + (p : D) * b ^ 2 = 0 → b = 0) :
    ∃ (E : Type) (_ : Field E) (i : D →+* E) (s : E), s ^ 2 = -(p : E) ∧
      ∀ u v : D, i u + i v * s = 0 → u = 0 ∧ v = 0 := by
  classical
  let F := FractionRing D
  let g : Polynomial F := Polynomial.X ^ 2 + Polynomial.C (p : F)
  have hmonic : g.Monic := Polynomial.monic_X_pow_add_C _ (by norm_num)
  have hdeg : g.natDegree = 2 := Polynomial.natDegree_X_pow_add_C
  have hinjF : Function.Injective (algebraMap D F) := IsFractionRing.injective D F
  have hnr : ∀ r : F, r ^ 2 + (p : F) ≠ 0 := by
    intro r hr
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := D) r
    have hb0 : algebraMap D F b ≠ 0 := by
      intro h0
      exact nonZeroDivisors.ne_zero hb (hinjF (by simpa using h0))
    have h1 : algebraMap D F (a ^ 2 + (p : D) * b ^ 2) = 0 := by
      simp only [map_add, map_mul, map_pow, map_natCast]
      have e : algebraMap D F a ^ 2 + (p : F) * algebraMap D F b ^ 2 =
          ((algebraMap D F a / algebraMap D F b) ^ 2 + (p : F)) * algebraMap D F b ^ 2 := by
        rw [div_pow, add_mul, div_mul_cancel₀ _ (pow_ne_zero 2 hb0)]
      rw [e, hr, zero_mul]
    have h2 : a ^ 2 + (p : D) * b ^ 2 = 0 := hinjF (by simpa using h1)
    exact hb0 (by rw [h a b h2, map_zero])
  have hirr : Irreducible g := by
    rw [hmonic.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)]
    refine Multiset.eq_zero_of_forall_notMem fun r hr => ?_
    have := (Polynomial.mem_roots'.mp hr).2
    simp [g, Polynomial.IsRoot] at this
    exact hnr r this
  haveI : Fact (Irreducible g) := ⟨hirr⟩
  refine ⟨AdjoinRoot g, inferInstance, (AdjoinRoot.of g).comp (algebraMap D F), AdjoinRoot.root g, ?_, ?_⟩
  · have h0 : AdjoinRoot.mk g (Polynomial.X ^ 2 + Polynomial.C (p : F)) = 0 := AdjoinRoot.mk_self
    rw [map_add, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, map_natCast] at h0
    linear_combination h0
  · intro u v huv
    have h1 : AdjoinRoot.mk g (Polynomial.C (algebraMap D F u) +
        Polynomial.C (algebraMap D F v) * Polynomial.X) = 0 := by
      simpa using huv
    rw [AdjoinRoot.mk_eq_zero] at h1
    have h2 := Polynomial.eq_zero_of_dvd_of_degree_lt h1 (by
      rw [Polynomial.degree_eq_natDegree hmonic.ne_zero, hdeg]
      compute_degree
      exact_mod_cast (by norm_num : 1 < 2))
    have hu := congrArg (fun t => Polynomial.coeff t 0) h2
    have hv := congrArg (fun t => Polynomial.coeff t 1) h2
    simp at hu hv
    exact ⟨hu, hv⟩

theorem twist_isPrime (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ)
    (W : Ideal (MRing ι)) (hW : W.IsPrime) (hN : NoRoot p W) : (twist p W).IsPrime := by
  classical
  haveI : IsDomain (MRing ι ⧸ W) := Ideal.Quotient.isDomain W
  have hD : ∀ a b : MRing ι ⧸ W, a ^ 2 + (p : MRing ι ⧸ W) * b ^ 2 = 0 → b = 0 := by
    intro a b h
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [Ideal.Quotient.eq_zero_iff_mem]
    apply hN a
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simpa using h
  obtain ⟨E, _, i, s, hs, hind⟩ := exists_root_field p hD
  let φ : MRing (Tb ι) →+* Polynomial E :=
    (aeval (fun q : Σ o, Tb ι o => match q with
      | ⟨none, j⟩ => if j = (0 : Fin 2) then Polynomial.C s * Polynomial.X else Polynomial.X
      | ⟨some k, l⟩ => Polynomial.C (i (Ideal.Quotient.mk W (X ⟨k, l⟩)))) :
        MRing (Tb ι) →ₐ[ℤ] Polynomial E).toRingHom
  have hinc : ∀ f : MRing ι, φ (inc f) = Polynomial.C (i (Ideal.Quotient.mk W f)) := by
    intro f
    have : (φ.comp inc) = (Polynomial.C.comp (i.comp (Ideal.Quotient.mk W))) := by
      apply MvPolynomial.ringHom_ext
      · intro r; simp [φ, inc]
      · intro l; simp [φ, inc, oldIdx]
    exact congrArg (fun g => g f) this
  have hx : φ xN = Polynomial.C s * Polynomial.X := by
    simp only [φ, xN, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
    exact if_pos rfl
  have hy : φ yN = Polynomial.X := by
    simp only [φ, yN, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
    exact if_neg (show ¬ ((1 : Fin 2) = 0) by decide)
  have hCp : φ (C (p : ℤ)) = (p : Polynomial E) := by
    simp [φ]
  have hle : twist p W ≤ RingHom.ker φ := by
    refine sup_le (Ideal.map_le_iff_le_comap.mpr fun f hf => ?_) ?_
    · rw [Ideal.mem_comap, RingHom.mem_ker, hinc, Ideal.Quotient.eq_zero_iff_mem.mpr hf]
      simp
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      show quad p ∈ RingHom.ker φ
      rw [RingHom.mem_ker]
      simp only [quad, map_add, map_mul, map_pow, hx, hy, hCp]
      have hs' : (Polynomial.C s) ^ 2 = -(p : Polynomial E) := by
        rw [← map_pow, hs]; simp
      linear_combination (Polynomial.X ^ 2 : Polynomial E) * hs'
  let φ' : (MRing (Tb ι) ⧸ twist p W) →+* Polynomial E :=
    Ideal.Quotient.lift _ φ (fun a ha => hle ha)
  let mk' := Ideal.Quotient.mk (twist p W)
  have hWle : ∀ a ∈ W, (mk'.comp inc) a = 0 := by
    intro a ha
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ha))
  let τ : (MRing ι ⧸ W) →+* (MRing (Tb ι) ⧸ twist p W) :=
    Ideal.Quotient.lift W (mk'.comp inc) hWle
  let σ : Polynomial (MRing ι ⧸ W) →+* (MRing (Tb ι) ⧸ twist p W) :=
    Polynomial.eval₂RingHom τ (mk' yN)
  have hσC : ∀ d, σ (Polynomial.C d) = τ d := fun d => by simp [σ]
  have hσX : σ Polynomial.X = mk' yN := by simp [σ]
  have hxx : mk' xN * mk' xN = σ (-(p : Polynomial (MRing ι ⧸ W)) * Polynomial.X ^ 2) := by
    have hq : mk' (quad p) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    simp only [quad, map_add, map_mul, map_pow] at hq
    have hc : mk' (C (p : ℤ)) = (p : MRing (Tb ι) ⧸ twist p W) := by simp [mk']
    rw [hc] at hq
    simp only [map_mul, map_neg, map_natCast, map_pow, hσX]
    linear_combination hq
  have hform : ∀ f : MRing (Tb ι), ∃ a b : Polynomial (MRing ι ⧸ W),
      mk' f = σ a + σ b * mk' xN := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C n =>
      refine ⟨(n : Polynomial (MRing ι ⧸ W)), 0, ?_⟩
      simp [mk']
    | add f g hf hg =>
      obtain ⟨a, b, h1⟩ := hf
      obtain ⟨a', b', h2⟩ := hg
      exact ⟨a + a', b + b', by rw [map_add, h1, h2, map_add, map_add]; ring⟩
    | mul_X f q hf =>
      obtain ⟨a, b, h1⟩ := hf
      rw [map_mul, h1]
      obtain ⟨o, l⟩ := q
      cases o with
      | none =>
        have aux : ∀ l : Fin 2, (X (⟨none, l⟩ : Σ o, Tb ι o) : MRing (Tb ι)) = xN ∨
            (X (⟨none, l⟩ : Σ o, Tb ι o) : MRing (Tb ι)) = yN := by
          intro l
          fin_cases l
          · exact Or.inl rfl
          · exact Or.inr rfl
        rcases aux l with hl | hl
        · rw [hl]
          refine ⟨b * (-(p : Polynomial (MRing ι ⧸ W)) * Polynomial.X ^ 2), a, ?_⟩
          rw [map_mul σ b, ← hxx]
          ring
        · rw [hl]
          refine ⟨a * Polynomial.X, b * Polynomial.X, ?_⟩
          rw [map_mul, map_mul, hσX]
          ring
      | some k =>
        refine ⟨a * Polynomial.C (Ideal.Quotient.mk W (X ⟨k, l⟩)),
          b * Polynomial.C (Ideal.Quotient.mk W (X ⟨k, l⟩)), ?_⟩
        have hτ : τ (Ideal.Quotient.mk W (X ⟨k, l⟩)) = mk' (X ⟨some k, l⟩) := by
          rw [show τ (Ideal.Quotient.mk W (X ⟨k, l⟩)) = mk' (inc (X ⟨k, l⟩)) from Ideal.Quotient.lift_mk _ _ _]
          simp [inc, oldIdx]
        rw [map_mul, map_mul, hσC, hτ]
        ring
  have hφ' : ∀ f, φ' (mk' f) = φ f := fun f => Ideal.Quotient.lift_mk _ _ _
  have hτ' : ∀ d, τ (Ideal.Quotient.mk W d) = mk' (inc d) := fun d => Ideal.Quotient.lift_mk _ _ _
  have hσ : ∀ a, φ' (σ a) = a.map (i : (MRing ι ⧸ W) →+* E) := by
    have : (φ'.comp σ) = Polynomial.mapRingHom i := by
      apply Polynomial.ringHom_ext
      · intro d
        obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective d
        show φ' (σ (Polynomial.C _)) = (Polynomial.C _).map i
        rw [hσC, hτ', hφ', hinc, Polynomial.map_C]
      · show φ' (σ Polynomial.X) = Polynomial.X.map i
        rw [hσX, hφ', hy, Polynomial.map_X]
    exact fun a => congrArg (fun g => g a) this
  have hφx : φ' (mk' xN) = Polynomial.C s * Polynomial.X := by
    rw [hφ', hx]
  have hinj : Function.Injective φ' := by
    rw [injective_iff_map_eq_zero]
    intro q hq
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨a, b, h1⟩ := hform f
    change φ' (mk' f) = 0 at hq
    change mk' f = 0
    rw [h1] at hq ⊢
    rw [map_add, map_mul, hσ, hσ, hφx] at hq
    have hcoef : ∀ n, (a.coeff (n + 1) = 0 ∧ b.coeff n = 0) := by
      intro n
      have := congrArg (fun t => Polynomial.coeff t (n + 1)) hq
      simp only [Polynomial.coeff_add, Polynomial.coeff_map, Polynomial.coeff_zero] at this
      have e : (Polynomial.map i b * (Polynomial.C s * Polynomial.X)).coeff (n + 1) =
          i (b.coeff n) * s := by
        rw [← mul_assoc, Polynomial.coeff_mul_X, mul_comm, Polynomial.coeff_C_mul,
          Polynomial.coeff_map, mul_comm]
      rw [e] at this
      exact hind _ _ this
    have ha0 : a.coeff 0 = 0 := by
      have := congrArg (fun t => Polynomial.coeff t 0) hq
      simp only [Polynomial.coeff_add, Polynomial.coeff_map, Polynomial.coeff_zero] at this
      have e : (Polynomial.map i b * (Polynomial.C s * Polynomial.X)).coeff 0 = 0 := by
        rw [← mul_assoc, Polynomial.coeff_mul_X_zero]
      rw [e, add_zero] at this
      have h3 := hind (a.coeff 0) 0 (by simpa using this)
      exact h3.1
    have ha : a = 0 := by
      ext n
      cases n with
      | zero => simpa using ha0
      | succ n => simpa using (hcoef n).1
    have hb : b = 0 := by
      ext n
      simpa using (hcoef n).2
    rw [ha, hb]; simp
  haveI : IsDomain (MRing (Tb ι) ⧸ twist p W) := hinj.isDomain φ'
  exact (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance

end GlobalTheory.CompanionTheory.Ar.Tw
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.WeakConvergenceOffZeroSetStatement
section
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weak_convergence_off_zero_set : ∀ {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X) (μT : ℝ → Measure X) (N : X → ℝ), IsFiniteMeasure μ → (∀ᶠ t in 𝓝[>] (0 : ℝ), IsFiniteMeasure (μT t)) → Continuous N → (∀ y, 0 ≤ N y ∧ N y ≤ 1) → μ {y | N y = 0} = 0 → (∀ᶠ t in 𝓝[>] (0 : ℝ), μT t {y | N y = 0} = 0) → (∀ (g : X → ℝ) (B : ℝ), Continuous g → (∀ y, |g y| ≤ B) → Tendsto (fun t => ∫ y, g y ∂μT t) (𝓝[>] 0) (𝓝 (∫ y, g y ∂μ))) → (∀ η : ℝ, 0 < η → ∃ ε₀ t₁ : ℝ, 0 < ε₀ ∧ 0 < t₁ ∧ ∀ ε t : ℝ, 0 < ε → ε ≤ ε₀ → 0 < t → t ≤ t₁ → Integrable (fun y => Real.log (1 + ε / N y ^ 2)) (μT t) ∧ ∫ y, Real.log (1 + ε / N y ^ 2) ∂μT t ≤ η) → Integrable (fun y => -Real.log (N y)) μ ∧ (∀ᶠ t in 𝓝[>] (0 : ℝ), Integrable (fun y => -Real.log (N y)) (μT t)) ∧ Tendsto (fun t => ∫ y, -Real.log (N y) ∂μT t) (𝓝[>] 0) (𝓝 (∫ y, -Real.log (N y) ∂μ)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.tendsto_integral_neg_log_of_green_small | exact GlobalTheory.CompanionTheory.Ar.Giv.tendsto_integral_neg_log_of_green_small | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.tendsto_integral_neg_log_of_green_small <;> assumption)
end

