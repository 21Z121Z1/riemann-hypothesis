import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialDifferentialWords.KappaRight
import Mathlib

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialDifferentialWords.DivideAll
section
open MvPolynomial

noncomputable section

namespace PI.OpWords

theorem wtLe_span (K : Type) [Field K] (k : ℕ) (c : ℤ) (s : Set (Pol K k))
    (hs : ∀ f ∈ s, WtLe K k c f) : ∀ f ∈ Submodule.span K s, WtLe K k c f := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem x hx => exact hs x hx
  | zero =>
    intro m hm
    simp at hm
  | add x y _ _ hx hy =>
    intro m hm a
    rcases Finset.mem_union.1 (support_add hm) with h | h
    · exact hx m h a
    · exact hy m h a
  | smul r x _ hx =>
    intro m hm a
    exact hx m (support_smul hm) a

theorem kappa_ad (hL : KappaLeft) (hR : KappaRight) (K : Type) [Field K] [CharZero K] (k d : ℕ)
    (a b : Fin k) (A : Module.End K ↥(homogeneousSubmodule (Fin k) K d)) :
    kappa K k d (Formalism.MainNotions.TestSideCounting.Ed K k d a b * A - A * Formalism.MainNotions.TestSideCounting.Ed K k d a b) =
      Rop K k a b (kappa K k d A) := by
  rw [map_sub, hL K k d a b A, hR K k d a b A]
  rfl

theorem divide_all (hV : Vanish) (hD : DivT) (hRB : RBihom) (hRT : RTT) (hTW : TTWt)
    (K : Type) [Field K] [CharZero K] (k c : ℕ) : ∀ n : ℕ, ∀ (W : Submodule K (Pol K k)),
    W ≤ Bihom K k (c + n) → (∀ f ∈ W, ∀ a b, Rop K k a b f ∈ W) → (∀ f ∈ W, WtLe K k c f) →
    ∀ f ∈ W, ∃ g ∈ Bihom K k c, f = tt K k ^ n * g := by
  intro n
  induction n with
  | zero =>
    intro W hW _ _ f hf
    exact ⟨f, by simpa using hW hf, by simp⟩
  | succ n ih =>
    intro W hW hst hwt f hf
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      refine ⟨0, Submodule.zero_mem _, ?_⟩
      have hf' : f ∈ weightedHomogeneousSubmodule K (wx 0) (c + (n + 1)) ⊓
          weightedHomogeneousSubmodule K (wxi 0) (c + (n + 1)) := hW hf
      have h1 := (Submodule.mem_inf.1 hf').1
      rw [mem_weightedHomogeneousSubmodule] at h1
      rw [mul_zero]
      ext m
      rw [coeff_zero]
      by_contra h
      have h2 := h1 h
      have h3 : m = 0 := by
        ext v
        rcases v with i | i <;> exact i.elim0
      rw [h3, map_zero] at h2
      omega
    · have htt : tt K k ≠ 0 := by
        intro h
        have h1 := congrArg (eval (fun _ : Fin k ⊕ Fin k => (1 : K))) h
        simp [tt] at h1
        omega
      have hdiv : ∀ f ∈ W, ∃ g ∈ Bihom K k (c + n), f = tt K k * g := by
        intro f hf
        have hv := hV K k (c + (n + 1)) c W hW hst hwt (by omega) f hf
        obtain ⟨g, hg, rfl⟩ := hD K k (c + (n + 1)) (by omega) f (hW hf) hv
        exact ⟨g, by simpa using hg, rfl⟩
      let W' : Submodule K (Pol K k) := W.comap (LinearMap.mulLeft K (tt K k))
      have hmem : ∀ g, g ∈ W' ↔ tt K k * g ∈ W := fun g => Iff.rfl
      have hW' : W' ≤ Bihom K k (c + n) := by
        intro g hg
        obtain ⟨g', hg', he⟩ := hdiv _ ((hmem g).1 hg)
        rw [mul_left_cancel₀ htt he]
        exact hg'
      have hst' : ∀ f ∈ W', ∀ a b, Rop K k a b f ∈ W' := by
        intro g hg a b
        rw [hmem, ← hRT K k a b g]
        exact hst _ ((hmem g).1 hg) a b
      have hwt' : ∀ f ∈ W', WtLe K k c f := by
        intro g hg
        exact hTW K k c g (hwt _ ((hmem g).1 hg))
      obtain ⟨g, hg, rfl⟩ := hdiv f hf
      obtain ⟨g'', hg'', rfl⟩ := ih W' hW' hst' hwt' g ((hmem g).2 hf)
      exact ⟨g'', hg'', by ring⟩

theorem opWords_of (hI : KappaInj) (hL : KappaLeft) (hR : KappaRight) (hB : KappaBihom)
    (hE : WtOfEig) (hRB : RBihom) (hRT : RTT) (hTW : TTWt) (hD : DivT) (hV : Vanish)
    (hS : Surj) : Formalism.MainNotions.TestSideCounting.OpBound := by
  intro K _ _ k d c WW Sg hst hspan heig A hA
  have key : ∃ c' : ℕ, c' ≤ c ∧ c' ≤ d ∧ ∃ g ∈ Bihom K k c', kappa K k d A = tt K k ^ (d - c') * g := by
    rcases Nat.lt_or_ge c d with hcd | hdc
    · let W : Submodule K (Pol K k) := WW.map (kappa K k d)
      have hW : W ≤ Bihom K k (c + (d - c)) := by
        have e : c + (d - c) = d := by omega
        rw [e]
        rintro f ⟨A', _, rfl⟩
        exact hB K k d A'
      have hWst : ∀ f ∈ W, ∀ a b, Rop K k a b f ∈ W := by
        rintro f ⟨A', hA', rfl⟩ a b
        rw [← kappa_ad hL hR K k d a b A']
        exact Submodule.mem_map_of_mem (hst A' hA' a b)
      have hWwt : ∀ f ∈ W, WtLe K k c f := by
        have hWeq : W = Submodule.span K (kappa K k d '' Sg) := by
          show WW.map (kappa K k d) = _
          rw [hspan, Submodule.map_span]
        rw [hWeq]
        apply wtLe_span
        rintro f ⟨A', hA', rfl⟩ m hm a
        obtain ⟨ω, hω, hωc⟩ := heig A' hA'
        have h1 : Rop K k a a (kappa K k d A') = (ω a : K) • kappa K k d A' := by
          rw [← kappa_ad hL hR K k d a a A', hω a, map_smul]
        have h2 := hE K k a (ω a) (kappa K k d A') h1 m hm
        rw [h2]
        exact_mod_cast hωc a
      obtain ⟨g, hg, he⟩ := divide_all hV hD hRB hRT hTW K k c (d - c) W hW hWst hWwt _
        (Submodule.mem_map_of_mem hA)
      exact ⟨c, le_rfl, hcd.le, g, hg, he⟩
    · exact ⟨d, hdc, le_rfl, kappa K k d A, hB K k d A, by simp⟩
  obtain ⟨c', hc'c, hc'd, g, hg, he⟩ := key
  have hsurj := hS K k d c' hc'd g hg
  rw [← he] at hsurj
  obtain ⟨B, hB', hBe⟩ := Submodule.mem_map.1 hsurj
  have hAB : B = A := hI K k d hBe
  subst hAB
  have hmono : Wc K k d c' ≤ Wc K k d c := by
    unfold Wc
    apply Submodule.span_mono
    rintro Bx ⟨l, hl, rfl⟩
    exact ⟨l, le_trans hl hc'c, rfl⟩
  exact hmono hB'

end PI.OpWords
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialDifferentialWords.KappaCoeff
section
open MvPolynomial Finsupp

noncomputable section

namespace PI.OpWords

variable {K : Type} [Field K] {k d : ℕ}

lemma mapDomain_inl_add_inr (u g : Fin k →₀ ℕ) :
    u.mapDomain Sum.inl + g.mapDomain Sum.inr = Finsupp.sumElim u g := by
  ext v
  rcases v with i | i
  · simp [Finsupp.mapDomain_apply Sum.inl_injective, Finsupp.mapDomain_notin_range]
  · simp [Finsupp.mapDomain_apply Sum.inr_injective, Finsupp.mapDomain_notin_range]

lemma sumElim_inj {u g u' g' : Fin k →₀ ℕ} :
    Finsupp.sumElim u g = Finsupp.sumElim u' g' ↔ u = u' ∧ g = g' := by
  constructor
  · intro h
    constructor
    · ext i
      have h1 := congrArg (fun f => f (Sum.inl i)) h
      simpa using h1
    · ext i
      have h1 := congrArg (fun f => f (Sum.inr i)) h
      simpa using h1
  · rintro ⟨rfl, rfl⟩
    rfl

lemma exists_sumElim (n : Fin k ⊕ Fin k →₀ ℕ) : ∃ m g : Fin k →₀ ℕ, n = Finsupp.sumElim m g := by
  refine ⟨Finsupp.comapDomain Sum.inl n Sum.inl_injective.injOn,
    Finsupp.comapDomain Sum.inr n Sum.inr_injective.injOn, ?_⟩
  ext v
  rcases v with i | i <;> simp [Finsupp.comapDomain_apply]

lemma pol_ext {P Q : Pol K k}
    (h : ∀ m g : Fin k →₀ ℕ, coeff (Finsupp.sumElim m g) P = coeff (Finsupp.sumElim m g) Q) : P = Q := by
  ext n
  obtain ⟨m, g, rfl⟩ := exists_sumElim n
  exact h m g

lemma sumElim_sub_single_inr (m g : Fin k →₀ ℕ) (b : Fin k) :
    Finsupp.sumElim m g - single (Sum.inr b) 1 = Finsupp.sumElim m (g - single b 1) := by
  ext v
  rcases v with i | i <;> simp [Finsupp.single_apply]

lemma sumElim_add_single_inr (m g : Fin k →₀ ℕ) (b : Fin k) :
    Finsupp.sumElim m g + single (Sum.inr b) 1 = Finsupp.sumElim m (g + single b 1) := by
  ext v
  rcases v with i | i <;> simp [Finsupp.single_apply]

lemma coeff_term (P : MvPolynomial (Fin k) K) (m g g' : Fin k →₀ ℕ) :
    coeff (Finsupp.sumElim m g) (rename Sum.inl P * monomial (g'.mapDomain Sum.inr) (1 : K)) =
      if g' = g then coeff m P else 0 := by
  classical
  induction P using MvPolynomial.induction_on'
  next u c =>
    rw [rename_monomial, monomial_mul, mapDomain_inl_add_inr]
    simp only [coeff_monomial, sumElim_inj, mul_one]
    by_cases h1 : u = m <;> by_cases h2 : g' = g <;> simp [h1, h2]
  next p q hp hq =>
    rw [map_add, add_mul, coeff_add, hp, hq]
    split_ifs <;> simp [coeff_add]

lemma mono_val (g : Fin k →₀ ℕ) :
    (mono K k d g : MvPolynomial (Fin k) K) = if g.degree = d then monomial g 1 else 0 := by
  unfold mono
  split_ifs <;> rfl

lemma mem_antidiag_iff (g : Fin k →₀ ℕ) :
    g ∈ (Finset.univ : Finset (Fin k)).finsuppAntidiag d ↔ g.degree = d := by
  rw [Finset.mem_finsuppAntidiag, Finsupp.degree_eq_sum]
  simp

lemma kappa_apply (A : Module.End K ↥(homogeneousSubmodule (Fin k) K d)) :
    kappa K k d A = ∑ g ∈ (Finset.univ : Finset (Fin k)).finsuppAntidiag d,
      invFact K g • (rename Sum.inl ((A (mono K k d g) : MvPolynomial (Fin k) K)) *
        monomial (g.mapDomain Sum.inr) (1 : K)) := by
  simp [kappa]

lemma coeff_kappa (A : Module.End K ↥(homogeneousSubmodule (Fin k) K d)) (m g : Fin k →₀ ℕ) :
    coeff (Finsupp.sumElim m g) (kappa K k d A) =
      invFact K g * coeff m (A (mono K k d g) : MvPolynomial (Fin k) K) := by
  classical
  rw [kappa_apply, coeff_sum]
  simp only [coeff_smul, coeff_term, smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [mem_antidiag_iff] at h
    have h0 : mono K k d g = 0 := by
      unfold mono
      rw [dif_neg h]
    rw [h0, map_zero]
    simp

lemma degree_of_coeff_ne (F : ↥(homogeneousSubmodule (Fin k) K d)) {m : Fin k →₀ ℕ}
    (h : coeff m (F : MvPolynomial (Fin k) K) ≠ 0) : m.degree = d := by
  have hF := (mem_homogeneousSubmodule d _).1 F.2
  rw [Finsupp.degree_eq_weight_one]
  exact hF h

lemma eq_sum_mono (F : ↥(homogeneousSubmodule (Fin k) K d)) :
    F = ∑ g ∈ (F : MvPolynomial (Fin k) K).support,
      coeff g (F : MvPolynomial (Fin k) K) • mono K k d g := by
  apply Subtype.ext
  rw [Submodule.coe_sum]
  conv_lhs => rw [(F : MvPolynomial (Fin k) K).as_sum]
  refine Finset.sum_congr rfl fun g hg => ?_
  rw [Submodule.coe_smul, mono_val, if_pos (degree_of_coeff_ne F (MvPolynomial.mem_support_iff.1 hg)),
    smul_monomial, smul_eq_mul, mul_one]

lemma prodFact_fintype (g : Fin k →₀ ℕ) :
    g.prod (fun _ n => (n.factorial : K)) = ∏ i, ((g i).factorial : K) := by
  exact Finsupp.prod_fintype _ _ (fun _ => by simp)

lemma prodFact_ne_zero [CharZero K] (g : Fin k →₀ ℕ) :
    g.prod (fun _ n => (n.factorial : K)) ≠ 0 := by
  rw [prodFact_fintype]
  exact Finset.prod_ne_zero_iff.2 (fun i _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _))

lemma invFact_ne_zero [CharZero K] (g : Fin k →₀ ℕ) : invFact K g ≠ 0 := by
  unfold invFact
  exact inv_ne_zero (prodFact_ne_zero g)

lemma prodFact_add_single (g : Fin k →₀ ℕ) (i : Fin k) :
    (g + single i 1).prod (fun _ n => (n.factorial : K)) =
      ((g i : K) + 1) * g.prod (fun _ n => (n.factorial : K)) := by
  rw [prodFact_fintype, prodFact_fintype, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  have h1 : ∏ j ∈ Finset.univ.erase i, (((g + single i 1 : Fin k →₀ ℕ) j).factorial : K) =
      ∏ j ∈ Finset.univ.erase i, ((g j).factorial : K) := by
    refine Finset.prod_congr rfl fun j hj => ?_
    simp [Finsupp.single_apply, Finset.ne_of_mem_erase hj, Ne.symm (Finset.ne_of_mem_erase hj)]
  rw [h1, Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ, Nat.cast_mul]
  push_cast
  ring

lemma invFact_add_single [CharZero K] (g : Fin k →₀ ℕ) (i : Fin k) :
    invFact K (g + single i 1) * ((g i : K) + 1) = invFact K g := by
  unfold invFact
  rw [prodFact_add_single, mul_inv]
  have h1 : ((g i : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (g i)
  rw [mul_comm ((g i : K) + 1)⁻¹ _, mul_assoc, inv_mul_cancel₀ h1, mul_one]

lemma degree_sub_add (g : Fin k →₀ ℕ) (a b : Fin k) (hb : g b ≠ 0) :
    (g - single b 1 + single a 1).degree = g.degree := by
  have hle : single b 1 ≤ g := by
    rw [Finsupp.single_le_iff]
    omega
  have hs : ∀ c : Fin k, (single c 1 : Fin k →₀ ℕ).degree = 1 := fun c => by
    rw [Finsupp.degree_eq_sum]
    simp [Finsupp.single_apply]
  conv_rhs => rw [← tsub_add_cancel_of_le hle]
  rw [map_add, map_add, hs, hs]

lemma Ed_val (a b : Fin k) (F : ↥(homogeneousSubmodule (Fin k) K d)) :
    (Formalism.MainNotions.TestSideCounting.Ed K k d a b F : MvPolynomial (Fin k) K) = X a * pderiv b (F : MvPolynomial (Fin k) K) :=
  rfl

lemma Ed_mono (a b : Fin k) (g : Fin k →₀ ℕ) :
    Formalism.MainNotions.TestSideCounting.Ed K k d a b (mono K k d g) =
      ((g b : ℕ) : K) • mono K k d (g - single b 1 + single a 1) := by
  apply Subtype.ext
  rw [Ed_val, Submodule.coe_smul, mono_val, mono_val]
  by_cases hb : g b = 0
  · split_ifs <;> simp [pderiv_monomial, hb]
  · rw [degree_sub_add g a b hb]
    split_ifs with h
    · rw [pderiv_monomial, X, monomial_mul, smul_monomial, add_comm (Finsupp.single a 1)]
      simp
    · simp

lemma pderiv_inl_xi (b : Fin k) (g : Fin k →₀ ℕ) :
    pderiv (Sum.inl b) (monomial (g.mapDomain Sum.inr) (1 : K) : Pol K k) = 0 := by
  simp [pderiv_monomial, Finsupp.mapDomain_notin_range]

lemma weight_wx (m g : Fin k →₀ ℕ) : Finsupp.weight (wx k) (Finsupp.sumElim m g) = m.degree := by
  simp [Finsupp.weight_apply, Finsupp.sum_fintype, wx, Fintype.sum_sum_type, Finsupp.degree_eq_sum]

lemma weight_wxi (m g : Fin k →₀ ℕ) : Finsupp.weight (wxi k) (Finsupp.sumElim m g) = g.degree := by
  simp [Finsupp.weight_apply, Finsupp.sum_fintype, wxi, Fintype.sum_sum_type, Finsupp.degree_eq_sum]

end PI.OpWords
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialDifferentialWords.PolarizationBihomogeneous
section
open MvPolynomial Finsupp

noncomputable section

namespace PI.OpWords

theorem rop_apply_eq (K : Type) [Field K] (k : ℕ) (a b : Fin k) (f : Pol K k) :
    Rop K k a b f = X (Sum.inl a) * pderiv (Sum.inl b) f - X (Sum.inr b) * pderiv (Sum.inr a) f := rfl

theorem pderiv_inl_tt (K : Type) [Field K] (k : ℕ) (b : Fin k) :
    pderiv (Sum.inl b) (tt K k) = X (Sum.inr b) := by
  simp [tt, Derivation.leibniz, pderiv_X, Pi.single_apply]

theorem pderiv_inr_tt (K : Type) [Field K] (k : ℕ) (a : Fin k) :
    pderiv (Sum.inr a) (tt K k) = X (Sum.inl a) := by
  simp [tt, Derivation.leibniz, pderiv_X, Pi.single_apply]

theorem rttRelation : RTT := by
  intro K _ _ k a b g
  rw [rop_apply_eq, rop_apply_eq]
  simp only [Derivation.leibniz, pderiv_inl_tt, pderiv_inr_tt, smul_eq_mul]
  ring

theorem iwh_X_pderiv {σ : Type} {K : Type} [Field K] (w : σ → ℕ) (i j : σ) (hij : w i = w j)
    {f : MvPolynomial σ K} {n : ℕ} (hf : IsWeightedHomogeneous w f n) :
    IsWeightedHomogeneous w (X i * pderiv j f) n := by
  classical
  rw [f.as_sum, map_sum, Finset.mul_sum]
  apply IsWeightedHomogeneous.sum
  intro m hm
  have hwm : weight w m = n := hf (MvPolynomial.mem_support_iff.1 hm)
  rw [pderiv_monomial]
  by_cases hmj : m j = 0
  · simp [hmj, isWeightedHomogeneous_zero]
  · have hle : Finsupp.single j 1 ≤ m := by
      rw [Finsupp.single_le_iff]
      omega
    have hs : ∀ v, weight w (Finsupp.single v 1) = w v := by
      intro v
      simp [Finsupp.weight_apply, Finsupp.sum_single_index]
    have h1 : weight w (m - Finsupp.single j 1) + w j = n := by
      rw [← hs j, ← map_add, tsub_add_cancel_of_le hle, hwm]
    rw [X, monomial_mul, one_mul]
    apply isWeightedHomogeneous_monomial
    rw [map_add, hs i, hij, add_comm, h1]

theorem polarizationBihomogeneous : RBihom := by
  intro K _ _ k d a b f hf
  have hf' : f ∈ weightedHomogeneousSubmodule K (wx k) d ⊓ weightedHomogeneousSubmodule K (wxi k) d := hf
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hf'
  rw [mem_weightedHomogeneousSubmodule] at h1 h2
  show Rop K k a b f ∈ weightedHomogeneousSubmodule K (wx k) d ⊓ weightedHomogeneousSubmodule K (wxi k) d
  rw [rop_apply_eq]
  refine Submodule.mem_inf.2 ⟨Submodule.sub_mem _ ?_ ?_, Submodule.sub_mem _ ?_ ?_⟩ <;>
    rw [mem_weightedHomogeneousSubmodule]
  · exact iwh_X_pderiv _ _ _ (by simp [wx]) h1
  · exact iwh_X_pderiv _ _ _ (by simp [wx]) h1
  · exact iwh_X_pderiv _ _ _ (by simp [wxi]) h2
  · exact iwh_X_pderiv _ _ _ (by simp [wxi]) h2

theorem coeff_X_pderiv_self {σ : Type} {K : Type} [Field K] (i : σ) (f : MvPolynomial σ K)
    (m : σ →₀ ℕ) : coeff m (X i * pderiv i f) = coeff m f * (m i : K) := by
  classical
  induction f using MvPolynomial.induction_on'
  next u a =>
    rw [pderiv_monomial]
    by_cases hu : u i = 0
    · by_cases h : u = m
      · subst h
        simp [hu]
      · simp [hu, coeff_monomial, h]
    · have hle : Finsupp.single i 1 ≤ u := by
        rw [Finsupp.single_le_iff]
        omega
      rw [X, monomial_mul, one_mul, add_tsub_cancel_of_le hle, coeff_monomial, coeff_monomial]
      split_ifs with h
      · subst h
        rfl
      · simp
  next p q hp hq =>
    simp only [map_add, mul_add, coeff_add, hp, hq, add_mul]

theorem weightOfEigenvector : WtOfEig := by
  intro K _ _ k a w f h m hm
  have h1 := congrArg (coeff m) h
  rw [rop_apply_eq, coeff_sub, coeff_X_pderiv_self, coeff_X_pderiv_self, coeff_smul] at h1
  have hc : coeff m f ≠ 0 := MvPolynomial.mem_support_iff.1 hm
  have h2 : (((m (Sum.inl a) : ℤ) - m (Sum.inr a) : ℤ) : K) = (w : K) := by
    apply mul_left_cancel₀ hc
    push_cast
    linear_combination h1
  exact_mod_cast h2

def va (k : ℕ) (a : Fin k) : Fin k ⊕ Fin k → ℤ :=
  Sum.elim (fun i => if i = a then 1 else 0) (fun i => if i = a then -1 else 0)

theorem weight_va (k : ℕ) (a : Fin k) (m : Fin k ⊕ Fin k →₀ ℕ) :
    weight (va k a) m = (m (Sum.inl a) : ℤ) - m (Sum.inr a) := by
  simp [Finsupp.weight_apply, Finsupp.sum_fintype, va, Fintype.sum_sum_type, sub_eq_add_neg]

theorem tt_va (K : Type) [Field K] (k : ℕ) (a : Fin k) :
    IsWeightedHomogeneous (va k a) (tt K k) 0 := by
  show IsWeightedHomogeneous (va k a) (∑ i, X (Sum.inl i) * X (Sum.inr i) : Pol K k) 0
  apply IsWeightedHomogeneous.sum
  intro i _
  have h := (isWeightedHomogeneous_X K (va k a) (Sum.inl i)).mul
    (isWeightedHomogeneous_X K (va k a) (Sum.inr i))
  by_cases hi : i = a <;> simpa [va, hi] using h

theorem comp_mul_zero {σ : Type} {K : Type} [Field K] (w : σ → ℤ) {φ : MvPolynomial σ K}
    (hφ : IsWeightedHomogeneous w φ 0) (n : ℤ) (ψ : MvPolynomial σ K) :
    weightedHomogeneousComponent w n (φ * ψ) = φ * weightedHomogeneousComponent w n ψ := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent, coeff_mul, coeff_mul]
  split_ifs with hd
  · refine Finset.sum_congr rfl fun x hx => ?_
    rw [coeff_weightedHomogeneousComponent]
    by_cases h0 : coeff x.1 φ = 0
    · simp [h0]
    · have hx0 := hφ h0
      have hsum := by simpa using hx
      have hw : weight w x.2 = n := by
        rw [← hd, ← hsum, map_add, hx0, zero_add]
      rw [if_pos hw]
  · symm
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [coeff_weightedHomogeneousComponent]
    by_cases h0 : coeff x.1 φ = 0
    · simp [h0]
    · have hx0 := hφ h0
      have hsum := by simpa using hx
      have hw : weight w x.2 ≠ n := by
        rw [← hsum, map_add, hx0, zero_add] at hd
        exact hd
      rw [if_neg hw, mul_zero]

theorem tt_ne_zero (K : Type) [Field K] [CharZero K] (k : ℕ) (hk : 0 < k) : tt K k ≠ 0 := by
  intro h
  have h1 := congrArg (eval (fun _ : Fin k ⊕ Fin k => (1 : K))) h
  simp [tt] at h1
  omega

theorem pairingWeightCancel : TTWt := by
  intro K _ _ k c g h m hm a
  by_contra hlt
  push_neg at hlt
  obtain ⟨n, hn⟩ : ∃ n : ℤ, n = (m (Sum.inl a) : ℤ) - m (Sum.inr a) := ⟨_, rfl⟩
  have hwm : weight (va k a) m = n := by rw [weight_va, hn]
  have hk : 0 < k := Fin.pos a
  have hcomp : weightedHomogeneousComponent (va k a) n g ≠ 0 := by
    intro h0
    have h3 := congrArg (coeff m) h0
    rw [coeff_weightedHomogeneousComponent, if_pos hwm] at h3
    exact (MvPolynomial.mem_support_iff.1 hm) (by simpa using h3)
  have hprod : weightedHomogeneousComponent (va k a) n (tt K k * g) ≠ 0 := by
    rw [comp_mul_zero (va k a) (tt_va K k a) n g]
    exact mul_ne_zero (tt_ne_zero K k hk) hcomp
  apply hprod
  ext m'
  rw [coeff_weightedHomogeneousComponent, coeff_zero]
  split_ifs with hw
  · by_contra hne
    have h4 := h m' (MvPolynomial.mem_support_iff.2 hne) a
    rw [weight_va] at hw
    omega
  · rfl

end PI.OpWords
end
end

