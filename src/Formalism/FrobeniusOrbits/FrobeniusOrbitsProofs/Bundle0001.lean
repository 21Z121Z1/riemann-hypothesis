import Mathlib
import Formalism.FrobeniusOrbits.Statement
import Formalism.TameInertiaTowers.TowerFieldFoundations
import Formalism.TameInertiaTowers.CentralOrderTwo.Bundle0002
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.JumpSets
import Formalism.FrobeniusOrbits.Bundle0002

-- bundled from Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.ConjReal
section
open NumberField IntermediateField

noncomputable section

namespace Formalism.FrobeniusOrbits

open Formalism.TwoAdicCyclotomicDecomposition

namespace ConjReal

variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}

lemma hcl_neg_one (e : ℕ) : hcl e (-1) = 1 := by
  unfold hcl
  rw [QuotientGroup.eq_one_iff]
  exact Subgroup.mem_zpowers _

theorem conj_main (hGal : HostGalois) (hSpec : HostGalSpec) (hqd : HypOdd q d)
    (h : IsLayer (e + 2) q d ζ a b) :
    ∃ (τ : L ≃ₐ[ℚ] L) (σc : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b),
      galMap h.1 a b τ = JJ (e + 2) ∧ (∀ x : hostE ζ a b, ((σc x : hostE ζ a b) : L) = τ x) ∧
      galE e ζ a b σc = cc e ∧
      ∀ (φ : hostE ζ a b →+* ℂ) (x : hostE ζ a b), φ (σc x) = starRingEnd ℂ (φ x) := by
  obtain ⟨hG, _, _, _⟩ := hGal e q d hqd L ζ a b h
  have := hG
  obtain ⟨τ, hτ⟩ := (layerGalois (e + 2) q d (by omega) hqd L ζ a b h).2.2.2.2 (JJ (e + 2))
  let σc : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b := τ.restrictNormal (hostE ζ a b)
  have hres : ∀ x : hostE ζ a b, ((σc x : hostE ζ a b) : L) = τ x := fun x =>
    AlgEquiv.restrictNormal_commutes τ (hostE ζ a b) x
  refine ⟨τ, σc, hτ, hres, ?_, ?_⟩
  · rw [(hSpec e q d hqd L ζ a b h σc).2.2.2 τ hres, hτ]
    simp [JJ, cc, c0, hcl_neg_one]
  · intro φ x
    let ψ : L →+* ℂ := ComplexEmbedding.lift L φ
    have hψ : ∀ y : hostE ζ a b, ψ (y : L) = φ y := fun y =>
      ComplexEmbedding.lift_algebraMap_apply L φ y
    have hc := (layerConj (e + 2) q d (by omega) hqd L ζ a b h ψ τ).2 hτ
    rw [← hψ (σc x), ← hψ x, hres x]
    exact hc x

lemma aE_sq (h : IsLayer (e + 2) q d ζ a b) : aE ζ a b ^ 2 = -(q : hostE ζ a b) := by
  apply Subtype.ext
  push_cast
  exact h.2.1

end ConjReal

open ConjReal

theorem hostConj_of (hGal : HostGalois) (hSpec : HostGalSpec) : HostConj := by
  intro e q d hqd L _ _ ζ a b h
  obtain ⟨hG, _, _, hbij⟩ := hGal e q d hqd L ζ a b h
  have := hG
  obtain ⟨_, σc, _, _, hσc, hconj⟩ := conj_main hGal hSpec hqd h
  have hq : 0 < q := hqd.1.pos
  have haE := aE_sq h
  have hTC : IsTotallyComplex (hostE ζ a b) := by
    refine ⟨fun w => ?_⟩
    rw [InfinitePlace.isComplex_iff, ComplexEmbedding.isReal_iff]
    intro hw
    have h2 := RingHom.congr_fun hw (aE ζ a b)
    rw [ComplexEmbedding.conjugate_coe_eq, UnitConjugation.phi_conj hq haE] at h2
    have h3 : (2 : ℂ) * w.embedding (aE ζ a b) = 0 := by linear_combination -h2
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact two_ne_zero h4
    · exact (map_ne_zero _).2 (UnitConjugation.ne_zero_of_sq hq haE) h4
  have hCM : IsCMField (hostE ζ a b) := by
    refine IsCMField.of_forall_isConj (hostE ζ a b) (σ := σc) (fun φ => ?_)
    ext x
    rw [ComplexEmbedding.conjugate_coe_eq]
    exact (hconj φ x).symm
  refine ⟨hCM, fun φ σ => ⟨fun hx => ?_, fun hσ => ?_⟩⟩
  · have hσ : σ = σc := AlgEquiv.ext fun x => φ.injective (by rw [hx, hconj])
    rw [hσ, hσc]
  · have hσ' : σ = σc := hbij.1 (hσ.trans hσc.symm)
    subst hσ'
    exact hconj φ

theorem hostReal_of (hGal : HostGalois) (hSpec : HostGalSpec) (hConj : HostConj) : HostReal :=
  _root_.UpperTheory.Reformulated.B.JumpSetsAlt.hostReal_of hGal hSpec hConj

end Formalism.FrobeniusOrbits
end
end

-- bundled from Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.FrobMulInertia
section
open NumberField IntermediateField Ideal

noncomputable section

namespace Formalism.FrobeniusOrbits

open Formalism.TwoAdicCyclotomicDecomposition

namespace Frob

theorem frob_mul_inertia {S : Type*} [CommRing S] {G : Type*} [Group G] [MulSemiringAction G S]
    [SMulCommClass G ℤ S] (Q : Ideal S) (ρ τ : G) (hρ : ρ ∈ Q.inertia G)
    (hτ : IsArithFrobAt ℤ τ Q) : IsArithFrobAt ℤ (ρ * τ) Q := by
  intro x
  have h1 : ρ • (τ • x) - τ • x ∈ Q := hρ (τ • x)
  have h2 := hτ x
  try simp only [MulSemiringAction.toAlgHom_apply] at h2 ⊢
  rw [mul_smul]
  have h3 := Q.add_mem h1 h2
  rwa [sub_add_sub_cancel] at h3

end Frob

theorem hostFrob_of (hGal : HostGalois) (hSpec : HostGalSpec) : HostFrob := by
  intro e q d hqd L _ _ ζ a b h p _ hp2 hpq hpd P _ _
  obtain ⟨hEgal, -, hmulE, hbijE⟩ := hGal e q d hqd L ζ a b h
  obtain ⟨hLgal, -, hmulL, hbijL⟩ := layerGalois (e + 2) q d (by omega) hqd L ζ a b h
  have := hEgal
  have := hLgal
  obtain ⟨⟨Q, hQp, hQl⟩⟩ : Nonempty (P.primesOver (𝓞 L)) := inferInstance
  have : Q.LiesOver (span {(p : ℤ)}) := Ideal.LiesOver.trans Q P (span {(p : ℤ)})
  have hFr := layerFrob (e + 2) q d (by omega) hqd L ζ a b h p hp2 hpq hpd Q
  obtain ⟨⟨τ, hτ⟩, hτspec⟩ := hFr
  obtain ⟨hτ1, hτ2, hτ3⟩ := (hτspec τ).mp hτ

  have hgm1 : galMap h.1 a b (1 : Gal(L/ℚ)) = 1 := by
    have := hmulL 1 1
    rw [mul_one] at this
    exact (mul_eq_left.mp this.symm)

  have hIQ : ∀ ρ ∈ Q.inertia Gal(L/ℚ), ρ = 1 := by
    intro ρ hρ
    have hF := Frob.frob_mul_inertia Q ρ τ hρ hτ
    obtain ⟨h1, h2, h3⟩ := (hτspec (ρ * τ)).mp hF
    have heq : galMap h.1 a b (ρ * τ) = galMap h.1 a b τ := by
      refine Prod.ext (Units.ext (h1.trans hτ1.symm)) (Prod.ext ?_ ?_)
      · exact Units.ext (h2.trans hτ2.symm)
      · exact Units.ext (h3.trans hτ3.symm)
    rw [hmulL, mul_eq_right] at heq
    exact hbijL.1 (heq.trans hgm1.symm)
  have heQ : Q.ramificationIdx ℤ = 1 := by
    rw [← odd_card L p Q]
    have : Q.inertia Gal(L/ℚ) = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hIQ
    rw [this]
    simp
  have heP : P.ramificationIdx ℤ = 1 := by
    have hte := Ideal.ramificationIdx_tower (R := ℤ) P Q
    rw [heQ] at hte
    exact Nat.eq_one_of_mul_eq_one_right hte.symm
  have hIP : ∀ σ ∈ P.inertia Gal(hostE ζ a b/ℚ), σ = 1 := by
    have hc := odd_card (hostE ζ a b) p P
    rw [heP, Nat.card_eq_one_iff_unique] at hc
    intro σ hσ
    have : (⟨σ, hσ⟩ : P.inertia Gal(hostE ζ a b/ℚ)) = ⟨1, one_mem _⟩ := hc.1.elim _ _
    exact congrArg Subtype.val this

  let σ₀ : Gal(hostE ζ a b/ℚ) := τ.restrictNormal (hostE ζ a b)
  have hσ₀ : ∀ x : hostE ζ a b, ((σ₀ x : hostE ζ a b) : L) = τ x :=
    fun x => AlgEquiv.restrictNormal_commutes τ (hostE ζ a b) x
  have hσ₀F : IsArithFrobAt ℤ σ₀ P := by
    intro x
    have hx := hτ (algebraMap (𝓞 (hostE ζ a b)) (𝓞 L) x)
    rw [odd_card_under p Q] at hx
    rw [odd_card_under p P]
    rw [Ideal.over_def Q P, Ideal.under_def, Ideal.mem_comap]
    convert hx using 1
    apply RingOfIntegers.coe_injective
    simp only [map_sub, map_pow, MulSemiringAction.toAlgHom_apply]
    congr 1
    show (((σ₀ • x : 𝓞 (hostE ζ a b)) : hostE ζ a b) : L) =
      τ (((x : 𝓞 (hostE ζ a b)) : hostE ζ a b) : L)
    exact hσ₀ x
  have hval := (hSpec e q d hqd L ζ a b h σ₀).2.2.2 τ hσ₀
  have hgalE1 : galE e ζ a b (1 : Gal(hostE ζ a b/ℚ)) = 1 := by
    have := hmulE 1 1
    rw [mul_one] at this
    exact (mul_eq_left.mp this.symm)
  have huniq : ∀ σ : Gal(hostE ζ a b/ℚ), IsArithFrobAt ℤ σ P → σ = σ₀ := by
    intro σ hσ
    have := hIP _ (hσ.mul_inv_mem_inertia hσ₀F)
    exact mul_inv_eq_one.mp this
  refine ⟨⟨σ₀, hσ₀F⟩, fun σ => ⟨fun hσ => ?_, fun hs => ?_⟩, fun σ => ⟨fun hσ => ?_, fun hσ => ?_⟩⟩
  · rw [huniq σ hσ, hval]
    exact ⟨hτ2, hτ3, (galMap h.1 a b τ).1, hτ1, rfl⟩
  · obtain ⟨s1, s2, u, hu, hu2⟩ := hs
    have : σ = σ₀ := by
      apply hbijE.1
      rw [hval]
      refine Prod.ext (Prod.ext ?_ ?_) ?_
      · exact Units.ext (s1.trans hτ2.symm)
      · exact Units.ext (s2.trans hτ3.symm)
      · rw [hu2]
        exact congrArg (hcl e) (Units.ext (hu.trans hτ1.symm))
    rw [this]
    exact hσ₀F
  · exact hIP σ (AddSubgroup.mem_inertia.mpr hσ)
  · subst hσ
    intro x
    simp

end Formalism.FrobeniusOrbits
end
end

-- bundled from Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.ThickFrames
section
open Finset

noncomputable section

namespace Formalism.FrobeniusOrbits.BernoulliSumsFrobeniusOrbits

variable {α : Type*} [Fintype α]

lemma sum_card (δ : ℝ) (f : ℕ → ℝ) :
    ∑ T : Finset α, bern δ T * f T.card =
      ∑ k ∈ range (Fintype.card α + 1),
        (bernsteinPolynomial ℝ (Fintype.card α) k).eval δ * f k := by
  have h := Finset.sum_powerset_apply_card
    (fun k => δ ^ k * (1 - δ) ^ (Fintype.card α - k) * f k) (x := (univ : Finset α))
  rw [powerset_univ, card_univ] at h
  simp only [bern]
  rw [h]
  refine sum_congr rfl fun k _ => ?_
  simp [bernsteinPolynomial, nsmul_eq_mul]
  ring

lemma bern_nonneg {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (T : Finset α) : 0 ≤ bern δ T := by
  unfold bern
  have : 0 ≤ 1 - δ := by linarith
  positivity

lemma sum_bern (δ : ℝ) : ∑ T : Finset α, bern δ T = 1 := by
  have h := sum_card (α := α) δ (fun _ => 1)
  simp only [mul_one] at h
  rw [h, ← Polynomial.eval_finsetSum, bernsteinPolynomial.sum, Polynomial.eval_one]

lemma sum_bern_var (δ : ℝ) :
    ∑ T : Finset α, bern δ T * ((T.card : ℝ) - δ * Fintype.card α) ^ 2 =
      Fintype.card α * δ * (1 - δ) := by
  have h := sum_card (α := α) δ (fun k => ((k : ℝ) - δ * Fintype.card α) ^ 2)
  rw [h]
  have hv := congrArg (Polynomial.eval δ) (bernsteinPolynomial.variance ℝ (Fintype.card α))
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_natCast,
    Polynomial.eval_one, nsmul_eq_mul] at hv
  rw [← hv]
  refine sum_congr rfl fun k _ => ?_
  ring

end Formalism.FrobeniusOrbits.BernoulliSumsFrobeniusOrbits

namespace Formalism.FrobeniusOrbits

open BernoulliSumsFrobeniusOrbits

open Classical in
theorem hostTops : HostTops := by
  intro α ι _ _ δ β ω BAD hδ hδ1 hβ hω hn hBAD
  set n : ℝ := (Fintype.card α : ℝ) with hn_def
  set M : ℝ := β * δ * n * ∑ p, ω p with hM_def
  set X : Finset α → ℝ := fun T => ∑ p, ω p * ((T.filter (fun t => BAD p t T)).card : ℝ)
    with hX_def
  have hb0 : ∀ T : Finset α, 0 ≤ bern δ T := bern_nonneg hδ.le hδ1
  have hX0 : ∀ T, 0 ≤ X T := fun T => sum_nonneg fun p _ => mul_nonneg (hω p) (Nat.cast_nonneg _)
  have hM0 : 0 ≤ M := by
    have : 0 ≤ ∑ p, ω p := sum_nonneg fun p _ => hω p
    have : 0 ≤ n := Nat.cast_nonneg _
    positivity

  have hc : ∀ p (T : Finset α), ((T.filter (fun t => BAD p t T)).card : ℝ) =
      ∑ t, if t ∈ T ∧ BAD p t T then (1 : ℝ) else 0 := by
    intro p T
    rw [Finset.sum_boole]
    congr 2
    ext t
    simp
  have hEX : ∑ T, bern δ T * X T ≤ M := by
    calc ∑ T, bern δ T * X T
        = ∑ T : Finset α, ∑ p, ∑ t, ω p * (if t ∈ T ∧ BAD p t T then bern δ T else 0) := by
          refine sum_congr rfl fun T _ => ?_
          simp only [X, hc, mul_sum]
          refine sum_congr rfl fun p _ => sum_congr rfl fun t _ => ?_
          split_ifs <;> ring
      _ = ∑ p, ∑ t, ω p * ∑ T : Finset α, (if t ∈ T ∧ BAD p t T then bern δ T else 0) := by
          rw [sum_comm]
          refine sum_congr rfl fun p _ => ?_
          rw [sum_comm]
          simp only [mul_sum]
      _ ≤ ∑ p, ∑ _t : α, ω p * (β * δ) :=
          sum_le_sum fun p _ => sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (hBAD p t) (hω p)
      _ = M := by
          simp only [hM_def, hn_def, sum_const, card_univ, nsmul_eq_mul, mul_sum]
          refine sum_congr rfl fun p _ => ?_
          ring

  have hA : ∑ T : Finset α, (if 4 * M < X T then bern δ T else 0) ≤ 1 / 4 := by
    have key : 4 * M * ∑ T : Finset α, (if 4 * M < X T then bern δ T else 0) ≤ M := by
      rw [mul_sum]
      refine le_trans (sum_le_sum fun T _ => ?_) hEX
      split_ifs with h
      · nlinarith [hb0 T]
      · simp only [mul_zero]; exact mul_nonneg (hb0 T) (hX0 T)
    rcases hM0.lt_or_eq with hpos | hzero
    · nlinarith
    · have hsum0 : ∑ T, bern δ T * X T = 0 :=
        le_antisymm (hzero ▸ hEX) (sum_nonneg fun T _ => mul_nonneg (hb0 T) (hX0 T))
      have hall := (Finset.sum_eq_zero_iff_of_nonneg
        (fun T _ => mul_nonneg (hb0 T) (hX0 T))).mp hsum0
      have : ∑ T : Finset α, (if 4 * M < X T then bern δ T else 0) = 0 := by
        refine sum_eq_zero fun T _ => ?_
        split_ifs with h
        · have hXT : 0 < X T := by rw [← hzero] at h; linarith
          have := hall T (mem_univ _)
          rcases mul_eq_zero.mp this with h' | h'
          · exact h'
          · linarith
        · rfl
      rw [this]; norm_num

  have hB : ∑ T : Finset α,
      (if (δ * n / 2) ^ 2 < ((T.card : ℝ) - δ * n) ^ 2 then bern δ T else 0) ≤ 1 / 4 := by
    set S := ∑ T : Finset α,
      (if (δ * n / 2) ^ 2 < ((T.card : ℝ) - δ * n) ^ 2 then bern δ T else 0) with hS
    have hS0 : 0 ≤ S := sum_nonneg fun T _ => by split_ifs <;> simp [hb0 T]
    have key : (δ * n / 2) ^ 2 * S ≤ δ * n := by
      have hv := sum_bern_var (α := α) δ
      rw [hS, mul_sum]
      calc ∑ T : Finset α, (δ * n / 2) ^ 2 *
            (if (δ * n / 2) ^ 2 < ((T.card : ℝ) - δ * n) ^ 2 then bern δ T else 0)
          ≤ ∑ T : Finset α, bern δ T * ((T.card : ℝ) - δ * n) ^ 2 := by
            refine sum_le_sum fun T _ => ?_
            split_ifs with h
            · nlinarith [hb0 T]
            · simp only [mul_zero]; exact mul_nonneg (hb0 T) (sq_nonneg _)
        _ = n * δ * (1 - δ) := hv
        _ ≤ δ * n := by nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card α)]
    by_contra hlt
    push Not at hlt
    have hc0 : 0 < δ * n := by linarith
    have h1 : (δ * n / 2) ^ 2 * (1 / 4) < (δ * n / 2) ^ 2 * S :=
      mul_lt_mul_of_pos_left hlt (by positivity)
    nlinarith [hn]

  by_contra hne
  push Not at hne
  have hle : ∀ T : Finset α, bern δ T ≤ (if 4 * M < X T then bern δ T else 0) +
      (if (δ * n / 2) ^ 2 < ((T.card : ℝ) - δ * n) ^ 2 then bern δ T else 0) := by
    intro T
    by_cases h2 : (δ * n / 2) ^ 2 < ((T.card : ℝ) - δ * n) ^ 2
    · rw [if_pos h2]; split_ifs <;> linarith [hb0 T]
    · rw [if_neg h2]
      have hab := abs_le_of_sq_le_sq' (not_lt.mp h2) (by positivity)
      have h4 : 4 * M < X T := by
        have := hne T (by linarith [hab.1]) (by linarith [hab.2])
        simp only [X, hM_def]
        linarith
      rw [if_pos h4]; linarith
  have := sum_le_sum fun T (_ : T ∈ (univ : Finset (Finset α))) => hle T
  rw [sum_add_distrib, sum_bern] at this
  linarith

end Formalism.FrobeniusOrbits
end
end

