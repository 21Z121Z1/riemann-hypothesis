import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0574
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDensityOfImmersion
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralDetCharacterFockColumnSubstitutionEqZero
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0282
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0758
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0383
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0263
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0646
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0555
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0570
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0832
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0760
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0356
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0822
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0825
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0696
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0699
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0812
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0705
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0791
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0823
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0828
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0826
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0607
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0829
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0777

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockColumnSubstitutionExpOfColumnDerivation
section
noncomputable section

open MvPolynomial

namespace GlobalTheory.ColLie

open GlobalTheory.MinorFrame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in

theorem totalDegree_colSub_le {d a : ℕ} (g : ι → Matrix (Fin a) (Fin a) ℂ) (P : Pol ι d a) :
    (colSub g P).totalDegree ≤ P.totalDegree := by
  have hX : ∀ y : Var ι d a, (colSub g (X y : Pol ι d a)).totalDegree ≤ 1 := by
    intro y
    rw [colSub, aeval_X]
    refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun j _ => ?_)
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, totalDegree_X]
  conv_lhs => rw [as_sum P]
  rw [map_sum]
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun m hm => ?_)
  refine le_trans ?_ (le_totalDegree hm)
  rw [monomial_eq, map_mul, algHom_C, algebraMap_eq, Finsupp.prod, map_prod]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finset_prod _ _).trans (Finset.sum_le_sum fun y _ => ?_)
  rw [map_pow]
  refine (totalDegree_pow _ _).trans ?_
  simpa using Nat.mul_le_mul_left (m y) (hX y)

theorem hasDerivAt_dual_of_coeff {σ : Type} [Finite σ] (l : MvPolynomial σ ℂ →ₗ[ℂ] ℂ) (N : ℕ)
    (u : ℝ → MvPolynomial σ ℂ) (u' : MvPolynomial σ ℂ) (t : ℝ) (hu : ∀ s, (u s).totalDegree ≤ N)
    (hd : ∀ m, HasDerivAt (fun s => coeff m (u s)) (coeff m u') t) : HasDerivAt (fun s => l (u s)) (l u') t := by
  classical
  let A : Finset (σ →₀ ℕ) := (Finsupp.finite_of_degree_le (σ := σ) N).toFinset ∪ u'.support
  have key : ∀ P : MvPolynomial σ ℂ, P.support ⊆ A → l P = ∑ m ∈ A, coeff m P * l (monomial m 1) := by
    intro P hP
    conv_lhs => rw [as_sum P]
    rw [map_sum]
    refine Finset.sum_subset_zero_on_sdiff hP (fun m hm => ?_) (fun m _ => ?_)
    · rw [notMem_support_iff.1 (Finset.mem_sdiff.1 hm).2, zero_mul]
    · rw [← smul_eq_mul, ← map_smul, smul_monomial, smul_eq_mul, mul_one]
  have h1 : ∀ s, (u s).support ⊆ A := by
    intro s m hm
    refine Finset.mem_union_left _ ?_
    rw [Set.Finite.mem_toFinset]
    exact (le_totalDegree hm).trans (hu s)
  rw [key u' Finset.subset_union_right, funext fun s => key (u s) (h1 s)]
  exact HasDerivAt.fun_sum fun m _ => (hd m).mul_const _

omit [Fintype ι] in
theorem atPl_mul {a : ℕ} (τ : ι) (A B : Matrix (Fin a) (Fin a) ℂ) :
    atPl τ (A * B) = fun σ => atPl τ A σ * atPl τ B σ := by
  funext σ
  by_cases h : σ = τ
  · subst h; simp [atPl]
  · simp [atPl, h]

theorem colSub_atPl_one {d a : ℕ} (τ : ι) (P : Pol ι d a) : colSub (atPl τ 1) P = P := by
  have : (colSub (atPl τ 1) : Pol ι d a →ₐ[ℂ] Pol ι d a) = AlgHom.id ℂ _ := by
    refine algHom_ext fun v => ?_
    have h1 : atPl τ (1 : Matrix (Fin a) (Fin a) ℂ) v.1 = 1 := by
      by_cases h : v.1 = τ
      · rw [h]; simp [atPl]
      · simp [atPl, h]
    rw [colSub, aeval_X, h1, Finset.sum_eq_single v.2.2]
    · simp
    · intro b _ hb
      rw [Matrix.one_apply_ne hb]
      simp
    · simp
  rw [this, AlgHom.id_apply]

theorem colSub_exp_of_colDer : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (d a : ℕ) (τ : ι) (c : ℕ) (Q : Type) [AddCommGroup Q] [Module ℂ Q]
    (q : GlobalTheory.MinorFrame.Pol ι d a →ₗ[ℂ] Q),
    (∀ (S : Matrix (Fin a) (Fin a) ℂ) (R : GlobalTheory.MinorFrame.Pol ι d a) (m : GlobalTheory.MinorFrame.Var ι d a →₀ ℕ),
      HasDerivAt (fun h : ℝ => MvPolynomial.coeff m (GlobalTheory.MinorFrame.colSub (GlobalTheory.ColLie.atPl τ (NormedSpace.exp ((h : ℂ) • S))) R))
        (MvPolynomial.coeff m (GlobalTheory.ColLie.colDer τ S R)) 0) →
    (∀ S : Matrix (Fin a) (Fin a) ℂ, S.conjTranspose = -S → ∀ P, q (GlobalTheory.ColLie.colDer τ S P) = ((c : ℂ) * S.trace) • q P) →
    ∀ S : Matrix (Fin a) (Fin a) ℂ, S.conjTranspose = -S → ∀ P,
      q (GlobalTheory.MinorFrame.colSub (GlobalTheory.ColLie.atPl τ (NormedSpace.exp S)) P) = ((NormedSpace.exp S).det ^ c) • q P := by
  intro ι _ _ d a τ c Q _ _ q hco hq S hS P
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro l
  rw [map_sub, map_smul, sub_eq_zero, smul_eq_mul]
  set k : ℂ := (c : ℂ) * S.trace with hk
  let R : ℝ → Pol ι d a := fun t => colSub (atPl τ (NormedSpace.exp ((t : ℂ) • S))) P
  let f : ℝ → ℂ := fun t => l (q (R t))
  have hadd : ∀ s t : ℝ, colSub (atPl τ (NormedSpace.exp ((s : ℂ) • S))) (R t) = R (s + t) := by
    intro s t
    simp only [R]
    rw [← colSub_mul, ← atPl_mul, Complex.ofReal_add, add_smul,
      Matrix.exp_add_of_commute _ _ (((Commute.refl S).smul_left _).smul_right _)]
  have hd : ∀ t, HasDerivAt f (f t * k) t := by
    intro t
    have h0 := hasDerivAt_dual_of_coeff (l ∘ₗ q) (R t).totalDegree
      (fun h : ℝ => colSub (atPl τ (NormedSpace.exp ((h : ℂ) • S))) (R t)) (colDer τ S (R t)) 0
      (fun s => totalDegree_colSub_le _ _) (hco S (R t))
    simp only [hadd, LinearMap.comp_apply, hq S hS, map_smul, smul_eq_mul] at h0
    rw [← sub_self t] at h0
    have h1 := h0.comp_sub_const t t
    simp only [sub_add_cancel] at h1
    rw [mul_comm]
    exact h1
  have hg : ∀ t : ℝ, HasDerivAt (fun s : ℝ => f s * Complex.exp (-(s * k))) 0 t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => -((s : ℂ) * k)) (-k) t := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const k).fun_neg
    exact ((hd t).fun_mul h1.cexp).congr_deriv (by ring)
  have hc := is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv) 1 0
  simp only [f, R, Complex.ofReal_one, Complex.ofReal_zero, one_smul, zero_smul, NormedSpace.exp_zero, colSub_atPl_one,
    one_mul, zero_mul, neg_zero, Complex.exp_zero, mul_one] at hc
  rw [← hc, GlobalTheory.SUVol.det_exp, ← Complex.exp_nat_mul, ← hk, mul_comm, mul_assoc, ← Complex.exp_add, neg_add_cancel,
    Complex.exp_zero, mul_one]

end GlobalTheory.ColLie

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGermBaseChange
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

noncomputable section

namespace GlobalTheory.Shin.DescentAll

theorem mem_zpowers_of_prime {F F' : Type} [Field F] [Field F'] [Algebra F F'] [Finite F']
    (s : F' ≃ₐ[F] F') (hl : (Module.finrank F F').Prime) (hs : s ≠ 1) :
    ∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s := by
  haveI : Finite F := Finite.of_injective _ (algebraMap F F').injective
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fintype F' := Fintype.ofFinite F'
  haveI : FiniteDimensional F F' := Module.Finite.of_finite
  haveI : IsGalois F F' := inferInstance
  haveI : Fact (Module.finrank F F').Prime := ⟨hl⟩
  have hc : Nat.card (F' ≃ₐ[F] F') = Module.finrank F F' := IsGalois.card_aut_eq_finrank F F'
  intro t
  rw [zpowers_eq_top_of_prime_card hc hs]
  exact Subgroup.mem_top t

theorem isCl_cusp (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (m k : ℕ) :
    IsCl (cusp θ m k) := by
  intro x y
  have h := ((GlobalTheory.T.twistedHarishChandraInductionGL_isTwistedClassFunction F (RingHom.id F) 0 0 m (fun _ => 1) (fun _ => 1)).2.2 (rootSum θ k)).1 x y
  simp only [cusp]
  rw [h]

end GlobalTheory.Shin.DescentAll

namespace GlobalTheory.Shin.DescentAll

theorem kills_liftAll : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'),
    (Module.finrank F F').Prime → s ≠ 1 → ∀ (ι : AlgebraicClosure F →ₐ[F] AlgebraicClosure F')
    (θ : AlgebraicClosure F' →* ℂ), (∀ x y : AlgebraicClosure F', x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) →
    ∀ L : List (ℕ × ℕ), (∀ p ∈ L, 0 < p.1 ∧ Reg (Nat.card F) p.1 p.2) → ∀ n, n = deg L →
    Kills (shLift s (J (pullθ ι θ) L n)) (J θ (liftAll (Nat.card F) (Module.finrank F F') L) n) := by
  intro F F' _ _ _ _ s hl hs ι θ hθ
  haveI : Finite F := Finite.of_injective _ (algebraMap F F').injective
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fintype F' := Fintype.ofFinite F'
  haveI : FiniteDimensional F F' := Module.Finite.of_finite
  have hgen := mem_zpowers_of_prime s hl hs
  set q := Nat.card F with hqdef
  set l := Module.finrank F F' with hldef
  have hq2 : 2 ≤ q := by
    rw [hqdef, Nat.card_eq_fintype_card]; exact Fintype.one_lt_card
  have hcard' : Nat.card F' = q ^ l := by
    rw [hqdef, hldef, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Module.card_eq_pow_finrank
  have hlist := GlobalTheory.T.harishChandraProductCuspidalGL_list_properties F' θ
  have happ : ∀ (A B : List (ℕ × ℕ)) (a b : ℕ), deg A = a → deg B = b →
      J θ (A ++ B) (a + b) = hc a b (J θ A a) (J θ B b) (a + b) := by
    intro A B a b ha hb
    subst ha hb
    exact hlist.2.1 A B _ rfl
  intro L
  induction L with
  | nil =>
    intro _ n hn
    obtain rfl : n = 0 := hn
    have hlift : liftAll q l ([] : List (ℕ × ℕ)) = [] := by simp [liftAll]
    rw [hlift]
    have h1 : shLift s (J (pullθ ι θ) [] 0) = J θ [] 0 := by
      funext δ
      have hδ : δ = 1 := by ext i j; exact i.elim0
      unfold shLift
      rw [dif_pos ⟨1, by rw [hδ]; exact isNorm_one s 0⟩]
      rfl
    rw [h1]
    exact GlobalTheory.T.isInCharacterIsotypicPart_self _ _ (GlobalTheory.T.isCharacter_harishChandraProductCuspidalGL_of_regular F' θ hθ [] (by simp) 0 rfl)
  | cons p L ih =>
    intro hL n hn
    have hp := hL p List.mem_cons_self
    have hLt : ∀ x ∈ L, 0 < x.1 ∧ Reg q x.1 x.2 := fun x hx => hL x (List.mem_cons_of_mem _ hx)
    have hdeg : deg (p :: L) = p.1 + deg L := by simp [deg]
    obtain rfl : n = p.1 + deg L := hn.trans hdeg
    set A : List (ℕ × ℕ) := (if l ∣ p.1 then liftL q l [p] else [(p.1, p.2 * ∑ i ∈ Finset.range l, q ^ (p.1 * i))])
      with hAdef
    have hsplit : liftAll q l (p :: L) = A ++ liftAll q l L := by simp [liftAll, hAdef]
    have hA1 : liftAll q l [p] = A := by simp [liftAll, hAdef]
    obtain ⟨hdA, hRA⟩ := GlobalTheory.T.lift_all_preserves_degree_and_regularity q l [p] hq2 hl (by simpa using hp)
    obtain ⟨hdB, hRB⟩ := GlobalTheory.T.lift_all_preserves_degree_and_regularity q l L hq2 hl hLt
    rw [hA1] at hdA hRA
    have hdA' : deg A = p.1 := by rw [hdA]; simp [deg]
    have hKA : Kills (shLift s (cusp (pullθ ι θ) p.1 p.2)) (J θ A p.1) := by
      by_cases h : l ∣ p.1
      · have := GlobalTheory.T.shintani_lift_kills_cusp_divisible_degree F F' s hl hs ι θ hθ p.1 p.2 hp.1 h hp.2
        rw [hAdef, if_pos h]
        simpa only [Prod.mk.eta] using this
      · rw [hAdef, if_neg h]
        have hu := GlobalTheory.T.shintani_lift_kills_cusp_of_degree_not_dvd F F' s hl hs ι θ hθ p.1 p.2 hp.1 h hp.2
        have hJ : J θ [(p.1, p.2 * ∑ i ∈ Finset.range l, q ^ (p.1 * i))] p.1 =
            cusp θ p.1 (p.2 * ∑ i ∈ Finset.range l, q ^ (p.1 * i)) := by
          rw [J_cons]
          exact (GlobalTheory.T.harishChandraInductionGL_one_left_right_unit F' p.1 _ (isCl_cusp F' θ _ _)).2
        rw [hJ]
        exact hu
    have hRA' : ∀ x ∈ A, 0 < x.1 ∧ Reg (Nat.card F') x.1 x.2 := by rw [hcard']; exact hRA
    have hRB' : ∀ x ∈ liftAll q l L, 0 < x.1 ∧ Reg (Nat.card F') x.1 x.2 := by rw [hcard']; exact hRB
    have hcharA := GlobalTheory.T.isCharacter_harishChandraProductCuspidalGL_of_regular F' θ hθ A hRA' p.1 hdA'.symm
    have hcharB := GlobalTheory.T.isCharacter_harishChandraProductCuspidalGL_of_regular F' θ hθ (liftAll q l L) hRB' (deg L) hdB.symm
    rw [J_cons, GlobalTheory.T.shintaniLift_harishChandraInduction_eq_twisted F F' s hgen p.1 (deg L) _ rfl _ _ (isCl_cusp F _ _ _)
      ((GlobalTheory.T.harishChandraProductCuspidalGL_list_properties F (pullθ ι θ)).1 L (deg L)), hsplit, happ A (liftAll q l L) p.1 (deg L) hdA' hdB]
    exact GlobalTheory.T.twistedHarishChandra_isotypic_part F' (s : F' →+* F') p.1 (deg L) _ rfl _ _ _ _ hcharA hcharB hKA (ih hLt (deg L) rfl)

end GlobalTheory.Shin.DescentAll
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionalIdealNormEqFiniteIdeleModule
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.LatVal.InvIdealNorm

open scoped GlobalTheory.Idele

variable {K : Type} [Field K] [NumberField K]

theorem eq_inv_smul_one {t : (Af K)ˣ} {𝔞 : FractionalIdeal (𝓞 K)⁰ K} (h : IsInvIdealOf t 𝔞) :
    𝔞 = t⁻¹ • (1 : FractionalIdeal (𝓞 K)⁰ K) := by
  have h' := GlobalTheory.LatVal.CurveTransport.isInvIdealOf_inv_smul_one t
  ext x
  rw [h x, h' x]

theorem finprod_absNorm_zpow_count {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) :
    ∏ᶠ v : HeightOneSpectrum (𝓞 K), ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ FractionalIdeal.count K v I =
      ((FractionalIdeal.absNorm I : ℚ) : ℝ) := by
  let g : FractionalIdeal (𝓞 K)⁰ K →*₀ ℝ :=
    (Rat.castHom ℝ).toMonoidWithZeroHom.comp FractionalIdeal.absNorm
  have hg : ∀ J, g J = ((FractionalIdeal.absNorm J : ℚ) : ℝ) := fun _ => rfl
  conv_rhs => rw [← hg, ← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI]
  rw [map_finprod g]
  · refine finprod_congr fun v => ?_
    rw [map_zpow₀, hg, FractionalIdeal.coeIdeal_absNorm]
    simp
  · refine (Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors I)).subset fun v hv h0 => hv ?_
    simp only [h0, zpow_zero]

end GlobalTheory.LatVal.InvIdealNorm

open GlobalTheory.LatVal.InvIdealNorm in
open scoped GlobalTheory.Idele in

theorem GlobalTheory.LatVal.nrm_eq_modF_of_isInvIdealOf : ∀ {K : Type} [Field K] [NumberField K] (t : (Af K)ˣ)
    (𝔞 : FractionalIdeal (𝓞 K)⁰ K) (h : IsInvIdealOf t 𝔞), nrm 𝔞 = modF t := by
  intro K _ _ t 𝔞 h
  have e := eq_inv_smul_one h
  rw [GlobalTheory.Idele.smul_one_eq] at e
  have h0 : 𝔞 ≠ 0 := e ▸ GlobalTheory.Idele.idealOf_ne_zero _
  rw [nrm, ← finprod_absNorm_zpow_count h0, modF]
  refine finprod_congr fun v => ?_
  congr 1
  rw [e, GlobalTheory.Idele.count_idealOf, GlobalTheory.Idele.ord_vw_inv, GlobalTheory.Idele.ord_vw, neg_neg]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasValLogOfHasValFormalLogStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasVal_log_eval_of_hasVal_formalLog : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] [Algebra ℚ Q] (θ : B →+* O), IsFrame p Q θ → ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (z : σ → B), (∀ i, ∃ N : ℕ, (p : B) ∣ z i ^ N) → ∀ E : MvPowerSeries σ B →ₐ[B] B, IsEval p z E → ∀ (g : MvPowerSeries σ B) (q : Q), constantCoeff g = 1 → HasVal p z (formalLog (map (algebraMap B Q) g)) q → HasVal p (fun _ : Unit => E g - 1) (PowerSeries.log Q : MvPowerSeries Unit Q) q := by
  first | exact @GlobalTheory.QLog.hasVal_log_of_hasVal_formalLog | exact GlobalTheory.QLog.hasVal_log_of_hasVal_formalLog | (intros; apply GlobalTheory.QLog.hasVal_log_of_hasVal_formalLog <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasValLogOfMulSelfEqZeroStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasVal_log_of_mul_self_eq_zero' : ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] [Algebra ℚ Q] (p : ℕ) (x : B), x * x = 0 → HasVal p (fun _ : Unit => x) (PowerSeries.log Q : MvPowerSeries Unit Q) (algebraMap B Q x) := by
  first | exact @GlobalTheory.QLog.SqZero.hasVal_log_of_mul_self_eq_zero | exact GlobalTheory.QLog.SqZero.hasVal_log_of_mul_self_eq_zero | (intros; apply GlobalTheory.QLog.SqZero.hasVal_log_of_mul_self_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomFixedPullbackRepresentableGlue
section
set_option autoImplicit false
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.EndLoc.HomGlue

theorem reps_iso : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (hL : L.IsLB) (hM : M.IsLB) (X : Scheme.{0}) (u : HomGlue.Pt A B L M X), (∀ (Z : Scheme.{0}) (x : HomGlue.Pt A B L M Z), ∃! c : Z ⟶ X, u.map hL hM c = x) → ∀ (W : S.Opens) (T : Scheme.{0}) (y : HomGlue.Pt A B L M T) (πT : T ⟶ W), y.t = πT ≫ W.ι → (∀ (Z : Scheme.{0}) (x : HomGlue.Pt A B L M Z) (b : Z ⟶ W), x.t = b ≫ W.ι → ∃! c : Z ⟶ T, y.map hL hM c = x) → ∃ e : T ≅ (u.t ⁻¹ᵁ W).toScheme, e.hom ≫ (u.t ∣_ W) = πT := by
  intro S A B _ _ L M hL hM X u hu W T y πT hy hloc
  obtain ⟨c, hc, -⟩ := hu T y
  have hcW : Set.range c ⊆ ((u.t ⁻¹ᵁ W).ι).opensRange := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.opensRange_ι]
    show u.t (c z) ∈ W
    have e : c ≫ u.t = πT ≫ W.ι := by rw [← hy, ← hc]; rfl
    rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply]
    exact (πT z).2
  let c' := IsOpenImmersion.lift (u.t ⁻¹ᵁ W).ι c (by simpa using hcW)
  have hc' : c' ≫ (u.t ⁻¹ᵁ W).ι = c := IsOpenImmersion.lift_fac _ _ _
  have hx : (u.map hL hM (u.t ⁻¹ᵁ W).ι).t = (u.t ∣_ W) ≫ W.ι := by
    rw [HomGlue.Pt.map_t, morphismRestrict_ι]
  obtain ⟨d, hd, -⟩ := hloc _ (u.map hL hM (u.t ⁻¹ᵁ W).ι) (u.t ∣_ W) hx
  have h1 : c' ≫ d = 𝟙 T := by
    refine (hloc T y πT hy).unique ?_ ?_
    · rw [HomGlue.Pt.map_comp, hd, ← HomGlue.Pt.map_comp, hc', hc]
    · exact HomGlue.Pt.map_id hL hM y
  have h2 : d ≫ c' = 𝟙 _ := by
    have : d ≫ c = (u.t ⁻¹ᵁ W).ι := (hu _ (u.map hL hM (u.t ⁻¹ᵁ W).ι)).unique
      (by rw [HomGlue.Pt.map_comp, hc, hd]) rfl
    rw [← cancel_mono (u.t ⁻¹ᵁ W).ι, Category.assoc, hc', this, Category.id_comp]
  refine ⟨⟨c', d, h1, h2⟩, ?_⟩
  show c' ≫ (u.t ∣_ W) = πT
  rw [← cancel_mono W.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hc', ← hy, ← hc]
  rfl

theorem wit_of_eq {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] {L : LB A.left} {M : LB B.left}
    {Z : Scheme.{0}} {t t' : Z ⟶ S} {f : pullback A.hom t ⟶ B.left} {f' : pullback A.hom t' ⟶ B.left} (h : t = t')
    (hf : ∀ e : pullback A.hom t' ⟶ pullback A.hom t, e ≫ pullback.fst _ _ = pullback.fst _ _ →
      e ≫ pullback.snd _ _ = pullback.snd _ _ → e ≫ f = f') (w : HomGlue.Wit A B L M t f) :
    HomGlue.Wit A B L M t' f' := by
  subst h
  have := hf (𝟙 _) (Category.id_comp _) (Category.id_comp _)
  rw [Category.id_comp] at this
  subst this
  exact w

theorem glue_pts : (∀ (H : Scheme.{0}) (A B : Over H) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (Φ : A ⟶ B), IsMonHom Φ → IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Out.Rigidified A L → Out.Rigidified B M → (∀ h : H, ∃ W : H.Opens, h ∈ W ∧ LBIso (L.pull (A.hom ⁻¹ᵁ W).ι) ((M.pull Φ.left).pull (A.hom ⁻¹ᵁ W).ι)) → LBIso L (M.pull Φ.left)) → ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (hL : L.IsLB) (hM : M.IsLB), IsAbelianScheme A → IsAbelianScheme B → Out.Rigidified A L → Out.Rigidified B M → ∀ (Z : Scheme.{0}) (𝒰 : Z.OpenCover) (x : ∀ i, HomGlue.Pt A B L M (𝒰.X i)), (∀ i j (T : Scheme.{0}) (b : T ⟶ 𝒰.X i) (c : T ⟶ 𝒰.X j), b ≫ 𝒰.f i = c ≫ 𝒰.f j → (x i).map hL hM b = (x j).map hL hM c) → ∃ y : HomGlue.Pt A B L M Z, ∀ i, y.map hL hM (𝒰.f i) = x i := by
  intro hiso S A B _ _ _ _ L M hL hM hA hB hrA hrB Z 𝒰 x hx
  obtain ⟨t, f, h⟩ := GlobalTheory.T.exists_glued_morphism_of_compatible_family S A B L M hL hM Z 𝒰 x hx
  have hw : ∀ i, HomGlue.Wit A B L M (𝒰.f i ≫ t) (HomGlue.pmap A t (𝒰.f i) ≫ f) := by
    intro i
    have hc : pullback.fst A.hom (x i).t ≫ A.hom = (pullback.snd A.hom (x i).t ≫ 𝒰.f i) ≫ t := by
      rw [pullback.condition, Category.assoc, (h i).1]
    refine wit_of_eq (h i).1.symm (fun e e1 e2 => ?_) (x i).wit
    rw [← (h i).2 (pullback.lift _ _ hc) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _), ← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, e1, pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, e2, pullback.lift_snd]
  refine ⟨⟨t, f, GlobalTheory.T.glue_wit_alt hiso S A B L M hL hM hA hB hrA hrB Z 𝒰 t f hw⟩, fun i => ?_⟩
  refine HomGlue.Pt.ext' (h i).1 ?_
  show _ ≫ HomGlue.pmap A t (𝒰.f i) ≫ f = _
  exact (Category.assoc _ _ _).symm.trans ((h i).2 _
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (pullback.lift_fst _ _ _)).trans (pullback.lift_fst _ _ _)))
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (pullback.lift_snd _ _ _)).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ 𝒰.f i) (pullback.lift_snd _ _ _))))))

theorem isSheaf_homFun : (∀ (H : Scheme.{0}) (A B : Over H) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (Φ : A ⟶ B), IsMonHom Φ → IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Out.Rigidified A L → Out.Rigidified B M → (∀ h : H, ∃ W : H.Opens, h ∈ W ∧ LBIso (L.pull (A.hom ⁻¹ᵁ W).ι) ((M.pull Φ.left).pull (A.hom ⁻¹ᵁ W).ι)) → LBIso L (M.pull Φ.left)) → ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (hL : L.IsLB) (hM : M.IsLB), IsAbelianScheme A → IsAbelianScheme B → Out.Rigidified A L → Out.Rigidified B M → Presieve.IsSheaf Scheme.zariskiTopology (HomGlue.homFun A B L M hL hM) := by
  intro hiso S A B _ _ _ _ L M hL hM hA hB hrA hrB
  rw [Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange]
  rintro Y P hP
  obtain ⟨(𝒰 : Scheme.OpenCover Y), rfl⟩ := Scheme.exists_cover_of_mem_pretopology hP
  rw [Presieve.isSheafFor_arrows_iff]
  intro x hx
  exact existsUnique_of_exists_of_unique
    (glue_pts hiso S A B L M hL hM hA hB hrA hrB Y 𝒰 x fun i j T b c h => hx i j T b c h)
    fun y y' h h' => GlobalTheory.T.homGlue_pt_ext_of_openCover S A B L M hL hM Y 𝒰 y y' fun i => (h i).trans (h' i).symm

theorem homFixRep_glue : (∀ (H : Scheme.{0}) (A B : Over H) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (Φ : A ⟶ B), IsMonHom Φ → IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Out.Rigidified A L → Out.Rigidified B M → (∀ h : H, ∃ W : H.Opens, h ∈ W ∧ LBIso (L.pull (A.hom ⁻¹ᵁ W).ι) ((M.pull Φ.left).pull (A.hom ⁻¹ᵁ W).ι)) → LBIso L (M.pull Φ.left)) → ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Out.Rigidified A L → Out.Rigidified B M → ∀ (Ix : Type) (V : Ix → Scheme.{0}) (j : ∀ i, V i ⟶ S), (∀ i, IsOpenImmersion (j i)) → (∀ s : S, ∃ i, s ∈ Set.range (j i)) → (∀ i, ∃ (A' B' : Over (V i)) (_ : GrpObj A') (_ : GrpObj B') (φA : A'.left ⟶ A.left) (φB : B'.left ⟶ B.left) (R : HomFixRep A' B' (L.pull φA) (M.pull φB)), IsGrpPullback A' A (j i) φA ∧ IsGrpPullback B' B (j i) φB ∧ QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π) → ∃ R : HomFixRep A B L M, QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π := by
  intro hiso S A B _ _ _ _ L M hA hB hL hM hrA hrB Ix V j hj hcov hR
  choose A' B' gA gB φA φB R hpA hpB hqc hsep hlft using hR
  have hy : ∀ i, ∃ y : HomGlue.Pt A B L M (R i).H, y.t = (R i).π ≫ j i ∧ ∀ (Z : Scheme.{0})
      (x : HomGlue.Pt A B L M Z) (b : Z ⟶ V i), x.t = b ≫ j i → ∃! c : Z ⟶ (R i).H, y.map hL hM c = x := by
    intro i
    letI := gA i; letI := gB i
    exact GlobalTheory.T.exists_universal_pt_of_isGrpPullback S A B L M hL hM (V i) (j i) (A' i) (B' i) (φA i) (φB i) (R i) (hpA i) (hpB i)
  choose y hyt hyu using hy
  let W : Ix → S.Opens := fun i => (j i).opensRange
  have hW : iSup W = ⊤ := by
    refine top_le_iff.1 fun s _ => ?_
    obtain ⟨i, hi⟩ := hcov s
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩
  let πW : ∀ i, (R i).H ⟶ W i := fun i => (R i).π ≫ (j i).isoOpensRange.hom
  have hπW : ∀ i, πW i ≫ (W i).ι = (R i).π ≫ j i := fun i => by
    simp [πW, W]
  have hloc : ∀ i (Z : Scheme.{0}) (x : HomGlue.Pt A B L M Z) (b : Z ⟶ W i), x.t = b ≫ (W i).ι →
      ∃! c : Z ⟶ (R i).H, (y i).map hL hM c = x := by
    intro i Z x b hb
    refine hyu i Z x (b ≫ (j i).isoOpensRange.inv) ?_
    rw [hb, Category.assoc]; simp [W]
  have hrep : (HomGlue.homFun A B L M hL hM).IsRepresentable :=
    GlobalTheory.GenTorsor.isRepresentable_of_cover _ (isSheaf_homFun hiso S A B L M hL hM hA hB hrA hrB) (HomGlue.homProj A B L M hL hM)
      W hW (fun i => (R i).H) y πW (fun i => (hyt i).trans (hπW i).symm) hloc
  set F := HomGlue.homFun A B L M hL hM
  let X := F.reprX
  let u : HomGlue.Pt A B L M X := F.reprx
  have huniv : ∀ (Z : Scheme.{0}) (x : HomGlue.Pt A B L M Z), ∃! c : Z ⟶ X, u.map hL hM c = x := by
    intro Z x
    have key : ∀ c : Z ⟶ X, u.map hL hM c = F.representableBy.homEquiv c := fun c => by
      rw [F.representableBy.homEquiv_eq c]; rfl
    refine ⟨F.representableBy.homEquiv.symm x, ?_, fun c hc => ?_⟩
    · dsimp only; rw [key]; exact F.representableBy.homEquiv.apply_symm_apply x
    · dsimp only at hc; rw [key] at hc; rw [← hc]; exact (F.representableBy.homEquiv.symm_apply_apply c).symm
  obtain ⟨R0, e, he⟩ := GlobalTheory.T.exists_homFixRep_iso_of_universal S A B L M hL hM X u huniv
  have hloc' : ∀ i, ∃ e : (R i).H ≅ (u.t ⁻¹ᵁ W i).toScheme, e.hom ≫ (u.t ∣_ W i) = πW i := fun i =>
    reps_iso S A B L M hL hM X u huniv (W i) (R i).H (y i) (πW i) ((hyt i).trans (hπW i).symm) (hloc i)
  choose ei hei using hloc'
  have key : ∀ i, u.t ∣_ W i = (ei i).inv ≫ πW i := fun i => by
    rw [← hei i, Iso.inv_hom_id_assoc]
  have hP : ∀ (P : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget P],
      (∀ i, P (R i).π) → P R0.π := by
    intro P _ hR
    rw [← he]
    refine (MorphismProperty.cancel_left_of_respectsIso P e.hom u.t).2 ?_
    refine IsZariskiLocalAtTarget.of_iSup_eq_top W hW fun i => ?_
    rw [key i]
    refine (MorphismProperty.cancel_left_of_respectsIso P _ _).2 ?_
    exact (MorphismProperty.cancel_right_of_respectsIso P _ _).2 (hR i)
  have : IsZariskiLocalAtTarget @QuasiCompact.{0} := by
    set_option backward.isDefEq.respectTransparency.types false in exact inferInstance
  have : IsZariskiLocalAtTarget @LocallyOfFiniteType.{0} :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @LocallyOfFiniteType)
  exact ⟨R0, hP @QuasiCompact hqc, hP @IsSeparated hsep, hP @LocallyOfFiniteType hlft⟩

end GlobalTheory.EndLoc.HomGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomomorphismMatrixUniqueFixedPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homomorphism_matrix_unique_fixed_pullback : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (k : ℕ) (mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))), Hyps L M k bA bB eA eB → ∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B') (c c' : Fin mA → Fin mB → Γ(Sp R, ⊤)), IsTest A B L M t A' B' φA' φB' Φ' → IsMat L M k bA bB eA eB t A' B' φA' φB' Φ' c → IsMat L M k bA bB eA eB t A' B' φA' φB' Φ' c' → c = c' := by
  first | exact @GlobalTheory.HomFixUniq.mat_unique | exact GlobalTheory.HomFixUniq.mat_unique | (intros; apply GlobalTheory.HomFixUniq.mat_unique <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatSumThIndRegroupStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_latSum_thInd_eq_sum : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (L : Submodule (𝓞 X.E) (Sp X.E a)) (L' : Submodule (𝓞 X.E) (Sp X.E b)) (cA c c' : ℕ) (Ξ : HomE X.E a b → ℂ), A.IndAdd a b S (cA * (c * c')) → IsSdLat L → IsSdLat L' → 0 < cA → 0 < c → 0 < c' → (∀ x, Ξ x ≠ 0 → x ∈ homAt S L L') → (∀ x, ∀ y ∈ mulLat c (homAt S L L'), Ξ (x + y) = Ξ x) → ∃ R : Finset (HomE X.E a b), R.card ≤ c ^ (Module.finrank ℚ X.E * a * b) ∧ ∀ z, latSum (divLat cA (homAt S L L')) (mulLat (c * c') (homAt S L L')) (fun x => Ξ x * A.thInd S L L' (c * c') x z) = ∑ x ∈ R, Ξ x * A.thInd S L L' c x z := by
  first | exact @GlobalTheory.latSum_thInd_regroup | exact GlobalTheory.latSum_thInd_regroup | (intros; apply GlobalTheory.latSum_thInd_regroup <;> assumption)
end

