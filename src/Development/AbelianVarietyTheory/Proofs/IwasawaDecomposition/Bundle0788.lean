import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0769
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0749
import Formalism.LocalToGlobal.Columns.MtAdWt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0938
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0771
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0767
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0048
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodReductionCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0456
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0019
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0750
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0810
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0818
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0819
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0775
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0682
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0742
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2095
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0770
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0745
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HodgeGramEqRiemann

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MatchingMatricesOfBaseChangeRepresentationStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

open Formalism.L2.DIV GlobalTheory.CoefModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matchingMatrices_of_baseChange_representation : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {K K' : Type} [Field K] [Field K'] (f : K →+* K') (e : K' →+* ℂ) {W₀ W W' : Type} [AddCommGroup W₀] [Module K W₀] [AddCommGroup W] [Module K' W] [AddCommGroup W'] [Module ℂ W'] (ρ₀ : Representation K (GQ L n) W₀) (ρ : Representation K' (GQ L n) W) (ρ' : Representation ℂ (GQ L n) W'), (∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (b₀ : Module.Basis ι K W₀) (b₁ : Module.Basis ι K' W), ∀ γ, LinearMap.toMatrix b₁ b₁ (ρ γ) = (LinearMap.toMatrix b₀ b₀ (ρ₀ γ)).map f) → GlobalTheory.LevCmp.WtMatch (e.comp f) ρ₀ ρ' → GlobalTheory.LevCmp.WtMatch e ρ ρ' := by
  first | exact @GlobalTheory.BcMatch.bcmatch_main | exact GlobalTheory.BcMatch.bcmatch_main | (intros; apply GlobalTheory.BcMatch.bcmatch_main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemGrassmannianRelationIdealSupMonomialSpan
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

noncomputable section

namespace GlobalTheory.GrassTop

lemma rel_mem_J {p q k : ℕ} (hk : 1 ≤ k) : rel k ∈ J p q :=
  Ideal.subset_span (Or.inl ⟨k, hk, rfl⟩)

lemma X_zero_sub_one_mem_J {p q : ℕ} (b : Bool) :
    (X (b, 0) - 1 : MvPolynomial (Bool × ℕ) ℝ) ∈ J p q :=
  Ideal.subset_span (Or.inr (Or.inl ⟨b, rfl⟩))

lemma X_true_mem_J {p q k : ℕ} (hk : p < k) : (X (true, k) : MvPolynomial (Bool × ℕ) ℝ) ∈ J p q :=
  Ideal.subset_span (Or.inr (Or.inr (Or.inl ⟨k, hk, rfl⟩)))

lemma X_false_mem_J {p q k : ℕ} (hk : q < k) : (X (false, k) : MvPolynomial (Bool × ℕ) ℝ) ∈ J p q :=
  Ideal.subset_span (Or.inr (Or.inr (Or.inr ⟨k, hk, rfl⟩)))

lemma mem_of_neg_one_pow_mul {I : Ideal (MvPolynomial (Bool × ℕ) ℝ)} {x : MvPolynomial (Bool × ℕ) ℝ}
    (n : ℕ) (h : C ((-1 : ℝ) ^ n) * x ∈ I) : x ∈ I := by
  have := I.mul_mem_left (C ((-1 : ℝ) ^ n)) h
  rwa [← mul_assoc, ← C_mul, ← mul_pow, neg_one_mul, neg_neg, one_pow, C_1, one_mul] at this

lemma X_mul_X_mem_J {p q : ℕ} (hpq : 1 ≤ p + q) :
    (X (true, p) * X (false, q) : MvPolynomial (Bool × ℕ) ℝ) ∈ J p q := by
  have hrel := rel_mem_J (p := p) (q := q) hpq
  have hp : p ∈ Finset.range (p + q + 1) := Finset.mem_range.2 (by omega)
  rw [rel, ← Finset.add_sum_erase _ _ hp] at hrel
  have hrest : (∑ a ∈ (Finset.range (p + q + 1)).erase p,
      C ((-1 : ℝ) ^ (p + q - a)) * X (true, a) * X (false, p + q - a)) ∈ J p q := by
    refine Ideal.sum_mem _ fun a ha => ?_
    have hap := Finset.ne_of_mem_erase ha
    rcases lt_or_gt_of_ne hap with h | h
    · exact (J p q).mul_mem_left _ (X_false_mem_J (by omega))
    · exact (J p q).mul_mem_right _ ((J p q).mul_mem_left _ (X_true_mem_J h))
  have := (J p q).sub_mem hrel hrest
  rw [add_sub_cancel_right, Nat.add_sub_cancel_left, mul_assoc] at this
  exact mem_of_neg_one_pow_mul q this

lemma sub_C_eval_mem {I : Ideal (MvPolynomial (Bool × ℕ) ℝ)} (v : Bool × ℕ → ℝ)
    (hv : ∀ y, X y - C (v y) ∈ I) (P : MvPolynomial (Bool × ℕ) ℝ) : P - C (eval v P) ∈ I := by
  refine MvPolynomial.induction_on (motive := fun P => P - C (eval v P) ∈ I) P (fun a => ?_) (fun P Q hP hQ => ?_) (fun P y hP => ?_)
  · simp
  · have := I.add_mem hP hQ
    convert this using 1
    simp only [map_add]; ring
  · have := I.add_mem (I.mul_mem_right (X y) hP) (I.mul_mem_left (C (eval v P)) (hv y))
    convert this using 1
    simp only [map_mul, eval_X]; ring

lemma X_false_mem_J_zero {q k : ℕ} (hk : 1 ≤ k) : (X (false, k) : MvPolynomial (Bool × ℕ) ℝ) ∈ J 0 q := by
  have hrel := rel_mem_J (p := 0) (q := q) hk
  rw [rel, Finset.sum_range_succ'] at hrel
  have hrest : (∑ i ∈ Finset.range k,
      C ((-1 : ℝ) ^ (k - (i + 1))) * X (true, i + 1) * X (false, k - (i + 1))) ∈ J 0 q :=
    Ideal.sum_mem _ fun i _ => (J 0 q).mul_mem_right _ ((J 0 q).mul_mem_left _ (X_true_mem_J (by omega)))
  have h0 := (J 0 q).sub_mem hrel hrest
  rw [add_sub_cancel_left, Nat.sub_zero] at h0
  have h1 := (J 0 q).sub_mem h0
    ((J 0 q).mul_mem_right (C ((-1 : ℝ) ^ k) * X (false, k)) (X_zero_sub_one_mem_J true))
  refine mem_of_neg_one_pow_mul k ?_
  convert h1 using 1
  ring

lemma X_true_mem_J_zero {p k : ℕ} (hk : 1 ≤ k) : (X (true, k) : MvPolynomial (Bool × ℕ) ℝ) ∈ J p 0 := by
  have hrel := rel_mem_J (p := p) (q := 0) hk
  rw [rel, Finset.sum_range_succ] at hrel
  have hrest : (∑ a ∈ Finset.range k,
      C ((-1 : ℝ) ^ (k - a)) * X (true, a) * X (false, k - a)) ∈ J p 0 :=
    Ideal.sum_mem _ fun a ha => (J p 0).mul_mem_left _ (X_false_mem_J (by simp at ha; omega))
  have h0 := (J p 0).sub_mem hrel hrest
  rw [add_sub_cancel_left, Nat.sub_self, pow_zero, C_1, one_mul] at h0
  have h1 := (J p 0).sub_mem h0 ((J p 0).mul_mem_left (X (true, k)) (X_zero_sub_one_mem_J false))
  convert h1 using 1
  ring

lemma hv_zero_left (q : ℕ) (y : Bool × ℕ) :
    X y - C (if y.2 = 0 then (1 : ℝ) else 0) ∈ J 0 q := by
  obtain ⟨b, k⟩ := y
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using X_zero_sub_one_mem_J (p := 0) (q := q) b
  · simp only [show k ≠ 0 by omega, if_false, C_0, sub_zero]
    cases b
    · exact X_false_mem_J_zero hk
    · exact X_true_mem_J hk

lemma hv_zero_right (p : ℕ) (y : Bool × ℕ) :
    X y - C (if y.2 = 0 then (1 : ℝ) else 0) ∈ J p 0 := by
  obtain ⟨b, k⟩ := y
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using X_zero_sub_one_mem_J (p := p) (q := 0) b
  · simp only [show k ≠ 0 by omega, if_false, C_0, sub_zero]
    cases b
    · exact X_false_mem_J hk
    · exact X_true_mem_J_zero hk

lemma base_left (q : ℕ) (h : MvPolynomial (Bool × ℕ) ℝ) :
    h ∈ (J 0 q).restrictScalars ℝ ⊔ Submodule.span ℝ (basis 0 q) := by
  have h1 := sub_C_eval_mem (fun y => if y.2 = 0 then (1 : ℝ) else 0) (hv_zero_left q) h
  set c := eval (fun y : Bool × ℕ => if y.2 = 0 then (1 : ℝ) else 0) h
  have hpow : (1 : MvPolynomial (Bool × ℕ) ℝ) - X (true, 0) ^ q ∈ J 0 q := by
    obtain ⟨d, hd⟩ := sub_dvd_pow_sub_pow (X (true, 0) : MvPolynomial (Bool × ℕ) ℝ) 1 q
    rw [one_pow] at hd
    have := (J 0 q).mul_mem_right d (X_zero_sub_one_mem_J true)
    rw [← hd] at this
    simpa using (J 0 q).neg_mem this
  have hdecomp : h = (h - C c + C c * (1 - X (true, 0) ^ q)) + c • X (true, 0) ^ q := by
    rw [smul_eq_C_mul]; ring
  rw [hdecomp]
  refine Submodule.add_mem _ (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right ?_)
  · rw [Submodule.restrictScalars_mem]
    exact (J 0 q).add_mem h1 ((J 0 q).mul_mem_left _ hpow)
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr rfl))

lemma base_right (p : ℕ) (h : MvPolynomial (Bool × ℕ) ℝ) :
    h ∈ (J p 0).restrictScalars ℝ ⊔ Submodule.span ℝ (basis p 0) := by
  have h1 := sub_C_eval_mem (fun y => if y.2 = 0 then (1 : ℝ) else 0) (hv_zero_right p) h
  set c := eval (fun y : Bool × ℕ => if y.2 = 0 then (1 : ℝ) else 0) h
  have hdecomp : h = (h - C c) + c • X (true, p) ^ 0 := by
    rw [pow_zero, smul_eq_C_mul, mul_one]; ring
  rw [hdecomp]
  refine Submodule.add_mem _ (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right ?_)
  · rwa [Submodule.restrictScalars_mem]
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr rfl))

lemma J_le_succ_left (p q : ℕ) :
    J p q ≤ J (p + 1) q ⊔ Ideal.span {(X (true, p + 1) : MvPolynomial (Bool × ℕ) ℝ)} := by
  refine Ideal.span_le.2 ?_
  rintro f (⟨k, hk, rfl⟩ | ⟨b, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩)
  · exact Ideal.mem_sup_left (rel_mem_J hk)
  · exact Ideal.mem_sup_left (X_zero_sub_one_mem_J b)
  · rcases Nat.lt_or_ge (p + 1) k with h | h
    · exact Ideal.mem_sup_left (X_true_mem_J h)
    · obtain rfl : k = p + 1 := by omega
      exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  · exact Ideal.mem_sup_left (X_false_mem_J hk)

lemma J_le_succ_right (p q : ℕ) :
    J p q ≤ J p (q + 1) ⊔ Ideal.span {(X (false, q + 1) : MvPolynomial (Bool × ℕ) ℝ)} := by
  refine Ideal.span_le.2 ?_
  rintro f (⟨k, hk, rfl⟩ | ⟨b, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩)
  · exact Ideal.mem_sup_left (rel_mem_J hk)
  · exact Ideal.mem_sup_left (X_zero_sub_one_mem_J b)
  · exact Ideal.mem_sup_left (X_true_mem_J hk)
  · rcases Nat.lt_or_ge (q + 1) k with h | h
    · exact Ideal.mem_sup_left (X_false_mem_J h)
    · obtain rfl : k = q + 1 := by omega
      exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)

lemma wt_add_single (d : Bool × ℕ →₀ ℕ) (y : Bool × ℕ) :
    wt (d + Finsupp.single y 1) = wt d + y.2 := by
  unfold wt
  rw [Finsupp.sum_add_index' (fun _ => mul_zero _) (fun _ _ _ => mul_add _ _ _),
    Finsupp.sum_single_index (mul_zero _), mul_one]

lemma wt_single (y : Bool × ℕ) (n : ℕ) : wt (Finsupp.single y n) = y.2 * n := by
  unfold wt
  rw [Finsupp.sum_single_index (mul_zero _)]

lemma basis_subset_succ_left (p q : ℕ) : basis p (q + 1) ⊆ basis (p + 1) (q + 1) := by
  rintro f (⟨d, hd, rfl⟩ | rfl)
  · exact Or.inl ⟨d, lt_of_lt_of_le hd (Nat.mul_le_mul_right _ (Nat.le_succ p)), rfl⟩
  · refine Or.inl ⟨Finsupp.single (true, p) (q + 1), ?_, X_pow_eq_monomial⟩
    rw [wt_single]
    show p * (q + 1) < (p + 1) * (q + 1)
    nlinarith

lemma X_mul_span_basis (p q : ℕ) {s : MvPolynomial (Bool × ℕ) ℝ}
    (hs : s ∈ Submodule.span ℝ (basis (p + 1) q)) :
    X (true, p + 1) * s ∈ Submodule.span ℝ (basis (p + 1) (q + 1)) := by
  induction hs using Submodule.span_induction with
  | mem x hx =>
    apply Submodule.subset_span
    rcases hx with ⟨d, hd, rfl⟩ | rfl
    · refine Or.inl ⟨d + Finsupp.single (true, p + 1) 1, ?_, ?_⟩
      · rw [wt_add_single]
        show wt d + (p + 1) < (p + 1) * (q + 1)
        nlinarith
      · rw [add_comm d, monomial_single_add, pow_one]
    · exact Or.inr (by rw [pow_succ'])
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ a hx

lemma X_mul_mem (p q : ℕ) (f : MvPolynomial (Bool × ℕ) ℝ)
    (hf : f ∈ (J (p + 1) q).restrictScalars ℝ ⊔ Submodule.span ℝ (basis (p + 1) q)) :
    X (true, p + 1) * f ∈
      (J (p + 1) (q + 1)).restrictScalars ℝ ⊔ Submodule.span ℝ (basis (p + 1) (q + 1)) := by
  obtain ⟨j, hj, s, hs, rfl⟩ := Submodule.mem_sup.1 hf
  rw [mul_add]
  refine Submodule.add_mem _ (Submodule.mem_sup_left ?_)
    (Submodule.mem_sup_right (X_mul_span_basis p q hs))
  rw [Submodule.restrictScalars_mem] at hj ⊢
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (J_le_succ_right (p + 1) q hj)
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hb
  have hXX := X_mul_X_mem_J (p := p + 1) (q := q + 1) (by omega)
  have : X (true, p + 1) * (a + c * X (false, q + 1)) =
      X (true, p + 1) * a + c * (X (true, p + 1) * X (false, q + 1)) := by ring
  rw [this]
  exact (J _ _).add_mem ((J _ _).mul_mem_left _ ha) ((J _ _).mul_mem_left _ hXX)

theorem mem_rel_sup_span_low_or_top : ∀ (p q : ℕ) (h : MvPolynomial (Bool × ℕ) ℝ),
    h ∈ (J p q).restrictScalars ℝ ⊔ Submodule.span ℝ (basis p q) := by
  intro p
  induction p with
  | zero => exact base_left
  | succ p ihp =>
    intro q
    induction q with
    | zero => exact base_right (p + 1)
    | succ q ihq =>
      intro h
      obtain ⟨j, hj, s, hs, rfl⟩ := Submodule.mem_sup.1 (ihp (q + 1) h)
      rw [Submodule.restrictScalars_mem] at hj
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (J_le_succ_left p (q + 1) hj)
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hb
      refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.mem_sup_left ?_) ?_)
        (Submodule.mem_sup_right ?_)
      · rwa [Submodule.restrictScalars_mem]
      · rw [mul_comm]; exact X_mul_mem p q c (ihq c)
      · exact Submodule.span_mono (basis_subset_succ_left p q) hs

end GlobalTheory.GrassTop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemLevelIffUnipotentAtTypePlace
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section

namespace GlobalTheory.LevUniLoc

theorem mem_iff_uniRT : ∀ (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
    (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (e : ℤ) (W₀ : Type) [AddCommGroup W₀] [Module (FractionRing (D.ntw.O i)) W₀]
    (ρ₀ : Representation (FractionRing (D.ntw.O i)) (GQ D.host.E D.R.nV) W₀)
    (τ : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ)
    (M : NX.MtVReal D i j b k Q ψ e W₀ ρ₀ τ) (kv0 : Σ kk : Fin 2, D.nd.PlG kk),
    (∀ kv, kv ≠ kv0 → (M.sp (NX.pG D kv)).v ≠ (M.sp (NX.pG D kv0)).v) →
    (∀ P ∈ M.QP, (M.sp P).v ≠ (M.sp (NX.pG D kv0)).v) → (∀ P ∈ M.DP, (M.sp P).v ≠ (M.sp (NX.pG D kv0)).v) →
    ∀ κ, TrivOutside {(M.sp (NX.pG D kv0)).v} κ →
      (κ ∈ M.J ↔ NG.UniRT (M.sp (NX.pG D kv0)) D.R.r ((M.sp (NX.pG D kv0)).loc D.R.nV κ)) := by
  intro D i j b k Q ψ e W₀ _ _ ρ₀ τ M kv0 hG hQ hD κ hκ
  rw [M.J_mem κ]
  constructor
  · rintro ⟨hU, hL, -, -⟩
    obtain ⟨⟨_, hll⟩, huni⟩ := hL kv0
    exact ⟨⟨(GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff _ hκ).2 hU, hll⟩, huni⟩
  · rintro ⟨⟨hGL, hll⟩, huni⟩
    refine ⟨(GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff _ hκ).1 hGL, fun kv => ?_, fun P hP => ?_, fun P hP => ?_⟩
    · by_cases hk : kv = kv0
      · subst hk
        exact ⟨⟨fun a b => (GlobalTheory.HeckeScalarSph.mem_GLint_iff.1 hGL).1 a b, hll⟩, huni⟩
      · rw [GlobalTheory.LevParaLoc.locM_eq_one_of_ne _ _ hκ (hG kv hk)]; exact NX.inLevG_one _ _
    · rw [GlobalTheory.LevParaLoc.locM_eq_one_of_ne _ _ hκ (hQ P hP)]; exact NX.inParah_one _ _
    · rw [GlobalTheory.LevParaLoc.locM_eq_one_of_ne _ _ hκ (hD P hP)]; exact NX.inParah_one _ _

end GlobalTheory.LevUniLoc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemParahoricOfScalarActionOnRamifiedParahoricForStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_parahoric_of_scalar_action_on_ramifiedParahoricForm : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (r : ℕ) (s : SplitPlace L) (V : Type) [AddCommGroup V] [Module ℂ V] (F : GAf L n → V) (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (a : s.v.adicCompletion (maximalRealSubfield L)), F ≠ 0 → Valued.v a = 1 → (∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ NG.ParaRT s r (s.loc n κ))) → (∀ κ : J, Eig F κ (χ κ : ℂˣ)) → (∀ κ (h : κ ∈ J), TrivOutside {s.v} κ → NG.detDD s r (s.loc n κ) = 1 → χ ⟨κ, h⟩ = 1) → (∀ κ (h : κ ∈ J), TrivOutside {s.v} κ → NG.detDD s r (s.loc n κ) = a → χ ⟨κ, h⟩ ≠ 1) → ∀ κ ∈ Umax L n, TrivOutside {s.v} κ → (∃ c, Eig F κ c) → NG.ParaRT s r (s.loc n κ) := by
  first | exact @GlobalTheory.ParaRigid.mem_para_of_eig | exact GlobalTheory.ParaRigid.mem_para_of_eig | (intros; apply GlobalTheory.ParaRigid.mem_para_of_eig <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemberPreservedLargeGrid
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.LiteralAutomorphy

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {N : NExt hL} {S : SExt} {Γ : GeoP} {A : AtP}

def builtA_drop {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {c : V4.Core K (w.st Z) f T}
    (b : Built (prmR (NEa hL N A) S Γ).s K w Z c) : Built (prmR N S Γ).s K w Z c :=
  { b with nx := ⟨b.nx.1, b.nx.2.1⟩ }

def builtA_add {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {c : V4.Core K (w.st Z) f T}
    (b : Built (prmR N S Γ).s K w Z c) (a : A K B f T) : Built (prmR (NEa hL N A) S Γ).s K w Z c :=
  { b with nx := ⟨b.nx.1, b.nx.2, PLift.up a⟩ }

theorem isBuiltE_prmA_iff (K X f T c) :
    IsBuiltE (prmR (NEa hL N A) S Γ).s K X f T c ↔ IsBuiltE (prmR N S Γ).s K X f T c ∧ A K X.B f T := by
  constructor
  · rintro ⟨w, Z, c', ⟨b, hb⟩, he⟩
    exact ⟨⟨w, Z, c', ⟨builtA_drop b, hb⟩, he⟩, b.nx.2.2.down⟩
  · rintro ⟨⟨w, Z, c', ⟨b, hb⟩, he⟩, a⟩
    exact ⟨w, Z, c', ⟨builtA_add b a, hb⟩, he⟩

theorem isGoodE_prmA_iff (K X f T c) :
    IsGoodE (prmR (NEa hL N A) S Γ).s K X f T c ↔ IsGoodE (prmR N S Γ).s K X f T c ∧ A K X.B f T := by
  constructor
  · rintro ⟨w, Z, c', ⟨⟨b, hb⟩, g⟩, he⟩
    exact ⟨⟨w, Z, c', ⟨⟨builtA_drop b, hb⟩, g⟩, he⟩, b.nx.2.2.down⟩
  · rintro ⟨⟨w, Z, c', ⟨⟨b, hb⟩, g⟩, he⟩, a⟩
    exact ⟨w, Z, c', ⟨⟨builtA_add b a, hb⟩, g⟩, he⟩

theorem memberE_prmR_NEa : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (S : SExt) (Γ : GeoP) (A : AtP), EvLgG A →
    MemberE (prmR N S Γ).s → MemberE (prmR (NEa hL N A) S Γ).s := by
  intro hL N S Γ A hA ⟨hB, h1, hE, h2⟩
  refine ⟨hB, ?_, ?_, ?_⟩
  · have h := Step.and (KP := KPx) h1 (Step.of_evLgG (p := fun _ B _ T => T = TwDat.untw B T.pl) hA)
    refine EvG.imp h fun K _ _ _ _ H => H.imp fun B f T _ G k u v => ?_
    obtain ⟨⟨C, W, V, S, N, Gs, c, q⟩, a⟩ := G k u v
    exact ⟨C, W, V, S, N, Gs, c, (isBuiltE_prmA_iff K ⟨B, C, W, V, S, N, Gs⟩ f T c).2 ⟨q, a⟩⟩
  · exact EvG.imp hE fun K _ _ _ _ H => H.imp fun B f T _ G k u C W V S N Gs c q =>
      G k u C W V S N Gs c ((isBuiltE_prmA_iff K ⟨B, C, W, V, S, N, Gs⟩ f T c).1 q).1
  · have hR : LargeBaseConditionG KPx (IsBuiltE (prmR N S Γ).s) (fun K X f T _ => A K X.B f T) :=
      EvG.imp hA fun K _ _ _ _ H => H.imp fun B f T _ a _ C W V S N Gs c _ => a
    have h2' := SecondG.sAnd_of_largeBase KPx _ _ _ hB hR h2
    refine EvG.imp h2' fun K _ _ _ _ H => H.imp fun B f T _ G k u C W V S N Gs c q e Av S₂ hS₂ => ?_
    obtain ⟨B', f', T', a1, a2, a3, a4, a5, C', W', V', S', N', G', c', q', tw, g', a⟩ :=
      G k u C W V S N Gs c ((isBuiltE_prmA_iff K ⟨B, C, W, V, S, N, Gs⟩ f T c).1 q).1 e Av S₂ hS₂
    exact ⟨B', f', T', a1, a2, a3, a4, a5, C', W', V', S', N', G', c',
      (isBuiltE_prmA_iff K ⟨B', C', W', V', S', N', G'⟩ f' T' c').2 ⟨q', a⟩, tw,
      (isGoodE_prmA_iff K ⟨B', C', W', V', S', N', G'⟩ f' T' c').2 ⟨g', a⟩⟩

end GlobalTheory.Mem.LiteralAutomorphy
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MovedEqDatTw
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.Mem.R3

theorem dat_ext_heq {X : Stages} {px : PreX X.B.toPre} {I : Col2.ColIn X.B px} {hX : X.B.fields.Ok} {T : Top.TwDat X.B}
    {Wt : Set X.B.places.Pl} {d₁ d₂ : Dat X I hX T Wt} (hXg : d₁.Xg = d₂.Xg) (htr : d₁.tr = d₂.tr)
    (hcore : d₁.core = d₂.core) (hR : HEq d₁.R d₂.R) (hcG : HEq d₁.cG d₂.cG) (hgeo : HEq d₁.geo d₂.geo) : d₁ = d₂ := by
  cases d₁ with
  | @mk Xg tr core alg alg_eq R cG geo pins lev idG good mu fieldValues_mem_fixedField Ks_le =>
  cases d₂ with
  | @mk Xg' tr' core' alg' alg_eq' R' cG' geo' pins' lev' idG' good' mu' le_LL0' Ks_le' =>
  dsimp only at hXg htr hcore hR hcG hgeo
  subst hXg htr hcore
  have halg : alg = alg' := Algebra.algebra_ext _ _ fun y => X.B.embLL.injective ((alg_eq y).trans (alg_eq' y).symm)
  subst halg
  cases eq_of_heq hR
  cases eq_of_heq hcG
  cases eq_of_heq hgeo
  rfl

end GlobalTheory.Mem.R3

namespace GlobalTheory.HeightCounting.Up
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.R3.Rw

theorem coreJ_coreJ {B : Base} {C : Cols B} {a : Late B C} (b c : Late B C) (T : Formalism.L2.Pj.CoreJ a.D) :
    coreJ (a := b) c (coreJ b T) = coreJ c T := (by with_unfolding_all exact ((Eq.refl (coreJ c T)) :))

theorem moved_eq_datTw : ∀ {K : GlobalTheory.Mem.Top.Ctx} {B : GlobalTheory.Mem.Base} {f : GlobalTheory.Mem.Top.Fr B.toPre} {T : GlobalTheory.Mem.Top.TwDat B} {w : GlobalTheory.Mem.Top.Bl.ColW B f T} {P : GlobalTheory.Mem.R3.Rw.Pre2 K w} (x : GlobalTheory.Mem.R3.Rw.St P) (N : TwNew (GlobalTheory.HeightCounting.Up.Dof x)) (m : GlobalTheory.Mem.R3.Rw.Moved (GlobalTheory.HeightCounting.Up.oTw x N)), m.Copy → HEq m.z.R (GlobalTheory.Mem.R3.Tr.real3 (a := x.o.Z) (GlobalTheory.HeightCounting.Up.oTw x N).Z (iK := x.m.z.alg) x.m.z.R) → HEq m.z.cG x.m.z.cG → HEq m.z.geo (GlobalTheory.Mem.R3.Tr.geoHalf (a := x.o.Z) (GlobalTheory.HeightCounting.Up.oTw x N).Z (iK := x.m.z.alg) x.m.z.geo) → m.z = GlobalTheory.HeightCounting.Up.datTw x N := by
  intro K B f T w P x N m hc hR hcG hgeo
  have h1 : x.m.z.core = coreJ (a := P.Z₀) x.o.Z P.z.core := (by with_unfolding_all exact ((eq_of_heq x.copy.core) :))
  have h2 : m.z.core = coreJ (a := P.Z₀) (oTw x N).Z P.z.core := (by with_unfolding_all exact ((eq_of_heq hc.core) :))
  have h3 : coreJ (a := x.o.Z) (oTw x N).Z x.m.z.core = coreJ (a := P.Z₀) (oTw x N).Z P.z.core :=
    (congrArg (coreJ (a := x.o.Z) (oTw x N).Z) h1).trans (coreJ_coreJ _ _ _)
  have h4 : HEq (datTw x N).cG x.m.z.cG := (by with_unfolding_all exact ((HEq.refl x.m.z.cG) :))
  exact dat_ext_heq (d₁ := m.z) (d₂ := datTw x N) ((by with_unfolding_all exact ((m.Xg.trans x.m.Xg.symm) :))) ((by with_unfolding_all exact ((m.tr.trans x.m.tr.symm) :)))
    ((by with_unfolding_all exact ((h2.trans h3.symm) :))) ((by with_unfolding_all exact (hR :))) (hcG.trans h4.symm) ((by with_unfolding_all exact (hgeo :)))

end GlobalTheory.HeightCounting.Up
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyAgreeRealOfReadGaloisStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.HeightCounting.Up.RealOfReading

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_agree_real_of_read_galois : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ T w Z Wt _ t nch n c => ∀ (hC : t.r.z.R.C = TC.cf w.I w.l Z) (Xd : DivX (w.D Z)) (E : EigIdx (w.D Z) Xd) (labPi : E.Pi → (famR (w.st Z) w.I t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr).A.fam.base.Ix) hb htup hg hf, Nonempty (GlobalTheory.NJoin.Agree (realOfRead t.r.z.R.toRealDat t.r.z.F.lv2 t.r.Y n.tp hC Xd E labPi hb htup hg hf) c.a.all.gal.mt (realOfRead t.r.z.R.toRealDat t.r.z.F.lv2 t.r.Y n.tp hC Xd E labPi hb htup hg hf).rep) := by
  first | exact @GlobalTheory.HeightCounting.Up.StandardFrameAgreement.agree_of_layer | exact GlobalTheory.HeightCounting.Up.StandardFrameAgreement.agree_of_layer | (intros; apply GlobalTheory.HeightCounting.Up.StandardFrameAgreement.agree_of_layer <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormFieldSquareClass
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.LiteralAutomorphy

theorem nfSq_of_fieldDat : GlobalTheory.NormSum.IntSt → GlobalTheory.SqTop.FieldDat → GlobalTheory.SqTop.TorEx → GlobalTheory.SqTop.BotSmall → NFSq := by
  intro hI hFD hTE hBS
  obtain ⟨CF0, h⟩ := GlobalTheory.SqTop.SqField.gBig_and hFD (GlobalTheory.SqTop.SqField.gBig_and hTE hBS)
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x₀, h⟩ := h ε CF hCF
  refine ⟨x₀, fun D large₂ he hx hR T L μ₀ hμ G => ?_⟩
  obtain ⟨⟨_, _, _, _, hΛ⟩, hT, hQ, -, hB⟩ := h C0 le_rfl D large₂ he hx hR T L μ₀ hμ G
  exact GlobalTheory.SqTop.SqField.sqIn_of G μ₀ hI hΛ
    (fun i j s h1 h2 c => let ⟨x, a, b, _, d⟩ := hT i j s h1 h2 c; ⟨x, a, b, d⟩) hQ hB

end GlobalTheory.Mem.LiteralAutomorphy

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormalisedSubgroupColumnMatricesEntryZeroStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.HeightCounting GlobalTheory.CenFrame
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalised_subgroup_column_matrices_entry_zero : ∀ (k : Type) [CommRing k], IsField k → ∀ n r : ℕ, 2 ≤ r → r < n → ∀ (H : Subgroup (GL (Fin n) k)) (b : GL (Fin n) k), (∀ u ∈ unip k n, ∀ h ∈ H, u * h * u⁻¹ ∈ H) → (∀ (h : GL (Fin n) k) (m : Fin n) (v : Fin n → k), r ≤ (m : ℕ) → v m = 0 → h.val = colMat v m → h ∈ H) → (∀ (h : GL (Fin n) k) (m : Fin n) (v : Fin n → k), r ≤ (m : ℕ) → v m = 0 → (b * h * b⁻¹).val = colMat v m → h ∈ H) → (∀ i j : Fin n, (i : ℕ) + 1 = j → (j : ℕ) < r → ∃ (c : k) (h : GL (Fin n) k), h.val = Matrix.transvection i j c ∧ h ∉ H) → ∀ a c : Fin n, r ≤ (a : ℕ) → (c : ℕ) < r → b.val a c = 0 := by
  first | exact @GlobalTheory.PosAgree.entry_zero | exact GlobalTheory.PosAgree.entry_zero | (intros; apply GlobalTheory.PosAgree.entry_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrthonormalFramesLieCoordinatesUnitaryStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.ShFam
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthonormalFrames_lie_coordinates_unitary : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ r}, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (k : U.Comp) (x x₁ : (U.X k).dom), IsOrth (U.X k) x.1 → IsOrth (U.X k) x₁.1 → (U.un k x₁).x = (U.un k x).x → ∀ (τ : E →+* ℂ) (T : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ), (∀ b, Formalism.L2.Pj.IsCombAt (U.un k x).x ((U.un k x).u τ) (show Fin (Dw.mult τ) → CAt σ from fun b' => (T b' b : ℂ)) ((U.un k x₁).u τ b)) → Tᴴ * T = 1 := by
  first | exact @GlobalTheory.ShFam.lie_coord_unitary | exact GlobalTheory.ShFam.lie_coord_unitary | (intros; apply GlobalTheory.ShFam.lie_coord_unitary <;> assumption)
end

