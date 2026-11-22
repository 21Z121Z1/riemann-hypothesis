import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2577
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2573
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2578
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2410
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2672
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2670
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0587
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2416
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2505
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2569
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2545

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeTwoObstructionClassNaturalStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degreeTwoObstructionClass_natural : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (C₂ : Type) [Category.{0} C₂] (F₂ : C₂ ⥤ CommAlgCat.{0} R₀) (C' : Type) [Category.{0} C'] (G : C' ⥤ C₂) (n : CoefMap (RingHom.id R₀) F (G ⋙ F₂)) (L : Pre I π F) (L₂ : Pre I π F₂) (w : Glob1 F) (w₂ : Glob1 F₂) (c : GlobalTheory.CatCoh.H2 (ext R₁ F)) (c₂ : GlobalTheory.CatCoh.H2 (ext R₁ F₂)), (∀ T, q1 n T (w.1 _) = w₂.1 (G.obj T)) → L.IsOb2 α w c → L₂.IsOb2 α w₂ c₂ → (extMap R₁ n).pull2 c = (extMap R₁ (CoefMap.restrict F₂ G)).pull2 c₂ := by
  first | exact @GlobalTheory.Obs.isOb2_natural | exact GlobalTheory.Obs.isOb2_natural | (intros; apply GlobalTheory.Obs.isOb2_natural <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationHomotopyOperatorFiltrationProperties
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm.HotFil

theorem hot_fil : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B) (δ : DividedPowers J) (v : Derivation R B B) (e : ℕ → B) (N : ℕ), (∀ n, ∀ a ∈ J, v (δ.dpow (n + 1) a) = δ.dpow n a * v a) → (∀ k, e k ∈ fil δ k) → (∀ x y, hot v e N (x + y) = hot v e N x + hot v e N y) ∧ (∀ b, hot v e N (algebraMap B (DR R B) b) = 0) ∧ (∀ (j : ℕ), ∀ x ∈ ⋀[B]^(j + 1) Ω[B⁄R], hot v e N x ∈ ⋀[B]^j Ω[B⁄R]) ∧ (∀ x ∈ rel R δ, hot v e N x ∈ rel R δ) ∧ ∀ n, ∀ x ∈ filDR R δ n, hot v e N x ∈ filDR R δ (n + 1) := by
  intro R B _ _ _ J δ v e N hv he
  obtain ⟨hc0, -, -, -, -, hcdeg⟩ := (GlobalTheory.T.derivationContraction_lieDerivative_deRham_rules).1 R B v
  obtain ⟨-, -, -, -, -, hldeg⟩ := (GlobalTheory.T.derivationContraction_lieDerivative_deRham_rules).2 R B v
  have hrel := (GlobalTheory.T.contraction_lieDerivative_divPowerCompat_filtration_rules).1
  have hfil := (GlobalTheory.T.contraction_lieDerivative_divPowerCompat_filtration_rules).2
  obtain ⟨-, -, -, -, hfil0, hanti, hsmul⟩ := (GlobalTheory.T.divPowerCompatRel_filtration_twoSided_rel_eq_bot_of_base).1 R B J δ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    simp only [hot, map_add, smul_add, Finset.sum_add_distrib]
  · intro b
    simp only [hot, hc0, map_zero, smul_zero, Finset.sum_const_zero]
  · intro j x hx
    have hc := hcdeg j x hx
    have hk : ∀ k, (lie v ^ k) (ctr v x) ∈ ⋀[B]^j Ω[B⁄R] := by
      intro k
      induction k with
      | zero => simpa using hc
      | succ k ih =>
        rw [pow_succ', Module.End.mul_apply]
        exact hldeg j _ ih
    exact Submodule.sum_mem _ fun k _ ↦ Submodule.smul_mem _ _ (hk k)
  · intro x hx
    have hc := (hrel R B J δ v hv x hx).1
    have hk : ∀ k, (lie v ^ k) (ctr v x) ∈ rel R δ := by
      intro k
      induction k with
      | zero => simpa using hc
      | succ k ih =>
        rw [pow_succ', Module.End.mul_apply]
        exact (hrel R B J δ v hv _ ih).2
    refine Ideal.sum_mem _ fun k _ ↦ ?_
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (hk k)
  · intro n x hx
    have hc := (hfil R B J δ v hv n).1 x hx
    have hk : ∀ k, (lie v ^ k) (ctr v x) ∈ filDR R δ (n - k) := by
      intro k
      induction k with
      | zero => simpa using hc
      | succ k ih =>
        rw [pow_succ', Module.End.mul_apply]
        rcases Nat.eq_zero_or_pos (n - k) with h0 | hpos
        · have : n - (k + 1) = 0 := by omega
          rw [this, hfil0]
          exact Submodule.mem_top
        · have h1 : n - k = (n - (k + 1)) + 1 := by omega
          rw [h1] at ih
          exact (hfil R B J δ v hv (n - (k + 1))).2.2 _ ih
    refine Ideal.sum_mem _ fun k _ ↦ ?_
    have hek : (-1) ^ k * e (k + 1) ∈ fil δ (k + 1) := Ideal.mul_mem_left _ _ (he (k + 1))
    exact hanti (n + 1) ((k + 1) + (n - k)) (by omega) (hsmul (k + 1) (n - k) _ hek _ (hk k))

end GlobalTheory.PDForm.HotFil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationTaylorPowerSeriesInjectiveLocalRing
section
open IsLocalRing GlobalTheory.FormalOrigin MvPowerSeries

noncomputable section
namespace GlobalTheory.TaylorInj

theorem foldr_ite {A : Type} {n : ℕ} (D : A → A) (a : Fin n) (f : A) (l : List (Fin n)) :
    l.foldr (fun i g => if i = a then D g else g) f = D^[l.count a] f := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.foldr_cons, ih, List.count_cons]
    by_cases h : i = a
    · subst h; simp [Function.iterate_succ_apply']
    · simp [h]

theorem iterOp_single {A : Type} {n : ℕ} (ds : Fin n → A → A) (a : Fin n) (f : A) :
    iterOp ds (Finsupp.single a 1) f = ds a f := by
  have e : (fun i g => (ds i)^[Finsupp.single a 1 i] g) = (fun i g => if i = a then ds a g else g) := by
    funext i g
    by_cases h : i = a
    · subst h; simp
    · simp [Finsupp.single_apply, Ne.symm h, h]
  unfold iterOp
  rw [e, foldr_ite, List.count_eq_one_of_mem (List.nodup_finRange n) (List.mem_finRange a)]
  rfl

theorem coeff_taylor {A B : Type} [CommRing A] [CommRing B] [Algebra ℚ B] {n : ℕ} (ev : A →+* B)
    (ds : Fin n → A → A) (f : A) (α : Fin n →₀ ℕ) :
    coeff α (taylor ev ds f) = (∏ i, ((α i).factorial : ℚ))⁻¹ • ev (iterOp ds α f) := rfl

theorem degree_eq_one {n : ℕ} {D : Fin n →₀ ℕ} (h : D.degree = 1) : ∃ s, D = Finsupp.single s 1 := by
  have hsum := h
  rw [Finsupp.degree_eq_sum] at hsum
  obtain ⟨s, hs⟩ : ∃ s, D s ≠ 0 := by
    by_contra hc
    push_neg at hc
    simp [hc] at hsum
  refine ⟨s, ?_⟩
  have hle : ∀ t, t ≠ s → D s + D t ≤ 1 := fun t ht => by
    rw [← hsum, ← Finset.sum_pair (Ne.symm ht)]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  ext t
  by_cases ht : t = s
  · subst ht
    have : D t ≤ 1 := h ▸ Finsupp.le_degree t D
    simp only [Finsupp.single_eq_same]
    omega
  · have := hle t ht
    simp only [Finsupp.single_apply, if_neg (Ne.symm ht)]
    omega

section Rel
variable {σ S : Type} [CommRing S]

def Rel (e : ℕ) (F G : MvPowerSeries σ S) : Prop :=
  (e : ℕ∞) ≤ G.order ∧ ((e + 1 : ℕ) : ℕ∞) ≤ (F - G).order

theorem le_order_of_rel {e : ℕ} {F G : MvPowerSeries σ S} (h : Rel e F G) : (e : ℕ∞) ≤ F.order := by
  have : F = G + (F - G) := by ring
  rw [this]
  exact le_trans (le_min h.1 (le_trans (by exact_mod_cast Nat.le_succ e) h.2)) min_order_le_add

theorem rel_mul {a b : ℕ} {F G F' G' : MvPowerSeries σ S} (h : Rel a F G) (h' : Rel b F' G') :
    Rel (a + b) (F * F') (G * G') := by
  refine ⟨?_, ?_⟩
  · refine le_trans ?_ le_order_mul
    push_cast; exact add_le_add h.1 h'.1
  · have e : F * F' - G * G' = (F - G) * F' + G * (F' - G') := by ring
    rw [e]
    refine le_trans (le_min ?_ ?_) min_order_le_add
    · refine le_trans ?_ le_order_mul
      refine le_trans (le_of_eq ?_) (add_le_add h.2 (le_order_of_rel h'))
      push_cast; ring
    · refine le_trans ?_ le_order_mul
      refine le_trans (le_of_eq ?_) (add_le_add h.1 h'.2)
      push_cast; ring

theorem rel_one : Rel 0 (1 : MvPowerSeries σ S) 1 := by
  refine ⟨by simp, by simp⟩

theorem rel_pow {a : ℕ} {F G : MvPowerSeries σ S} (h : Rel a F G) (k : ℕ) :
    Rel (a * k) (F ^ k) (G ^ k) := by
  induction k with
  | zero => simpa using (rel_one (σ := σ) (S := S))
  | succ k ih =>
    rw [pow_succ, pow_succ, Nat.mul_succ]
    exact rel_mul ih h

theorem rel_prod_pow {ι : Type} (s : Finset ι) (F G : ι → MvPowerSeries σ S) (β : ι → ℕ)
    (h : ∀ i, Rel 1 (F i) (G i)) :
    Rel (∑ i ∈ s, β i) (∏ i ∈ s, F i ^ β i) (∏ i ∈ s, G i ^ β i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (rel_one (σ := σ) (S := S))
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, Finset.prod_insert hi]
    have := rel_mul (rel_pow (h i) (β i)) ih
    rwa [one_mul] at this

end Rel

theorem ker_le_span {R A : Type} [CommRing R] [IsLocalRing R] [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (inc : R →+* A) (ev : A →+* R) (hev : ∀ r, ev (inc r) = r) {n : ℕ}
    (z : Fin n → A) (hz : ∀ i, ev (z i) = 0)
    (hm : maximalIdeal A = (maximalIdeal R).map inc ⊔ Ideal.span (Set.range z)) :
    RingHom.ker ev ≤ Ideal.span (Set.range z) := by
  set K := RingHom.ker ev
  set J := Ideal.span (Set.range z)
  set I := (maximalIdeal R).map inc
  have hJK : J ≤ K := Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hz i)
  have key : ∀ y ∈ I, y - inc (ev y) ∈ I * K := by
    intro y hy
    refine Submodule.span_induction (p := fun y _ => y - inc (ev y) ∈ I * K) ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨r, -, rfl⟩; simp [hev]
    · simp
    · intro x y _ _ hx hy
      have := Ideal.add_mem _ hx hy
      convert this using 1; simp only [map_add]; ring
    · intro a x hx' hx
      have e : a • x - inc (ev (a • x)) = (a - inc (ev a)) * x + inc (ev a) * (x - inc (ev x)) := by
        simp only [smul_eq_mul, map_mul]; ring
      rw [e]
      refine Ideal.add_mem _ ?_ (Ideal.mul_mem_left _ _ hx)
      rw [mul_comm (a - inc (ev a))]; exact Ideal.mul_mem_mul hx' (RingHom.mem_ker.2 (by simp [hev]))
  have hle : K ≤ J ⊔ I • K := by
    intro x hx
    have hxm : x ∈ maximalIdeal A := by
      rw [mem_maximalIdeal, mem_nonunits_iff]; intro hu
      have := hu.map ev; rw [RingHom.mem_ker.1 hx] at this; exact not_isUnit_zero this
    rw [hm, Submodule.mem_sup] at hxm
    obtain ⟨y, hy, w, hw, rfl⟩ := hxm
    have hw0 : ev w = 0 := hJK hw
    have hy0 : ev y = 0 := by
      have := RingHom.mem_ker.1 hx; rwa [map_add, hw0, add_zero] at this
    have := key y hy
    rw [hy0, map_zero, sub_zero] at this
    rw [add_comm]; exact Submodule.add_mem_sup hw this
  have hIj : I ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, hm]; exact le_sup_left
  exact Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian K) hIj hle

end GlobalTheory.TaylorInj

namespace GlobalTheory.TaylorInj
section Main
variable {R A : Type} [CommRing R] [Algebra ℚ R] [CommRing A] {n : ℕ}

theorem rel_const (ev : A →+* R) (ds : Fin n → A → A) (T : A →+* MvPowerSeries (Fin n) R)
    (hT : ∀ f, T f = taylor ev ds f) (c : A) : Rel 0 (T c) (C (ev c)) := by
  refine ⟨by simp, ?_⟩
  have h0 : constantCoeff (T c) = ev c := by
    rw [← coeff_zero_eq_constantCoeff_apply, hT, coeff_taylor]; simp [iterOp_zero]
  rw [zero_add, Nat.cast_one, one_le_order_iff_constCoeff_eq_zero, map_sub, h0]
  simp

theorem rel_coord (ev : A →+* R) (ds : Fin n → Derivation ℤ A A) (T : A →+* MvPowerSeries (Fin n) R)
    (hT : ∀ f, T f = taylor ev (fun i => ⇑(ds i)) f) (z : Fin n → A) (hz : ∀ i, ev (z i) = 0)
    (hd : ∀ a i, ev (ds a (z i)) = if a = i then 1 else 0) (i : Fin n) :
    Rel 1 (T (z i)) (X i) := by
  refine ⟨?_, ?_⟩
  · exact one_le_order_iff_constCoeff_eq_zero.2 (by simp)
  · refine nat_le_order fun d hd2 => ?_
    rw [map_sub, hT, coeff_taylor]
    by_cases h0 : d.degree = 0
    · rw [(Finsupp.degree_eq_zero_iff d).1 h0]; simp [iterOp_zero, hz]
    · obtain ⟨a, rfl⟩ := degree_eq_one (by omega : d.degree = 1)
      rw [iterOp_single, hd, coeff_X]
      have hf : ∀ j, (((Finsupp.single a 1 : Fin n →₀ ℕ) j).factorial : ℚ) = 1 := by
        intro j; rw [Finsupp.single_apply]; split_ifs <;> simp
      simp only [hf, Finset.prod_const_one, inv_one, one_smul]
      by_cases hai : a = i
      · subst hai; simp
      · simp [hai, Finsupp.single_left_inj (one_ne_zero)]

theorem step (ev : A →+* R) (ds : Fin n → Derivation ℤ A A) (T : A →+* MvPowerSeries (Fin n) R)
    (hT : ∀ f, T f = taylor ev (fun i => ⇑(ds i)) f) (z : Fin n → A) (hz : ∀ i, ev (z i) = 0)
    (hd : ∀ a i, ev (ds a (z i)) = if a = i then 1 else 0)
    (hker : RingHom.ker ev ≤ Ideal.span (Set.range z)) (k : ℕ) (f : A) (hf : T f = 0)
    (hk : f ∈ Ideal.span (Set.range z) ^ k) : f ∈ Ideal.span (Set.range z) ^ (k + 1) := by
  classical
  obtain ⟨p, hp, rfl⟩ := (Ideal.mem_span_pow_iff_exists_isHomogeneous z f).1 hk
  have hdeg : ∀ β ∈ p.support, β.degree = k := by
    intro β hβ
    have := hp (MvPolynomial.mem_support_iff.1 hβ)
    rw [Finsupp.degree_eq_weight_one]; exact this
  have hev : MvPolynomial.eval z p = ∑ β ∈ p.support, p.coeff β * ∏ i, z i ^ β i :=
    MvPolynomial.eval_eq' z p
  have hmon : ∀ (β : Fin n →₀ ℕ) (c : R), C c * ∏ i, (X i : MvPowerSeries (Fin n) R) ^ β i = monomial β c := by
    intro β c
    simp only [X_pow_eq]
    rw [prod_monomial, ← monomial_zero_eq_C_apply, monomial_mul_monomial]
    simp [Finsupp.univ_sum_single]
  set G : MvPowerSeries (Fin n) R := ∑ β ∈ p.support, monomial β (ev (p.coeff β)) with hGdef
  have hrel : ∀ β ∈ p.support,
      Rel k (T (p.coeff β * ∏ i, z i ^ β i)) (monomial β (ev (p.coeff β))) := by
    intro β hβ
    have h := rel_mul (rel_const ev _ T hT (p.coeff β))
      (rel_prod_pow Finset.univ (fun i => T (z i)) X (fun i => β i) (rel_coord ev ds T hT z hz hd))
    rw [zero_add, ← Finsupp.degree_eq_sum, hdeg β hβ, hmon] at h
    rw [map_mul, map_prod]; simp only [map_pow]; exact h
  have hcoef : ∀ α : Fin n →₀ ℕ, α.degree = k →
      coeff α (T (MvPolynomial.eval z p)) = coeff α G := by
    intro α hα
    rw [← sub_eq_zero, ← map_sub, hev, map_sum, hGdef, ← Finset.sum_sub_distrib, map_sum]
    refine Finset.sum_eq_zero fun β hβ => coeff_of_lt_order ?_
    exact lt_of_lt_of_le (by rw [hα]; exact_mod_cast Nat.lt_succ_self k) (hrel β hβ).2
  have hG : ∀ α, coeff α G = ev (p.coeff α) := by
    intro α
    simp only [hGdef, map_sum, coeff_monomial, Finset.sum_ite_eq]
    split_ifs with h
    · rfl
    · rw [MvPolynomial.mem_support_iff, not_not] at h; rw [h, map_zero]
  rw [hev]
  refine Ideal.sum_mem _ fun β hβ => ?_
  rw [pow_succ']
  refine Ideal.mul_mem_mul (hker (RingHom.mem_ker.2 ?_)) ?_
  · rw [← hG, ← hcoef β (hdeg β hβ), hf, map_zero]
  · rw [← hdeg β hβ, Finsupp.degree_eq_sum, ← Finset.prod_pow_eq_pow_sum]
    exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self i)) _

end Main

theorem taylor_injective : ∀ (R A : Type) [CommRing R] [IsLocalRing R] [Algebra ℚ R] [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (inc : R →+* A) (ev : A →+* R), (∀ r, ev (inc r) = r) → ∀ (n : ℕ) (ds : Fin n → Derivation ℤ A A) (z : Fin n → A), (∀ i, ev (z i) = 0) → (∀ a i, ev (ds a (z i)) = if a = i then 1 else 0) → maximalIdeal A = (maximalIdeal R).map inc ⊔ Ideal.span (Set.range z) → ∀ f, taylor ev (fun i => ⇑(ds i)) f = 0 → f = 0 := by
  intro R A _ _ _ _ _ _ inc ev hev n ds z hz hd hm f hf
  obtain ⟨T, hT⟩ := GlobalTheory.T.exists_ringHom_eq_taylor A R n ev ds
  have hker := ker_le_span inc ev hev z hz hm
  have hTf : T f = 0 := by rw [hT]; exact hf
  have hall : ∀ k, f ∈ Ideal.span (Set.range z) ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => exact step ev ds T hT z hz hd hker k f hTf ih
  have hne : Ideal.span (Set.range z) ≠ ⊤ := by
    intro h
    apply (maximalIdeal.isMaximal A).ne_top
    rw [eq_top_iff, hm, ← h]; exact le_sup_right
  have := Ideal.iInf_pow_eq_bot_of_isLocalRing _ hne
  rw [← Ideal.mem_bot, ← this, Ideal.mem_iInf]; exact hall

end GlobalTheory.TaylorInj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendsTo
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PlaceModel

def DescendsTo {R₀ R : Type} [CommRing R₀] [CommRing R] (ic : R₀ →+* R) (j : R →+* Qb) {G₀ H₀ : Over (Sp R₀)}
    [GrpObj G₀] [GrpObj H₀] {GQ HQ : Over (Sp Qb)} [GrpObj GQ] [GrpObj HQ] (gQ : GQ.left ⟶ G₀.left)
    (hQ : HQ.left ⟶ H₀.left) (f : GQ ⟶ HQ) : Prop :=
  ∀ (G H : Over (Sp R)) [GrpObj G] [GrpObj H] (g : G.left ⟶ G₀.left) (h : H.left ⟶ H₀.left) (pG : GQ.left ⟶ G.left)
    (pH : HQ.left ⟶ H.left), IsGrpPullback G G₀ (spMap ic) g → IsGrpPullback H H₀ (spMap ic) h →
    IsGrpPullback GQ G (spMap j) pG → IsGrpPullback HQ H (spMap j) pH → pG ≫ g = gQ → pH ≫ h = hQ →
    ∃ F : G ⟶ H, f.left ≫ pH = pG ≫ F.left

end GlobalTheory.PlaceModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescentCocycleDefectIsTripleCocycleStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot
open GlobalTheory.LBDescent GlobalTheory.DescNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descentCocycleDefect_isTripleCocycle : ∀ (X Y : Scheme.{0}) (f : X ⟶ Y) (M : LB X), M.IsLB → ∀ (φ : ∀ i j, Γ(pullback f f, chart f M i j)ˣ) (D : Γ(Triple f, ⊤)ˣ), Defect f M φ D → TriCocycle f D := by
  first | exact @GlobalTheory.PolRoot.triCocycle_of_defect | exact GlobalTheory.PolRoot.triCocycle_of_defect | (intros; apply GlobalTheory.PolRoot.triCocycle_of_defect <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescentDatumCarriesTranslateChart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

section

variable {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G' : Over S} [GrpObj G']

theorem Near.datum_pt (N : Near π G') {φ} (hφ : N.Datum φ) {T : Scheme.{0}} (s : T ⟶ pullback π π)
    (x₀ x₀' : T ⟶ pullback N.U.hom π) (z : T ⟶ pullback G'.hom (pullback.fst π π))
    (h₁ : x₀' ≫ pullback.fst _ _ = x₀ ≫ pullback.fst _ _) (h₂ : x₀ ≫ pullback.snd _ _ = s ≫ pullback.fst π π)
    (h₃ : x₀' ≫ pullback.snd _ _ = s ≫ pullback.snd π π) (hz₁ : z ≫ pullback.fst _ _ = x₀ ≫ N.u)
    (hz₂ : z ≫ pullback.snd _ _ = s) :
    z ≫ φ.hom.left ≫ pullback.fst G'.hom (pullback.snd π π) = x₀' ≫ N.u := by
  obtain ⟨x₁, e₁, e₂, e₃⟩ := hφ.2 T (x₀ ≫ pullback.fst _ _) z
    ⟨x₀, rfl, by rw [← Category.assoc, hz₂, h₂], hz₁.symm⟩
  have : x₁ = x₀' := pullback.hom_ext (e₁.trans h₁.symm) (by rw [e₂, ← Category.assoc, hz₂, h₃])
  rw [← e₃, this]

theorem transl_pt {T : Scheme.{0}} (t : T ⟶ S) (g : Over.mk t ⟶ G') (y : Over.mk (𝟙 S) ⟶ G') :
    g ≫ transl y = g * (Over.homMk t (Category.comp_id t) ≫ y) := by
  unfold transl
  rw [comp_mul, Category.comp_id, ← Category.assoc]
  congr 2
  ext
  simp [Over.w g]

theorem pull_pt_ext {S' : Scheme.{0}} (f : S' ⟶ S) {T : Scheme.{0}} {s : T ⟶ S'}
    (a b : Over.mk s ⟶ (Over.pullback f).obj G') (h : a.left ≫ pullback.fst G'.hom f = b.left ≫ pullback.fst G'.hom f) :
    a = b :=
  Over.OverMorphism.ext (pullback.hom_ext h ((Over.w a).trans (Over.w b).symm))

end

theorem Near.datum_chart {R : Type} [CommRing R] [IsLocalRing R] (S : Scheme.{0}) (π : S ⟶ Sp R) (G' : Over S)
    [GrpObj G'] (N : Near π G') (n : ℕ) (a : Fin n → (Sp R ⟶ N.U.left)) (x : Fin n → (Over.mk (𝟙 S) ⟶ G'))
    (hx : ∀ i, N.Pt (𝟙 S) (π ≫ a i) (x i).left) (φ) (hφ : N.Datum φ) (j : Option (Fin n)) (T : Scheme.{0})
    (y₁ y₂ : T ⟶ pullback N.U.hom π) (s : T ⟶ pullback π π)
    (hy : y₁ ≫ pullback.fst _ _ = y₂ ≫ pullback.fst _ _) (h₁ : y₁ ≫ pullback.snd _ _ = s ≫ pullback.fst π π)
    (h₂ : y₂ ≫ pullback.snd _ _ = s ≫ pullback.snd π π) (z : T ⟶ pullback G'.hom (pullback.fst π π))
    (hz₁ : z ≫ pullback.fst _ _ = y₁ ≫ N.chart x j) (hz₂ : z ≫ pullback.snd _ _ = s) :
    z ≫ φ.hom.left ≫ pullback.fst G'.hom (pullback.snd π π) = y₂ ≫ N.chart x j := by
  cases j with
  | none => exact N.datum_pt hφ s y₁ y₂ z hy.symm h₁ h₂ hz₁ hz₂
  | some k =>
  haveI := hφ.1
  rw [Near.chart_some] at hz₁ ⊢
  obtain ⟨x₀, e₁, e₂, e₃⟩ := hx k
  have hxo : (x k).left ≫ G'.hom = 𝟙 S := Over.w (x k)
  have c₁ : (y₁ ≫ N.u) ≫ G'.hom = s ≫ pullback.fst π π := by rw [Category.assoc, N.u_over, h₁]
  have c₂ : (y₂ ≫ N.u) ≫ G'.hom = s ≫ pullback.snd π π := by rw [Category.assoc, N.u_over, h₂]
  have d₁ : (s ≫ pullback.fst π π ≫ (x k).left) ≫ G'.hom = s ≫ pullback.fst π π := by
    simp only [Category.assoc, hxo, Category.comp_id]
  have d₂ : (s ≫ pullback.snd π π ≫ (x k).left) ≫ G'.hom = s ≫ pullback.snd π π := by
    simp only [Category.assoc, hxo, Category.comp_id]
  let G₁ := (Over.pullback (pullback.fst π π)).obj G'
  let G₂ := (Over.pullback (pullback.snd π π)).obj G'
  let W₁ : Over.mk s ⟶ G₁ := Over.homMk (pullback.lift _ _ c₁) (pullback.lift_snd _ _ _)
  let X₁ : Over.mk s ⟶ G₁ := Over.homMk (pullback.lift _ _ d₁) (pullback.lift_snd _ _ _)
  let W₂ : Over.mk s ⟶ G₂ := Over.homMk (pullback.lift _ _ c₂) (pullback.lift_snd _ _ _)
  let X₂ : Over.mk s ⟶ G₂ := Over.homMk (pullback.lift _ _ d₂) (pullback.lift_snd _ _ _)
  let Z₁ : Over.mk s ⟶ G₁ := Over.homMk z hz₂
  let P₁ := pushHom (isGrpPullback_pullback G' (pullback.fst π π)) (Over.mk s)
  let P₂ := pushHom (isGrpPullback_pullback G' (pullback.snd π π)) (Over.mk s)
  let w₁ : Over.mk (s ≫ pullback.fst π π) ⟶ G' := Over.homMk (y₁ ≫ N.u) c₁
  let w₂ : Over.mk (s ≫ pullback.snd π π) ⟶ G' := Over.homMk (y₂ ≫ N.u) c₂
  have pW₁ : P₁ W₁ = w₁ := Over.OverMorphism.ext (pullback.lift_fst _ _ _)
  have pW₂ : P₂ W₂ = w₂ := Over.OverMorphism.ext (pullback.lift_fst _ _ _)
  have pX₁ : P₁ X₁ = Over.homMk (s ≫ pullback.fst π π) (Category.comp_id _) ≫ x k :=
    Over.OverMorphism.ext (pullback.lift_fst _ _ _)
  have pX₂ : P₂ X₂ = Over.homMk (s ≫ pullback.snd π π) (Category.comp_id _) ≫ x k :=
    Over.OverMorphism.ext (pullback.lift_fst _ _ _)

  have hZ : Z₁ = W₁ * X₁⁻¹ := by
    apply pull_pt_ext
    have e : P₁ Z₁ = P₁ (W₁ * X₁⁻¹) := by
      rw [map_mul, map_inv, pW₁, pX₁, ← GrpObj.comp_inv, ← transl_pt]
      exact Over.OverMorphism.ext (by
        show z ≫ pullback.fst _ _ = (y₁ ≫ N.u) ≫ (transl (x k)⁻¹).left
        rw [hz₁, Category.assoc])
    exact congrArg (fun q => q.left) e
  have hW : W₁ ≫ φ.hom = W₂ := by
    apply pull_pt_ext
    rw [Over.comp_left, Category.assoc]
    refine (N.datum_pt hφ s y₁ y₂ _ hy.symm h₁ h₂ (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)).trans ?_
    exact (pullback.lift_fst _ _ _).symm
  have hX : X₁ ≫ φ.hom = X₂ := by
    apply pull_pt_ext
    rw [Over.comp_left, Category.assoc]
    refine (N.datum_pt hφ s (s ≫ pullback.fst π π ≫ x₀) (s ≫ pullback.snd π π ≫ x₀) _ ?_ ?_ ?_ ?_
      (pullback.lift_snd _ _ _)).trans ?_
    · simp only [Category.assoc, e₁]
      rw [← Category.assoc (pullback.snd π π), ← pullback.condition, Category.assoc]
    · simp only [Category.assoc, e₂, Category.comp_id]
    · simp only [Category.assoc, e₂, Category.comp_id]
    · rw [pullback.lift_fst]; simp only [Category.assoc, e₃]
    · refine Eq.trans ?_ (pullback.lift_fst _ _ d₂).symm
      simp only [Category.assoc, e₃]
  have e : P₂ (Z₁ ≫ φ.hom) = w₂ ≫ transl (x k)⁻¹ := by
    rw [hZ, mul_comp, GrpObj.inv_comp, hW, hX, map_mul, map_inv, pW₂, pX₂, ← GrpObj.comp_inv, ← transl_pt]
  have e' : (z ≫ φ.hom.left) ≫ pullback.fst G'.hom (pullback.snd π π) = (y₂ ≫ N.u) ≫ (transl (x k)⁻¹).left :=
    congrArg (fun q => q.left) e
  simpa only [Category.assoc] using e'

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscrepancyLtAdaptedCoordsIndependentFunctionStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discrepancy_lt_adaptedCoords_independent_function : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ) (n : ℕ) [SmoothOfRelativeDimension n q] (B : Closeds Y) (y : Y) (U : Y.Opens) (hy : y ∈ U) (z : Fin n → Γ(Y, U)) (J : Finset (Fin n)) (w : Fin n → Y) (u : Fin n → Y.functionFieldˣ), IsSncChart q n B y U hy z J w u → (∀ j ∈ J, y ∉ Y.basicOpen (z j)) → ∀ F : Γ(Y, U), (∀ h : ∀ j : Option J, Y.presheaf.germ U y hy (j.elim F fun j => z j) ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y), LinearIndependent (IsLocalRing.ResidueField (Y.presheaf.stalk y)) (fun j : Option J => ((IsLocalRing.maximalIdeal (Y.presheaf.stalk y)).toCotangent ⟨Y.presheaf.germ U y hy (j.elim F fun j => z j), h j⟩ : IsLocalRing.CotangentSpace (Y.presheaf.stalk y)))) → ∀ (φ f : Y.functionFieldˣ) (a : Fin n → ℚ) (c : ℚ), (φ : Y.functionField) = fnOf U (gen_mem hy) F → UnitAt y ((f : Y.functionField) / φ) → (∀ j ∈ J, a j < 1) → c < 1 → ∀ E : DivOver q, E.Through y → -1 < (E.formOrd (formOf U (gen_mem hy) (dOn q z)) : ℚ) - ∑ j ∈ J, a j * E.ord (u j) - c * E.ord f := by
  first | exact @GlobalTheory.Discrepancy.IsSncChart.neg_one_lt_formOrd_sub_sum_sub_ord_of_indep | exact GlobalTheory.Discrepancy.IsSncChart.neg_one_lt_formOrd_sub_sum_sub_ord_of_indep | (intros; apply GlobalTheory.Discrepancy.IsSncChart.neg_one_lt_formOrd_sub_sum_sub_ord_of_indep <;> assumption)
end

