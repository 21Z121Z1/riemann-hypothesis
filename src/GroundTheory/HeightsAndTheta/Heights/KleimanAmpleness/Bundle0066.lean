import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0059
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0058

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.RingKrullDimSegreLift
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsRelevant)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

noncomputable section

variable {F : Type} [Field F] {K : Type} [Fintype K] {ι : K → Type}

theorem segreLiftMap_segreIncl (W : Ideal (MRing ι F)) (s : MRing ι F) :
    segreLiftMap ι F W (segreIncl ι F s) = Polynomial.C (Ideal.Quotient.mk W s) := by
  have h : (segreLiftMap ι F W).comp (segreIncl ι F) =
      (IsScalarTower.toAlgHom F (MRing ι F ⧸ W) (Polynomial (MRing ι F ⧸ W))).comp
        (Ideal.Quotient.mkₐ F W) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [segreIncl, segreLiftMap, segreLiftVal]
  simpa using DFunLike.congr_fun h s

abbrev segreLiftAlgebra (W : Ideal (MRing ι F)) :
    Algebra (MRing (segreIdx ι) F ⧸ RingHom.ker (segreLiftMap ι F W)) (Polynomial (MRing ι F ⧸ W)) :=
  RingHom.toAlgebra' (Ideal.kerLiftAlg (segreLiftMap ι F W)).toRingHom
    fun c x => mul_comm ((Ideal.kerLiftAlg (segreLiftMap ι F W)).toRingHom c) x

theorem isAlgebraic_segreLift (W : Ideal (MRing ι F)) [W.IsPrime] (hrel : IsRelevant W) :
    letI := segreLiftAlgebra W
    Algebra.IsAlgebraic (MRing (segreIdx ι) F ⧸ RingHom.ker (segreLiftMap ι F W))
      (Polynomial (MRing ι F ⧸ W)) := by
  classical
  let _ := segreLiftAlgebra W
  have : (RingHom.ker (segreLiftMap ι F W)).IsPrime := RingHom.ker_isPrime _
  have hmap : ∀ x, algebraMap (MRing (segreIdx ι) F ⧸ RingHom.ker (segreLiftMap ι F W))
      (Polynomial (MRing ι F ⧸ W)) (Ideal.Quotient.mk _ x) = segreLiftMap ι F W x :=
    fun x => Ideal.kerLiftAlg_mk (segreLiftMap ι F W) x
  choose c hc using hrel
  have hm : Ideal.Quotient.mk W (∏ k, X ⟨k, c k⟩ : MRing ι F) ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem, Ideal.IsPrime.prod_mem_iff]
    simpa using hc
  have hC : ∀ s : MRing ι F, algebraMap (MRing (segreIdx ι) F ⧸ RingHom.ker (segreLiftMap ι F W))
      (Polynomial (MRing ι F ⧸ W)) (Ideal.Quotient.mk _ (segreIncl ι F s)) =
        Polynomial.C (Ideal.Quotient.mk W s) := fun s => by
    rw [hmap, segreLiftMap_segreIncl]
  have hY : algebraMap (MRing (segreIdx ι) F ⧸ RingHom.ker (segreLiftMap ι F W))
      (Polynomial (MRing ι F ⧸ W)) (Ideal.Quotient.mk _ (segreY c)) =
        Polynomial.X * Polynomial.C (Ideal.Quotient.mk W (∏ k, X ⟨k, c k⟩)) := by
    rw [hmap]
    simp [segreLiftMap, segreY, segreLiftVal]
  have hX : IsAlgebraic (MRing (segreIdx ι) F ⧸ RingHom.ker (segreLiftMap ι F W))
      (Polynomial.X : Polynomial (MRing ι F ⧸ W)) := by
    refine ⟨Polynomial.C (Ideal.Quotient.mk _ (segreIncl ι F (∏ k, X ⟨k, c k⟩))) * Polynomial.X -
      Polynomial.C (Ideal.Quotient.mk _ (segreY c)), ?_, ?_⟩
    · intro h
      have h1 := congrArg (fun p => algebraMap
        (MRing (segreIdx ι) F ⧸ RingHom.ker (segreLiftMap ι F W))
        (Polynomial (MRing ι F ⧸ W)) (Polynomial.coeff p 1)) h
      simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X, Polynomial.coeff_C,
        if_true, one_ne_zero, if_false, sub_zero, Polynomial.coeff_zero, map_zero, hC,
        Polynomial.C_eq_zero] at h1
      exact hm h1
    · simp only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, hC, hY]
      ring
  refine ⟨fun p => ?_⟩
  have : p ∈ Subalgebra.algebraicClosure (MRing (segreIdx ι) F ⧸ RingHom.ker (segreLiftMap ι F W))
      (Polynomial (MRing ι F ⧸ W)) := by
    rw [p.as_sum_range_C_mul_X_pow]
    refine Subalgebra.sum_mem _ fun i _ => Subalgebra.mul_mem _ ?_ (Subalgebra.pow_mem _ hX _)
    obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (p.coeff i)
    rw [← hs, ← hC]
    exact isAlgebraic_algebraMap _
  exact this

open Algebra in

theorem ringKrullDim_segreLift [∀ k, Fintype (ι k)] [DecidableEq K] (W : Ideal (MRing ι F))
    [W.IsPrime] (hrel : IsRelevant W) :
    ringKrullDim (MRing (segreIdx ι) F ⧸ RingHom.ker (segreLiftMap ι F W)) =
      ringKrullDim (MRing ι F ⧸ W) + 1 := by
  let _ : ∀ x, Fintype (segreIdx ι x) := fun x => match x with
    | .inl _ => (inferInstance : Fintype (∀ k, ι k))
    | .inr k => (inferInstance : Fintype (ι k))
  let _ := segreLiftAlgebra W
  have : (RingHom.ker (segreLiftMap ι F W)).IsPrime := RingHom.ker_isPrime _
  have : IsScalarTower F (MRing (segreIdx ι) F ⧸ RingHom.ker (segreLiftMap ι F W))
      (Polynomial (MRing ι F ⧸ W)) :=
    IsScalarTower.of_algebraMap_eq fun c =>
      ((Ideal.kerLiftAlg (segreLiftMap ι F W)).commutes c).symm
  have : FaithfulSMul (MRing (segreIdx ι) F ⧸ RingHom.ker (segreLiftMap ι F W))
      (Polynomial (MRing ι F ⧸ W)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (Ideal.kerLiftAlg_injective _)
  have := isAlgebraic_segreLift W hrel
  obtain ⟨n, hA, htA⟩ :=
    GroundTheory.Arith.Abelian.Jacobian.exists_ringKrullDim_eq_trdeg F (A := MRing ι F ⧸ W)
  have hP : trdeg F (Polynomial (MRing ι F ⧸ W)) = n + 1 := by
    rw [← trdeg_add_eq F (MRing ι F ⧸ W) (A := Polynomial (MRing ι F ⧸ W)),
      Polynomial.trdeg_of_isDomain, htA]
  have hQ : trdeg F (MRing (segreIdx ι) F ⧸ RingHom.ker (segreLiftMap ι F W)) = n + 1 := by
    have h2 := trdeg_add_eq F (MRing (segreIdx ι) F ⧸ RingHom.ker (segreLiftMap ι F W))
      (A := Polynomial (MRing ι F ⧸ W))
    rw [trdeg_eq_zero (R := MRing (segreIdx ι) F ⧸ RingHom.ker (segreLiftMap ι F W))
      (A := Polynomial (MRing ι F ⧸ W)), add_zero] at h2
    rw [h2, hP]
  rw [GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg F, hQ, hA]
  simp

theorem SegreLiftRelDim.proof : SegreLiftRelDim.Statement := by
  intro F _ K _ _ ι _ W hW
  have := hW.isPrime
  have h := ringKrullDim_segreLift W hW.relevant
  obtain ⟨n, hA, -⟩ :=
    GroundTheory.Arith.Abelian.Jacobian.exists_ringKrullDim_eq_trdeg F (A := MRing ι F ⧸ W)
  unfold relDim
  erw [h, hA]
  rw [show ((n : WithBot ℕ∞) + 1) = (((n + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) by norm_cast,
    show (n : WithBot ℕ∞) = (((n : ℕ) : ℕ∞) : WithBot ℕ∞) by norm_cast]
  simp only [WithBot.map_coe, Fintype.card_sum, Fintype.card_unit]
  congr 1
  change WithTop.map _ (WithTop.some (n + 1)) = WithTop.map _ (WithTop.some n)
  rw [WithTop.map_coe, WithTop.map_coe]
  congr 1
  push_cast
  ring

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SegreInclWeightedHomogeneousComponent
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiProjPrime)

noncomputable section

section

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type} [Field F]

omit [Fintype K] in

theorem segre_weight_mapDomain (e : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (NumbersDVR.blockWeight (segreIdx ι))
        (Finsupp.mapDomain (fun v : Σ k, ι k => (⟨Sum.inr v.1, v.2⟩ : Σ c, segreIdx ι c)) e) =
      Sum.elim (fun _ => 0) (Finsupp.weight (NumbersDVR.blockWeight ι) e) := by
  rw [Finsupp.weight_apply, Finsupp.weight_apply,
    Finsupp.sum_mapDomain_index
      (h := fun (v : Σ c, segreIdx ι c) (n : ℕ) => n • NumbersDVR.blockWeight (segreIdx ι) v)
      (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]
  funext c
  rcases c with ⟨⟨⟩⟩ | k
  · simp [Finsupp.sum, Finset.sum_apply, NumbersDVR.blockWeight]
  · simp [Finsupp.sum, Finset.sum_apply, NumbersDVR.blockWeight, Pi.single_apply]

theorem segreIncl_weightedHomogeneousComponent (b : K → ℕ) (f : MRing ι F) :
    segreIncl ι F (weightedHomogeneousComponent (NumbersDVR.blockWeight ι) b f) =
      weightedHomogeneousComponent (NumbersDVR.blockWeight (segreIdx ι)) (Sum.elim (fun _ => 0) b)
        (segreIncl ι F f) := by
  classical
  have hinj : Function.Injective (fun v : Σ k, ι k => (⟨Sum.inr v.1, v.2⟩ : Σ c, segreIdx ι c)) := by
    rintro ⟨k, i⟩ ⟨k', i'⟩ h
    have h1 := Sigma.mk.inj h
    obtain rfl := Sum.inr_injective h1.1
    obtain rfl := eq_of_heq h1.2
    rfl
  ext e'
  rw [coeff_weightedHomogeneousComponent]
  by_cases he : ∃ e, Finsupp.mapDomain
      (fun v : Σ k, ι k => (⟨Sum.inr v.1, v.2⟩ : Σ c, segreIdx ι c)) e = e'
  · obtain ⟨e, rfl⟩ := he
    rw [segreIncl, coeff_rename_mapDomain _ hinj, coeff_rename_mapDomain _ hinj,
      coeff_weightedHomogeneousComponent, segre_weight_mapDomain]
    by_cases hd : Finsupp.weight (NumbersDVR.blockWeight ι) e = b
    · rw [if_pos hd, if_pos (by rw [hd])]
    · rw [if_neg hd, if_neg fun h => hd (funext fun k => congrFun h (Sum.inr k))]
  · push Not at he
    rw [segreIncl, coeff_rename_eq_zero _ _ _ fun u hu => absurd hu (he u)]
    split_ifs
    · rw [coeff_rename_eq_zero _ _ _ fun u hu => absurd hu (he u)]
    · rfl

theorem segreLiftVal_eq (W : Ideal (MRing ι F)) (v : Σ c, segreIdx ι c) :
    ∃ β, segreLiftVal ι F W v =
      Polynomial.X ^ (NumbersDVR.blockWeight (segreIdx ι) v (Sum.inl ())) * Polynomial.C β := by
  rcases v with ⟨⟨⟨⟩⟩ | k, i⟩
  · exact ⟨Ideal.Quotient.mk W (∏ k, X ⟨k, i k⟩), by
      simp [segreLiftVal, NumbersDVR.blockWeight]⟩
  · exact ⟨Ideal.Quotient.mk W (X ⟨k, i⟩), by simp [segreLiftVal, NumbersDVR.blockWeight]⟩

theorem segreLiftMap_monomial (W : Ideal (MRing ι F)) (s : (Σ c, segreIdx ι c) →₀ ℕ) :
    ∀ r : F, ∃ a, segreLiftMap ι F W (monomial s r) =
      Polynomial.X ^ (Finsupp.weight (NumbersDVR.blockWeight (segreIdx ι)) s (Sum.inl ())) *
        Polynomial.C a := by
  refine Finsupp.induction s ?_ ?_
  · intro r
    refine ⟨algebraMap F _ r, ?_⟩
    simp [segreLiftMap, Polynomial.algebraMap_apply]
  · intro v n s _ _ ih r
    obtain ⟨a, ha⟩ := ih r
    obtain ⟨β, hβ⟩ := segreLiftVal_eq W v
    refine ⟨β ^ n * a, ?_⟩
    have hm : (monomial (Finsupp.single v n + s) r : MRing (segreIdx ι) F) =
        X v ^ n * monomial s r := by
      rw [X_pow_eq_monomial, monomial_mul, one_mul]
    rw [hm, map_mul, map_pow, ha, segreLiftMap, aeval_X, hβ, map_add, Pi.add_apply,
      Finsupp.weight_single, Pi.smul_apply, smul_eq_mul, map_mul, map_pow]
    ring

theorem segreLiftMap_of_isWeightedHomogeneous (W : Ideal (MRing ι F)) {f : MRing (segreIdx ι) F}
    {e : Unit ⊕ K → ℕ} (hf : IsWeightedHomogeneous (NumbersDVR.blockWeight (segreIdx ι)) f e) :
    ∃ a, segreLiftMap ι F W f = Polynomial.X ^ e (Sum.inl ()) * Polynomial.C a := by
  classical
  choose a ha using fun s => segreLiftMap_monomial W s (coeff s f)
  refine ⟨∑ s ∈ f.support, a s, ?_⟩
  conv_lhs => rw [f.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [ha s, hf (mem_support_iff.mp hs)]

end

theorem SegreLiftComap.proof : SegreLiftComap.Statement := by
  intro F _ K _ _ ι _ W' hW' hrel
  classical
  have := hW'.isPrime
  have hW : IsMultiProjPrime (W'.comap (segreIncl ι F)) := by
    refine ⟨inferInstance, ?_, ?_⟩
    · intro f hf b
      rw [Ideal.mem_comap, segreIncl_weightedHomogeneousComponent]
      exact hW'.multiHomog _ hf _
    · intro k
      obtain ⟨i, hi⟩ := hW'.relevant (Sum.inr k)
      exact ⟨i, by rwa [Ideal.mem_comap, segreIncl, rename_X]⟩
  refine ⟨hW, ?_⟩
  set W := W'.comap (segreIncl ι F) with hWdef

  choose c' hc using fun k => hW'.relevant (Sum.inr k)
  let c : ∀ k, ι k := c'
  let D := MRing (segreIdx ι) F ⧸ W'
  let L := FractionRing D
  let π : MRing (segreIdx ι) F →+* L := (algebraMap D L).comp (Ideal.Quotient.mk W')
  have hπ : ∀ f, π f = 0 ↔ f ∈ W' := by
    intro f
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact (IsFractionRing.injective D L).eq_iff' (map_zero _)
  have hmc : segreMon (R := F) c ∉ W' := by
    intro h
    obtain ⟨k, -, hk⟩ := Ideal.IsPrime.prod_mem_iff.mp h
    exact hc k hk
  have hYc : segreY (R := F) c ∉ W' := by
    intro h
    obtain ⟨d, hd⟩ := hW'.relevant (Sum.inl ())
    have hr : segreY c * segreMon d - segreY d * segreMon c ∈ W' := hrel ⟨c, d, rfl⟩
    have : segreY (R := F) d * segreMon c ∈ W' := by
      have := W'.sub_mem (W'.mul_mem_right (segreMon d) h) hr
      rwa [sub_sub_cancel] at this
    exact (hW'.isPrime.mem_or_mem this).elim hd hmc
  have hMc : π (segreMon c) ≠ 0 := fun h => hmc ((hπ _).mp h)
  let u : L := π (segreY c) / π (segreMon c)
  have hu : u ≠ 0 := div_ne_zero (fun h => hYc ((hπ _).mp h)) hMc
  let j : MRing ι F ⧸ W →+* D :=
    Ideal.quotientMap W' (segreIncl ι F : MRing ι F →+* MRing (segreIdx ι) F) le_rfl
  have hj : Function.Injective j := Ideal.quotientMap_injective' le_rfl
  have hjmk : ∀ x, j (Ideal.Quotient.mk W x) = Ideal.Quotient.mk W' (segreIncl ι F x) :=
    fun x => Ideal.quotientMap_mk
  let Φ : Polynomial (MRing ι F ⧸ W) →+* L := Polynomial.eval₂RingHom ((algebraMap D L).comp j) u
  have hΦ : ∀ a, Φ (Polynomial.C a) = algebraMap D L (j a) := fun a => by
    simp [Φ]
  have hkey : ∀ f, Φ (segreLiftMap ι F W f) = π f := by
    have : Φ.comp (segreLiftMap ι F W : MRing (segreIdx ι) F →+* Polynomial (MRing ι F ⧸ W)) = π := by
      refine MvPolynomial.ringHom_ext (fun r => ?_) (fun v => ?_)
      · simp only [RingHom.comp_apply, RingHom.coe_coe, segreLiftMap, aeval_C,
          Polynomial.algebraMap_apply, hΦ]
        rw [← Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_eq, hjmk, segreIncl, rename_C]
        rfl
      · rcases v with ⟨⟨⟨⟩⟩ | k, i⟩
        · have hs : π (segreY c) * π (segreMon i) = π (segreY i) * π (segreMon c) := by
            have := (hπ _).mpr (hrel ⟨c, i, rfl⟩)
            rwa [map_sub, map_mul, map_mul, sub_eq_zero] at this
          have hinc : segreIncl ι F (∏ k, X ⟨k, i k⟩) = segreMon i := by
            simp [segreIncl, segreMon, map_prod]
          simp only [RingHom.comp_apply, RingHom.coe_coe, segreLiftMap, aeval_X, segreLiftVal,
            map_mul, hΦ]
          simp only [Φ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
          rw [hjmk, hinc]
          change u * π (segreMon i) = π (segreY i)
          rw [div_mul_eq_mul_div, div_eq_iff hMc, hs]
        · simp only [RingHom.comp_apply, RingHom.coe_coe, segreLiftMap, aeval_X, segreLiftVal, hΦ]
          rw [hjmk, segreIncl, rename_X]
          rfl
    intro f
    exact RingHom.congr_fun this f
  ext f
  rw [segreLift, RingHom.mem_ker]
  constructor
  · intro hf
    rw [← sum_weightedHomogeneousComponent (NumbersDVR.blockWeight (segreIdx ι)) f,
      finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f), map_sum]
    refine Finset.sum_eq_zero fun e _ => ?_
    obtain ⟨a, ha⟩ := segreLiftMap_of_isWeightedHomogeneous W
      (weightedHomogeneousComponent_isWeightedHomogeneous
        (w := NumbersDVR.blockWeight (segreIdx ι)) e f)
    have h0 : Φ (Polynomial.X ^ e (Sum.inl ()) * Polynomial.C a) = 0 := by
      rw [← ha, hkey]
      exact (hπ _).mpr (hW'.multiHomog f hf e)
    rw [map_mul, map_pow, hΦ] at h0
    have h1 := (mul_eq_zero.mp h0).resolve_left (pow_ne_zero _ (by simpa [Φ] using hu))
    have h2 : j a = 0 := (IsFractionRing.injective D L) (by rw [h1, map_zero])
    have h3 : a = 0 := hj (by rw [h2, map_zero])
    rw [ha, h3, map_zero, mul_zero]
  · intro hf
    exact (hπ f).mp (by rw [← hkey, hf, map_zero])

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SegreLiftValEqAndIsWeightedHomogeneous
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiProjPrime blockWeight)

noncomputable section

section Lift

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type} [Field F]

def segreSubstVal : (Σ d, segreIdx ι d) → MRing ι F
  | ⟨Sum.inl _, c⟩ => ∏ k, X ⟨k, c k⟩
  | ⟨Sum.inr k, i⟩ => X ⟨k, i⟩

def segreDeg (b : Unit ⊕ K → ℕ) : K → ℕ := fun k => b (Sum.inr k) + b (Sum.inl ())

omit [Fintype K] [DecidableEq K] in

theorem segreDeg_injective_of_fst {b b' : Unit ⊕ K → ℕ} (h₀ : b' (Sum.inl ()) = b (Sum.inl ()))
    (h : segreDeg b' = segreDeg b) : b' = b := by
  funext x
  rcases x with u | k
  · cases u; exact h₀
  · have := congrFun h k
    simp only [segreDeg] at this
    omega

theorem segreLiftVal_eq_and_isWeightedHomogeneous (W : Ideal (MRing ι F)) (v : Σ d, segreIdx ι d) :
    segreLiftVal ι F W v = Polynomial.C (Ideal.Quotient.mk W (segreSubstVal v)) *
        Polynomial.X ^ (blockWeight (segreIdx ι) v (Sum.inl ())) ∧
      IsWeightedHomogeneous (blockWeight ι) (segreSubstVal (F := F) v)
        (segreDeg (blockWeight (segreIdx ι) v)) := by
  obtain ⟨d, i⟩ := v
  rcases d with u | k
  · cases u
    refine ⟨by simp [segreLiftVal, segreSubstVal, blockWeight]; ring, ?_⟩
    have hp := IsWeightedHomogeneous.prod (w := blockWeight ι) Finset.univ
      (fun k => (X ⟨k, i k⟩ : MRing ι F)) (fun k => blockWeight ι ⟨k, i k⟩)
      (fun k _ => isWeightedHomogeneous_X _ _ _)
    have hd : segreDeg (blockWeight (segreIdx ι) ⟨Sum.inl (), i⟩) =
        ∑ k, blockWeight ι ⟨k, i k⟩ := by
      funext k
      simp [segreDeg, blockWeight, Finset.sum_apply, Pi.single_apply]
    rw [hd]
    exact hp
  · refine ⟨by simp [segreLiftVal, segreSubstVal, blockWeight], ?_⟩
    have hd : segreDeg (blockWeight (segreIdx ι) ⟨Sum.inr k, i⟩) = blockWeight ι ⟨k, i⟩ := by
      funext k'
      by_cases h : k' = k
      · subst h; simp [segreDeg, blockWeight]
      · simp [segreDeg, blockWeight, h]
    rw [hd]
    exact isWeightedHomogeneous_X _ _ _

theorem segreLiftMap_of_isMultiHomog (W : Ideal (MRing ι F)) (b : Unit ⊕ K → ℕ)
    {f : MRing (segreIdx ι) F} (hf : IsWeightedHomogeneous (blockWeight (segreIdx ι)) f b) :
    segreLiftMap ι F W f = Polynomial.C (Ideal.Quotient.mk W (aeval segreSubstVal f)) *
        Polynomial.X ^ (b (Sum.inl ())) ∧
      IsWeightedHomogeneous (blockWeight ι) (aeval (segreSubstVal (F := F)) f) (segreDeg b) := by
  induction hf using IsWeightedHomogeneous.induction_on with
  | zero => exact ⟨by simp, isWeightedHomogeneous_zero _ _ _⟩
  | add p q hp hq ihp ihq =>
    refine ⟨?_, ?_⟩
    · rw [map_add, map_add, map_add, map_add, ihp.1, ihq.1, add_mul]
    · rw [map_add]; exact ihp.2.add ihq.2
  | monomial d r hr =>
    have hb : b (Sum.inl ()) =
        ∑ v ∈ d.support, blockWeight (segreIdx ι) v (Sum.inl ()) * d v := by
      rw [← hr, Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
      simp [smul_eq_mul, mul_comm]
    have hdeg : segreDeg b = ∑ v ∈ d.support, d v • segreDeg (blockWeight (segreIdx ι) v) := by
      rw [← hr, Finsupp.weight_apply, Finsupp.sum]
      funext k
      simp [segreDeg, Finset.sum_apply, Finset.sum_add_distrib, mul_add]
    rw [monomial_eq, Finsupp.prod]
    refine ⟨?_, ?_⟩
    · simp only [map_mul, map_prod, map_pow, segreLiftMap, aeval_X, aeval_C]
      rw [Finset.prod_congr rfl (fun v _ => by rw [(segreLiftVal_eq_and_isWeightedHomogeneous W v).1]), hb]
      rw [Finset.prod_congr rfl (fun v _ =>
        show (Polynomial.C (Ideal.Quotient.mk W (segreSubstVal v)) *
            Polynomial.X ^ blockWeight (segreIdx ι) v (Sum.inl ())) ^ d v =
          Polynomial.C (Ideal.Quotient.mk W (segreSubstVal v)) ^ d v *
            Polynomial.X ^ (blockWeight (segreIdx ι) v (Sum.inl ()) * d v) by ring)]
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Polynomial.algebraMap_apply,
        ← Ideal.Quotient.mk_algebraMap]
      ring
    · simp only [map_mul, map_prod, map_pow, aeval_X, aeval_C]
      rw [hdeg]
      refine IsWeightedHomogeneous.C_mul ?_ _
      exact IsWeightedHomogeneous.prod _ _ _ fun v _ => (segreLiftVal_eq_and_isWeightedHomogeneous (F := F) ⊥ v).2.pow _

end Lift

theorem SegreLiftPrime.proof : SegreLiftPrime.Statement := by
  intro F _ K _ _ ι _ W hW
  classical
  have := hW.isPrime
  refine ⟨RingHom.ker_isPrime _, ?_, ?_⟩
  · intro f hf b
    set w := blockWeight (segreIdx ι)
    have hB := fun b' => segreLiftMap_of_isMultiHomog W b'
      (weightedHomogeneousComponent_isWeightedHomogeneous (w := w) b' f)
    set s : Finset (Unit ⊕ K → ℕ) := insert b (f.support.image (Finsupp.weight w)) with hs
    have hsum : f = ∑ b' ∈ s, weightedHomogeneousComponent w b' f := by
      ext d
      simp only [coeff_sum, coeff_weightedHomogeneousComponent]
      rw [Finset.sum_ite_eq]
      split_ifs with h
      · rfl
      · by_contra hne
        exact h (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (mem_support_iff.mpr hne)))
    have hker : segreLiftMap ι F W f = 0 := hf
    rw [hsum, map_sum, Finset.sum_congr rfl (fun b' _ => (hB b').1)] at hker
    have hcoeff := congrArg (fun p => Polynomial.coeff p (b (Sum.inl ()))) hker
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero]
      at hcoeff
    rw [← Finset.sum_filter, ← map_sum, Ideal.Quotient.eq_zero_iff_mem] at hcoeff
    have hcomp := hW.multiHomog _ hcoeff (segreDeg b)
    have hval : ∀ b' ∈ s.filter (fun b' => b (Sum.inl ()) = b' (Sum.inl ())),
        weightedHomogeneousComponent (blockWeight ι) (segreDeg b)
            (aeval (segreSubstVal (F := F)) (weightedHomogeneousComponent w b' f)) =
          if b' = b then aeval (segreSubstVal (F := F)) (weightedHomogeneousComponent w b' f)
          else 0 := by
      intro b' hb'
      rw [weightedHomogeneousComponent_of_mem
        (by rw [mem_weightedHomogeneousSubmodule]; exact (hB b').2)]
      have h₀ := (Finset.mem_filter.mp hb').2
      by_cases hbb : b' = b
      · subst hbb; simp
      · rw [if_neg hbb, if_neg (fun h => hbb (segreDeg_injective_of_fst h₀.symm h.symm))]
    have hbmem : b ∈ s.filter (fun b' => b (Sum.inl ()) = b' (Sum.inl ())) :=
      Finset.mem_filter.mpr ⟨Finset.mem_insert_self _ _, rfl⟩
    rw [map_sum, Finset.sum_congr rfl hval, Finset.sum_ite_eq', if_pos hbmem] at hcomp
    show segreLiftMap ι F W _ = 0
    rw [(hB b).1, (Ideal.Quotient.eq_zero_iff_mem).mpr hcomp, map_zero, zero_mul]
  · intro d
    rcases d with u | k
    · choose c hc using hW.relevant
      refine ⟨c, ?_⟩
      show ¬ segreLiftMap ι F W _ = 0
      rw [segreLiftMap, aeval_X]
      simp only [segreLiftVal, mul_eq_zero, Polynomial.X_ne_zero, false_or, Polynomial.C_eq_zero,
        Ideal.Quotient.eq_zero_iff_mem]
      rw [Ideal.IsPrime.prod_mem_iff]
      rintro ⟨k, -, hk⟩
      exact hc k hk
    · obtain ⟨i, hi⟩ := hW.relevant k
      refine ⟨i, ?_⟩
      show ¬ segreLiftMap ι F W _ = 0
      rw [segreLiftMap, aeval_X]
      simp only [segreLiftVal, Polynomial.C_eq_zero, Ideal.Quotient.eq_zero_iff_mem]
      exact hi

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

