import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Bundle0018
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0054
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0044
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0038
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.ImportsAlt
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.PFSSmallCountBound
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0017
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PLemmaETailLog
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PTailLogOfMass
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0011
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0008

-- bundled from GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.FibreDim
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.ForSecondHalf

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace FibreTranscendenceDegree

theorem isAlgebraic_of_forall_div {M : Type} [Field M] (B : Subalgebra ℤ M)
    (h : ∀ m : M, ∃ a b : M, a ∈ B ∧ b ∈ B ∧ b ≠ 0 ∧ m = a / b) : Algebra.IsAlgebraic B M := by
  refine ⟨fun m => ?_⟩
  obtain ⟨a, b, ha, hb, hb0, rfl⟩ := h m
  refine ⟨Polynomial.C (⟨b, hb⟩ : B) * Polynomial.X - Polynomial.C (⟨a, ha⟩ : B), fun h0 => hb0 ?_, ?_⟩
  · have h1 := congrArg (fun p : Polynomial B => p.coeff 1) h0
    simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X, Polynomial.coeff_C, if_neg one_ne_zero,
      sub_zero, Polynomial.coeff_zero] at h1
    exact congrArg Subtype.val h1
  · simp only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
    show b * (a / b) - a = 0
    rw [mul_div_cancel₀ _ hb0, sub_self]

theorem trdeg_eq_of_forall_div {M : Type} [Field M] (B : Subalgebra ℤ M)
    (hZ : Function.Injective (algebraMap ℤ M))
    (h : ∀ m : M, ∃ a b : M, a ∈ B ∧ b ∈ B ∧ b ≠ 0 ∧ m = a / b) :
    Algebra.trdeg ℤ M = Algebra.trdeg ℤ B := by
  have := isAlgebraic_of_forall_div B h
  have : FaithfulSMul ℤ B := (faithfulSMul_iff_algebraMap_injective ℤ B).mpr fun a b hab =>
    hZ (by simpa using congrArg Subtype.val hab)
  have : FaithfulSMul B M := (faithfulSMul_iff_algebraMap_injective B M).mpr Subtype.val_injective
  have h0 := trdeg_add_eq ℤ B (A := M)
  rw [trdeg_eq_zero (R := B) (A := M), add_zero] at h0
  exact h0.symm

theorem trdeg_quot_ker {σ : Type} {M : Type} [CommRing M] [IsDomain M] (y : σ → M) :
    Algebra.trdeg ℤ (MvPolynomial σ ℤ ⧸ RingHom.ker (aeval y : MvPolynomial σ ℤ →ₐ[ℤ] M)) =
      Algebra.trdeg ℤ (aeval y : MvPolynomial σ ℤ →ₐ[ℤ] M).range := by
  have hker : RingHom.ker (aeval y : MvPolynomial σ ℤ →ₐ[ℤ] M) =
      RingHom.ker (aeval y : MvPolynomial σ ℤ →ₐ[ℤ] M).rangeRestrict := by
    ext p
    simp [RingHom.mem_ker, Subtype.ext_iff]
  exact ((Ideal.quotientEquivAlgOfEq ℤ hker).trans
    (Ideal.quotientKerAlgEquivOfSurjective (AlgHom.rangeRestrict_surjective _))).trdeg_eq

theorem trdeg_of_isArithVar {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {J : Ideal (MRing ι)}
    {n : ℕ} (h : IsArithVar J n) :
    ∃ t : ℕ, Algebra.trdeg ℤ (MRing ι ⧸ J) = t ∧ t + 1 = n + Fintype.card K := by
  obtain ⟨-, ⟨hprime, -, -⟩, hhor, hdim⟩ := h
  have := hprime
  have hA := IntDomainDim.proof (MRing ι ⧸ J) (CoordinateConeArithVar.algebraMap_injective J hhor)
  rw [hdim] at hA
  have hA' : ((n + Fintype.card K : ℕ) : ℕ∞) = Cardinal.toENat (Algebra.trdeg ℤ (MRing ι ⧸ J)) + 1 := by
    exact_mod_cast hA
  obtain ⟨t, ht⟩ : ∃ t : ℕ, Cardinal.toENat (Algebra.trdeg ℤ (MRing ι ⧸ J)) = t := by
    refine ENat.ne_top_iff_exists.mp (fun htop => ?_) |>.imp fun _ h => h.symm
    rw [htop] at hA'
    simp at hA'
  rw [ht] at hA'
  refine ⟨t, Cardinal.toENat_eq_natCast.mp ht, ?_⟩
  exact_mod_cast hA'.symm

theorem aeval_mem_closure {σ : Type} {L : Type} [Field L] (y : σ → L) (f : MvPolynomial σ ℤ) :
    aeval y f ∈ Subfield.closure (Set.range y) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [intCast_mem]
  | add f g hf hg => simpa using add_mem hf hg
  | mul_X f i hf => simpa using mul_mem hf (Subfield.subset_closure ⟨i, rfl⟩)

end FibreTranscendenceDegree

open FibreTranscendenceDegree in

theorem FibreDim.proof : FibreDimStatement := by
  intro K _ ι _ K' _ ι' _ κ v P' d r G hv hP' hP
  classical
  refine ⟨⟨RingHom.ker_isPrime _, Targets.FibreMultiHomog.proof K ι K' ι' κ v P' G hv hP'.2.1.2.1,
    fun k => ?_⟩, ?_⟩
  · obtain ⟨i, hi⟩ := hP'.2.1.2.2 k.1
    refine ⟨i, fun h => hi ?_⟩
    rw [fibreIdeal, RingHom.mem_ker, aeval_X] at h
    rw [← G.genericFibre_ker_target, RingHom.mem_ker, aeval_X]
    exact h
  rw [fibreIdeal, Inter.EvalKerKrullDim.proof (FibreBlock κ) (fibreIdx ι' κ) G.Φ G.Φ']
  set E := IntermediateField.adjoin G.Φ
    (Set.range fun q : (Σ k : FibreBlock κ, ι' k.1) => G.x' ⟨q.1.1, q.2⟩) with hEdef

  have hZ : Function.Injective (algebraMap ℤ G.Φ) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have hmem : (C a : MRing ι) ∈ imageZ v P' := by
      rw [← G.ker_x, RingHom.mem_ker, aeval_C]
      exact ha
    have h' : a ∈ (imageZ v P').comap (C : ℤ →+* MRing ι) := hmem
    rw [show (imageZ v P').comap (C : ℤ →+* MRing ι) = ⊥ from hP.2.2.1] at h'
    exact (Submodule.mem_bot ℤ).mp h'

  obtain ⟨t, ht, htd⟩ := trdeg_of_isArithVar hP
  have hΦ : Algebra.trdeg ℤ G.Φ = t := by
    rw [trdeg_eq_of_forall_div (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).range hZ, ← trdeg_quot_ker, G.ker_x, ht]
    intro c
    obtain ⟨f, g, hg, rfl⟩ := G.gen c
    exact ⟨_, _, ⟨f, rfl⟩, ⟨g, rfl⟩, hg, rfl⟩

  have hxE : ∀ q, G.x' q ∈ E := by
    intro q
    by_cases hq : q.1 ∈ Set.range κ
    · obtain ⟨p, rfl⟩ := hv.2.2.2 q hq
      rw [G.compat]
      exact E.algebraMap_mem _
    · exact IntermediateField.subset_adjoin _ _ ⟨⟨⟨q.1, hq⟩, q.2⟩, rfl⟩
  set xE : (Σ k', ι' k') → E := fun q => ⟨G.x' q, hxE q⟩ with hxEdef
  have hval : ∀ f : MRing ι', ((aeval xE f : E) : G.Φ') = aeval G.x' f := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp
    | add f g hf hg => simp only [map_add, IntermediateField.coe_add, hf, hg]
    | mul_X f i hf =>
      simp only [map_mul, IntermediateField.coe_mul, hf, aeval_X]
      rfl
  have hkerE : RingHom.ker (aeval xE : MRing ι' →ₐ[ℤ] E) = P' := by
    ext f
    rw [RingHom.mem_ker]
    constructor
    · intro h
      have h2 : f ∈ RingHom.ker (aeval G.x' : MRing ι' →ₐ[ℤ] G.Φ') := by
        rw [RingHom.mem_ker, ← hval f, h]
        rfl
      rwa [G.genericFibre_ker_target] at h2
    · intro h
      have h2 := h
      rw [← G.genericFibre_ker_target, RingHom.mem_ker, ← hval f] at h2
      exact Subtype.ext h2

  obtain ⟨t', ht', htd'⟩ := trdeg_of_isArithVar hP'
  have hZE : Function.Injective (algebraMap ℤ E) := by
    intro a b hab
    apply hZ
    apply (algebraMap G.Φ E).injective
    simpa using hab
  have hE : Algebra.trdeg ℤ E = t' := by
    rw [trdeg_eq_of_forall_div (aeval xE : MRing ι' →ₐ[ℤ] E).range hZE, ← trdeg_quot_ker, hkerE, ht']
    intro e

    have hle : E.toSubfield ≤ Subfield.closure (Set.range G.x') := by
      rw [hEdef, IntermediateField.adjoin_toSubfield]
      refine Subfield.closure_le.2 (Set.union_subset ?_ ?_)
      · rintro _ ⟨c, rfl⟩
        obtain ⟨f, g, -, rfl⟩ := G.gen c
        have key : ∀ f : MRing ι, algebraMap G.Φ G.Φ' (aeval G.x f) = aeval G.x' (rename v f) := by
          intro f
          induction f using MvPolynomial.induction_on with
          | C a => simp
          | add f g hf hg => simp only [map_add, hf, hg]
          | mul_X f i hf => simp only [map_mul, hf, aeval_X, rename_X, G.compat]
        rw [map_div₀, key, key]
        exact div_mem (aeval_mem_closure _ _) (aeval_mem_closure _ _)
      · rintro _ ⟨q, rfl⟩
        exact Subfield.subset_closure ⟨_, rfl⟩
    obtain ⟨a, ha, b, hb, hab⟩ := Subfield.mem_closure_iff.mp (hle e.2)
    have hsub : Subring.closure (Set.range G.x') ≤ (aeval G.x' : MRing ι' →ₐ[ℤ] G.Φ').range.toSubring := by
      rw [Subring.closure_le]
      rintro _ ⟨q, rfl⟩
      exact ⟨X q, aeval_X _ _⟩
    obtain ⟨f, rfl⟩ := hsub ha
    obtain ⟨g, rfl⟩ := hsub hb
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hab
    by_cases hg : aeval xE g = 0
    · refine ⟨0, 1, zero_mem _, one_mem _, one_ne_zero, ?_⟩
      have hg' : (aeval G.x' g : G.Φ') = 0 := by rw [← hval, hg]; rfl
      apply Subtype.ext
      rw [← hab, hg', div_zero]
      simp
    · refine ⟨aeval xE f, aeval xE g, ⟨f, rfl⟩, ⟨g, rfl⟩, hg, ?_⟩
      apply Subtype.ext
      rw [IntermediateField.coe_div, hval, hval]
      exact hab.symm

  have : FaithfulSMul ℤ G.Φ := (faithfulSMul_iff_algebraMap_injective ℤ G.Φ).mpr hZ
  have : FaithfulSMul G.Φ E := (faithfulSMul_iff_algebraMap_injective G.Φ E).mpr (algebraMap G.Φ E).injective
  have hadd := trdeg_add_eq ℤ G.Φ (A := E)
  rw [hΦ, hE] at hadd
  have hc : Fintype.card (FibreBlock κ) + Fintype.card K = Fintype.card K' := by
    simp only [← Nat.card_eq_fintype_card]
    have h1 := Set.ncard_add_ncard_compl (Set.range κ)
    rw [Set.ncard_range_of_injective hv.1, add_comm] at h1
    exact h1
  have hlt : Algebra.trdeg G.Φ E < Cardinal.aleph0 :=
    lt_of_le_of_lt (le_add_self.trans_eq hadd) Cardinal.natCast_lt_aleph0
  obtain ⟨m, hm⟩ := Cardinal.lt_aleph0.1 hlt
  rw [hm] at hadd
  have hm' : t + m = t' := by exact_mod_cast hadd
  have hmr : m = r + Fintype.card (FibreBlock κ) := by omega
  rw [hm, hmr, Cardinal.toENat_nat]
  rfl

end GroundTheory.Heights₂.Heights.ForSecondHalf
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.FibreDimB
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.ForSecondHalf

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace FibreDimB

theorem trdeg_eq_of_isFractionRing (B : Type) [CommRing B] [IsDomain B] (L : Type) [Field L] [Algebra B L]
    [IsFractionRing B L] (hB : Function.Injective (algebraMap ℤ B)) :
    Algebra.trdeg ℤ L = Algebra.trdeg ℤ B := by
  have : FaithfulSMul B L :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (IsFractionRing.injective B L)
  have : FaithfulSMul ℤ B := (faithfulSMul_iff_algebraMap_injective _ _).2 hB
  have : Algebra.IsAlgebraic B L := IsLocalization.isAlgebraic L (nonZeroDivisors B)
  rw [← trdeg_add_eq ℤ B (A := L), trdeg_eq_zero (R := B) (A := L), add_zero]

theorem trdeg_eq_of_gen {σ L : Type} [Field L] (y : σ → L) (P : Ideal (MvPolynomial σ ℤ))
    (hker : RingHom.ker (aeval y : MvPolynomial σ ℤ →ₐ[ℤ] L) = P)
    (hZ : Function.Injective (algebraMap ℤ L))
    (hgen : ∀ z : L, ∃ f g : MvPolynomial σ ℤ, z = aeval y f / aeval y g) :
    Algebra.trdeg ℤ L = Algebra.trdeg ℤ (MvPolynomial σ ℤ ⧸ P) := by
  subst hker
  set φ := Ideal.kerLiftAlg (aeval y : MvPolynomial σ ℤ →ₐ[ℤ] L) with hφdef
  have : (RingHom.ker (aeval y : MvPolynomial σ ℤ →ₐ[ℤ] L)).IsPrime := RingHom.ker_isPrime _
  let _ : Algebra (MvPolynomial σ ℤ ⧸ RingHom.ker (aeval y : MvPolynomial σ ℤ →ₐ[ℤ] L)) L :=
    φ.toRingHom.toAlgebra
  have hφ : Function.Injective φ := Ideal.kerLiftAlg_injective _
  have : FaithfulSMul (MvPolynomial σ ℤ ⧸ RingHom.ker (aeval y : MvPolynomial σ ℤ →ₐ[ℤ] L)) L :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hφ
  have : IsFractionRing (MvPolynomial σ ℤ ⧸ RingHom.ker (aeval y : MvPolynomial σ ℤ →ₐ[ℤ] L)) L :=
    IsFractionRing.of_field _ L fun z => by
      obtain ⟨f, g, rfl⟩ := hgen z
      exact ⟨Ideal.Quotient.mk _ f, Ideal.Quotient.mk _ g, (congrArg₂ (· / ·) (Ideal.kerLiftAlg_mk (aeval y : MvPolynomial σ ℤ →ₐ[ℤ] L) f)
        (Ideal.kerLiftAlg_mk (aeval y : MvPolynomial σ ℤ →ₐ[ℤ] L) g)).symm⟩
  refine trdeg_eq_of_isFractionRing _ L fun a b h => hZ ?_
  simpa only [eq_intCast, map_intCast] using congrArg φ h

theorem trdeg_of_isArithVar {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)}
    {n : ℕ} (hP : IsArithVar P n) :
    ∃ t : ℕ, Algebra.trdeg ℤ (MRing ι ⧸ P) = t ∧ t + 1 = n + Fintype.card K := by
  obtain ⟨_, ⟨hprime, -, -⟩, hhor, hdim⟩ := hP
  have := hprime
  have hA := IntDomainDim.proof (MRing ι ⧸ P) (CoordinateConeArithVar.algebraMap_injective P hhor)
  rw [hdim] at hA
  have h' : ((n + Fintype.card K : ℕ) : ℕ∞) = (Algebra.trdeg ℤ (MRing ι ⧸ P)).toENat + 1 := by
    exact_mod_cast hA
  obtain ⟨t, ht⟩ : ∃ t : ℕ, (Algebra.trdeg ℤ (MRing ι ⧸ P)).toENat = t := by
    refine ENat.ne_top_iff_exists.mp (fun htop => ?_) |>.imp fun _ h => h.symm
    rw [htop] at h'
    simp at h'
  refine ⟨t, Cardinal.toENat_eq_natCast.mp ht, ?_⟩
  rw [ht] at h'
  exact_mod_cast h'.symm

theorem aeval_mem_closure {σ L : Type} [Field L] (y : σ → L) (f : MvPolynomial σ ℤ) :
    aeval y f ∈ Subfield.closure (Set.range y) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [intCast_mem]
  | add f g hf hg => simpa using add_mem hf hg
  | mul_X f i hf => simpa using mul_mem hf (Subfield.subset_closure ⟨i, rfl⟩)

end FibreDimB

open FibreDimB in

theorem FibreDimB.full : FibreDimStatement := by
  intro K _ ι _ K' _ ι' _ κ v P' d r G hv hP' hP
  refine ⟨⟨RingHom.ker_isPrime _,
    Targets.FibreMultiHomog.proof K ι K' ι' κ v P' G hv hP'.2.1.2.1, fun k => ?_⟩, ?_⟩
  · obtain ⟨i, hi⟩ := hP'.2.1.2.2 k.1
    refine ⟨i, fun h => hi ?_⟩
    rw [fibreIdeal, RingHom.mem_ker, aeval_X] at h
    rw [← G.genericFibre_ker_target, RingHom.mem_ker, aeval_X]
    exact h

  have hZ' : Function.Injective (algebraMap ℤ G.Φ') := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have hm : a ∈ P'.comap (C : ℤ →+* MRing ι') := by
      rw [Ideal.mem_comap, ← G.genericFibre_ker_target, RingHom.mem_ker, aeval_C, ha]
    rw [show P'.comap (C : ℤ →+* MRing ι') = ⊥ from hP'.2.2.1] at hm
    exact (Submodule.mem_bot ℤ).mp hm
  have hZ : Function.Injective (algebraMap ℤ G.Φ) := fun a b h =>
    hZ' (by simpa only [eq_intCast, map_intCast] using congrArg (algebraMap G.Φ G.Φ') h)

  set E := IntermediateField.adjoin G.Φ
    (Set.range fun q : (Σ k : FibreBlock κ, ι' k.1) => G.x' ⟨q.1.1, q.2⟩) with hEdef
  have hmem : ∀ q, G.x' q ∈ E := by
    intro q
    by_cases hq : q.1 ∈ Set.range κ
    · obtain ⟨q0, rfl⟩ := hv.2.2.2 q hq
      rw [G.compat]
      exact E.algebraMap_mem _
    · exact IntermediateField.subset_adjoin _ _ ⟨⟨⟨q.1, hq⟩, q.2⟩, rfl⟩
  let y' : (Σ k', ι' k') → E := fun q => ⟨G.x' q, hmem q⟩
  have hval : ∀ f : MRing ι', ((aeval y' f : E) : G.Φ') = aeval G.x' f := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp
    | add f g hf hg => simp only [map_add, IntermediateField.coe_add, hf, hg]
    | mul_X f i hf => simp only [map_mul, IntermediateField.coe_mul, hf, aeval_X, y']
  have hkerE : RingHom.ker (aeval y' : MRing ι' →ₐ[ℤ] E) = P' := by
    ext f
    have h2 : f ∈ P' ↔ aeval G.x' f = 0 := by rw [← RingHom.mem_ker, G.genericFibre_ker_target]
    rw [RingHom.mem_ker, h2, ← hval]
    exact ⟨fun h => by rw [h]; rfl, fun h => Subtype.ext h⟩
  have hZE : Function.Injective (algebraMap ℤ E) := fun a b h =>
    hZ' (by simpa using congrArg (fun z : E => (z : G.Φ')) h)

  have hkey : ∀ f : MRing ι, algebraMap G.Φ G.Φ' (aeval G.x f) = aeval G.x' (rename v f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp
    | add f g hf hg => simp only [map_add, hf, hg]
    | mul_X f i hf => simp only [map_mul, hf, aeval_X, rename_X, G.compat]
  have hle : E.toSubfield ≤ Subfield.closure (Set.range G.x') := by
    rw [hEdef, IntermediateField.adjoin_toSubfield]
    refine Subfield.closure_le.2 (Set.union_subset ?_ ?_)
    · rintro _ ⟨c, rfl⟩
      obtain ⟨f, g, -, rfl⟩ := G.gen c
      rw [map_div₀, hkey, hkey]
      exact div_mem (aeval_mem_closure _ _) (aeval_mem_closure _ _)
    · rintro _ ⟨q, rfl⟩
      exact Subfield.subset_closure ⟨_, rfl⟩
  have hgenE : ∀ z : E, ∃ f g : MRing ι', z = aeval y' f / aeval y' g := by
    intro z
    obtain ⟨a, ha, b, hb, hab⟩ := (Subfield.mem_closure_iff).1 (hle z.2)
    have hsub : Subring.closure (Set.range G.x') ≤ (aeval G.x' : MRing ι' →ₐ[ℤ] G.Φ').range.toSubring :=
      Subring.closure_le.2 (by rintro _ ⟨q, rfl⟩; exact ⟨X q, aeval_X _ _⟩)
    obtain ⟨f, hf⟩ := hsub ha
    obtain ⟨g, hg⟩ := hsub hb
    refine ⟨f, g, Subtype.ext ?_⟩
    rw [IntermediateField.coe_div, hval, hval]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hf hg
    rw [hf, hg, hab]

  have tΦ : Algebra.trdeg ℤ G.Φ = Algebra.trdeg ℤ (MRing ι ⧸ imageZ v P') :=
    trdeg_eq_of_gen G.x _ G.ker_x hZ fun z => by
      obtain ⟨f, g, -, h⟩ := G.gen z
      exact ⟨f, g, h⟩
  have tE : Algebra.trdeg ℤ E = Algebra.trdeg ℤ (MRing ι' ⧸ P') :=
    trdeg_eq_of_gen y' _ hkerE hZE hgenE
  obtain ⟨a, ha, ha1⟩ := trdeg_of_isArithVar hP
  obtain ⟨b, hb, hb1⟩ := trdeg_of_isArithVar hP'
  have : FaithfulSMul ℤ G.Φ := (faithfulSMul_iff_algebraMap_injective _ _).2 hZ
  have : FaithfulSMul G.Φ E := (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap G.Φ E).injective
  have hadd := trdeg_add_eq ℤ G.Φ (A := E)
  rw [tΦ, ha, tE, hb] at hadd
  have hc : Fintype.card (FibreBlock κ) + Fintype.card K = Fintype.card K' := by
    simp only [← Nat.card_eq_fintype_card]
    have h1 := Set.ncard_add_ncard_compl (Set.range κ)
    rw [Set.ncard_range_of_injective hv.1, add_comm] at h1
    exact h1
  have hlt : Algebra.trdeg G.Φ E < Cardinal.aleph0 :=
    lt_of_le_of_lt (le_add_self.trans_eq hadd) (Cardinal.natCast_lt_aleph0)
  obtain ⟨m, hm⟩ := Cardinal.lt_aleph0.1 hlt
  rw [hm] at hadd
  have hm' : a + m = b := by exact_mod_cast hadd
  have hmr : m = r + Fintype.card (FibreBlock κ) := by omega
  rw [fibreIdeal, Inter.EvalKerKrullDim.proof (FibreBlock κ) (fibreIdx ι' κ) G.Φ G.Φ']
  rw [show IntermediateField.adjoin G.Φ
      (Set.range fun q : (Σ k : FibreBlock κ, ι' k.1) => G.x' ⟨q.1.1, q.2⟩) = E from hEdef.symm, hm, hmr]
  simp

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.ForSecondHalf
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.OfMoriwaki
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ForSecondHalf

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

theorem G6ppB.of_moriwaki (hBig : MoriwakiBigStatement) (hHS : MoriwakiHSStatement) : BirationalPullbackPushforwardFormula :=
  G6ppB.proof hBig NmSmallIntoFS.proof (FSSmallFinite.proof SmallFormsFinite.proof)
    (FSSmallCountBound.proof hHS)

end GroundTheory.Heights₂.Heights.ForSecondHalf
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.TailBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ForSecondHalf

open GroundTheory.Heights₂.Heights.AnalyticLimit

theorem ListMono.full : ListMono.Statement :=
  ListMono.proof ListMonoRaise.proof ListMonoDens.proof LocDensContOnOpen.proof
    MIntegrableOfDensLe.proof MIntMonoOfDensLe.proof

theorem RegSection.full : RegSection.Statement :=
  RegSection.proof RegYoDense.proof RegRCont.proof
    (BdMetric.proof ChartCont.proof
      (BdTransition.proof RegYoDense.proof BdEqHolo.proof
        (BdDivides.proof (CoordDivDivisible.proof HyperplaneDivisible.proof)))
      (BdCocycle.proof RegYoDense.proof BdEqHolo.proof)
      (LogNormHolo.proof ChartCont.proof)
      (BdWeight.proof BdPartition.proof IndicatorSmooth.proof NormSqSmooth.proof))
    (BdSectionProps.proof BdEqHolo.proof)
    (BdNormCont.proof ChartCont.proof BdEqHolo.proof)
    (BdComparison.proof ChartCont.proof BddOnInner.proof)

theorem TailShift.full : TailShift.Statement := TailShift.proof

theorem LemmaETailLog.of_lemmaETailMass (h : LemmaETailMass.Statement) : LemmaETailLog.Statement :=
  LemmaETailLog.proof h TailLogOfMass.proof

theorem ListTailLog.of_lemmaETailMass (h : LemmaETailMass.Statement) : ListTailLog.Statement :=
  ListTailLog.of_lemmaE (LemmaETailLog.of_lemmaETailMass h) ListMono.full RegSection.full
    TailShift.full

theorem TailBound.of_lemmaETailMass (h : LemmaETailMass.Statement) : TailBound.Statement :=
  TailBound.of_listTailLog (ListTailLog.of_lemmaETailMass h)

end GroundTheory.Heights₂.Heights.ForSecondHalf
end

