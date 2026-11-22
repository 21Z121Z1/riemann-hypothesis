import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0348
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0342
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0230
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0250
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncludeLInjective
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapSplit
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Formalism.LocalToGlobal.PlaceMapInjectivity.MapPlInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0349
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0206
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiamondOperatorHermitianSideLevelPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmulLk
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0329
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0326
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0320
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0322
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0350
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AutomorphicMultiplicityEqOfIsoStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.automorphic_multiplicity_eq_of_iso : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π π' : NG.AutRep L n),
    π.Iso π' → π.mult = π'.mult := by
  first | exact @GlobalTheory.MultIso.mult_eq_of_iso | exact GlobalTheory.MultIso.mult_eq_of_iso | (intros; apply GlobalTheory.MultIso.mult_eq_of_iso <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AutomorphicRepCmQuotientModelStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.automorphic_rep_cm_quotient_model : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.AutRep L n),
    ∃ m : GlobalTheory.AutQuot.AutRepM L n, π.Iso m.toAutRep := by
  first | exact @GlobalTheory.AutModel.exists_autRepM | exact GlobalTheory.AutModel.exists_autRepM | (intros; apply GlobalTheory.AutModel.exists_autRepM <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AuxiliaryPrimePlacesNonemptyStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.auxiliaryPrimePlaces_nonempty : ∀ (D : D7) (T : TwR D.LL0 D.nd) (i : T.Tw), (T.pD i).Nonempty := by
  first | exact @GlobalTheory.PdPlace.pD_nonempty | exact GlobalTheory.PdPlace.pD_nonempty | (intros; apply GlobalTheory.PdPlace.pD_nonempty <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharZeroFractionRingCoefficientRing
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.HeightCounting.FracCharZero

theorem injective_of_finite_dvr {A B : Type} [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [Module.Finite A B] :
    Function.Injective (algebraMap A B) := by
  rw [injective_iff_map_eq_zero]
  by_contra hne
  push_neg at hne
  obtain ⟨a, ha, ha0⟩ := hne
  have hker : (⊥ : Ideal B).comap (algebraMap A B) ≠ ⊥ := by
    intro h
    apply ha0
    have : a ∈ (⊥ : Ideal B).comap (algebraMap A B) := by simp [Ideal.mem_comap, ha]
    rw [h] at this
    simpa using this
  have hmax : ((⊥ : Ideal B).comap (algebraMap A B)).IsMaximal :=
    Ideal.IsPrime.isMaximal inferInstance hker
  have hbot : (⊥ : Ideal B).IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := A) _ hmax
  exact IsDiscreteValuationRing.not_a_field B (IsLocalRing.eq_maximalIdeal hbot).symm

theorem charZero_of_injective {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] [CharZero R]
    (f : R →+* S) (hf : Function.Injective f) : CharZero S :=
  ⟨fun m n h => by
    have : f (m : R) = f (n : R) := by simpa [map_natCast] using h
    exact Nat.cast_injective (hf this)⟩

end GlobalTheory.HeightCounting.FracCharZero

namespace GlobalTheory.HeightCounting

theorem TwR.charZero_fractionRing_O : ∀ (D : D7) (T : TwR D.LL0 D.nd) (i : T.Tw),
    CharZero (FractionRing (T.O i)) := by
  intro D T i
  have h1 : Function.Injective (algebraMap ℤ_[T.l i] (T.O0 i)) :=
    FracCharZero.injective_of_finite_dvr
  have h2 := T.O_inj i
  have h3 := IsFractionRing.injective (T.O i) (FractionRing (T.O i))
  exact FracCharZero.charZero_of_injective
    (((algebraMap (T.O i) (FractionRing (T.O i))).comp (algebraMap (T.O0 i) (T.O i))).comp
      (algebraMap ℤ_[T.l i] (T.O0 i))) (h3.comp (h2.comp h1))

end GlobalTheory.HeightCounting
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmTypeEmbeddingAtSideDistinctNonconjugate
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.HeightCounting.FormsStep

theorem complexConj_eq_hostConj (D : D7) (x : D.host.E) : IsCMField.complexConj D.host.E x = D.host.conj x := by
  apply D.host.φ₀.injective
  rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]

theorem kEmbT_cmDist : ∀ (D : D7) (T : TwR D.LL0 D.nd) (i : T.Tw) (b : Bool), GlobalTheory.AlgWtF.CMDist (kEmbT D T i b) := by
  intro D T i b
  have hR : Function.Injective ((readT D T i b).comp (Formalism.L2.NX.embEL0 D)) := RingHom.injective _
  have hS : ∀ g h : D.R.GG, (∀ x : D.host.E, D.host.sigmaOf g x = D.host.sigmaOf h x) → g = h := by
    intro g h e
    exact Formalism.MainNotions.Gaps.LevGap.sigmaOf_injective D.host (AlgEquiv.ext e)
  have hk : ∀ t x, kEmbT D T i b t x =
      ((readT D T i b).comp (Formalism.L2.NX.embEL0 D)) (D.host.sigmaOf ((D.eTau t : D.R.Psi) : D.R.GG) x) :=
    fun _ _ => rfl
  refine ⟨?_, ?_⟩
  · intro t t' e
    apply D.eTau.injective
    apply Subtype.ext
    apply hS
    intro x
    apply hR
    rw [← hk, ← hk, e]
  · intro t t' e
    have h1 : ((D.eTau t : D.R.Psi) : D.R.GG) =
        ((D.eTau t' : D.R.Psi) : D.R.GG) * D.R.cc := by
      apply hS
      intro x
      apply hR
      rw [← hk, Formalism.MainNotions.Gaps.LevGap.sigmaOf_mul, AlgEquiv.mul_apply, ← Formalism.MainNotions.Gaps.LevGap.conj_eq_sigmaOf,
        ← complexConj_eq_hostConj D x]
      exact DFunLike.congr_fun e x
    have ht : ((D.eTau t : D.R.Psi) : D.R.GG).1.2 = 1 := (Formalism.HC.Frame.mem_Psi_iff _).1 (D.eTau t).2
    have ht' : ((D.eTau t' : D.R.Psi) : D.R.GG).1.2 = 1 := (Formalism.HC.Frame.mem_Psi_iff _).1 (D.eTau t').2
    have h2 : ((D.eTau t : D.R.Psi) : D.R.GG).1.2 =
        ((D.eTau t' : D.R.Psi) : D.R.GG).1.2 * (-1) := by rw [h1]; rfl
    rw [ht, ht'] at h2
    exact absurd h2 (by decide)

end GlobalTheory.HeightCounting.FormsStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefficientSpaceStableEqBotOrTop
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX
  GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TensorIrr

open Formalism.L2.DIV

section General

variable {K : Type} [Field K] {n : ℕ}

def bSq (lam : DomWeight n) : Module.Basis (Formalism.GradedWeylDivisibility.ssIdx n n lam.natW) K (nablaSq K n lam) :=
  (Module.Basis.span (Formalism.GradedWeylDivisibility.sSBasis K n n lam.natW).choose_spec.1.1).map
    (LinearEquiv.ofEq _ _ (Formalism.GradedWeylDivisibility.sSBasis K n n lam.natW).choose_spec.1.2.1)

theorem bSq_coe (lam : DomWeight n) (k : Formalism.GradedWeylDivisibility.ssIdx n n lam.natW) :
    ((bSq (K := K) lam k : nablaSq K n lam) : MvPolynomial (Fin n × Fin n) K) = ssB K lam.natW k := by
  simp [bSq, Module.Basis.span_apply, ssB]
  rfl

theorem ssB_mem (lam : DomWeight n) (k : Formalism.GradedWeylDivisibility.ssIdx n n lam.natW) : ssB K lam.natW k ∈ nablaSq K n lam :=
  bSq_coe (K := K) lam k ▸ (bSq (K := K) lam k).2

theorem sqAct_one_of_mem (lam : DomWeight n) {f : MvPolynomial (Fin n × Fin n) K} (hf : f ∈ nablaSq K n lam) :
    sqAct K n lam 1 f = f :=
  congrArg Subtype.val (LinearMap.congr_fun (GlobalTheory.Branching.sqRep K n lam).map_one ⟨f, hf⟩)

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def tenAt (f : ι → MvPolynomial (Fin n × Fin n) K) (τ₀ : ι) : MvPolynomial (Fin n × Fin n) K →ₗ[K] Pol K ι n :=
  LinearMap.mulLeft K (∏ τ ∈ Finset.univ.erase τ₀, Formalism.GradedWeylDivisibility.blockEmb K τ (f τ)) ∘ₗ
    (Formalism.GradedWeylDivisibility.blockEmb K (k := n) (n := n) τ₀).toLinearMap

theorem tenAt_apply (f : ι → MvPolynomial (Fin n × Fin n) K) (τ₀ : ι) (x : MvPolynomial (Fin n × Fin n) K) :
    tenAt f τ₀ x = ten (Function.update f τ₀ x) := by
  simp only [tenAt, ten, LinearMap.comp_apply, LinearMap.mulLeft_apply, AlgHom.toLinearMap_apply]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ τ₀), Function.update_self, mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun τ hτ => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hτ)]

theorem ten_update_ssB (lam : ι → DomWeight n) (τ₀ : ι) (k : VVIdx lam) (l : Formalism.GradedWeylDivisibility.ssIdx n n (lam τ₀).natW) :
    ten (Function.update (fun τ => ssB K (lam τ).natW (k τ)) τ₀ (ssB K (lam τ₀).natW l)) =
      ((bVV K lam (Function.update k τ₀ l) : VV K lam) : Pol K ι n) := by
  rw [bVV_coe, bVVfun]
  congr 1
  funext τ
  exact (Function.apply_update (fun τ k => ssB K (lam τ).natW k) k τ₀ l τ).symm

theorem exists_op (lam : ι → DomWeight n) (τ₀ : ι) (φ : nablaSq K n (lam τ₀) →ₗ[K] nablaSq K n (lam τ₀))
    (hφ : ∃ (s : Finset (GL (Fin n) K)) (c : GL (Fin n) K → K), ∀ f : nablaSq K n (lam τ₀),
      (φ f : MvPolynomial (Fin n × Fin n) K) = ∑ g ∈ s, c g • sqAct K n (lam τ₀) g f)
    (W : Submodule K (VV K lam)) (hW : ∀ g : ι → GL (Fin n) K, ∀ w ∈ W, rhoK lam g w ∈ W) :
    ∃ T : VV K lam →ₗ[K] VV K lam, (∀ w ∈ W, T w ∈ W) ∧ ∀ k : VVIdx lam,
      ((T (bVV K lam k) : VV K lam) : Pol K ι n) =
        ten (Function.update (fun τ => ssB K (lam τ).natW (k τ)) τ₀
          (φ (bSq (lam τ₀) (k τ₀)) : MvPolynomial (Fin n × Fin n) K)) := by
  obtain ⟨s, c, hc⟩ := hφ
  refine ⟨∑ g ∈ s, c g • rhoK lam (Function.update 1 τ₀ g), ?_, ?_⟩
  · intro w hw
    rw [LinearMap.sum_apply]
    exact Submodule.sum_mem _ fun g _ => by
      rw [LinearMap.smul_apply]
      exact W.smul_mem _ (hW _ _ hw)
  · intro k
    rw [hc, bSq_coe, ← tenAt_apply, map_sum, LinearMap.sum_apply, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [LinearMap.smul_apply, Submodule.coe_smul, map_smul]
    congr 1
    rw [rhoK_coe, bVV_coe, bVVfun, actTen K ι n lam _ _, tenAt_apply]
    congr 1
    funext τ
    by_cases h : τ = τ₀
    · subst h; simp
    · rw [Function.update_of_ne h, Function.update_of_ne h, Pi.one_apply, sqAct_one_of_mem _ (ssB_mem _ _)]

def elemOp (lam : DomWeight n) (a b : Formalism.GradedWeylDivisibility.ssIdx n n lam.natW) : nablaSq K n lam →ₗ[K] nablaSq K n lam :=
  ((bSq lam).coord a).smulRight (bSq lam b)

theorem exists_elem (lam : ι → DomWeight n)
    (H : ∀ τ, ∀ φ : nablaSq K n (lam τ) →ₗ[K] nablaSq K n (lam τ), ∃ (s : Finset (GL (Fin n) K)) (c : GL (Fin n) K → K),
      ∀ f : nablaSq K n (lam τ), (φ f : MvPolynomial (Fin n × Fin n) K) = ∑ g ∈ s, c g • sqAct K n (lam τ) g f)
    (W : Submodule K (VV K lam)) (hW : ∀ g : ι → GL (Fin n) K, ∀ w ∈ W, rhoK lam g w ∈ W)
    (τ₀ : ι) (a b : Formalism.GradedWeylDivisibility.ssIdx n n (lam τ₀).natW) :
    ∃ T : VV K lam →ₗ[K] VV K lam, (∀ w ∈ W, T w ∈ W) ∧ ∀ k : VVIdx lam,
      T (bVV K lam k) = if k τ₀ = a then bVV K lam (Function.update k τ₀ b) else 0 := by
  obtain ⟨T, hTW, hT⟩ := exists_op lam τ₀ (elemOp (lam τ₀) a b) (H τ₀ _) W hW
  refine ⟨T, hTW, fun k => Subtype.ext ?_⟩
  rw [hT k]
  have e : (elemOp (K := K) (lam τ₀) a b (bSq (lam τ₀) (k τ₀)) : MvPolynomial (Fin n × Fin n) K) =
      (if k τ₀ = a then (1 : K) else 0) • ssB K (lam τ₀).natW b := by
    simp only [elemOp, LinearMap.smulRight_apply, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_apply, Submodule.coe_smul, bSq_coe]
  rw [e, ← tenAt_apply, map_smul, tenAt_apply, ten_update_ssB]
  split_ifs <;> simp

end General

theorem eq_bot_or_eq_top : ∀ (K : Type) [Field K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n),
    (∀ τ, ∀ φ : nablaSq K n (lam τ) →ₗ[K] nablaSq K n (lam τ), ∃ (s : Finset (GL (Fin n) K)) (c : GL (Fin n) K → K),
      ∀ f : nablaSq K n (lam τ), (φ f : MvPolynomial (Fin n × Fin n) K) = ∑ g ∈ s, c g • sqAct K n (lam τ) g f) →
    ∀ W : Submodule K (Formalism.L2.DIV.VV K lam), (∀ g : ι → GL (Fin n) K, ∀ w ∈ W, Formalism.L2.DIV.rhoK lam g w ∈ W) →
      W = ⊥ ∨ W = ⊤ := by
  intro K _ ι _ n lam H W hW
  classical
  by_cases hW0 : W = ⊥
  · exact Or.inl hW0
  right
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  obtain ⟨i, hi⟩ : ∃ i, (bVV K lam).repr w i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hw0 ((bVV K lam).ext_elem fun k => by simp [h k])
  have hproj : ∀ S : Finset ι, (∑ k ∈ Finset.univ.filter (fun k : VVIdx lam => ∀ τ ∈ S, k τ = i τ),
      (bVV K lam).repr w k • bVV K lam k) ∈ W := by
    intro S
    refine Finset.induction_on S ?_ ?_
    · have hf : Finset.univ.filter (fun k : VVIdx lam => ∀ τ ∈ (∅ : Finset ι), k τ = i τ) = Finset.univ := by
        ext k; simp
      rw [hf, (bVV K lam).sum_repr w]
      exact hw
    · intro a S ha ih
      obtain ⟨T, hTW, hT⟩ := exists_elem lam H W hW a (i a) (i a)
      have h1 := hTW _ ih
      rw [map_sum] at h1
      convert h1 using 1
      simp only [map_smul, hT]
      rw [Finset.sum_filter, Finset.sum_filter]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hk : k a = i a
      · have hu : Function.update k a (i a) = k := by rw [← hk, Function.update_eq_self]
        simp [hk, hu, Finset.forall_mem_insert]
      · simp [hk, Finset.forall_mem_insert]
  have hi' : bVV K lam i ∈ W := by
    have h := hproj Finset.univ
    have hf : Finset.univ.filter (fun k : VVIdx lam => ∀ τ ∈ (Finset.univ : Finset ι), k τ = i τ) = {i} := by
      ext k; simp [funext_iff]
    rw [hf, Finset.sum_singleton] at h
    have := W.smul_mem ((bVV K lam).repr w i)⁻¹ h
    rwa [smul_smul, inv_mul_cancel₀ hi, one_smul] at this
  have hall : ∀ j, bVV K lam j ∈ W := by
    intro j
    have key : ∀ S : Finset ι, bVV K lam (fun τ => if τ ∈ S then j τ else i τ) ∈ W := by
      intro S
      refine Finset.induction_on S ?_ ?_
      · simpa using hi'
      · intro a S ha ih
        obtain ⟨T, hTW, hT⟩ := exists_elem lam H W hW a (i a) (j a)
        have h1 := hTW _ ih
        rw [hT, if_pos (by simp [ha])] at h1
        convert h1 using 2
        funext τ
        by_cases h : τ = a
        · subst h; simp
        · simp [h, Function.update_of_ne h]
    simpa using key Finset.univ
  rw [eq_top_iff]
  intro x _
  rw [← (bVV K lam).sum_repr x]
  exact W.sum_mem fun k _ => W.smul_mem _ (hall k)

end GlobalTheory.TensorIrr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComapRealSubfieldEqIffEqOrIsConjPlaceStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comap_realSubfield_eq_iff_eq_or_isConjPlace : ∀ (D : D7) (P P' : PlE D.host),
    P.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) =
      P'.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) ↔ (P = P' ∨ IsConjPl D.host P P') := by
  first | exact @GlobalTheory.PlacePair.comap_eq_iff | exact GlobalTheory.PlacePair.comap_eq_iff | (intros; apply GlobalTheory.PlacePair.comap_eq_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousChiDet
section
noncomputable section

open NumberField MeasureTheory Matrix Formalism.L2.Host
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory.OneRep

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}
  (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (χ : HChar E)

def twR : GA E a →* (L2 (latticeGL E a) μ →L[ℂ] L2 (latticeGL E a) μ) where
  toFun g := (((chiDet a χ g)⁻¹ : ℂˣ) : ℂ) • R (latticeGL E a) μ g
  map_one' := by simp
  map_mul' g h := by simp only [map_mul, mul_inv, Units.val_mul, smul_mul_smul_comm]

def Repr (F : L2 (latticeGL E a) μ) (φ : GA E a → ℂ) : Prop :=
  lift (latticeGL E a) F =ᵐ[μ] fun g => φ g * ((chiDet a χ g : ℂˣ) : ℂ)

def cls (V : Submodule ℂ (Sm E a)) : Submodule ℂ (L2 (latticeGL E a) μ) :=
  classes (V.map (mulChi a χ).toLinearMap) μ

variable {μ χ}

namespace Repr

variable {F F' : L2 (latticeGL E a) μ} {φ φ' : GA E a → ℂ}

theorem twR (h : Repr μ χ F φ) (k : GA E a) : Repr μ χ (twR μ χ k F) fun g => φ (g * k) := by
  filter_upwards [ae_quotMeasure_iff.1 (Lp.coeFn_smul (((chiDet a χ k)⁻¹ : ℂˣ) : ℂ) (R (latticeGL E a) μ k F)),
    lift_R k F, (measurePreserving_mul_right μ k).quasiMeasurePreserving.ae h] with g e1 e2 e3
  refine e1.trans ?_
  change _ * lift _ (R (latticeGL E a) μ k F) g = _
  rw [e2, e3, map_mul, Units.val_mul, Units.val_inv_eq_inv_val]
  field_simp

omit [μ.IsMulRightInvariant]

theorem zero : Repr μ χ 0 0 := by
  filter_upwards [ae_quotMeasure_iff.1 (Lp.coeFn_zero ℂ 2 (AutomorphicL2Unitary.quotMeasure (latticeGL E a) μ))] with g e
  exact e.trans (zero_mul _).symm

theorem add (h : Repr μ χ F φ) (h' : Repr μ χ F' φ') : Repr μ χ (F + F') (φ + φ') := by
  filter_upwards [ae_quotMeasure_iff.1 (Lp.coeFn_add F F'), h, h'] with g e1 e2 e3
  exact e1.trans ((congrArg₂ (· + ·) e2 e3).trans (add_mul _ _ _).symm)

theorem smul (h : Repr μ χ F φ) (c : ℂ) : Repr μ χ (c • F) (c • φ) := by
  filter_upwards [ae_quotMeasure_iff.1 (Lp.coeFn_smul c F), h] with g e1 e2
  exact e1.trans ((congrArg (c * ·) e2).trans (mul_assoc _ _ _).symm)

theorem sum {ι : Type*} (s : Finset ι) {F : ι → L2 (latticeGL E a) μ} {φ : ι → GA E a → ℂ}
    (h : ∀ i ∈ s, Repr μ χ (F i) (φ i)) : Repr μ χ (∑ i ∈ s, F i) (∑ i ∈ s, φ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem unique (h : Repr μ χ F φ) (h' : Repr μ χ F' φ) : F = F' := l2DiscreteQuotient_ext_iff_lift_ae_eq.2 (h.trans h'.symm)

end Repr

end GlobalTheory.OneRep

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContragredientIsIrreducibleFiniteDimensional
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory

theorem contragredient_isIrreducible : ∀ (k : Type) [Field k] (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V), ρ.IsIrreducible → ρ.dual.IsIrreducible := by
  intro k _ G _ V _ _ _ ρ hρ
  haveI : Nontrivial V := by
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    exact (bot_ne_top (α := Subrepresentation ρ))
      (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))
  have hdualNT : Nontrivial (Module.Dual k V) := inferInstance
  refine { toNontrivial := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun S => ?_ }
  · have h' := congrArg Subrepresentation.toSubmodule h
    obtain ⟨x, y, hxy⟩ := hdualNT
    have hx : x ∈ (⊤ : Subrepresentation ρ.dual).toSubmodule := Submodule.mem_top
    have hy : y ∈ (⊤ : Subrepresentation ρ.dual).toSubmodule := Submodule.mem_top
    rw [← h'] at hx hy
    exact hxy (((Submodule.mem_bot k).1 hx).trans ((Submodule.mem_bot k).1 hy).symm)
  · let T : Subrepresentation ρ := ⟨S.toSubmodule.dualCoannihilator, fun g v hv => by
      rw [Submodule.mem_dualCoannihilator] at hv ⊢
      intro φ hφ
      have h1 := hv _ (S.apply_mem_toSubmodule g⁻¹ hφ)
      simpa [Representation.dual_apply, Module.Dual.transpose_apply] using h1⟩
    have hST : S.toSubmodule = T.toSubmodule.dualAnnihilator :=
      (Subspace.dualCoannihilator_dualAnnihilator_eq (W := S.toSubmodule)).symm
    rcases hρ.eq_bot_or_eq_top T with hT | hT
    · right
      apply Subrepresentation.toSubmodule_injective
      rw [hST, hT]
      exact Submodule.dualAnnihilator_bot
    · left
      apply Subrepresentation.toSubmodule_injective
      rw [hST, hT]
      exact Submodule.dualAnnihilator_top

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryRealPointsActFockSubstitutionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteUnitary_realPoints_act_fock_substitution : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (θ : InfFam D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (f : WO V W → ℂ), IsWeilDatumO ψ V W χS χT ω → IsInfFam θ → V.SigOK → W.SigOK → AllPlus M → AllPlus M' → IsThetaFunO ψ V W f → (∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO (cart M τ) (cart M' τ)) f) → ∀ τ, (∀ g : Matrix.unitaryGroup (Fin V.rank) ℂ, ∃ c : ℂ, c ≠ 0 ∧ ∀ P, ω (atTau θ V τ (unfr M τ g), 1) (ptOf ψ θ M M' f P) = c • ptOf ψ θ M M' f (colSub W.rank τ g P)) ∧ ∀ u : Matrix.unitaryGroup (Fin W.rank) ℂ, ∃ c : ℂ, c ≠ 0 ∧ ∀ P, ω (1, atTau θ W τ (unfr M' τ u)) (ptOf ψ θ M M' f P) = c • ptOf ψ θ M M' f (rowSub V.rank τ u P) := by
  first | exact @GlobalTheory.DefLift.FockAct.fock_act | exact GlobalTheory.DefLift.FockAct.fock_act | (intros; apply GlobalTheory.DefLift.FockAct.fock_act <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiamondOperatorHermitianSideLevelPrimeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diamondOperator_hermitian_side_levelPrime : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u i v (a : (((I.rec7 l Z).mem u).A.Fv v)ˣ) (c : ((I.rec7 l Z).mem u).C.cls i), ∃ γ, i ≤ (I.rec7 l Z).R.m → DilCl (F u).atT (F u).lv i v a c γ ∧ AdOf H u i c (((I.rec7 l Z).fm u).dil i v a c) γ v := by
  first | exact @GlobalTheory.Mem.Col2.HAt.Dil.diamond_on_hermitian_side | exact GlobalTheory.Mem.Col2.HAt.Dil.diamond_on_hermitian_side | (intros; apply GlobalTheory.Mem.Col2.HAt.Dil.diamond_on_hermitian_side <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAveragedOperatorMappingToKFiniteStatement
section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_averaged_operator_mapping_to_KFinite : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ a : H, a ≠ 0 → ∀ v, IsKFin ε σ v → ∃ T : H → H, IsAvg ε σ T ∧ T a = v := by
  first | exact @GlobalTheory.TypeSum.exists_isAvg_apply_eq | exact GlobalTheory.TypeSum.exists_isAvg_apply_eq | (intros; apply GlobalTheory.TypeSum.exists_isAvg_apply_eq <;> assumption)
end

