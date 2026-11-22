import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0014
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMahler
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LowerBoundConditional
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0011

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PProjSecDomain
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace ProjSecDomain

abbrev Kf (e : ℕ) : Type := FractionRing (MvPolynomial (Fin (e + 1)) ℂ)

variable {n e : ℕ} (W : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (e + 1)) (Fin n) ℂ)

abbrev S : Type :=
  Vertical.SecAlg (W.map (MvPolynomial.map (algebraMap ℂ (Kf e)))) (projPar A)

theorem map_linPoly (k : Fin (e + 1)) :
    MvPolynomial.map (algebraMap ℂ (Kf e)) (ComplexSets.linPoly A k) =
      linForm fun j => algebraMap ℂ (Kf e) (A k j) := by
  simp [ComplexSets.linPoly, linForm, map_sum]

theorem projVar_ne_zero (k : Fin (e + 1)) : projVar e k ≠ 0 := by
  rw [projVar, ne_eq, IsFractionRing.to_map_eq_zero_iff]; exact X_ne_zero k

theorem chartForm_eq : Vertical.chartForm (projPar A) =
    C (projVar e 0)⁻¹ * linForm fun j => algebraMap ℂ (Kf e) (A 0 j) := by
  simp [Vertical.chartForm, linForm, projPar, Finset.mul_sum, div_eq_mul_inv, mul_comm, mul_left_comm]

theorem secForm_eq (i : Fin e) : Vertical.secForm (projPar A) i =
    C (projVar e i.succ) * (linForm fun j => algebraMap ℂ (Kf e) (A 0 j)) -
      C (projVar e 0) * linForm fun j => algebraMap ℂ (Kf e) (A i.succ j) := by
  simp [Vertical.secForm, linForm, projPar, Finset.mul_sum, ← Finset.sum_sub_distrib, sub_mul, mul_assoc]

variable {W A}

theorem mk_row (k : Fin (e + 1)) :
    Ideal.Quotient.mk (Vertical.secIdeal (W.map (MvPolynomial.map (algebraMap ℂ (Kf e)))) (projPar A))
        (linForm fun j => algebraMap ℂ (Kf e) (A k j)) =
      algebraMap (Kf e) (S W A) (projVar e k) := by
  set q := Ideal.Quotient.mk (Vertical.secIdeal (W.map (MvPolynomial.map (algebraMap ℂ (Kf e)))) (projPar A))
  have hC : ∀ c, q (C c) = algebraMap (Kf e) (S W A) c := fun _ => rfl
  have hu : q (C (projVar e 0)) * q (C ((projVar e 0)⁻¹)) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ (projVar_ne_zero 0), map_one, map_one]
  have hch : q (Vertical.chartForm (projPar A) - 1) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  rw [map_sub, map_one, chartForm_eq, map_mul] at hch
  have ha0 : q (linForm fun j => algebraMap ℂ (Kf e) (A 0 j)) = q (C (projVar e 0)) := by
    linear_combination q (C (projVar e 0)) * hch - q (linForm fun j => algebraMap ℂ (Kf e) (A 0 j)) * hu
  induction k using Fin.cases with
  | zero => rw [ha0, hC]
  | succ i =>
    have hs : q (Vertical.secForm (projPar A) i) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2
        (Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩)))
    rw [secForm_eq, map_sub, map_mul, map_mul, ha0] at hs
    rw [← hC]
    linear_combination (-q (C ((projVar e 0)⁻¹))) * hs +
      (q (C (projVar e i.succ)) - q (linForm fun j => algebraMap ℂ (Kf e) (A i.succ j))) * hu

variable (W A)

def psi : MvPolynomial (Fin n) ℂ ⧸ W →+* S W A :=
  Ideal.Quotient.lift W
    ((Ideal.Quotient.mk _).comp (MvPolynomial.map (algebraMap ℂ (Kf e))))
    fun _ hf => Ideal.Quotient.eq_zero_iff_mem.2
      (Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hf)))

def M : Submonoid (MvPolynomial (Fin n) ℂ ⧸ W) :=
  (nonZeroDivisors (MvPolynomial (Fin (e + 1)) ℂ)).map (ComplexSets.projHom W A)

abbrev T : Type := Localization (M W A)

def kappa : Kf e →+* T W A :=
  IsLocalization.lift (M := nonZeroDivisors (MvPolynomial (Fin (e + 1)) ℂ)) (S := Kf e) (P := T W A)
    (g := (algebraMap _ (T W A)).comp (ComplexSets.projHom W A).toRingHom)
    fun y => IsLocalization.map_units (T W A) (⟨_, Submonoid.mem_map_of_mem _ y.2⟩ : M W A)

def phi : MvPolynomial (Fin n) (Kf e) →+* T W A :=
  eval₂Hom (kappa W A) fun j => algebraMap _ (T W A) (Ideal.Quotient.mk W (X j))

variable {W A}

theorem psi_mk (f : MvPolynomial (Fin n) ℂ) : psi W A (Ideal.Quotient.mk W f) =
    Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap ℂ (Kf e)) f) := rfl

theorem projHom_X (k : Fin (e + 1)) :
    ComplexSets.projHom W A (X k) = Ideal.Quotient.mk W (ComplexSets.linPoly A k) := by
  rw [ComplexSets.projHom, AlgHom.comp_apply, ComplexSets.pullback, aeval_X]; rfl

theorem psi_comp_projHom :
    (psi W A).comp (ComplexSets.projHom W A).toRingHom =
      (algebraMap (Kf e) (S W A)).comp (algebraMap (MvPolynomial (Fin (e + 1)) ℂ) (Kf e)) := by
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun k => ?_)
  · have h1 : algebraMap (MvPolynomial (Fin (e + 1)) ℂ) (Kf e) (C r) = algebraMap ℂ (Kf e) r :=
      (IsScalarTower.algebraMap_apply ℂ _ (Kf e) r).symm
    have h2 : ComplexSets.projHom W A (C r) = Ideal.Quotient.mk W (C r) := (ComplexSets.projHom W A).commutes r
    rw [RingHom.comp_apply, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h1, h2, psi_mk,
      map_C]
    rfl
  · rw [RingHom.comp_apply, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, projHom_X,
      psi_mk, map_linPoly, mk_row]
    rfl

theorem kappa_alg (p : MvPolynomial (Fin (e + 1)) ℂ) :
    kappa W A (algebraMap _ (Kf e) p) = algebraMap _ (T W A) (ComplexSets.projHom W A p) := by
  unfold kappa; exact IsLocalization.lift_eq _ p

theorem phi_C (c : Kf e) : phi W A (C c) = kappa W A c := eval₂Hom_C _ _ _

theorem phi_map (f : MvPolynomial (Fin n) ℂ) :
    phi W A (MvPolynomial.map (algebraMap ℂ (Kf e)) f) = algebraMap _ (T W A) (Ideal.Quotient.mk W f) := by
  have : (phi W A).comp (MvPolynomial.map (algebraMap ℂ (Kf e))) =
      (algebraMap _ (T W A)).comp (Ideal.Quotient.mk W) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_)
    · rw [RingHom.comp_apply, RingHom.comp_apply, map_C, phi_C,
        IsScalarTower.algebraMap_apply ℂ (MvPolynomial (Fin (e + 1)) ℂ) (Kf e), kappa_alg, AlgHom.commutes]
      rfl
    · rw [RingHom.comp_apply, RingHom.comp_apply, map_X, phi, eval₂Hom_X']
  exact RingHom.congr_fun this f

theorem phi_row (k : Fin (e + 1)) :
    phi W A (linForm fun j => algebraMap ℂ (Kf e) (A k j)) = kappa W A (projVar e k) := by
  rw [← map_linPoly, phi_map, projVar, kappa_alg, projHom_X]

theorem secIdeal_le_ker :
    Vertical.secIdeal (W.map (MvPolynomial.map (algebraMap ℂ (Kf e)))) (projPar A) ≤
      RingHom.ker (phi W A) := by
  have hu : kappa W A (projVar e 0)⁻¹ * kappa W A (projVar e 0) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ (projVar_ne_zero 0), map_one]
  refine sup_le (sup_le ?_ ?_) ?_
  · rw [Ideal.map_le_iff_le_comap]; intro f hf
    rw [Ideal.mem_comap, RingHom.mem_ker, phi_map, Ideal.Quotient.eq_zero_iff_mem.2 hf, map_zero]
  · rw [Ideal.span_le]; rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, secForm_eq, map_sub, map_mul, map_mul, phi_C, phi_C, phi_row,
      phi_row]
    ring
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one,
      chartForm_eq, map_mul, phi_C, phi_row, hu, sub_self]

variable (W A)

def g : S W A →+* T W A := Ideal.Quotient.lift _ (phi W A) fun _ hf => RingHom.mem_ker.1 (secIdeal_le_ker hf)

theorem psi_unit (y : M W A) : IsUnit (psi W A y) := by
  obtain ⟨_, p, hp, rfl⟩ := y
  have h := RingHom.congr_fun (psi_comp_projHom (W := W) (A := A)) p
  rw [RingHom.comp_apply, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h
  rw [h]
  exact (IsUnit.mk0 _ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hp)).map _

def chi : T W A →+* S W A :=
  IsLocalization.lift (M := M W A) (S := T W A) (P := S W A) (g := psi W A) (psi_unit W A)

variable {W A}

theorem chi_kappa : (chi W A).comp (kappa W A) = algebraMap (Kf e) (S W A) := by
  refine IsLocalization.ringHom_ext (nonZeroDivisors (MvPolynomial (Fin (e + 1)) ℂ)) ?_
  rw [RingHom.comp_assoc, kappa, IsLocalization.lift_comp, ← RingHom.comp_assoc, chi,
    IsLocalization.lift_comp, psi_comp_projHom]

theorem chi_g (s : S W A) : chi W A (g W A s) = s := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective s
  have : (chi W A).comp (phi W A) = Ideal.Quotient.mk _ := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun j => ?_)
    · rw [RingHom.comp_apply, phi_C, ← RingHom.comp_apply, chi_kappa]; rfl
    · rw [RingHom.comp_apply, phi, eval₂Hom_X', chi, IsLocalization.lift_eq, psi_mk, map_X]
  show chi W A (phi W A f) = _
  exact RingHom.congr_fun this f

theorem proof : ProjSecDomain.Statement := by
  intro n e W A hW hA
  have hM : M W A ≤ nonZeroDivisors _ := by
    rintro _ ⟨p, hp, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero fun h =>
      nonZeroDivisors.ne_zero hp (hA.injective (by rw [map_zero]; exact h))
  have : IsDomain (T W A) := IsLocalization.isDomain_localization hM
  refine ⟨Function.Injective.isDomain (g W A) (Function.LeftInverse.injective chi_g), ?_⟩
  let _ : Algebra (MvPolynomial (Fin (e + 1)) ℂ) (MvPolynomial (Fin n) ℂ ⧸ W) :=
    (ComplexSets.projHom W A).toRingHom.toAlgebra
  have hint (j : Fin n) : IsIntegral (Kf e) (Ideal.Quotient.mk
      (Vertical.secIdeal (W.map (MvPolynomial.map (algebraMap ℂ (Kf e)))) (projPar A)) (X j)) := by
    have := IsIntegral.map_of_comp_eq (algebraMap _ (Kf e)) (psi W A) psi_comp_projHom.symm
      (hA.finite.to_isIntegral (Ideal.Quotient.mk W (X j)))
    rwa [psi_mk, map_X] at this
  have : Algebra.IsIntegral (Kf e) (S W A) := ⟨fun s => by
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective s
    induction f using MvPolynomial.induction_on with
    | C c => exact isIntegral_algebraMap
    | add p q hp hq => rw [map_add]; exact hp.add hq
    | mul_X p j hp => rw [map_mul]; exact hp.mul (hint j)⟩
  have : Algebra.FiniteType (Kf e) (S W A) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ (Kf e) _)
      (Ideal.Quotient.mkₐ_surjective _ _)
  exact Algebra.IsIntegral.finite

end ProjSecDomain

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PProperSymm
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Ideal

theorem localMult_ne_zero_of_mem_minimalPrimes {A : Type*} [CommRing A] [IsNoetherianRing A]
    {J P : Ideal A} (hP : P ∈ J.minimalPrimes) : localMult J P ≠ 0 := by
  have hPp : P.IsPrime := hP.1.1
  unfold localMult
  rw [dif_pos hPp]
  let R := Localization.AtPrime P
  let I : Ideal R := J.map (algebraMap A R)
  have hmin : IsLocalRing.maximalIdeal R ∈ I.minimalPrimes := by
    rw [IsLocalization.minimalPrimes_map P.primeCompl R J, Set.mem_preimage,
      Localization.AtPrime.under_maximalIdeal]
    exact hP
  have := IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing I hmin
  have : IsArtinian R (R ⧸ I) :=
    isArtinian_of_surjective_algebraMap (Ideal.Quotient.mk_surjective (I := I))
  have : IsNoetherian R (R ⧸ I) := isNoetherian_quotient I
  have hI : I ≠ ⊤ := ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top hmin.1.2
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  rw [Ne, ENat.toNat_eq_zero, not_or]
  exact ⟨(Module.length_pos (R := R) (M := R ⧸ I)).ne', Module.length_ne_top⟩

theorem ProperSymm.proof : ProperSymm.Statement := by
  intro n W u u' hW hu hu' hadm W'' hW'' hlu
  classical
  have hval := Finsupp.mem_support_iff.mp hW''
  simp only [divCycle, fundCycle, Finsupp.onFinset_apply] at hval
  have hrel : W'' ∈ relComps (W ⊔ span {linForm u'}) := by
    by_contra h
    exact hval (if_neg h)
  obtain ⟨hmin'', hrel''⟩ := hrel
  have : W''.IsPrime := hmin''.1.1
  have hle : W ⊔ span {linForm u} ≤ W'' :=
    sup_le (le_sup_left.trans hmin''.1.2) ((span_singleton_le_iff_mem _).mpr hlu)
  obtain ⟨W', hW', hW'le⟩ := Ideal.exists_minimalPrimes_le hle
  have hrel' : IsRelevant W' := by
    obtain ⟨j, hj⟩ := hrel''
    exact ⟨j, fun h => hj (hW'le h)⟩
  have hsupp : W' ∈ (divCycle W u).support := by
    rw [Finsupp.mem_support_iff]
    simp only [divCycle, fundCycle, Finsupp.onFinset_apply]
    rw [if_pos ⟨hW', hrel'⟩]
    exact localMult_ne_zero_of_mem_minimalPrimes hW'
  have hu'W' : linForm u' ∉ W' := hadm W' hsupp
  have : W'.IsPrime := hW'.1.1
  have : W.IsPrime := hW.isPrime
  have hWW' : W ≤ W' := le_sup_left.trans hW'.1.2
  have huW' : linForm u ∈ W' := hW'.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hu'W'' : linForm u' ∈ W'' :=
    hmin''.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  let f := Ideal.Quotient.mk W
  have hf : Function.Surjective f := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker f = W := Ideal.mk_ker
  have : (W'.map f).IsPrime := Ideal.map_isPrime_of_surjective hf (by rw [hker]; exact hWW')
  have : (W''.map f).IsPrime :=
    Ideal.map_isPrime_of_surjective hf (by rw [hker]; exact hWW'.trans hW'le)
  have : IsDomain (MvPolynomial (Fin n) ℂ ⧸ W) := Ideal.Quotient.isDomain W
  have : (⊥ : Ideal (MvPolynomial (Fin n) ℂ ⧸ W)).IsPrime := Ideal.isPrime_bot
  have h0 : (⊥ : Ideal (MvPolynomial (Fin n) ℂ ⧸ W)) < W'.map f := by
    refine bot_lt_iff_ne_bot.mpr fun h => hu ?_
    have hm := Ideal.mem_map_of_mem f huW'
    rw [h, Ideal.mem_bot] at hm
    exact Ideal.Quotient.eq_zero_iff_mem.mp hm
  have h1 : W'.map f < W''.map f := by
    refine lt_of_le_of_ne (Ideal.map_mono hW'le) fun h => hu'W' ?_
    have hm := Ideal.mem_map_of_mem f hu'W''
    rw [← h, ← Ideal.mem_comap, Ideal.comap_map_of_surjective' f hf, hker,
      sup_eq_left.mpr hWW'] at hm
    exact hm
  have e1 := Ideal.height_add_one_le_of_lt_of_isPrime h0
  have e2 := Ideal.height_add_one_le_of_lt_of_isPrime h1
  have e3 : (W''.map f).height ≤ 1 := Ideal.map_height_le_one_of_mem_minimalPrimes hmin''
  rw [Ideal.height_bot, zero_add] at e1
  have h2 : (2 : ℕ∞) ≤ 1 :=
    calc (2 : ℕ∞) = 1 + 1 := by norm_num
      _ ≤ (W'.map f).height + 1 := by gcongr
      _ ≤ (W''.map f).height := e2
      _ ≤ 1 := e3
  exact absurd h2 (by norm_num)

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PRecursion
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory NumberField

noncomputable section

theorem map_specFirst {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S) {k n : ℕ}
    (f : MvPolynomial (Fin (k + 1) × Fin n) R) (u : Fin n → R) :
    MvPolynomial.map φ (specFirst f u) = specFirst (MvPolynomial.map φ f) (fun j => φ (u j)) := by
  unfold specFirst
  rw [map_bind₁]
  congr 2
  funext ij
  obtain ⟨i, j⟩ := ij
  induction i using Fin.cases with
  | zero => simp [specFirstVar]
  | succ i => simp [specFirstVar]

theorem ChowHeightRecursion.proof (hV : ChowFormSectionVertical.Statement) (hA : MahlerSection.Statement)
    (hB : ChowFormBaseChange.Statement) (hAv : BaseChangeAvoid.Statement) :
    ChowHeightRecursion.Statement := by
  intro K _ _ n e δ H I f u hI hf hδ hu
  set u' : Fin n → K := fun j => (u j : K) with hu'
  set g := specFirst f u' with hg

  have hfin_f := log_gaussNorm_support_finite (K := K) hf.1
  have hfin_g : (Function.support fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
      Real.log (gaussNorm v g)).Finite := by
    by_cases hg0 : g = 0
    · have : (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) => Real.log (gaussNorm v g)) = 0 := by
        funext v
        rw [hg0]
        simp [gaussNorm]
        exact Or.inl rfl
      rw [this, Function.support_zero]
      exact Set.finite_empty
    · exact log_gaussNorm_support_finite hg0
  have hfinsum : ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), Real.log (gaussNorm v f) =
      (∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), Real.log (gaussNorm v g)) + vertTerm I (e + 1) u := by
    unfold vertTerm
    rw [← finsum_add_distrib hfin_g]
    · refine finsum_congr fun v => ?_
      rw [← hV K n e I f u hI hf hu v]
      ring
    · refine Set.Finite.subset (hfin_f.union hfin_g) fun v hv => ?_
      rw [Function.mem_support, ← hV K n e I f u hI hf hu v] at hv
      by_contra hcon
      simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hcon
      exact hv (by rw [hcon.1, hcon.2, sub_zero])

  have harch : ∀ σ : K →+* ℂ, mahler (H.normAt σ) (e + 1) (f.map σ) =
      mahler (H.normAt σ) e (g.map σ) - δ * (harmonic (n - 1) : ℝ) / 2 -
        cycleIntegral (H.normAt σ) (fundCycle (I.map (MvPolynomial.map σ))) e
          (fsLog (H.normAt σ) fun j => σ (u j)) := by
    intro σ
    obtain ⟨hprime, hcyc⟩ := hB K n (e + 1) I f σ hI hf
    have hδσ : IsMultiHomog δ (MvPolynomial.map σ f) :=
      (isMultiHomog_iff _ _).mpr fun i => IsWeightedHomogeneous.map' ((isMultiHomog_iff _ _).mp hδ i) σ
    have h := hA n e δ (H.normAt σ) _ _ (fun j => σ (u j)) hprime hcyc hδσ
      (fun W hW => hAv K n I u' σ hI hu W hW)
    rw [hg, map_specFirst, h]
    ring
  unfold chowHt
  have hs : ∑ σ : K →+* ℂ, (mahler (H.normAt σ) (e + 1) (f.map σ) +
        ((e + 1 : ℕ) : ℝ) * δ * (harmonic (n - 1) : ℝ) / 2) =
      ∑ σ : K →+* ℂ, (mahler (H.normAt σ) e (g.map σ) + (e : ℝ) * δ * (harmonic (n - 1) : ℝ) / 2) -
        ∑ σ : K →+* ℂ, cycleIntegral (H.normAt σ) (fundCycle (I.map (MvPolynomial.map σ))) e
          (fsLog (H.normAt σ) fun j => σ (u j)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [harch σ]
    push_cast
    ring
  rw [hfinsum, hs]
  ring

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PSpecFirstRename
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem SpecFirstRename.proof : SpecFirstRename.Statement := by
  intro n k f u u'
  simp only [specFirst, bind₁_bind₁, bind₁_rename]
  refine congrArg (fun φ => bind₁ φ f) (funext fun ij => ?_)
  obtain ⟨i, j⟩ := ij
  have one : (1 : Fin (k + 1 + 1)) = Fin.succ 0 := Fin.succ_zero_eq_one.symm
  cases i using Fin.cases with
  | zero =>
    show (bind₁ (specFirstVar u')) (specFirstVar u (Equiv.swap (0 : Fin (k + 1 + 1)) 1 0, j)) =
      (bind₁ (specFirstVar u)) (specFirstVar u' (0, j))
    rw [Equiv.swap_apply_left, one]
    simp only [specFirstVar, Fin.cases_succ, Fin.cases_zero, bind₁_X_right, bind₁_C_right]
  | succ i =>
    cases i using Fin.cases with
    | zero =>
      show (bind₁ (specFirstVar u'))
          (specFirstVar u (Equiv.swap (0 : Fin (k + 1 + 1)) 1 (Fin.succ 0), j)) =
        (bind₁ (specFirstVar u)) (specFirstVar u' (Fin.succ 0, j))
      have h : Equiv.swap (0 : Fin (k + 1 + 1)) 1 (Fin.succ 0) = 0 := by
        rw [← one]; exact Equiv.swap_apply_right _ _
      rw [h]
      simp only [specFirstVar, Fin.cases_succ, Fin.cases_zero, bind₁_X_right, bind₁_C_right]
    | succ i =>
      show (bind₁ (specFirstVar u'))
          (specFirstVar u (Equiv.swap (0 : Fin (k + 1 + 1)) 1 (Fin.succ (Fin.succ i)), j)) =
        (bind₁ (specFirstVar u)) (specFirstVar u' (Fin.succ (Fin.succ i), j))
      have h : Equiv.swap (0 : Fin (k + 1 + 1)) 1 (Fin.succ (Fin.succ i)) = Fin.succ (Fin.succ i) := by
        refine Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) ?_
        rw [one]
        exact fun h' => Fin.succ_ne_zero i (Fin.succ_injective _ h')
      rw [h]
      simp only [specFirstVar, Fin.cases_succ, bind₁_X_right]

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PSpecFirstSwapMahler
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem mahler_C_mul_of_norm_eq_one {n k : ℕ} (h : HermNorm n) (c : ℂ) (hc : ‖c‖ = 1)
    (g : MvPolynomial (Fin k × Fin n) ℂ) : mahler h k (C c * g) = mahler h k g := by
  have hfun : (fun v : Fin k × Fin n → ℂ => Real.log ‖eval v (C c * g)‖) =
      fun v => Real.log ‖eval v g‖ := by
    funext v
    rw [eval_mul, eval_C, norm_mul, hc, one_mul]
  unfold mahler
  rw [hfun]

theorem specFirst_C_mul {n k : ℕ} (c : ℂ) (f : MvPolynomial (Fin (k + 1) × Fin n) ℂ) (u : Fin n → ℂ) :
    specFirst (C c * f) u = C c * specFirst f u := by
  unfold specFirst
  rw [map_mul, bind₁_C_right]

theorem SpecFirstSwapMahler.proof (h1 : SpecFirstRename.Statement) (h2 : ChowCycleSwap.Statement) :
    SpecFirstSwapMahler.Statement := by
  intro n e h Z f u u' hf
  obtain ⟨c, hc2, hren⟩ := h2 ℂ n (e + 1 + 1) Z f hf (Equiv.swap 0 1)
  have hc : ‖c‖ = 1 := by
    have hsq : ‖c‖ ^ 2 = 1 := by rw [← norm_pow, hc2, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg c) two_ne_zero).1 hsq
  have key : specFirst (specFirst f u) u' = C c * specFirst (specFirst f u') u := by
    rw [← h1 n e f u' u, hren, specFirst_C_mul, specFirst_C_mul]
  rw [key, mahler_C_mul_of_norm_eq_one h c hc]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChartChoiceAlgClosed
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def ChartChoiceAlgClosed.Statement : Prop :=
  ∀ (F : Type) [Field F] [IsAlgClosed F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (q : MvPolynomial (Fin e × Fin n) F),
    IsProjPrime I → IsChowForm I (e + 1) f → Prime q → ∃ t : Fin n → F, ¬ q ∣ specFirst f t

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsSectionComponents
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

def SectionComponents.Statement : Prop :=
  ∀ (F : Type) [Field F] (n : ℕ) (J : Ideal (MvPolynomial (Fin n) F)) (f : MvPolynomial (Fin n) F),
    (∀ P ∈ J.minimalPrimes, ∀ Q ∈ J.minimalPrimes,
      ringKrullDim (MvPolynomial (Fin n) F ⧸ P) = ringKrullDim (MvPolynomial (Fin n) F ⧸ Q)) →
    (∀ P ∈ J.minimalPrimes, f ∉ P) →
    ∀ P ∈ J.minimalPrimes, ∀ W : Ideal (MvPolynomial (Fin n) F),
      W ∈ (P ⊔ Ideal.span {f}).minimalPrimes ↔ W ∈ (J ⊔ Ideal.span {f}).minimalPrimes ∧ P ≤ W

end GroundTheory.Heights₂.Heights
end

