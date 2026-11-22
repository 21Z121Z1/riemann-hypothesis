import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0066
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0555
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0125
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsEqTransposeMulDiagonalMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0365
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0303
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0305
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0300
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0307
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0306
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Formalism.CyclotomicNorms.NonsquarefreeBounds.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0549
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0165
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0552
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MayerVietorisExtendClassCoprimeEtaleExcision
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.MVGlue

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Functor.map_comp]

theorem etale_awayMap : ∀ (A C : Type) [CommRing A] [CommRing C] [Algebra A C] [Algebra.Etale A C] (f : A), @Algebra.Etale (Localization.Away f) (Localization.Away (algebraMap A C f)) _ _ (Localization.awayMap (algebraMap A C) f).toAlgebra := by
  intro A C _ _ _ _ f
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap A C f)) :=
    (Localization.awayMap (algebraMap A C) f).toAlgebra
  haveI : Algebra.Etale C (Localization.Away (algebraMap A C f)) := Algebra.Etale.of_isLocalizationAway (algebraMap A C f)
  haveI : Algebra.Etale A (Localization.Away f) := Algebra.Etale.of_isLocalizationAway f
  haveI : Algebra.Etale A (Localization.Away (algebraMap A C f)) := Algebra.Etale.comp A C _
  haveI : IsScalarTower A (Localization.Away f) (Localization.Away (algebraMap A C f)) := by
    refine IsScalarTower.of_algebraMap_eq (fun a => ?_)
    show _ = Localization.awayMap (algebraMap A C) f (algebraMap A (Localization.Away f) a)
    simp [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq, IsScalarTower.algebraMap_apply A C (Localization.Away (algebraMap A C f))]
  exact Algebra.Etale.of_restrictScalars A _ _

theorem pull_spMap_comp (q : ℕ) {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C)
    (n i : ℤ) (x : Ht q (sp A) n i) :
    pull _ (spMap (g.comp f)) _ _ x = pull _ (spMap g) _ _ (pull _ (spMap f) _ _ x) := by
  rw [spMap_comp', pull_comp]

theorem pull_spMap_id (q : ℕ) {A : Type} [CommRing A] (n i : ℤ) (x : Ht q (sp A) n i) :
    pull _ (spMap (RingHom.id A)) _ _ x = x := by
  have : spMap (RingHom.id A) = 𝟙 (sp A) := by
    simp only [spMap, CommRingCat.ofHom_id, Spec.map_id]
    exact sch.map_id _
  rw [this, pull_id]

theorem glue : ∀ (q : ℕ) (A C : Type) [CommRing A] [CommRing C] [Algebra A C] (f g : A), IsCoprime f g → IsExcisionNbhd A C g → ∀ (n i : ℤ) (a : Ht q (sp (Localization.Away (f * g))) n i), pull _ (spMap (Localization.awayMap (algebraMap A C) (f * g))) _ _ a = 0 → ∃ b : Ht q (sp (Localization.Away f)) n i, ∀ ρ : Localization.Away f →+* Localization.Away (f * g), ρ.comp (algebraMap A _) = algebraMap A _ → pull _ (spMap ρ) _ _ b = a := by
  intro q A C _ _ _ f g hfg hC n i a ha
  obtain ⟨hEt, h1, h2⟩ := hC
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap A C f)) :=
    (Localization.awayMap (algebraMap A C) f).toAlgebra
  haveI : Algebra.Etale (Localization.Away f) (Localization.Away (algebraMap A C f)) := etale_awayMap A C f
  have hB : algebraMap (Localization.Away f) (Localization.Away (algebraMap A C f)) =
      Localization.awayMap (algebraMap A C) f := rfl
  set h : Localization.Away f := algebraMap A (Localization.Away f) g with hh
  have c1 := GlobalTheory.T.away_congr_mod_of_isCoprime A C f g hfg h1
  have c2 := GlobalTheory.T.awayMap_span_singleton_divisibility_descends A C f g h2
  rw [← hB] at c1 c2

  have hu1 : IsUnit (((algebraMap (Localization.Away f) (Localization.Away h)).comp
      (algebraMap A (Localization.Away f))) (f * g)) := by
    rw [map_mul, RingHom.comp_apply, RingHom.comp_apply]
    refine IsUnit.mul ?_ ?_
    · exact (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away f) f).map
        (algebraMap (Localization.Away f) (Localization.Away h))
    · exact IsLocalization.Away.algebraMap_isUnit (S := Localization.Away h) h
  let ψ : Localization.Away (f * g) →+* Localization.Away h :=
    IsLocalization.Away.lift (S := Localization.Away (f * g)) (f * g) hu1
  have hψ : ∀ x : A, ψ (algebraMap A _ x) = algebraMap _ _ (algebraMap A (Localization.Away f) x) := fun x => by
    simp only [ψ, IsLocalization.Away.lift_eq, RingHom.comp_apply]
  have hgB : algebraMap (Localization.Away f) (Localization.Away (algebraMap A C f)) h =
      algebraMap C (Localization.Away (algebraMap A C f)) (algebraMap A C g) := by
    rw [hB, hh]
    simp [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
  have hu2 : IsUnit (((algebraMap (Localization.Away (algebraMap A C f))
      (Localization.Away (algebraMap (Localization.Away f) (Localization.Away (algebraMap A C f)) h))).comp
      (algebraMap C (Localization.Away (algebraMap A C f)))) (algebraMap A C (f * g))) := by
    rw [map_mul, map_mul, RingHom.comp_apply, RingHom.comp_apply, ← hgB]
    refine IsUnit.mul ?_ (IsLocalization.Away.algebraMap_isUnit _)
    exact (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (algebraMap A C f)) (algebraMap A C f)).map _
  let χ : Localization.Away (algebraMap A C (f * g)) →+*
      Localization.Away (algebraMap (Localization.Away f) (Localization.Away (algebraMap A C f)) h) :=
    IsLocalization.Away.lift (S := Localization.Away (algebraMap A C (f * g))) (algebraMap A C (f * g)) hu2
  have hsq : (Localization.awayMap (algebraMap (Localization.Away f) (Localization.Away (algebraMap A C f))) h).comp ψ =
      χ.comp (Localization.awayMap (algebraMap A C) (f * g)) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (f * g))
    ext x
    simp only [RingHom.comp_apply, hψ, χ]
    simp [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq, IsLocalization.Away.lift_eq, hB]
  obtain ⟨b, hb, -⟩ := GlobalTheory.T.localization_pullback_injective q (Localization.Away f) (Localization.Away (algebraMap A C f)) h c1 c2 n i
    (pull _ (spMap ψ) _ _ a) 0 (by
      rw [map_zero, ← pull_spMap_comp, hsq, pull_spMap_comp, ha, map_zero])
  refine ⟨b, fun ρ hρ => ?_⟩
  have hρu : IsUnit (ρ h) := by
    rw [hh, ← RingHom.comp_apply, hρ, map_mul] at *
    exact isUnit_of_mul_isUnit_right (by rw [← map_mul]; exact IsLocalization.Away.algebraMap_isUnit (f * g))
  let ψ' : Localization.Away h →+* Localization.Away (f * g) :=
    IsLocalization.Away.lift (S := Localization.Away h) h hρu
  have h1' : ψ'.comp (algebraMap (Localization.Away f) (Localization.Away h)) = ρ :=
    IsLocalization.Away.lift_comp _ _
  have h2' : ψ'.comp ψ = RingHom.id _ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (f * g))
    ext x
    simp only [RingHom.comp_apply, hψ, ψ', IsLocalization.Away.lift_eq, RingHom.id_apply]
    rw [← RingHom.comp_apply ρ, hρ]
  rw [← h1', pull_spMap_comp, hb, ← pull_spMap_comp, h2', pull_spMap_id]

end GlobalTheory.MVGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetaplecticRepresentationHolds
section
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate

namespace GlobalTheory

theorem metaplecticRepresentation_holds : GlobalTheory.Published.MetaplecticRepresentation := by
  intro ι _ _
  obtain ⟨G, iG, tG, tgG, pr, om, omS, φ, hcov, hsurj, ⟨ε, hε1, hker, hεf⟩, hcont, hint, hcompat, hφ, hjc,
    hgauss⟩ := GlobalTheory.T.metaplectic_cover_weil_representation ι
  obtain ⟨e, u, he, hu⟩ := GlobalTheory.T.schwartz_L2_euclidean_identification ι
  have hes : ∀ (ψ : Sch ι) (x : ι → ℝ), e.symm ψ x = ψ (WithLp.toLp 2 x) := by
    intro ψ x
    simpa using (he (e.symm ψ) (WithLp.toLp 2 x)).symm
  have inj : ∀ ψ₁ ψ₂ : Sch ι, ψ₁.toLp 2 = ψ₂.toLp 2 → ψ₁ = ψ₂ := fun ψ₁ ψ₂ h =>
    SchwartzMap.injective_toLp (E := EuclideanSpace ℝ ι) (F := ℂ) 2 volume h
  let Ω : G →* (Lp ℂ 2 (volume : Measure (ι → ℝ)) →L[ℂ] Lp ℂ 2 (volume : Measure (ι → ℝ))) :=
    { toFun := fun g => ((u.symm.toContinuousLinearEquiv : L2 ι →L[ℂ] Lp ℂ 2 (volume : Measure (ι → ℝ))).comp
          ((om g).toContinuousLinearEquiv : L2 ι →L[ℂ] L2 ι)).comp
          (u.toContinuousLinearEquiv : Lp ℂ 2 (volume : Measure (ι → ℝ)) →L[ℂ] L2 ι)
      map_one' := by ext1 f; simp
      map_mul' := fun g h => by ext1 f; simp }
  have hΩ : ∀ g f, Ω g f = u.symm (om g (u f)) := fun g f => rfl
  let ω : G →* (𝓢(ι → ℝ, ℂ) →L[ℂ] 𝓢(ι → ℝ, ℂ)) :=
    { toFun := fun g => ((e.symm : Sch ι →L[ℂ] 𝓢(ι → ℝ, ℂ)).comp (omS g)).comp (e : 𝓢(ι → ℝ, ℂ) →L[ℂ] Sch ι)
      map_one' := by ext1 f; simp
      map_mul' := fun g h => by ext1 f; simp }
  have hω : ∀ g f, ω g f = e.symm (omS g (e f)) := fun g f => rfl
  have heω : ∀ g f, e (ω g f) = omS g (e f) := fun g f => by rw [hω, e.apply_symm_apply]
  have hφ₀ : ∀ x : ι → ℝ, e.symm φ x = cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)) := by
    intro x
    rw [hes, hφ]
  refine ⟨G, iG, tG, tgG, pr, Ω, ω, e.symm φ, hsurj, hcov, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hφ₀, ?_, ?_⟩
  · have hk : (pr.ker : Set G) = {1, ε} := by
      ext g
      simp [MonoidHom.mem_ker, hker]
    rw [← SetLike.coe_sort_coe, hk, Nat.card_coe_set_eq, Set.ncard_pair hε1.symm]
  · intro g f
    rw [hΩ, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map]
  · intro f
    exact u.symm.continuous.comp (hcont (u f))
  · intro g ψ
    rw [hΩ, LinearIsometryEquiv.symm_apply_eq, hu, hu, heω, hcompat]
  · have : (fun x : G × 𝓢(ι → ℝ, ℂ) => ω x.1 x.2) =
        (fun y : Sch ι => e.symm y) ∘ (fun y : G × Sch ι => omS y.1 y.2) ∘ (fun x : G × 𝓢(ι → ℝ, ℂ) => (x.1, e x.2)) := by
      funext x; rfl
    rw [this]
    exact e.symm.continuous.comp (hjc.comp (continuous_fst.prodMk (e.continuous.comp continuous_snd)))
  · intro g w ψ
    apply e.injective
    apply inj
    rw [heω, ← hcompat]
    rw [GlobalTheory.T.schrodinger_product_euclidean_models_agree ι w ψ (e ψ) (e (GlobalTheory.Published.Metaplectic.rho w ψ)) (he ψ) (he _)]
    rw [hint, hcompat]
    rw [GlobalTheory.T.schrodinger_product_euclidean_models_agree ι (GlobalTheory.Published.Metaplectic.act (pr g).1 w) (ω g ψ) (e (ω g ψ))
      (e (GlobalTheory.Published.Metaplectic.rho (GlobalTheory.Published.Metaplectic.act (pr g).1 w) (ω g ψ))) (he _) (he _)]
    rw [heω]
    congr 2
    simp [GlobalTheory.Published.Metaplectic.act, Sum.elim_comp_inl_inr]
  · intro g hg1 hg ψ
    have hgε : g = ε := ((hker g).1 hg1).resolve_left hg
    subst hgε
    have h1 : omS g (e ψ) = -(e ψ) := by
      apply inj
      have hn := (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))).map_neg (e ψ)
      simp only [SchwartzMap.toLpCLM_apply] at hn
      rw [← hcompat, hεf, hn]
    rw [hω, h1, map_neg, e.symm_apply_apply]
  · intro g
    obtain ⟨c, hc, hcx⟩ := hgauss g (Matrix.of fun a b => ((pr g).1 (.inl a) (.inl b) : ℂ) - I * ((pr g).1 (.inl a) (.inr b) : ℂ))
      (Matrix.of fun a b => ((pr g).1 (.inr a) (.inl b) : ℂ) - I * ((pr g).1 (.inr a) (.inr b) : ℂ))
      (fun a b => rfl) (fun a b => rfl)
    have hdet : (Matrix.of fun a b => ((pr g).1 (.inl a) (.inl b) : ℂ) - I * ((pr g).1 (.inl a) (.inr b) : ℂ)).det ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hc; exact zero_ne_one hc
    obtain ⟨-, hsymm⟩ := GlobalTheory.T.symplectic_holPart_det_ne_zero_and_isSymm ι (pr g).1 (Matrix.of fun a b => ((pr g).1 (.inl a) (.inl b) : ℂ) - I * ((pr g).1 (.inl a) (.inr b) : ℂ)) (Matrix.of fun a b => ((pr g).1 (.inr a) (.inl b) : ℂ) - I * ((pr g).1 (.inr a) (.inr b) : ℂ)) (fun a b => rfl) (fun a b => rfl) (pr g).2
    have hsieg := GlobalTheory.T.isSiegelUpperHalfSpace_neg_mul_inv_symplectic ι (pr g).1 (Matrix.of fun a b => ((pr g).1 (.inl a) (.inl b) : ℂ) - I * ((pr g).1 (.inl a) (.inr b) : ℂ)) (Matrix.of fun a b => ((pr g).1 (.inr a) (.inl b) : ℂ) - I * ((pr g).1 (.inr a) (.inr b) : ℂ)) (fun a b => rfl) (fun a b => rfl) (pr g).2 hdet hsymm
    have hωx : ∀ x : ι → ℝ, ω g (e.symm φ) x = c * cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ
        (-((Matrix.of fun a b => ((pr g).1 (.inr a) (.inl b) : ℂ) - I * ((pr g).1 (.inr a) (.inr b) : ℂ)) *
          (Matrix.of fun a b => ((pr g).1 (.inl a) (.inl b) : ℂ) - I * ((pr g).1 (.inl a) (.inr b) : ℂ))⁻¹)) *ᵥ
          fun i => (x i : ℂ))) := by
      intro x
      rw [hω, e.apply_symm_apply, hes, hcx]
    simp only [hωx, hφ₀]
    exact GlobalTheory.T.vacuum_matrix_coefficient_sq ι (pr g).1 (Matrix.of fun a b => ((pr g).1 (.inl a) (.inl b) : ℂ) - I * ((pr g).1 (.inl a) (.inr b) : ℂ)) (Matrix.of fun a b => ((pr g).1 (.inr a) (.inl b) : ℂ) - I * ((pr g).1 (.inr a) (.inr b) : ℂ)) (fun a b => rfl) (fun a b => rfl) hdet hsieg c hc
  · intro g horth
    obtain ⟨c, hc, hcx⟩ := hgauss g (Matrix.of fun a b => ((pr g).1 (.inl a) (.inl b) : ℂ) - I * ((pr g).1 (.inl a) (.inr b) : ℂ))
      (Matrix.of fun a b => ((pr g).1 (.inr a) (.inl b) : ℂ) - I * ((pr g).1 (.inr a) (.inr b) : ℂ))
      (fun a b => rfl) (fun a b => rfl)
    have hdet : (Matrix.of fun a b => ((pr g).1 (.inl a) (.inl b) : ℂ) - I * ((pr g).1 (.inl a) (.inr b) : ℂ)).det ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hc; exact zero_ne_one hc
    obtain ⟨hP, hq⟩ := GlobalTheory.T.orthogonal_symplectic_fixes_siegel_point_i ι (pr g).1 (Matrix.of fun a b => ((pr g).1 (.inl a) (.inl b) : ℂ) - I * ((pr g).1 (.inl a) (.inr b) : ℂ)) (Matrix.of fun a b => ((pr g).1 (.inr a) (.inl b) : ℂ) - I * ((pr g).1 (.inr a) (.inr b) : ℂ)) (fun a b => rfl) (fun a b => rfl) (pr g).2 horth hdet
    refine ⟨c, by rw [hP]; exact hc, ?_⟩
    ext x
    rw [hω, e.apply_symm_apply, hes, hcx, SchwartzMap.smul_apply, smul_eq_mul, hφ₀]
    simp only [PiLp.toLp_apply]
    rw [hq x]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneSubGoodIdempotentEqBadTupleSums
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module Polynomial

namespace GlobalTheory.BadCount

open Classical

variable (D : D7)

theorem neZeroG (k : Fin 2) : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩

theorem factG (k : Fin 2) : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩

attribute [local instance] neZeroG factG

def allTup (k : Fin 2) : Finset (Tup D k) :=
  Finset.univ.image fun a : D.nd.PlG k → (Fin D.R.r → ZMod (D.host.g k)) => fun v => Formalism.CyclotomicNorms.monicOf (a v)

theorem monicOf_injective (k : Fin 2) :
    Function.Injective (Formalism.CyclotomicNorms.monicOf : (Fin D.R.r → ZMod (D.host.g k)) → (ZMod (D.host.g k))[X]) := by
  intro a b h
  funext i
  rw [← Formalism.CyclotomicNorms.Sqf.coeff_monicOf_lt a i, h, Formalism.CyclotomicNorms.Sqf.coeff_monicOf_lt]

theorem tupOf_injective (k : Fin 2) :
    Function.Injective fun a : D.nd.PlG k → (Fin D.R.r → ZMod (D.host.g k)) => fun v => Formalism.CyclotomicNorms.monicOf (a v) := by
  intro a b h
  funext v
  exact monicOf_injective D k (congrFun h v)

theorem badElt_coeff (k : Fin 2) (S : Finset (Tup D k)) (g : G0g D.nd) :
    (badElt D k S).coeff g = if ∀ kv : (Σ k : Fin 2, D.nd.PlG k), kv.1 ≠ k → g kv = 1 then
      ∑ t ∈ S, ∏ v : D.nd.PlG k, (D.ntypes.eSer k (t v)).coeff (g ⟨k, v⟩) else 0 := by
  unfold badElt
  rfl

theorem sum_eSer_monicOf (k : Fin 2) :
    ∑ b : Fin D.R.r → ZMod (D.host.g k), D.ntypes.eSer k (Formalism.CyclotomicNorms.monicOf b) = 1 := by
  obtain ⟨S, hS, hsum⟩ := D.ntypes.eSer_sum k
  rw [← hsum, ← Finset.sum_image (fun a _ b _ h => monicOf_injective D k h)]
  symm
  apply Finset.sum_subset
  · intro f hf
    obtain ⟨h1, h2, -⟩ := (hS f).1 hf
    exact Finset.mem_image.2 ⟨_, Finset.mem_univ _, Formalism.CyclotomicNorms.Sqf.monicOf_coeffs f h1 h2⟩
  · intro f _ hf
    exact D.ntypes.eSer_zero k f fun h => hf ((hS f).2 h)

theorem badElt_all (k : Fin 2) : badElt D k (allTup D k) = 1 := by
  apply MonoidAlgebra.coeff_injective
  ext g
  rw [badElt_coeff, allTup, Finset.sum_image (fun a _ b _ h => tupOf_injective D k h)]
  have e : ∑ a : D.nd.PlG k → (Fin D.R.r → ZMod (D.host.g k)),
      ∏ v, (D.ntypes.eSer k (Formalism.CyclotomicNorms.monicOf (a v))).coeff (g ⟨k, v⟩) =
      ∏ v, (1 : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k)))).coeff (g ⟨k, v⟩) := by
    refine (Fintype.prod_sum (fun v (b : Fin D.R.r → ZMod (D.host.g k)) =>
      (D.ntypes.eSer k (Formalism.CyclotomicNorms.monicOf b)).coeff (g ⟨k, v⟩))).symm.trans ?_
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← sum_eSer_monicOf D k, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  rw [e, MonoidAlgebra.one_def, MonoidAlgebra.one_def]
  simp only [MonoidAlgebra.coeff_single, Finsupp.single_apply]
  by_cases h1 : g = 1
  · subst h1; simp
  · rw [if_neg (Ne.symm h1)]
    split_ifs with hs
    · obtain ⟨kv, hkv⟩ := Function.ne_iff.1 h1
      obtain ⟨k', v⟩ := kv
      by_cases hk : k' = k
      · subst hk
        exact Finset.prod_eq_zero (Finset.mem_univ v) (if_neg fun h => hkv h.symm)
      · exact absurd (hs ⟨k', v⟩ hk) hkv
    · rfl

def goodSet (k : Fin 2) : Finset (Tup D k) := (allTup D k).filter (goodAt D k)

def badSet (k : Fin 2) : Finset (Tup D k) := (allTup D k).filter fun t => ¬ goodAt D k t

theorem badElt_good_add_bad (k : Fin 2) : badElt D k (goodSet D k) + badElt D k (badSet D k) = 1 := by
  rw [← badElt_all D k]
  apply MonoidAlgebra.coeff_injective
  ext g
  rw [MonoidAlgebra.coeff_add, Finsupp.add_apply, badElt_coeff, badElt_coeff, badElt_coeff]
  split_ifs
  · exact Finset.sum_filter_add_sum_filter_not _ _ _
  · simp

theorem badElt_coeff_off (k : Fin 2) (S : Finset (Tup D k)) (h : G0g D.nd)
    (hh : ∃ kv : (Σ k : Fin 2, D.nd.PlG k), kv.1 ≠ k ∧ h kv ≠ 1) : (badElt D k S).coeff h = 0 := by
  rw [badElt_coeff, if_neg]
  obtain ⟨kv, h1, h2⟩ := hh
  exact fun hs => h2 (hs kv h1)

theorem coeff_mul_factors (x y : MonoidAlgebra ℂ (G0g D.nd))
    (hx : ∀ h : G0g D.nd, (∃ kv : (Σ k : Fin 2, D.nd.PlG k), kv.1 ≠ 0 ∧ h kv ≠ 1) → x.coeff h = 0)
    (hy : ∀ h : G0g D.nd, (∃ kv : (Σ k : Fin 2, D.nd.PlG k), kv.1 ≠ 1 ∧ h kv ≠ 1) → y.coeff h = 0)
    (g : G0g D.nd) :
    (x * y).coeff g = x.coeff (fun kv => if kv.1 = 0 then g kv else 1) *
      y.coeff (fun kv => if kv.1 = 0 then 1 else g kv) := by
  rw [MonoidAlgebra.coeff_mul_apply_left]
  rw [Finsupp.sum_eq_single (fun kv => if kv.1 = 0 then g kv else 1)]
  · congr 2
    funext kv
    by_cases h0 : kv.1 = 0
    · simp [h0]
    · simp [h0]
  · intro b hb hne
    have hb0 : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), kv.1 ≠ 0 → b kv = 1 := by
      intro kv hkv
      by_contra hc
      exact hb (hx b ⟨kv, hkv, hc⟩)
    obtain ⟨kv, hkv⟩ := Function.ne_iff.1 hne
    by_cases h0 : kv.1 = 0
    · rw [hy _ ⟨kv, by rw [h0]; decide, ?_⟩, mul_zero]
      intro hc
      apply hkv
      simp only [h0, if_true]
      have : (b⁻¹ * g) kv = 1 := hc
      rw [Pi.mul_apply, Pi.inv_apply, inv_mul_eq_one] at this
      exact this
    · exact absurd (by simp [h0, hb0 kv h0]) hkv
  · intro _
    exact zero_mul _

theorem e0_eq : D.ntypes.e0 = badElt D 0 (goodSet D 0) * badElt D 1 (goodSet D 1) := by
  apply MonoidAlgebra.coeff_injective
  ext g
  rw [coeff_mul_factors D _ _ (fun h hh => badElt_coeff_off D 0 _ h hh) (fun h hh => badElt_coeff_off D 1 _ h hh),
    badElt_coeff, badElt_coeff, if_pos, if_pos]
  rotate_left
  · rintro ⟨k, v⟩ hk
    fin_cases k
    · simp
    · exact absurd rfl hk
  · rintro ⟨k, v⟩ hk
    fin_cases k
    · exact absurd rfl hk
    · simp
  have he : D.ntypes.e0.coeff g =
      ∑ᶠ a : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), (Fin D.R.r → ZMod (D.host.g kv.1))),
        (if D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) then
          ∏ kv : (Σ k : Fin 2, D.nd.PlG k), (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (a kv))).coeff (g kv) else 0) := rfl
  rw [he, finsum_eq_sum_of_fintype, goodSet, goodSet, Finset.sum_filter, Finset.sum_filter, allTup, allTup,
    Finset.sum_image (fun a _ b _ h => tupOf_injective D 0 h),
    Finset.sum_image (fun a _ b _ h => tupOf_injective D 1 h),
    Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  refine Fintype.sum_equiv ((Equiv.piCurry fun k (_ : D.nd.PlG k) => Fin D.R.r → ZMod (D.host.g k)).trans
    (piFinTwoEquiv _)) _ _ fun a => ?_
  have hg : D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) ↔
      goodAt D 0 (fun v => Formalism.CyclotomicNorms.monicOf (a ⟨0, v⟩)) ∧ goodAt D 1 (fun v => Formalism.CyclotomicNorms.monicOf (a ⟨1, v⟩)) :=
    Fin.forall_fin_two
  rw [Fintype.prod_sigma, Fin.prod_univ_two]
  by_cases h0 : goodAt D 0 (fun v => Formalism.CyclotomicNorms.monicOf (a ⟨0, v⟩)) <;>
  by_cases h1 : goodAt D 1 (fun v => Formalism.CyclotomicNorms.monicOf (a ⟨1, v⟩)) <;>
  simp [hg, h0, h1, piFinTwoEquiv_apply, Equiv.piCurry_apply, Sigma.curry]

theorem one_sub_goodTypeIdempotent_eq_badTupleSums : ∃ S : ∀ k : Fin 2, Finset (Tup D k), (∀ k, ∀ t ∈ S k, ¬ goodAt D k t) ∧
    1 - D.ntypes.e0 = badElt D 0 (S 0) + badElt D 1 (S 1) - badElt D 0 (S 0) * badElt D 1 (S 1) := by
  refine ⟨badSet D, fun k t ht => (Finset.mem_filter.1 ht).2, ?_⟩
  rw [e0_eq, ← sub_eq_iff_eq_add'.2 (badElt_good_add_bad D 0).symm,
    ← sub_eq_iff_eq_add'.2 (badElt_good_add_bad D 1).symm]
  noncomm_ring

end GlobalTheory.BadCount
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointedEtaleNbhdTransitionMapDirectedSystem
section
open IsLocalRing GlobalTheory.Henselisation

namespace GlobalTheory.Henselisation.EtNbhd

variable {R : Type} [CommRing R] [IsLocalRing R]

theorem algebraMap_comp_eq_of_pt {i j : EtNbhd R} (φ₁ φ₂ : i.A →ₐ[R] j.A)
    (h₁ : j.pt.comp φ₁ = i.pt) (h₂ : j.pt.comp φ₂ = i.pt) (a : i.A) :
    algebraMap j.A j.B (φ₁ a) = algebraMap j.A j.B (φ₂ a) := by
  let ψ₁ : i.A →ₐ[R] j.B := (IsScalarTower.toAlgHom R j.A j.B).comp φ₁
  let ψ₂ : i.A →ₐ[R] j.B := (IsScalarTower.toAlgHom R j.A j.B).comp φ₂
  have : ψ₁ = ψ₂ := by
    refine GlobalTheory.EtaleHensel.algHom_eq_of_residue_eq fun b => ?_
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    show algebraMap j.A j.B (φ₁ b) - algebraMap j.A j.B (φ₂ b) ∈ maximalIdeal j.B
    rw [← map_sub, IsLocalization.AtPrime.to_map_mem_maximal_iff j.B j.q]
    show φ₁ b - φ₂ b ∈ RingHom.ker j.pt
    rw [RingHom.mem_ker, map_sub, sub_eq_zero]
    exact (congr($h₁ b)).trans (congr($h₂ b)).symm
  exact congr($this a)

theorem trans_algebraMap_eq_of_pt {i j : EtNbhd R} (h : i ≤ j) (φ : i.A →ₐ[R] j.A)
    (hφ : j.pt.comp φ = i.pt) (a : i.A) :
    trans h (algebraMap i.A i.B a) = algebraMap j.A j.B (φ a) := by
  unfold trans
  rw [Localization.localRingHom_to_map]
  exact algebraMap_comp_eq_of_pt _ _ h.choose_spec hφ a

end GlobalTheory.Henselisation.EtNbhd

namespace GlobalTheory.Henselisation

theorem trans_system : ∀ (R : Type) [CommRing R] [IsLocalRing R], (∀ (i : EtNbhd R) (x : i.B), EtNbhd.trans (le_refl i) x = x) ∧ ∀ (i j k : EtNbhd R) (hij : i ≤ j) (hjk : j ≤ k) (x : i.B), EtNbhd.trans hjk (EtNbhd.trans hij x) = EtNbhd.trans (hij.trans hjk) x := by
  intro R _ _
  refine ⟨fun i x => ?_, fun i j k hij hjk x => ?_⟩
  · have : EtNbhd.trans (le_refl i) = RingHom.id i.B :=
      IsLocalization.ringHom_ext i.q.primeCompl (RingHom.ext fun a => by
        simp only [RingHom.comp_apply, RingHom.id_apply]
        exact EtNbhd.trans_algebraMap_eq_of_pt _ (AlgHom.id R i.A) (AlgHom.comp_id _) a)
    exact congr($this x)
  · have : (EtNbhd.trans hjk).comp (EtNbhd.trans hij) = EtNbhd.trans (hij.trans hjk) :=
      IsLocalization.ringHom_ext i.q.primeCompl (RingHom.ext fun a => by
        simp only [RingHom.comp_apply]
        rw [EtNbhd.trans_algebraMap_eq_of_pt hij hij.choose hij.choose_spec,
          EtNbhd.trans_algebraMap_eq_of_pt hjk hjk.choose hjk.choose_spec,
          EtNbhd.trans_algebraMap_eq_of_pt (hij.trans hjk) (hjk.choose.comp hij.choose)
            (by rw [← AlgHom.comp_assoc, hjk.choose_spec, hij.choose_spec])]
        rfl)
    exact congr($this x)

end GlobalTheory.Henselisation
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageConnectedComponentRationalPointFieldExt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem preimage_connectedComponent_rationalPoint_baseChange : ∀ (k k' : Type) [Field k] [Field k'] (X X' : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of k)) (f' : X' ⟶ Spec (CommRingCat.of k')) (p : Spec (CommRingCat.of k') ⟶ Spec (CommRingCat.of k)) (q : X' ⟶ X) (e : Spec (CommRingCat.of k) ⟶ X) (e' : Spec (CommRingCat.of k') ⟶ X'), Smooth f → IsPullback q f' f p → e ≫ f = 𝟙 _ → e' ≫ f' = 𝟙 _ → e' ≫ q = p ≫ e → q ⁻¹' connectedComponent (e (IsLocalRing.closedPoint k)) = connectedComponent (e' (IsLocalRing.closedPoint k')) := by
  intro k k' _ _ X X' f f' p q e e' hf hP he he' hq
  have hN : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  set x : X := e (IsLocalRing.closedPoint k) with hx
  set x' : X' := e' (IsLocalRing.closedPoint k') with hx'
  have hopen : IsOpen (connectedComponent x) := GlobalTheory.T.isOpen_connectedComponent_of_isLocallyNoetherian' X hN x
  let U : X.Opens := ⟨connectedComponent x, hopen⟩
  have hsub : Subsingleton (Spec (CommRingCat.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  have hrange : Set.range e ⊆ Set.range U.ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι, Subsingleton.elim y (IsLocalRing.closedPoint k)]
    exact mem_connectedComponent
  let eU : Spec (CommRingCat.of k) ⟶ U.toScheme := IsOpenImmersion.lift U.ι e hrange
  have heU : eU ≫ U.ι = e := IsOpenImmersion.lift_fac _ _ _
  have hUc : ConnectedSpace U.toScheme :=
    isConnected_iff_connectedSpace.mp (isConnected_connectedComponent (x := x))
  have hgc : GeometricallyConnected (U.ι ≫ f) :=
    GlobalTheory.T.geometricallyConnected_of_smooth_of_section' k U.toScheme (U.ι ≫ f) eU inferInstance (by rw [← Category.assoc, heU, he]) hUc
  have hP1 : IsPullback (q ∣_ U) (q ⁻¹ᵁ U).ι U.ι q := isPullback_morphismRestrict q U
  have hP2 : IsPullback (q ∣_ U) ((q ⁻¹ᵁ U).ι ≫ f') (U.ι ≫ f) p := hP1.paste_vert hP
  have hc : ConnectedSpace (q ⁻¹ᵁ U).toScheme :=
    GeometricallyConnected.geometrically_connectedSpace (f := U.ι ≫ f) p _ _ hP2
  have hc' : _root_.IsConnected (q ⁻¹' connectedComponent x) :=
    isConnected_iff_connectedSpace.mpr hc
  have hmem : x' ∈ q ⁻¹' connectedComponent x := by
    have : q x' = x := by
      have h1 : q x' = (e' ≫ q) (IsLocalRing.closedPoint k') := rfl
      have h2 : (p ≫ e) (IsLocalRing.closedPoint k') = e (p (IsLocalRing.closedPoint k')) := rfl
      rw [h1, hq, h2]
      exact congrArg e (Subsingleton.elim _ _)
    rw [Set.mem_preimage, this]
    exact mem_connectedComponent
  have hclopen : IsClopen (q ⁻¹' connectedComponent x) :=
    IsClopen.preimage ⟨isClosed_connectedComponent, hopen⟩ q.continuous
  exact Set.Subset.antisymm (hc'.subset_connectedComponent hmem)
    (hclopen.connectedComponent_subset hmem)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShintaniLiftClassFunctionIsometryStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shintaniLiftClassFunction_isometry : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (n : ℕ) (f f' : GL (Fin n) F → ℂ), IsCl f → IsCl f' → (Nat.card (GL (Fin n) F) : ℂ) * ∑ᶠ δ, shLift s f δ * star (shLift s f' δ) = (Nat.card (GL (Fin n) F') : ℂ) * ∑ᶠ γ, f γ * star (f' γ) := by
  first | (exact @GlobalTheory.Shin.shLift_isometry) | (exact GlobalTheory.Shin.shLift_isometry) | (intros; apply GlobalTheory.Shin.shLift_isometry  <;> assumption)
end

