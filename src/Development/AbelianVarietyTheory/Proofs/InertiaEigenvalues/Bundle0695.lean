import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivContraOfChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0677
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0681
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0256
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelSubgroupRestrictedProductOfLaws
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0682
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0125
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Formalism.SharpRestriction.LevelLetterCocycles.RamificationTwoAndConjugationAtQAndD
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0676
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0333
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0291
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0542

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLanglandsClassificationDetCharacter
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
  GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published

namespace GlobalTheory.LocGL.DetQuot

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nonempty_equiv_multiProd {t : ℕ} {n : Type} [Fintype n] [DecidableEq n] (e : (Σ _ : Fin t, Fin 1) ≃ n)
    {θ : Fin t → kˣ →* ℂˣ} {Θ : Levi k (fun _ : Fin t => Fin 1) →* ℂˣ}
    (hΘ : ∀ g, Θ g = ∏ a, θ a (GeneralLinearGroup.det (g a))) :
    Nonempty ((parInd e (ofChar Θ)).Equiv (multiProd e fun a => detRep (Fin 1) (θ a))) := by
  refine ⟨parIndEquiv e (Representation.Equiv.mk
    (PiTensorProduct.constantBaseRingEquiv (Fin t) ℂ).toLinearEquiv.symm fun g => ?_)⟩
  refine LinearMap.ext_ring ?_
  apply (PiTensorProduct.constantBaseRingEquiv (Fin t) ℂ).injective
  simp [ofChar_apply, hΘ, PiTensorProduct.one_def, piTensor_tprod, detRep, detChar_apply, Units.coe_prod]

theorem exists_embedding {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) {η : kˣ →* ℂˣ} (hη : IsSmoothChar η) :
    ∃ f : (detRep n η).IntertwiningMap (parInd e (ofChar (detLevi e η))), Function.Injective f := by
  have hsm : IsSmooth (detRep n η) := (isSmooth_ofChar_iff _).2 hη.detChar
  let ψ : (jac e (detRep n η)).IntertwiningMap (ofChar (detLevi e η)) :=
    { toLinearMap := (twKer (detRep n η) (unipRad k e) 1).liftQ LinearMap.id
        (by rw [twKer_detRep]; exact bot_le)
      isIntertwining' := fun g => LinearMap.ext fun x => by
        rw [LinearMap.comp_apply, LinearMap.comp_apply, GlobalTheory.SmGL.Model.jac_detRep, map_smul, ofChar_apply,
          smul_eq_mul] }
  obtain ⟨f, hf⟩ := (GlobalTheory.SmGL.Model.evalOne_bijective e hsm (ofChar (detLevi e η))).2 ψ
  refine ⟨f, (injective_iff_map_eq_zero f).2 fun c hc => ?_⟩
  by_contra hc0
  have h1 : f 1 = 0 := by
    have h1' : (1 : ℂ) = c⁻¹ • c := by simp [hc0]
    rw [h1', map_smul, hc, smul_zero]
  have h2 : ψ (Submodule.Quotient.mk (p := twKer (detRep n η) (unipRad k e) 1) (1 : ℂ)) = 1 := rfl
  have h3 : ψ (Submodule.Quotient.mk (p := twKer (detRep n η) (unipRad k e) 1) (1 : ℂ)) = (f 1).1.1 1 := by
    rw [← hf]; rfl
  rw [h1] at h3
  exact one_ne_zero (h2.symm.trans h3)

theorem exists_surjective_of_contra {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V]
    [Module ℂ V] {π : Representation ℂ G V} {χ : G →* ℂˣ} (f : (ofChar χ⁻¹).IntertwiningMap (contra π))
    (hf : Function.Injective f) : ∃ l : π.IntertwiningMap (ofChar χ), Function.Surjective l := by
  set lam : Module.Dual ℂ V := ((f 1 : smoothPart π.dual) : Module.Dual ℂ V) with hlam
  have key : ∀ g v, lam (π g v) = (χ g : ℂ) * lam v := by
    intro g v
    have h1 : f (ofChar (χ⁻¹) (g⁻¹) (1 : ℂ)) = contra π (g⁻¹) (f 1) :=
      LinearMap.congr_fun (f.isIntertwining' (g⁻¹)) (1 : ℂ)
    have h2 : ofChar (χ⁻¹) (g⁻¹) (1 : ℂ) = (χ g : ℂ) • (1 : ℂ) := by simp [ofChar_apply]
    rw [h2, map_smul] at h1
    have h3 := congrArg (fun x : smoothPart π.dual => (x : Module.Dual ℂ V) v) h1
    simp only [contra_apply, inv_inv] at h3
    rw [← h3]
    simp [lam]
  have hne : lam ≠ 0 := by
    intro h0
    have h1 : f 1 = 0 := Subtype.ext (by simpa [lam] using h0)
    exact one_ne_zero (hf (h1.trans (map_zero f).symm))
  obtain ⟨v, hv⟩ : ∃ v, lam v ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (LinearMap.ext h)
  refine ⟨⟨lam, fun g => LinearMap.ext fun w => ?_⟩, fun c => ⟨(c / lam v) • v, ?_⟩⟩
  · simp [key, ofChar_apply]
  · simp [hv]

theorem exists_surjective {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) {η : kˣ →* ℂˣ} (hη : IsSmoothChar η) :
    ∃ l : (parInd e (ofChar (detLevi e η⁻¹)⁻¹)).IntertwiningMap (detRep n η), Function.Surjective l := by
  have hc : IsSmoothChar (detLevi e η⁻¹) := by
    unfold detLevi
    exact (hη.inv.detChar.comp (leviEmb k e) (continuous_leviEmb (R := k) e)).mul
      (isSmoothChar_deltaHalf k).inv
  have hc' : IsSmoothChar (detLevi e η⁻¹)⁻¹ := hc.inv
  have hτ : IsSmooth (ofChar (detLevi e η⁻¹)⁻¹) := (isSmooth_ofChar_iff _).2 hc'
  obtain ⟨Φ1⟩ := GlobalTheory.LocGL.ProjLine.nonempty_equiv_contra_ofChar hc'
  rw [inv_inv] at Φ1
  obtain ⟨Φ2⟩ := (GlobalTheory.SmGL.IndDual.inductionContragredient k).nonempty_equiv e hτ
  obtain ⟨f, hf⟩ := exists_embedding e hη.inv
  let F := (Φ2.toIntertwiningMap.comp (parIndEquiv e Φ1).toIntertwiningMap).comp f
  have hF : Function.Injective F := fun a b h =>
    hf ((EquivLike.injective (parIndEquiv e Φ1)) ((EquivLike.injective Φ2) h))
  have hdet : detChar n η⁻¹ = (detChar n η)⁻¹ := by
    ext g
    simp [detChar_apply]
  have key : ∀ (χ' : GL n k →* ℂˣ), χ' = (detChar n η)⁻¹ →
      ∀ f' : (ofChar χ').IntertwiningMap (contra (parInd e (ofChar (detLevi e η⁻¹)⁻¹))), Function.Injective f' →
      ∃ l : (parInd e (ofChar (detLevi e η⁻¹)⁻¹)).IntertwiningMap (ofChar (detChar n η)), Function.Surjective l := by
    rintro χ' rfl f' hf'
    exact exists_surjective_of_contra f' hf'
  exact key (detChar n η⁻¹) hdet F hF

theorem surj_of_equiv {G V W X : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup X] [Module ℂ X] {π : Representation ℂ G V} {σ : Representation ℂ G W} {τ : Representation ℂ G X}
    (Φ : π.Equiv σ) (l : π.IntertwiningMap τ) (hl : Function.Surjective l) :
    ∃ l' : σ.IntertwiningMap τ, Function.Surjective l' := by
  refine ⟨l.comp Φ.symm.toIntertwiningMap, fun y => ?_⟩
  obtain ⟨x, rfl⟩ := hl y
  refine ⟨Φ x, ?_⟩
  show l (Φ.symm (Φ x)) = l x
  rw [Representation.Equiv.symm_apply_apply]

theorem detLevi_inv_apply {t : ℕ} {n : Type} [Fintype n] [DecidableEq n] (e : (Σ _ : Fin t, Fin 1) ≃ n)
    (χ : kˣ →* ℂˣ) (g : Levi k fun _ : Fin t => Fin 1) :
    (detLevi e χ⁻¹)⁻¹ g =
      ∏ a : Fin t, (χ * absPow k ((((t : ℝ) - 1) / 2 - (a : ℕ) : ℝ) : ℂ)) (GeneralLinearGroup.det (g a)) := by
  rw [MonoidHom.inv_apply, detLevi_apply, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  have hs : (((((t : ℝ) - 1) / 2 - (a : ℕ) : ℝ) : ℂ)) =
      -(-((modExp (fun _ : Fin t => Fin 1) a : ℤ) : ℂ) / 2) := by
    rw [modExp_fin (fun _ : Fin t => Fin 1) (fun _ => Fintype.card_fin 1) a]
    push_cast
    ring
  rw [hs, absPow_neg]
  simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv, inv_inv]

theorem exists_surjective_multiProd {t : ℕ} {n : Type} [Fintype n] [DecidableEq n] (e : (Σ _ : Fin t, Fin 1) ≃ n)
    {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) :
    ∃ l : (multiProd e fun a : Fin t => detRep (Fin 1)
      (χ * absPow k ((((t : ℝ) - 1) / 2 - (a : ℕ) : ℝ) : ℂ))).IntertwiningMap (detRep n χ), Function.Surjective l := by
  obtain ⟨Φ⟩ := nonempty_equiv_multiProd e (Θ := (detLevi e χ⁻¹)⁻¹)
    (θ := fun a : Fin t => χ * absPow k ((((t : ℝ) - 1) / 2 - (a : ℕ) : ℝ) : ℂ)) (detLevi_inv_apply e χ)
  obtain ⟨l, hl⟩ := exists_surjective e hχ
  exact surj_of_equiv Φ l hl

theorem exists_equiv_prodIrr {t : ℕ} {θ : Fin t → kˣ →* ℂˣ} (hθ : ∀ a, IsSmoothChar (θ a)) {x : Fin t → IrrGL k}
    (hx : ∀ a, x a = IrrGL.ofChar (θ a) (hθ a)) :
    ∃ (e : (Σ _ : Fin t, Fin 1) ≃ Fin t) (hd' : ∑ a, (x a).1 = t), Nonempty ((multiProd e fun a => detRep (Fin 1) (θ a)).Equiv (prodIrr x hd')) := by
  obtain rfl : x = fun a => IrrGL.ofChar (θ a) (hθ a) := funext hx
  have hd : ∑ a : Fin t, (IrrGL.ofChar (θ a) (hθ a)).1 = t := by simp [IrrGL.ofChar]
  exact ⟨stdBlocks _ hd, hd, ⟨multiProdEquiv _ fun a => equivRep (IrrRep.det (Fin 1) (θ a) (hθ a))⟩⟩

set_option maxHeartbeats 1600000 in
private theorem exists_surjective_prodIrr_to_detRep (t : ℕ) {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) {x : Fin t → IrrGL k}
    (hx : ∀ j, x j = (IrrGL.ofChar χ hχ).nu ((((t : ℝ) - 1) / 2 - (j : ℕ) : ℝ) : ℂ)) :
    ∃ (hd : ∑ a, (x a).1 = t) (l : (prodIrr x hd).IntertwiningMap (detRep (Fin t) χ)), Function.Surjective l := by
  have hθ : ∀ a : Fin t, IsSmoothChar (χ * absPow k ((((t : ℝ) - 1) / 2 - (a : ℕ) : ℝ) : ℂ)) :=
    fun a => hχ.mul (isSmoothChar_absPow _)
  have hx' : ∀ a, x a = IrrGL.ofChar (χ * absPow k ((((t : ℝ) - 1) / 2 - (a : ℕ) : ℝ) : ℂ)) (hθ a) :=
    fun a => (hx a).trans (IrrGL.tw_ofChar χ _ hχ (isSmoothChar_absPow _))
  obtain ⟨e, hd, hΦ⟩ := exists_equiv_prodIrr hθ hx'
  obtain ⟨Φ⟩ := hΦ
  obtain ⟨l, hl⟩ := exists_surjective_multiProd (t := t) (n := Fin t) e (χ := χ) hχ
  refine ⟨hd, ?_⟩
  exact surj_of_equiv Φ l hl

theorem exists_surjective_prodIrr (t : ℕ) {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) {x : Fin t → IrrGL k}
    (hx : ∀ j, x j = (IrrGL.ofChar χ hχ).nu ((((t : ℝ) - 1) / 2 - (j : ℕ) : ℝ) : ℂ)) :
    ∃ (hd : ∑ a, (x a).1 = t) (l : (prodIrr x hd).IntertwiningMap (detRep (Fin t) χ)), Function.Surjective l :=
  exists_surjective_prodIrr_to_detRep t hχ hx

end GlobalTheory.LocGL.DetQuot

namespace GlobalTheory.LocGL

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem isL_det : StandardCosocleGL → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [CharZero k] (t : ℕ) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ),
    IsL (((List.range t).map fun j : ℕ => Segment.single ((IrrGL.ofChar χ hχ).nu
      ((((t : ℝ) - 1) / 2 - j : ℝ) : ℂ)) ((IrrGL.isCusp_ofChar χ hχ).nu _) : List (Segment k)) : Multiset (Segment k))
      (IrrRep.det (Fin t) χ hχ).ρ := by
  intro H k _ _ _ _ _ t χ hχ
  let x : Fin t → IrrGL k := fun j => (IrrGL.ofChar χ hχ).nu ((((t : ℝ) - 1) / 2 - (j : ℕ) : ℝ) : ℂ)
  obtain ⟨hd, l, hl⟩ := DetQuot.exists_surjective_prodIrr t hχ (x := x) (fun j => rfl)
  have hcusp : ∀ j, (x j).IsCusp := fun j => (IrrGL.isCusp_ofChar χ hχ).nu _
  let Δ : Fin t → Segment k := fun j => Segment.single (x j) (hcusp j)
  have hfirst : ∀ j, (Δ j).first = x j := fun j => Segment.first_ofFirst _ _ _ _
  have hord : IsOrderedForm Δ (((List.range t).map fun j : ℕ => Segment.single ((IrrGL.ofChar χ hχ).nu
      ((((t : ℝ) - 1) / 2 - j : ℝ) : ℂ)) ((IrrGL.isCusp_ofChar χ hχ).nu _) : List (Segment k)) : Multiset (Segment k)) := by
    refine ⟨?_, ?_⟩
    · rw [Fin.univ_val_map]
      congr 1
      apply List.ext_get (by simp)
      intro i h1 h2
      simp [Δ, x]
    · rintro i j hij ⟨-, m, hm, heq⟩
      rw [hfirst, hfirst] at heq
      have key : (IrrGL.ofChar χ hχ).nu ((((t : ℝ) - 1) / 2 - ((j : ℕ) : ℝ) : ℝ) : ℂ) =
          (IrrGL.ofChar χ hχ).nu ((((t : ℝ) - 1) / 2 - ((i : ℕ) : ℝ) + (m : ℝ) : ℝ) : ℂ) := by
        calc (IrrGL.ofChar χ hχ).nu ((((t : ℝ) - 1) / 2 - ((j : ℕ) : ℝ) : ℝ) : ℂ) = x j := rfl
          _ = (x i).nu (m : ℂ) := heq
          _ = ((IrrGL.ofChar χ hχ).nu ((((t : ℝ) - 1) / 2 - ((i : ℕ) : ℝ) : ℝ) : ℂ)).nu (m : ℂ) := rfl
          _ = _ := by
            rw [IrrGL.nu_nu]
            congr 1
            push_cast
            ring
      rw [IrrGL.nu_ofChar_inj] at key
      have hij' : ((i : ℕ) : ℝ) < ((j : ℕ) : ℝ) := by exact_mod_cast hij
      have hm' : (0 : ℝ) < m := by exact_mod_cast hm
      linarith
  have hL : LFactors (((List.range t).map fun j : ℕ => Segment.single ((IrrGL.ofChar χ hχ).nu
      ((((t : ℝ) - 1) / 2 - j : ℝ) : ℂ)) ((IrrGL.isCusp_ofChar χ hχ).nu _) : List (Segment k)) : Multiset (Segment k)) x :=
    ⟨Δ, hord, fun j => (single_spec (hcusp j)).2.1⟩
  obtain ⟨π0, hπ0⟩ := H k _ t t x hd hL
  obtain ⟨Ψ⟩ := hπ0.equiv_of_surjective (IrrRep.det (Fin t) χ hχ).irr l hl
  exact ⟨t, x, hd, hL, hπ0.of_equiv Ψ.symm (Representation.Equiv.refl _)⟩

end GlobalTheory.LocGL

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsTameWeilDeligneIffWildCharpoly
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LlcTame

variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

end GlobalTheory.LlcTame

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial in
attribute [local instance] _root_.GlobalTheory.LocalData.complRel _root_.GlobalTheory.LocalData.isLocalField in
private theorem eq_one_of_isSemisimple_of_charpoly_eq {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (f : Module.End ℂ V) (hs : f.IsSemisimple)
    (hc : f.charpoly = (X - 1) ^ Module.finrank ℂ V) : f = 1 := by
  have hn : IsNilpotent (f - 1) := by
    refine ⟨Module.finrank ℂ V, ?_⟩
    have := LinearMap.aeval_self_charpoly f
    rw [hc] at this
    simpa using this
  have hs' : (f - 1).IsSemisimple :=
    hs.sub_of_commute (Commute.one_right f) Module.End.isSemisimple_id
  exact sub_eq_zero.mp (Module.End.eq_zero_of_isNilpotent_isSemisimple hn hs')

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial in
attribute [local instance] _root_.GlobalTheory.LocalData.complRel _root_.GlobalTheory.LocalData.isLocalField in
theorem _root_.GlobalTheory.LlcTame.isTameWD_iff_charPol : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E))
    (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w) (y : _root_.GlobalTheory.WeilDeligne.WD h), _root_.GlobalTheory.LocLanglands.IsTameWD y ↔
    ∀ σ : _root_.GlobalTheory.WeilDeligne.Weil h, _root_.Formalism.MainNotions.BlochKatoReduction.IsWild A (σ : _root_.Formalism.ConjugateSelfDual.G E Ω) →
      y.charPol σ = (X - 1) ^ y.lpDim := by
  intro E Ω _ _ _ _ _ A w h y
  unfold _root_.GlobalTheory.LocLanglands.IsTameWD
  constructor
  · rintro ⟨n, a, rfl, ha⟩ σ hσ
    have hd : (_root_.GlobalTheory.WeilDeligne.WD.mk a).lpDim =
        Module.finrank ℂ (Fin n → ℂ) := _root_.GlobalTheory.WeilDeligne.WD.lpDim_mk a
    refine (_root_.GlobalTheory.WeilDeligne.WD.charPol_mk a σ).trans ?_
    rw [hd, ha σ hσ, LinearMap.charpoly_one]
  · intro H
    obtain ⟨n, a, rfl⟩ := y.exists_rep
    refine ⟨n, a, rfl, fun σ hσ => ?_⟩
    have hc := H σ hσ
    have hd : (_root_.GlobalTheory.WeilDeligne.WD.mk a).lpDim =
        Module.finrank ℂ (Fin n → ℂ) := _root_.GlobalTheory.WeilDeligne.WD.lpDim_mk a
    rw [hd] at hc
    have hc' := (_root_.GlobalTheory.WeilDeligne.WD.charPol_mk a σ).symm.trans hc
    exact eq_one_of_isSemisimple_of_charpoly_eq _ (a.semisimple σ) hc'
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitarisableOfIsSpehOne
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DefiniteBC GlobalTheory.BcSpeh

namespace GlobalTheory.DiscreteSpectrumCM

theorem isUnitarisable_of_injective {G X Y : Type} [Group G] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y]
    [Module ℂ Y] {ρ : Representation ℂ G X} {τ : Representation ℂ G Y} (q : ρ.IntertwiningMap τ)
    (hq : Function.Injective q) (hu : IsUnitarisable τ) : IsUnitarisable ρ := by
  obtain ⟨B, h1, h2, h3⟩ := hu
  let B' : X →ₗ[ℂ] X →ₗ⋆[ℂ] ℂ := (B.compl₂ q.toLinearMap).comp q.toLinearMap
  have hB : ∀ v w, B' v w = B (q v) (q w) := fun _ _ => rfl
  refine ⟨B', fun v w => by rw [hB, hB, h1], fun v hv => by
    rw [hB]; exact h2 _ fun e => hv (hq (e.trans (map_zero q).symm)), fun g v w => ?_⟩
  rw [hB, hB, ← h3 g (q v) (q w)]
  rw [q.isIntertwining _ _ g v, q.isIntertwining _ _ g w]

section Local

open GlobalTheory.PRep GlobalTheory.LocGL

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem injective_of_irreducible {G X Y : Type} [Group G] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y]
    [Module ℂ Y] {ρ : Representation ℂ G X} {τ : Representation ℂ G Y} (hi : ρ.IsIrreducible)
    (q : ρ.IntertwiningMap τ) (h0 : q.toLinearMap ≠ 0) : Function.Injective q := by
  rcases ((GlobalTheory.CuspRep.isIrreducible_iff _).1 hi).2 (LinearMap.ker q.toLinearMap) (fun g v hv => by
    rw [LinearMap.mem_ker] at hv ⊢
    change q (ρ g v) = 0
    rw [q.isIntertwining _ _ g v]
    change τ g (q.toLinearMap v) = 0
    rw [hv, map_zero]) with h | h
  · exact LinearMap.ker_eq_bot.1 h
  · exact absurd (LinearMap.ker_eq_top.1 h) h0

theorem isUnitarisable_of_isSpeh_one {a : ℕ} {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    {ρ : Representation ℂ (GL (Fin a) k) X} (hs : IsSmooth ρ) (hi : ρ.IsIrreducible)
    {τ : Representation ℂ (GL (Fin a) k) Y} (h : IsSpeh (IrrGL.of ρ hs hi) 1 τ) (hu : IsUnitarisable τ) :
    IsUnitarisable ρ := by
  obtain ⟨hd, hτ, p, hp, -⟩ := h
  have key : ∀ y : Fin 1 → IrrGL k, y = (fun _ => IrrGL.of ρ hs hi) → ∀ hd : ∑ i, (y i).1 = a,
      Nonempty ((IrrGL.of ρ hs hi).rep.Equiv (prodIrr y hd)) := by
    rintro _ rfl hd
    exact nonempty_equiv_prodIrr_one _ hd
  obtain ⟨e⟩ := key _ (funext fun _ => by simp [spehFactor]) hd
  let q : ρ.IntertwiningMap τ := p.comp (e.toIntertwiningMap.comp (IrrGL.equivOf ρ hs hi).toIntertwiningMap)
  have hq : Function.Surjective q :=
    hp.comp (e.toLinearEquiv.surjective.comp (IrrGL.equivOf ρ hs hi).toLinearEquiv.surjective)
  refine isUnitarisable_of_injective q (injective_of_irreducible hi q fun h0 => ?_) hu
  have : Nontrivial Y := ((GlobalTheory.CuspRep.isIrreducible_iff _).1 hτ).1
  obtain ⟨y, hy⟩ := exists_ne (0 : Y)
  obtain ⟨v, rfl⟩ := hq y
  exact hy (LinearMap.congr_fun h0 v)

end Local

section Speh

open GlobalTheory.PRep GlobalTheory.LocGL

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E]

theorem isSpehQuot_of_isSpeh {a d N : ℕ} (h : ∑ _ : Fin d, a = N) {w : HeightOneSpectrum (𝓞 E)} (σ : LocIrr w a)
    (σ' : LocIrr w N) (hs : IsSpeh (IrrGL.of σ.ρ σ.smooth σ.irred) d σ'.ρ) : IsSpehQuot h σ σ' := by
  obtain ⟨hd, -, p, hp, -⟩ := hs
  let T : ∀ i : Fin d, (twist σ.ρ (detChar (Fin a) (absPow (w.adicCompletion E) (((d : ℂ) - 1) / 2 - (i : ℕ))))).Equiv
      (spehFactor (IrrGL.of σ.ρ σ.smooth σ.irred) d i).rep := fun i =>
    (twistEquiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred) _).trans
      ((IrrGL.of σ.ρ σ.smooth σ.irred).twEquiv _ (isSmoothChar_absPow _))
  let M := multiProdEquiv (stdBlocks (fun _ : Fin d => a) h) T
  exact ⟨p.comp M.toIntertwiningMap, hp.comp M.toLinearEquiv.surjective⟩

end Speh

section Inf

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ}

theorem hasInfCharGL_unique {V : Submodule ℂ (Sm E N)} (hV : V ≠ ⊥) {τ : E →+* ℂ} {m m' : Multiset ℂ}
    (h : HasInfCharGL V τ m) (h' : HasInfCharGL V τ m') : m = m' := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 hV
  have e : ((m.map Neg.neg).map fun z => Polynomial.X - Polynomial.C z).prod =
      ((m'.map Neg.neg).map fun z => Polynomial.X - Polynomial.C z).prod := by
    refine Polynomial.funext fun u => ?_
    have := smul_left_injective ℂ h0 ((h.2 u φ hφ).symm.trans (h'.2 u φ hφ))
    simpa [Polynomial.eval_multiset_prod, Multiset.map_map] using this
  have e2 := congrArg Polynomial.roots e
  rw [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at e2
  exact Multiset.map_injective neg_injective e2

end Inf

theorem spehInf_eq (d : ℕ) (m : Multiset ℂ) : GlobalTheory.SphGal.spehInf d m = GlobalTheory.DefiniteBC.spehInf d m := by
  simp only [GlobalTheory.SphGal.spehInf, GlobalTheory.DefiniteBC.spehInf]
  rw [← List.sum_ofFn, ← List.map_coe_finRange_eq_range, List.map_map, List.ofFn_eq_map]
  rfl

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem discreteSpectrum_of_discreteSpectrumGL : GlobalTheory.Published.DiscreteSpectrumGL →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], DiscreteSpectrum E := by
  intro H E _ _ _ N hN V hV
  obtain ⟨a, d, π, -, hπ, hS⟩ := (H E N hN).1 V hV
  have hSp := hS
  obtain ⟨h, -⟩ := hSp
  have hda : d * a = N := hS.mul_eq
  have ha : 1 ≤ a := Nat.pos_of_mul_pos_left (by omega : 0 < d * a)
  have hC := (H E N hN).2.2.2.2 V hV a d π hπ hS
  obtain ⟨V₁, ⟨hV₁, hS₁⟩, -⟩ := (H E a ha).2.1 a 1 π (one_mul a) hπ
  have hC₁ := (H E a ha).2.2.2.2 V₁ hV₁ a 1 π hπ hS₁
  refine ⟨a, d, h, π, fun hc => GlobalTheory.DiscSpec.isCsd_of_isSpehOf H hN hV hc hπ hS, fun w σ' hσ' => ?_, fun τ m' hm' => ?_⟩
  · refine ⟨GlobalTheory.T.discreteAutomorphicRepGL_localComponent_isUnitarisable E N V hV w σ' hσ', ?_⟩
    obtain ⟨σ, -, hσ, -⟩ := hC.exLoc w
    obtain ⟨-, τ, -, hτ⟩ := hC₁.exLoc w
    refine ⟨σ, hσ, isUnitarisable_of_isSpeh_one σ.smooth σ.irred (hC₁.loc w σ τ hσ hτ)
      (GlobalTheory.T.discreteAutomorphicRepGL_localComponent_isUnitarisable E a V₁ hV₁ w τ hτ), isSpehQuot_of_isSpeh h σ σ' (hC.loc w σ σ' hσ hσ')⟩
  · obtain ⟨m, hm, hm''⟩ := hC.inf τ
    exact ⟨m, hm, (hasInfCharGL_unique hV.ne_bot hm' hm'').trans (spehInf_eq d m)⟩

end GlobalTheory.DiscreteSpectrumCM

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelCharacterTeichmullerLabelOfGoodTypesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelCharacter_teichmullerLabel_of_goodTypes : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks),
    GlobalTheory.IndefiniteRowSideFullHecke.CommutingLevelOperators.GoodTypes R → ∀ (k : Fin 2) (v : D.nd.PlG k) (i : Fin D.R.m) (PP : Pl D.host.E),
    R.C.P.Div k PP → ∀ (iso : ZMod (D.host.g k) ≃+* kP PP) (ε : ℤ), (ε = 1 ∨ ε = -1) →
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    ∃ L : GlobalTheory.GLq.LabelDatum (D.host.g k), (∀ f, D.ntypes.eSer k f = GlobalTheory.GLq.eSerC L D.R.r f) ∧
      ∃ c : ZMod (D.host.g k),
        GlobalTheory.GLp.IsCharLab L ((zpowGroupHom ε).comp ((R.chi ((i : ℕ) + 1) PP).comp
          (Units.map (iso : ZMod (D.host.g k) →* kP PP)))) c ∧
        (c = ((D.nd.chiT k v i : (ZMod (D.host.g k))ˣ) : ZMod (D.host.g k)) ∨
          c = (((D.nd.chiT k v i)⁻¹ : (ZMod (D.host.g k))ˣ) : ZMod (D.host.g k))) := by
  first | exact @GlobalTheory.CharLabTransport.charLab_of_goodTypes | exact GlobalTheory.CharLabTransport.charLab_of_goodTypes | (intros; apply GlobalTheory.CharLabTransport.charLab_of_goodTypes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelSubgroupRestrictedProductOfLawsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_subgroup_restricted_product_of_laws : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ i, LevProd R i := by
  first | exact @GlobalTheory.LevelProduct.levProd_of_laws | exact GlobalTheory.LevelProduct.levProd_of_laws | (intros; apply GlobalTheory.LevelProduct.levProd_of_laws <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LieDerivativeInducedTensorFormsStatement
section
open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_derivative_induced_tensor_forms : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] {c N : ℕ} (n : Fin c → ℕ) (h : ∑ i, n i = N) (π : ∀ i, CuspSub E (n i)) (X : Lie E N) (φ : Sm E N), φ ∈ indForms h π → ∀ (k : Kinf E N) (g : GL (Fin N) (Af E)), (fun m => (lie E N X φ).1 (leviEmb (Ad E) (stdBlocks n h) m * (infGL E N (Unitary.toUnits k) * finGL E N g))) ∈ tensorForms π := by
  first | exact @GlobalTheory.LieTensor.lie_tensorForms | exact GlobalTheory.LieTensor.lie_tensorForms | (intros; apply GlobalTheory.LieTensor.lie_tensorForms <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalAbsorptionLengthBoundOfBlochKato
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.ClosingStatement

theorem main : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK →
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
      BlochKatoDuality.Conclusion1 D ∧ BlochKatoDuality.Conclusion2 D := by
  intro hBK hTD hEC D _ _ _
  have h5 : Formalism.MainNotions.LocalSituation.Conclusion5 D := GlobalTheory.T.blochKatoLocal_all_of_tateDuality_eulerChar hBK hTD hEC D
  have a1 : BlochKatoDuality.adm1 D := dimension_input_one_of_bloch_kato D h5
  have a2 : BlochKatoDuality.adm2 D := dimension_input_two_of_bloch_kato D h5
  have a3 : BlochKatoDuality.adm3 D := fun l _ K => GlobalTheory.T.tate_H2_period_datum hTD l (D.loc l) K
  have a5 : BlochKatoDuality.adm5 D := fun l _ K => GlobalTheory.T.finite_H1_period_datum hTD l (D.loc l) K
  have a6 : BlochKatoDuality.adm6 D := fun l _ K => (GlobalTheory.T.tateDual_deRham_and_filZero_dim_all D l K).1
  exact ⟨BlochKatoDuality.ramification_two_and_conjugation_at_q_and_d D a1 a2 a6, BlochKatoDuality.second_proposition_every_localisation D a1 a2 a3 a5 a6⟩

end GlobalTheory.ClosingStatement
end

