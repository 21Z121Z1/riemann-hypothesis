import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SecEqZeroOfComplex
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MarkedIsometryHalf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0922
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0907
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0923
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Formalism.SharpRestriction.Bundle0002
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0030
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPullbackSectionToLevelCover
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0915
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0924
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0008
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2023

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetCharacterEqOfMarkedLatticeIsometry
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix
namespace GlobalTheory.MarkIso

open GlobalTheory.Member

set_option maxHeartbeats 2000000 in

theorem xi_det_eq_of_marked_isometry : ∀ {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} (l : Level H) (V : HSp D)
    (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (hio : LinearMap.range io = latG V 1)
    (A A' : Datum H) (t : Dw.La →ₗ[𝓞 D.host.E] A.La) (t' : Dw.La →ₗ[𝓞 D.host.E] A'.La)
    (X X' : Data D.host.E V.rank) (φ : A.La ≃ₗ[𝓞 D.host.E] X.Λ) (φ' : A'.La ≃ₗ[𝓞 D.host.E] X'.Λ) (g g' : GA D V)
    (hW : ModelW V rfl X) (hW' : ModelW V rfl X')
    (hE : ∀ a b, ((A.EF a b : ℤ) : ℚ) =
      Algebra.trace ℚ D.host.E (-X.ξ0 * herm X.Gm (φ a : Fin V.rank → D.host.E) (φ b)))
    (hE' : ∀ a b, ((A'.EF a b : ℤ) : ℚ) =
      Algebra.trace ℚ D.host.E (-X'.ξ0 * herm X'.Gm (φ' a : Fin V.rank → D.host.E) (φ' b)))
    (hL : (X.Λ : Set (Fin V.rank → D.host.E)) =
      (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast rfl) '' (latG V g : Set _))
    (hL' : (X'.Λ : Set (Fin V.rank → D.host.E)) =
      (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast rfl) '' (latG V g' : Set _))
    (hm : ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∃ w ∈ latGHat V g, finVec V ((φ (t a) : Fin V.rank → D.host.E) ∘ Fin.cast rfl) -
        (finHom V g).1.mulVec (finVec V (io a)) = (l.M : ℕ) • w)
    (hm' : ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∃ w ∈ latGHat V g', finVec V ((φ' (t' a) : Fin V.rank → D.host.E) ∘ Fin.cast rfl) -
        (finHom V g').1.mulVec (finVec V (io a)) = (l.M : ℕ) • w)
    (gam : A.La ≃ₗ[𝓞 D.host.E] A'.La) (hgE : ∀ a b, A'.EF (gam a) (gam b) = A.EF a b)
    (hgm : ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∃ x, gam (t a) = t' a + l.M • x)
    (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ)
    (hxi1 : ∀ u : GA D V, gLat V u = latHat V → (∃ w ∈ GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)),
      ((Matrix.GeneralLinearGroup.det (finHom V u) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) :
        (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = (l.M : ℕ) • w) → xi (Matrix.GeneralLinearGroup.det (finHom V u)) = 1)
    (hxi2 : ∀ γ ∈ GQ V, xi (Matrix.GeneralLinearGroup.det (finHom V γ)) = 1), xi (Matrix.GeneralLinearGroup.det (finHom V g')) = xi (Matrix.GeneralLinearGroup.det (finHom V g)) := by
  intro D H Dw l V io hio A A' t t' X X' φ φ' g g' hW hW' hE hE' hL hL' hm hm' gam hgE hgm xi hxi1 hxi2
  have hGm : X'.Gm = X.Gm := hW'.1.trans hW.1.symm
  have hξ : X'.ξ0 = X.ξ0 := hW'.2.trans hW.2.symm
  let φL : A.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E) := X.Λ.subtype ∘ₗ φ.toLinearMap
  let φL' : A'.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E) := X'.Λ.subtype ∘ₗ φ'.toLinearMap
  have hr : Set.range φL = X.Λ := by
    ext v
    exact ⟨by rintro ⟨a, rfl⟩; exact (φ a).2, fun hv => ⟨φ.symm ⟨v, hv⟩,
      congrArg Subtype.val (φ.apply_symm_apply ⟨v, hv⟩)⟩⟩
  have hr' : Set.range φL' = X'.Λ := by
    ext v
    exact ⟨by rintro ⟨a, rfl⟩; exact (φ' a).2, fun hv => ⟨φ'.symm ⟨v, hv⟩,
      congrArg Subtype.val (φ'.apply_symm_apply ⟨v, hv⟩)⟩⟩
  have hcc : cc (-X.ξ0) = -(-X.ξ0) := by
    have := X.ξ0_im
    simp only [cc, map_neg] at this ⊢
    rw [this]
  obtain ⟨δ', hδ1, hδ2⟩ := GlobalTheory.IsoExt.exists_unitary_of_isometry _ H A A' V.rank (-X.ξ0) X.Gm φL φL' gam hcc
    ⟨Subtype.val_injective.comp φ.injective, by rw [hr]; exact X.Λ_span, X.Gm_herm, X.Gm_det,
      fun x y => hE x y⟩
    ⟨Subtype.val_injective.comp φ'.injective, by rw [hr']; exact X'.Λ_span, hGm ▸ X'.Gm_herm, hGm ▸ X'.Gm_det,
      fun x y => by rw [hE' x y, hGm, hξ]; rfl⟩ hgE
  have hG0 : X.Gm = -(HSpace.gram V)ᵀ := by
    rw [hW.1]
    simp
  obtain ⟨r1, -, r3, -⟩ := GlobalTheory.T.rational_points_adelicUnitary_eq_unitary D V
  obtain ⟨δ, hδ⟩ := r3 δ' (by rw [← hG0]; exact hδ1)
  have hLg : Set.range φL = latG V g := hr.trans (hL.trans (Set.image_id _))
  have hLg' : Set.range φL' = latG V g' := hr'.trans (hL'.trans (Set.image_id _))
  obtain ⟨u, h1, h2, h3⟩ := GlobalTheory.ConjMark.exists_of_matched V g g' δ δ' 1 l.M (by have := l.three_le; omega) l.Mb _
    l.prod hδ (fun v => by
      rw [← SetLike.mem_coe, ← SetLike.mem_coe, ← hLg, ← hLg']
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨_, hδ2 a⟩
      · rintro ⟨a, ha⟩
        refine ⟨gam.symm a, ?_⟩
        have e := hδ2 (gam.symm a)
        rw [LinearEquiv.apply_symm_apply, ha] at e
        have e' := congrArg (fun t => ((δ'⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ t) e
        simpa only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] using e'.symm)
    (fun v hv => by rw [Matrix.one_mulVec]; exact hv)
    (fun b hb x hx => by
      rw [← hio] at hx
      obtain ⟨x, rfl⟩ := hx
      have hv : b • x ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La) :=
        Submodule.smul_mem_smul hb trivial
      rw [← map_smul]
      refine ⟨φL (t (b • x)), φL' (t' (b • x)), hm _ hv, hm' _ hv, ?_⟩
      obtain ⟨z, hz⟩ := hgm _ hv
      refine ⟨-φL' z, ?_, ?_⟩
      · rw [← SetLike.mem_coe, ← hLg']
        exact ⟨-z, map_neg _ _⟩
      · rw [Matrix.one_mulVec, ← hδ2, hz, map_add, map_nsmul, smul_neg]
        abel)
  have hδQ : δ ∈ GQ V := (r1 δ).2 ⟨δ', hδ⟩
  have h3' : (finHom V u).1.det * 1 - 1 ∈
      GlobalTheory.AdLat.hat1 D.host.F ((algebraMap (𝓞 D.host.E) D.host.E) '' (l.Mb : Set (𝓞 D.host.E))) := by
    simpa [Algebra.TensorProduct.one_def] using h3
  have hq := GlobalTheory.DetTranslate.quot_cong_one D.host.F (cF D) l.M l.Mb _ l.coprime l.prod
    (fun b hb => ⟨H.bar b, Ideal.mem_map_of_mem (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) hb, H.bar_eq b⟩)
    _ _ 1 (GlobalTheory.DetTranslate.det_int_of_gLat V h1) (GlobalTheory.DetTranslate.det_int_of_gLat V (GlobalTheory.DetTranslate.gLat_one V))
    (finHom_herm_det D V u).2.1 (finHom_herm_det D V 1).2.1 h3' (by simp)
  have hK := hxi1 u h1 (by
    obtain ⟨w, hw, e⟩ := hq
    refine ⟨w, hw, ?_⟩
    simpa using e)
  have h4 := congrArg (fun g => xi (Matrix.GeneralLinearGroup.det g)) h2
  simp only [map_mul] at h4
  rw [hK, hxi2 δ hδQ, mul_one, one_mul] at h4
  exact h4

end GlobalTheory.MarkIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsExactLocalConditionDataAtPlaceStatement
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_exactLocalConditionData_at_place : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
    (π : D.nd.X i), tableLineDegreeTwo.adm20 D HW F → AdmissibleParameterJ.ConclusionJa D → GoodR D.nd i r → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.admG2 i r ρ π →
    TruncatedSeriesCountingIdentities.admG3 i r ρ π → TruncatedSeriesCountingIdentities.FamilyContinuous i r → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π → TruncatedSeriesCountingIdentities.CyclotomicInertiaImage (D := D) i → 5 ≤ D.nd.l i →
    D.nd.l i ∉ D.host.small → D.nd.l i ≠ D.host.q → D.nd.l i ≠ D.host.d →
    (∀ (n : ℕ) [NeZero n] (up : ZMod n → Bool) (τ : ZMod n → D.what₂.Tau), ∃ (h w η : ZMod n → ℕ) (typ : ZMod n → Bool)
      (U : ZMod n → Multiset ℤ), tableLineDegreeTwo.PositionHyps (D.nd.l i) n D.R.t h w η typ U ∧ ∀ (a : ZMod n) (b : ℤ),
        ((U a).count (b + w a) = 1 ↔ (b : ℚ) ∈ AdmissibleParameterJ.JW D (up a) (D.nd.j i) (τ a)) ∧ (U a).count (b + w a) ≤ 1) →
    ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      ∃ (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hA : CaseA (D.nbr i w hw).Kw C.LL) (lam : ↥(OL C.LL)) (_ : Irreducible lam)
        (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ)
        (h w' η : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → ℕ)
        (typ : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Bool)
        (U : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Multiset ℤ),
        SetC HW r ρ π C hA lam θ h w' η typ U := by
  first | exact @GlobalTheory.UseLocInst.exists_setC | exact GlobalTheory.UseLocInst.exists_setC | (intros; apply GlobalTheory.UseLocInst.exists_setC <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHubDataFamilyStatement
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hub_data_family : Hypotheses₂ → ∀ {eps : ℝ} (Fm : FamP eps), ∀ (C C₂ : ℝ) (CT : ℕ), TwGood Fm → FactsF Fm C CT → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x), TwistedPlaces.ShaFinOdd (Fm.D x i) → ∀ exc : Finset ℕ, ∃ (HW : HWOf (Fm.D x i).loc) (F : FonOf (Fm.D x i).loc (Fm.D x i).locA HW) (_ : CmpOf (Fm.D x i).loc (Fm.D x i).locA HW F) (X : KillingConditions.HubData (Fm.D x i)), X.exc = exc ∧ AdmissibleParameterJ.AdmJ (Fm.L x i) ∧ Setup (Fm.L x i) (Fm.ex x hx i).nch HW X C₂ := by
  first | exact @GlobalTheory.NLink.exists_setup_large | exact GlobalTheory.NLink.exists_setup_large | (intros; apply GlobalTheory.NLink.exists_setup_large <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralCoverFormPullbackCombination
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.NX Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.CoverRead GlobalTheory.TowerCov GlobalTheory.Member
open scoped TensorProduct Matrix
open Classical

namespace GlobalTheory.CoverPullComb

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem exists_pull_comb_integral : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ C : Cover T j σ, C.IsUnif → C.IsPinned a n → ∀ (la : HeightOneSpectrum (𝓞 C.d.c₂.F)) (m : ℕ) (β : Fin m → Rul (T.Q.Xo j) T.Q.c), (∀ k, β k ∈ sec (T.Q.Xo j) T.Q.c a n) → ∀ y : Fin m → C.d.c₂.F, (∑ k, C.σ₂ (y k) • T.phiJ j σ a (β k)) ∈ C.intForms a n {la} → ∃ g : Fin m → Rul C.d.Xo₂ C.d.c₂, (∀ k, g k ∈ sec C.d.Xo₂ C.d.c₂ a n) ∧ (∀ k, C.IsPull (β k) (g k)) ∧ ∀ v ∈ valSet C.d.Xo₂ C.d.c₂ (algCls C.d.Xo₂ C.d.c₂) la, 0 ≤ v (∑ k, y k • g k) := by
  intro D T hL j hj σ hσ a n hD C hU hP la m β hβ y hy
  have hpull : ∀ k, ∃ g₂ ∈ sec C.d.Xo₂ C.d.c₂ a n, C.IsPull (β k) g₂ :=
    fun k => GlobalTheory.CovPull.exists_pull D T hL j hj σ hσ C hU.1 a n (β k) (hβ k)
  choose g hg hgp using hpull
  refine ⟨g, hg, hgp, ?_⟩
  obtain ⟨f₂, ⟨hf₂c, hf₂i⟩, hf₂r⟩ := hy

  let R : Rul C.d.Xo₂ C.d.c₂ →ₛₗ[C.σ₂] (GA D (T.V j σ) → ℂ) :=
    (lieFac (T.Q.Dw j) (xiR D) a : ℂ) •
      ((adel (T.V j σ) C.dict₂ (muPin (T.V j σ) C.dict₂ (T.mu j σ) C.cc₂)).comp (rdU C.U₂))
  have hR : ∀ f, C.rd a f = R f := fun _ => rfl
  have hsum : C.rd a (∑ k, y k • g k) = ∑ k, C.σ₂ (y k) • T.phiJ j σ a (β k) := by
    rw [hR, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smulₛₗ, ← hR, hP.2 (β k) (hβ k) (g k) (hg k) (hgp k)]
  set s := ∑ k, y k • g k with hs
  have hsmem : s ∈ sec C.d.Xo₂ C.d.c₂ a n := Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hg k)
  have hdmem : f₂ - s ∈ sec C.d.Xo₂ C.d.c₂ a n := Submodule.sub_mem _ hf₂c.1 hsmem
  have hd0 : C.rd a (f₂ - s) = 0 := by
    rw [hR, map_sub, ← hR, ← hR, hf₂r, hsum, sub_self]
  have heq : f₂ = s := by
    by_contra hne
    have hne' : f₂ - s ≠ 0 := sub_ne_zero.mpr hne
    have hli : LinearIndependent C.d.c₂.F (fun _ : Fin 1 => f₂ - s) := by
      rw [Fintype.linearIndependent_iff]
      intro c hc i
      rw [Fin.sum_univ_one] at hc
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      by_contra hc0
      apply hne'
      calc f₂ - s = (c 0)⁻¹ • (c 0 • (f₂ - s)) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
        _ = 0 := by rw [hc, smul_zero]
    have hC := GlobalTheory.CoverIndep.cover_rd_linearIndependent D T hL j hj σ hσ C hU hP.1 a n hD 1 (fun _ => f₂ - s)
      (fun _ => hdmem) hli
    exact hC.ne_zero 0 hd0
  intro v hv
  rw [← heq]
  exact hf₂i la rfl v hv

end GlobalTheory.CoverPullComb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralTensorTorsionCocycleOfTorsionLocalStatement
section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralTensorTorsion_cocycle_of_torsion_localCocycle : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (lam : ↥(OL C.LL)), Irreducible lam →
    ∀ {k : ℕ} (N : Br.G D.nbr i w hw →* Matrix (Fin k) (Fin k) ↥(OL C.LL)) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (a : ℕ)
      (f : Br.G D.nbr i w hw → (Fin k → ↥C.LL.1) ⧸ stdG ↥(OL C.LL) ↥C.LL.1 k),
    f ∈ divisibleCocycles (latC C N) → (∀ g, lam ^ a • f g = 0) →
    ∃ z' : Br.G D.nbr i w hw → ↥(latC C (twistM N θ)).T ⊗[↥(OL C.LL)] ↥(Xq ↥C.LL.1 lam a),
      tableLineDegreeTwo.IsCoc (latC C (twistM N θ)) ↥(Xq ↥C.LL.1 lam a) (chiT C θ 1) z' ∧ ∀ g, iotaW ↥C.LL.1 lam a k (z' g) = f g := by
  first | exact @GlobalTheory.UseLoc.Cases.LiftW.lift_cocycle | exact GlobalTheory.UseLoc.Cases.LiftW.lift_cocycle | (intros; apply GlobalTheory.UseLoc.Cases.LiftW.lift_cocycle <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsCentAtScalar
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

noncomputable section

namespace GlobalTheory.CentScal

variable {D : D7}

def scalU (V : HSp D) (a : AE D) (h : a * cA D a = 1) : GA D V :=
  ⟨⟨Matrix.diagonal (fun _ => a), Matrix.diagonal (fun _ => cA D a),
      by rw [Matrix.diagonal_mul_diagonal, h, Matrix.diagonal_one],
      by rw [Matrix.diagonal_mul_diagonal, mul_comm, h, Matrix.diagonal_one]⟩, by
    show Formalism.UG.cT _ (Matrix.diagonal (fun _ => a)) * _ * Matrix.diagonal (fun _ => a) = _
    ext k l
    simp only [Formalism.UG.cT, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose, Matrix.diagonal_mul,
      Matrix.mul_diagonal]
    have e : ∀ t : AE D, cA D a * t * a = t := fun t => by rw [mul_right_comm, mul_comm (cA D a) a, h, one_mul]
    exact e _⟩

theorem mt_scalU (V : HSp D) (a : AE D) (h : a * cA D a = 1) :
    Formalism.L2.Theta.mt V (scalU V a h) = Matrix.diagonal (fun _ => a) := rfl

theorem scalU_mem_center (V : HSp D) (a : AE D) (h : a * cA D a = 1) :
    scalU V a h ∈ Subgroup.center (GA D V) := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  apply Units.ext
  show (matHom V g).1 * Matrix.diagonal (fun _ => a) =
    Matrix.diagonal (fun _ => a) * (matHom V g).1
  ext k l
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm]

theorem scalU_mem_GfC (V : HSp D) (a : AE D) (h : a * cA D a = 1) (h1 : infPart D a = 1) :
    scalU V a h ∈ GfC V := by
  show infHom V (scalU V a h) = 1
  apply Units.ext
  show (Matrix.diagonal (fun _ => a)).map (infPart D) = 1
  rw [Matrix.diagonal_map (map_zero _), h1, Matrix.diagonal_one]

theorem scal_norm_one {R : Type} [CommRing R] (c : R →+* R) (hc : ∀ t, c (c t) = t) (e x w : R) (he2 : e * e = e)
    (hef : e * c e = 0) (hxw : x * w = 1) :
    (e * x + c e * c w + (1 - e - c e)) * c (e * x + c e * c w + (1 - e - c e)) = 1 := by
  have hf2 : c e * c e = c e := by rw [← map_mul, he2]
  have hyX : c w * c x = 1 := by rw [← map_mul, mul_comm, hxw, map_one]
  simp only [map_add, map_mul, map_sub, map_one, hc]
  linear_combination (x * c x + c w * w - x - c w - c x - w + 2) * hef +
    (x * w - x - w + 1) * he2 + (c w * c x - c w - c x + 1) * hf2 + e * hxw + c e * hyX

theorem hom_scal {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (e f x y : R) (h0 : φ e = 0) (h1 : φ f = 0) :
    φ (e * x + f * y + (1 - e - f)) = 1 := by
  rw [map_add, map_add, map_mul, map_mul, map_sub, map_sub, map_one, h0, h1]
  simp

theorem scal_supp {R : Type} [CommRing R] (e f x y : R) (he2 : e * e = e) (hf2 : f * f = f) (hef : e * f = 0) :
    (e + f) * (e * x + f * y + (1 - e - f) - 1) = e * x + f * y + (1 - e - f) - 1 := by
  linear_combination (x - 1) * he2 + (y - 1) * hf2 + (y + x - 2) * hef

theorem exists_isCentAt_scalar : ∀ (D : D7) (i : Fin D.R.m) (Q : Finset (Pl D.host.E)) (eQ : AE D), IsIdemSum eQ Q → ∀ ϖ : D.host.E, ϖ ≠ 0 → ∃ z : GA D (Vc D i), IsCentAt i Q z ∧ mt (Vc D i) z = Matrix.diagonal (fun _ => eQ * incA D ϖ⁻¹ + cA D eQ * cA D (incA D ϖ) + (1 - eQ - cA D eQ)) := by
  intro D i Q eQ hQ ϖ hϖ
  have he2 : eQ * eQ = eQ := GlobalTheory.PlaceVec.idemSum_mul_self hQ
  have hf2 : cA D eQ * cA D eQ = cA D eQ := by rw [← map_mul, he2]
  have hef : eQ * cA D eQ = 0 := hQ.2
  have hxw : incA D ϖ⁻¹ * incA D ϖ = 1 := by rw [← map_mul, inv_mul_cancel₀ hϖ, map_one]
  have hunit := scal_norm_one (cA D) cA_cA eQ (incA D ϖ⁻¹) (incA D ϖ) he2 hef hxw
  have hinf : infPart D (eQ * incA D ϖ⁻¹ + cA D eQ * cA D (incA D ϖ) + (1 - eQ - cA D eQ)) = 1 := by
    have h0 : infPart D eQ = 0 := GlobalTheory.PlaceVec.idemSum_infPart hQ
    have h0' : infPart D (cA D eQ) = 0 := GlobalTheory.PlaceVec.infPart_cA h0
    exact hom_scal (infPart D) _ _ _ _ h0 h0'
  refine ⟨scalU (Vc D i) _ hunit, ⟨scalU_mem_center _ _ hunit, scalU_mem_GfC _ _ hunit hinf, eQ, hQ, ?_⟩,
    mt_scalU _ _ hunit⟩
  intro k l
  rw [mt_scalU]
  by_cases hkl : k = l
  · subst hkl
    rw [Matrix.sub_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    exact scal_supp _ _ _ _ he2 hf2 hef
  · rw [Matrix.sub_apply, Matrix.diagonal_apply_ne _ hkl, Matrix.one_apply_ne hkl, sub_zero, mul_zero]

end GlobalTheory.CentScal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocalSlotDataOffExceptionalPrimesStatement
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localPositionData_off_exceptional_primes : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ (a : Fm.Ix x), AdmissibleParameterJ.JumpConditions (Fm.L x a) → ∀ l : ℕ, l.Prime → LevelStarExponents.lStar (Fm.L x a) < (l : ℝ) → (5 ≤ l ∧ (Fm.D x a).R.t + 1 < l ∧ l ≠ (Fm.D x a).host.q ∧ l ≠ (Fm.D x a).host.d ∧ l ∉ (Fm.D x a).host.small) ∧ (l ∉ GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.Exc (Fm.L x a) → ∀ j : ℕ, 1 ≤ j → j ≤ (Fm.D x a).R.m → ∀ (n : ℕ) [NeZero n] (up : ZMod n → Bool) (τ : ZMod n → (Fm.D x a).what₂.Tau), ∃ (h w η : ZMod n → ℕ) (typ : ZMod n → Bool) (U : ZMod n → Multiset ℤ), tableLineDegreeTwo.PositionHyps l n (Fm.D x a).R.t h w η typ U ∧ ∀ (c : ZMod n) (b : ℤ), ((U c).count (b + w c) = 1 ↔ (b : ℚ) ∈ AdmissibleParameterJ.JW (Fm.D x a) (up c) j (τ c)) ∧ (U c).count (b + w c) ≤ 1) := by
  first | exact @GlobalTheory.LocalPositionData.position_data_exist | exact GlobalTheory.LocalPositionData.position_data_exist | (intros; apply GlobalTheory.LocalPositionData.position_data_exist <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNatIntegralFrameOfUniformizerMul
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory.FlatLift

theorem kmul_int : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (ϖ : 𝓞 D.host.E), ϖ ≠ 0 → ∃ k : ℕ, 0 < k ∧ ∀ u : WO S T, IsIntM (frMapO S T βS βT (u.map fun w => incA D (ϖ : D.host.E) * w)) → IsIntM (frMapO S T βS βT (k • u)) := by
  intro D S T βS βT ϖ hϖ
  let I : Ideal (𝓞 D.host.E) := Ideal.span {ϖ}
  have hI : I ≠ ⊥ := by simpa [I, Ideal.span_singleton_eq_bot] using hϖ
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem I)
  refine ⟨Ideal.absNorm I, Nat.pos_of_ne_zero (fun h => hI (Ideal.absNorm_eq_zero_iff.1 h)), fun u hu => ?_⟩
  have hk : ((Ideal.absNorm I : ℕ) : D.host.E) = (c : D.host.E) * (ϖ : D.host.E) := by
    have := congrArg (fun z : 𝓞 D.host.E => (z : D.host.E)) hc
    simpa using this.symm
  have hm : (((Ideal.absNorm I) • u : WO S T) : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (Formalism.IndefR.Datum.toEAf D) =
      Formalism.IndefR.Datum.eToEAf D (c : D.host.E) •
        ((u.map fun w => incA D (ϖ : D.host.E) * w : WO S T) : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map
          (Formalism.IndefR.Datum.toEAf D) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, nsmul_eq_mul]
    rw [map_natCast]
    have h1 : Formalism.IndefR.Datum.toEAf D (incA D (ϖ : D.host.E)) = Formalism.IndefR.Datum.eToEAf D (ϖ : D.host.E) := rfl
    rw [h1, ← mul_assoc, ← map_mul, ← hk, map_natCast]
  intro i j
  have he : frMapO S T βS βT ((Ideal.absNorm I) • u) =
      Formalism.IndefR.Datum.eToEAf D (c : D.host.E) • frMapO S T βS βT (u.map fun w => incA D (ϖ : D.host.E) * w) := by
    simp only [frMapO]
    rw [hm, Matrix.mul_smul, Matrix.smul_mul]
  rw [he, Matrix.smul_apply, smul_eq_mul]
  exact (Formalism.L2.Herm.intAf D.host.F D.host.E).mul_mem (Subring.subset_closure (Or.inl ⟨⟨((c : 𝓞 D.host.E) : D.host.E), ⟨c, rfl⟩⟩, rfl⟩)) (hu i j)

end GlobalTheory.FlatLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTwistedCharacterCocycleOfTorsionLocalCocycStatement
section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_twistedCharacter_cocycle_of_torsion_localCocycle : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (lam : ↥(OL C.LL)), Irreducible lam →
    ∀ (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (c a : ℕ) (f : Br.G D.nbr i w hw → (Fin 1 → ↥C.LL.1) ⧸ stdG ↥(OL C.LL) ↥C.LL.1 1),
    f ∈ divisibleCocycles (latC C (locOC C (chiRatO D.nd i c))) → (∀ g, lam ^ a • f g = 0) →
    ∃ z' : Br.G D.nbr i w hw → ↥(latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ c)).T ⊗[↥(OL C.LL)] ↥(Xq ↥C.LL.1 lam a),
      tableLineDegreeTwo.IsCoc (latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ c)) ↥(Xq ↥C.LL.1 lam a) (chiT C θ 1) z' ∧
      ∀ g, iotaC ↥C.LL.1 lam a (z' g) = f g := by
  first | exact @GlobalTheory.UseLoc.Cases.liftC_main | exact GlobalTheory.UseLoc.Cases.liftC_main | (intros; apply GlobalTheory.UseLoc.Cases.liftC_main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtraBoundOfTwistingEigenFactsStatement
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extra_bound_of_twisting_eigen_facts : Hypotheses₂ → ∃ (C : ℝ) (CT : ℕ), 0 ≤ C ∧ ∀ (D : D7) (nch : NChoice D), GlobalTheory.NFacts.Facts D nch → (PairedCharacterCondition.tieChi (D := D) ∧ (∃ Q : PairedCharacterCondition.Pend (D), PairedCharacterCondition.admDZ Q ∧ GlobalTheory.Pass.EigSpan Q) ∧ GlobalTheory.Pass.TieInePoly (D) ∧ GlobalTheory.TypeLeaf.SerLoc (D)) → Extra D C CT := by
  first | exact @GlobalTheory.ExtraFromFacts.main | exact GlobalTheory.ExtraFromFacts.main | (intros; apply GlobalTheory.ExtraFromFacts.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteLambdaPowerTorsionFieldModIntStatement
section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_lambdaPowerTorsionFieldModInt : ∀ {l : ℕ} [Fact l.Prime] (LL : FinExt l) (lam : ↥(OL LL)), Irreducible lam → ∀ a : ℕ, Finite ↥(Xq ↥LL.1 lam a) := by
  first | exact @GlobalTheory.UseLoc.Cases.finite_Xq | exact GlobalTheory.UseLoc.Cases.finite_Xq | (intros; apply GlobalTheory.UseLoc.Cases.finite_Xq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GeneralLinearHaarIsMulRightInvariantUnramified
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem gl_lc_sc (F : Type) [NontriviallyNormedField F] [LocallyCompactSpace F] (r : ℕ) :
    LocallyCompactSpace (GL (Fin r) F) ∧ SecondCountableTopology (GL (Fin r) F) := by
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : SecondCountableTopology (Matrix (Fin r) (Fin r) F) :=
    inferInstanceAs (SecondCountableTopology (Fin r → Fin r → F))
  haveI : LocallyCompactSpace (Matrix (Fin r) (Fin r) F) :=
    inferInstanceAs (LocallyCompactSpace (Fin r → Fin r → F))
  haveI : SecondCountableTopology (Matrix (Fin r) (Fin r) F)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin r) (Fin r) F)).symm.secondCountableTopology
  exact ⟨Units.isClosedEmbedding_embedProduct.locallyCompactSpace,
    Units.isEmbedding_embedProduct.secondCountableTopology⟩

theorem gl_unimodular : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E), (letI := M.mG; M.μG.IsMulRightInvariant) := by
  intro F E _ _ _ _ hU r M
  haveI : LocallyCompactSpace F := hU.lcF
  obtain ⟨h1, h2⟩ := gl_lc_sc F r
  letI := M.mG
  haveI := M.bG
  haveI := M.haarG
  refine ⟨fun g => ?_⟩
  rw [Measure.isMulLeftInvariant_eq_smul (Measure.map (· * g) M.μG) M.μG,
    ← Measure.modularCharacterFun_eq_haarScalarFactor, GlobalTheory.ParAvg.modularCharacterFun_GL, one_smul]

end GlobalTheory.JR
end

