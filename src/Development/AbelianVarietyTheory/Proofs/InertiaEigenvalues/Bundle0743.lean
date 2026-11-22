import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0732
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPotCrysAtOfMono0
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0068
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0735
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0399
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingSecond
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0160
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.Bundle0004
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1317
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0918
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0138
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0214
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0205
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0204
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0733
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HeckePin
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AbsNormUnderEqOfInertiaDegOneStatement
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.Pst
  GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absNorm_under_eq_of_inertiaDeg_one : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (w : HeightOneSpectrum (𝓞 L)), w.asIdeal.inertiaDeg ℤ = 1 → normV (w.under (𝓞 K)) = normV w := by
  first | exact @GlobalTheory.NormDegOne.normV_under_eq | exact GlobalTheory.NormDegOne.normV_under_eq | (intros; apply GlobalTheory.NormDegOne.normV_under_eq <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleConjugatePairPlacesEqOfTwistConditionA
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdmAll

theorem admissibleConjugatePairPlaces_eq_of_twist_condition : ∀ {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (Y : NExp D.R D.host D.what₂ D.LL0 N X),
  GlobalTheory.UnivChar.IsUnivChar Y → ∀ (i : X.Tw) (k : ℕ) (Q : Finset (Pl D.host.E)) (M : ℕ)
    (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ),
    TwOK i k Q (χ.comp (Y.delU i Q M)) → admissibleConjugatePairPlaces X i Q M = Q := by
  intro D N X Y hY i k Q M χ hT
  classical
  refine Finset.Subset.antisymm (admissibleConjugatePairPlaces_subset i Q M) fun v hv => ?_
  by_contra hna
  obtain ⟨A, hA⟩ := exists_isPlaceOver N.Om v
  obtain ⟨σ, hσ, hne⟩ := (hT.2.2.2.2.2.1 v A hA).2 hv
  apply hne
  have h1 : Y.delU i Q M σ = 1 := by
    apply Multiplicative.toAdd.injective
    funext w
    by_cases hw : w.1 ∈ admissibleConjugatePairPlaces X i Q M
    · rw [delU_on hY σ w hw]
      have hvp : v ∉ GalChar.pair D.host w.1 := by
        rintro (h | hc)
        · exact hna (h ▸ hw)
        · exact hna (conj_mem_admissibleConjugatePairPlaces hw hc)
      rw [(GalChar.delOf_laws D.host X.cc (X.l i) M _).2.2.2 v hvp A hA σ hσ]
      rfl
    · rw [delU_off hY (twSet_of_twOK hT) σ w hw]
      rfl
  rw [MonoidHom.comp_apply, h1, map_one]

end GlobalTheory.AdmAll
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleConjugatePairPlacesEqSelfOfGoodCharsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissibleConjugatePairPlaces_eq_self_of_good_chars : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) (M : ℕ) (Q : Finset (Pl D.host.E)) (d : PlE D.host → (G D.host.E N.Om →* Multiplicative (ZMod (X.l i ^ M)))), (∀ P ∈ Q, IsSplitPl D.host P) → (∀ P ∈ Q, ∀ P', IsConjPl D.host P P' → P' ∈ Q) → (∀ P ∈ Q, GlobalTheory.TwSys.GoodChar X i M P (d P) ∧ normV P % (2 * X.l i ^ M) = 1) → (0 < M ∨ ∀ P ∈ Q, P ∉ placesOver D.host.E (X.l i)) → admissibleConjugatePairPlaces X i Q M = Q := by
  first | exact @GlobalTheory.AdmSelf.admissibleConjugatePairPlaces_eq_self_of_goodChar | exact GlobalTheory.AdmSelf.admissibleConjugatePairPlaces_eq_self_of_goodChar | (intros; apply GlobalTheory.AdmSelf.admissibleConjugatePairPlaces_eq_self_of_goodChar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseCoverFramesDifferByRationalIsometry
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

namespace GlobalTheory.CoverFrameMove

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem move {D : D7} (V : HSp D) {r : ℕ} (hr : V.rank = r) (h γ₁ γ₂ : GA D V) (hγ₁ : γ₁ ∈ GQ V) (hγ₂ : γ₂ ∈ GQ V)
    (L₁ L₂ : Submodule (𝓞 D.host.E) (Fin r → D.host.E)) (G₁ G₂ : Matrix (Fin r) (Fin r) D.host.E)
    (hG₁ : G₁ = -(Matrix.reindex (finCongr hr) (finCongr hr) V.gram).transpose)
    (hG₂ : G₂ = -(Matrix.reindex (finCongr hr) (finCongr hr) V.gram).transpose)
    (hL₁ : (L₁ : Set (Fin r → D.host.E)) =
      (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast hr.symm) '' (latG V (γ₁ * h) : Set _))
    (hL₂ : (L₂ : Set (Fin r → D.host.E)) =
      (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast hr.symm) '' (latG V (γ₂ * h) : Set _)) :
    ∃ γ : GL (Fin r) D.host.E,
      (L₁ : Set (Fin r → D.host.E)) = (γ : Matrix (Fin r) (Fin r) D.host.E).mulVec '' (L₂ : Set _) ∧
      (∀ v w, herm G₁ ((γ : Matrix (Fin r) (Fin r) D.host.E).mulVec v) ((γ : Matrix (Fin r) (Fin r) D.host.E).mulVec w) =
        herm G₂ v w) ∧
      ∀ (τ : D.host.E →+* ℂ) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ), Formalism.MainNotions.StandardLattice.IsInfEmb τ θ →
        ∀ x : Matrix (Fin r) (Fin r) ℂ,
          Matrix.reindex (finCongr hr) (finCongr hr) (archM V θ (γ₁ * h)) * x =
            (γ : Matrix (Fin r) (Fin r) D.host.E).map τ *
              (Matrix.reindex (finCongr hr) (finCongr hr) (archM V θ (γ₂ * h)) * x) := by
  subst hr
  have hgr : Matrix.reindex (finCongr (rfl : V.rank = V.rank)) (finCongr rfl) V.gram = V.gram := by
    ext i j
    rfl
  have hre : ∀ m : Matrix (Fin V.rank) (Fin V.rank) ℂ,
      Matrix.reindex (finCongr (rfl : V.rank = V.rank)) (finCongr rfl) m = m := fun m => by
    ext i j
    rfl
  rw [hgr] at hG₁ hG₂
  obtain ⟨δ, hδu, hδf, hδa⟩ := GlobalTheory.MarkCoset.rational_matrix V _ (mul_mem hγ₁ (inv_mem hγ₂))
  have hprod : γ₁ * γ₂⁻¹ * (γ₂ * h) * 1 = γ₁ * h := by group
  obtain ⟨ht1, -⟩ := GlobalTheory.ShortMoveIso.transport (finHom V) (latGHat V)
    (fun g => (GlobalTheory.MarkCoset.latG_spec D V g).2) 1 (γ₁ * γ₂⁻¹) (γ₂ * h) 1 rfl
  rw [hprod] at ht1
  have hmem : ∀ (L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (g : GA D V),
      (L : Set (Fin V.rank → D.host.E)) =
        (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast (rfl : V.rank = V.rank).symm) '' (latG V g : Set _) →
      ∀ v, v ∈ L ↔ finVec V v ∈ latGHat V g := fun L g hL v => by
    rw [← (GlobalTheory.MarkCoset.latG_spec D V _).1, ← SetLike.mem_coe, hL]
    exact Set.ext_iff.1 (Set.image_id _) v
  have hlat : ∀ v, v ∈ L₂ ↔ δ.1 *ᵥ v ∈ L₁ := fun v => by
    rw [hmem _ _ hL₂, hmem _ _ hL₁, ht1, hδf]
  refine ⟨δ, ?_, fun u v => ?_, fun τ θ hθ x => ?_⟩
  · ext v
    constructor
    · intro hv
      have hri : δ.1 *ᵥ ((δ⁻¹).1 *ᵥ v) = v := by
        rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      exact ⟨(δ⁻¹).1 *ᵥ v, (hlat _).2 (by rw [hri]; exact hv), hri⟩
    · rintro ⟨u, hu, rfl⟩
      exact (hlat u).1 hu
  · rw [hG₁, hG₂]
    exact hδu u v
  · have hmul : ∀ a b : GA D V, archM V θ (a * b) = archM V θ a * archM V θ b := by
      intro a b
      rw [archM, archM, archM, map_mul, Units.val_mul, Matrix.map_mul]
    have e : γ₁ * h = γ₁ * γ₂⁻¹ * (γ₂ * h) := by group
    rw [hre, hre, e, hmul, hδa _ _ hθ, Matrix.mul_assoc]

set_option maxHeartbeats 1000000 in

theorem frames_differ : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ h : GA D (T.V j σ), ∃ γ : GL (Fin D.R.r) D.host.E, (((T.U j σ).X (T.dict j σ h).1).Λ : Set (Fin D.R.r → D.host.E)) = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec '' ((C.U₂.X (C.dict₂ h).1).Λ : Set _) ∧ (∀ v w, herm ((T.U j σ).X (T.dict j σ h).1).Gm ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm (C.U₂.X (C.dict₂ h).1).Gm v w) ∧ (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X (C.dict₂ h).1).Ψ) (h₁ : τ ∈ ((T.U j σ).X (T.dict j σ h).1).Ψ), mat (T.dict j σ h).2 ⟨τ, h₁⟩ = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat (C.dict₂ h).2 ⟨τ, h₂⟩) := by
  intro D T hT j hj σ hσ C hC h
  obtain ⟨hr₁, g₁, e₁, F₁, ik₁, φ₁, th₁, -, -, hth₁, -, hd₁⟩ := hT.adPin j hj σ hσ
  obtain ⟨-, -, -, -, -, hr₂, g₂, e₂, F₂, ik₂, φ₂, th₂, hW₂, hth₂, -, hd₂⟩ := hC
  obtain ⟨hr₀, hW₁⟩ := hT.modelW j hj σ hσ
  obtain ⟨γ₁, hγ₁, hL₁, -, hf₁⟩ := hd₁ h
  obtain ⟨γ₂, hγ₂, hL₂, -, hf₂⟩ := hd₂ h
  obtain ⟨γ, hl, hi, hf⟩ := move (T.V j σ) hr₁ h γ₁ γ₂ hγ₁ hγ₂ _ _ _ _ (hW₁ _).1 (hW₂ _).1 hL₁ hL₂
  refine ⟨γ, hl, hi, fun τ t₂ t₁ => ?_⟩
  have e₂' := hf₂ ⟨τ, t₂⟩
  have e₁' := hf₁ ⟨τ, t₁⟩
  rw [GlobalTheory.LettersCheck.isInfEmb_unique τ _ _ (hth₂ _ ⟨τ, t₂⟩) (hth₁ _ ⟨τ, t₁⟩)] at e₂'
  rw [e₁', e₂']
  exact hf τ _ (hth₁ _ ⟨τ, t₁⟩) _

end GlobalTheory.CoverFrameMove
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChangeOfSplittingPair
section
set_option autoImplicit false

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum Formalism.IndefR.Lift

noncomputable section

namespace GlobalTheory.SplitChange

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} {χV χW ν : (AE D)ˣ →* Circle}
  {om om' : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)}

theorem resEta_zero_of_triv {χ : (AE D)ˣ →* Circle} {n : ℕ} (h : ResEta D χ n) (hF : ∀ a, ν (idF D a) = 1) :
    ResEta D ν 0 :=
  ⟨h.1, fun η _ a => by rw [hF, pow_zero]⟩

theorem exists_twist_root (ho : IsWeilDatumO ψ V W χV χW om) (hν : IsHeckeChar D ν) (hF : ∀ a, ν (idF D a) = 1) :
    ∃ om', IsWeilDatumO ψ V W (χV * ν) (χW * ν) om' ∧ ∀ h g x y, IsDetRoot V h x → IsDetRoot W g y →
      om' (h, g) = (((ν y : Circle) : ℂ) * ((ν x : Circle) : ℂ)⁻¹) • om (h, g) := by
  obtain ⟨o, h1, h2⟩ := GlobalTheory.WeilChange.exists_weilDatum_twist D ψ ho.std V W χV χW ν ν om ho hν hν
    (resEta_zero_of_triv ho.resS hF) (resEta_zero_of_triv ho.resS hF)
  refine ⟨o, h1, fun h g x y hx hy => ?_⟩
  rw [h2 h g x y hx hy, Circle.coe_mul, Circle.coe_inv, mul_comm]

theorem twist_eq_root (ho : IsWeilDatumO ψ V W χV χW om) (hν : IsHeckeChar D ν) (hF : ∀ a, ν (idF D a) = 1)
    (ho' : IsWeilDatumO ψ V W (χV * ν) (χW * ν) om') {h : GA D V} {g : GA D W} {x y : (AE D)ˣ}
    (hx : IsDetRoot V h x) (hy : IsDetRoot W g y) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) :
    om' (h, g) f = (((ν y : Circle) : ℂ) * ((ν x : Circle) : ℂ)⁻¹) • om (h, g) f := by
  obtain ⟨o, h1, h2⟩ := exists_twist_root ho hν hF
  rw [GlobalTheory.WeilUniq.weilDatum_unique D ψ ho.std V W _ _ om' o ho' h1 _ f hf, h2 h g x y hx hy, LinearMap.smul_apply]

theorem exists_twist (ho : IsWeilDatumO ψ V W χV χW om) (hν : IsHeckeChar D ν) (hF : ∀ a, ν (idF D a) = 1)
    {nV : GA D V → ℂ} {nW : GA D W → ℂ} (hV : MuVal V ν nV) (hW : MuVal W ν nW) :
    ∃ om', IsWeilDatumO ψ V W (χV * ν) (χW * ν) om' ∧ ∀ h g, om' (h, g) = (nW g * (nV h)⁻¹) • om (h, g) := by
  obtain ⟨o, h1, h2⟩ := exists_twist_root ho hν hF
  refine ⟨o, h1, fun h g => ?_⟩
  obtain ⟨x, hx⟩ := hV.1 h
  obtain ⟨y, hy⟩ := hW.1 g
  rw [h2 h g x y hx hy, hV.2 h x hx, hW.2 g y hy]

theorem twist_eq (ho : IsWeilDatumO ψ V W χV χW om) (hν : IsHeckeChar D ν) (hF : ∀ a, ν (idF D a) = 1)
    (ho' : IsWeilDatumO ψ V W (χV * ν) (χW * ν) om') {nV : GA D V → ℂ} {nW : GA D W → ℂ} (hV : MuVal V ν nV)
    (hW : MuVal W ν nW) (h : GA D V) (g : GA D W) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) :
    om' (h, g) f = (nW g * (nV h)⁻¹) • om (h, g) f := by
  obtain ⟨x, hx⟩ := hV.1 h
  obtain ⟨y, hy⟩ := hW.1 g
  rw [twist_eq_root ho hν hF ho' hx hy hf, hV.2 h x hx, hW.2 g y hy]

theorem thetaKO_twist (ho : IsWeilDatumO ψ V W χV χW om) (hν : IsHeckeChar D ν) (hF : ∀ a, ν (idF D a) = 1)
    (ho' : IsWeilDatumO ψ V W (χV * ν) (χW * ν) om') {nV : GA D V → ℂ} {nW : GA D W → ℂ} (hV : MuVal V ν nV)
    (hW : MuVal W ν nW) (h : GA D V) (g : GA D W) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) :
    thetaKO om' h g f = nW g * (nV h)⁻¹ * thetaKO om h g f := by
  unfold thetaKO
  rw [twist_eq ho hν hF ho' hV hW h g hf, Pi.smul_apply, smul_eq_mul]

theorem chrTh_tup {C : Type*} [CommGroup C] (μ : ℕ → C) (η ν : C) (j : ℕ) :
    chrTh (tup μ ν) η j = ((chrTh μ η j).1 * ν, (chrTh μ η j).2 * ν) := by
  unfold chrTh tup
  rw [mul_right_comm]

theorem tup_mul {C : Type*} [CommGroup C] (μ : ℕ → C) (ξ ν : C) : tup μ (ξ * ν) = tup (tup μ ξ) ν := by
  funext j
  unfold tup
  rw [mul_assoc]

theorem change_of_splitting_pair (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW ν : (AE D)ˣ →* Circle)
    (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ho : IsWeilDatumO ψ V W χV χW om) (hν : IsHeckeChar D ν)
    (hF : ∀ a, ν (idF D a) = 1) :
    (∃ (nV : GA D V → ℂ) (nW : GA D W → ℂ), MuVal V ν nV ∧ MuVal W ν nW) ∧
    (∀ (nV : GA D V → ℂ) (nW : GA D W → ℂ), MuVal V ν nV → MuVal W ν nW →
      (∃ om', IsWeilDatumO ψ V W (χV * ν) (χW * ν) om' ∧ ∀ h g, om' (h, g) = (nW g * (nV h)⁻¹) • om (h, g)) ∧
      ∀ om', IsWeilDatumO ψ V W (χV * ν) (χW * ν) om' → ∀ h g f, IsThetaFunO ψ V W f →
        om' (h, g) f = (nW g * (nV h)⁻¹) • om (h, g) f) ∧
    ∀ om₁, IsWeilDatumO ψ V W χV χW om₁ → ∀ p f, IsThetaFunO ψ V W f → om₁ p f = om p f := by
  refine ⟨?_, fun nV nW hV hW => ⟨exists_twist ho hν hF hV hW, fun om' ho' h g f hf => twist_eq ho hν hF ho' hV hW h g hf⟩,
    fun om₁ h1 => GlobalTheory.WeilUniq.weilDatum_unique D ψ ho.std V W χV χW om₁ om h1 ho⟩
  obtain ⟨nV, hV, -⟩ := GlobalTheory.Member.exists_muVal D V ν hν hF
  obtain ⟨nW, hW, -⟩ := GlobalTheory.Member.exists_muVal D W ν hν hF
  exact ⟨nV, nW, hV, hW⟩

theorem change_of_splitting (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (μ : ℕ → (AE D)ˣ →* Circle)
    (η ν : (AE D)ˣ →* Circle) (j : ℕ) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ))
    (ho : IsWeilDatumO ψ V W (chrTh μ η j).1 (chrTh μ η j).2 om) (hν : IsHeckeChar D ν) (hF : ∀ a, ν (idF D a) = 1) :
    (∃ (nV : GA D V → ℂ) (nW : GA D W → ℂ), MuVal V ν nV ∧ MuVal W ν nW) ∧
    (∀ (nV : GA D V → ℂ) (nW : GA D W → ℂ), MuVal V ν nV → MuVal W ν nW →
      (∃ om', IsWeilDatumO ψ V W (chrTh (tup μ ν) η j).1 (chrTh (tup μ ν) η j).2 om' ∧
        ∀ h g, om' (h, g) = (nW g * (nV h)⁻¹) • om (h, g)) ∧
      ∀ om', IsWeilDatumO ψ V W (chrTh (tup μ ν) η j).1 (chrTh (tup μ ν) η j).2 om' → ∀ h g f, IsThetaFunO ψ V W f →
        om' (h, g) f = (nW g * (nV h)⁻¹) • om (h, g) f) ∧
    ∀ om₁, IsWeilDatumO ψ V W (chrTh μ η j).1 (chrTh μ η j).2 om₁ → ∀ p f, IsThetaFunO ψ V W f → om₁ p f = om p f := by
  rw [chrTh_tup]
  exact change_of_splitting_pair D ψ V W _ _ ν om ho hν hF

end GlobalTheory.SplitChange

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharOfLowerRightBlockDetEventuallyEqOneStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charOfLowerRightBlockDet_eventually_eq_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (χ : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar χ → ∃ U : Set (GL (Fin (r + t)) k), IsOpen U ∧ (1 : GL (Fin (r + t)) k) ∈ U ∧ ∀ g ∈ U, GlobalTheory.BlockType.blockChar χ g = 1 := by
  first | exact @GlobalTheory.BlockType.blockChar_eventually_one | exact GlobalTheory.BlockType.blockChar_eventually_one | (intros; apply GlobalTheory.BlockType.blockChar_eventually_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChosenPlacesAdmissibleGoodSetupStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chosenPlaces_admissible_goodSetup : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (ρ : Setup X), ρ.Good → ∀ (i : X.Tw) (j : Fin D.R.m) (b : Bool) (Q : Finset (Pl D.host.E)), (∀ P ∈ Q, Formalism.BasicNotions.IsSplitPl D.host P) → Disjoint Q (X.S0 i) → (ρ.B i j b).admitted (half (ρ.ch i) Q) := by
  first | exact @GlobalTheory.ChoiceAdm.adm_half_of_good_of_split_disjoint | exact GlobalTheory.ChoiceAdm.adm_half_of_good_of_split_disjoint | (intros; apply GlobalTheory.ChoiceAdm.adm_half_of_good_of_split_disjoint <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffPolynomialEqZeroOfVanishingOnGLFamilyStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries
open Formalism.IndefR.Links
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeffPolynomial_eq_zero_of_vanishing_on_GLFamily : ∀ (D : D7) (n : ℕ) (lam : D.what₂.Tau → DomWeight n) (F : Formalism.L2.DIV.Pol ℂ D.what₂.Tau n), (∀ x : GLR D n, coefFn (RingHom.id ℂ) lam F x = 0) → F = 0 := by
  first | exact @GlobalTheory.ExportSeries.eq_zero_of_coefFn_id_eq_zero | exact GlobalTheory.ExportSeries.eq_zero_of_coefFn_id_eq_zero | (intros; apply GlobalTheory.ExportSeries.eq_zero_of_coefFn_id_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompletionIsoSplitPlace
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TypeVecEig

theorem main : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D) (S : Reading P.T), IsTrue P S → ∀ (i : D.nd.Loc) (PI : D.naut.AV i) (k : Fin 2) (v : D.nd.PlG k) (s : SplitPlace D.host.E) (hw : IsSplitPl D.host s.w), s.w = D.naut.plGw k v → ∀ c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E, Continuous c → (∀ x : D.host.E, c (s.i x) = algebraMap D.host.E (s.w.adicCompletion D.host.E) x) → ∀ F ∈ D.naut.typeV i PI, ∀ x : GAf D.host.E D.R.nV, TrivOutside {s.v} x → Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x) ∈ GlobalTheory.BlockType.blockGrp (s.w.adicCompletion D.host.E) D.R.r D.R.t → NG.rt D.host.E D.R.nV x ((P.M.loc i).real F) = GlobalTheory.BlockType.blockChar (S i s.w hw).mu (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) • (P.M.loc i).real F := by
  intro hL D P S hT i PI k v s hw hsw c hcont hci F _hF x hx hh
  obtain ⟨j, hj⟩ : ∃ j : Fin D.R.m, j.1 + 1 = D.nd.j i :=
    ⟨⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩, by have := D.nd.j_range i; simp only; omega⟩
  obtain ⟨ψ₀, ξ, hψ, hξ, hlev⟩ := P.H.level.uni i j hj k v s hsw
  have hcv := GlobalTheory.SplitConjVal.valuation_eq s c hcont hci
  obtain ⟨h1, h2⟩ := GlobalTheory.BlockConj.facts_of_mem s D.R.r D.R.t c hcv (s.loc D.R.nV x) hh
  obtain ⟨i1, -⟩ := GlobalTheory.BlockConj.facts_of_mem s D.R.r D.R.t c hcv (s.loc D.R.nV x)⁻¹
    (by
      have := (GlobalTheory.BlockType.blockGrp _ _ _).inv_mem hh
      convert this using 1
      exact map_inv (Matrix.GeneralLinearGroup.map (n := Fin (D.R.r + D.R.t)) c.toRingHom) _)
  have huni : NG.UniRT s D.R.r (s.loc D.R.nV x) := by
    refine ⟨⟨GlobalTheory.BlockConj.mem_GLint_of (fun a b => ?_) (fun a b => ?_), fun a b ha hb => ?_⟩,
      fun a b ha hb => ⟨fun hlt => ?_, fun he => ?_⟩⟩
    · exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (h1 a b)
    · exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (i1 a b)
    · have := h2 a b hb
      split_ifs at this with e
      · rw [e] at ha; omega
      · rwa [sub_zero] at this
    · have := h2 a b hb
      split_ifs at this with e
      · rw [e] at hlt; omega
      · rwa [sub_zero] at this
    · subst he
      have := h2 a a ha
      split_ifs at this with e
      · exact this
      · exact absurd rfl e
  have hxJ : x ∈ (P.M.loc i).J := (hlev.mem x hx).2 huni
  have hTS : (P.M.loc i).real F ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ := by
    rw [← (P.M.loc i).real_range]; exact LinearMap.mem_range_self _ _
  have hrt := hTS.2 ⟨x, hxJ⟩
  let h : GL (Fin (D.R.r + D.R.t)) (s.w.adicCompletion D.host.E) :=
    Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)
  have hh' : h ∈ GlobalTheory.BlockType.blockGrp (s.w.adicCompletion D.host.E) D.R.r D.R.t := hh
  have hdet := GlobalTheory.BlockConjDet.val_det_mul_sub_one_lt hh'
  have hne2 : (h.val.submatrix (Fin.natAdd D.R.r) (Fin.natAdd D.R.r)).det ≠ 0 := by
    intro h0
    rw [h0, mul_zero, zero_sub, Valuation.map_neg, map_one] at hdet
    exact lt_irrefl _ hdet
  have hc_det : c (NG.detDD s D.R.r (s.loc D.R.nV x)) =
      (h.val.submatrix (Fin.natAdd D.R.r) (Fin.natAdd D.R.r)).det := by
    let e : Fin D.R.t ≃ {y : Fin D.R.nV // D.R.r ≤ y.val} :=
      { toFun := fun a => ⟨Fin.natAdd D.R.r a, by simp⟩
        invFun := fun y => ⟨y.1.val - D.R.r, by
          have h1 := y.1.2; have h2 := y.2; change y.1.val < D.R.r + D.R.t at h1; omega⟩
        left_inv := fun a => by ext; simp
        right_inv := fun y => by ext; simp; have := y.2; omega }
    rw [NG.detDD, ← Matrix.det_submatrix_equiv_self e]
    rw [show c _ = c.toRingHom _ from rfl, RingHom.map_det]
    congr 1
  have hF0 : NG.detDD s D.R.r (s.loc D.R.nV x) ≠ 0 := fun h0 => hne2 (by rw [← hc_det, h0, map_zero])
  let u := Units.mk0 _ hF0
  have hchr := hlev.chr x hxJ hx u rfl
  have hsup : ψ₀ (NG.supDiag s D.R.r (s.loc D.R.nV x)) = 1 := hψ.1 _ (by
    unfold NG.supDiag
    refine Valuation.map_sum_lt _ one_ne_zero fun p _ => Valuation.map_sum_lt _ one_ne_zero fun q _ => ?_
    split_ifs with h
    · have := h2 p q h.2
      split_ifs at this with e
      · rw [e] at h; omega
      · rwa [sub_zero] at this
    · rw [map_zero]; exact zero_lt_one)
  have hμ := hT.mu i s.w hw j hj
  have hξμ := GlobalTheory.ConjDense.eq_of_agree s c hcont hci (S i s.w hw).mu ξ hμ.1 hξ.1
    (fun k => by rw [hξ.2 k, hμ.2 k]) u
  have hbc : GlobalTheory.BlockType.blockChar (S i s.w hw).mu h =
      (((S i s.w hw).mu (Units.map c.toMonoidHom u) : ℂˣ) : ℂ) :=
    GlobalTheory.BlockType.blockChar_eq _ _ _ (by rw [← hc_det]; rfl)
  change _ = GlobalTheory.BlockType.blockChar (S i s.w hw).mu h • _
  rw [hbc, ← hξμ, hrt, hchr, hsup, one_mul]

end GlobalTheory.TypeVecEig

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComplexPrincipalLevelEqRealisationPrincipalLevelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.Lev Formalism.L2.DIV Formalism.IndefR.Mult
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complex_principal_level_eq_realisation_principal_level : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks) {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {ρ : Setup D.ntw}, RealPin Rl cG ρ → ∀ (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool), ρ.levK i j b = levG (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv) := by
  first | exact @GlobalTheory.SeriesTie.levK_eq_levG_triv | exact GlobalTheory.SeriesTie.levK_eq_levG_triv | (intros; apply GlobalTheory.SeriesTie.levK_eq_levG_triv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConductorRecCompatibleStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conductor_rec_compatible : DepthZeroCuspidalLL → DepthZeroInduction → LanglandsExhaustionGL → ZelevinskyPolynomialRing → GeometricLemma → BernsteinZelevinskyFiniteness → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion E) → WD h), IsRecLit h rc → ∀ x : IrrGL (w.adicCompletion E), fixed x.rep (KOne (w.adicCompletion E) (Fin x.1)) ≠ ⊥ ↔ IsTameWD (rc x) := by
  first | exact @GlobalTheory.LlcDepth.fixed_ne_bot_iff_isTameWD | exact GlobalTheory.LlcDepth.fixed_ne_bot_iff_isTameWD | (intros; apply GlobalTheory.LlcDepth.fixed_ne_bot_iff_isTameWD <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousRestrictScalarsHomMaximalRealSubfieldStatement
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.Pst
  GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_restrictScalarsHom_maximalRealSubfield : ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω],
    Continuous (AlgEquiv.restrictScalarsHom (maximalRealSubfield E) : G E Ω →* G (maximalRealSubfield E) Ω) := by
  first | exact @GlobalTheory.restrictScalarsHom_maximalRealSubfield_continuous | exact GlobalTheory.restrictScalarsHom_maximalRealSubfield_continuous | (intros; apply GlobalTheory.restrictScalarsHom_maximalRealSubfield_continuous <;> assumption)
end
end

