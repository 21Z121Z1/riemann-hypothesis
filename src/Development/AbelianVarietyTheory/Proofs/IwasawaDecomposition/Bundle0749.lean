import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0721
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTiedChoiceOfReads
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0810
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0424
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0385
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0338
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0722
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0436
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0440
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0438
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0682
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0031
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0728
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0730
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IsLinked
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AllRows
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0006
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0005
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0043
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0417
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0704
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0404
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0731

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
section
noncomputable section

namespace GlobalTheory.LevCmp

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

section Gen

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

def Eig {V : Type} [AddCommGroup V] [Module ℂ V] (F : GAf L n → V) (κ : GAf L n) (c : ℂ) : Prop := ∀ g, F (g * κ) = c • F g

def FrameAut (θ : GAf L n ≃* GAf L n) : Prop :=
  (∀ κ, θ κ ∈ Umax L n ↔ κ ∈ Umax L n) ∧ ∀ v κ, TrivOutside {v} (θ κ) ↔ TrivOutside {v} κ

def cx {K : Type} [Field K] (e : K →+* ℂ) {J : Subgroup (GAf L n)} (χ : J →* Kˣ) : J →* ℂˣ := (Units.map e.toMonoidHom).comp χ

theorem cx_apply {K : Type} [Field K] (e : K →+* ℂ) {J : Subgroup (GAf L n)} (χ : J →* Kˣ) (κ : J) :
    ((cx e χ κ : ℂˣ) : ℂ) = e (χ κ : Kˣ) := rfl

def LevEq (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (J' : Subgroup (GAf L n)) (χ' : J' →* ℂˣ) : Prop :=
  J = J' ∧ ∀ κ (h : κ ∈ J) (h' : κ ∈ J'), χ ⟨κ, h⟩ = χ' ⟨κ, h'⟩

def WtMatch {K : Type} [Field K] (e : K →+* ℂ) {W W' : Type} [AddCommGroup W] [Module K W] [AddCommGroup W'] [Module ℂ W']
    (ρ : Representation K (GQ L n) W) (ρ' : Representation ℂ (GQ L n) W') : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (b : Module.Basis ι K W) (b' : Module.Basis ι ℂ W'),
    ∀ γ, LinearMap.toMatrix b' b' (ρ' γ) = (LinearMap.toMatrix b b (ρ γ)).map e

example : FrameAut (MulEquiv.refl (GAf L n)) := ⟨fun _ => Iff.rfl, fun _ _ => Iff.rfl⟩

end Gen

variable {D : D7}

def SideRead (i : D.ntw.Tw) (b : Bool) (k : ℕ) (e : NX.Kk D i k →+* ℂ) : Prop :=
  ∀ x : ↥D.LL0, e (NX.toKk D i k (GlobalTheory.SeriesTie.sideEmb D.ntw i b x)) = embLL0 D x

def ReadsHecke {i : D.ntw.Tw} {k : ℕ} (e : NX.Kk D i k →+* ℂ) (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (χ : HChar D.host.E) : Prop :=
  ∃ art : Ideles D.host.E →* Gab D.host.E D.nd.Om, IsGlobalArtin art ∧
    GlobalTheory.GalToHecke.IsHeckeOf art ((Units.map (e.comp (NX.ofOk D i k)).toMonoidHom).comp ψ) χ

variable (D) in

def GalOf (χ : HChar D.host.E) (ψ₀ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ) : Prop :=
  IsOpen (ψ₀.ker : Set (G D.host.E D.nd.Om)) ∧ ∃ art : Ideles D.host.E →* Gab D.host.E D.nd.Om, IsGlobalArtin art ∧
    GlobalTheory.GalToHecke.IsHeckeOf art ((Units.map D.what₂.embLL.toMonoidHom).comp ψ₀) χ

variable (D) in

def GPlaces : Prop :=
  (∀ k v, D.naut.plGw k v ∈ placesOver D.host.E (D.host.g k) ∧ ∃ s : SplitPlace D.host.E, s.w = D.naut.plGw k v) ∧
    (∀ u ∈ gPl D, ∃ (k : Fin 2) (v : D.nd.PlG k) (s : SplitPlace D.host.E), s.v = u ∧ s.w = D.naut.plGw k v) ∧
    ∃ k, Nonempty (D.nd.PlG k)

variable (D) in

def ParaShape (η : HChar D.host.E) (J : Subgroup (GAf D.host.E D.R.nV)) (χ : J →* ℂˣ) : Prop :=
  ∀ v ∈ qPl D η, ∃ (s : SplitPlace D.host.E) (ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ), s.v = v ∧
    NG.IsCompAt η s ξ ∧ NG.LevelPara J χ s D.R.r ξ

variable (D) in

def GrpShape (η : HChar D.host.E) (J : Subgroup (GAf D.host.E D.R.nV)) : Prop :=
  NG.IsProdLevel J ∧
    (∀ v ∈ qPl D η, ∃ s : SplitPlace D.host.E, s.v = v ∧ ∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ NG.ParaRT s D.R.r (s.loc _ κ))) ∧
    (∀ k v (s : SplitPlace D.host.E), s.w = D.naut.plGw k v →
      ∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ NG.UniRT s D.R.r (s.loc _ κ))) ∧
    ∀ κ, TrivOutside (gPl D ∪ qPl D η)ᶜ κ → (κ ∈ J ↔ κ ∈ Umax D.host.E D.R.nV)

abbrev cell (X : NExpTied D) {i : D.ntw.Tw} (b : Bool) {k : ℕ} {Q : Finset (PlE D.host)}
    {ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ} (hA : NX.AdmTw D i k Q ψ) (j : Fin D.R.m) :=
  X.mtV i (j.1 + 1) b k Q ψ (by omega) (by omega) hA

abbrev eta (cf : CharFrame D) (xi : D.what₂.Tup → HChar D.host.E) (v : D.what₂.places.Pl) (j : Fin D.R.m) : HChar D.host.E :=
  cf.mu0 j * xi (D.what₂.muTw v)

abbrev mtAt (M : MtFam D) (v : D.what₂.places.Pl) (j : Fin D.R.m) : MtReal D (D.what₂.muTw v) (j.1 + 1) :=
  M (D.what₂.muTw v) (j.1 + 1) (by omega) (by omega)

def CellWt {μ : D.what₂.Tup} {j' : ℕ} (m : MtReal D μ j') (X : NExpTied D) {i : D.ntw.Tw} (b : Bool) {k : ℕ}
    {Q : Finset (PlE D.host)} {ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ} (hA : NX.AdmTw D i k Q ψ) (j : Fin D.R.m)
    (e : NX.Kk D i k →+* ℂ) : Prop := WtMatch e (cell X b hA j).ρ m.wt.ρ

def Joint (η : HChar D.host.E) {μ : D.what₂.Tup} {j' : ℕ} (m : MtReal D μ j') (X : NExpTied D) {i : D.ntw.Tw} (b : Bool) {k : ℕ}
    {Q : Finset (PlE D.host)} {ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ} (hA : NX.AdmTw D i k Q ψ) (j : Fin D.R.m) : Prop :=
  ∃ (θ : GAf D.host.E D.R.nV ≃* GAf D.host.E D.R.nV) (J₁ : Subgroup (GAf D.host.E D.R.nV)) (e : NX.Kk D i k →+* ℂ)
    (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (ω : (cell X b hA j).W →ₛₗ[e] V),
    FrameAut θ ∧ SideRead i b k e ∧ Function.Injective ω ∧
    (∀ v ∈ qPl D η, ∃ s : SplitPlace D.host.E, s.v = v ∧ ∀ κ, TrivOutside {s.v} κ → NG.ParaRT s D.R.r (s.loc _ κ) → κ ∈ J₁) ∧
    (∀ kk v (s : SplitPlace D.host.E), s.w = D.naut.plGw kk v →
      ∀ κ, TrivOutside {s.v} κ → NG.UniRT s D.R.r (s.loc _ κ) → κ ∈ J₁) ∧
    ∀ κ ∈ J₁, ∃ c c' : ℂ, (∀ x, Eig (m.real x) (θ κ) c) ∧ (∀ f, Eig (fun g => ω (((cell X b hA j).real f).1 g)) (θ κ) c') ∧
      ∀ kk v (s : SplitPlace D.host.E), s.w = D.naut.plGw kk v → TrivOutside {s.v} κ →
        c ^ (D.host.g kk - 1) = c' ^ (D.host.g kk - 1)

end GlobalTheory.LevCmp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowDepthOfPrimitive
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RowDepthTrue

set_option maxHeartbeats 1000000 in

theorem rowDepth_rowRepR : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → HostHyp D → D.host.F = maximalRealSubfield D.host.E →
    GlobalTheory.HeightCounting.RowDepth D (fun σ => principalLevelFrame.rowRepR R.θ (Y.eFT σ)) := by
  intro hHC hCR D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH hHo hF σ k v
  obtain ⟨s, hs⟩ := GlobalTheory.FixedPlaceOverType.exists_splitPlace_w_plGw D k v
  obtain ⟨τ, hτ⟩ := GlobalTheory.RowLocalRows2.finTyp_rows_exists_isLocS hHC hCR D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH hHo hF σ s
  have hβ := hP.char.base.lev.βY 0 Y.hm
  obtain ⟨h, hA⟩ := GlobalTheory.RowLevelSplit.lemA_pf
    (GlobalTheory.RowLevelSplit.stdFrame_splitPlace_entries_off_place GlobalTheory.FrameOffPlace.cpt_conj_finE_eq_one GlobalTheory.ConjLt.frame_mat_sub_one_lt GlobalTheory.SplitFrameW.main
      GlobalTheory.PlaceOverSplit.eq_or_eq_cP) D (Yc D 0) D.R.r Y.hF Y.PY (R.βY 0) _ _ Y.stdPsi.1 hβ s
  have hh : ∀ (b : Bool) (κ : Formalism.AUTREP.GAf D.host.E D.R.r), TrivOutside {s.v} κ →
      h⁻¹ * s.loc D.R.r κ * h ∈ GlobalTheory.SplitWeil.KOne (s.v.adicCompletion (maximalRealSubfield D.host.E)) (Fin D.R.r) →
      Y.PY.ψ κ ∈ levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b)) ∧
        levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b)) (Y.PY.ψ κ) = 1 := by
    intro b κ hκ hk
    classical
    exact GlobalTheory.RowLevelSplit.lemB_pf D (Yc D 0) (R.βY 0) _ (_ ∪ _) (Y.PY.ψ κ) Finset.subset_union_left
      Finset.subset_union_right (Y.PY.into κ) (hA κ hκ hk _)
  obtain ⟨f, hfS, hf0, hfix⟩ := GlobalTheory.RowFix.exists_fixed_rowRep D (Yc D 0) D.R.r _ R.θ Y.PY (R.MY 0) _ _ _ (Y.eFT σ)
    (fun κ => TrivOutside {s.v} κ ∧
      h⁻¹ * s.loc D.R.r κ * h ∈ GlobalTheory.SplitWeil.KOne (s.v.adicCompletion (maximalRealSubfield D.host.E)) (Fin D.R.r))
    (fun b κ hκ => hh b κ hκ.1 hκ.2)
  exact ⟨s, τ, hs, hτ, GlobalTheory.RowLevelSplitData.fixed_ne_bot_of_fixed_vector_conj D.host.E D.R.r _ s τ h hτ f hfS hf0
    (fun κ h1 h2 => hfix κ ⟨h1, h2⟩)⟩

open GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up in
open GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl in

theorem stepW_of_ev {Q : Ctx → Prop} (h : Ev Q) (p : WP) : StepW p fun K _ _ _ _ => Q K :=
  Step.of_evG ((evG_of_ev h).imp fun _ _ _ _ _ H _ _ _ _ _ _ _ _ _ => H)

open GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up in
set_option maxHeartbeats 2000000 in

theorem rowDepth_allSt : PrN → AllSt fun _ _ _ _ _ _ x => RowDepth (Dof x) (repOf x.r.Y) := by
  intro hPr
  have hId : StepW Start Start := StepW.of_all fun _ _ _ _ _ _ _ h => h
  refine (hId.and (GlobalTheory.RowDepthTrue.stepW_of_ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev Start)).trans
    (StepW.of_all fun K B f T w hO _ H => ?_)
  intro P x
  obtain ⟨hHo, hF, -⟩ := H.2 (w.st x.o.Z) hO
  exact rowDepth_rowRepR hPr.hc hPr.decay _ _ _ _ _ _ _ _ _ _ _ _ x.m.z.pins x.m.intersectionNumber_baseChange hHo hF

attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM in
set_option maxHeartbeats 1000000 in

theorem typeLab_rowRepR : GlobalTheory.GLq.Green → GlobalTheory.Published.ZelevinskyPolynomialRing → GlobalTheory.Published.DepthZeroInertia →
    GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → HostHyp D → D.host.F = maximalRealSubfield D.host.E →
    ∀ (Tw : GlobalTheory.RowTie.WDTie D.nd D.naut) (Rw : GlobalTheory.HeightCounting.RowSide D) (Ld : ∀ k, GlobalTheory.GLq.LabelDatum (D.host.g k)),
    GlobalTheory.HeightCounting.LabTrue D Tw →
    GlobalTheory.HeightCounting.RowTrue hL D (fun σ => principalLevelFrame.rowRepR R.θ (Y.eFT σ)) (fun σ w => Tw.e w (Rw.locR σ w)) Rw.satR →
    GlobalTheory.SerSys.LabTie D Ld →
    (∀ k v, ∃ κ : IsLocalRing.ResidueField (D.nd.plOm.1 (D.naut.plGw k v)) ≃+* Formalism.CyclotomicNorms.Fbar (D.host.g k),
      Formalism.L2.NT.TameCoupled (D.nd.plOm.1 (D.naut.plGw k v)) κ (D.ntypes.tg k v) (Ld k).gen) →
    GlobalTheory.LabPin.TypeLab D (fun σ => principalLevelFrame.rowRepR R.θ (Y.eFT σ)) := by
  intro hG hZ hDZ hHC hCR hL D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH hHo hF Tw Rw Ld hLab hRow hTie hTame
  exact GlobalTheory.LabPin.typeLab_of_local hG hZ hDZ hL D Tw Rw _ Ld hLab hRow
    (rowDepth_rowRepR hHC hCR D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH hHo hF) hTie hTame

end GlobalTheory.RowDepthTrue

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SameTwistOfOneField
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

theorem GlobalTheory.CommonReading.norm_aut {l : ℕ} [Fact l.Prime] (τ : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) (x : PadicAlgCl l) :
    ‖τ x‖ = ‖x‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq]
  exact (spectralNorm_eq_of_equiv τ x).symm

theorem GlobalTheory.CommonReading.norm_aut_le {l : ℕ} [Fact l.Prime] (τ : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l)
    (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (x : Formalism.L2.TwC.intOf l K) : ‖τ x‖ ≤ 1 := by
  rw [GlobalTheory.CommonReading.norm_aut, ← PadicAlgCl.valuation_coe]
  exact_mod_cast x.2.2

namespace GlobalTheory.HeightCounting.SameTw

def Reads (D : D7) (C : NChoice D) (w : D.what₂.places.Pl) {Λ : Type} [Field Λ] (e : D.what₂.LL →+* Λ)
    (φ : D.ntw.O0 (C.twI w) →+* Λ) : Prop :=
  ∃ (Ω : Type) (_ : Field Ω) (τ : Λ →+* Ω) (ι : FractionRing (C.Oe w) →+* Ω),
    (∀ y, τ (φ y) = ι (algebraMap (C.Oe w) (FractionRing (C.Oe w)) (algebraMap (D.ntw.Ok (C.twI w) (C.k' w)) (C.Oe w)
      (BlochKatoReduction.Gen.phiK D.ntw (C.twI w) (C.k' w) y)))) ∧
    ∀ x : D.what₂.LL, τ (e x) = ι (C.embW w x)

theorem exists_reads (D : D7) (C : NChoice D) (F : TwFrameC D) {low : Finset ℕ} (hF : TwistFrameLowIndexCompatibility D F low) (w : D.what₂.places.Pl)
    (l : ℕ) [Fact l.Prime] (hl : D.ntw.l (C.twI w) = l) (e : D.what₂.LL →+* PadicAlgCl l)
    (he : ∀ x, 0 ≤ D.what₂.places.val w x ↔ ‖e x‖ ≤ 1) :
    ∃ φ : D.ntw.O0 (C.twI w) →+* PadicAlgCl l, Reads D C w e φ ∧ (∀ y, ‖φ y‖ ≤ 1) ∧
      (∃ K : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] K ∧ ∀ y, φ y ∈ K) ∧
      ∀ (z : ℤ_[D.ntw.l (C.twI w)]) (z' : ℤ_[l]), HEq z z' →
        φ (algebraMap _ (D.ntw.O0 (C.twI w)) z) = algebraMap ℚ_[l] (PadicAlgCl l) (z' : ℚ_[l]) := by
  subst hl
  haveI := C.Oe_fin w
  obtain ⟨σ, ι, h1, h2⟩ := GlobalTheory.CommonReading.exists_common (C.Oe_inj w)
    ((Subring.subtype _).comp (F.eOk (C.twI w) (C.k' w)).toRingHom)
    (Subtype.val_injective.comp (F.eOk (C.twI w) (C.k' w)).injective)
    (fun y => (F.eOk (C.twI w) (C.k' w) y).2.2) (C.embW w) e fun x => (C.embW_w w x).symm.trans (he x)
  refine ⟨σ.symm.toAlgHom.toRingHom.comp ((Subring.subtype _).comp (F.eO0 (C.twI w)).toRingHom),
    ⟨ℂ_[D.ntw.l (C.twI w)], inferInstance, (algebraMap (PadicAlgCl (D.ntw.l (C.twI w))) ℂ_[D.ntw.l (C.twI w)]).comp
      σ.toAlgHom.toRingHom, ι, fun y => ?_,
      fun x => (h2 x).symm⟩, fun y => ?_, ⟨(F.K0 (C.twI w)).1.map σ.symm.toAlgHom, ?_, fun y => ⟨_, (F.eO0 (C.twI w) y).2.1, rfl⟩⟩, ?_⟩
  · rw [h1]
    refine Eq.trans ?_ ((hF.eOk_alg _ _ _).trans (hF.eO_alg _ y)).symm
    simp
  · exact GlobalTheory.CommonReading.norm_aut_le σ.symm _ (F.eO0 (C.twI w) y)
  · haveI := (F.K0 (C.twI w)).2
    exact LinearEquiv.finiteDimensional (IntermediateField.equivMap _ σ.symm.toAlgHom).toLinearEquiv
  · rintro z _ ⟨⟩
    change σ.symm (F.eO0 (C.twI w) _ : PadicAlgCl _) = _
    rw [hF.ringSpec_baseIntegersEquiv_algebraMap, AlgEquiv.commutes]

theorem Reads.emb {D : D7} {C : NChoice D} (hC : ChoiceC D C) {w : D.what₂.places.Pl} (hw : TwistedAt D w) {Λ : Type} [Field Λ]
    {e : D.what₂.LL →+* Λ} {φ : D.ntw.O0 (C.twI w) →+* Λ} (h : Reads D C w e φ) (x : D.LL0) (y : D.ntw.O0 (C.twI w))
    (hy : algebraMap _ (FractionRing (D.ntw.O0 (C.twI w))) y =
      (if C.sd w then D.ntw.emb0 (C.twI w) else D.ntw.emb0b (C.twI w)) x) : e x = φ y := by
  obtain ⟨Ω, _, τ, ι, h1, h2⟩ := h
  apply τ.injective
  rw [h1, h2, hC.emb_side w hw x]
  have : (if C.sd w then D.ntw.emb0 (C.twI w) x else D.ntw.emb0b (C.twI w) x) =
      algebraMap _ (FractionRing (D.ntw.O0 (C.twI w))) y := by
    rw [hy]; split_ifs <;> rfl
  rw [this, fracOe, IsFractionRing.map, IsLocalization.map_eq]
  rfl

theorem Reads.of_comp {D : D7} {C : NChoice D} {w : D.what₂.places.Pl} {Λ Λ' : Type} [Field Λ] [Field Λ'] (q : Λ →+* Λ')
    {e : D.what₂.LL →+* Λ} {φ : D.ntw.O0 (C.twI w) →+* Λ} (h : Reads D C w (q.comp e) (q.comp φ)) : Reads D C w e φ :=
  let ⟨Ω, i, τ, ι, h1, h2⟩ := h
  ⟨Ω, i, τ.comp q, ι, h1, h2⟩

def OneField (D : D7) (C : NChoice D) : Prop :=
  ∀ a : D.nd.Loc, ∃ f : D.ntw.O0 (C.twI (D.nd.w a)) →+* D.nd.O a, HEq f (D.ntw.twist₂ a) ∧
    Reads D C (D.nd.w a) (D.nd.embK a) ((algebraMap (D.nd.O a) (FractionRing (D.nd.O a))).comp f)

def TwReads {D : D7} (C : NChoice D) (X : LocNd (lay0 D)) (T : LocTw X) : Prop :=
  ∀ a : X.nd.Loc, ∃ f : D.ntw.O0 (C.twI (X.nd.w a)) →+* X.nd.O a, HEq f (T.twist₂ a) ∧
    Reads D C (X.nd.w a) (X.nd.embK a) ((algebraMap (X.nd.O a) (FractionRing (X.nd.O a))).comp f)

set_option maxHeartbeats 2000000 in

theorem oneField_withLoc {D : D7} (L : LocAll (lay0 D)) (C : NChoice D) :
    OneField (withLoc L) (chL L C) ↔ TwReads C L.X L.T := Iff.rfl

theorem sameChar_of_inj {O₀ O₁ O₂ Γ Ω : Type} [CommRing O₀] [CommRing O₁] [CommRing O₂] [Group Γ] [CommRing Ω]
    (f₁ : O₀ →+* O₁) (f₂ : O₀ →+* O₂) (ψ₁ : Γ →* O₁ˣ) (ψ₂ : Γ →* O₂ˣ) (j₁ : O₁ →+* Ω) (j₂ : O₂ →+* Ω)
    (h₁ : Function.Injective j₁) (h₂ : Function.Injective j₂) (hf : ∀ y, j₁ (f₁ y) = j₂ (f₂ y))
    (hψ : ∀ g, j₁ (ψ₁ g : O₁ˣ) = j₂ (ψ₂ g : O₂ˣ)) : GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.SameChar f₁ f₂ ψ₁ ψ₂ := by
  intro F
  rw [← map_eq_zero_iff j₁ h₁, ← map_eq_zero_iff j₂ h₂]
  simp only [Finsupp.sum, map_sum, map_mul, hf, hψ]

theorem sameTwist_of_oneField (D : D7) (C : NChoice D) (hT : NChTie D C) (h : OneField D C) : GlobalTheory.PtCore.SameTwist D C := by
  intro a
  obtain ⟨f, hf, Ω, _, ιA, ιB, h1, h2⟩ := h a
  obtain ⟨ψ0, -, hw, hl⟩ := hT.psi_eq
  refine (GlobalTheory.PtCore.sameTwistAt_iff D a _ _ _).2 ⟨hT.twOf_eq a, f, hf, ?_⟩
  refine sameChar_of_inj _ _ _ _ (ιA.comp (algebraMap (D.nd.O a) (FractionRing (D.nd.O a))))
    (ιB.comp ((algebraMap (C.Oe (D.nd.w a)) (FractionRing (C.Oe (D.nd.w a)))).comp
      (algebraMap (D.ntw.Ok (C.twI (D.nd.w a)) (C.k' (D.nd.w a))) (C.Oe (D.nd.w a)))))
    (ιA.injective.comp (IsFractionRing.injective _ _))
    (ιB.injective.comp ((IsFractionRing.injective (C.Oe (D.nd.w a)) _).comp (C.Oe_inj _))) h1 fun g => ?_
  have := h2 ((ψ0 (D.nd.w a) g : (D.what₂.LL)ˣ) : D.what₂.LL)
  rw [hl, hw] at this
  exact this

end GlobalTheory.HeightCounting.SameTw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchubGamApply
section
noncomputable section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric
open Classical

namespace GlobalTheory.Schubert

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def flagRoot {H : Host E} (Dw : Datum H) (x : Root Dw.mult) :
    MvPolynomial (GlobalTheory.AllWt.Psi H × Fin (Dw.p + Dw.q)) ℝ :=
  if h : x.1 (H.rt : E) = H.rt0 then
    X (⟨x.1, h⟩, ⟨x.2, by have h1 : (x.2 : ℕ) < Dw.mult x.1 := x.2.2; have h2 := GlobalTheory.PointChern.mult_of_mem Dw h; omega⟩)
  else
    -X (⟨conjEmb x.1, GlobalTheory.AllWt.conj_mem h⟩,
      ⟨Dw.p + (Dw.q - 1 - x.2), by have h1 : (x.2 : ℕ) < Dw.mult x.1 := x.2.2; have h2 := GlobalTheory.PointChern.mult_of_not_mem Dw h; omega⟩)

def flagMap {H : Host E} (Dw : Datum H) :
    MvPolynomial (Root Dw.mult) ℝ →ₐ[ℝ] MvPolynomial (GlobalTheory.AllWt.Psi H × Fin (Dw.p + Dw.q)) ℝ :=
  aeval (flagRoot Dw)

def flagLin (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) : MvPolynomial (ι × Fin N) ℝ →ₗ[ℝ] ℝ :=
  ((-1 : ℝ) ^ Formalism.DegreeFormula.dimFl ι N) • ∑ σ : ι → Equiv.Perm (Fin N),
    (∏ τ, ((Equiv.Perm.sign (σ τ) : ℤ) : ℝ)) • lcoeff ℝ (Formalism.DegreeFormula.permExp σ)

theorem flagLin_apply (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (P : MvPolynomial (ι × Fin N) ℝ) :
    flagLin ι N P = Formalism.DegreeFormula.degFl ι N P := by
  simp [flagLin, Formalism.DegreeFormula.degFl, LinearMap.sum_apply, smul_eq_mul, Finset.mul_sum]

def schubGam {H : Host E} (Dw : Datum H) : MvPolynomial ((E →+* ℂ) × ℕ) ℝ →ₗ[ℝ] ℝ :=
  flagLin (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q) ∘ₗ (flagMap Dw).toLinearMap ∘ₗ
    LinearMap.mulRight ℝ (fibrePoint Dw.mult) ∘ₗ (chernRoots Dw.mult).toLinearMap

theorem schubGam_apply {H : Host E} (Dw : Datum H) (P : MvPolynomial ((E →+* ℂ) × ℕ) ℝ) :
    schubGam Dw P = Formalism.DegreeFormula.degFl (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q)
      (flagMap Dw (chernRoots Dw.mult P * fibrePoint Dw.mult)) := by
  simp [schubGam, flagLin_apply]

def admitted (H : Host E) (Dw : Datum H) (Θ : MvPolynomial ((E →+* ℂ) × ℕ) ℝ →ₗ[ℝ] ℝ) : Prop :=
  (∀ (τ : GlobalTheory.AllWt.Psi H) (k : ℕ), 1 ≤ k → ∀ P, Θ (GlobalTheory.PointChern.relPoly τ k * P) = 0) ∧
  (∀ (τ : E →+* ℂ) (P : MvPolynomial ((E →+* ℂ) × ℕ) ℝ), Θ ((X (τ, 0) - 1) * P) = 0) ∧
  (∀ (τ : E →+* ℂ) (k : ℕ), Dw.mult τ < k → ∀ P : MvPolynomial ((E →+* ℂ) × ℕ) ℝ, Θ (X (τ, k) * P) = 0) ∧
  (∀ d : (E →+* ℂ) × ℕ →₀ ℕ, (d.sum fun x i => x.2 * i) ≠ Fintype.card (GlobalTheory.AllWt.Psi H) * (Dw.p * Dw.q) →
    Θ (monomial d 1) = 0)

end GlobalTheory.Schubert
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SelectedLowerMapHoldsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw

open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem.R3

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selected_lower_map_holds : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.NT.RayField → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (Γ : GeoP) (p : Prm hL), p = prmR N SExt.none Γ → (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (NEb hL K B f T w Z Wt p0 t nch n xd c)) → ∀ (K : Ctx) (q : WPt p.s K), (∀ X : GlobalTheory.Mem.Stages, K.Over X.B.toPre → HostHyp X.toD7 ∧ X.toD7.host.F = maximalRealSubfield X.toD7.host.E ∧ (∀ i, IsFDiag (Wc X.toD7 i) ∧ IsFDiag (Vc X.toD7 i)) ∧ (∀ i, (Vc X.toD7 i).IsPosDef) ∧ (∀ j, Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.Y j) ∧ Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.V j) ∧ (1 ≤ j → j ≤ X.toD7.R.m → Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.W j))) ∧ Formalism.IndefR.Seed.FrmC.StdLat X.toD7.sp.X' ∧ (∀ i, (∀ a b, (Vc X.toD7 i).hT ((Vc X.toD7 i).frame a) ((Vc X.toD7 i).frame b) = if a = b then 1 else 0) ∧ (Vc X.toD7 i).L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range (Vc X.toD7 i).frame)) ∧ ((∀ a b, X.toD7.sp.X'.hT (X.toD7.sp.X'.frame a) (X.toD7.sp.X'.frame b) = if a = b then 1 else 0) ∧ X.toD7.sp.X'.L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range X.toD7.sp.X'.frame))) → GlobalTheory.CuspMult.MultEq q.x.what₂.r.z.R.toRealDat → ∀ (R : Formalism.L2.RecT q.O.ex), RecPinE q R → ∀ (sP : GlobalTheory.Mem.SRe.SPack (q.w.D q.Z) fun u => (R.T.cols.forms u).to0) (sS : GlobalTheory.Mem.SRe.SRest sP), HEq sP q.sat.P → HEq sS q.sat.S → ∀ (a : TwArgs q.O.ex q.x.what₂) (x : TwIn q.O.ex), HEq a.x x → Formalism.L2.Rows.RowSideDetermined R.T (divisionPairOfAdelicFormsFaceColumnsData x) := by
  first | exact @GlobalTheory.Mem.R3.SelRowPin.selected_lower_map_third_stage | exact GlobalTheory.Mem.R3.SelRowPin.selected_lower_map_third_stage | (intros; apply GlobalTheory.Mem.R3.SelRowPin.selected_lower_map_third_stage <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SelectedRealizationGeometricStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw

open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem.R3

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selected_realization_geometric : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.NT.RayField → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (Γ : GeoP) (p : Prm hL), p = prmR N SExt.none Γ → (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (NEb hL K B f T w Z Wt p0 t nch n xd c)) → ∀ (K : Ctx) (q : WPt p.s K), (∀ X : GlobalTheory.Mem.Stages, K.Over X.B.toPre → HostHyp X.toD7 ∧ X.toD7.host.F = maximalRealSubfield X.toD7.host.E ∧ (∀ i, IsFDiag (Wc X.toD7 i) ∧ IsFDiag (Vc X.toD7 i)) ∧ (∀ i, (Vc X.toD7 i).IsPosDef) ∧ (∀ j, Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.Y j) ∧ Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.V j) ∧ (1 ≤ j → j ≤ X.toD7.R.m → Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.W j))) ∧ Formalism.IndefR.Seed.FrmC.StdLat X.toD7.sp.X' ∧ (∀ i, (∀ a b, (Vc X.toD7 i).hT ((Vc X.toD7 i).frame a) ((Vc X.toD7 i).frame b) = if a = b then 1 else 0) ∧ (Vc X.toD7 i).L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range (Vc X.toD7 i).frame)) ∧ ((∀ a b, X.toD7.sp.X'.hT (X.toD7.sp.X'.frame a) (X.toD7.sp.X'.frame b) = if a = b then 1 else 0) ∧ X.toD7.sp.X'.L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range X.toD7.sp.X'.frame))) → GlobalTheory.CuspMult.MultEq q.x.what₂.r.z.R.toRealDat → ∀ (R : Formalism.L2.RecT q.O.ex), RecPinE q R → ∀ (sP : GlobalTheory.Mem.SRe.SPack (q.w.D q.Z) fun u => (R.T.cols.forms u).to0) (sS : GlobalTheory.Mem.SRe.SRest sP), HEq sP q.sat.P → HEq sS q.sat.S → ∀ (a : TwArgs q.O.ex q.x.what₂) (x : TwIn q.O.ex), HEq a.x x → ∀ (hin : ∀ u, Formalism.L2.SG.PoincareInHH.PoincareSetting.InHH (sS.toSTiesR R).X u (sS.toSTiesR R).Y.hK), HEq (x.F.Sp (zsOf x.R x.F)) (Formalism.IndefR.Cx.spOf (X := (sS.toSTiesR R).X) (twAt (q.w.D q.Z).what₂.embLL x.A3.A.v0) (x.F.Dc (zsOf x.R x.F)) (sS.toSTiesR R).Y.hK (sS.toSTiesR R).G x.wd (fun m => pwOf (sS.toSTiesR R) hin (x.wd m)) x.bR) → ∀ (κ : ℝ) (sEEc : Tw (twAt (q.w.D q.Z).what₂.embLL x.A3.A.v0) x.R.HE.H →ₗ⋆[ℂ] Tw (twAt (q.w.D q.Z).what₂.embLL x.A3.A.v0) (Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX (sS.toSTiesR R).X)), HEq x.sEE sEEc → 0 < κ → (∀ (v : Tw (twAt (q.w.D q.Z).what₂.embLL x.A3.A.v0) x.R.HE.H) (hx : x.R.HE.e (Tw.out v) ∈ (x.R.toRealDat.EEat (x.R.toRealDat.levR x.F.lv2 true))), sEEc v = Tw.mk (twAt (q.w.D q.Z).what₂.embLL x.A3.A.v0) (((1 : ℂ) * (κ : ℂ)) • (Formalism.IndefR.AutomorphicEvaluation.sEEofTT (x.R.MY 0) x.R.ν0 x.R.fd0 (x.R.toRealDat.EEat (x.R.toRealDat.levR x.F.lv2 true)) (sS.toSTiesR R).X (sS.toSTiesR R).G (Formalism.L2.SG.RowsJoinPinned.iotaX sP.X sP.inst).toMulEquiv q.sat.t q.sat.c) ⟨x.R.HE.e (Tw.out v), hx⟩) ∧ RealDat.nP x.F.lv2 true * ‖sEEc v‖ ^ 2 = ‖v‖ ^ 2) → ∃ y : RealIn x R (sS.toSTiesR R), HEq y.tS q.sat.t ∧ y.cS = q.sat.c ∧ HEq y.Sx (Formalism.IndefR.NX.ratDatR (D := (q.w.st q.Z).toD7) q.x.what₂.r.z.R q.x.what₂.r.z.cG q.core.row.kKs q.core.row.hk) ∧ HEq y.nexp.eF q.core.row.nexp.eF ∧ HEq y.nexp.fi q.core.row.nexp.fi ∧ y.uS = 1 := by
  first | exact @GlobalTheory.Mem.R3.SelRealIn.realIn_exists | exact GlobalTheory.Mem.R3.SelRealIn.realIn_exists | (intros; apply GlobalTheory.Mem.R3.SelRealIn.realIn_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SelectedSideRealizationHoldsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw

open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem.R3

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selected_side_realization_holds : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.NT.RayField → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (Γ : GeoP) (p : Prm hL), p = prmR N SExt.none Γ → (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (NEb hL K B f T w Z Wt p0 t nch n xd c)) → ∀ (K : Ctx) (q : WPt p.s K), (∀ X : GlobalTheory.Mem.Stages, K.Over X.B.toPre → HostHyp X.toD7 ∧ X.toD7.host.F = maximalRealSubfield X.toD7.host.E ∧ (∀ i, IsFDiag (Wc X.toD7 i) ∧ IsFDiag (Vc X.toD7 i)) ∧ (∀ i, (Vc X.toD7 i).IsPosDef) ∧ (∀ j, Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.Y j) ∧ Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.V j) ∧ (1 ≤ j → j ≤ X.toD7.R.m → Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.W j))) ∧ Formalism.IndefR.Seed.FrmC.StdLat X.toD7.sp.X' ∧ (∀ i, (∀ a b, (Vc X.toD7 i).hT ((Vc X.toD7 i).frame a) ((Vc X.toD7 i).frame b) = if a = b then 1 else 0) ∧ (Vc X.toD7 i).L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range (Vc X.toD7 i).frame)) ∧ ((∀ a b, X.toD7.sp.X'.hT (X.toD7.sp.X'.frame a) (X.toD7.sp.X'.frame b) = if a = b then 1 else 0) ∧ X.toD7.sp.X'.L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range X.toD7.sp.X'.frame))) → GlobalTheory.CuspMult.MultEq q.x.what₂.r.z.R.toRealDat → ∀ (R : Formalism.L2.RecT q.O.ex), RecPinE q R → ∀ (sP : GlobalTheory.Mem.SRe.SPack (q.w.D q.Z) fun u => (R.T.cols.forms u).to0) (sS : GlobalTheory.Mem.SRe.SRest sP), HEq sP q.sat.P → HEq sS q.sat.S → ∀ (a : TwArgs q.O.ex q.x.what₂) (x : TwIn q.O.ex), HEq a.x x → ∀ (y : RealIn x R (sS.toSTiesR R)) (r : RecIn y) (HD : Formalism.L2.HostDatumC R.T.toTiedDataS), HD.d3b = q.x.pin.d3b → Formalism.L2.SelSideRT R (divisionPairOfAdelicFormsFaceColumnsData x) (realTOf y) (realRecOf r) HD q.core.a.Pq := by
  first | exact @GlobalTheory.Mem.R3.SelSideW.selected_side_realization | exact GlobalTheory.Mem.R3.SelSideW.selected_side_realization | (intros; apply GlobalTheory.Mem.R3.SelSideW.selected_side_realization <;> assumption)
end

