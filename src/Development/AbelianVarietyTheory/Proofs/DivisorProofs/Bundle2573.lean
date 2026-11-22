import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2459
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2291
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2458
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2295
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2520
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0074
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2460
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2209
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2213
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0044
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0074
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2229
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1719
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0288
import Development.AbelianVarietyTheory.Definitions.Divisors.DiagValExtTraceNonneg
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0704

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexPointsComponentSamePeriodSpaceStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexPoints_component_same_periodSpace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : (Xo.XF c).Opens) (e : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (e.comp (IntermediateField.inclusion c.le).toRingHom) ty) (i i' : Fin Fu.n) (P : (Fu.Di i).La →+ (Fin g → ℂ)) (P' : (Fu.Di i').La →+ (Fin g → ℂ)) (y y' : Sp ℂ ⟶ Xo.XF c) (B : GlobalTheory.ProjVar.Var c.F) (io : B.X ⟶ gen Y), IsClosed (U : Set (Xo.XF c)) → IsOpenImmersion io → Set.range io = compactOf Y U → io ≫ genStr Y = B.str → y ≫ toF Xo c = spMap e → y' ≫ toF Xo c = spMap e → Set.range y ⊆ U → Set.range y' ⊆ U → IsPeriod (Fu.Di i) ty P → IsPeriod (Fu.Di i') ty P' → y ≫ toX Xo c = Fu.u i P → y' ≫ toX Xo c = Fu.u i' P' → i = i' := by
  first | exact @GlobalTheory.DetLine.SameIndex.index_eq | exact GlobalTheory.DetLine.SameIndex.index_eq | (intros; apply GlobalTheory.DetLine.SameIndex.index_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentImageDegreeBetweenOfProportionalityStatement
section
open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.componentImageDegree_between_of_proportionality : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), UnfAll U → Proport U → EqVolume U → ∀ u : Weight Dw, (∀ τ, StrictAnti (u τ)) → (∀ τ, StrictAnti (uPrime Dw u τ)) → (∀ Z, BirOn U Z (wtOf Dw u 0)) → (∀ Z, ValMult U Z (wtOf Dw u 0) (wtOf Dw (uPrime Dw u) 0)) → ∀ Z Z' : Comp Xo c, delPrime U Z' u ≤ compDeg U Z (wtOf Dw u 0) ∧ (compDeg U Z (wtOf Dw u 0) : ℝ) ≤ delPrime U Z' u / (1 - rhoB Dw u) := by
  first | exact @GlobalTheory.DegVal.compDeg_between | exact GlobalTheory.DegVal.compDeg_between | (intros; apply GlobalTheory.DegVal.compDeg_between <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CongruenceSubgroupIndicatorWeightStatement
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.congruence_subgroup_indicator_weight : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (n a b k : ℕ), a + b = n → 1 ≤ k → Match n a b w 1 ((({γ : UL n w | γ.1 ∈ {g : GLw n w | g ∈ GlobalTheory.LFun.KGL w n ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))}} : Set (UL n w))).indicator 1) (fun y : GLw a w × GLw b w => ((-((Real.sqrt (qV E w : ℝ) : ℝ) : ℂ)) ^ (k * a * b))⁻¹ * (if y.1 ∈ GlobalTheory.LFun.KGL w a ∧ nrmL a w y.1 ∈ {g : GLw a w | g ∈ GlobalTheory.LFun.KGL w a ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} ∧ y.2 ∈ GlobalTheory.LFun.KGL w b ∧ nrmL b w y.2 ∈ {g : GLw b w | g ∈ GlobalTheory.LFun.KGL w b ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin b) (Fin b) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} then 1 else 0)) := by
  first | exact @GlobalTheory.CongMatch.match_principal_congruence_inert | exact GlobalTheory.CongMatch.match_principal_congruence_inert | (intros; apply GlobalTheory.CongMatch.match_principal_congruence_inert <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateWeightSmoothNormalization
section
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CoverNorm

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

theorem isRatSec_one_pull_triv (V : Cover Y) :
    IsRatSec ((LB.triv V.X).pull V.j) (fun _ => 1) := fun a b h => by
  have hL := LB.isLB_pull (LB.isLB_triv V.X) V.j
  obtain rfl : a = b := Subsingleton.elim (α := PUnit → PUnit) _ _
  have := congrArg (fun u : Γ(V.G, _)ˣ => fnOf _ h.1 u.val) (hL.g_self a)
  rw [Units.val_one, map_one] at this
  exact (this.symm.trans (fnOf_resG _ h.1 _)).trans (mul_one _).symm

theorem norms_triv_fnB : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y), Norms V (HermLB.triv V.p) (fun _ => 1) (fun _ _ => 0) (fun _ _ _ => 0) ∧ ∀ (u : ∀ σ : 𝓞 F →+* ℂ, CxPts V.p σ → ℝ) (hu : ∀ σ y, CxPts.CInfAt (u σ) y) (hc : ∀ σ σ', (Weight.ofFun (u σ)).IsConj (Weight.ofFun (u σ'))) (a : ∀ σ : F →+* ℂ, Pts Y σ → ℝ), (∀ (σ : F →+* ℂ) (z : CxPts (V.π ≫ Y.str) σ) (y : Pts Y σ) (y' : CxPts V.p (σ.comp (algebraMap (𝓞 F) F))), y.1 = z.1 ≫ V.π → y'.1 = z.1 ≫ V.j → a σ y = -(u _ y' / 2)) → Norms V (ArInt.fnB u hu hc) (fun _ => 1) a (fun _ _ _ => 0) := by
  intro F _ _ Y V
  have hcx {σ : F →+* ℂ} (z : CxPts (V.π ≫ Y.str) σ) :
      Real.log ‖ratVal (V.φ 1 * ((1 : V.G.functionFieldˣ) : V.G.functionField)) z‖ = 0 := by
    rw [map_one, Units.val_one, mul_one]
    have e := ratVal_fnOf (y := z) CxPts.mem_ptsIn_top trivial 1
    rw [map_one, CxPts.ev_one CxPts.mem_ptsIn_top] at e
    rw [e, norm_one, Real.log_one]
  have hfin {v : HeightOneSpectrum (𝓞 F)} (e : Ext v) (z : Sp (AlgebraicClosure F) ⟶ V.G) :
      0 = Real.log (e.w (valAt z (V.φ 1 * ((1 : V.G.functionFieldˣ) : V.G.functionField)))) := by
    rw [map_one, Units.val_one, mul_one, GlobalTheory.TrueGeo.Res.valAt_one, map_one, Real.log_one]
  refine ⟨⟨fun _ => 1, isRatSec_one_pull_triv V, fun i x _ => ?_, fun σ z y y' i _ _ _ => ?_,
    fun v e y z yt i _ _ _ => hfin e z⟩, fun u hu hc a ha => ⟨fun _ => 1, isRatSec_one_pull_triv V,
    fun i x _ => ?_, fun σ z y y' i e₁ e₂ _ => ?_, fun v e y z yt i _ _ _ => hfin e z⟩⟩
  · rw [map_one, Units.val_one, mul_one]; exact unitAt_one x
  · rw [hcx]
    show (0 : ℝ) = 0 - 0 / 2
    ring
  · rw [map_one, Units.val_one, mul_one]; exact unitAt_one x
  · rw [hcx, ha σ z y y' e₁ e₂]
    show -(u _ y' / 2) = 0 - u _ y' / 2
    ring

end GlobalTheory.CoverNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedSpacePullbackOfCompSurjective
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory

theorem connectedSpace_pullback_of_comp_surjective (X P Q Z : Scheme.{0}) (a : X ⟶ P)
    (b : P ⟶ Q) (g : X ⟶ Q) (ν : Z ⟶ Q) (hg : a ≫ b = g) (ha : Surjective a)
    (hc : ConnectedSpace (pullback g ν : Scheme.{0})) :
    ConnectedSpace (pullback b ν : Scheme.{0}) := by
  subst hg
  let f : pullback (a ≫ b) ν ⟶ pullback b ν :=
    (pullbackRightPullbackFstIso b ν a).inv ≫ pullback.snd a (pullback.fst b ν)
  have hf : Surjective f := inferInstance
  exact Function.Surjective.connectedSpace hf.surj f.base.hom.continuous

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedSpacePullbackRestrictOpenContainingFibr
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem geomFibre_restrict_open_connected : ∀ (H Q Z : Scheme.{0}) (U : H.Opens) (f : H ⟶ Q) (ν : Z ⟶ Q), (∀ h : H, f h ∈ Set.range ν → h ∈ U) → ConnectedSpace (pullback f ν : Scheme.{0}) → ConnectedSpace (pullback (U.ι ≫ f) ν : Scheme.{0}) := by
  intro H Q Z U f ν hU hc
  have hs : IsIso (pullback.snd U.ι (pullback.fst f ν)) := by
    refine isIso_of_isOpenImmersion_of_opensRange_eq_top _ ?_
    rw [Scheme.Hom.opensRange_pullbackSnd]
    refine top_unique fun z _ => ?_
    show pullback.fst f ν z ∈ U.ι.opensRange
    rw [Scheme.Opens.opensRange_ι]
    refine hU _ ⟨pullback.snd f ν z, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  let e := Scheme.homeoOfIso ((pullbackRightPullbackFstIso f ν U.ι).symm ≪≫
    asIso (pullback.snd U.ι (pullback.fst f ν)))
  exact e.connectedSpace_iff.2 hc

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectionWeightJetBoundStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open IsLocalRing Formalism.MainNotions.ModuliIntegralCharts.H1 ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cuspOn_evI_eq : Hypotheses2 → DeepGood → Size → FlatDeg → Covers fun Fm x _ ι p i Y PP _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂), ∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).ub} : Set (AllWt.Weight (dat p i))), letI := p.T.Q.H.starRing; ∀ (nab : NabV Y.d.Xo₂ Y.d.c₂), IsNab Y.d.Xo₂ Y.d.c₂ nab → ∀ f ∈ thGen Y.d.Xo₂ Y.d.c₂ nab (GlobalTheory.RefSum.thA (dat p i) la (GlobalTheory.RefSum.nCol (dat p i))) (GlobalTheory.RefSum.nCol (dat p i)), ∀ (y : Y₀ TF.X Z) (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (y' : IntFr Y.d.Xo₂ Y.d.c₂ T io) (g : (Y₀ TF.X Z).presheaf.stalk y →+* T.V), (letI := io.toAlgebra; TF.X.ptY y'.1 = Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) → ∃ f' ∈ AllWt.cuspOn Y.U Z (Formalism.L2.Pj.wtZ (GlobalTheory.RefSum.thA (dat p i) la (GlobalTheory.RefSum.nCol (dat p i))) (GlobalTheory.RefSum.nCol (dat p i))), evI y' f' = evI y' f := by
  first | exact @GlobalTheory.ThetaCuspOn.theta_cuspOn_value | exact GlobalTheory.ThetaCuspOn.theta_cuspOn_value | (intros; apply GlobalTheory.ThetaCuspOn.theta_cuspOn_value <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstLengthFlatSectionEqFrameNormComplexEmbeddinStatement
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constLengthFlatSection_eq_frameNorm_complexEmbedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K), LiesOn Z y → ∀ (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (h : ReciprocityTheory.GeometryOfNumbersTheory.HermFam K (Fin F.P₀.g → K)), F.IsHerm h → ∀ (u : Fin (Dw.mult τ.1) → Fin F.P₀.g → K) (u' : Fin (Dw.mult (conjEmb τ.1)) → Fin F.P₀.g → K), GlobalTheory.PtDeg.FrameCoord y m1 m2 F τ.1 u → GlobalTheory.PtDeg.FrameCoord y m1 m2 F (conjEmb τ.1) u' → ∀ σ : K →+* ℂ, s.cInf (σ.comp (algebraMap c.F K)) = ‖σ (evR Xo c s.sig y)‖ * Real.sqrt (h.gram σ u).det.re / Real.sqrt (h.gram σ u').det.re := by
  first | exact @GlobalTheory.PtDegArch.cInf_eq_frame_norm | exact GlobalTheory.PtDegArch.cInf_eq_frame_norm | (intros; apply GlobalTheory.PtDegArch.cInf_eq_frame_norm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContractionLieDerivativeDivPowerCompatFiltrationStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contraction_lieDerivative_divPowerCompat_filtration_rules : (∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B) (δ : DividedPowers J) (v : Derivation R B B), (∀ n, ∀ a ∈ J, v (δ.dpow (n + 1) a) = δ.dpow n a * v a) → ∀ x ∈ rel R δ, ctr v x ∈ rel R δ ∧ lie v x ∈ rel R δ) ∧ ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B) (δ : DividedPowers J) (v : Derivation R B B), (∀ n, ∀ a ∈ J, v (δ.dpow (n + 1) a) = δ.dpow n a * v a) → ∀ n, (∀ x ∈ filDR R δ n, ctr v x ∈ filDR R δ n) ∧ (∀ x ∈ filDR R δ (n + 1), dDR R B x ∈ filDR R δ n) ∧ ∀ x ∈ filDR R δ (n + 1), lie v x ∈ filDR R δ n := by
  first | exact @GlobalTheory.PDForm.ctr_lie_rel_filDR | exact GlobalTheory.PDForm.ctr_lie_rel_filDR | (intros; apply GlobalTheory.PDForm.ctr_lie_rel_filDR <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordinateDividesOnNonzeroLocusSectionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coordinate_divides_on_nonzeroLocus_section : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : ZH.RatModel o Ω) (δ : LB M.Z) {I : Type} (t : I → δ.Sec) (th : I → Ω), δ.IsLB → ZM.SecCoord δ t M.pt th → ∀ (a : I) (z : M.Z), z ∈ nonzeroLocus (t a) → M.Div th a z := by
  first | exact @GlobalTheory.ThetaDiv.div_of_mem_nonzeroLocus | exact GlobalTheory.ThetaDiv.div_of_mem_nonzeroLocus | (intros; apply GlobalTheory.ThetaDiv.div_of_mem_nonzeroLocus <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CountingVolumeLeSelfIntersectionNefHermitianBundStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.countingVolume_le_selfIntersection_nefHermitianBundle : ∀ (k : Type) [CommRing k] (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp k) (D d a : ℕ) (L : GlobalTheory.HermLB p) (A : ℝ) (m : ℕ → ℕ∞), GlobalTheory.Published.ArithHilbertSamuel → GlobalTheory.IsArithVar p D → L.IsNef D → L.IsSelfInter A → 0 < d → 0 < a → (∀ i : ℕ, 1 ≤ i → m (a * i) ≤ (L.pow (a * i)).smallSec.encard) → countVol D d a m ≤ ENNReal.ofReal (A / ((d : ℝ) * ((D : ℝ) + 1))) := by
  first | exact @GlobalTheory.countVol_le_selfInter | exact GlobalTheory.countVol_le_selfInter | (intros; apply GlobalTheory.countVol_le_selfInter <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovDelHolExtensionZero
section
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms

noncomputable section

namespace GlobalTheory.SubQuotDelHol

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
  [IsScalarTower ℝ ℂ V]

theorem conn_flat {n : Type*} [Fintype n] [DecidableEq n] {H : V → Matrix n n ℂ} {z : V}
    (h2 : MContDiffAt 2 H z) (hu : IsUnit (H z).det) (ξ₁ ξ₂ : V) :
    mdel (fun x => conn H x ξ₂) z ξ₁ - mdel (fun x => conn H x ξ₁) z ξ₂ +
      conn H z ξ₁ * conn H z ξ₂ - conn H z ξ₂ * conn H z ξ₁ = 0 := by
  have h1 : MContDiffAt 1 H z := h2.of_le one_le_two
  have hu' : IsUnit (H z)ᵀ.det := by rwa [det_transpose]
  have e : ∀ ζ ζ', mdel (fun x => conn H x ζ) z ζ' =
      (H z)ᵀ⁻¹ * (mdel (fun x => mdel H x ζ) z ζ')ᵀ +
        -((H z)ᵀ⁻¹ * (mdel H z ζ')ᵀ * (H z)ᵀ⁻¹) * (mdel H z ζ)ᵀ := by
    intro ζ ζ'
    simp only [conn]
    rw [mdel_mul (h1.transpose.inv hu') (h2.mdel (by norm_num) ζ).transpose,
      mdel_inv h1.transpose hu', mdel_transpose (fun x => mdel H x ζ), mdel_transpose]
  rw [e, e, mdel_mdel_comm h2 ξ₁ ξ₂]
  simp only [conn, Matrix.mul_add, Matrix.add_mul, Matrix.mul_neg, Matrix.neg_mul,
    Matrix.mul_assoc]
  abel

variable {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]

theorem covDelHol_extFormAdj_eq_zero {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V}
    (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) (ξ₁ ξ₂ : V) :
    covDelHol (gramS H) (gramQ H) (extFormAdj H) z ξ₁ ξ₂ = 0 := by
  have hu := h.isUnit z hz
  have hsz := hs z hz
  have h2 := h.two hz
  have h1 := h.one hz
  have hγ : ∀ ζ, (fun x => extFormAdj H x ζ) =ᶠ[𝓝 z]
      fun x => -(quotMap m l * conn H x ζ * incl m l) := fun ζ => by
    filter_upwards [h.isOpen.mem_nhds hz] with x hx
    rw [extFormAdj_eq_neg_secondForm (h.one hx) (h.eventually_herm hx) (h.isUnit x hx) (hs x hx),
      secondForm, blockQS]
  have hc : ∀ ζ, MContDiffAt 1 (fun x => conn H x ζ) z := fun ζ => h2.conn hu (by norm_num) ζ
  have hd : ∀ ζ ζ', mdel (fun x => extFormAdj H x ζ) z ζ' =
      -(quotMap m l * mdel (fun x => conn H x ζ) z ζ' * incl m l) := by
    intro ζ ζ'
    rw [mdel_congr (hγ ζ), mdel_neg, mdel_mul ((mContDiffAt_const _).mul (hc ζ))
      (mContDiffAt_const _), mdel_mul (mContDiffAt_const _) (hc ζ)]
    simp
  have hv : ∀ ζ, extFormAdj H z ζ = -(quotMap m l * conn H z ζ * incl m l) :=
    fun ζ => (hγ ζ).self_of_nhds
  have hS : ∀ ζ, conn (gramS H) z ζ = orthProj (H z) * conn H z ζ * incl m l :=
    fun ζ => Model.conn_sub hu hsz ζ
  have hQ : ∀ ζ, conn (gramQ H) z ζ = quotMap m l * conn H z ζ * orthLift (H z) :=
    fun ζ => Model.conn_quot h1 hu hsz ζ
  have hF := conn_flat h2 hu ξ₁ ξ₂
  have key : quotMap m l * (mdel (fun x => conn H x ξ₂) z ξ₁ - mdel (fun x => conn H x ξ₁) z ξ₂ +
      conn H z ξ₁ * (incl m l * orthProj (H z) + orthLift (H z) * quotMap m l) * conn H z ξ₂ -
      conn H z ξ₂ * (incl m l * orthProj (H z) + orthLift (H z) * quotMap m l) * conn H z ξ₁) *
      incl m l = 0 := by
    rw [incl_mul_orthProj_add, Matrix.mul_one, Matrix.mul_one, hF]; simp
  simp only [covDelHol, homDel, hd, hv, hS, hQ]
  rw [← neg_eq_zero, ← key]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_neg,
    Matrix.neg_mul, Matrix.mul_assoc, neg_neg, neg_sub, neg_add]
  abel

end GlobalTheory.SubQuotDelHol
end
end

