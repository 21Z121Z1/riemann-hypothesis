import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0797
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0034
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0033
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0524
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0684
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricUniformisationSmoothOnInterior
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0633
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0634
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0642
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0707
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Formalism.DegreeFormula.Statement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0034
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0751
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0803
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0760
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0742
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramSmoothOfHolomorphicFrames
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0703
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0946
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0798
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0756
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0730
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowsSameGeometricHalf
import Formalism.LocalToGlobal.NumberFieldFamilies.OwnStruct
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0699
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharacterisedDataWeilEnlargedBaseStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_characterisedData_weil_enlargedBase : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
    ∀ (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
      (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) →
      (∀ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y ∈ B'.LL0) →
      (∀ x ∈ B'.Ks, ∃ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y = x) →
      (HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
      HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
      HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
      HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota) →
      Formalism.L2.Pj.LawsCore core'.toCore → core'.Q.Canon → (∀ j, 1 ≤ (core'.Q.Dw j).p + (core'.Q.Dw j).q) → core'.pb = f'.P.pb →
      letI := alg'; ∀ (Xg : Finset (Gc B' w'.px → B'.LL)) (tr₀ : TrI B' w'.px)
        (R₀ : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀) core'.Q.c.F)
        (cG : G0 R₀.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
        LevOf (w'.st Z') w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) R₀.toLevCh ∧ IsPlacewiseIdentity (w'.st Z') (px := w'.px) R₀.eG ∧
        GoodSet (w'.st Z') (px := w'.px) (R₀.eG.trans cG) Xg ∧ MuOf (w'.st Z') w'.I T' {v | B'.places.resChar v ∈ T'.pl} R₀.mu R₀.twPl ∧
        IdemClass (D := (w'.st Z').toD7) (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).A ∧ R₀.toRealDat.Pre0 (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).lv2 ∧ R₀.IsInert ∧ R₀.IsTup ∧
        R₀.AllPlaces ∧ Keep R₀.toRealDat (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).lv2 cG ∧ BrgStd (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀ R₀.toRealDat ∧
        RSideW z {v | B'.places.resChar v ∈ T'.pl} R₀ →
        ∃ (tr : TrI B' w'.px)
        (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr) core'.Q.c.F)
        (cG' : G0 R'.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
        Pins R' (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr) cG' ∧
        LevOf (w'.st Z') w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) R'.toLevCh ∧ IsPlacewiseIdentity (w'.st Z') (px := w'.px) R'.eG ∧
        GoodSet (w'.st Z') (px := w'.px) (R'.eG.trans cG') Xg ∧ MuOf (w'.st Z') w'.I T' {v | B'.places.resChar v ∈ T'.pl} R'.mu R'.twPl ∧
        BrgStd (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr R'.toRealDat ∧ R'.toRealDat.ExAt ∧ RSide z {v | B'.places.resChar v ∈ T'.pl} R') := by
  first | exact @GlobalTheory.Mem.R3.Rw.WeilExt.exists_pins_rSide | exact GlobalTheory.Mem.R3.Rw.WeilExt.exists_pins_rSide | (intros; apply GlobalTheory.Mem.R3.Rw.WeilExt.exists_pins_rSide <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDiagonalRiemannFormOrthonormalFrame
section
open AlgebraicGeometry CategoryTheory Limits MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.ArcQ GlobalTheory.FrameNormLie GlobalTheory.HodgeSmooth
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

section EigenvectorOrthogonality

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ProjVar.Var GlobalTheory.ShFam.Pad
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.ArcQ GlobalTheory.FrameNormLie GlobalTheory.ShFam
open scoped ComplexOrder

namespace GlobalTheory.HodgeSmooth.EigOrth

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

open Classical in

def riemConst (U : Formalism.L2.PjFree.Unf Xo c σ r) (k : U.Comp) (τ : E →+* ℂ) : ℝ :=
  2 * ((if Formalism.L2.PjFree.relab c σ τ ∈ (U.X k).Ψ then Formalism.L2.PjFree.relab c σ τ
    else ComplexEmbedding.conjugate (Formalism.L2.PjFree.relab c σ τ)) (-(U.X k).ξ0)).im

theorem exists_diag_im {U : Formalism.L2.PjFree.Unf Xo c σ r} (hσ : Formalism.L2.PjFree.GoodEmb c σ)
    (hU : Formalism.L2.PjFree.IsUnf U) (W : UnfWit U) (k : U.Comp) (x : (U.X k).dom) (hx : IsOrth (U.X k) x.1) :
    ∃ D : Fin W.g → ℂ, (∀ τ (j : Fin (Dw.mult τ)), D (W.e.symm ⟨τ, j⟩) = ((riemConst U k τ : ℝ) : ℂ)) ∧
      ∀ v w, (hermForm (diagonal D) (W.Pm k x v) (W.Pm k x w)).im = (W.F.Di (W.ik k)).EF v w := by
  classical
  obtain ⟨hp0, hty⟩ := hU.2.1 k
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  obtain ⟨f, hf⟩ := FrameUnif.exists_letter_equiv (U.X k).Ψ (U.X k).cmType Dw.p Dw.q r hU.1
    (Formalism.L2.PjFree.relab c σ) hbij Dw.mult
    (fun τ h => by unfold Datum.mult; rw [if_pos ((hrt τ).1 ((hty _).1 h))])
    (fun τ h => by unfold Datum.mult; rw [if_neg (fun h' => h ((hty _).2 ((hrt τ).2 h')))])
  rw [← hp0] at hf
  have hper (v) : W.Pm k x v = perVec (U.X k) (W.e.trans f) x.1 (W.φ k v : Fin r → E) := funext fun j => by
    rw [W.Pm_eq, perVec, Equiv.trans_apply]
    have h := hf (W.e j)
    generalize f (W.e j) = t at h ⊢
    obtain ⟨⟨τ, hτ⟩, ⟨n, hn⟩⟩ := t
    dsimp only at h ⊢
    rcases h with ⟨a, rfl, rfl⟩ | ⟨a, rfl, rfl, d⟩
    · rw [if_neg (by omega), Formalism.L2.PjFree.perFr, dif_pos a, dif_pos hn]
    · rw [if_pos (by omega), Formalism.L2.PjFree.perFr, dif_neg a,
        dif_pos (show conjEmb (Formalism.L2.PjFree.relab c σ (W.e j).1) ∈ (U.X k).Ψ from hτ), dif_pos hn]
      rfl
  refine ⟨diagXi (U.X k) (W.e.trans f), fun τ j => ?_, fun v w => ?_⟩
  · rw [diagXi, Equiv.trans_apply, Equiv.apply_symm_apply]
    rcases hf ⟨τ, j⟩ with ⟨a, h1, -⟩ | ⟨a, h1, -, -⟩
    · rw [h1]
      simp only [riemConst, if_pos a]
    · rw [h1]
      simp only [riemConst, if_neg a]
  · rw [hper, hper, im_diag_ortho _ _ _ hx, ← W.iso]
    simp

theorem riemConst_pos {U : Formalism.L2.PjFree.Unf Xo c σ r} (hσ : Formalism.L2.PjFree.GoodEmb c σ)
    (hU : Formalism.L2.PjFree.IsUnf U) (W : UnfWit U) (k : U.Comp) (x : (U.X k).dom) (hx : IsOrth (U.X k) x.1)
    (τ : E →+* ℂ) (hτ : 0 < Dw.mult τ) : 0 < riemConst U k τ := by
  classical
  obtain ⟨D, hD, him⟩ := exists_diag_im hσ hU W k x hx
  obtain ⟨-, -, -, hspan, Hm₀, -, hpos, hHm₀⟩ := W.period k x
  have e := UnitDet.eq_of_im_hermForm_eq _ hspan (diagonal D) Hm₀ (by
    rintro _ ⟨v, rfl⟩ _ ⟨w, rfl⟩
    rw [him, hHm₀])
  set j := W.e.symm ⟨τ, ⟨0, hτ⟩⟩
  have h := hpos (Pi.single j 1) (by simp)
  rw [← e] at h
  have h2 : hermForm (diagonal D) (Pi.single j 1) (Pi.single j 1) = D j := by
    simp [hermForm]
  rw [h2, hD] at h
  simpa using h

end GlobalTheory.HodgeSmooth.EigOrth

end EigenvectorOrthogonality

open GlobalTheory.HodgeSmooth.EigOrth in

theorem GlobalTheory.HodgeSmooth.exists_diag_riem_orth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (W : UnfWit U), ∃ d : U.Comp → (E →+* ℂ) → ℝ, (∀ (k : U.Comp) (x : (U.X k).dom), IsOrth (U.X k) x.1 → ∀ τ : E →+* ℂ, 0 < Dw.mult τ → 0 < d k τ) ∧ ∀ (k : U.Comp) (x : (U.X k).dom), IsOrth (U.X k) x.1 → ∀ (i : Fin W.F.n) (P : (W.F.Di i).La →+ (Fin W.g → ℂ)), IsPeriod (W.F.Di i) (fun j => Formalism.L2.PjFree.relab c σ (W.e j).1) P → ∀ (Hm : Matrix (Fin W.g) (Fin W.g) ℂ), (∀ v w, (hermForm Hm (P v) (P w)).im = (W.F.Di i).EF v w) → W.F.u i P = (U.un k x).x → ∀ (τ τ' : E →+* ℂ) (zz : Fin (Dw.mult τ) → (Fin W.g → ℂ)) (zz' : Fin (Dw.mult τ') → (Fin W.g → ℂ)) (uu : Fin (Dw.mult τ) → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)) (uu' : Fin (Dw.mult τ') → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)) (T : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ) (T' : Matrix (Fin (Dw.mult τ')) (Fin (Dw.mult τ')) ℂ), (∀ b, IsDerivAt0 (fun w => (W.F.ex i P w).left) (zz b) (uu b)) → (∀ b, IsDerivAt0 (fun w => (W.F.ex i P w).left) (zz' b) (uu' b)) → (∀ b, IsCombAt (U.un k x).x ((U.un k x).u τ) (show Fin (Dw.mult τ) → CAt σ from fun b' => T b' b) (uu b)) → (∀ b, IsCombAt (U.un k x).x ((U.un k x).u τ') (show Fin (Dw.mult τ') → CAt σ from fun b' => T' b' b) (uu' b)) → (of fun b b' => hermForm Hm (zz b') (zz b)) = ((d k τ : ℝ) : ℂ) • (Tᴴ * T) ∧ (τ' ≠ τ → ∀ b b', hermForm Hm (zz' b') (zz b) = 0) := by
  classical
  intro E _ _ _ H Dw l Xo c σ r U hσ hU W
  refine ⟨fun k τ => riemConst U k τ, fun k x hx τ hτ => riemConst_pos hσ hU W k x hx τ hτ, ?_⟩
  intro k x hx i P hP Hm hH hPu τ τ' zz zz' uu uu' T T' hder hder' hT hT'
  obtain ⟨D, hD, him⟩ := exists_diag_im hσ hU W k x hx
  have p := W.period k x
  obtain ⟨hPx, hv⟩ := W.lie k x
  obtain ⟨h, gam, hex, hh, hiso, -⟩ := familyUnif_exp_unique E H Dw l Xo _ _ _ W.F i (W.ik k) P _ hP p
    (by rw [← hPx]; exact hPu)
  set A := LinearMap.toMatrix' h.toLinearMap with hA
  have hAv : ∀ z, A *ᵥ z = h z := fun z => by rw [hA, LinearMap.toMatrix'_mulVec]; rfl
  have hcol : ∀ (τ : E →+* ℂ) (zz : Fin (Dw.mult τ) → (Fin W.g → ℂ))
      (uu : Fin (Dw.mult τ) → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left))
      (T : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ),
      (∀ b, IsDerivAt0 (fun w => (W.F.ex i P w).left) (zz b) (uu b)) →
      (∀ b, IsCombAt (U.un k x).x ((U.un k x).u τ) (show Fin (Dw.mult τ) → CAt σ from fun b' => T b' b) (uu b)) →
      ∀ b, A *ᵥ zz b = ∑ j, T j b • (Pi.single (W.e.symm ⟨τ, j⟩) 1 : Fin W.g → ℂ) := by
    intro τ zz uu T hder hT b
    have d1 := (DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ _ _ W.F _ _ p _ ((U.un k x).u τ) _ (hv τ) _
      (uu b)).1 (hPx ▸ hT b)
    have d2 := (ExpChain.isDerivAt0_ex_iff E H Dw l Xo _ _ _ W.F _ P hP _ _ h.toLinearMap p hex _ _).1 (hder b)
    have tn := isDerivAt0_ex_isTanAt E H Dw l Xo _ _ _ W.F _ _ p
    rw [hAv]
    exact (tn.2.2 _ (tn.1 _ _ d2)).unique d2 d1
  have key := UnitDet.eq_of_im_hermForm_eq _ hP.2.2.2.1
    (Aᵀ * (diagonal D * A.map (starRingEnd ℂ))) Hm (by
      rintro _ ⟨v, rfl⟩ _ ⟨w, rfl⟩
      rw [← UnitDet.hermForm_mulVec, hAv, hAv, ← hh, ← hh, him, hiso, hH])
  refine ⟨?_, fun hne b b' => ?_⟩
  · have hsupp : ∀ b, diagonal D *ᵥ star (∑ j, T j b • (Pi.single (W.e.symm ⟨τ, j⟩) 1 : Fin W.g → ℂ)) =
        (((riemConst U k τ : ℝ) : ℂ) • (1 : Matrix (Fin W.g) (Fin W.g) ℂ)) *ᵥ
          star (∑ j, T j b • (Pi.single (W.e.symm ⟨τ, j⟩) 1 : Fin W.g → ℂ)) := by
      intro b
      simp only [smul_mulVec, Matrix.one_mulVec]
      funext p'
      rw [mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
      by_cases hp : ∃ j, W.e.symm ⟨τ, j⟩ = p'
      · obtain ⟨j, rfl⟩ := hp
        rw [hD τ j]
      · push_neg at hp
        have : (∑ j, T j b • (Pi.single (W.e.symm ⟨τ, j⟩) 1 : Fin W.g → ℂ)) p' = 0 := by
          rw [Finset.sum_apply]
          exact Finset.sum_eq_zero fun j _ => by rw [Pi.smul_apply, Pi.single_eq_of_ne (hp j).symm, smul_zero]
        simp [Pi.star_apply, this]
    ext b b'
    rw [of_apply, ← key, ← UnitDet.hermForm_mulVec, hcol τ zz uu T hder hT, hcol τ zz uu T hder hT, hermForm,
      hsupp, ← hermForm]
    beta_reduce
    generalize ((riemConst U k τ : ℝ) : ℂ) = dd
    clear hsupp key hcol hAv hiso hh hex him hD hT hder hH hPu hT' hder'
    have hi : ∀ j j' : Fin (Dw.mult τ), W.e.symm ⟨τ, j⟩ = W.e.symm ⟨τ, j'⟩ ↔ j = j' := fun j j' => by simp
    simp [hermForm, smul_mulVec, sum_dotProduct, dotProduct_sum, star_sum, Pi.single_apply, hi, mul_apply, mul_comm]
  · rw [← key, ← UnitDet.hermForm_mulVec, hcol τ' zz' uu' T' hder' hT', hcol τ zz uu T hder hT]
    simp only [hermForm, dotProduct, mulVec_diagonal, Pi.star_apply]
    refine Finset.sum_eq_zero fun q _ => ?_
    by_cases hq : ∃ j, W.e.symm ⟨τ', j⟩ = q
    · obtain ⟨j, rfl⟩ := hq
      have : (∑ j'', T j'' b • (Pi.single (W.e.symm ⟨τ, j''⟩) 1 : Fin W.g → ℂ)) (W.e.symm ⟨τ', j⟩) = 0 := by
        rw [Finset.sum_apply]
        refine Finset.sum_eq_zero fun j'' _ => ?_
        rw [Pi.smul_apply, Pi.single_eq_of_ne, smul_zero]
        intro he
        exact hne (congrArg Sigma.fst (W.e.symm.injective he))
      rw [this]
      simp
    · push_neg at hq
      have : (∑ j, T' j b' • (Pi.single (W.e.symm ⟨τ', j⟩) 1 : Fin W.g → ℂ)) q = 0 := by
        rw [Finset.sum_apply]
        exact Finset.sum_eq_zero fun j _ => by rw [Pi.smul_apply, Pi.single_eq_of_ne (hq j).symm, smul_zero]
      rw [this]
      simp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicFrameChangeAlongAnalyticLift
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx
open scoped Matrix
open Filter Topology
open GlobalTheory.PointChern

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnifFrameChange

theorem isHolTo_cxPt_V {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β) {σ : c.F →+* ℂ}
    {r : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ r} (hU : Formalism.L2.PjFree.IsUnf U) (k : U.Comp) {n : ℕ}
    {B : Set (ReciprocityTheory.L2DbarEstimates.V n)} (hB : IsOpen B) (x : ReciprocityTheory.L2DbarEstimates.V n → (U.X k).dom)
    (hd : ∀ τ a a', DifferentiableOn ℂ (fun b => ReciprocityTheory.ChartRestriction.G.FD.mat (x b).1 τ a a') B) :
    IsHolTo B fun b => (cxPt Z (U.un k (x b))).1 := by
  let L := EuclideanSpace.equiv (Fin n) ℂ
  have hB₁ : IsOpen (L.symm ⁻¹' B) := hB.preimage L.symm.continuous
  have h1 := GlobalTheory.GramFamily.isHolTo_cxPt Z hU k hB₁ (fun u => x (L.symm u)) fun τ a a' =>
    (hd τ a a').comp L.symm.differentiableOn fun u hu => hu
  intro W f
  obtain ⟨ho, hdf⟩ := h1 W f
  have hset : {b ∈ B | ⊤ ≤ (cxPt Z (U.un k (x b))).1 ⁻¹ᵁ W} =
      L ⁻¹' {u ∈ L.symm ⁻¹' B | ⊤ ≤ (cxPt Z (U.un k (x (L.symm u)))).1 ⁻¹ᵁ W} := by
    ext b
    simp only [Set.mem_setOf_eq, Set.mem_preimage, ContinuousLinearEquiv.symm_apply_apply]
  rw [hset]
  refine ⟨ho.preimage L.continuous, ?_⟩
  have := hdf.comp L.differentiableOn (Set.mapsTo_preimage _ _)
  refine this.congr fun b _ => ?_
  simp only [Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]

end GlobalTheory.UnifFrameChange

open GlobalTheory.UnifFrameChange in

theorem GlobalTheory.UnifFrameChange.exists_holomorphic_frame_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (k : U.Comp) (X : Var F) (j : X.X ⟶ gen T.Z) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsOpenImmersion j → Tied e X j f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ∀ (h : Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p)) = X.dim) (v : ReciprocityTheory.L2DbarEstimates.V X.dim), GlobalTheory.UnifDens.flatL h v ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) → ∀ A ∈ Eb.S (under (ψ (GlobalTheory.UnifDens.flatL h v))), ∀ s : ReciprocityTheory.L2DbarEstimates.V X.dim → ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k).Ψ (Dw.p + Dw.q), AnalyticAt ℂ s v → (∀ᶠ w in nhds v, ∃ hs : s w ∈ (U.X k).dom, flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) (s w)) = GlobalTheory.UnifDens.flatL h w) → ∃ K : ReciprocityTheory.L2DbarEstimates.V X.dim → Mat Dw.mult ℂ, (∀ τ a b, AnalyticAt ℂ (fun w => K w τ a b) v) ∧ (∀ τ, IsUnit (K v τ).det) ∧ ∀ᶠ w in nhds v, ∀ (hs : s w ∈ (U.X k).dom) (g : EigFrame T.Z σ ((cxOf e σ hj (ψ (GlobalTheory.UnifDens.flatL h w))).1 ≫ genι T.Z)), FrameAt e f₀ A₀ A (ψ (GlobalTheory.UnifDens.flatL h w)) g → ∀ (M : EigMet T.Z σ) (τ : E →+* ℂ), M.gram (cxOf e σ hj (ψ (GlobalTheory.UnifDens.flatL h w))) g τ = (K w τ)ᴴ * M.gram (cxPt T.Z (U.un k ⟨s w, hs⟩)) (cxFrame T.Z (U.un k ⟨s w, hs⟩)) τ * K w τ := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U _ hU k X j f₀ Eb A₀ hj hoi hT ψ hψ h v _ A hA s han hlift
  classical

  set pt : ReciprocityTheory.L2DbarEstimates.V X.dim → CxPts X.str (σ.comp e.toRingHom) := fun w => ψ (GlobalTheory.UnifDens.flatL h w) with hptdef

  obtain ⟨B₀, hB₀all, hB₀, hv₀⟩ := eventually_nhds_iff.1 (hlift.and han.eventually_analyticAt)
  choose hsB₀ hflB₀ using fun b (hb : b ∈ B₀) => (hB₀all b hb).1
  have hpt₀ : ∀ b (hb : b ∈ B₀), cxPt T.Z (U.un k ⟨s b, hsB₀ b hb⟩) = cxOf e σ hj (pt b) := by
    intro b hb
    have := hψ ⟨s b, hsB₀ b hb⟩
    rw [hflB₀ b hb] at this
    exact this.symm
  let x : ReciprocityTheory.L2DbarEstimates.V X.dim → (U.X k).dom := fun b =>
    if hb : b ∈ B₀ then ⟨s b, hsB₀ b hb⟩ else ⟨s v, hsB₀ v hv₀⟩
  have hxB : ∀ b (hb : b ∈ B₀), x b = ⟨s b, hsB₀ b hb⟩ := fun b hb => by simp only [x, dif_pos hb]
  have hsd : DifferentiableOn ℂ s B₀ := fun b hb => (hB₀all b hb).2.differentiableAt.differentiableWithinAt
  have hd : ∀ τ a a', DifferentiableOn ℂ (fun b => ReciprocityTheory.ChartRestriction.G.FD.mat (x b).1 τ a a') B₀ := by
    intro τ a a'
    refine (differentiableOn_pi.1 (differentiableOn_pi.1 (differentiableOn_pi.1 hsd τ) a) a').congr fun b hb => ?_
    rw [hxB b hb]
    rfl
  have hY := isHolTo_cxPt_V T.Z hU k hB₀ x hd
  have hxpt : ∀ b (hb : b ∈ B₀), (cxPt T.Z (U.un k (x b))) = cxOf e σ hj (pt b) := fun b hb => by
    rw [hxB b hb]; exact hpt₀ b hb

  have hgenev : ∀ W' : (gen T.Z).Opens, cxOf e σ hj (pt v) ∈ ptsIn (genStr T.Z) σ W' →
      ∀ᶠ w in 𝓝 v, w ∈ B₀ ∧ ⊤ ≤ (cxPt T.Z (U.un k (x w))).1 ⁻¹ᵁ W' := by
    intro W' hW'
    refine ((hY W' 0).1).mem_nhds ⟨hv₀, ?_⟩
    show ⊤ ≤ (cxPt T.Z (U.un k (x v))).1 ⁻¹ᵁ W'
    rw [hxpt v hv₀]
    exact hW'
  have hpre : ∀ (W : X.X.Opens) (z : CxPts X.str (σ.comp e.toRingHom)),
      z ∈ ptsIn X.str (σ.comp e.toRingHom) W ↔ cxOf e σ hj z ∈ ptsIn (genStr T.Z) σ (j ''ᵁ W) := by
    intro W z
    have := mem_ptsIn_preimage (m := cxOf e σ hj) (f := j) (fun _ => rfl) (U := j ''ᵁ W) (z := z)
    rwa [j.preimage_image_eq W] at this
  have hXev : ∀ W : X.X.Opens, pt v ∈ ptsIn X.str (σ.comp e.toRingHom) W →
      ∀ᶠ w in 𝓝 v, pt w ∈ ptsIn X.str (σ.comp e.toRingHom) W := by
    intro W hW
    filter_upwards [hgenev _ ((hpre W _).1 hW)] with w hw
    refine (hpre W _).2 ?_
    rw [← hxpt w hw.1]
    exact hw.2
  have hregev : ∀ {g : X.Fn}, RegAt (under (pt v)) g → ∀ᶠ w in 𝓝 v, RegAt (under (pt w)) g := by
    intro g hg
    obtain ⟨W, hW, a, rfl⟩ := hg.exists_fnOf
    filter_upwards [hXev W (mem_ptsIn.2 hW)] with w hw
    exact regAt_fnOf (mem_ptsIn.1 hw) _ a
  have hmemev : ∀ᶠ w in 𝓝 v, A ∈ Eb.S (under (pt w)) := by
    obtain ⟨U', B', hU', hB', hS⟩ := Eb.loc (under (pt v))
    have hP := (hS _ hU' A).1 hA
    have hU'' : ∀ᶠ w in 𝓝 v, under (pt w) ∈ U' := by
      filter_upwards [hXev U' (mem_ptsIn.2 hU')] with w hw
      exact mem_ptsIn.1 hw
    have h1 : ∀ᶠ w in 𝓝 v, ∀ τ, (∀ i j, RegAt (under (pt w)) ((A * B'⁻¹) τ i j)) ∧
        RegAt (under (pt w)) ((A * B'⁻¹) τ).det⁻¹ :=
      Filter.eventually_all.2 fun τ => (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
        hregev (mem_O_ratOf.1 ((hP τ).1 i j))).and (hregev (mem_O_ratOf.1 (hP τ).2.2.1))
    filter_upwards [hU'', h1] with w hw hw1
    exact (hS _ hw A).2 fun τ => ⟨fun i j => mem_O_ratOf.2 ((hw1 τ).1 i j), (hP τ).2.1, mem_O_ratOf.2 (hw1 τ).2,
      fun i j hi => absurd hi (by simp)⟩
  have hratan : ∀ {g : X.Fn}, RegAt (under (pt v)) g → AnalyticAt ℂ (fun w => ratVal g (pt w)) v := by
    intro g hg
    haveI : IsOpenImmersion j := hoi
    obtain ⟨W, hW, a, rfl⟩ := hg.exists_fnOf
    set g' := (j.appIso W).inv.hom a
    have hvS : v ∈ {b ∈ B₀ | ⊤ ≤ (cxPt T.Z (U.un k (x b))).1 ⁻¹ᵁ (j ''ᵁ W)} := by
      refine ⟨hv₀, ?_⟩
      rw [hxpt v hv₀]
      exact GlobalTheory.LieBase.le_preimage_cxOf e σ hj W (mem_ptsIn.2 hW)
    have han' := GlobalTheory.SCV.analyticAt_of_differentiableOn ((hY (j ''ᵁ W) g').2) (((hY (j ''ᵁ W) g').1).mem_nhds hvS)
    refine han'.congr ?_
    filter_upwards [hXev W (mem_ptsIn.2 hW), hB₀.mem_nhds hv₀] with w hw hwB
    show valAt' _ _ _ = ratVal _ (pt w)
    rw [ratVal_fnOf hw, GlobalTheory.LieBase.ev_eq_valAt'_cxOf e σ hj W a hw, hxpt w hwB]

  obtain ⟨V₀, hV₀, φ, Φ, hzV, hφ, -⟩ := EigSpread.exists_stable_eigFrame E H Dw l Xo c O β T.Z
    ((cxOf e σ hj (pt v)).1 (IsLocalRing.closedPoint ℂ))
  let V : (gen T.Z).affineOpens := ⟨V₀, hV₀⟩
  have hφ' : LogKS.chart V ≫ genStr T.Z = spMap φ := hφ
  have hyV : cxOf e σ hj (pt v) ∈ ptsIn (genStr T.Z) σ V.1 := mem_ptsIn.2 hzV
  obtain ⟨M, hM⟩ := GlobalTheory.T.frame_coordinates_eq_rational_matrix_values_chart E H Dw l Xo c O β T.Z σ F e X j f₀ Eb A₀ hj hoi hT V φ Φ hφ' A
  have hVn : ∀ᶠ w in 𝓝 v, cxOf e σ hj (pt w) ∈ ptsIn (genStr T.Z) σ V.1 := by
    filter_upwards [hgenev _ hyV] with w hw
    rw [← hxpt w hw.1]
    exact hw.2
  obtain ⟨B, hBall, hB, hb₀⟩ := eventually_nhds_iff.1
    ((show ∀ᶠ w in 𝓝 v, w ∈ B₀ from hB₀.mem_nhds hv₀).and (hVn.and hmemev))
  have hsB : ∀ b ∈ B, s b ∈ (U.X k).dom := fun b hb => hsB₀ b (hBall b hb).1
  have hpt : ∀ b (hb : b ∈ B), cxPt T.Z (U.un k ⟨s b, hsB b hb⟩) = cxOf e σ hj (pt b) :=
    fun b hb => hpt₀ b (hBall b hb).1
  obtain ⟨N, hN, hNco⟩ := GlobalTheory.FrameLift.exists_coords (Z := T.Z) hU k hB hb₀ hsB
    (hsd.mono fun b hb => (hBall b hb).1) V Φ (fun b hb => by rw [hpt b hb]; exact (hBall b hb).2.1)
  have key : ∀ b (hb : b ∈ B) (G g : EigFrame T.Z σ ((cxOf e σ hj (pt b)).1 ≫ genι T.Z)),
      (∀ τ i, G.v τ i = (cxFrame T.Z (U.un k ⟨s b, hsB b hb⟩)).v τ i) → FrameAt e f₀ A₀ A (pt b) g →
        ∀ τ, G.co g τ = N b τ * (M τ).map fun r => ratVal r (pt b) := by
    intro b hb G g hG hg τ
    obtain ⟨-, hzV, hzS⟩ := hBall b hb
    have hov : σ = (evHom hzV).comp φ := by
      generalize cxOf e σ hj (pt b) = z at hzV
      exact GlobalTheory.ShFam.EigLoc.spMap_inj (z.2.symm.trans (by
        rw [← ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap, ← hφ', ← Category.assoc, GlobalTheory.LieMet.spMap_evHom hzV]))
    have hx : (cxOf e σ hj (pt b)).1 ≫ genι T.Z = spMap (evHom hzV) ≫ LogKS.chart V ≫ genι T.Z := by
      rw [← Category.assoc, GlobalTheory.LieMet.spMap_evHom hzV]
    obtain ⟨f, hf⟩ := Φ.exists_isMap (evHom hzV) hov hx
    rw [← hNco b hb _ (hpt b hb) hzV G f hG hf τ, ← (hM _ hzS hzV).2.2 g hg f hf τ, EigFrame.co_mul]
  have hex : ∀ b ∈ B, ∃ g : EigFrame T.Z σ ((cxOf e σ hj (pt b)).1 ≫ genι T.Z),
      FrameAt e f₀ A₀ A (pt b) g := fun b hb => (hM _ (hBall b hb).2.2 (hBall b hb).2.1).2.1
  refine ⟨fun b τ => N b τ * (M τ).map fun r => ratVal r (pt b), fun τ a a' => ?_, fun τ => ?_, ?_⟩
  · simp only [Matrix.mul_apply, Matrix.map_apply]
    exact Finset.analyticAt_fun_sum _ fun i _ =>
      (GlobalTheory.SCV.analyticAt_of_differentiableOn (hN τ a i) (hB.mem_nhds hb₀)).mul
        (hratan ((hM (pt v) hA hyV).1 τ i a'))
  · obtain ⟨g, hg⟩ := hex _ hb₀
    obtain ⟨G, hG, -⟩ := GlobalTheory.FrameLift.exists_transport (hpt _ hb₀) (cxFrame T.Z _)
    show IsUnit (N v τ * (M τ).map fun r => ratVal r (pt v)).det
    rw [← key _ hb₀ G g hG hg τ]
    exact G.isUnit_det_co g τ
  · filter_upwards [hB.mem_nhds hb₀] with b hb
    intro hsb g hg Me τ
    obtain ⟨G, hG, hGm⟩ := GlobalTheory.FrameLift.exists_transport (hpt b hb) (cxFrame T.Z _)
    rw [← key b hb G g hG hg τ, ← hGm Me τ]
    exact Me.change _ G g τ

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHomogeneousPolysTangentBasisStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_homogeneous_polys_tangent_basis : HTBoundSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X), X.IsSeparated → ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [CharZero A] (x₀ : Sp A ⟶ X) (g : ℕ) (e : Fin g → (Sp (DualNumber A) ⟶ t.G.left)), IsTanBasis t x₀ e → ∀ q k : ℕ, ∃ (d : ℕ+) (n : ℕ) (B : Fin n → MvPolynomial (Fin k → Fin g) A), (∀ i, (B i).IsHomogeneous d) ∧ (∀ s, ∃ (i : Fin n) (c : ℕ), c ≠ 0 ∧ B i = MvPolynomial.C (c : A) * (MvPolynomial.X s : MvPolynomial (Fin k → Fin g) A) ^ (d : ℕ)) ∧ ∀ (p : ℕ) [Fact p.Prime] (x : A →+* ℂ_[p]), (∀ a, ‖x a‖ ≤ 1) → ∀ (m : ℕ) (hk : k ≤ m) (u : Fin m → (Sp (DualNumber ℂ_[p]) ⟶ t.G.left)) (a : Fin m → Fin g → ℂ_[p]), LinearIndependent ℂ_[p] a → (∀ l, IsCombAtG t (spMap x ≫ x₀) (fun i => spMap (dualMap x) ≫ e i) (a l) (u l)) → ((d : ℕ) : ℝ) * ∑ l : Fin k, Real.log (GlobalTheory.ShFam.Pad.grNorm t (spMap x ≫ x₀) (lat t p (spMap x ≫ x₀) (decide (p = q))) u (Fin.castLE hk l)) = Real.log (⨆ i, ‖MvPolynomial.eval₂ x (minor a hk) (B i)‖) := by
  first | exact @GlobalTheory.LineNorm.WedgeMax.wedge_norm_max | exact GlobalTheory.LineNorm.WedgeMax.wedge_norm_max | (intros; apply GlobalTheory.LineNorm.WedgeMax.wedge_norm_max <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsKeptChoiceUpperLattice
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr

noncomputable section
namespace GlobalTheory.LayerMove
set_option maxHeartbeats 4000000

theorem tupTied_ext {D : D7} {cf : CharFrame D} {C : NChoice D} {p q : TupTied D cf C} (h1 : p.xi = q.xi) (h2 : p.psi = q.psi) :
    p = q := by
  cases p; cases q; cases h1; cases h2; rfl

section
variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
  (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) {nch : NChoice (w.D Z)}
  {xd : ThData (w.D Z)}

theorem nchT_up (n : NchT w Z Wt nch) : Nonempty (NchT w (upL Z S' N h) Wt (nchUp S' N h nch)) :=
  ⟨{ tp := by kcopy n.tp, xi := kc% n.xi, psi := kc% n.psi, tie := by kcopy n.tie, Q := n.Q, chrPsi := by kcopy n.chrPsi }⟩

theorem kept_up (nch : NChoice (w.D Z)) : Kept nch (nchUp S' N h nch) := by
  refine ⟨?_, ?_, ?_, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩ <;> constructor <;> first | rfl | exact HEq.rfl

theorem goodO_up (g : GoodO (w.D Z) nch xd) : GoodO (w.D (upL Z S' N h)) (nchUp S' N h nch) (xdUp S' N h xd) := by
  obtain ⟨⟨E, N0, S⟩, h1, h2, h3⟩ := g.tw
  cases h1
  exact ⟨⟨⟨twEOf (xdUp S' N h xd), N0, S⟩, rfl, kc% h2, kc% h3⟩, g.sep⟩
end

theorem layer_up : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL), ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) (nch : NChoice (w.D Z)) (xd : ThData (w.D Z)), ∃ (nch' : NChoice (w.D (upL Z S' N h))) (xd' : ThData (w.D (upL Z S' N h))), Kept nch nch' ∧ (S' = Z.S → HEq nch' (nchTr (D := w.D Z) N h nch) ∧ HEq xd' (xdTr (D := w.D Z) N h xd)) ∧ (NchT w Z Wt nch → Nonempty (NchT w (upL Z S' N h) Wt nch')) ∧ (GoodO (w.D Z) nch xd → GoodO (w.D (upL Z S' N h)) nch' xd') ∧ ∀ (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0) (n : NchT w Z Wt nch) (p0' : BaseLevelRowSide (w.D (upL Z S' N h))) (t' : RowsT K w (upL Z S' N h) Wt p0') (n' : NchT w (upL Z S' N h) Wt nch'), RowsSame t t' → HEq t'.r.z.geo (R3.Tr.geoHalf (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) (upL Z S' N h) (iK := t.r.z.alg) t.r.z.geo) → NX hL (NEb hL) K B f T w Z Wt p0 t nch n xd → Nonempty (NX hL (NEb hL) K B f T w (upL Z S' N h) Wt p0' t' nch' n' xd') := by
  intro hL K B f T w Z Wt S' N h nch xd
  refine ⟨nchUp S' N h nch, xdUp S' N h xd, kept_up S' N h nch, ?_, nchT_up S' N h, goodO_up S' N h, ?_⟩
  · rintro rfl
    exact ⟨HEq.rfl, HEq.rfl⟩
  · rintro p0 t n p0' t' ⟨tp', xi', psi', tie', Q', chr'⟩ hs hg ⟨c, e, ⟨bk⟩⟩
    have e1 : tp' = (by with_unfolding_all exact (((mvOf w Z S' N h).tp n.tp) :)) := tupTied_ext (xi'.trans ((by with_unfolding_all exact (n.xi.symm :)))) (psi'.trans ((by with_unfolding_all exact (n.psi.symm :))))
    subst e1
    obtain ⟨a', hA⟩ := (mvOf w Z S' N h).exists_at c.a
    refine Exists.elim (exists_row hL K B f T w Z Wt S' N h nch xd p0 t p0' t' hs hg
      (GlobalTheory.T.rowReadings_sameRows_identify_definiteForms K B f T w Z Wt S' N h p0 t p0' t' hs) (GlobalTheory.T.rows_same_geometric_half K B f T w Z Wt S' N h nch p0 t p0' t' hs hg)
      (tp' := (by with_unfolding_all exact (((mvOf w Z S' N h).tp n.tp) :))) c.a ((by with_unfolding_all exact (a' :))) ((by with_unfolding_all exact (hA :))) c.row e) fun r' hr => hr.elim fun e' => ?_
    have hq : a'.Pq = (by with_unfolding_all exact (c.a.Pq :)) := eq_of_heq ((by with_unfolding_all exact (hA.2.1 :)))
    have hsel : Set.range a'.Pq = (by with_unfolding_all exact ((Set.range w.I.sel) :)) := (congrArg Set.range hq).trans ((by with_unfolding_all exact (c.sel :)))
    exact ⟨⟨⟨(by with_unfolding_all exact (a' :)), (by with_unfolding_all exact (r' :)), (by with_unfolding_all exact (hsel :))⟩, (by with_unfolding_all exact (e' :)), ⟨(by with_unfolding_all exact (((mvOf w Z S' N h).bkLaw bk) :))⟩⟩⟩

end GlobalTheory.LayerMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMarkedFormPiecesRaysOfSimplicialCellsStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_markedForm_pieces_rays_of_simplicialCells : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (φ : InvFun (𝓞 E)), IsTwInv H φ →
  ∀ {X₀ : Type} [AddCommGroup X₀] [Module (𝓞 E) X₀] [Module.Finite (𝓞 E) X₀] {m₀ : ℕ} (δ₀ : Fin m₀ → LinearMap.BilinForm ℤ X₀) (h₀ : IsCell H.bar φ δ₀),
  LinearIndependent ℤ δ₀ → (∀ i, IsPrim H.bar (⟨δ₀ i, h₀.mem i⟩ : balForms H.bar X₀)) →
  ∀ (v : LinearMap.BilinForm ℤ X₀) (t : Fin m₀ → ℝ), v ≠ 0 → (∀ i, 0 ≤ t i) → toReal v = ∑ i, t i • toReal (δ₀ i) →
  ∀ {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (β : LinearMap.BilinForm ℤ X), (OrbMark.orbFun (𝓞 E) H.w0 v).evalZ β = 1 →
  ∃ p : Fin m₀ → LinearMap.BilinForm ℤ X, toReal β = ∑ i, t i • toReal (p i) ∧
    (∀ i, 0 < t i → p i ∈ balForms H.bar X ∧ (∀ y, 0 ≤ p i y y) ∧
      (∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = p i → k = 1) ∧
      ∀ lab : InvFun (𝓞 E), IsTwInv H lab → lab.evalZ (p i) = lab.evalZ (δ₀ i)) ∧
    ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar φ δ → LinearIndependent ℤ δ →
      ∀ c : Fin m → ℝ, (∀ j, 0 ≤ c j) → toReal β = ∑ j, c j • toReal (δ j) →
        (∀ i, 0 < t i → ∃ j, 0 < c j ∧ ∃ d : ℝ, 0 < d ∧ toReal (p i) = d • toReal (δ j)) ∧
        (∀ j, 0 < c j → ∃ i, 0 < t i ∧ ∃ d : ℝ, 0 < d ∧ toReal (p i) = d • toReal (δ j) ∧ c j = t i * d) := by
  first | exact @GlobalTheory.PolFan.OrbMark.exists_pieces_match | exact GlobalTheory.PolFan.OrbMark.exists_pieces_match | (intros; apply GlobalTheory.PolFan.OrbMark.exists_pieces_match <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FamilyMetricsSmoothStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.family_metrics_smooth : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (Φ : s.Flag) (k : s.Comp) (σ : D.what₂.LL →+* ℂ) (n : Pad.Letter S.Dw → ℤ), (∀ R : ℝ, 2 ≤ R → (cxSt D.what₂.LL).mSmooth _ σ _ (metsOf x Φ k (some R) σ n)) ∧ (cxSt D.what₂.LL).mSmooth _ σ _ (refMet x Φ k σ n) ∧ Var.Met.SmoothOn (metsOf x Φ k none σ n) {p | (Φ.C k).π (Var.base p) ∉ genBd s.T.Z} := by
  first | exact @GlobalTheory.metsOf_smooth | exact GlobalTheory.metsOf_smooth | (intros; apply GlobalTheory.metsOf_smooth <;> assumption)
end

