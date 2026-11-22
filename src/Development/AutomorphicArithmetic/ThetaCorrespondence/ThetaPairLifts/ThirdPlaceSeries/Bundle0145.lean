import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0600
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0123
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0067
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0128
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0138
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0744
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2715
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0057
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0748
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2777
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0062
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0140
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0132
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0071
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0124
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0749
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0027
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0033
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0030
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0035
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0037
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0044
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0139
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0040
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0031
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealTB
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0601
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0599
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0186
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0078
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2761
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0082
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0024
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowLocPin
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0017
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0048
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0134
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0043
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0049
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0041
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0029
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0045
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0032
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0093
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RunWeightArch
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0060

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RankMuOfBundleStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankMu_all_linked_members : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ D _ _ _ => ∀ u, GlobalTheory.Core.Rk.RankMu D u) := by
  first | exact @_root_.GlobalTheory.Fam.MemberCount.rankMu_of_good_linked | exact _root_.GlobalTheory.Fam.MemberCount.rankMu_of_good_linked | (intros; apply _root_.GlobalTheory.Fam.MemberCount.rankMu_of_good_linked <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RatHeckeKeepsBallStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_reading_eigenvalue_place_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, GlobalTheory.Published.CuspRapidDecay → GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt → GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform → GlobalTheory.HeckeSupSt.HeckeReadTie → StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x → ∀ (hL' : ∀ j, ℕ → PlE (Dof x).host → Module.End (Dof x).what₂.LL ((SOf x).WL j)), StabC (SOf x) hL' → HeckeRd x.m.z.R x.m.z.cG (kKsOf x) (hkOf x) (SbD (Dof x)) hL' → ∀ (j k : ℕ) (Pl : PlE (Dof x).host), 1 ≤ j → j ≤ (Dof x).R.m → IsSplitPl (Dof x).host Pl → Pl ∉ SbD (Dof x) → k ≤ (Dof x).R.r → ∀ la : HeightOneSpectrum (𝓞 (SOf x).Ks), (∀ q : ℕ, q.Prime → (q : 𝓞 (Dof x).host.E) ∈ Pl.asIdeal → (q : 𝓞 (SOf x).Ks) ∉ la.asIdeal) → ∀ (f : (SOf x).WL j) (hf : f ∈ ((SOf x).A j).WK) (hg : hL' j k Pl f ∈ ((SOf x).A j).WK), (∀ y, ((SOf x).A j).nrm la y ⟨f, hf⟩ ≤ 1) → ∀ y, ((SOf x).A j).nrm la y ⟨hL' j k Pl f, hg⟩ ≤ 1 := by
  first | exact @_root_.GlobalTheory.RatHeckeBall.ratHecke_keeps_ball_alt | exact _root_.GlobalTheory.RatHeckeBall.ratHecke_keeps_ball_alt | (intros; apply _root_.GlobalTheory.RatHeckeBall.ratHecke_keeps_ball_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RatUnframeStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.BigOn GlobalTheory.BigOn.Exp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_data_realization_alt : GlobalTheory.Published.CuspRapidDecay → ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (p : Pt Fm x hx i), p.PointConditions' → More p →
  ∀ (t : (Fm.D x i).ntw.Tw) (j : Fin (Fm.D x i).R.m), RatHyp0 p.T p.R (F2 p) p.κ p.v₀ p.O t j →
  ∃ (T' : CoreJ (Fm.D x i)) (_ : Algebra T'.Q.c.F (Fm.D x i).what₂.LL) (Rl' : RealDat3 (Fm.D x i) p.P.A3 T'.Q.c.F)
    (cG' : G0 Rl'.Pg (Fm.D x i).R.r ≃* G0g (Fm.D x i).nd) (S' : NX.RatDat (Fm.D x i).ntw) (YS' : NX.NExpRealS Rl' cG' S')
    (F' : Face (Fm.D x i) p.P.A3.A) (κ' : ∀ j : Fin (Fm.D x i).R.m, WeightFamilies.Wt (Fm.D x i) ((j : ℕ) + 1))
    (v₀' : ∀ (j : Fin (Fm.D x i).R.m) (σ : (Fm.D x i).what₂.LL →+* ℂ), (Rl'.MW j σ).Vec)
    (O' : ∀ j, OMDat T'.toCore Rl'.toRealDat j Unit (fun _ => p.P.A3.A.μ0)) (hV' : T'.V ((j : ℕ) + 1) T'.σ₀ = Wc (Fm.D x i) j),
    RatHyp T' Rl' F' κ' v₀' O' t j hV' ∧ (∀ ρ : Setup (Fm.D x i).ntw, RealPin p.R p.cG ρ → RealPin Rl' cG' ρ) ∧
      ∀ (ρ : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (b : Bool), RatRow YS' v₀' hρ t j b → RatRow p.nexp p.v₀ hρ t j b := by
  first | exact @_root_.GlobalTheory.UnframePt.rat_unframe_alt | exact _root_.GlobalTheory.UnframePt.rat_unframe_alt | (intros; apply _root_.GlobalTheory.UnframePt.rat_unframe_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RationalHeckeAllStStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalHecke_of_levelA : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, GlobalTheory.Published.CuspRapidDecay → GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform → GlobalTheory.HeckeSupSt.HeckeReadTie → StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x → ∀ i : Fin (Dof x).R.m, GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.RationalHecke x.m.z.R.toRealDat i := by
  first | exact @_root_.GlobalTheory.HeckeFamRead.rationalHecke_allSt_alt | exact _root_.GlobalTheory.HeckeFamRead.rationalHecke_allSt_alt | (intros; apply _root_.GlobalTheory.HeckeFamRead.rationalHecke_allSt_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Reading
section
set_option synthInstance.maxHeartbeats 200000

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CovTop.HodgeGapBounds
section Weights
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H}
end Weights
end GlobalTheory.CovTop.HodgeGapBounds
namespace GlobalTheory.CovTop.HodgeGapBounds
theorem reading_alt : _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i _ _ => (i : ℕ) + 1 < (Fm.D x ι).R.m → LawsJ p.T ∧ 1 ≤ (dat p i).p ∧
    1 ≤ (dat p i).q ∧ 2 < Module.finrank ℚ (Fm.D x ι).host.E / 2 ∧ InR (Fm.D x ι) ((i : ℕ) + 1) ∧ Even (p.κ i).n ∧
    (∀ τ, Antitone (uM p i τ)) ∧ (∀ τ, 1 ≤ gap (uM p i τ) ((dat p i).p - 1)) ∧
    ∀ s : ℤ, (s = -(cZero (Fm.D x ι) ((i : ℕ) + 1)) ∨ s = 0 ∨ s = cZero (Fm.D x ι) ((i : ℕ) + 1)) →
      (∀ τ, Antitone ((laOf (dat p i) (wtA (p.κ i)) (p.κ i).n + s • hodgeWt (dat p i)) τ)) ∧
      ∀ τ, 1 ≤ gap ((laOf (dat p i) (wtA (p.κ i)) (p.κ i).n + s • hodgeWt (dat p i)) τ) ((dat p i).p - 1) := by
  have hA := _root_.GlobalTheory.T.weight_parameter_strict_antitone_alt _root_.GlobalTheory.T.cov_size_bound
  have hB := _root_.GlobalTheory.CovTop.WtShape.wtN_z
  unfold _root_.GlobalTheory.CovTop.LiftWeightNumerator at hB
  unfold _root_.GlobalTheory.CovTop.LiftsCondition at hA hB ⊢
  refine (hA.and hB).imp fun Fm CH _ h => ?_
  obtain ⟨⟨C1, -, x1, h1⟩, ⟨C2, -, x2, h2⟩⟩ := h
  refine ⟨0, le_rfl, max x1 x2, fun x hx hle ι p hp i hi => ?_⟩
  have a := h1 x hx ((le_max_left _ _).trans hle) ι p hp i hi
  have b := h2 x hx ((le_max_right _ _).trans hle) ι p hp i
  obtain ⟨hp1, hq1, hdeg, -, hSA, -, hanti⟩ := a
  have hc0 : 0 ≤ cZero (Fm.D x ι) ((i : ℕ) + 1) := Int.natCast_nonneg _
  have hgap : ∀ τ, 1 ≤ gap (uM p i τ) ((dat p i).p - 1) := fun τ =>
    one_le_gap_uMinus _ τ hp1 hq1 (hSA τ).1
  have hant0 : ∀ τ, Antitone (uM p i τ) := fun τ => by simpa using (hanti 0 (by norm_num) τ).1
  refine ⟨p.fw.laws, hp1, hq1, hdeg, ⟨by omega, i.2⟩, b.dom.2, hant0, hgap, fun s hs => ?_⟩
  obtain ⟨t, ht3, hts⟩ : ∃ t : ℕ, t ≤ 3 ∧ s + cZero (Fm.D x ι) ((i : ℕ) + 1) = (t : ℤ) * cZero (Fm.D x ι) ((i : ℕ) + 1) := by
    rcases hs with hs | hs | hs
    · exact ⟨0, by norm_num, by rw [hs]; ring⟩
    · exact ⟨1, by norm_num, by rw [hs]; ring⟩
    · exact ⟨2, by norm_num, by rw [hs]; ring⟩
  rw [laOf_add_smul (kc := (Fm.D x ι).R.k - 1) (c0 := cZero (Fm.D x ι) ((i : ℕ) + 1))]
  refine ⟨fun τ => antitone_add_par _ _ τ ?_, fun τ => ?_⟩
  · rw [hts]; exact (hanti t ht3 τ).1
  · rw [gap_add_smul_hodge _ _ _ τ hp1 hq1]
    have := hgap τ
    have h2 : 0 ≤ s + cZero (Fm.D x ι) ((i : ℕ) + 1) := by rw [hts]; positivity
    exact le_add_of_le_of_nonneg this h2
end GlobalTheory.CovTop.HodgeGapBounds
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealInExistsStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selected_realization_geometric_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (Γ : GeoP) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), p = _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none Γ → (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → ∀ (K : Ctx) (q : WPt p.s K), (∀ X : GlobalTheory.Mem.Stages, K.Over X.B.toPre → HostHyp X.toD7 ∧ X.toD7.host.F = maximalRealSubfield X.toD7.host.E ∧ (∀ i, IsFDiag (Wc X.toD7 i) ∧ IsFDiag (Vc X.toD7 i)) ∧ (∀ i, (Vc X.toD7 i).IsPosDef) ∧ (∀ j, Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.Y j) ∧ Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.V j) ∧ (1 ≤ j → j ≤ X.toD7.R.m → Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.W j))) ∧ Formalism.IndefR.Seed.FrmC.StdLat X.toD7.sp.X' ∧ (∀ i, (∀ a b, (Vc X.toD7 i).hT ((Vc X.toD7 i).frame a) ((Vc X.toD7 i).frame b) = if a = b then 1 else 0) ∧ (Vc X.toD7 i).L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range (Vc X.toD7 i).frame)) ∧ ((∀ a b, X.toD7.sp.X'.hT (X.toD7.sp.X'.frame a) (X.toD7.sp.X'.frame b) = if a = b then 1 else 0) ∧ X.toD7.sp.X'.L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range X.toD7.sp.X'.frame))) → GlobalTheory.CuspMult.MultEq q.x.what₂.r.z.R.toRealDat → ∀ (R : _root_.Formalism.L2.RecTAlt q.O.ex), _root_.GlobalTheory.Mem.Top.Bl.RecordCompatibleExtended q R → ∀ (sP : GlobalTheory.Mem.SRe.SPack (q.w.D q.Z) fun u => (R.T.cols.forms u).to0) (sS : GlobalTheory.Mem.SRe.SRest sP), HEq sP q.saturationAtWeightedPoint.P → HEq sS q.saturationAtWeightedPoint.S → ∀ (a : TwArgs q.O.ex q.x.what₂) (x : TwIn q.O.ex), HEq a.x x → ∀ (hin : ∀ u, Formalism.L2.SG.PoincareInHH.PoincareSetting.InHH (sS.toRealSpectralMatching R).X u (sS.toRealSpectralMatching R).Y.hK), HEq (x.F.Sp (zsOf x.R x.F)) (Formalism.IndefR.Cx.spOf (X := (sS.toRealSpectralMatching R).X) (twAt (q.w.D q.Z).what₂.embLL x.A3.A.v0) (x.F.Dc (zsOf x.R x.F)) (sS.toRealSpectralMatching R).Y.hK (sS.toRealSpectralMatching R).G x.wd (fun m => _root_.Formalism.IndefR.pwOf_alt (sS.toRealSpectralMatching R) hin (x.wd m)) x.bR) → ∀ (κ : ℝ) (sEEc : Tw (twAt (q.w.D q.Z).what₂.embLL x.A3.A.v0) x.R.HE.H →ₗ⋆[ℂ] Tw (twAt (q.w.D q.Z).what₂.embLL x.A3.A.v0) (Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX (sS.toRealSpectralMatching R).X)), HEq x.sEE sEEc → 0 < κ → (∀ (v : Tw (twAt (q.w.D q.Z).what₂.embLL x.A3.A.v0) x.R.HE.H) (hx : x.R.HE.e (Tw.out v) ∈ (x.R.toRealDat.EEat (x.R.toRealDat.levR x.F.lv2 true))), sEEc v = Tw.mk (twAt (q.w.D q.Z).what₂.embLL x.A3.A.v0) (((1 : ℂ) * (κ : ℂ)) • (Formalism.IndefR.AutomorphicEvaluation.sEEofTT (x.R.MY 0) x.R.ν0 x.R.fd0 (x.R.toRealDat.EEat (x.R.toRealDat.levR x.F.lv2 true)) (sS.toRealSpectralMatching R).X (sS.toRealSpectralMatching R).G (Formalism.L2.SG.RowsJoinPinned.iotaX sP.X sP.inst).toMulEquiv q.saturationAtWeightedPoint.t q.saturationAtWeightedPoint.c) ⟨x.R.HE.e (Tw.out v), hx⟩) ∧ RealDat.nP x.F.lv2 true * ‖sEEc v‖ ^ 2 = ‖v‖ ^ 2) → ∃ y : _root_.GlobalTheory.Mem.R3.RealInAlt x R (sS.toRealSpectralMatching R), HEq y.tS q.saturationAtWeightedPoint.t ∧ y.cS = q.saturationAtWeightedPoint.c ∧ HEq y.Sx (Formalism.IndefR.NX.ratDatR (D := (q.w.st q.Z).toD7) q.x.what₂.r.z.R q.x.what₂.r.z.cG q.core_data_of_point.row.kKs q.core_data_of_point.row.hk) ∧ HEq y.nexp.eF q.core_data_of_point.row.nexp.eF ∧ HEq y.nexp.fi q.core_data_of_point.row.nexp.fi ∧ y.uS = 1 := by
  first | exact @_root_.GlobalTheory.Mem.R3.SelRealIn.realIn_exists_alt | exact _root_.GlobalTheory.Mem.R3.SelRealIn.realIn_exists_alt | (intros; apply _root_.GlobalTheory.Mem.R3.SelRealIn.realIn_exists_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPinsOfSeeAtStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPins_of_bWit_third_place_series : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → _root_.Formalism.IndefR.IndefiniteRealisationNormalisation b.B.Q := by
  first | exact @_root_.GlobalTheory.Fam.realPins_bundle_of_bWit | exact _root_.GlobalTheory.Fam.realPins_bundle_of_bWit | (intros; apply _root_.GlobalTheory.Fam.realPins_bundle_of_bWit <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RecValPackB
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Matrix
noncomputable section
namespace GlobalTheory.TopVal.OneForm
section Generic
variable {D : D7} {O : Obj D} {c : ℝ}
set_option maxHeartbeats 800000 in
theorem row_of_btw_alt (b : _root_.GlobalTheory.Fc.BundleCondition D O c) (x : R3.TwIn O.ex) (y : _root_.GlobalTheory.Mem.Top.Bl.TwistedBundle b x) (t : (_root_.GlobalTheory.Fam.packB_alt b).P.T)
    (F : Fin (((_root_.GlobalTheory.Fam.packB_alt b).P.A3.side3 (_root_.GlobalTheory.Fam.packB_alt b).P.Ps (_root_.GlobalTheory.Fam.packB_alt b).P.ψs (_root_.GlobalTheory.Fam.packB_alt b).P.Zs).nV t) → D.what₂.LL)
    (F' : Fin (((_root_.GlobalTheory.Fam.packB_alt b).Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace (_root_.GlobalTheory.Fam.packB_alt b)).zs).Df1.nV t) → D.what₂.LL) (hF : HEq F F') :
    ∃ (s : x.T) (v : Fin (rDim D x.A3.A x.F.P1 x.F.ψ1 s) → D.what₂.LL), (_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t = x.Y.tup s ∧
      HEq ((_root_.GlobalTheory.Fam.packB_alt b).Q.F.eV (_root_.GlobalTheory.MiS.packageCoefficientSpace (_root_.GlobalTheory.Fam.packB_alt b)).zs t F') (R3.rowForm x.A3.A x.F.P1 x.F.ψ1 s v) ∧
      HEq ((_root_.GlobalTheory.Fam.packB_alt b).P.I.jA t ((rV0 D (_root_.GlobalTheory.Fam.packB_alt b).P.A3.A (_root_.GlobalTheory.Fam.packB_alt b).P.Ps (_root_.GlobalTheory.Fam.packB_alt b).P.ψs t).mulVec F)) (x.Y.jA s v) := by
  have key : ∀ k : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S, k = _root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput y.y → ∀ (t : k.P.T)
      (F : Fin ((k.P.A3.side3 k.P.Ps k.P.ψs k.P.Zs).nV t) → D.what₂.LL)
      (F' : Fin ((k.B.Q.F.fc (k.B.Q.Rl.toCx3 k.B.Q.F).zs).Df1.nV t) → D.what₂.LL), HEq F F' →
      ∃ (s : x.T) (v : Fin (rDim D x.A3.A x.F.P1 x.F.ψ1 s) → D.what₂.LL), k.P.I.tup t = x.Y.tup s ∧
        HEq (k.B.Q.F.eV (k.B.Q.Rl.toCx3 k.B.Q.F).zs t F') (R3.rowForm x.A3.A x.F.P1 x.F.ψ1 s v) ∧
        HEq (k.P.I.jA t ((rV0 D k.P.A3.A k.P.Ps k.P.ψs t).mulVec F)) (x.Y.jA s v) := by
    intro k hk
    subst hk
    intro t F F' hF
    have e : F = F' := eq_of_heq hF
    subst e
    refine ⟨t, (rV0 D x.A3.A x.F.P1 x.F.ψ1 t).mulVec F, rfl, heq_of_eq ?_, HEq.rfl⟩
    have hOk := y.intersectionNumber_baseChange.ok
    have hb : BlockHyp (x.A3.A.fam.R t) (x.A3.A.fam.lvl x.F.P1 x.F.ψ1) x.A3.A.fam.v0 1 :=
      ⟨hOk.ok2.conj, hOk.ok2.irr, hOk.ok2.what₂ t⟩
    have key := BlockDat.lf_lvl_vE hb
    unfold R3.rowForm rV0
    show (x.A3.A.fam.R t).S.basis.equivFun.symm (((x.A3.A.fam.R t).vE (x.A3.A.fam.lvl x.F.P1 x.F.ψ1)) *ᵥ F) = _
    congr 1
    conv_lhs => rw [← key]
    rw [Matrix.mul_assoc]
    exact (Matrix.mulVec_mulVec _ _ _).symm
  exact key (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b) y.eq t F F' hF
end Generic
section Rows
open GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.Bl
end Rows
set_option maxHeartbeats 800000 in
theorem exists_frm_isRes_recVal {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) (x : R3.TwIn q.O.ex)
    (a : R3.TwArgs q.O.ex q.x.what₂) (ax : HEq a.x x) (rx : Bl.RXs q.x.what₂) (s : x.T)
    (v : Fin (rDim (q.w.D q.Z) x.A3.A x.F.P1 x.F.ψ1 s) → (q.w.D q.Z).what₂.LL) :
    ∃ φ : Frm q.w.I (x.Y.tup s), IsRes φ (R3.rowForm x.A3.A x.F.P1 x.F.ψ1 s v) ∧
      ∀ u, RecVal (I := q.w.I) (l := q.w.l) (Z := q.Z) u (x.Y.tup s) φ (x.Y.jA s v) := by
  have e : a.x = x := eq_of_heq ax
  subst e
  obtain ⟨s', v', k1, k2, k3⟩ := row_of_args (w := q.w) (Z := q.Z) (ex := q.O.ex) (t := q.x.what₂) a s v
  exact one_form_congr (I := q.w.I) (l := q.w.l) (Z := q.Z) k1 k2 k3 (one_form_rows rx s' v')
set_option maxHeartbeats 800000 in
theorem recVal_packB_alt : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → Nonempty (Bl.RXs q.x.what₂) → ∀ (t : (_root_.GlobalTheory.Fam.packB_alt b).P.T) (F : Fin (((_root_.GlobalTheory.Fam.packB_alt b).P.A3.side3 (_root_.GlobalTheory.Fam.packB_alt b).P.Ps (_root_.GlobalTheory.Fam.packB_alt b).P.ψs (_root_.GlobalTheory.Fam.packB_alt b).P.Zs).nV t) → (q.w.D q.Z).what₂.LL) (F' : Fin (((_root_.GlobalTheory.Fam.packB_alt b).Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace (_root_.GlobalTheory.Fam.packB_alt b)).zs).Df1.nV t) → (q.w.D q.Z).what₂.LL), HEq F F' → ∃ φ : GlobalTheory.TopVal.Frm q.w.I ((_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t), GlobalTheory.TopVal.IsRes φ ((_root_.GlobalTheory.Fam.packB_alt b).Q.F.eV (_root_.GlobalTheory.MiS.packageCoefficientSpace (_root_.GlobalTheory.Fam.packB_alt b)).zs t F') ∧ ∀ u, GlobalTheory.TopVal.RecVal (I := q.w.I) (l := q.w.l) (Z := q.Z) u ((_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t) φ ((_root_.GlobalTheory.Fam.packB_alt b).P.I.jA t ((rV0 (q.w.D q.Z) (_root_.GlobalTheory.Fam.packB_alt b).P.A3.A (_root_.GlobalTheory.Fam.packB_alt b).P.Ps (_root_.GlobalTheory.Fam.packB_alt b).P.ψs t).mulVec F)) := by
  intro hL p K q c b hb hR t F F' hF
  obtain ⟨rx⟩ := hR
  obtain ⟨s, v, h1, h2, h3⟩ := _root_.GlobalTheory.TopVal.OneForm.row_of_btw_alt b hb.x hb.y t F F' hF
  exact one_form_congr (I := q.w.I) (l := q.w.l) (Z := q.Z) h1 h2 h3 (_root_.GlobalTheory.TopVal.OneForm.exists_frm_isRes_recVal q hb.x hb.a hb.ax rx s v)
end GlobalTheory.TopVal.OneForm
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowEBigGapStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bigGap_of_isGoodE_isLinked : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ D _ _ _ => GlobalTheory.Core.Rk.BigGap D) := by
  first | exact @_root_.GlobalTheory.Core.Rk.GapAt.rowE_bigGap_alt | exact _root_.GlobalTheory.Core.Rk.GapAt.rowE_bigGap_alt | (intros; apply _root_.GlobalTheory.Core.Rk.GapAt.rowE_bigGap_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowEDcPtLinkedStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linkedAt_hDcPtG_prmR : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.R1.SlotDecompositionPointCondition := by
  first | exact @_root_.GlobalTheory.Fc.RL.linkedAt_hDcPtG | exact _root_.GlobalTheory.Fc.RL.linkedAt_hDcPtG | (intros; apply _root_.GlobalTheory.Fc.RL.linkedAt_hDcPtG <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowEHasTie
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fc.TieOfLink
theorem tie_of_rpk_alt {D : D7} {O : Obj D} {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition D O c) {x : TwIn O.ex} (y : _root_.GlobalTheory.Mem.R3.RealInAlt x b.R b.S) (r : _root_.GlobalTheory.Mem.R3.RecursiveInput y)
    (e : _root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b = _root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput y)
    (hpsi : PsiPPTie D (divisionPairOfAdelicFormsFaceColumnsData x).P0 (divisionPairOfAdelicFormsFaceColumnsData x).ψ0 (divisionPairOfAdelicFormsFaceColumnsData x).Ps (divisionPairOfAdelicFormsFaceColumnsData x).ψs (divisionPairOfAdelicFormsFaceColumnsData x).I.eG)
    (h3 : _root_.Formalism.IndefR.IndefiniteRealisationNormalisationDegreeThree (_root_.GlobalTheory.Mem.R3.realisationOfInput y)) (hp : ∃ pins : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation (_root_.GlobalTheory.Mem.R3.realisationOfInput y), _root_.Formalism.IndefR.IndefiniteRealisationCompatible pins (_root_.GlobalTheory.Mem.R3.realisationRecursionOfInput r)) :
    Nonempty b.Comparison₂ := by
  have key : ∀ z : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S, z = _root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput y → ∃ Rr : _root_.Formalism.IndefR.IndefiniteRealisationRecursion z.B.Q, PsiPPTie D z.P.P0 z.P.ψ0 z.P.Ps z.P.ψs z.P.I.eG ∧
      _root_.Formalism.IndefR.IndefiniteRealisationNormalisationDegreeThree z.B.Q ∧ ∃ pins : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation z.B.Q, _root_.Formalism.IndefR.IndefiniteRealisationCompatible pins Rr := by
    rintro z rfl
    exact ⟨_root_.GlobalTheory.Mem.R3.realisationRecursionOfInput r, hpsi, h3, hp⟩
  obtain ⟨Rr, h⟩ := key _ e
  exact ⟨⟨Rr, h⟩⟩
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx}
theorem nonempty_tie_of_wit (q : WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c) (w : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b)
    (hF0 : HEq (w.a.Zsc (zsOf q.x.what₂.r.z.R q.x.what₂.r.z.F)).F0 (F0K K.s (q.w.D q.Z)))
    (hp : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation (_root_.GlobalTheory.Mem.R3.realisationOfInput w.y.y))
    (hloc : _root_.Formalism.IndefR.principalLevelFrame.RowLocPinAlt b.R.T.n.gal.lp w.x.R.θ w.x.Y.PY (w.x.R.MY 0)
      (fun b => levS _ (w.x.R.βY 0) (w.x.R.dat0 (w.x.R.toRealDat.levR w.x.F.lv2 b)))
      (fun b => Formalism.IndefR.Lev.levChi _ (w.x.R.βY 0) (w.x.R.dat0 (w.x.R.toRealDat.levR w.x.F.lv2 b))) (fun _ => w.x.R.e0) w.x.Y.eFT) :
    Nonempty b.Comparison₂ := by
  have hI := _root_.GlobalTheory.T.recursion_local_row_condition_alt _ _ _ _ _ _ _ _ q.O.ex w.x b.R b.S w.y.y w.y.r
  have h3 : _root_.Formalism.IndefR.IndefiniteRealisationNormalisationDegreeThree (_root_.GlobalTheory.Mem.R3.realisationOfInput w.y.y) := by
    obtain ⟨x, a, ax, y⟩ := w
    cases ax
    exact _root_.GlobalTheory.Mem.R3.realPins3_realTOf_alt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ q.x.what₂ a b.R b.S y.y hF0
  exact _root_.GlobalTheory.Fc.TieOfLink.tie_of_rpk_alt b w.y.y w.y.r w.y.eq hI.2.2 h3 ⟨hp, hI.1 hp hloc⟩
theorem hasTie_of_linked {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) (Q : V4.Slot) :
    RowE Q (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) fun _ => _root_.GlobalTheory.Fc.HasCompatibility := by
  have hH := EvP.of_ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev
  refine ((((((_root_.GlobalTheory.T.bWit_zsc_F0_heq_F0K_local_of_sc_eq hL p).and (_root_.GlobalTheory.T.bWit_C_eq_cf_of_sc_eq hL p)).and (_root_.GlobalTheory.T.bWit_Pg_eq_image_plMap_of_sc_eq hL p)).and (_root_.GlobalTheory.T.theta_level_conjugate_character_alt hL p)).and (_root_.GlobalTheory.T.local_level_character_pin_of_witness hL p)).and hH).mono
    fun κ K _ h β _ c b hl => ?_
  obtain ⟨⟨⟨⟨⟨h0, hc⟩, hg⟩, ht⟩, hl'⟩, hh⟩ := h
  obtain ⟨q, b', ⟨w⟩, e⟩ := hl
  have eO : (⟨β.D, β.O⟩ : Σ D : D7, Obj D) = ⟨q.w.D q.Z, q.O⟩ := congrArg (fun s => (⟨s.1, s.2.1⟩ : Σ D : D7, Obj D)) e
  have hsc : q.O.L.sc = K.s := by
    have := congrArg (fun s : Σ D : D7, Obj D => s.2.L.sc) eO
    exact this.symm.trans β.sc
  have hfd := (hh (q.w.st q.Z) q.x.isOver).2.2.1
  have hp : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation (_root_.GlobalTheory.Mem.R3.realisationOfInput w.y.y) :=
    _root_.GlobalTheory.Mem.R3.realPins_realTOf_alt _ _ _ _ _ _ _ _ q.O.ex w.x b'.R b'.S w.y.y (hc q c b' w hsc) hfd (hg q c b' w hsc)
      (ht q c b' w hsc).1 (ht q c b' w hsc).2.1 (ht q c b' w hsc).2.2
  have h' : _root_.GlobalTheory.Fc.HasCompatibility _ _ c b' := _root_.GlobalTheory.Fc.TieOfLink.nonempty_tie_of_wit q b' w (h0 q c b' w hsc) hp (hl' q c b' w hsc)
  have tr : ∀ s : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Fc.BundleCondition D O c, s = ⟨q.w.D q.Z, q.O, b'⟩ → _root_.GlobalTheory.Fc.HasCompatibility s.1 s.2.1 c s.2.2 := by
    rintro s rfl; exact h'
  exact tr _ e
end GlobalTheory.Fc.TieOfLink
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RunModelArch
section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open GlobalTheory.RunJoin
namespace GlobalTheory.ShareOn
section Model
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
end Model
section Run
end Run
section Point
open Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem p0_extreme_or_archOn_of_runModel : _root_.GlobalTheory.BigOn.ForallTwoRuns fun Fm x hx ι p r h => ∀ (i : Fin (Fm.D x ι).R.m) (C : Type) [Finite C]
    [MulAction p.P.Gp C] (M : TwoLevels (Fm.D x ι).host.E (Fm.D x ι).R.r p.P.Gp C) (ka : Wt M.Ψ (Fm.D x ι).R.r),
    RunModel p r h i M ka → (M.p0 = 0 ∨ M.p0 = (Fm.D x ι).R.r) ∨
      (0 < M.p0 ∧ M.p0 < (Fm.D x ι).R.r ∧ ArchOn M ka (Fm.parT x hx ι).TO) := by
  obtain ⟨x₀, hrun⟩ := GlobalTheory.FinalJoin.runHolds_of_parOK
  obtain ⟨CK, hCK⟩ := GlobalTheory.FinalJoin.RecordRun.exists_pageRun_record_sub_four
  obtain ⟨x₂, hpg⟩ := GlobalTheory.FinalJoin.pageOK_of_pageRun_beyond (fun _ _ => 0)
  refine Formalism.MainNotions.Closed.imp (GlobalTheory.T.runNumericalConditions_hold_along_family (max ((10 : ℝ) ^ 60) (max (x₀ 20 CK) (x₂ 20 CK)))) ?_
  intro eps Fm CH _ hx0
  obtain ⟨x0, hx0⟩ := hx0
  refine ⟨x0, fun x hx hle ι p _ hmore r hr hown i C _ _ M ka hRM => ?_⟩
  obtain ⟨⟨S, hCnW, hg, hC, hCZ, hxl⟩, -⟩ := hx0 x hx hle ι
  obtain ⟨-, hcore, -⟩ := hmore
  obtain ⟨v, e, hXc, hkaC, -⟩ := hRM
  have hl := hr.laws v
  have hj : InR (Fm.D x ι) ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hinj := hcore.inj
  have hpar : ∀ j, InR (Fm.D x ι) j → ParOK (r.used v).full.toTop (Fm.ex x hx ι).errX (ownAt (Fm.D x ι) v) j :=
    GlobalTheory.FinalJoin2.liftIndexParameterConditions_of_coreAndShortLaws _ p.T _ _ _ hl.j hl.p hl.sh rfl hcore.canon (hcore.fieldAt v) hcore.halfEX
      (fun j hj n => ⟨hl.lvA j hj n, hown v j n hj⟩)
  have hO := (GlobalTheory.FinalJoin2.fieldSmall_iff_opo (Fm.D x ι) _ hl.p (Fm.L x ι)).1 hcore.small
  have hP := hCK (Fm.D x ι) (Fm.L x ι) _ (Fm.parT x hx ι) (Fm.ex x hx ι).kap_def S hCnW hg
    ((le_max_left _ _).trans hxl) hC hCZ _ _ _ (recPJ hl.p ((i : ℕ) + 1) hj) hj hO
  have hHC := (hrun (Fm.D x ι) _ hl.p hinj _ _ hpar ((i : ℕ) + 1) hj (Fm.L x ι) _ _ _ _ _ _ _ _ _ _ _ hP
    (((le_max_left _ _).trans (le_max_right _ _)).trans hxl)).2.1
  have hOK := (hpg (Fm.D x ι) _ _ ((i : ℕ) + 1) (recPJ hl.p ((i : ℕ) + 1) hj) (Fm.L x ι) _ _ _ _ _ _ _ _ _ _ _ hj hP
    (((le_max_right _ _).trans (le_max_right _ _)).trans hxl)).1
  have hwd := fun k => GlobalTheory.Shares.WtDic.weights_dictionary (Fm.D x ι) (r.used v).full.toTop hl.p ((i : ℕ) + 1) hj k
  haveI : Nonempty C := ⟨e.symm ((r.used v).full.toTop.dict ((i : ℕ) + 1) (r.used v).full.toTop.σ₀ 1).1⟩
  obtain ⟨c0⟩ := ‹Nonempty C›
  have hp0M : M.p0 = ((Fm.D x ι).R.sigW ((i : ℕ) + 1)).2 :=
    (M.comp_basePoint c0).symm.trans ((congrArg Data.p0 (hXc c0)).trans (hwd (e c0)).2.2.2.2.2.1)
  have hq : ((Fm.D x ι).R.sigW ((i : ℕ) + 1)).2 = (Fm.D x ι).R.m - ((i : ℕ) + 1) := rfl
  have hr : (Fm.D x ι).R.r = (Fm.D x ι).R.k + (Fm.D x ι).R.m - 1 := rfl
  have hk := (Fm.D x ι).R.m_add_three_le_k
  by_cases hjm : (i : ℕ) + 1 < (Fm.D x ι).R.m
  swap
  · left; left; rw [hp0M, hq]; omega
  right
  refine ⟨by rw [hp0M, hq]; omega, by rw [hp0M, hq, hr]; omega, ?_⟩
  have hκ : p.κ i = kaR (Fm.parT x hx ι) (Fm.ex x hx ι).kap_def ((i : ℕ) + 1) :=
    GlobalTheory.BigOn.eq_kaR _ _ i (p.κ i) (fun τ => ((fw2 p).kap i τ).1) (fun τ => ((fw2 p).kap i τ).2.1)
      ((fw2 p).kap i (GlobalTheory.RunDepth.plOf _ (false, Classical.arbitrary _))).2.2
  have hΨ : M.Ψ = (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c0)).Ψ :=
    (M.comp_Ψ c0).symm.trans (congrArg Data.Ψ (hXc c0))
  have hcard : M.Ψ.card = (Fm.D x ι).R.f := by rw [hΨ]; exact (hwd (e c0)).2.2.2.2.2.2.1
  have hr1 : 1 ≤ (Fm.D x ι).R.r := by rw [hr]; omega
  have hdim : WeightFamilies.dimY (Fm.D x ι) ((i : ℕ) + 1) = M.dimY := by
    unfold TwoLevels.dimY
    rw [hcard]
    have h2 := GlobalTheory.ArchInputs.two_mul_dimY _ hj
    have h3 : ((2 * WeightFamilies.dimY (Fm.D x ι) ((i : ℕ) + 1) : ℕ) : ℝ) =
        (((Fm.D x ι).R.f * ((Fm.D x ι).R.r * ((Fm.D x ι).R.r - 1)) : ℕ) : ℝ) := by
      push_cast [Nat.cast_sub hr1]
      linarith
    have h4 : 2 * WeightFamilies.dimY (Fm.D x ι) ((i : ℕ) + 1) = (Fm.D x ι).R.f * ((Fm.D x ι).R.r * ((Fm.D x ι).R.r - 1)) :=
      by exact_mod_cast h3
    obtain ⟨t, ht⟩ := Nat.even_mul_pred_self (Fm.D x ι).R.r
    rw [ht] at h4 ⊢
    rw [show (t + t) / 2 = t by omega]
    rw [mul_add] at h4
    linarith
  refine archOn_of_comps M ka (fun k => ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X k) e hXc
    (fun k => laR (r.used v).full.toTop ((i : ℕ) + 1) (p.κ i) k)
    (fun k => laR (r.used v).full.toTop ((i : ℕ) + 1) (lR (Fm.parT x hx ι) (Fm.ex x hx ι).kap_def ((i : ℕ) + 1)) k)
    (fun k => laR (r.used v).full.toTop ((i : ℕ) + 1) (fR (Fm.parT x hx ι) (Fm.ex x hx ι).kap_def ((i : ℕ) + 1)) k)
    (Fm.parT x hx ι).TO _ hdim hkaC (fun k => ?_) (fun k k' τ h h' a => ?_) (fun k k' τ h h' a => ?_)
    (fun k => run_weight_arch _ _ hl.p _ hj _ _ _ _ _ _ _ _ _ _ _ _ _ hOK.hyp hjm k)
    (fun k => archOne_of_run _ _ hl.p hinj _ _ _ hj _ _ _ _ _ _ _ _ _ _ _ _ _ (hpar _ hj) hOK hHC hjm k)
  · show laR _ _ (p.κ i) k = _
    rw [hκ, ← (GlobalTheory.SharesDefinite.weight_and_degree hOK.hyp).1]
    exact (hwd k).2.2.1 _ _ _
  · simp only [GlobalTheory.Shares.laR, Formalism.L2.Pj.laU, (hwd k).2.2.2.2.2.1, (hwd k').2.2.2.2.2.1]
  · simp only [GlobalTheory.Shares.laR, Formalism.L2.Pj.laU, (hwd k).2.2.2.2.2.1, (hwd k').2.2.2.2.2.1]
end Point
end GlobalTheory.ShareOn
end
end
end

