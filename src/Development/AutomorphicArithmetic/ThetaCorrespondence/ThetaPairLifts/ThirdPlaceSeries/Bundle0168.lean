import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0819
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0133
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0027
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0017
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0024
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0166
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0822
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0123
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0128
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0033
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0067
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0030
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0035
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0037
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0031
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0032
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0093
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0149
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0044
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0145
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0040
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0167
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0146
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0029
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0045
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealTB
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0013
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0062
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0140
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0161
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0163
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3151
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0048
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0064
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0057
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0082
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualCompatibleRows
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.IsPotCrysAtOfMono0
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0154
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0126
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3169
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0092
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0074
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0109
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0611
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0141
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0159
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0153

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BlockTriAtStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.central_frame_split_place_nontrivial_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t _ _ c =>
  ∀ (ad : MtAd t.r.Y c.a.all.gal.mt) (i : (w.st Z).toD7.nd.Loc) s (k : Fin (w.st Z).toD7.R.m), t.r.Y.tup s = (w.st Z).toD7.nd.mu i →
    Nontrivial ((w.st Z).toD7.what₂.Mt (t.r.Y.tup s) ((k : ℕ) + 1)) →
    ∀ (s' : ReciprocityTheory.Aut.SplitPlace (w.st Z).toD7.host.E) (φ : GlobalTheory.CenFrame.Os s' →+* Formalism.L2.DIV.kP s'.w)
      (b : GL (Fin (w.st Z).toD7.R.nV) (Formalism.L2.DIV.kP s'.w)), s'.w ∈ t.r.z.R.Pg → GlobalTheory.CenFrame.IsResidue s' φ →
        GlobalTheory.CenFrame.FrameRed (GlobalTheory.FrameBlockDiagonal.rankV (w.st Z).toD7 k) (ad.PV k) (t.r.z.R.βV k) s' φ b →
        b ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 (w.st Z).toD7.R.r) := by
  first | exact @_root_.GlobalTheory.FrameBlockTriangular.blockTri_at_alt | exact _root_.GlobalTheory.FrameBlockTriangular.blockTri_at_alt | (intros; apply _root_.GlobalTheory.FrameBlockTriangular.blockTri_at_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BwitExists
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem.R3
namespace GlobalTheory.Mem.R3.SelAll
theorem rpk_eq_alt {D : D7} {O : Obj D} {R : _root_.Formalism.L2.RecTAlt O.ex} {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R} (P : Formalism.L2.Rows.RowSideFamily O.ex)
    {Dc Dc' : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)} {Sp : ∀ Zs, SPer (Dc Zs)} {Sp' : ∀ Zs, SPer (Dc' Zs)}
    {Z Z' : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3} {B : _root_.Formalism.IndefR.RealTBAlt R P Dc Sp Z S} {B' : _root_.Formalism.IndefR.RealTBAlt R P Dc' Sp' Z' S}
    (h1 : Dc = Dc') (h2 : HEq Sp Sp') (h3 : Z = Z') (h4 : HEq B B') :
    (⟨P, Dc, Sp, Z, B⟩ : _root_.GlobalTheory.Mem.Top.Bl.RealPackage R S) = ⟨P, Dc', Sp', Z', B'⟩ := by
  subst h1; subst h3; cases h2; cases h4; rfl
theorem real_tb_congr_of_heq {D : D7} {O : Obj D} (R : _root_.Formalism.L2.RecTAlt O.ex) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R) (P : Formalism.L2.Rows.RowSideFamily O.ex)
    {Dc Dc' : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)} {Sp : ∀ Zs, SPer (Dc Zs)} {Sp' : ∀ Zs, SPer (Dc' Zs)}
    {Z Z' : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
    (h1 : Dc = Dc') (h2 : HEq Sp Sp') (h3 : Z = Z') :
    _root_.Formalism.IndefR.RealTBAlt R P Dc Sp Z S = _root_.Formalism.IndefR.RealTBAlt R P Dc' Sp' Z' S := by
  subst h1; subst h3; cases h2; rfl
set_option maxHeartbeats 4000000 in
theorem bwit_exists_alt : GlobalTheory.Published.GreenCuspidal → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (Γ : GeoP) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), p = _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none Γ → (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → (GlobalTheory.Fc.EvP fun _ K => ∀ q : WPt p.s K, GlobalTheory.CuspMult.MultEq q.x.what₂.r.z.R.toRealDat) → GlobalTheory.Fc.EvP fun _ K => ∀ (q : WPt p.s K) (R : _root_.Formalism.L2.RecTAlt q.O.ex), _root_.GlobalTheory.Mem.Top.Bl.RecordCompatibleExtended q R → ∀ (c : ℝ) (_ : {n : ℕ × ℕ // (q.w.D q.Z).s.Del = (n.1 : ℚ) ∧ q.O.L.etaSz = ((q.w.D q.Z).R.m : ℝ) * (n.2 : ℝ)}), q.O.L.sc = K.s → Val K.C K.cD K.ch q.O.L → ∃ b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c, b.R = R ∧ Nonempty (_root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b) := by
  intro hG hDC hHM hCW hW hDS hHC hCR hGAR hRF hL N Γ p hp hN hM
  refine ((GlobalTheory.Fc.EvP.of_ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev).and hM).mono ?_
  rintro κ K - ⟨hH, hMK⟩ q R hR c DH _ _
  have hMq := hMK q
  have hcols : R.T.cols = q.x.col.C := hR.s.cols
  obtain ⟨sP, sS, hP, hS⟩ : ∃ (sP : GlobalTheory.Mem.SRe.SPack (q.w.D q.Z) fun u => (R.T.cols.forms u).to0) (sS : GlobalTheory.Mem.SRe.SRest sP),
      HEq sP q.saturationAtWeightedPoint.P ∧ HEq sS q.saturationAtWeightedPoint.S := by
    rw [hcols]; exact ⟨q.saturationAtWeightedPoint.P, q.saturationAtWeightedPoint.S, HEq.rfl, HEq.rfl⟩
  have hin : ∀ u, Formalism.L2.SG.PoincareInHH.PoincareSetting.InHH (sS.toRealSpectralMatching R).X u (sS.toRealSpectralMatching R).Y.hK := sP.fin.inHH
  obtain ⟨a, x, ax, C, hDc, hSp, hW', hXg, hCP, hZ, hsp, κS, sEEc, hsE, hκ, hsee⟩ :=
    _root_.GlobalTheory.T.exists_selected_realization_alt hDC hHM hCW hW hDS hHC hCR hGAR hRF hL N Γ p hp hN K q hH hMq R hR sP sS hP hS DH.1.1 DH.1.2 c hin
  obtain ⟨y, hyt, hyc, hySx, hyeF, hyfi, hyu⟩ := _root_.GlobalTheory.T.selected_realization_geometric_alt hDC hHM hCW hW hDS hHC hCR hGAR hRF hL N Γ p hp hN K q hH hMq R hR sP sS hP hS a x ax hin hsp κS sEEc hsE hκ hsee
  obtain ⟨r, hr⟩ := _root_.GlobalTheory.T.selected_realization_side_alt hG hDC hHM hCW hW hDS hHC hCR hGAR hRF hL N Γ p hp hN K q hH hMq R hR sP sS hP hS a x ax y
  have pin := _root_.GlobalTheory.T.selected_lower_map_holds_alt hDC hHM hCW hW hDS hHC hCR hGAR hRF hL N Γ p hp hN K q hH hMq R hR sP sS hP hS a x ax
  obtain ⟨HD, hHD⟩ := _root_.GlobalTheory.HostDatumExists.exists_hostDatum_alt hGAR _ _ _ _ _ _ _ _ q.O.ex R.T.toTiedDataS (GlobalTheory.Mem.Top.Bl.hostPins_wpt hRF _ _ q) q.x.pin.d3b
  have side := _root_.GlobalTheory.T.selected_side_realization_holds_alt hDC hHM hCW hW hDS hHC hCR hGAR hRF hL N Γ p hp hN K q hH hMq R hR sP sS hP hS a x ax y r HD hHD
  have h1 : C.c.face = x.F.Dc := eq_of_heq hDc
  have h3 : GlobalTheory.Fc.zsc (divisionPairOfAdelicFormsFaceColumnsData x) DH.1.1 DH.1.2 c = x.F.Zsc := hZ.symm
  have hB := _root_.GlobalTheory.Mem.R3.SelAll.real_tb_congr_of_heq R (sS.toRealSpectralMatching R) (divisionPairOfAdelicFormsFaceColumnsData x) h1 hSp h3
  have hx : Holds x.R x.F := by
    have e : a.x = x := eq_of_heq ax
    rw [← e]; exact a.intersectionNumber_baseChange
  let b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c := ⟨R, sS.toRealSpectralMatching R, divisionPairOfAdelicFormsFaceColumnsData x, pin, DH, C, cast hB.symm (_root_.GlobalTheory.Mem.R3.boundedRealisationOfInput y)⟩
  have heq : _root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b = _root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput y := _root_.GlobalTheory.Mem.R3.SelAll.rpk_eq_alt (divisionPairOfAdelicFormsFaceColumnsData x) h1 hSp h3 (cast_heq _ _)
  exact ⟨b, rfl, ⟨{ x := x, a := a, ax := ax, y := ⟨hx, y, r, heq, HD⟩, recPin := hR, s := ⟨sP, sS, hP, hS, rfl⟩, pt := ⟨hyt, hyc⟩, sx := hySx, eF := hyeF, fi := hyfi, uS := hyu, parts := hr, cW := ⟨hW', hXg⟩, d3b := heq_of_eq hHD, side := side, colPins := hCP }⟩⟩
end GlobalTheory.Mem.R3.SelAll
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoveringMinGenusBound
section
set_option synthInstance.maxHeartbeats 200000

section
section
set_option synthInstance.maxHeartbeats 400000
open NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.AllWt GlobalTheory.LevDesc
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
namespace GlobalTheory.CovGminTop
section Abstract
variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
variable [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
end Abstract
section Point
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
end Point
theorem covering_gmin_of_gram_deep_size : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.MinimalGenerator := by
  intro hP hGr hDG hS
  obtain ⟨C, hC, hg⟩ := _root_.GlobalTheory.T.exists_good_cover_at_minimal_level hP
  refine Closed.imp (((_root_.GlobalTheory.T.weight_parameter_strict_antitone_alt hS).and (_root_.GlobalTheory.T.size_bounds_for_family_alt hS)).and ((_root_.GlobalTheory.T.exists_psi_isTypeLevel_latDeep_eq_latN hP hGr hDG).and hDG)) ?_
  rintro eps Fm CH - ⟨⟨⟨_, -, h1⟩, _, -, h2⟩, ⟨_, -, h3⟩, _, -, h4⟩
  obtain ⟨x1, h5⟩ := GlobalTheory.family_sizes_eventually_large eps Fm (C + 45)
  obtain ⟨x0, h⟩ := (h1.and h2).and (h3.and h4)
  refine ⟨0, le_rfl, max x0 x1, fun x hx hle ι p hp i hi Y hY => ?_⟩
  obtain ⟨⟨a1, a2⟩, a3, a4⟩ := h x hx ((le_max_left _ _).trans hle) ι p hp
  obtain ⟨b1, b2, b3, -⟩ := a1 i hi
  obtain ⟨c1, c2, c3, c4, c5, c6, -, -, c7, c8, -, c9, c10, -⟩ := a2 i hi Y hY
  obtain ⟨fr, ψ, -, d1, d2, d3⟩ := a3 i hi Y hY
  have hL := (h5 x ((le_max_right _ _).trans hle) ι).2.2.1
  have hn : 8 * (Fm.D x ι).R.f * (Fm.D x ι).R.r + 4 ≤ (p.κ i).n := by
    rw [WtShape.cols_eq]; exact (Fm.parT x hx ι).nV_ge
  obtain ⟨s, e1, e2, e3⟩ := hg _ p.T c1 _ b1 b2 b3 c2 Y _ _ hY.1 _ c3 c4 c5 c6 le_rfl (wtA (p.κ i)) (p.κ i).n
    (dom_wtA _) (p.κ i).n_even hn (half_lt_laOf p i) (c9.trans (by linarith))
  obtain ⟨k1, k2⟩ := GlobalTheory.LevelIsometry.keeps_cusp_lattice_norm _ p.T c1 _ b1 b2 b3 c2 Y _ _ hY.1 (Gk p i)
    ((Int.even_coe_nat _).2 (p.κ i).n_even)
  refine gminAt_of_gens p i Y (by omega) d1.coprime k1 k2 (a4 i hi Y hY).1 _ _ d2 s e1 e2 _ _ (fun y hy σ => (e3 y hy σ).1)
    (num_step hC (hL.trans ?_) (one_le_kap p i b1) c10 d3)
  have f1 : (1 : ℝ) ≤ (Fm.D x ι).R.f := by exact_mod_cast (by omega : 1 ≤ (Fm.D x ι).R.f)
  have f2 : (1 : ℝ) ≤ (Fm.D x ι).R.r := by exact_mod_cast (by omega : 1 ≤ (Fm.D x ι).R.r)
  exact le_mul_of_one_le_left (by linarith) (one_le_mul_of_one_le_of_one_le f1 f2)
end GlobalTheory.CovGminTop
end
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covering_gmin_of_prints_gram_deep_size : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.MinimalGenerator := by
  first | exact @_root_.GlobalTheory.CovGminTop.covering_gmin_of_gram_deep_size | exact _root_.GlobalTheory.CovGminTop.covering_gmin_of_gram_deep_size | (intros; apply _root_.GlobalTheory.CovGminTop.covering_gmin_of_gram_deep_size <;> assumption)
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EvWPRowsOfRows
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Top GlobalTheory.Fc
namespace GlobalTheory.Fc.Ind
theorem evW_pRows_of_rows_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → ∀ (𝒜 : FamClass) (τ : RawSel _root_.GlobalTheory.Fc.Ind.PointSummands 𝒜), AtAll _root_.GlobalTheory.Fc.Ind.summandPrimitive 𝒜 τ → AtAll _root_.GlobalTheory.Fc.Ind.DivisorPointSummands 𝒜 τ → Ind.EvW (fun D _ _ _ => Formalism.BasicNotions.GoodFTAll D) 𝒜 τ → AtAll (fun D O c (b : _root_.GlobalTheory.Fc.Ind.PointSummands D O c) => GlobalTheory.ExportPin.ClassSumPin b.pt ∧ b.pt.CompatibilityConditions) 𝒜 τ → Ind.EvW _root_.GlobalTheory.Fc.Ind.RowPointSummands 𝒜 τ := by
  intro hDS hHC hCR hCW 𝒜 τ hPA hDiv hG hPin
  obtain ⟨hF, hRB, -, hFr⟩ := _root_.GlobalTheory.T.fire_realBound_thR_frames_at_all hDS hHC hCR hCW 𝒜 τ
  refine Formalism.MainNotions.Closed.imp hG ?_
  intro eps Fm CH _ h hc
  obtain ⟨x0, hx0⟩ := h hc
  refine ⟨x0, fun x hx h0 i => ?_⟩
  have ha := w3_a hc
  have hp := hPin Fm ha x hx i
  exact _root_.GlobalTheory.T.bundle_lines_of_primitive_frames_div_nmj _ _ _ _ (hF Fm ha x hx i) (hRB Fm ha x hx i) (hPA Fm ha x hx i) (hFr Fm ha x hx i)
    (hDiv Fm ha x hx i) (_root_.GlobalTheory.T.pNmj_of_pDiv_classSumPin _ _ _ _ (hDiv Fm ha x hx i) hp.1) (hx0 x hx h0 i) hp.2
end GlobalTheory.Fc.Ind
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsGalRepCast
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ResLoc
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open GlobalTheory.EigTie (ResTied IsRowPar plRed resTied_of_plSide)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf Zbar GalE OnW)
theorem exists_galRep_cast_alt {D : D7} {a p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q) {ι : Qbar p ≃+* ℂ} {π : D.naut.CG a}
    {r : GalE D →* GL (Fin a) (Qbar p)} (hr : _root_.UpperTheory.GalS.IsGaloisRepOfN D π p ι r) : ∃ r', _root_.UpperTheory.GalS.IsGaloisRepOfN D π q (qCast h ι) r' := by
  subst h
  exact ⟨r, hr⟩
end GlobalTheory.ResLoc
namespace GlobalTheory.ResLoc
end GlobalTheory.ResLoc
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsThetaRuleValueLeCoverCharZero
section
set_option synthInstance.maxHeartbeats 200000

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open IsLocalRing Formalism.MainNotions.ModuliIntegralCharts.H1 ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.JetsCharZero
theorem exists_theta_rule_value_le_cover_char_zero_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).ub} : Set (AllWt.Weight (dat p i))), ∀ cst : ℝ, GlobalTheory.RefSum.JetNum (Fm.D x ι) (DF (dat p i) (GlobalTheory.RefSum.thA (dat p i) la (GlobalTheory.RefSum.nCol (dat p i)))) cst → letI := p.T.Q.H.starRing; ∀ (nab : NabV Y.d.Xo₂ Y.d.c₂), IsNab Y.d.Xo₂ Y.d.c₂ nab → ∀ (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (y' : IntFr Y.d.Xo₂ Y.d.c₂ T io) (C : IntegralChartA3 Y.d.Xo₂ Y.d.c₂ T io y') (P : PELUnif (IsLocalRing.maximalIdeal T.V) C.I.G) (φT : ℝ), CharZero (IsLocalRing.ResidueField T.V) → Formalism.MainNotions.ModuliIntegralCharts.H1.FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → P.TorsionIso → GlobalTheory.SlopeRec.HasPhi y' φT → ∃ f ∈ thGen Y.d.Xo₂ Y.d.c₂ nab (GlobalTheory.RefSum.thA (dat p i) la (GlobalTheory.RefSum.nCol (dat p i))) (GlobalTheory.RefSum.nCol (dat p i)), evI y' f ≠ 0 ∧ (vV T.V (evI y' f) : ℝ) ≤ cst * φT := by
  intro h1 h2 h3 h4
  have hA := _root_.GlobalTheory.T.divisor_half_generated_of_covers h1 h2 h3 h4
  have hG := _root_.GlobalTheory.LiftGaps.weights_antitone_and_gap_ge_nCol_succ h3
  unfold _root_.GlobalTheory.CovTop.CoversCondition _root_.GlobalTheory.CovTop.LiftsCondition Formalism.MainNotions.Closed at hA hG ⊢
  obtain ⟨ε1, hε1, hA⟩ := hA
  obtain ⟨ε2, hε2, hG⟩ := hG
  refine ⟨min ε1 ε2, lt_min hε1 hε2, fun eps he hle => ?_⟩
  obtain ⟨K1, hK1⟩ := hA eps he (hle.trans (min_le_left _ _))
  obtain ⟨K2, hK2⟩ := hG eps he (hle.trans (min_le_right _ _))
  refine ⟨⟨max K1.pre K2.pre, fun l => max (K1.t l) (K2.t l), fun l => max (K1.mid l) (K2.mid l),
    fun l => max (K1.last l) (K2.last l)⟩, fun Fm CH hF hL => ?_⟩
  have hL1 : Fm.Large K1 CH := ⟨fun c hc => (le_max_left _ _).trans (hL.1 c hc), trivial,
    fun c hc => (le_max_left _ _).trans (hL.2.2.1 c hc), fun c hc => (le_max_left _ _).trans (hL.2.2.2 c hc)⟩
  have hL2 : Fm.Large K2 CH := ⟨fun c hc => (le_max_right _ _).trans (hL.1 c hc), trivial,
    fun c hc => (le_max_right _ _).trans (hL.2.2.1 c hc), fun c hc => (le_max_right _ _).trans (hL.2.2.2 c hc)⟩
  obtain ⟨C1, hC1, hE1⟩ := hK1 Fm CH hF hL1
  obtain ⟨C2, -, hE2⟩ := hK2 Fm CH hF hL2
  refine ⟨C1, hC1, ?_⟩
  obtain ⟨x1, hx1⟩ := hE1.and hE2
  refine ⟨x1, fun x hx hle ι p hp i hi Y hY => ?_⟩
  obtain ⟨hAi, hGi⟩ := hx1 x hx hle ι p hp
  obtain ⟨α, hα, hdvd, hMb, hρq⟩ := hAi i hi Y hY
  obtain ⟨hp1, hgap⟩ := hGi i hi Y hY
  intro la hla cst hJ nab hnab T io y' C P φT hch hTr hP hφ
  obtain ⟨hanti, hgp⟩ := hgap la hla
  have hbd : ∀ (τ : AllWt.Psi p.T.Q.H) (k : Fin ((dat p i).p + (dat p i).q)),
      |((la τ k : ℤ) : ℝ)| ≤ ∑ τ' : AllWt.Psi p.T.Q.H, ∑ k' : Fin ((dat p i).p + (dat p i).q), |((la τ' k' : ℤ) : ℝ)| :=
    fun τ k => (Finset.single_le_sum (f := fun k' => |((la τ k' : ℤ) : ℝ)|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ k)).trans (Finset.single_le_sum (f := fun τ' => ∑ k' : Fin ((dat p i).p + (dat p i).q),
        |((la τ' k' : ℤ) : ℝ)|) (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ τ))
  have hEven : Even (GlobalTheory.RefSum.nCol (dat p i)) := by
    unfold GlobalTheory.RefSum.nCol
    exact ⟨4 * ((∑ f : Lt1 (dat p i), 2 * rk f) / 8 + Fintype.card (Lt1 (dat p i)) + 1), by ring⟩
  have hn1 : 1 ≤ GlobalTheory.RefSum.nCol (dat p i) := by unfold GlobalTheory.RefSum.nCol; omega
  obtain ⟨hDom, -⟩ := GlobalTheory.RefSum.thA_dominant_lastPos_degree _ _ (dat p i) la (GlobalTheory.RefSum.nCol (dat p i)) _ hp1 hEven
    hanti hgp hbd
  have hg0 : 2 ≤ (Fm.D x ι).host.g 0 := ((Fm.D x ι).host.g_prime 0).two_le
  have hg1 : 2 ≤ (Fm.D x ι).host.g 1 := ((Fm.D x ι).host.g_prime 1).two_le
  obtain ⟨j1, j2, j3⟩ := hJ 0
  have hle0 : (Fm.D x ι).host.g 0 ≤ (Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1 := Nat.le_mul_of_pos_right _ (by omega)
  have hle0' : ((Fm.D x ι).host.g 0 : ℝ) ≤ (((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1 : ℕ) : ℝ) := by exact_mod_cast hle0
  have hg0' : (0 : ℝ) < (Fm.D x ι).host.g 0 := by exact_mod_cast (show 0 < (Fm.D x ι).host.g 0 by omega)
  have hN0 : (0 : ℝ) ≤ 2 * ((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.m := by positivity
  have hR0 : 0 ≤ GlobalTheory.PtTie.rr0 (Fm.D x ι) := by unfold GlobalTheory.PtTie.rr0; positivity
  exact exists_thRule_value_le _ _ _ _ Y.d.Xo₂ Y.d.c₂ nab hnab T io y' C hTr P hP hch φT hφ α _ hα hdvd hMb _ _ hDom.1
    GlobalTheory.RefSum.sum_le_nCol hn1 (2 * ((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.m) cst (by exact_mod_cast hρq) (j1.trans hle0)
    (lt_of_lt_of_le j2 hle0') (num_le _ _ _ _ _ _ _ hR0 hN0 (Nat.cast_nonneg _) hg0' hle0' j3)
end GlobalTheory.JetsCharZero
end
end
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
theorem _root_.GlobalTheory.T.theta_jet_value_bound_char_zero' : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).ub} : Set (AllWt.Weight (dat p i))), ∀ cst : ℝ, GlobalTheory.RefSum.JetNum (Fm.D x ι) (DF (dat p i) (GlobalTheory.RefSum.thA (dat p i) la (GlobalTheory.RefSum.nCol (dat p i)))) cst → letI := p.T.Q.H.starRing; ∀ (nab : NabV Y.d.Xo₂ Y.d.c₂), IsNab Y.d.Xo₂ Y.d.c₂ nab → ∀ (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (y' : IntFr Y.d.Xo₂ Y.d.c₂ T io) (C : IntegralChartA3 Y.d.Xo₂ Y.d.c₂ T io y') (P : PELUnif (IsLocalRing.maximalIdeal T.V) C.I.G) (φT : ℝ), CharZero (IsLocalRing.ResidueField T.V) → Formalism.MainNotions.ModuliIntegralCharts.H1.FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → P.TorsionIso → GlobalTheory.SlopeRec.HasPhi y' φT → ∃ f ∈ thGen Y.d.Xo₂ Y.d.c₂ nab (GlobalTheory.RefSum.thA (dat p i) la (GlobalTheory.RefSum.nCol (dat p i))) (GlobalTheory.RefSum.nCol (dat p i)), evI y' f ≠ 0 ∧ (vV T.V (evI y' f) : ℝ) ≤ cst * φT := by
  first | exact @_root_.GlobalTheory.JetsCharZero.exists_theta_rule_value_le_cover_char_zero_alt | exact _root_.GlobalTheory.JetsCharZero.exists_theta_rule_value_le_cover_char_zero_alt | (intros; apply _root_.GlobalTheory.JetsCharZero.exists_theta_rule_value_le_cover_char_zero_alt <;> assumption)
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LatIoAt
section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT Formalism.IndefR.Datum GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.OnCmp
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist GlobalTheory.FlatVecSum GlobalTheory.BigOn.Exp.SerBase
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp.SerBase
section BaseChange
variable {E K₀ K ι : Type} [Field E] [NumberField E] [Field K₀] [NumberField K₀] [Field K] [NumberField K] [Fintype ι]
  {n : ℕ}
end BaseChange
end GlobalTheory.BigOn.Exp.SerBase
namespace GlobalTheory.BigOn.Exp.SerBase
theorem latIoAt_alt : _root_.GlobalTheory.BigOn.Exp.SerBase.LatticeInclusionAt := by
  refine _root_.GlobalTheory.BigOn.Exp.TwistConditions.of_forall fun Fm x hx i p hR hM w hw j => ?_
  intro ρ hρ hpin c hc hs
  obtain ⟨gramR, c0R, c0L, hft, u, hu, hsc⟩ := hs
  refine ⟨u, hu, fun h hh P hP => ?_⟩
  have hL := _root_.GlobalTheory.T.links2_of_single_index_twisted _ _ _ _ _ _ _ _ _ _ p hR hM.1
  have hC : GlobalTheory.Hk3.Core (R2 p) (F2 p) := ⟨hL.1.lev, hL.1.grp, hL.1.fam, hL.1.models, hL.1.chain, hL.1.thP⟩
  have hio : IoExt (R2 p) := hR.ioExt
  have hB := hρ.base ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)
  have hBo : BaseOf (R2 p) j (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) := by
    have h0 := baseOf_of_realPin_at (cG := p.cG) hC.lev hρ hpin ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)
    exact { h0 with }
  have hlam := hBo.lam
  have hMlat := GlobalTheory.LatFull.latAt_isLattice _ ρ hρ ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h
  obtain ⟨hPh, hPF⟩ := (mem_harmLat _ _ _).1 hP
  rw [hlam] at hPF
  have key : ∀ φ ∈ coefLatFn (embLL0 (Fm.D x i)) (labLL0 (Fm.D x i)) (smallInt (Fm.D x i)) (lamV (Fm.D x i) j)
      ((ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)).latAt (finPt (Vc (Fm.D x i) j) h)),
      ∃ F : VV (Fm.D x i).what₂.LL (lamV (Fm.D x i) j), F ∈ nabAtr (labLL (Fm.D x i)) (lamV (Fm.D x i) j)
        ((ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)).latAt (finPt (Vc (Fm.D x i) j) h)) ∧
        φ = coefFn (Fm.D x i).what₂.embLL (lamV (Fm.D x i) j) (F : Pol (Fm.D x i).what₂.LL (Fm.D x i).what₂.Tau (Vc (Fm.D x i) j).rank) := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem φ hφ =>
      obtain ⟨F₀, hF₀, rfl⟩ := hφ
      refine ⟨⟨MvPolynomial.map (Fm.D x i).LL0.val.toRingHom F₀.1, GlobalTheory.Proof.TensorMapDescent.map_mem_VV _ _ _ F₀.2⟩,
        map_mem_nabAtr_comp (Fm.D x i).LL0.val.toRingHom (labLL0 (Fm.D x i)) _ _ hMlat hF₀, ?_⟩
      funext y
      rw [coefFn, coefFn, MvPolynomial.eval₂Hom_map_hom]
      rfl
    | zero => exact ⟨0, zero_mem _, funext fun y => by simp [coefFn]⟩
    | add φ ψ _ _ h1 h2 =>
      obtain ⟨F1, m1, rfl⟩ := h1
      obtain ⟨F2, m2, rfl⟩ := h2
      exact ⟨F1 + F2, add_mem m1 m2, funext fun y => by simp [coefFn, mul_add]⟩
    | smul a φ _ h1 =>
      obtain ⟨F1, m1, rfl⟩ := h1
      obtain ⟨t, ht⟩ := a.2
      refine ⟨RingOfIntegers.mapRingHom (Fm.D x i).LL0.val.toRingHom t • F1, Submodule.smul_mem _ _ m1, funext fun y => ?_⟩
      have e1 : ((RingOfIntegers.mapRingHom (Fm.D x i).LL0.val.toRingHom t • F1 : VV (Fm.D x i).what₂.LL (lamV (Fm.D x i) j)) :
          Pol (Fm.D x i).what₂.LL (Fm.D x i).what₂.Tau (Vc (Fm.D x i) j).rank) =
          MvPolynomial.C (((RingOfIntegers.mapRingHom (Fm.D x i).LL0.val.toRingHom t : 𝓞 (Fm.D x i).what₂.LL)) :
            (Fm.D x i).what₂.LL) * (F1 : Pol (Fm.D x i).what₂.LL (Fm.D x i).what₂.Tau (Vc (Fm.D x i) j).rank) := by
        rw [← MvPolynomial.smul_eq_C_mul]
        rfl
      have e2 : (Fm.D x i).what₂.embLL (((RingOfIntegers.mapRingHom (Fm.D x i).LL0.val.toRingHom t : 𝓞 (Fm.D x i).what₂.LL)) :
          (Fm.D x i).what₂.LL) = (a : ℂ) := by
        rw [← ht]
        rfl
      show (a : ℂ) * coefFn _ _ (F1 : Pol (Fm.D x i).what₂.LL (Fm.D x i).what₂.Tau (Vc (Fm.D x i) j).rank) y = _
      rw [e1, coefFn, coefFn, map_mul, MvPolynomial.eval₂Hom_C, e2]
      ring
  obtain ⟨F, hF, hFe⟩ := key _ hPF
  have hM' : (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)).latAt (finPt (Vc (Fm.D x i) j) h) =
      Bridge.hLat (Vc (Fm.D x i) j) (fin (Vc (Fm.D x i) j) h) :=
    GlobalTheory.LatAtHLat.latAt_eq_hLat _ _ _ _ (GlobalTheory.LatFull.baseFrame_one_eq _ _ _ (hρ.latS _ j _)) _
  refine ⟨c0L j F, ⟨gramR, c0R, c0L, hft, F, by rw [← hM']; exact hF, rfl⟩, ?_⟩
  obtain ⟨u', w₀, hu', -, hw₀⟩ := IsChosenExtremalVector.io _ ((fw2 p).hv₀ j _) hio
  have huu : u' = (u : ∀ τ, lowT ((R2 p).MW j (sg0 (Fm.D x i) p.P.A3.A)) τ) :=
    funext fun τ => Subtype.ext ((hu' τ).trans (hu τ).symm)
  rw [huu] at hw₀
  have hm : ∀ τ, (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)).w.p τ +
      (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)).w.q τ ≤ (Wc (Fm.D x i) j).rank := fun τ => by
    have h1 := hB.sig τ
    have h2 := Formalism.BasicNotions.sig_sum _ hB.sigOK (Formalism.BasicNotions.TH.tauE (Fm.D x i) τ)
    rw [← h1] at h2
    exact h2.le
  have hinj := GlobalTheory.T.harmonic_polynomial_eq_zero_of_function _ _ _ _ (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)).F.BS hB.wt hm
  exact IsScaleAt.ioP_eq (Rl := p.R) hsc hinj hPh
    (GlobalTheory.SeriesTie.UnivRat.ioP_mem_harmonic hC.lev hC.thP (hC.models.cV j) hB (hpin.psi _ j _) (hpin.inf _ j _)
      (hpin.cartT _ j _) (hpin.onbS _ j _) (hpin.onbT _ j _) (hpin.mu0 _ j _) (hpin.eta _ j _) (hpin.ap _ j _) (hpin.am _ j _)
      _ w₀ hw₀ _) hFe
end GlobalTheory.BigOn.Exp.SerBase
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MemberSizes
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.Fam.MemberSizes
variable (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL)
theorem ties_at_alt : GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ D _ _ _ => Formalism.BasicNotions.Ties D) :=
  RowE.of_all fun _ _ β _ _ _ _ _ => β.p.pt.xa.ties
theorem linked_scale_ge_H_and_cgam_eq (H : Formalism.MainNotions.Inhab.FC → ℝ) : GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun κ _ O _ _ =>
    H κ.C ≤ O.L.sc.L ∧ O.L.CGam = κ.C.CGam ∧ 1 ≤ κ.C.CGam) := by
  refine ⟨1, one_pos, fun eps C8 C5 c6 Cb he _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C hC _ _ =>
    ⟨0, fun cD _ => ⟨0, fun ch _ _ => ⟨max 1 (max (H C) 1 ^ eps⁻¹), fun K hK hx β _ c b _ => ?_⟩⟩⟩⟩⟩
  have hG : 1 ≤ C.CGam := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ (by simp [Inhab.FC.cMid])
  have hs : β.O.L.sc = K.s := β.sc
  have hc : β.O.L.CGam = C.CGam := β.val.CGam_eq.trans (congrArg Inhab.FC.CGam hK.1)
  refine ⟨?_, hc, hG⟩
  show H C ≤ β.O.L.sc.x ^ β.O.L.sc.eps
  rw [hs, hK.2.2.2.1]
  have h1 : 0 ≤ max (H C) 1 := le_trans zero_le_one (le_max_right _ _)
  calc H C ≤ max (H C) 1 := le_max_left _ _
    _ = (max (H C) 1 ^ eps⁻¹) ^ eps := (Real.rpow_inv_rpow h1 he.ne').symm
    _ ≤ K.s.x ^ eps := Real.rpow_le_rpow (Real.rpow_nonneg h1 _) (le_trans (le_max_right _ _) hx) he.le
theorem parameters_scale_rank_gap_bounds (F G H : ℝ → ℝ → ℝ) : GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ D O _ _ =>
    ∃ C' Cl Cg CT : ℝ, F Cg CT ≤ C' ∧ G Cg CT ≤ Cl ∧ H Cg CT ≤ O.L.sc.L ∧
      GlobalTheory.Core.Rk.HD D O.L.sc.L C' Cl Cg (1 / 4) 3 (1 / 2) CT ∧ GlobalTheory.Core.Rk.IsScaleWithBoundedGamma D O.L.sc.L C' ∧
      (∀ u, GlobalTheory.Core.Rk.RankMu D u) ∧ GlobalTheory.Core.Rk.BigGap D ∧ 1 ≤ D.R.rS) := by
  have h := (((((((_root_.GlobalTheory.Fam.MemberSizes.ties_at_alt hL p).and (_root_.GlobalTheory.T.familyMidVolume_at_linked hL p)).and (_root_.GlobalTheory.T.degHypL_all_linked_good_members hL p (fun C => F (C.P.CYL + 1) C.CTu) (fun C => G (C.P.CYL + 1) C.CTu))).and (_root_.GlobalTheory.T.dataNW_all_linked_good_members hL p)).and (_root_.GlobalTheory.T.type_frame_all_members' hL p)).and (_root_.GlobalTheory.T.rankMu_all_linked_members hL p)).and (_root_.GlobalTheory.T.bigGap_of_isGoodE_isLinked hL p)).and (_root_.GlobalTheory.Fam.MemberSizes.linked_scale_ge_H_and_cgam_eq hL p (fun C => H (C.P.CYL + 1) C.CTu))
  refine RowE.imp h ?_
  intro κ K β c b _ _ _ H0
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8, h9, h10⟩ := H0
  have hm : max (G (κ.C.P.CYL + 1) κ.C.CTu) 40 ≤ (β.D.R.m : ℝ) :=
    h3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨max (F (κ.C.P.CYL + 1) κ.C.CTu) (8 * κ.C.CGam), max (G (κ.C.P.CYL + 1) κ.C.CTu) 40, κ.C.P.CYL + 1, κ.C.CTu,
    le_max_left _ _, le_max_left _ _, h8, ⟨h1, h2, h3, h4, h5⟩, ⟨β.O.L, rfl, h9 ▸ le_max_right _ _, h9 ▸ h10⟩, h6, h7, ?_⟩
  have h40 : (40 : ℝ) ≤ β.D.R.m := le_trans (le_max_right _ _) hm
  have : 40 ≤ β.D.R.m := by exact_mod_cast h40
  show 1 ≤ β.D.R.m / 2 - 1
  omega
theorem parameters_scale_size_bounds_of_member : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) (F G H : ℝ → ℝ → ℝ),
    GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ D O _ _ => ∃ C' Cl Cg CT : ℝ, F Cg CT ≤ C' ∧ G Cg CT ≤ Cl ∧
      H Cg CT ≤ O.L.sc.L ∧ GlobalTheory.Core.Rk.HD D O.L.sc.L C' Cl Cg (1 / 4) 3 (1 / 2) CT ∧ GlobalTheory.Core.Rk.IsScaleWithBoundedGamma D O.L.sc.L C' ∧
      (∀ u, GlobalTheory.Core.Rk.RankMu D u) ∧ GlobalTheory.Core.Rk.BigGap D ∧ 1 ≤ D.R.rS) :=
  fun hL p F G H => _root_.GlobalTheory.Fam.MemberSizes.parameters_scale_rank_gap_bounds hL p F G H
end GlobalTheory.Fam.MemberSizes
end
end
end

