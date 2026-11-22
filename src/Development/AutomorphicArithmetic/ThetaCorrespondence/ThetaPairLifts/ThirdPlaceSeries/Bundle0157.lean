import Development.AbelianVarietyTheory.Proofs.HeightProofs.RowEPartTies
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0074
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0048
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0064
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealTB
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0037
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0152
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0789
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0027
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0123
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0128
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0151
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0783
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0067
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0082
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0030
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0033
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0035
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0044
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0040
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0031
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0029
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0045
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0032
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0093
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0024
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2955
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0062
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0114
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0130
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0131
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0153
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0133
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0115
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0605
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0051
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0049
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0075
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0039
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0046
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2940
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2956
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0139
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0098
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0606
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0132
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0134
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0149
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0150
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0148

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowEPartTies
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.PlugPt
theorem rowE_part_ties_alt : GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (𝒮 : Slots) (ν : _root_.GlobalTheory.PlugPt.ExtensionReading hL 𝒮) (Q : V4.Slot),
    CoreSlot 𝒮 → RowE (Bd := _root_.GlobalTheory.Fc.Ind.PointSummands) (sAnd Q RayPosition) (linkOf fun K p c b => _root_.GlobalTheory.PlugPt.pinnedPointOfReading ν K p c b.pt)
      fun _ D O c b => TiesB D O c b.pt ∧ GlobalTheory.CovTop.RecTied D O.L ∧ More b.pt := by
  intro hR hL 𝒮 ν Q hC
  refine (EvP.and (_root_.GlobalTheory.PlugPt.rowE_tiesB_alt hR hL 𝒮 ν Q hC) GlobalTheory.T.eventually_constructedPoint_hostSize_numerical).mono ?_
  intro κ K _ H β hq c b hl
  obtain ⟨p, b', hpin, heq⟩ := hl
  have hl' : linkOf (_root_.GlobalTheory.PlugPt.pinnedPointOfReading ν) K β c b.pt :=
    ⟨p, b'.pt, hpin, congrArg (fun y : (Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Fc.Ind.PointSummands D O c) =>
      (⟨y.1, y.2.1, y.2.2.pt⟩ : Σ (D : D7) (O : Obj D), BdPt D O c)) heq⟩
  have ht : TiesB β.D β.O c b.pt := H.1 β hq c b.pt hl'
  have hs : FieldSmall β.D β.O.L := ((H.2 β).2 _ ht.1.tied.field).2.2
  have hw : SingleIndexPlacesAreTwisted b.pt := fun w hw => ((b.muDef 0 0).2.2.2 w).2 hw
  exact ⟨ht, ⟨hs, (GlobalTheory.T.pathCoreConditions_of_intrinsicConditions β.D β.O c b.pt ht hs).2.2.1⟩, GlobalTheory.PlugPt.more_of_tiesB β.D β.O c b.pt ht hs hw⟩
end GlobalTheory.PlugPt
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ScalRows
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem.R3
noncomputable section
namespace GlobalTheory.Mem.R3.ScalarComponentUnique
set_option maxHeartbeats 4000000 in
theorem scal_rows_alt : GlobalTheory.Published.GreenCuspidal → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (Γ : GeoP) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), p = _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none Γ → (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → ∀ (K : Ctx) (q : WPt p.s K), (∀ X : GlobalTheory.Mem.Stages, K.Over X.B.toPre → HostHyp X.toD7 ∧ X.toD7.host.F = maximalRealSubfield X.toD7.host.E ∧ (∀ i, IsFDiag (Wc X.toD7 i) ∧ IsFDiag (Vc X.toD7 i)) ∧ (∀ i, (Vc X.toD7 i).IsPosDef) ∧ (∀ j, Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.Y j) ∧ Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.V j) ∧ (1 ≤ j → j ≤ X.toD7.R.m → Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.W j))) ∧ Formalism.IndefR.Seed.FrmC.StdLat X.toD7.sp.X' ∧ (∀ i, (∀ a b, (Vc X.toD7 i).hT ((Vc X.toD7 i).frame a) ((Vc X.toD7 i).frame b) = if a = b then 1 else 0) ∧ (Vc X.toD7 i).L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range (Vc X.toD7 i).frame)) ∧ ((∀ a b, X.toD7.sp.X'.hT (X.toD7.sp.X'.frame a) (X.toD7.sp.X'.frame b) = if a = b then 1 else 0) ∧ X.toD7.sp.X'.L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range X.toD7.sp.X'.frame))) → GlobalTheory.CuspMult.MultEq q.x.what₂.r.z.R.toRealDat → ∀ (a : TwArgs q.O.ex q.x.what₂), letI := a.x.grp; letI := a.x.fin; letI := a.x.alg; ∀ (i : Fin (q.w.D q.Z).R.m) π (c : a.x.A3.fam3.base3.Ix) (e : (q.w.D q.Z).what₂.LL →+* ℂ), (q.w.D q.Z).what₂.isot ((i : ℕ) + 1) π ≠ ⊥ → (q.w.D q.Z).what₂.isot ((i : ℕ) + 1) π ≤ (a.x.R.Wp3 i c).comap (a.x.Y.mj.eW i) → q.O.X.logLam ((i : ℕ) + 1) π e = Real.log (a.x.R.lam3 i a.x.A3.A.μ0 c (InfinitePlace.mk e)) := by
  intro hGC h1 h2 h3 h4 h5 h6 hCRD h8 h9 hL N Γ p hp hNE K q hHost hMult a
  letI := a.x.grp; letI := a.x.fin; letI := a.x.alg
  intro i π c e hne hle
  by_cases he : e = (q.w.D q.Z).what₂.embLL
  · subst he
    have h := eigenvalue_of_part hCRD a.x.R a.x.F a.x.cG _ a.x.Y a.x.pins a.intersectionNumber_baseChange i π c hne hle
    exact (q.O.X.logLam_base _ π).trans
      (congrArg Real.log (h.trans (congrArg (a.x.R.lam3 i a.x.A3.A.μ0 c) a.x.R.hv0)))
  · exact _root_.GlobalTheory.T.parameter_of_discrete_series_ray_alt hGC h1 h2 h3 h4 h5 h6 hCRD h8 h9 hL N Γ p hp hNE K q hHost hMult a i π c e he hne hle
end GlobalTheory.Mem.R3.ScalarComponentUnique
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SidePtPartOfPack
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.PlugPt
open GlobalTheory.Mem.R3 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
set_option maxHeartbeats 4000000 in
theorem sidePt_part_of_pack_alt {D : D7} {O : Obj D} {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition D O c) (t : b.Comparison₂) {x : R3.TwIn O.ex}
    (y : _root_.GlobalTheory.Mem.R3.RealInAlt x b.R b.S) (h : _root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b = _root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput y) :
    ∃ Tp : Formalism.L2.Host.TupTied D x.R.C O.ex.nch, HEq Tp t.1.Tp ∧
      sidePt (O := O) (b.part t).pt = ({ G := x.G, Pl0 := x.Pl0, I0 := x.I0, T := x.T, A3 := x.A3, J := x.core, R := x.R, P0 := x.F.P0, ψ0 := x.F.ψ0, cG := x.cG, v₀ := x.geo.v₀, S := y.Sx, YS := y.nexp, cf := x.R.C, tp := Tp } : Side D O.ex.nch) := by
  have key : ∀ (p : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S) (_ : p = _root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput y) (Tq : Formalism.L2.Host.TupTied D p.B.Q.Rl.C O.ex.nch),
      ∃ Tp : Formalism.L2.Host.TupTied D x.R.C O.ex.nch, HEq Tp Tq ∧
        ({ G := p.P.Gp, Pl0 := p.P.Pl0, I0 := p.P.I0, T := p.P.T, A3 := p.P.A3, J := p.B.T, alg := p.B.alg, R := p.B.Q.Rl, P0 := p.P.P0, ψ0 := p.P.ψ0, cG := p.B.Q.cG, v₀ := p.B.v₀, S := p.B.Q.Sx, YS := p.B.Q.nexp, cf := p.B.Q.Rl.C, tp := Tq } : Side D O.ex.nch) =
          ({ G := x.G, Pl0 := x.Pl0, I0 := x.I0, T := x.T, A3 := x.A3, J := x.core, R := x.R, P0 := x.F.P0, ψ0 := x.F.ψ0, cG := x.cG, v₀ := x.geo.v₀, S := y.Sx, YS := y.nexp, cf := x.R.C, tp := Tp } : Side D O.ex.nch) := by
    intro p hp Tq
    subst hp
    exact ⟨Tq, HEq.rfl, rfl⟩
  exact key (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b) h t.1.Tp
set_option maxHeartbeats 4000000 in
theorem pin_pt_of_bundle_witness : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP) (hE : _root_.GlobalTheory.PlugPt.HasExponent' N) (K : Ctx) (q : WPt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K) (c : ℝ) (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c) (_ : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness (p := _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) q b) (t : b.Comparison₂), _root_.GlobalTheory.PlugPt.pinnedPointOfReading (_root_.GlobalTheory.PlugPt.ExtensionReading.of RX hE (SXE S) (OX Γ)) K q c (b.part t).pt := by
  intro hL N S Γ hE K q c b w t
  obtain ⟨x, a, ax, y, recPin, -, -, sx, eF, fi, -⟩ := w
  obtain rfl := eq_of_heq ax
  obtain ⟨Tp, hTp, h⟩ := _root_.GlobalTheory.PlugPt.sidePt_part_of_pack_alt b t y.y y.eq
  have htp : HEq Tp q.x.n.tp := hTp.trans (t.1.tpEq.trans (Sigma.mk.inj_iff.mp recPin.s.chr).2)
  have hcf : q.x.what₂.r.z.R.C = GlobalTheory.Mem.Col2.TC.cf q.w.I q.w.l q.Z := q.x.what₂.r.z.lev.C
  refine ⟨q.x.what₂.r.z.R.kap, a.lam, a.err, h.trans ?_⟩
  refine side_eq_upd (O := q.O) a.x (_root_.GlobalTheory.PlugPt.sideOf_alt q.x.what₂ q.x.n q.core_data_of_point) q.x.what₂.r.z.R.kap a.lam a.err (reFace q.x.what₂.r.z.F a.Dc a.Sp a.Zsc :)
    y.y.Sx y.y.nexp Tp ?pack rfl HEq.rfl ?v ?S ?fi ?eF hcf htp
  case pack => exact (by with_unfolding_all exact (a.pack :))
  case v => exact (by with_unfolding_all exact (a.v₀ :))
  case S => exact (by with_unfolding_all exact (sx :))
  case fi => exact (by with_unfolding_all exact (fi :))
  case eF => exact (by with_unfolding_all exact (eF :))
end GlobalTheory.PlugPt
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SizesOfCover
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
noncomputable section
namespace GlobalTheory.CovTop.CovSz
theorem sizes_of_cover_alt : _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => LawsJ p.T ∧ InR (Fm.D x ι) ((i : ℕ) + 1) ∧ 1 ≤ (Fm.L x ι).sc.L ∧ Real.log Y.d.l₂.M ≤ 30 * (Fm.L x ι).sc.L ∧ fieldSz (Fm.D x ι).host.E ≤ 3 * (Fm.L x ι).sc.L ∧ Real.log ((Fm.D x ι).R.f * (Fm.D x ι).R.r) ≤ (Fm.L x ι).sc.L ∧ 4 ≤ expL (Fm.L x ι).sc.L ∧ (∀ k, (Fm.D x ι).R.r + 1 < (Fm.D x ι).host.g k) ∧ 8 ≤ (Fm.D x ι).R.f ∧ 100 ≤ (Fm.D x ι).R.r ∧ zBase (Fm.L x ι) ^ 12 ≤ PP := by
  refine _root_.GlobalTheory.CovTop.CovSz.covers_of_lifts_alt (_root_.GlobalTheory.CovTop.Sizes.hostN_alt 6) ?_
  intro eps Fm x hx ι p i C _ hN hi Y hY
  have hL10 : 10 ≤ (Fm.L x ι).sc.L := hN.big.2.1
  have hx1 := (Fm.L x ι).sc.one_lt_alt
  have he0 := (Fm.L x ι).sc.eps_pos
  have he1 := (Fm.L x ι).sc.eps_lt
  have hx16 : (16 : ℝ) ≤ (Fm.L x ι).sc.x := by
    have h1 : (Fm.L x ι).sc.L ≤ (Fm.L x ι).sc.x ^ ((1 : ℝ) / 52) :=
      Real.rpow_le_rpow_of_exponent_le hx1.le he1.le
    have h2 : ((Fm.L x ι).sc.x ^ ((1 : ℝ) / 52)) ^ (52 : ℕ) = (Fm.L x ι).sc.x := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
    have h3 : (10 : ℝ) ^ (52 : ℕ) ≤ ((Fm.L x ι).sc.x ^ ((1 : ℝ) / 52)) ^ (52 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) (hL10.trans h1) _
    rw [h2] at h3
    linarith [show (16 : ℝ) ≤ 10 ^ (52 : ℕ) by norm_num]
  have hrec := fun j => GlobalTheory.sizes_record_at (Fm.L x ι) (Fm.sizes x hx ι) 5 (by norm_num) hx16 j
  obtain ⟨-, -, -, -, h100, hr5, -⟩ := hrec 0
  have hg : ∀ k, Real.exp (8 * (Fm.L x ι).sc.L) ≤ ((Fm.D x ι).host.g k : ℝ) := fun k => by
    have := (hrec k).1; unfold Formalism.BasicNotions.Scale.L; exact this
  have hgpos : ∀ k, (0 : ℝ) < ((Fm.D x ι).host.g k : ℝ) := fun k => lt_of_lt_of_le (Real.exp_pos _) (hg k)
  have hlog3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num); linarith
  have hlog3p : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hf8 : (8 : ℝ) ≤ (Fm.D x ι).R.f := by exact_mod_cast hN.f8
  have hfpos : (0 : ℝ) < (Fm.D x ι).R.f := by linarith
  have hr2 : (2 : ℝ) ≤ (Fm.D x ι).R.r := by exact_mod_cast (by omega : 2 ≤ (Fm.D x ι).R.r)
  refine ⟨p.fw.laws, ⟨by omega, by omega⟩, by linarith, ?_, ?_, hN.logfr.1, ?_, ?_, hN.f8, h100, hN.ppLow⟩
  ·
    have hM : Y.d.l₂.M = (Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1 * 15 ^ expL (Fm.L x ι).sc.L := by
      rw [hY.1.lev.1.2.1, hY.1.pd]
      congr 1
      exact p.fw.laws.toLawsM.pins.2.1.1
    have he : (expL (Fm.L x ι).sc.L : ℝ) * Real.log 3 ≤ 3 * (Fm.L x ι).sc.L := by
      have := Nat.floor_le (show 0 ≤ 3 * (Fm.L x ι).sc.L / Real.log 3 by positivity)
      unfold expL
      rwa [le_div_iff₀ hlog3p] at this
    have h15 : Real.log 15 ≤ 5 / 2 * Real.log 3 := by
      have : Real.log ((15 : ℝ) ^ 2) ≤ Real.log ((3 : ℝ) ^ 5) := Real.log_le_log (by norm_num) (by norm_num)
      rw [Real.log_pow, Real.log_pow] at this
      push_cast at this
      linarith
    have he0 : (0 : ℝ) ≤ expL (Fm.L x ι).sc.L := Nat.cast_nonneg _
    rw [hM]
    push_cast
    rw [Real.log_mul (mul_pos (hgpos 0) (hgpos 1)).ne' (by positivity : (0 : ℝ) < 15 ^ expL (Fm.L x ι).sc.L).ne',
      Real.log_mul (hgpos 0).ne' (hgpos 1).ne', Real.log_pow]
    have g0 := hN.logg 0
    have g1 := hN.logg 1
    nlinarith
  ·
    unfold fieldSz
    rw [hN.deg]
    have hd := hN.disc
    have h2f : Real.log ((2 * (Fm.D x ι).R.f : ℕ) : ℝ) ≤ (Fm.L x ι).sc.L := by
      refine le_trans ?_ hN.logfr.1
      push_cast
      exact Real.log_le_log (by positivity) (by nlinarith)
    have hq : Real.log |(NumberField.discr (Fm.D x ι).host.E : ℝ)| / ((2 * (Fm.D x ι).R.f : ℕ) : ℝ) ≤
        2 * (Fm.L x ι).sc.L := by
      rw [div_le_iff₀ (by push_cast; positivity)]
      push_cast
      nlinarith
    linarith
  ·
    exact le_expL (by push_cast; nlinarith)
  · intro k
    have hA := hN.poly.1
    have hxA : (Fm.L x ι).sc.x ≤ (Fm.L x ι).sc.x ^ C := by
      calc (Fm.L x ι).sc.x = (Fm.L x ι).sc.x ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (Fm.L x ι).sc.x ^ C := Real.rpow_le_rpow_of_exponent_le hx1.le hA
    have hroom : ((Fm.L x ι).sc.x ^ C) ^ (6 : ℕ) ≤ (Fm.L x ι).sc.b := by
      have := hN.room
      rwa [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at this
    have h6 : (Fm.L x ι).sc.x ^ (6 : ℕ) ≤ ((Fm.L x ι).sc.x ^ C) ^ (6 : ℕ) := pow_le_pow_left₀ (by linarith) hxA 6
    have h5 : (Fm.L x ι).sc.x ^ (5 : ℕ) + 1 < (Fm.L x ι).sc.x ^ (6 : ℕ) := pow_five_add_one_lt hx16
    have hb : (Fm.L x ι).sc.b ≤ Real.exp (8 * (Fm.L x ι).sc.L) := by
      unfold Formalism.BasicNotions.Scale.b; exact Real.exp_le_exp.2 (by linarith)
    have hr5' : ((Fm.D x ι).R.r : ℝ) ≤ (Fm.L x ι).sc.x ^ (5 : ℕ) := by
      have e : (Fm.L x ι).sc.x ^ (5 : ℕ) = (Fm.L x ι).sc.x ^ (5 : ℝ) := by exact_mod_cast (Real.rpow_natCast _ 5).symm
      first | exact hr5 | (rw [e]; exact hr5)
    have : ((Fm.D x ι).R.r : ℝ) + 1 < (Fm.D x ι).host.g k :=
      calc ((Fm.D x ι).R.r : ℝ) + 1 ≤ (Fm.L x ι).sc.x ^ (5 : ℕ) + 1 := add_le_add hr5' le_rfl
        _ < (Fm.L x ι).sc.x ^ (6 : ℕ) := h5
        _ ≤ ((Fm.L x ι).sc.x ^ C) ^ (6 : ℕ) := h6
        _ ≤ (Fm.L x ι).sc.b := hroom
        _ ≤ Real.exp (8 * (Fm.L x ι).sc.L) := hb
        _ ≤ (Fm.D x ι).host.g k := hg k
    exact_mod_cast this
theorem size_rows_alt : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => LawsJ p.T ∧ InR (Fm.D x ι) ((i : ℕ) + 1) ∧ 1 ≤ (Fm.L x ι).sc.L ∧ Real.log Y.d.l₂.M ≤ 30 * (Fm.L x ι).sc.L ∧ fieldSz (Fm.D x ι).host.E ≤ 3 * (Fm.L x ι).sc.L ∧ Real.log ((Fm.D x ι).R.f * (Fm.D x ι).R.r) ≤ (Fm.L x ι).sc.L ∧ 4 ≤ expL (Fm.L x ι).sc.L ∧ (∀ k, (Fm.D x ι).R.r + 1 < (Fm.D x ι).host.g k) ∧ 8 ≤ (Fm.D x ι).R.f ∧ 100 ≤ (Fm.D x ι).R.r ∧ |GlobalTheory.FlatLine.flatDegVal (dat p i) (Formalism.L2.DIV.ofRecord (Fm.D x ι) (Fm.L x ι) p.Del p.h0).logOm| ≤ 9 * (Fm.D x ι).R.r * (Fm.L x ι).sc.L ∧ Real.log (kap p i) ≤ 2 * (Fm.L x ι).sc.L ∧ zBase (Fm.L x ι) ^ 12 ≤ PP ∧ (lenT p i PP : ℝ) * PP ≤ Real.sqrt (Fm.L x ι).sc.b ∧ zed p i PP (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ * (PP * kap p i) ≤ (Fm.L x ι).sc.b ∧ zed p i PP (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ ≤ 1 / 2 ∧ (∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₂} : Set (AllWt.Weight (dat p i))), ∑ τ, ∑ k, |(la τ k : ℝ)| ≤ zBase (Fm.L x ι) ^ 2 * (kap p i / lenT p i PP + 1)) ∧ ∀ j ≤ lenT p i PP, ∑ τ, ∑ k, |((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt j τ k : ℝ)| ≤ zBase (Fm.L x ι) ^ 2 * kap p i := by
  intro hS
  refine _root_.GlobalTheory.CovTop.CovSz.covers_of_covers_of_imp (_root_.GlobalTheory.CovTop.CovSz.covers_and_alt _root_.GlobalTheory.CovTop.CovSz.sizes_of_cover_alt (_root_.GlobalTheory.CovTop.CovSz.covers_and_alt (_root_.GlobalTheory.T.abs_flatDegVal_logOm_le_nine_mul_of_size hS) (_root_.GlobalTheory.CovTop.CovSz.covers_and_alt (_root_.GlobalTheory.T.log_kap_le_and_lenT_mul_le_sqrt hS)
    (_root_.GlobalTheory.CovTop.CovSz.covers_and_alt (_root_.GlobalTheory.T.weight_parameter_size_bounds' hS) (_root_.GlobalTheory.CovTop.CovSz.covers_and_alt (_root_.GlobalTheory.T.weight_param_coeff_sum_bound' hS) (_root_.GlobalTheory.T.weight_param_coeff_sum_le_at_index' hS)))))) ?_
  intro eps Fm x hx ι p i Y PP h
  obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a13⟩, b11, ⟨b12, b14⟩, ⟨b15, b16⟩, b17, b18⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, b11, b12, a13, b14, b15, b16, b17, b18⟩
end GlobalTheory.CovTop.CovSz
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StepYIntegrableAndEqStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_chain_step_theta_lift_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ j, j + 1 < D.R.m → Lift.IsIo (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).ν (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).fd (thetaKO (_root_.GlobalTheory.BaseChain.transitionBetweenSpacesY f j).ω) (_root_.GlobalTheory.BaseChain.transitionBetweenSpacesY f j).pt (_root_.GlobalTheory.BaseChain.transitionBetweenSpacesY f j).It ((_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).CC (_root_.GlobalTheory.BaseChain.com_z W)) ((_root_.GlobalTheory.BaseChain.stageOfSpaceY W j).CC (_root_.GlobalTheory.BaseChain.com_z W)) (_root_.GlobalTheory.BaseChain.transitionBetweenSpacesY f j).io := by
  first | exact @_root_.GlobalTheory.BaseChain.stepY_isIo_alt | exact _root_.GlobalTheory.BaseChain.stepY_isIo_alt | (intros; apply _root_.GlobalTheory.BaseChain.stepY_isIo_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StepYThetaFunIsItW
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.BaseChain
variable {D : D7}
theorem stepY_thetaFun_isItW_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ j, j + 1 < D.R.m → (∀ φ, IsThetaFunO (_root_.GlobalTheory.BaseChain.com_z W).ψ (_root_.GlobalTheory.BaseChain.stageOfSpaceY W j).V (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).V ((_root_.GlobalTheory.BaseChain.transitionBetweenSpacesY f j).pt φ)) ∧ IsItW (_root_.GlobalTheory.BaseChain.com_z W).θ (_root_.GlobalTheory.BaseChain.stageOfSpaceY W j).M (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).M (_root_.GlobalTheory.BaseChain.transitionBetweenSpacesY f j).ω (_root_.GlobalTheory.BaseChain.transitionBetweenSpacesY f j).pt (_root_.GlobalTheory.BaseChain.transitionBetweenSpacesY f j).It := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hP hR j hj
  obtain ⟨-, -, -, hC, -⟩ := hP.bot.hyp
  have hj' : j < D.R.m := by omega
  have dS : IsSelfDualC (Yc D j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) :=
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βY j hj')
  have dT : IsSelfDualC (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) :=
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βY (j + 1) hj)
  have hP' := (hR.row W.P.A3.A.μ0).vP j hj
  have hY := hC.chain.vY W.P.A3.A.μ0 j hj
  have hω := hC.chain.ωY W.P.A3.A.μ0 j hj
  have hθ := hC.models.inf
  obtain ⟨vth, vne, -⟩ := GlobalTheory.InnerSteps.stepVec_vac dS dT (rank_Yc_le_succ j) hP'
  refine ⟨fun φ => GlobalTheory.FockTheta.ptStable D _ _ hP'.1.1 hθ _ _ _ _ _ _ _ φ vth, ?_⟩
  have h0 := GlobalTheory.Grid.isItW_of_mem_span hω hθ hP'.1.2.theta (GlobalTheory.Grid.stepVec_mem_span dS dT hY)
    (hC.chain.ItY W.P.A3.A.μ0 j hj)
  exact GlobalTheory.Grid.isItW_of_mem_span hω hθ vth (GlobalTheory.T.vacuum_mem_span_heisenbergTranslates_of_ne_zero hP'.1 dS dT (GlobalTheory.Grid.stepVec_mem_span dS dT hP') vne) h0
end GlobalTheory.BaseChain
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SumCOfDeepGoodStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_c_of_deep_good : _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SumBoundCondition := by
  first | exact @_root_.GlobalTheory.CovTop.sumC_of_deepGood_alt | exact _root_.GlobalTheory.CovTop.sumC_of_deepGood_alt | (intros; apply _root_.GlobalTheory.CovTop.sumC_of_deepGood_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SumPtOfSize
section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.RefSum GlobalTheory.CovTop GlobalTheory.BigTop
namespace GlobalTheory.RefSum
theorem sumPt_of_size_alt : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.RefSum.SumPtAlt := fun h => _root_.GlobalTheory.T.sum_pt_of_wt_pt_num_pt (_root_.GlobalTheory.T.weight_pt_of_size h) (_root_.GlobalTheory.T.numerical_point_statement_of_size h)
end GlobalTheory.RefSum
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopComb
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.TopConv
variable {D : D7}
end GlobalTheory.TopConv
end
noncomputable section
namespace GlobalTheory.TopConv
set_option maxHeartbeats 1000000 in
theorem top_comb_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) (v : WO (Yc D (j + 1)) D.sp.X' → ℂ), IsStepVecOf (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D (j + 1)) D.sp.X' (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).ΛX ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).βX ((_root_.GlobalTheory.Fam.pk_z W).datYt W.P.A3.A.μ0 (j + 1) (_root_.GlobalTheory.Fam.complexLevelStructure W)) ((_root_.GlobalTheory.Fam.pk_z W).chi D.R.m) ((_root_.GlobalTheory.Fam.pk_z W).Q W.P.A3.A.μ0) ((_root_.GlobalTheory.Fam.pk_z W).xiR W.P.A3.A.μ0) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) v → ∃ b : WO (Yc D (j + 1)) D.sp.X' →₀ ℂ, IsFinComb b ∧ comb (_root_.GlobalTheory.Fam.pk_z W).ψ (Yc D (j + 1)) D.sp.X' b v = Eq.rec (motive := fun n _ => WO (Yc D n) D.sp.X' → ℂ) ((_root_.GlobalTheory.Fam.pk_z W).vX W.P.A3.A.μ0) (idx_top h) := by
  intro D L hT Gi Gl Kc Yd cX ex W hP j h v hv
  have hLev := hP.bot.hyp.2.2.2.1.lev
  obtain ⟨cY, hbY⟩ := hLev.βY (j + 1) (by omega)
  obtain ⟨cX', hbX⟩ := hLev.βX
  have sdY : IsSelfDualC (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) :=
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hLev.βY (j + 1) (by omega))
  have sdX : IsSelfDualC D.sp.X' (_root_.GlobalTheory.Fam.pk_z W).ΛX := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hLev.βX
  have hr : (Yc D (j + 1)).rank ≤ D.sp.X'.rank := by
    rw [D.sp.Y_rank _ (min_le_right _ _), D.sp.X'_rank]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (min_le_right _ _)) _
  have key : ∀ n (e : D.R.m - 1 = n), IsStepVecOf (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D n) D.sp.X' (cart ((_root_.GlobalTheory.Fam.pk_z W).MY n)) (cart (_root_.GlobalTheory.Fam.pk_z W).MX)
      ((_root_.GlobalTheory.Fam.pk_z W).ΛY n) (_root_.GlobalTheory.Fam.pk_z W).ΛX ((_root_.GlobalTheory.Fam.pk_z W).βY n) (_root_.GlobalTheory.Fam.pk_z W).βX ((_root_.GlobalTheory.Fam.pk_z W).datYt W.P.A3.A.μ0 n (_root_.GlobalTheory.Fam.pk_z W).triv) ((_root_.GlobalTheory.Fam.pk_z W).chi D.R.m)
      ((_root_.GlobalTheory.Fam.pk_z W).Q W.P.A3.A.μ0) ((_root_.GlobalTheory.Fam.pk_z W).xiR W.P.A3.A.μ0) (Eq.rec (motive := fun n _ => WO (Yc D n) D.sp.X' → ℂ) (_root_.GlobalTheory.Fam.pk_z W).vacX e)
      (Eq.rec (motive := fun n _ => WO (Yc D n) D.sp.X' → ℂ) ((_root_.GlobalTheory.Fam.pk_z W).vX W.P.A3.A.μ0) e) := by
    intro n e
    subst e
    exact W.Q.charW.base.chain.vX _
  have hX := key (j + 1) (idx_top h)
  obtain ⟨d₁, hd₁, e₁⟩ := GlobalTheory.StepComb.exists_comb_of_isStepVecOf _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sdY sdX hbY.1 hbX.1 hX
  obtain ⟨d₂, hd₂, e₂⟩ := GlobalTheory.StepComb.exists_comb_of_isStepVecOf _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sdY sdX hbY.1 hbX.1 hv
  have hv0 : v ≠ 0 := (GlobalTheory.Chain.StepVac.stepVec_vac sdY sdX hr hv).2.1
  have hspan := comb_mem_span (_root_.GlobalTheory.Fam.pk_z W).ψ (GlobalTheory.Fam.VacTheta.isFinComb_of_combAt hd₂) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h)
  rw [← e₂] at hspan
  have hvac := GlobalTheory.T.vacuum_mem_span_heisenbergTranslates_of_ne_zero hv.1 sdY sdX hspan hv0
  obtain ⟨b, hb, hbv⟩ := exists_finComb_of_mem_span _ hvac
  obtain ⟨c, hc, hcc⟩ := isFinComb_comp (_root_.GlobalTheory.Fam.pk_z W).ψ (GlobalTheory.Fam.VacTheta.isFinComb_of_combAt hd₁) hb
  refine ⟨c, hc, ?_⟩
  rw [hcc, hbv]
  exact e₁.symm
end GlobalTheory.TopConv
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAtOfBWit
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.TopVal
section True
open GlobalTheory.Mem.Col2 GlobalTheory.Core.Rk.Top
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex)
theorem to_map_pr_x_eq_pk_at (t : W.P.T) (x : W.P.A3.A.fam.amb.FR t) (g : GA (I.rec7 l Z) (I.rec7 l Z).sp.X') (hg : g ∈ GfC (I.rec7 l Z).sp.X')
    (v : SmT (_root_.GlobalTheory.Fam.pk_z W).MX) :
    (_root_.GlobalTheory.Fam.pk_z W).cX.toMap (_root_.GlobalTheory.Fam.pk_z W).prX (((_root_.GlobalTheory.Fam.pk_z W).HX t).e ((_root_.GlobalTheory.Fam.pk_z W).jX t x)) v g = (_root_.GlobalTheory.Fam.pk_z W).prX (_root_.GlobalTheory.TopVal.packageAtPoint W t x g) v := by
  have h1 : (_root_.GlobalTheory.Fam.pk_z W).cX.ρ g⁻¹ = 1 := W.Q.charW.base.models.cX.1 _ (inv_mem hg)
  show (_root_.GlobalTheory.Fam.pk_z W).prX ((_root_.GlobalTheory.Fam.pk_z W).cX.ρ g⁻¹ (_root_.GlobalTheory.TopVal.packageAtPoint W t x g)) v = _
  rw [h1]
  rfl
set_option maxHeartbeats 1000000 in
theorem exists_is_j_pair_val_of_vanishing (hg : Formalism.L2.Forms.gramP (I.rec7 l Z) = 1) (u : B.Word) (cv : Val B →ₛₗ[B.embLL] (_root_.GlobalTheory.Fam.pk_z W).cX.W) (hE : _root_.GlobalTheory.TopVal.ValEqvAlt W cv)
    (hP : _root_.GlobalTheory.TopVal.PackageValuation W cv)
    (hi : ∀ (t : W.P.T) (φ : Frm I (W.P.I.tup t)) (x : W.P.A3.A.fam.amb.FR t), IsRes φ x →
      (∀ g y, HasMat g y → IsUni B y → _root_.GlobalTheory.TopVal.packageAtPoint W t x g = 0) → ∀ d, val φ d = 0) :
    ∃ j, IsJ u (_root_.GlobalTheory.Fam.pk_z W).MX j ∧ ∀ (t : W.P.T) (φ : Frm I (W.P.I.tup t)) (x : W.P.A3.A.fam.amb.FR t), IsRes φ x → ∀ d v,
      (_root_.GlobalTheory.Fam.pk_z W).prX (cv (val φ d)) v = pairVal B (j v) (val φ d) := by
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.SeeSaw.exists_isJ_of_par (GlobalTheory.SeeSaw.sg_trueColumns I l Z u) (_root_.GlobalTheory.Fam.pk_z W).MX rfl
  by_cases h0 : cv = 0
  · refine ⟨j₀, hj₀, fun t φ x hx d v => ?_⟩
    have hz := hi t φ x hx (fun g y h1 h2 => (hP t φ x hx g y h1 h2).trans (by rw [h0]; rfl)) d
    rw [hz, map_zero, map_zero, LinearMap.zero_apply]
    unfold pairVal
    rw [Submodule.coe_zero, map_zero, map_zero]
  · obtain ⟨a, ha, hJ⟩ := _root_.GlobalTheory.T.unit_gram_family_property_alt W hg u cv hE h0 j₀ hj₀
    exact ⟨a • j₀, isJ_smul hj₀ ha, fun t φ x _ d v => hJ _ v⟩
set_option maxHeartbeats 1000000 in
theorem reads_pk_alt (hOk : I.Ok) (hC : I.StdC l Z W.R.T.cols) (hW : _root_.GlobalTheory.AdForm.TwStdAlt W) (u : B.Word)
    (cv : Val B →ₛₗ[B.embLL] (_root_.GlobalTheory.Fam.pk_z W).cX.W) (hP : _root_.GlobalTheory.TopVal.PackageValuation W cv) (j : SmT (_root_.GlobalTheory.Fam.pk_z W).MX →ₗ[ℂ] (Formalism.L2.Forms.FrP (I.rec7 l Z) → ℂ))
    (t : W.P.T) (φ : Frm I (W.P.I.tup t)) (x : W.P.A3.A.fam.amb.FR t) (hx : IsRes φ x)
    (hV : ∀ d v, (_root_.GlobalTheory.Fam.pk_z W).prX (cv (val φ d)) v = pairVal B (j v) (val φ d))
    (G : (I.rec7 l Z).what₂.Amb (W.P.I.tup t)) (hG : RecVal u (W.P.I.tup t) φ G) :
    _root_.GlobalTheory.Fam.ReadsCoefficients W u j 1 (W.P.I.tup t) G ((_root_.GlobalTheory.Fam.pk_z W).cX.toMap (_root_.GlobalTheory.Fam.pk_z W).prX (((_root_.GlobalTheory.Fam.pk_z W).HX t).e ((_root_.GlobalTheory.Fam.pk_z W).jX t x))) := by
  refine _root_.GlobalTheory.TopVal.reads_of_pairVal W hC hW u j _ φ G hG _ fun g y pt v hy hp => ?_
  refine (_root_.GlobalTheory.TopVal.to_map_pr_x_eq_pk_at W t x g hy.1 v).trans ?_
  rw [hP t φ x hx g y hy hp.uni, GlobalTheory.T.decoratedLatticeOfAdelicMatrix_eq_rowPoint I hOk _ y pt hp]
  exact hV _ v
end True
set_option maxHeartbeats 2000000 in
theorem exists_read_at_pack_b_of_b_wit : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → Nonempty (Bl.RXs q.x.what₂) → ∀ u, ∃ j, _root_.GlobalTheory.Fam.LeadingReadAt (_root_.GlobalTheory.Fam.packB_alt b) u j 1 := by
  intro hL p K q c b hW ⟨rx⟩ u
  obtain ⟨hOk, ⟨hPins⟩, -, ⟨hC⟩, hTS⟩ := _root_.GlobalTheory.Fam.colsStd_of_bWit_alt q b hW
  have hg := (GlobalTheory.T.trueColumn_spaces_standard_in_frameCoords q.w.I hOk hPins q.w.l q.Z).2.1
  obtain ⟨cv, hE, hP⟩ := _root_.GlobalTheory.T.exists_valEqv_of_bWit_std q b hW rx.std
  obtain ⟨j, hJ, hV⟩ := _root_.GlobalTheory.TopVal.exists_is_j_pair_val_of_vanishing (I := q.w.I) (l := q.w.l) (Z := q.Z) (_root_.GlobalTheory.Fam.packB_alt b) hg u cv hE hP (_root_.GlobalTheory.T.pk_at_vanishing_of_is_uni q b hW)
  refine ⟨j, hJ, one_mem _, fun t => ⟨⟨fun h => _root_.GlobalTheory.T.level_group_reference_tuple_alt q b hW u t h,
    fun h => levG_one _ (_root_.GlobalTheory.T.mem_level_iff_twisted_class_alt q b hW u t h) (_root_.GlobalTheory.T.level_character_twisted_class_alt q b hW u t h)⟩, fun F F' hF => ?_⟩⟩
  obtain ⟨φ, hφ, hR⟩ := _root_.GlobalTheory.T.one_form_exists_heq_alt q b hW ⟨rx⟩ t F F' hF
  exact _root_.GlobalTheory.TopVal.reads_pk_alt (I := q.w.I) (l := q.w.l) (Z := q.Z) (_root_.GlobalTheory.Fam.packB_alt b) hOk hC hTS u cv hP j t φ _ hφ (hV t φ _ hφ) _ (hR u)
end GlobalTheory.TopVal
end
end

