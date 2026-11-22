import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0186
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0027
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0128
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0132
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0123
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0067
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0017
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0030
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0136
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0227
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0851
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0200
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0218
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0821
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0159
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle1028
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0823
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0135
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0816
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0019
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0018
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0164
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0197

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowLabOfLayer
section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.HeightCounting
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
namespace GlobalTheory.Fc.LabLinked
set_option maxHeartbeats 2000000 in
theorem typeLab_of_gen_alt_alt (hG : GlobalTheory.GLq.Green) (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing)
    {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch}
    (a : _root_.GlobalTheory.Mem.Top.Bl.NAtData hL D cf nch tp)
    (hl : GlobalTheory.SerSys.LabTie D fun k => @GlobalTheory.Mem.TypePl.labDat (D.host.g k) ⟨D.host.g_prime k⟩) (hp : _root_.GlobalTheory.Fc.LabLinked.GenPinAlt a)
    (rep : D.what₂.FT → Formalism.L2.NG.FinTyp D.host.E D.R.r) (hrep : HEq a.nt.rep rep) : GlobalTheory.LabPin.TypeLab D rep := by
  have e : ∀ (D' : D7), D' = withLoc a.nt.L →
      (GlobalTheory.SerSys.LabTie D' fun k => @GlobalTheory.Mem.TypePl.labDat (D'.host.g k) ⟨D'.host.g_prime k⟩) →
      ∀ rep' : D'.what₂.FT → Formalism.L2.NG.FinTyp D'.host.E D'.R.r, HEq a.nt.rep rep' → GlobalTheory.LabPin.TypeLab D' rep' := by
    rintro _ rfl hl' rep' hr
    obtain rfl := eq_of_heq hr
    refine _root_.UpperTheory.Lit.Dz.localBesselMultiplicityOne hG hZ hL a.nt.D a.nt.A.wdT a.nt.A.row a.nt.rep
      (fun k => @GlobalTheory.Mem.TypePl.labDat (a.nt.D.host.g k) ⟨a.nt.D.host.g_prime k⟩) a.nt.A.lab a.nt.row a.depth hl' ?_
    intro k v
    refine ⟨a.nt.A.grp.kv k v, ?_⟩
    rw [← hp k]
    exact a.nt.A.grp.tg_tame k v
  exact e D a.nt.eq hl rep hrep
section Rows
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.NX
set_option maxHeartbeats 1000000 in
theorem ties_of_nAtData_real (hG : GlobalTheory.GLq.Green) (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing)
    {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {cf : CharFrame D} {nch : NChoice D}
    {tp : TupTied D cf nch} {a : _root_.GlobalTheory.Mem.Top.Bl.NAtData hL D cf nch tp} {R : RealDat3 D A3 Ks} {F : Face3 D A3} {cG : G0 R.Pg D.R.r ≃* G0g D.nd}
    {X0 : BaseLevelRowSide D} {Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0} (r : _root_.GlobalTheory.Mem.Top.Bl.NormRealisationData a R F cG Y) {F0 : ∀ u, Formalism.L2.Forms.Forms0 D u}
    (s : SAt R.toRealDat F.lv2 Y.eE F0)
    (hl : GlobalTheory.SerSys.LabTie D fun k => @GlobalTheory.Mem.TypePl.labDat (D.host.g k) ⟨D.host.g_prime k⟩) (hp : _root_.GlobalTheory.Fc.LabLinked.GenPinAlt a)
    (hg : GoodFTAll D) : Ties D := by
  have hR := GlobalTheory.Mem.R3.RowFrameParts.main D G Pl0 I0 T A3 Ks R.toRealDat F.lv2 X0 Y
  have hT := _root_.GlobalTheory.Fc.LabLinked.typeLab_of_gen_alt_alt hG hZ a hl hp _ r.rep_eq
  exact ⟨s.P.X, s.P.G, s.S.hI.eHH,
    GlobalTheory.T.constructedSpectralObjects_irreducibilityConditions D G Pl0 T A3.A Ks R.toRealDat F.lv2 Y.eE F0 s Y.PY Y.hF
      (fun σ : D.what₂.FT => principalLevelFrame.rowRepR R.θ (Y.eFT σ)) hR.1 hR.2 hT hg⟩
end Rows
set_option maxHeartbeats 1000000 in
theorem ties_of_genPin_goodFTAll' (hG : GlobalTheory.GLq.Green) (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing)
    {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : WPt p.s K) (hp : _root_.GlobalTheory.Fc.LabLinked.GenPinAlt q.core_data_of_point.a)
    (hg : GoodFTAll (q.w.D q.Z)) : Ties (q.w.D q.Z) :=
  _root_.GlobalTheory.Fc.LabLinked.ties_of_nAtData_real hG hZ (D := (q.w.st q.Z).toD7) q.core_data_of_point.row q.saturationAtWeightedPoint (lab_of_rows q.x.what₂) hp hg
theorem ties_of_built_genPin (hG : GlobalTheory.GLq.Green) (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing)
    {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} (hp : ∀ (K : Ctx) (q : WPt p.s K), _root_.GlobalTheory.Fc.LabLinked.GenPinAlt q.core_data_of_point.a) {Q : V4.Slot} {κ : Par}
    {D : D7} {O : Obj D} {c : ℝ} {b : _root_.GlobalTheory.Fc.BundleCondition D O c} (hb : Built Q (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) κ D O c b) : GoodFTAll D → Ties D := by
  refine Built.ind (R := fun D _ _ _ => GoodFTAll D → Ties D) ?_ hb
  rintro K β c b - - ⟨q, b', -, e⟩
  have e1 : β.D = q.w.D q.Z := congrArg Sigma.fst e
  show GoodFTAll β.D → Ties β.D
  rw [e1]
  exact _root_.GlobalTheory.Fc.LabLinked.ties_of_genPin_goodFTAll' hG hZ q (hp K q)
theorem row_lab_of_good_alt_alt : GlobalTheory.GLq.Green → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → ∀ k, c.a.nt.A.grp.ζ k = @GlobalTheory.GLq.LabelDatum.gen _ ⟨c.a.nt.D.host.g_prime k⟩ (@GlobalTheory.Mem.TypePl.labDat (c.a.nt.D.host.g k) ⟨c.a.nt.D.host.g_prime k⟩)) → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) (fun Q Lk => Row Q Lk (AtAll fun D _ _ _ => GoodFTAll D)) → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.RL.RowLabelCondition := by
  intro hG hZ hL N S Γ hN ⟨R, hR, hrow⟩
  refine ⟨R, hR, hrow.imp fun 𝒜 σ s hA eps Fm hc x hx i => ?_⟩
  obtain ⟨κ, -, -, t⟩ := s Fm hc
  exact _root_.GlobalTheory.Fc.LabLinked.ties_of_built_genPin hG hZ (p := _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) (fun K q => hN _ _ _ _ _ _ _ _ _ _ _ _ _ q.x.nx.2) (t x hx i).1 (hA Fm hc x hx i)
theorem row_lab_of_layer_alt_alt : GlobalTheory.GLq.Green → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) (fun Q L => Row Q L (AtAll fun D _ _ (_ : _root_.GlobalTheory.Fc.BundleCondition _ _ _) => Formalism.BasicNotions.GoodFTAll D)) → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.RL.RowLabelCondition :=
  fun hG hZ hL N S Γ hN =>
    _root_.GlobalTheory.Fc.LabLinked.row_lab_of_good_alt_alt hG hZ hL N S Γ fun K B f T w Z Wt p0 t nch n xd c m =>
      (hN K B f T w Z Wt p0 t nch n xd c m).elim fun e => e.1.zeta
end GlobalTheory.Fc.LabLinked
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_ft_entries_alt_alt : GlobalTheory.GLq.Green → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) (fun Q L => Row Q L (AtAll fun D _ _ (_ : _root_.GlobalTheory.Fc.BundleCondition _ _ _) => Formalism.BasicNotions.GoodFTAll D)) → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.RL.RowLabelCondition := by
  first | exact @_root_.GlobalTheory.Fc.LabLinked.row_lab_of_layer_alt_alt | exact _root_.GlobalTheory.Fc.LabLinked.row_lab_of_layer_alt_alt | (intros; apply _root_.GlobalTheory.Fc.LabLinked.row_lab_of_layer_alt_alt <;> assumption)
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SeriesCoverOfPrimitive
section
set_option synthInstance.maxHeartbeats 200000

section
section
noncomputable section
namespace GlobalTheory.HeightCounting.Up.ChoiceEx
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
theorem stage_c_nonempty_of_published_inputs : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraModules → _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevelNonempty hL :=
  fun hCo hCW hHM a b hL => _root_.GlobalTheory.HeightCounting.Up.ChoiceEx.sc_of_sck_alt (_root_.GlobalTheory.T.stageCExists_of_casselmanWallach hCo hCW hHM a b hL)
end GlobalTheory.HeightCounting.Up.ChoiceEx
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stage_c_nonempty_of_prints_third_layer : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraModules → _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevelNonempty hL := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.ChoiceEx.stage_c_nonempty_of_published_inputs | exact _root_.GlobalTheory.HeightCounting.Up.ChoiceEx.stage_c_nonempty_of_published_inputs | (intros; apply _root_.GlobalTheory.HeightCounting.Up.ChoiceEx.stage_c_nonempty_of_published_inputs <;> assumption)
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SeriesStateB1OfGeometry
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting.Up GlobalTheory.Mem.R3.Tr
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
namespace GlobalTheory.HeightCounting.SerCopy
theorem series_state_b1_of_geometry_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {C : Formalism.L2.Pj.CoreJ D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat3 D A3 C.Q.c.F}
    {F : Face3 D A3} {X0 : BaseLevelRowSide D} {Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0} {cG : G0 R.Pg D.R.r ≃* G0g D.nd}
    {cf cf' : CharFrame D} (g : GlobalTheory.RealGeo.GeoHalf C R.toRealDat fun _ => 1) (a : _root_.GlobalTheory.HeightCounting.HeightCountingBaseData hL D cf (repOf Y)) (n : InRat Y cG)
    (PV : ∀ i : Fin D.R.m, principalLevelFrame.RowPsi (Vc D i) D.R.nV)
    {Pq Pq' : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host} {Rw : RowSide D} {kKs hk}
    {hk' : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL ((ratDatR R cG kKs hk).WL j)} {eig θ}
    (Bs : SideB D cf' Rw (lowAll D) Pq' (ratDatR R cG kKs hk) hk' eig θ) (YS : NExpRealS R cG (ratDatR R cG kKs hk))
    (eF : YS.eF = Bs.eF) (fi : ∀ i x, HEq ((YS.fi i).e x) x) (ser : SerAt YS g.v₀ Bs.exp PV cf' Pq') (tau : TauTrue Bs.exp)
    (e1 : cf' = cf) (e2 : Rw = a.A.row) (e3 : Pq' = Pq) (e4 : HEq hk' n.In.hL) (e5 : eig = n.In.eig) (e6 : θ = n.In.θ)
    (h1 : ∀ i, n.In.Sb ⊆ D.ntw.S0 i) (h2 : ∀ i, OverSet D (D.ntw.S0 i) (insert (D.ntw.l i) (lowAll D))) :
    Nonempty (_root_.GlobalTheory.HeightCounting.SeriesData g a n PV Pq) := by
  obtain rfl : kKs = n.kKs := RingHom.ext fun y => Subtype.ext ((hk y).trans (n.hk y).symm)
  subst e1 e2 e3 e5 e6
  cases e4
  exact ⟨{ Bs := Bs, Sb_le := h1, rootsOfUnityRing_le_wittIntegers := h2, lam := ⟨ser.lam, ser.lam_ok, ser.lam_teich, ser.lam_C, ser.lam_q, ser.lam_tie⟩
           YS := YS, eF := eF, fi := fi, ser := ser, tau := tau }⟩
variable {K : Ctx} {B : GlobalTheory.Mem.Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
theorem pre_at_of_side_b_tau_true_lam_ok (hA : GlobalTheory.Published.GlobalArtinReciprocity) {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (hK : K.Over B.toPre)
    (hS : Start K B f T w) (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x)
    (hB : ∃ Bs : SideB (Dof x) (cfOf x) l.a.A.row (lowAll (Dof x)) l.Pq l.rat.S l.rat.In.hL l.rat.In.eig l.rat.In.θ, TauTrue Bs.exp)
    (hSb : ∀ i, l.rat.In.Sb ⊆ (Dof x).ntw.S0 i) (hZ : ∃ Z : GlobalTheory.LamTie.LamDat (Dof x), Z.Ok) :
    PreAt (P := P) x.m.z l.a.A.row l.Pq l.rat.In.hL l.rat.In.eig l.rat.In.θ := by
  obtain ⟨h1, h2, h3, h4, -⟩ := _root_.GlobalTheory.T.isChoice_of_start_of_over hL hK hS x l.toLA
  obtain ⟨Bs, hτ⟩ := sideB_tau_congr h4.symm rfl rfl HEq.rfl hB
  exact ⟨h4, l.rat.kKs, l.rat.hk, l.rat.In.hL, HEq.rfl, Bs, x.r.Y.hF, hτ,
    GlobalTheory.T.exists_newThetaData_series_classSums_lattices hA (Dof x) _ _ _ _ _ _ x.m.z.R x.m.z.F x.m.z.cG l.rat.kKs l.rat.hk _ _ _ _ _ Bs l.rat.In.Sb x.m.z.geo.v₀ x.r.Y.hF
      x.m.z.pins x.m.intersectionNumber_baseChange (fun j => x.m.z.geo.fw.hv₀ j _) x.m.z.geo.fw.ks l.rat.rat.hecke hSb hτ (h4 ▸ l.a.A.chr) (h4 ▸ l.a.val)
      l.a.elem.split l.Pq_over h1 h2 hZ h3⟩
theorem pre_at_twisted_copy_of_side_b_tau_true (hA : GlobalTheory.Published.GlobalArtinReciprocity) {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (hK : K.Over B.toPre)
    (hS : Start K B f T w) (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x) (N : TwNew (Dof x))
    (hB : ∃ Bs : SideB N.toD7 (N.cf (cfOf x)) (N.row l.a.A.row) (lowAll (Dof x)) l.Pq (N.rat l.rat.S) l.rat.In.hL l.rat.In.eig
      l.rat.In.θ, TauTrue Bs.exp)
    (hSb : ∀ i, l.rat.In.Sb ⊆ N.tw.S0 i) (hZ : ∃ Z : GlobalTheory.LamTie.LamDat N.toD7, Z.Ok) :
    PreAt (P := P) (datTw x N) ((by with_unfolding_all exact ((N.row l.a.A.row) :))) ((by with_unfolding_all exact (l.Pq :))) l.rat.In.hL ((by with_unfolding_all exact (l.rat.In.eig :))) ((by with_unfolding_all exact (l.rat.In.θ :))) := by
  obtain ⟨x', l', ho, -, hrow, hPq, hS', hSb', hhL, heig, hθ, hR, hcG, hgeo⟩ := _root_.GlobalTheory.T.twisted_state_transport_heq_levels' hL x l N
  obtain ⟨o', fits', G_eq', etaF', bk', m', copy', coh', s', r', pin'⟩ := x'
  dsimp only at ho
  subst ho
  have hz : m'.z = datTw x N := moved_eq_datTw x N m' copy' hR hcG hgeo
  have e1 : l'.a.A.row = (by with_unfolding_all exact ((N.row l.a.A.row) :)) := (by with_unfolding_all exact ((eq_of_heq hrow) :))
  have e2 : l'.Pq = (by with_unfolding_all exact (l.Pq :)) := (by with_unfolding_all exact ((eq_of_heq hPq) :))
  have e3 : l'.rat.S = (by with_unfolding_all exact ((N.rat l.rat.S) :)) := (by with_unfolding_all exact ((eq_of_heq hS') :))
  have e4 : l'.rat.In.Sb = (by with_unfolding_all exact (l.rat.In.Sb :)) := (by with_unfolding_all exact ((eq_of_heq hSb') :))
  have e5 : l'.rat.In.eig = (by with_unfolding_all exact (l.rat.In.eig :)) := (by with_unfolding_all exact ((eq_of_heq heig) :))
  have e6 : l'.rat.In.θ = (by with_unfolding_all exact (l.rat.In.θ :)) := (by with_unfolding_all exact ((eq_of_heq hθ) :))
  have h := _root_.GlobalTheory.HeightCounting.SerCopy.pre_at_of_side_b_tau_true_lam_ok hA hK hS _ l' (by
    rewrite [e1, e5, e6]
    exact sideB_tau_congr rfl e2.symm e3.symm hhL.symm ((by with_unfolding_all exact (hB :)))) (by rewrite [e4]; exact (by with_unfolding_all exact (hSb :))) ((by with_unfolding_all exact (hZ :)))
  exact preAt_congr hz e1 e2 hhL e5 e6 h
section Install
variable {x : St P} {N₁ : TwNew (Dof x)} {kKs : (datTw x N₁).core.Q.c.F →+* ↥(DN x N₁).LL0}
  {hk : ∀ y, ((kKs y : ↥(DN x N₁).LL0) : (DN x N₁).what₂.LL) = algebraMap (datTw x N₁).core.Q.c.F (DN x N₁).what₂.LL y}
  {cf : CharFrame (DN x N₁)} {Rw : RowSide (DN x N₁)}
  {Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield (DN x N₁).host.E)) → PlE (DN x N₁).host} {hf eig θ}
  {Bs : SideB (DN x N₁) cf Rw (lowAll (DN x N₁)) Pq (ratDatR (datTw x N₁).R (datTw x N₁).cG kKs hk) hf eig θ} {hF}
  (p : PreTie (ysOf Bs) (datTw x N₁).geo.v₀ Bs.exp hF Pq)
theorem series_state_b1_twist_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (hτ : TauTrue Bs.exp) (hC : cf = TC.cf w.I w.l (oTw x N₁).Z)
    (hu : GlobalTheory.UnivChar.IsUnivChar (DN x N₁).nexp) (ho : NoOff (DN x N₁))
    (z : Dat (w.st (oTw x (nP p)).Z) w.I P.hX T P.Wt) (hz : z = datTw x (nP p)) {X0 : BaseLevelRowSide (DN x (nP p))}
    (Y : R3.Read z.R.toRealDat z.F.lv2 X0) (a : _root_.GlobalTheory.HeightCounting.HeightCountingBaseData hL (DN x (nP p)) (TC.cf w.I w.l (oTw x (nP p)).Z) (repOf Y)) (n : InRat Y z.cG)
    (PV : ∀ j : Fin (DN x (nP p)).R.m, principalLevelFrame.RowPsi (Vc (DN x (nP p)) j) (DN x (nP p)).R.nV) {hF'}
    (hPV : ∀ j, GlobalTheory.MtRead.IdFrame hF' (PV j))
    (Pq' : HeightOneSpectrum (𝓞 (maximalRealSubfield (DN x (nP p)).host.E)) → PlE (DN x (nP p)).host)
    (hZ : ∃ Z : GlobalTheory.LamTie.LamDat (DN x (nP p)), Z.Ok ∧ Z.Teich ∧ Z.C = TC.cf w.I w.l (oTw x (nP p)).Z ∧
      Z.q0 = AbsolutelyIrreducibleSpan.q0 (DN x (nP p)) ∧ GlobalTheory.LamTie.IsLamTieFull (DN x (nP p)).ntw Z)
    (e2 : HEq a.A.row ((kwP p).row Rw)) (e3 : HEq Pq' Pq) (e4 : HEq n.In.hL hf) (e5 : HEq n.In.eig eig) (e6 : HEq n.In.θ θ)
    (h1 : ∀ i, n.In.Sb ⊆ (DN x (nP p)).ntw.S0 i)
    (h2 : ∀ i, OverSet (DN x (nP p)) ((DN x (nP p)).ntw.S0 i) (insert ((DN x (nP p)).ntw.l i) (lowAll (DN x (nP p))))) :
    Nonempty (_root_.GlobalTheory.HeightCounting.SeriesData z.geo a n PV Pq') := by
  subst hz
  obtain ⟨Z, z1, z2, z3, z4, z5⟩ := hZ
  have e1 : ((by with_unfolding_all exact (((kwP p).cf cf) :)) : CharFrame (DN x (nP p))) = TC.cf w.I w.l (oTw x (nP p)).Z := (by with_unfolding_all exact ((congrArg (kwP p).cf hC) :))
  exact _root_.GlobalTheory.HeightCounting.SerCopy.series_state_b1_of_geometry_alt _ a n PV (bsP p) (ysP p) ((by with_unfolding_all exact ((Eq.refl Bs.eF) :))) ((by with_unfolding_all exact ((ysOf_fi Bs) :)))
    ((by with_unfolding_all exact ((serP p hu ho Bs.bsup PV hPV Z ⟨z1, z2, z3.trans e1.symm, z4, z5⟩) :))) ((by with_unfolding_all exact (hτ :))) e1 ((by with_unfolding_all exact ((eq_of_heq e2).symm :)))
    ((by with_unfolding_all exact ((eq_of_heq e3).symm :))) ((by with_unfolding_all exact (e4.symm :))) ((by with_unfolding_all exact ((eq_of_heq e5).symm :))) ((by with_unfolding_all exact ((eq_of_heq e6).symm :))) h1 h2
end Install
end GlobalTheory.HeightCounting.SerCopy
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SlotMvPin
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.NLink.Final
section Slot
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
set_option maxHeartbeats 4000000 in
theorem slot_mv_extension_with_list_geo_cl (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (cDep : ℝ) (Γ : GeoP) :
    PositionMv (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithList hL cDep) SExt.none (geoCl Γ)).s := by
  intro K B f T w Z O x N h O' hO' col n
  obtain ⟨t', hs, hgeo, hpk, hobj, hrx⟩ := GlobalTheory.T.rows_pass_to_moved_divisionLatticesHeights K B f T w Z x.Wt O x.what₂ N h O' hO'
  obtain ⟨nch', xd', -, hnx, -, -, hmv⟩ := _root_.GlobalTheory.T.exists_kept_choice_upper_lattice_alt hL K B f T w Z x.Wt Z.S N h O.nch O.xd
  obtain ⟨hn1, hn2⟩ := hnx rfl
  subst hO'
  have e1 : nch' = (O.tr N h).nch := eq_of_heq hn1
  have e2 : xd' = (O.tr N h).xd := eq_of_heq hn2
  subst e1 e2
  have hlp := GlobalTheory.Mem.GridMove.listPin_rowsSame cDep K.s.b K B f T w Z x.Wt Z.S N h O.p0 x.what₂ (O.tr N h).p0 t' hs x.nx.2.2.down
  obtain ⟨c⟩ := hmv O.p0 x.what₂ x.n (O.tr N h).p0 t' n hs hgeo ⟨x.nx.1, x.nx.2.1⟩
  obtain ⟨s⟩ := GlobalTheory.T.spectralStageData_transfer_lattices_heights K B f T w Z x.Wt O.p0 x.what₂ x.col.toColT N h (O.tr N h).p0 t' col.toColT hpk ⟨x.sx.1⟩
  obtain ⟨o⟩ := GlobalTheory.T.divisionGeometryScalars_transfer_setDivision Γ K B f T w Z x.Wt N h O (O.tr N h) rfl x.what₂ t' hs x.ox
  exact ⟨t', hobj x.obj, hrx ⟨x.rx⟩, ⟨⟨c.1, c.2, ⟨hlp⟩⟩⟩, ⟨⟨s, PUnit.unit⟩⟩, ⟨o⟩⟩
end Slot
end GlobalTheory.NLink.Final
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SlotMvPrmRNel
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
noncomputable section
namespace GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 4000000
theorem movable_prmR_nel_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (cDep : ℝ) (Γ : GeoP), PositionMv (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) SExt.none (geoCl Γ)).s := by
  intro hL cDep Γ
  intro K B f T w Z O x N h O' hO' col n
  obtain ⟨t', hs, hgeo, hpk, hobj, hrx⟩ := GlobalTheory.T.rows_pass_to_moved_divisionLatticesHeights K B f T w Z x.Wt O x.what₂ N h O' hO'
  obtain ⟨nch', xd', hkept, hnx, -, -, hmv⟩ := _root_.GlobalTheory.T.exists_kept_choice_upper_lattice_alt hL K B f T w Z x.Wt Z.S N h O.nch O.xd
  obtain ⟨hn1, hn2⟩ := hnx rfl
  subst hO'
  have e1 : nch' = (O.tr N h).nch := eq_of_heq hn1
  have e2 : xd' = (O.tr N h).xd := eq_of_heq hn2
  subst e1 e2
  have hlp := GlobalTheory.Mem.GridMove.listPin_rowsSame cDep K.s.b K B f T w Z x.Wt Z.S N h O.p0 x.what₂ (O.tr N h).p0 t' hs x.nx.2.1.2.down
  obtain ⟨P, y, l, hls, hW, hk⟩ := x.nx.2.2.down
  obtain ⟨c⟩ := hmv O.p0 x.what₂ x.n (O.tr N h).p0 t' n hs hgeo ⟨x.nx.1, x.nx.2.1.1⟩
  obtain ⟨s⟩ := GlobalTheory.T.spectralStageData_transfer_lattices_heights K B f T w Z x.Wt O.p0 x.what₂ x.col.toColT N h (O.tr N h).p0 t' col.toColT hpk ⟨x.sx.1⟩
  obtain ⟨o⟩ := GlobalTheory.T.divisionGeometryScalars_transfer_setDivision Γ K B f T w Z x.Wt N h O (O.tr N h) rfl x.what₂ t' hs x.ox
  exact ⟨t', hobj x.obj, hrx ⟨x.rx⟩, ⟨⟨c.1, ⟨c.2, ⟨hlp⟩⟩, ⟨⟨P, y, l, hls, hW, kept_trans hk hkept⟩⟩⟩⟩, ⟨⟨s, PUnit.unit⟩⟩, ⟨o⟩⟩
end GlobalTheory.HeightCounting.Up
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThirdSeriesWithLocalConditions
section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.HeightCounting
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.CenFrame
section Mat
variable {k : Type} [CommRing k] {n n' r t : ℕ}
end Mat
section Loc
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
end Loc
section Lev
variable {D : D7}
end Lev
section Core
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
end Core
section Main
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
end Main
end GlobalTheory.CenFrame
namespace GlobalTheory.SerThird
open Formalism.MainNotions.N Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting.Up GlobalTheory.CenFrame
attribute [local instance] GlobalTheory.TypeRec.factG
set_option maxHeartbeats 4000000 in
theorem exists_character_choice_with_loc_of_built (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hP : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B}
    {w : ColW B f T} {P : Pre2 K w} (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) (big : (Dof x).what₂.places.Pl → Finset ℂ)
    (L : LocAll (lay0 (Dof x))) (hB : _root_.GlobalTheory.CoefDuty.BuiltAlt l.a.A l.mt.M l.c.ch l.c.tp.tup big L) :
    ∃ Q : _root_.GlobalTheory.NPin.CharacterChoiceData hL (withLoc L), Q.M = mtL L l.mt.M := by
  obtain ⟨Sp, ⟨Au⟩, ss⟩ := hB
  have hmt : MtInput (Dof x) l.mt.M l.c.tp.tup l.c.ch.Q := by
    have key : ∀ (xi : (Dof x).what₂.Tup → HChar (Dof x).host.E) (Q : (Dof x).what₂.places.Pl → Finset (PlE (Dof x).host)),
        MtInput (Dof x) l.mt.M (fun μ j => (cfOf x).mu0 j * xi μ) Q → l.c.tp.xi = xi → l.c.ch.Q = Q →
          MtInput (Dof x) l.mt.M l.c.tp.tup l.c.ch.Q := by
      intro xi Q h hx hQ
      subst hx hQ
      exact h
    exact key _ _ l.mt.mt l.c.xi_eq l.c.Q_eq
  let nt : _root_.GlobalTheory.HeightCounting.NormChoiceRealisation hL (withLoc L) (cfL L (cfOf x)) (chL L l.c.ch) (tpL L l.c.tp) :=
    { D := Dof x, cf := cfOf x, jE := l.a.jE, A := l.a.A, cg := l.a.cg, au := l.a.au, rep := repOf x.r.Y, row := l.a.row,
      low := lowAll (Dof x), Pq := l.Pq, S := l.rat.S, hL := l.rat.In.hL, eig := l.rat.In.eig, θ := l.rat.In.θ, Bs := l.b.Bs,
      M := l.mt.M, C := l.c.ch, tp := l.c.tp, ch := l.c.side, mt := hmt, big := big, L := L, Sp := Sp, Au := Au, ss := ss,
      eq := rfl, pack := rfl }
  have hval : ValLL0 (withLoc L) (cfL L (cfOf x)) :=
    ⟨l.a.val.mu0, l.a.val.eta, l.a.val.chiPsi, l.a.val.del, l.a.val.del'⟩
  obtain ⟨Q, -, -, -, -, h5⟩ := _root_.GlobalTheory.NPin.exists_character_choice_of_nTrue_split hL _ _ _ _ nt hval
    (fun σ σ' h => x.r.Y.eFT.injective (Formalism.IndefR.principalLevelFrame.rowRepR_inj _ _ _ h)) l.a.elem.star l.a.elem.int l.a.elem.split
    (GlobalTheory.ChebSplitDense.chebSplit_nd hP.what₂.cheb _)
  exact ⟨Q, eq_of_heq h5⟩
set_option maxHeartbeats 4000000 in
theorem locComp_of_isRc_classMapD_cenLoc : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → AllSt fun _ _ _ _ _ _ x =>
    ∀ l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x, _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' => SumRepresentations.hypO D' → GlobalTheory.TypeLeaf.SerLoc D' := by
  intro hL hP
  refine StepW.of_all ?_
  intro K B f T w _ _ _ P x l
  refine ⟨fun _ => ∅, fun Lc hB _ => ?_⟩
  obtain ⟨Pn, hM⟩ := _root_.GlobalTheory.SerThird.exists_character_choice_with_loc_of_built hL hP x l _ Lc hB
  exact _root_.UpperTheory.Lit.Dz.compatibleSystemLocalProperty_explicit hP.what₂ hP.green hP.zel hL (withLoc Lc) Pn _ (labTie_withLoc x Lc) (_root_.GlobalTheory.SerThird.tame_coupled_with_loc x l Lc)
    (hM ▸ _root_.GlobalTheory.SerThird.cenLoc_third_alt x l Lc)
end GlobalTheory.SerThird
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ser_loc_eventually_of_built : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → AllSt fun _ _ _ _ _ _ x => ∀ l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x, _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' => SumRepresentations.hypO D' → GlobalTheory.TypeLeaf.SerLoc D' := by
  first | exact @_root_.GlobalTheory.SerThird.locComp_of_isRc_classMapD_cenLoc | exact _root_.GlobalTheory.SerThird.locComp_of_isRc_classMapD_cenLoc | (intros; apply _root_.GlobalTheory.SerThird.locComp_of_isRc_classMapD_cenLoc <;> assumption)
end
end
end

