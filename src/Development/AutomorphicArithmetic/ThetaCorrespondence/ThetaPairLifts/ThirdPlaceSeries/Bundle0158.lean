import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0997
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0133
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0027
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0153
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0793
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0123
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0067
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0128
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0024
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0783
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TypePlacesCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0794
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealTB
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0031
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0033
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0037
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0030
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0035
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0044
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0040
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0029
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0045
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0032
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0093
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0041
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0048
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0381
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0018

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedAtAtMemStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_twisted_place_at_member : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ _ _ _ _ => ∃ v, TwistedAt (w.D Z) v := by
  first | exact @_root_.GlobalTheory.GalLoc.twistedAt_atMem_alt | exact _root_.GlobalTheory.GalLoc.twistedAt_atMem_alt | (intros; apply _root_.GlobalTheory.GalLoc.twistedAt_atMem_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistsAtLinked
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.Mem.LiteralAutomorphy.TwAtLink
open GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems (Twisted SamePair SameBelow LiesUnder TwistedPlaceSettings)
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx}
theorem Q_eq_alt (q : WPt p.s K) {w w' : (q.w.D q.Z).what₂.places.Pl} (hw : Twisted (q.w.D q.Z) w)
    (hw' : Twisted (q.w.D q.Z) w') (h : SamePair (q.w.D q.Z) w w') :
    q.O.ex.nch.Q w = q.O.ex.nch.Q w' ∧ q.O.ex.nch.k' w = q.O.ex.nch.k' w' := by
  have key : ∀ v v', Twisted (q.w.D q.Z) v → Twisted (q.w.D q.Z) v' → SameBelow (q.w.D q.Z) v v' →
      q.O.ex.nch.Q v = q.O.ex.nch.Q v' ∧ q.O.ex.nch.k' v = q.O.ex.nch.k' v' := by
    intro v v' hv hv' hs
    have m : ∀ u, Twisted (q.w.D q.Z) u → u ∈ q.x.Wt := fun u hu => by
      by_contra hn
      exact hu (q.x.what₂.mu.off u hn)
    have a := q.x.n.Q v (m v hv)
    have a' := q.x.n.Q v' (m v' hv')
    have c := q.x.coh.same v v' fun x hx => hs ⟨x, hx⟩
    exact ⟨a.1.trans (c.1.trans a'.1.symm), a.2.trans (c.2.1.trans a'.2.symm)⟩
  rcases h with h | h
  · exact key w w' hw hw' h
  · have k := key _ w' ((GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.twisted_conj w).2 hw) hw' h
    have c := q.core_data_of_point.a.all.choice.conj w hw
    exact ⟨(congrArg (fun t : TwPack _ => t.2.1) c).symm.trans k.1, (congrArg (fun t : TwPack _ => t.2.2.1) c).symm.trans k.2⟩
theorem twists_at_linked_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) (Q : V4.Slot), RowE Q (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) fun _ D O _ _ => (∀ w, GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.Twisted D w → D.ntw.l (O.ex.nch.twI w) = D.what₂.places.resChar w ∧ (GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.LiesUnder D (O.ex.nch.twI w) w ∨ GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.LiesUnder D (O.ex.nch.twI w) (D.what₂.places.conj w))) ∧ (∀ w w', GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.Twisted D w → GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.Twisted D w' → GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.SamePair D w w' → O.ex.nch.Q w = O.ex.nch.Q w' ∧ O.ex.nch.k' w = O.ex.nch.k' w' ∧ (O.ex.nch.Q w ≠ ∅ → O.ex.nch.twI w = O.ex.nch.twI w')) ∧ (∀ w, TwistedAt D w → BlochKatoReduction.Gen.QOk D.ntw (O.ex.nch.twI w) (O.ex.nch.Q w)) ∧ ∃ N0 : D.ntw.Tw → ℕ, ∀ w, TwistedAt D w → ∀ a : ℤ, IsCoprime a (D.ntw.l (O.ex.nch.twI w) : ℤ) → BlochKatoReduction.Gen.partC N0 (O.ex.nch.twI w) (O.ex.nch.Q w) (O.ex.nch.k' w) (O.ex.nch.psi' w ^ a) (twEps D (O.ex.nch.twI w)) := by
  intro hL p Q
  refine RowE.of_all fun κ K β c b _ _ hl => ?_
  obtain ⟨q, b', -, he⟩ := hl
  have h1 := congrArg (fun s : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Fc.BundleCondition D O c =>
    (fun (D : D7) (O : Obj D) => (∀ w, GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.Twisted D w → D.ntw.l (O.ex.nch.twI w) = D.what₂.places.resChar w ∧ (GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.LiesUnder D (O.ex.nch.twI w) w ∨ GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.LiesUnder D (O.ex.nch.twI w) (D.what₂.places.conj w))) ∧ (∀ w w', GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.Twisted D w → GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.Twisted D w' → GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.SamePair D w w' → O.ex.nch.Q w = O.ex.nch.Q w' ∧ O.ex.nch.k' w = O.ex.nch.k' w' ∧ (O.ex.nch.Q w ≠ ∅ → O.ex.nch.twI w = O.ex.nch.twI w')) ∧ (∀ w, TwistedAt D w → BlochKatoReduction.Gen.QOk D.ntw (O.ex.nch.twI w) (O.ex.nch.Q w)) ∧ ∃ N0 : D.ntw.Tw → ℕ, ∀ w, TwistedAt D w → ∀ a : ℤ, IsCoprime a (D.ntw.l (O.ex.nch.twI w) : ℤ) → BlochKatoReduction.Gen.partC N0 (O.ex.nch.twI w) (O.ex.nch.Q w) (O.ex.nch.k' w) (O.ex.nch.psi' w ^ a) (twEps D (O.ex.nch.twI w))) s.1 s.2.1) he
  refine cast h1.symm ?_
  obtain ⟨I, -, hI, -⟩ := q.x.good.tw
  exact ⟨fun w hw => ⟨q.O.ex.nch.twI_l w, GlobalTheory.TwistGoodCompare.atPlace_of_tie q.B.coeffGaloisSubfield_isGalois q.O.ex.nch_tie w hw⟩,
    fun w w' hw hw' h => ⟨(_root_.GlobalTheory.Mem.LiteralAutomorphy.TwAtLink.Q_eq_alt q hw hw' h).1, (_root_.GlobalTheory.Mem.LiteralAutomorphy.TwAtLink.Q_eq_alt q hw hw' h).2, twI_eq q.x.good hw hw' (_root_.GlobalTheory.Mem.LiteralAutomorphy.TwAtLink.Q_eq_alt q hw hw' h).1⟩, cond_powers hI⟩
end GlobalTheory.Mem.LiteralAutomorphy.TwAtLink
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TypePlacesCoverStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gPlaces_of_levelA : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ _ _ _ _ _ x => _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x → GPlaces (Dof x) := by
  first | exact @_root_.GlobalTheory.TypePlacesCover.gPlaces_all_alt | exact _root_.GlobalTheory.TypePlacesCover.gPlaces_all_alt | (intros; apply _root_.GlobalTheory.TypePlacesCover.gPlaces_all_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightOnePlacesFiniteOfWitness
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3 NumberField IsDedekindDomain
noncomputable section
namespace GlobalTheory.Mem.Top.Bl
set_option maxHeartbeats 4000000 in
theorem zscale_f0_of_witness_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : WPt p.s K) {c : ℝ}
    (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c) (w : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b) (hsc : q.O.L.sc = K.s) :
    HEq (w.a.Zsc (zsOf q.x.what₂.r.z.R q.x.what₂.r.z.F)).F0 (F0K K.s (q.w.D q.Z)) := by
  have hK : DV.KapDef (q.w.D q.Z) := b.R.T.what₂.ka
  have hB : ∀ Zs, HEq ((_root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b).Zsc Zs).F0 (F0K K.s (q.w.D q.Z)) := by
    intro Zs
    apply heq_of_eq
    funext y j
    rw [← hsc]
    exact (forcedContent_eq_closedContent_numericalDatum _ _ _ _ hK y j).symm
  obtain ⟨x, a, ax, y, _⟩ := w
  cases ax
  have hX := y.eq ▸ hB
  letI := a.x.grp
  letI := a.x.fin
  have hX' : ∀ Zs : DefSub a.x.A3.fam3.amb3, HEq (a.x.F.Zsc Zs).F0 (F0K K.s (q.w.D q.Z)) := hX
  dsimp only
  clear * - hX'
  obtain ⟨Dc, Sp, Zsc, lam, err, lam_eq, x', pack, _⟩ := a
  dsimp only at hX' ⊢
  obtain ⟨G, grp, fin, Pl0, I0, T0, A3, core, alg, R, F, cG, _⟩ := x'
  dsimp only at pack hX' ⊢
  cases pack
  exact hX' _
set_option maxHeartbeats 4000000 in
theorem weight_one_places_finite_of_witness : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) (K : Ctx) (q : WPt p.s K) (c : ℝ)
    (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → q.O.L.sc = K.s →
    (∀ v, (b.B.Q.Rl.toCx3 b.B.Q.F).W1 b.B.Q.F.cr (b.B.Q.Rl.num b.B.Q.F 0 0) v → v ∈ b.B.Q.Rl.twPl) ∧
      b.B.Q.Rl.toRealDat.ExAt ∧ Finite b.P.T := by
  intro hL p K q c b w hsc
  have hZ := _root_.GlobalTheory.Mem.Top.Bl.zscale_f0_of_witness_alt q b w hsc
  obtain ⟨x, a, ax, y, _⟩ := w
  cases ax
  letI := a.x.grp
  letI := a.x.fin
  letI : Algebra (↥a.x.core.Q.c.F) (q.w.D q.Z).what₂.LL := a.x.alg
  have h3 : _root_.Formalism.IndefR.IndefiniteRealisationNormalisationDegreeThree (_root_.GlobalTheory.Mem.R3.realisationOfInput y.y) :=
    _root_.GlobalTheory.Mem.R3.realPins3_realTOf_alt K q.B q.f q.T q.w q.Z q.x.Wt _ _ _ _ _ _ _ q.O.ex q.x.what₂ a b.R b.S y.y hZ
  have hP : (fun r : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S => _root_.Formalism.IndefR.IndefiniteRealisationNormalisationDegreeThree r.B.Q ∧ r.B.Q.Rl.toRealDat.ExAt ∧ Finite r.P.T) (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput y.y) :=
    ⟨h3, y.intersectionNumber_baseChange.aux.ex, finite_T_of_twArgs a⟩
  rw [← y.eq] at hP
  exact ⟨hP.1.w1 0 0, hP.2.1, hP.2.2⟩
end GlobalTheory.Mem.Top.Bl
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightParamOfPinStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.NPin GlobalTheory.NFacts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_param_of_character_choice : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.WeightParam D := by
  first | exact @_root_.GlobalTheory.weightParam_of_pin_alt | exact _root_.GlobalTheory.weightParam_of_pin_alt | (intros; apply _root_.GlobalTheory.weightParam_of_pin_alt <;> assumption)
end
end

