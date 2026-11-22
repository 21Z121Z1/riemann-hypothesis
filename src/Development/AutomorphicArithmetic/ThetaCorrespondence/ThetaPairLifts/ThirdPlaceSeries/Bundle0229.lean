import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LinkedBundlesGoodOfLocalLanglandsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0027
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0128
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0132
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0123
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0067
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0164
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0030
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0133
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0160
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0227
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0017
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0837
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0200
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0204
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0225
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0206
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.Bundle0002
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsConj
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0198
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0195
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BciNarrowSwap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0923
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0197
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0024
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0018
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0226

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedBundlesGoodOfLocalLanglands
section
set_option synthInstance.maxHeartbeats 200000

section
section
noncomputable section
namespace GlobalTheory.Fc.GoodLinked
section Layer
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top
  GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 4000000 in
theorem goodFTAll_at_members_of_depthZero (h1 : GlobalTheory.GLq.Green) (h2 : GlobalTheory.Published.ZelevinskyPolynomialRing) :
    ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists,
    _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => GoodFTAll (w.D Z) := by
  intro hL
  have hA := _root_.GlobalTheory.T.coefficient_duty_pin_at_each_member hL
  have hO := GlobalTheory.TypeVecConj.typeVec
  refine EvG.imp (EvG.inter hA hO) fun K _ _ _ _ h => ?_
  refine large₂.imp (large₂.inter h.1 h.2) fun B f T _ g => ?_
  intro hK w Z Wt p0 t nch n xd c _ _ hpin
  have hop := g.1 hK w Z Wt p0 t nch n xd c ‹_› ‹_› hpin
  have hrow := g.2 hK w hpin Z Wt t.hX t.r.z p0 t.r.Y t.r.intersectionNumber_baseChange t.exAt t.inGeo t.grp t.grpAt
  refine _root_.UpperTheory.Lit.Dz.nonGaloisTwistType h1 h2 hL (w.D Z) _ nch n.tp c.a hop ?_
  have key : ∀ (D' : D7) (_ : D' = withLoc c.a.nt.L) (r' : D'.what₂.FT → NG.FinTyp D'.host.E D'.R.r), HEq c.a.nt.rep r' →
      (∀ (I : GlobalTheory.TypeRec.Ident D') cp, GlobalTheory.TypeRec.IsComp I r' cp → ∀ σ, ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V)
        (ρ : Representation ℂ (G0g D'.nd) V) (W : Submodule ℂ V) (x : V),
        (∀ k v, GlobalTheory.GoodTypes.ConjIn ρ W (GlobalTheory.GoodTypes.facHom D' k v) (cp σ k v).ρ) ∧ x ≠ 0 ∧ (∀ a, ρ.asAlgebraHom a x ∈ W) ∧
        ρ.asAlgebraHom D'.ntypes.e0 x = x) →
      ∀ (I : GlobalTheory.TypeRec.Ident c.a.nt.D) cp, GlobalTheory.TypeRec.IsComp I c.a.nt.rep cp → ∀ σ, ∃ (V : Type) (_ : AddCommGroup V)
        (_ : Module ℂ V) (ρ : Representation ℂ (G0g c.a.nt.D.nd) V) (W : Submodule ℂ V) (x : V),
        (∀ k v, GlobalTheory.GoodTypes.ConjIn ρ W (GlobalTheory.GoodTypes.facHom c.a.nt.D k v) (cp σ k v).ρ) ∧ x ≠ 0 ∧
        (∀ b, ρ.asAlgebraHom b x ∈ W) ∧ ρ.asAlgebraHom c.a.nt.D.ntypes.e0 x = x := by
    rintro _ rfl r' hr h
    have e : c.a.nt.rep = r' := eq_of_heq hr
    rw [e]
    intro I cp hc σ
    exact h ⟨I.i, I.cont⟩ cp hc σ
  exact key _ c.a.nt.eq _ c.row.rep_eq hrow
end Layer
end GlobalTheory.Fc.GoodLinked
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.GroupRetwisting
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.Fc.GoodLinked
set_option maxHeartbeats 2000000 in
theorem largeBasePropertyG_goodRec_alt_alt (h1 : GlobalTheory.GLq.Green) (h2 : GlobalTheory.Published.ZelevinskyPolynomialRing)
    (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP)
    (hN : ∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c →
      Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) :
    GroupRetwisting.LargeBaseConditionG KPx (IsBuiltE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) GoodRec := by
  refine GlobalTheory.Mem.Top.EvG.imp (_root_.GlobalTheory.Fc.GoodLinked.goodFTAll_at_members_of_depthZero h1 h2 hL) fun K _ _ _ _ H => H.imp fun B f T _ t k C W V S' N G c q => ?_
  obtain ⟨w, Z, c', ⟨b, _⟩, e⟩ := q
  have key : ∀ x : Σ (C : Cols B) (Y : TC.Later B C), V4.Core K ⟨B, C, Y.W, Y.V, Y.S, Y.N, Y.G⟩ f T,
      x = ⟨w.C, Z, c'⟩ → Formalism.BasicNotions.GoodFTAll (⟨B, x.1, x.2.1.W, x.2.1.V, x.2.1.S, x.2.1.N, x.2.1.G⟩ : Stages).toD7 := by
    rintro _ rfl
    exact t k w Z c'.Wt c'.O.p0 b.what₂ c'.O.nch b.n c'.O.xd b.nx.1 ((hN _ _ _ _ _ _ _ _ _ _ _ _ _ b.nx.2).map Prod.fst) ⟨b.rx⟩ b.pin
  exact key _ e
theorem linkedAt_goodFTAll : GlobalTheory.GLq.Green → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP),
    (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c →
      Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) →
    _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) fun Q L => Row Q L (AtAll fun D _ _ (_ : _root_.GlobalTheory.Fc.BundleCondition _ _ _) => Formalism.BasicNotions.GoodFTAll D) :=
  fun h1 h2 hL N S Γ hN => LgModel.rowL_of_good (_root_.GlobalTheory.Fc.GoodLinked.largeBasePropertyG_goodRec_alt_alt h1 h2 hL N S Γ hN) (_root_.GlobalTheory.Fc.GoodLinked.row_goodRec_alt _)
theorem row_good_alt_alt : GlobalTheory.GLq.Green → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP),
    (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c →
      Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) →
    _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) (fun Q L => Row Q L (AtAll fun D _ _ (_ : _root_.GlobalTheory.Fc.BundleCondition _ _ _) => Formalism.BasicNotions.GoodFTAll D)) ∧
      _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.RL.RowGoodnessCondition := by
  intro h1 h2 hL N S Γ hN
  refine ⟨_root_.GlobalTheory.Fc.GoodLinked.linkedAt_goodFTAll h1 h2 hL N S Γ hN, ?_⟩
  obtain ⟨R, hR, h⟩ := _root_.GlobalTheory.Fc.GoodLinked.linkedAt_goodFTAll h1 h2 hL N S Γ hN
  refine ⟨R, hR, h.imp fun _ _ _ key => ?_⟩
  exact ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ hc => Ind.ev_of_atAll key Fm (w3_a hc)⟩⟩
end GlobalTheory.Fc.GoodLinked
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linked_bundles_good_of_local_langlands_alt_alt : GlobalTheory.GLq.Green → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) (fun Q L => Row Q L (AtAll fun D _ _ (_ : _root_.GlobalTheory.Fc.BundleCondition _ _ _) => Formalism.BasicNotions.GoodFTAll D)) ∧ _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.RL.RowGoodnessCondition := by
  first | exact @_root_.GlobalTheory.Fc.GoodLinked.row_good_alt_alt | exact _root_.GlobalTheory.Fc.GoodLinked.row_good_alt_alt | (intros; apply _root_.GlobalTheory.Fc.GoodLinked.row_good_alt_alt <;> assumption)
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MultiplicityBoundTransferOfCmDatum
section
set_option synthInstance.maxHeartbeats 200000

section
section
noncomputable section
namespace GlobalTheory.HeightCounting.Up
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top
  GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000
theorem exists_levelB1_carried_of_levelI_same_gal : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, StepW Start fun K B' f' _ w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl B B' → HEq f' f → Start K B f T w → HEq w'.px w.px → HEq w'.I.sel w.I.sel → HEq w'.I.J w.I.J → HEq w'.δ w.δ → ∀ (P : Pre2 K w) (x : St P), _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x → ∀ (P' : Pre2 K w'), Ext P.z P'.z → ∀ x' : St P', _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x' → SameGal (Dof x) (Dof x') → ∃ x'' : St P', Nonempty (_root_.GlobalTheory.HeightCounting.Up.SecondIntermediateLevel hL x'') ∧ Carried (Dof x) (Dof x'') ∧ ∀ cDep : ℝ, ListSt cDep x → ListSt cDep x'' := by
  intro hPr hSer hL
  refine Step.of_evG (((evG_of_ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev).inter (evG_of_ev GlobalTheory.Mem.StdSize.vstd_size_ev)).imp
    fun K _ _ _ _ H B' f' T' hO hKP hF _ w' hS' B f T w hE hf hSt hpx hsel hJ hδ P x lb P' hExt x' l' hG => ?_)
  have hB : ∀ X : Stages, K.Over X.B.toPre → Formalism.IndefR.Links.HostHyp X.toD7 ∧ 8 * X.toD7.R.f * X.toD7.R.r + 4 ≤ X.toD7.R.nV :=
    fun X hX => ⟨(H.1 X hX).1, (H.2 X hX).2⟩
  obtain ⟨N, ι, e, hN⟩ := _root_.GlobalTheory.T.exists_eigenform_copy_of_eigensystem_alt hPr hSer hL hKP hF hS' B f T w hE hf hSt hpx hsel hJ hδ P x lb P' hExt x' l' hG
  obtain ⟨x'', l'', ho, hlev, hrow, hPq, hRS, hSb, hhL, heig, hθ⟩ := _root_.GlobalTheory.T.twisted_state_transport_heq' hL x' l' N
  have hD : Dof x'' = N.toD7 := by
    show (w'.st x''.o.Z).toD7 = N.toD7
    rw [ho]
    rfl
  refine ⟨x'', _root_.GlobalTheory.T.multiplicity_pos_of_restricted_eigenform_copy_alt hPr hSer hL hKP hF hS' hO hB B f T w hE hf hSt hpx hsel hJ hδ P x lb P' hExt x' l' hG N ι e hN x'' l'' ho hlev
    hrow hPq hRS hSb hhL heig hθ, ?_, _root_.GlobalTheory.T.hecke_eigenvalue_list_transfer_upper_alt hPr hSer hL hKP hF hS' B f T w hE hf hSt hpx hsel hJ hδ P x lb P' hExt x' l' hG N ι e
    hN x'' l'' ho hlev hrow hPq hRS hSb hhL heig hθ⟩
  rw [hD]
  exact hN.carried
end GlobalTheory.HeightCounting.Up
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelI_same_gal_transfer_to_levelB1_list : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, StepW Start fun K B' f' _ w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl B B' → HEq f' f → Start K B f T w → HEq w'.px w.px → HEq w'.I.sel w.I.sel → HEq w'.I.J w.I.J → HEq w'.δ w.δ → ∀ (P : Pre2 K w) (x : St P), _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x → ∀ (P' : Pre2 K w'), Ext P.z P'.z → ∀ x' : St P', _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x' → SameGal (Dof x) (Dof x') → ∃ x'' : St P', Nonempty (_root_.GlobalTheory.HeightCounting.Up.SecondIntermediateLevel hL x'') ∧ Carried (Dof x) (Dof x'') ∧ ∀ cDep : ℝ, ListSt cDep x → ListSt cDep x'' := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.exists_levelB1_carried_of_levelI_same_gal | exact _root_.GlobalTheory.HeightCounting.Up.exists_levelB1_carried_of_levelI_same_gal | (intros; apply _root_.GlobalTheory.HeightCounting.Up.exists_levelB1_carried_of_levelI_same_gal <;> assumption)
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NGalAut
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.GalN
theorem galoisRep_definiteUnitary_alt : _root_.GlobalTheory.GalAut.galoisRep_definiteUnitary_tyz := by
  intro H1 H3 _ H6 H7 H8 H9 H10 E Ω _ _ _ _ _ _ hE n hn π hπ lam hlam l _ ι hunr
  obtain ⟨c, a, d, h, P, ρ, m, σ, hP, hloc, hsplit⟩ := _root_.UpperTheory.BaseChangeIdentities.base_change_speh_narrow_swap H1 E hE n hn π hπ
  let J : (Σ i : Fin c, Fin (d i)) → (E →+* Qbar l) → Multiset ℤ := fun x τ =>
    (m x.1 (ι.toRingHom.comp τ)).map (fun z => ⌊(GlobalTheory.GalAut.shiftF n (d x.1) x.2 - z).re⌋)
  have hJ : ∀ x τ, (J x τ).map (fun k : ℤ => (k : ℂ)) =
      (m x.1 (ι.toRingHom.comp τ)).map (fun z => GlobalTheory.GalAut.shiftF n (d x.1) x.2 - z) := by
    intro x τ
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl fun z hz => ?_
    obtain ⟨j, hj⟩ := GlobalTheory.GalAut.int_shift hP (hlam _) x.1 x.2 hz
    exact GlobalTheory.GalAut.cast_floor_re hj
  have hnd : ∀ i τ, (m i τ).Nodup := fun i τ => GlobalTheory.GalAut.nodup_of_parts hP (hlam τ) i
  have hsph : ∀ i (w : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∈ w.asIdeal →
      ∀ σ' : SmIrr (GL (Fin (a i)) (w.adicCompletion E)), (P i).IsLocComp w σ' →
        GlobalTheory.LGrp.IsSpherical σ'.ρ (GlobalTheory.LFun.KGL w (a i)) := fun i w hw σ' h' =>
    GlobalTheory.SphBC.isSpherical_of_isUnramU E hE n π hπ c a d h P ρ m σ hP hloc hsplit w (hunr w hw) i σ' h'
  have hpc := fun x : (Σ i : Fin c, Fin (d i)) => _root_.GlobalTheory.CsdTwistGal.exists_galRep_csd_twist_alt_alt H3 H6 H7 H8 H9 H10 E Ω hE l ι (a x.1) (hP.pos x.1).1 (P x.1)
    (hP.csd x.1) (m x.1) (hP.inf x.1) (hnd x.1) (GlobalTheory.GalAut.shiftF n (d x.1) x.2) (J x) (hJ x)
  choose r hrc hrcrys hrfrob using hpc
  have hsize : ∑ x : (Σ i : Fin c, Fin (d i)), a x.1 = n := by
    rw [Fintype.sum_sigma, ← h]
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  obtain ⟨R, hRc, hRcrys, hRch⟩ := GlobalTheory.BlockSum.main H9 E Ω l (Σ i : Fin c, Fin (d i)) (fun x => a x.1) n hsize r hrc
  have hS : ∀ w, IsSplitAt w → ∀ (σw : SmIrr (GL (Fin n) (w.adicCompletion E))) (T : Multiset ℂˣ),
      IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) σw.ρ → GlobalTheory.LFun.HasSatGL w σw.ρ T →
      ∃ S : Fin c → Multiset ℂˣ, (∀ i, GlobalTheory.LFun.HasSatGL w (ρ i w).ρ (S i)) ∧
        ∑ i, ∑ k : Fin (d i), (S i).map (fun z => (z : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((d i : ℂ) - 1) / 2 - (k : ℕ))) =
          T.map (fun z => (z : ℂ)) := fun w hs σw T hc ht =>
    GlobalTheory.SatInd.satake_locProd_speh E w c n a d h (ρ · w) (σ · w) (fun i => (hP.pos i).2) (fun i => (hloc i w).2.2) T
      (GlobalTheory.SplitSatake.hasSatGL_of_isCompAlong_split E n π hπ w hs _ _ σw.ρ (locProd h w (σ · w)) hc (hsplit w hs) T ht)
  have hq : ∀ w : HeightOneSpectrum (𝓞 E), (Ideal.absNorm w.asIdeal : ℕ) ≠ 0 := fun w h0 =>
    w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  have hprod : ∀ w, IsSplitAt w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ (σw : SmIrr (GL (Fin n) (w.adicCompletion E))) (T : Multiset ℂˣ),
      IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) σw.ρ → GlobalTheory.LFun.HasSatGL w σw.ρ T →
      ∀ (B : ValuationSubring Ω) (g : G E Ω), IsPlaceOver (F := E) B w → IsFrob (F := E) B (normV w) g →
      ∏ x, (r x (g ^ (-1 : ℤ))).val.charpoly = (T.map fun z : ℂˣ =>
          Polynomial.X - Polynomial.C (ι.symm ((z : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((n : ℂ) - 1) / 2)))).prod := by
    intro w hs hl σw T hc ht B g hB hg
    obtain ⟨S, hS1, hS2⟩ := hS w hs σw T hc ht
    rw [GlobalTheory.satake_linear_factors_regroup (Qbar l) ι c d S T _ (hq w) (((n : ℂ) - 1) / 2) hS2, Fintype.prod_sigma]
    exact Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun k _ =>
      hrfrob ⟨i, k⟩ w hs hl (ρ i w) (hP.loc i w) (S i) (hS1 i) B g hB hg
  have hsg : ((-1 : ℤˣ) : ℤ) = -1 := rfl
  refine ⟨⟨R, ?_, ?_⟩, ?_⟩
  · have hj : (fun τ => ∑ x, J x τ) = GlobalTheory.GalDef.jumpsOf ι lam := by
      funext τ
      apply Multiset.map_injective (f := fun k : ℤ => (k : ℂ)) Int.cast_injective
      rw [GlobalTheory.GalAut.map_cast_sum]
      simp only [hJ]
      rw [Fintype.sum_sigma]
      have e1 : ∀ i : Fin c, ∑ k : Fin (d i), (m i (ι.toRingHom.comp τ)).map (fun z => GlobalTheory.GalAut.shiftF n (d i) k - z) =
          (spehInf (d i) (m i (ι.toRingHom.comp τ))).map (fun z => ((n : ℂ) - 1) / 2 - z) := fun i =>
        GlobalTheory.DefiniteBC.spehInf_map_sub_eq_sum_twists (d i) (m i (ι.toRingHom.comp τ)) (((n : ℂ) - 1) / 2)
      rw [Finset.sum_congr rfl fun i _ => e1 i, ← GlobalTheory.GalAut.map_sub_sum, hP.weight _ _ (hlam _)]
      unfold GlobalTheory.GalDef.jumpsOf infOfWeight
      rw [Multiset.map_map, Multiset.map_map]
      refine Multiset.map_congr rfl fun k _ => ?_
      simp only [Function.comp_apply]
      push_cast; ring
    rw [← hj]
    exact hRcrys J fun x => hrcrys x fun w hw => ⟨ρ x.1 w, hP.loc x.1 w, hsph x.1 w hw _ (hP.loc x.1 w)⟩
  · intro w hs hl hU σw T hc ht B g hB hg
    rw [hsg]
    show (R (g ^ (-1 : ℤ))).val.charpoly = _
    rw [hRch]
    exact hprod w hs hl σw T hc ht B g hB hg
  · intro t ht hrun hstr
    obtain ⟨w, hs, hl, hU, σw, T, ν, hc, ht', hν, hle⟩ := hstr
    obtain ⟨S, hS1, hS2⟩ := hS w hs σw T hc ht'
    have htemp : ∀ i, ∀ s ∈ S i, ‖(s : ℂ)‖ < (Ideal.absNorm w.asIdeal : ℝ) ^ (1 / 2 : ℝ) := fun i s hs =>
      (satake_window E (a i) (P i) (hP.csd i) w (ρ i w) (hP.loc i w) (S i) (hS1 i) s hs).2
    have ht1 : 1 ≤ t := by omega
    obtain ⟨i0, hi0⟩ := string_forces_long_part E w c d S T t ν ht1 htemp hν hS2 (by rw [GlobalTheory.GalAut.lift_eq]; exact hle)
    have hne : ∀ i τ, m i τ ≠ 0 := fun i τ h0 => by
      have h1 := (hP.inf i τ).1
      rw [h0, Multiset.card_zero] at h1
      have := (hP.pos i).1
      omega
    have hrunP : ∀ τ' p, GlobalTheory.GalDef.IsRunAt (lam τ') p t → d i0 = t ∧
        m i0 τ' = {(GlobalTheory.GalDef.wAt (lam τ') p : ℂ) + ((n : ℂ) - 1) / 2 - (p : ℕ) - ((t : ℂ) - 1) / 2} ∧
          ∀ j, j ≠ i0 → d j < t :=
      fun τ' p hp => GlobalTheory.GalDef.spehPart_is_run n t (lam τ') p ht hp c d (fun i => m i τ') (fun i => (hP.pos i).2)
        (fun i => hne i τ') (hP.weight τ' _ (hlam τ')) i0 hi0
    obtain ⟨τ0⟩ : Nonempty (E →+* ℂ) := inferInstance
    obtain ⟨p0, hp0⟩ := hrun τ0
    obtain ⟨hd0, hm0, -⟩ := hrunP τ0 p0 hp0
    have ha0 : a i0 = 1 := by
      have h1 := (hP.inf i0 τ0).1
      rw [hm0] at h1
      simpa using h1.symm
    let pp : (E →+* Qbar l) → ℕ := fun τ => (hrun (ι.toRingHom.comp τ)).choose
    have hpp : ∀ τ, GlobalTheory.GalDef.IsRunAt (lam (ι.toRingHom.comp τ)) (pp τ) t := fun τ => (hrun _).choose_spec
    let bot : (E →+* Qbar l) → ℤ := fun τ => (pp τ : ℤ) - GlobalTheory.GalDef.wAt (lam (ι.toRingHom.comp τ)) (pp τ)
    obtain ⟨ρR, hρc, -, hρch⟩ := GlobalTheory.BlockSum.main H9 E Ω l (Σ i : {i : Fin c // i ≠ i0}, Fin (d i)) (fun x => a x.1.1) _ rfl
      (fun x => r ⟨x.1.1, x.2⟩) (fun x => hrc _)
    let kk : Fin t → Σ i : Fin c, Fin (d i) := fun s => ⟨i0, Fin.cast hd0.symm (Fin.rev s)⟩
    refine ⟨_, ρR, fun s => Matrix.GeneralLinearGroup.det.comp (r (kk s)), bot, ?_, hρc, ?_, ?_, ?_⟩
    · rw [← hsize, Fintype.sum_sigma (fun x : Σ i : Fin c, Fin (d i) => a x.1), Fintype.sum_eq_add_sum_subtype_ne _ i0,
        Fintype.sum_sigma (fun x : Σ i : {i : Fin c // i ≠ i0}, Fin (d i) => a x.1.1)]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, hd0, ha0, mul_one]
      ring
    · intro s
      have hJk : ∀ τ, J (kk s) τ = {bot τ + ((s : ℕ) : ℤ)} := by
        intro τ
        show (m i0 (ι.toRingHom.comp τ)).map _ = _
        rw [(hrunP _ _ (hpp τ)).2.1, Multiset.map_singleton, Multiset.singleton_inj]
        have hs1 : (s : ℕ) + 1 ≤ t := s.isLt
        have e : GlobalTheory.GalAut.shiftF n (d i0) (kk s).2 - ((GlobalTheory.GalDef.wAt (lam (ι.toRingHom.comp τ)) (pp τ) : ℂ) +
            ((n : ℂ) - 1) / 2 - (pp τ : ℕ) - ((t : ℂ) - 1) / 2) = ((bot τ + ((s : ℕ) : ℤ) : ℤ) : ℂ) := by
          simp only [GlobalTheory.GalAut.shiftF, kk, bot, Fin.coe_cast, Fin.val_rev, hd0]
          rw [Nat.cast_sub hs1]
          push_cast
          ring
        rw [e]
        simp
      rw [show (fun τ => ({bot τ + ((s : ℕ) : ℤ)} : Multiset ℤ)) = J (kk s) from funext fun τ => (hJk τ).symm]
      exact GlobalTheory.GalAut.crystallineHodgeTate_det_rankOne ha0 (r (kk s)) (J (kk s)) (hrcrys (kk s) fun w hw => ⟨ρ i0 w, hP.loc i0 w, hsph i0 w hw _ (hP.loc i0 w)⟩)
    · intro τ p hp
      have e1 := (hrunP _ _ (hpp τ)).2.1
      have e2 := (hrunP _ _ hp).2.1
      rw [e1, Multiset.singleton_inj] at e2
      have e3 : (((pp τ : ℤ) - GlobalTheory.GalDef.wAt (lam (ι.toRingHom.comp τ)) (pp τ) : ℤ) : ℂ) =
          (((p : ℤ) - GlobalTheory.GalDef.wAt (lam (ι.toRingHom.comp τ)) p : ℤ) : ℂ) := by
        push_cast
        linear_combination -e2
      exact_mod_cast e3
    · intro w' hs' hl' hU' σ' T' hc' ht'' B g hB hg
      rw [hsg]
      show (ρR (g ^ (-1 : ℤ))).val.charpoly * ∏ s, (Polynomial.X - Polynomial.C
        (((Matrix.GeneralLinearGroup.det.comp (r (kk s))) (g ^ (-1 : ℤ)) : (Qbar l)ˣ) : Qbar l)) = _
      have e3 : ∏ x, (r x (g ^ (-1 : ℤ))).val.charpoly =
          (∏ k : Fin (d i0), (r ⟨i0, k⟩ (g ^ (-1 : ℤ))).val.charpoly) *
            ∏ x : (Σ i : {i : Fin c // i ≠ i0}, Fin (d i)), (r ⟨x.1.1, x.2⟩ (g ^ (-1 : ℤ))).val.charpoly := by
        rw [Fintype.prod_sigma, Fintype.prod_eq_mul_prod_subtype_ne _ i0, Fintype.prod_sigma]
      have e4 : ∏ s : Fin t, (Polynomial.X - Polynomial.C
          (((Matrix.GeneralLinearGroup.det.comp (r (kk s))) (g ^ (-1 : ℤ)) : (Qbar l)ˣ) : Qbar l)) =
          ∏ k : Fin (d i0), (r ⟨i0, k⟩ (g ^ (-1 : ℤ))).val.charpoly :=
        Fintype.prod_equiv (Fin.revPerm.trans (finCongr hd0.symm)) _ _ fun s =>
          (GlobalTheory.GalAut.charpoly_eq_of_one ha0 _).symm
      rw [← hprod w' hs' hl' σ' T' hc' ht'' B g hB hg, e3, hρch, e4, mul_comm]
end UpperTheory.GalN
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NonGaloisBlockTypeSplit
section
set_option synthInstance.maxHeartbeats 200000

section
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.BlockTypeSplit
open ValuativeRel Polynomial
section Finite
end Finite
section Local
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {p : ℕ} [Fact p.Prime] {r t : ℕ}
theorem block_type_split_local_alt (hP : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt) (hp : resCard F = p) (L : GlobalTheory.GLq.LabelDatum p) {χ : Fˣ →* ℂˣ}
    (hχ : IsSmoothChar χ) (hχt : IsTame χ) {θ : (ZMod p)ˣ →* ℂˣ} (hθχ : CharLift θ χ) {u : ZMod p}
    (hθ : GlobalTheory.GLp.IsCharLab L θ u) (π : Irr F (r + t)) (ρ : FDRep ℂ (GL (Fin r) (ZMod p))) (hρ : CategoryTheory.Simple ρ)
    {f : (ZMod p)[X]} (hf : GlobalTheory.GLq.HasLabel L (fun x => ρ.character x) f) (hu : ¬ f.IsRoot u) {x : π.V}
    (hx : IsBlockVec χ π.π x) (hxρ : NotKilled π.π (Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ) x) :
    ∃ (π₁ : Irr F r) (π₂ : Irr F t), IsSpherical π₂.π ∧
      Nonempty (π.π.Equiv (prod₂ π₁.π (_root_.GlobalTheory.SmGL.twist π₂.π (detChar (Fin t) χ)))) ∧
      ∃ y, IsLevelOne π₁.π y ∧ NotKilled π₁.π (Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ) y := by
  classical
  have hBZ := hP.bz
  have hG := hP.geo
  have hM := hP.mp
  obtain ⟨v, hv, hb, ℓ, hℓ, hzv⟩ := GlobalTheory.T.exists_fixed_parahoricBlockVector_of_idempotent F p r t χ _ π.π _ x hp (GlobalTheory.SerOSys.zIdem_idem_central ρ hρ).1 hx hxρ
  obtain ⟨Y, _, _, τ, hτ, hsub, y, hy0, hy, hyρ⟩ :=
    GlobalTheory.T.tame_character_parahoric_invariant hM F p r t χ _ π.π _ v ℓ hp π.smooth π.irr hχt hv hb hℓ hzv
  obtain ⟨s, d, σ, hsupp, hle⟩ := GlobalTheory.T.parahoricBlockTypeVector_cuspidalSupport_tame_characters hBZ hG hP.unl hM F r t χ π v hχ hχt hv hb
  rcases hle.lt_or_eq with hlt | heq
  · exfalso
    obtain ⟨-, hσ, e₀, hπσ⟩ := hsupp
    obtain ⟨b, fr, gc, S, hrow, hcol⟩ := exists_cell_of_isSubquotient (hG F).1 (hG F).2 e₀
      (two (stdSum (rfl : r + t = r + t))) (fun a => (σ a).smooth)
      (fun a => hasFiniteLength_of_isIrreducible (σ a).irr) hτ
      (hsub.trans (isSubquotient_jac_two _ (isSmooth_parInd _ _) hπσ))
    set A := {a | d a = 1 ∧ ∃ α : ℂˣ, Nonempty ((σ a).π.Equiv (detRep (Fin (d a)) (χ * unrChar F α)))} with hA
    obtain ⟨i, hi, hi0⟩ : ∃ i ∈ A, b.1 i true = 0 := by
      by_contra! hc
      have h2 := b.2.2 true
      have h3 : A.ncard ≤ ∑ i, b.1 i true := by
        rw [Set.ncard_eq_toFinset_card' A, Finset.card_eq_sum_ones]
        exact (Finset.sum_le_sum fun i hi => Nat.one_le_iff_ne_zero.2 (hc i (Set.mem_toFinset.1 hi))).trans
          (Finset.sum_le_sum_of_subset (Finset.subset_univ _))
      simp only [Fintype.card_fin] at h2
      omega
    obtain ⟨hd, α, hα⟩ := hi
    have hi1 : b.1 i false = 1 := by
      have h1 := b.2.1 i
      simp [Fintype.sum_bool] at h1
      omega
    have hact := GlobalTheory.T.jacquetSubquotient_detCharacter_factors_integral F _ Bool (b.1 i) (fr i) _ (σ i).π _ (S i) hα (hrow i) false
    obtain ⟨w, hw⟩ := typeVec_first (fun j => multiProd (gc j) fun i => (S i j).ρ) (fun j => isSmooth_parInd _ _) hcol hyρ
    obtain ⟨φ, hφ0, hφ⟩ := GlobalTheory.T.exists_equivariantMap_of_levelTypeVector F p (Fin r) _ _ ρ w hp hw
    obtain ⟨v', hv', hpar⟩ := GlobalTheory.T.exists_parabolicTypeVector_of_equivariantMap F p (Fin s) (Fin r) (fun i => Fin (b.1 i false)) (gc false) _
      (fun i => (S i false).ρ) i θ χ _ ρ.ρ φ hp hθχ (fun g hg v => by
        rw [hact g hg v, MonoidHom.mul_apply,
          isUnram_unrChar F α _ (GlobalTheory.StepData.valuation_det_of_mem_KO hg), mul_one]) hφ0 hφ
    exact hu (isRoot_of_parVec L (gc false) i ρ hρ hf hθ (by rw [Fintype.card_fin, hi1]) hv' hpar)
  · obtain ⟨π₁, π₂, ⟨φ⟩, hno⟩ := GlobalTheory.T.irreducible_split_exact_twistCount_product hBZ hG hP.unl F r t χ π s d σ hχ hsupp heq.symm
    have hsph := GlobalTheory.T.spherical_twist_of_blockTypeVector hBZ hG hM F r t χ π π₁ π₂ v hχ hχt hno ⟨φ⟩ hv hb
    refine ⟨π₁, GlobalTheory.SplitPairLift.twistIrr π₂ hχ.inv, hsph, ?_, ?_⟩
    · have h := GlobalTheory.SplitPairLift.twist_twist_inv π₂ χ⁻¹
      rw [inv_inv] at h
      show Nonempty (π.π.Equiv (prod₂ π₁.π (_root_.GlobalTheory.SmGL.twist (_root_.GlobalTheory.SmGL.twist π₂.π (detChar (Fin t) χ⁻¹)) (detChar (Fin t) χ))))
      rw [h]
      exact ⟨φ⟩
    obtain ⟨E⟩ := Exponents.prod₂_equiv_multiProd F r t _ _ π₁.π π₂.π
    let Ψ := φ.trans E
    have hρs : ∀ i, IsSmooth (Exponents.twoRep π₁.π π₂.π i) := fun i => by
      cases i
      · exact π₁.smooth
      · exact π₂.smooth
    have hρl : ∀ i, HasFiniteLength (Exponents.twoRep π₁.π π₂.π i) := fun i => by
      cases i
      · exact hasFiniteLength_of_isIrreducible π₁.irr
      · exact hasFiniteLength_of_isIrreducible π₂.irr
    obtain ⟨b, fr, gc, S, hrow, hcol⟩ := exists_cell_of_isSubquotient (hG F).1 (hG F).2
      (two (stdSum (rfl : r + t = r + t))) (two (stdSum (rfl : r + t = r + t))) hρs hρl hτ
      (hsub.trans (isSubquotient_jac_two _ (isSmooth_parInd _ _)
        (IsSubquotient.of_injective Ψ.toIntertwiningMap Ψ.toLinearEquiv.injective)))
    obtain ⟨z, hz0, hz⟩ := GlobalTheory.T.levi_rep_parabolic_char F Bool (Two (Fin r) (Fin t)) _ (fun j => multiProd (gc j) fun i => (S i j).ρ)
      Y τ true χ y (fun j => isSmooth_parInd _ _) hχ hcol hy0 hy
    obtain ⟨w, hw0, hw⟩ := GlobalTheory.T.exists_levi_block_eigenvector_at_identity F Bool (fun i => Fin (b.1 i true)) (Fin t) (gc true) _
      (fun i => (S i true).ρ) χ z hz0 hz
    have hm : b.1 false true = 0 := by
      by_contra hm
      obtain ⟨z', hz'0, hz'⟩ := GlobalTheory.T.levi_rep_parabolic_char F Bool (fun i => Fin (b.1 i true)) _ (fun i => (S i true).ρ) _
        (piTensor fun i => (S i true).ρ) false χ w (fun i => (S i true).smooth) hχ (IsSubquotient.refl _) hw0 (hw false)
      obtain ⟨α, hα⟩ := GlobalTheory.T.inSupport_mul_unramifiedChar_of_integralEigenvector hBZ hG hM F _ _ (S false true).ρ χ z' (S false true).smooth (S false true).irr hχ
        (Nat.pos_of_ne_zero hm) hz'0 hz'
      exact hno α (GlobalTheory.T.charInCuspidalSupport_of_jacquet_subquotient_factor hBZ hG F r _ π₁.π Bool (b.1 false) (fr false) (S false) true _ π₁.smooth (hrow false) hα)
    have hm' : b.1 true false = 0 := by
      have h1 := b.2.1 false
      have h2 := b.2.2 false
      simp [Fintype.sum_bool] at h1 h2
      omega
    obtain ⟨w₁, hw₁⟩ := typeVec_first (fun j => multiProd (gc j) fun i => (S i j).ρ) (fun j => isSmooth_parInd _ _) hcol hyρ
    obtain ⟨φ₁, h1⟩ := GlobalTheory.T.jacquetSubquotient_firstFactor_of_emptySecondBlock F r (b.1 false) (fr false) _ π₁.π (S false) hm (hrow false)
    obtain ⟨φ₂, h2⟩ := GlobalTheory.T.parabolicInduction_emptySecond_isSubquotient_first F r (fun i => b.1 i false) (gc false) (fun i => S i false) hm'
    obtain ⟨y₁, hy₁⟩ := TypeVec.up π₁.smooth (h2.trans ((GlobalTheory.T.isSubquotientRepresentation_two_reindexings F _ _ φ₂ φ₁ _ (S false false).ρ).trans h1)) hw₁
    exact ⟨y₁, typeVec_iff _ _ _ hy₁⟩
end Local
open Formalism.BasicNotions GlobalTheory.HeightCounting in
theorem locComp_of_isRc_classMapD_cenLoc : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (Γ : GrpSide D),
    GreenLab Γ → _root_.GlobalTheory.PendOf.SplitLocalCondition hL D := by
  intro hP hL D Γ hΓ k v χ hχ u π ρ f ht hlab hser hu ⟨x, hx, hxρ⟩
  have hchi := _root_.UpperTheory.Lit.Dz.localGlobalCompatibility_cmDatum_alt hL D Γ k v χ hχ u ht hlab
  have h0 : idemOf D k ρ ≠ 0 := fun e => by
    obtain ⟨ℓ, -, h⟩ := hxρ
    refine h ?_
    rw [e]
    simp
  obtain ⟨L, h1, h2, hf⟩ := @exists_hasLabel _ ⟨D.host.g_prime k⟩ _ (D.ntypes.teichC_inj k) _ (Γ.ζ_gen k) (Γ.O k) (hΓ k)
    _ ρ hser.1 f h0 (by rw [← Γ.eSer_def]; exact hser.2)
  refine (And.right hchi L h1 h2).elim fun θ hθ => ?_
  exact @_root_.GlobalTheory.BlockTypeSplit.block_type_split_local_alt _ _ _ _ _ _ ⟨D.host.g_prime k⟩ _ _ hP (And.left hchi) L χ hχ ht θ hθ.1 u hθ.2 π ρ hser.1 f hf hu x hx hxρ
end GlobalTheory.BlockTypeSplit
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitLoc_of_greenLab_depth_zero : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (Γ : GrpSide D), GreenLab Γ → _root_.GlobalTheory.PendOf.SplitLocalCondition hL D := by
  first | exact @_root_.GlobalTheory.BlockTypeSplit.locComp_of_isRc_classMapD_cenLoc | exact _root_.GlobalTheory.BlockTypeSplit.locComp_of_isRc_classMapD_cenLoc | (intros; apply _root_.GlobalTheory.BlockTypeSplit.locComp_of_isRc_classMapD_cenLoc <;> assumption)
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NonGaloisDepthZeroTame
section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.DepthZeroTame
end GlobalTheory.DepthZeroTame
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depthZ_of_rowMod_labAll_chiTOk : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → GlobalTheory.Published.DepthZeroSupport → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), (∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i))) → LabAll D P.T → ChiTOk D P.cf → DepthZ D := by
  first | exact @_root_.GlobalTheory.DepthZeroTame.depthZero_tame_alt | exact _root_.GlobalTheory.DepthZeroTame.depthZero_tame_alt | (intros; apply _root_.GlobalTheory.DepthZeroTame.depthZero_tame_alt <;> assumption)
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NonGaloisDepthZeroType
section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped Pointwise
namespace GlobalTheory.DepthZeroType
end GlobalTheory.DepthZeroType
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depthZeroG_of_rowMod : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → GlobalTheory.Published.DepthZeroSupport → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), (∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i))) → GlobalTheory.HubX.DepthZeroG D := by
  first | exact @_root_.GlobalTheory.DepthZeroType.depthZero_tame_alt | exact _root_.GlobalTheory.DepthZeroType.depthZero_tame_alt | (intros; apply _root_.GlobalTheory.DepthZeroType.depthZero_tame_alt <;> assumption)
end
end
end

