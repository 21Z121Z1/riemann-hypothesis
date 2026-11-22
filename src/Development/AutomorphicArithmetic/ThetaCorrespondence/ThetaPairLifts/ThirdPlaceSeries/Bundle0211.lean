import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0767
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0012
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0191
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0198
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0201
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0200
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle1005
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0141
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0138
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0748
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0769
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0849
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0027
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0128
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0132
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0123
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0078
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0149
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.SeparableConjugates.SepConjG
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.SwOn
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CGTrueT
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.Bundle0001
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.Bundle0003
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.AbsCentralAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0830
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0017
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0030
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0170
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0172
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0797
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0133
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0018
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0156
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0197
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0735
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0762
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0001
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0019

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RecSatakeRecT
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
namespace GlobalTheory.FormDict.RecTLaws
section Core
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {rc : IrrGL (w.adicCompletion E) → WD h}
theorem hasSatGL_rec_alt (H : _root_.UpperTheory.Zero.LLC.IsRecT h rc) {n : ℕ} (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (S : Multiset ℂˣ)
    (hS : GlobalTheory.LFun.HasSatGL w σ.ρ S) :
    (rc (cls (ParLaws.toRep σ))).unr ∧
      (rc (cls (ParLaws.toRep σ))).frobEig = S.map fun z => ((z⁻¹ : ℂˣ) : ℂ) := by
  have hsph : IsSpherical (ParLaws.toRep σ).ρ := by
    have := hS.1
    unfold IsSpherical IsSphericalFor
    rw [GlobalTheory.SmGL.SphCompletion.KO_completion w n]
    exact this
  have hu : (rc (cls (ParLaws.toRep σ))).unr := (_root_.GlobalTheory.CuspRep.ParLaws.reciprocity_unramified_iff_spherical H _).2 hsph
  obtain ⟨α, hα⟩ := _root_.UpperTheory.One.M.exists_hasSatake_of_unr_alt H hu
  have e : S = Finset.univ.val.map α := hS.unique (GlobalTheory.T.hasSatakeGL_of_hasSatakeParameters_principalSeries E w n _ σ.ρ α hα)
  refine ⟨hu, ?_⟩
  rw [_root_.GlobalTheory.CuspRep.ParLaws.reciprocity_eq_diagonal_inv_of_has_satake H hα, WD.frobEig_diag, e, Multiset.map_map]
  rfl
end Core
section Record
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}
  (T : GlobalTheory.RowTie.WDTie N A) (hL : _root_.UpperTheory.Zero.LLC.RecTExists)
theorem equiv_transported_reciprocity_eq_local_reciprocity (w : PlE H) {n : ℕ} (σ : LocIrr w n) :
    T.e w (_root_.GlobalTheory.FormDict.recT_alt T hL w n σ) = _root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (N.plOm.2 w) (cls (ParLaws.toRep σ)) :=
  (T.e w).apply_symm_apply _
theorem transported_reciprocity_prod : RecProd (_root_.GlobalTheory.FormDict.recT_alt T hL) := by
  intro w c n d hd σ σ' e
  apply (T.e w).injective
  rw [_root_.GlobalTheory.FormDict.RecTLaws.equiv_transported_reciprocity_eq_local_reciprocity, e_lpSumList, _root_.UpperTheory.One.M.locProd_eqG_alt (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (N.plOm.2 w)) hd σ σ' e, List.map_ofFn]
  congr 2
  funext i
  exact (_root_.GlobalTheory.FormDict.RecTLaws.equiv_transported_reciprocity_eq_local_reciprocity T hL w (σ i)).symm
theorem transported_reciprocity_satake : RecSatake (_root_.GlobalTheory.FormDict.recT_alt T hL) := by
  intro w n σ S hS
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.FormDict.RecTLaws.hasSatGL_rec_alt (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (N.plOm.2 w)) σ S hS
  have hu : A.unr (_root_.GlobalTheory.FormDict.recT_alt T hL w n σ) := (T.unr w _).2 (by rw [_root_.GlobalTheory.FormDict.RecTLaws.equiv_transported_reciprocity_eq_local_reciprocity]; exact h1)
  exact ⟨hu, (T.frobEig w _ hu).trans (by rw [_root_.GlobalTheory.FormDict.RecTLaws.equiv_transported_reciprocity_eq_local_reciprocity]; exact h2)⟩
theorem transported_reciprocity_speh_of_generic_unitary_dual (hTZ : GlobalTheory.Published.GenericUnitaryDualGL) (hSC : GlobalTheory.Published.StandardCosocleGL) :
    RecSpeh (_root_.GlobalTheory.FormDict.recT_alt T hL) := by
  intro w a d n hd P σ σ' hP hu hq
  have hg : IsGeneric σ.ρ := GlobalTheory.CuspRep.Generic.isGeneric_of_isLocComp H.E a P w σ hP
  apply (T.e w).injective
  rw [_root_.GlobalTheory.FormDict.RecTLaws.equiv_transported_reciprocity_eq_local_reciprocity, e_lpSumList, _root_.GlobalTheory.T.local_langlands_speh_product' _ _ _ w _ _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (N.plOm.2 w)) hTZ hSC a d n hd σ σ'
    hu hg hq, List.map_map]
  congr 1
  refine List.map_congr_left fun k _ => ?_
  simp only [Function.comp_apply, T.tw, _root_.GlobalTheory.FormDict.RecTLaws.equiv_transported_reciprocity_eq_local_reciprocity]
end Record
theorem transported_reciprocity_prod_and_speh_and_satake : GlobalTheory.Published.GenericUnitaryDualGL → GlobalTheory.Published.StandardCosocleGL →
    ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)
      (A : NAut N) (T : GlobalTheory.RowTie.WDTie N A), RecProd (_root_.GlobalTheory.FormDict.recT_alt T hL) ∧ RecSpeh (_root_.GlobalTheory.FormDict.recT_alt T hL) ∧ RecSatake (_root_.GlobalTheory.FormDict.recT_alt T hL) :=
  fun hTZ hSC hL _ _ _ _ _ T => ⟨_root_.GlobalTheory.FormDict.RecTLaws.transported_reciprocity_prod T hL, _root_.GlobalTheory.FormDict.RecTLaws.transported_reciprocity_speh_of_generic_unitary_dual T hL hTZ hSC, _root_.GlobalTheory.FormDict.RecTLaws.transported_reciprocity_satake T hL⟩
end GlobalTheory.FormDict.RecTLaws
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReferenceLiftInjective
section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.LiftRef.UpInjRows
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.RecTie Formalism.IndefR.Lev
theorem locComp_of_isRc_classMapD_cenLoc : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.LiftRef.ForallRowSideParameters hL fun D _ _ _ _ _ => ∀ (j : ℕ) (_ : 1 ≤ j) (_ : j ≤ D.R.m) (σ : D.what₂.FT), ∀ y ∈ D.what₂.isot j σ, D.what₂.thetaT D.what₂.mu0 j y = 0 → y = 0 := by
  intro _ _
  unfold _root_.GlobalTheory.LiftRef.ForallRowSideParameters OverRows
  refine GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun K B f T _ w _ Z Wt hX z p0 Y hH _ _ _ _ Rw a M tup Q _ _ j h1 h2 σ y hy h0 => ?_
  obtain ⟨i, rfl⟩ : ∃ i : Fin (w.st Z).toD7.R.m, j = (i : ℕ) + 1 := ⟨⟨j - 1, by omega⟩, by simp only; omega⟩
  exact thetaT_inj_real _ _ _ _ _ _ _ z.R z.F z.cG p0 Y z.pins hH i σ y hy h0
end GlobalTheory.LiftRef.UpInjRows
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaT_mu0_injective_on_isot : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.LiftRef.ForallRowSideParameters hL fun D _ _ _ _ _ => ∀ (j : ℕ) (_ : 1 ≤ j) (_ : j ≤ D.R.m) (σ : D.what₂.FT), ∀ y ∈ D.what₂.isot j σ, D.what₂.thetaT D.what₂.mu0 j y = 0 → y = 0 := by
  first | exact @_root_.GlobalTheory.LiftRef.UpInjRows.locComp_of_isRc_classMapD_cenLoc | exact _root_.GlobalTheory.LiftRef.UpInjRows.locComp_of_isRc_classMapD_cenLoc | (intros; apply _root_.GlobalTheory.LiftRef.UpInjRows.locComp_of_isRc_classMapD_cenLoc <;> assumption)
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RigidRawPacketEqPow
section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.HeightCounting.Rigid
theorem rigid_raw_packet_eq_pow_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ (D₁ D₂ : D7) (p : TwPack D₁) (A : Finset (PlE D₁.host)) (ι : GlobalTheory.Mem.Top.TwChar.RootIso D₁ p.1 p.2.2.1) (χ : HChar D₁.host.E) (cf : CharFrame D₂) (C : NChoice D₂) (tp : TupTied D₂ cf C) (v : D₂.what₂.places.Pl), SameExport D₁ D₂ → BlochKatoReduction.Gen.PsiOk p.1 A p.2.1 p.2.2.1 p.2.2.2 → GlobalTheory.Mem.Top.TwChar.FrobPick p.1 p.2.1 p.2.2.1 p.2.2.2 ι χ → PsiChoiceCompatible D₂ cf C tp → TwistedAt D₂ v → HEq (C.twI v) p.1 → HEq (C.Q v) p.2.1 → C.k' v = p.2.2.1 → HEq (tp.psi v) χ → (∀ z : ℂ, z ^ D₂.what₂.places.resChar v ^ C.k' v = 1 → ∃ x : D₂.what₂.LL, D₂.what₂.embLL x = z) → ∃ a : ℤ, Nat.Coprime a.natAbs (D₁.ntw.l p.1) ∧ HEq (rawPack C v) (GlobalTheory.HeightCounting.twPackPow D₁ a p) := by
  intro hc D₁ D₂ p A ι χ cf C tp v h hO hF hT htw hi hQ hk hχ hL
  obtain ⟨ψ₂, ι₂, A₂, hO₂, hF₂, hl, hpow⟩ := transfer h p A ι χ hO hF (C.twI v) (C.Q v) (C.k' v) (tp.psi v) hi hQ hk hχ
  obtain ⟨a, ha, hψ⟩ := pow_of_tied hc.cheb cf C tp v ψ₂ ι₂ hF₂ hT htw hO₂.2.2.1 hL
  refine ⟨a, by rw [Int.natAbs_natCast, ← hl]; exact ha, ?_⟩
  have e : rawPack C v = (⟨C.twI v, C.Q v, C.k' v, ψ₂ ^ (a : ℤ)⟩ : TwPack D₂) := by
    rw [zpow_natCast, ← hψ]
    rfl
  rw [e]
  exact hpow a
end GlobalTheory.HeightCounting.Rigid
end
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowDepthOfPrimitive
section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.RowDepthTrue
open GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up in
set_option maxHeartbeats 2000000 in
theorem rowDepth_allSt_alt_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → AllSt fun _ _ _ _ _ _ x => RowDepth (Dof x) (repOf x.r.Y) := by
  intro hPr
  have hId : StepW Start Start := StepW.of_all fun _ _ _ _ _ _ _ h => h
  refine (hId.and (GlobalTheory.RowDepthTrue.stepW_of_ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev Start)).trans
    (StepW.of_all fun K B f T w hO _ H => ?_)
  intro P x
  obtain ⟨hHo, hF, -⟩ := H.2 (w.st x.o.Z) hO
  exact rowDepth_rowRepR hPr.hc hPr.decay _ _ _ _ _ _ _ _ _ _ _ _ x.m.z.pins x.m.intersectionNumber_baseChange hHo hF
end GlobalTheory.RowDepthTrue
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depth_of_repOf_of_inputs : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → AllSt fun _ _ _ _ _ _ x => RowDepth (Dof x) (repOf x.r.Y) := by
  first | exact @_root_.GlobalTheory.RowDepthTrue.rowDepth_allSt_alt_alt | exact _root_.GlobalTheory.RowDepthTrue.rowDepth_allSt_alt_alt | (intros; apply _root_.GlobalTheory.RowDepthTrue.rowDepth_allSt_alt_alt <;> assumption)
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowGeo0AtStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linkedAt_geometricWeakTies_of_tie : GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.R1.SlotDivisorCondition → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.RL.Row_tie_alt → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.S0.GeometricWeakCompatibility' := by
  first | exact @_root_.GlobalTheory.Fc.GeoZeroAt.geometricWeakTies_of_linked_ties | exact _root_.GlobalTheory.Fc.GeoZeroAt.geometricWeakTies_of_linked_ties | (intros; apply _root_.GlobalTheory.Fc.GeoZeroAt.geometricWeakTies_of_linked_ties <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SepConjG
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Formalism.MainNotions.N Formalism.L2.Host Module
open GlobalTheory GlobalTheory.WeilDeligne GlobalTheory.CuspRep GlobalTheory.LocLanglands GlobalTheory.HeightCounting GlobalTheory.SmGL GlobalTheory.SatakeFlip GlobalTheory.LocGL
open GlobalTheory.Mem.Chr hiding HChar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.GalS
theorem sep_conj_g_alt (sw : _root_.UpperTheory.One.M.TrivialCondition) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) {D : D7}
    {T : GlobalTheory.RowTie.WDTie D.nd D.naut} (C : _root_.GlobalTheory.HeightCounting.CGTrueT hL D T) {a : ℕ} (π : D.naut.CG a) (hc : D.naut.csd π) {w w' : PlE D.host}
    (hw : IsConjPl D.host w w') (k : Sep D.nd D.naut (D.naut.locG π w)) : Sep D.nd D.naut (D.naut.locG π w') := by
  have := host_isCMField D.host
  obtain ⟨π₀, hπ₀⟩ := Quotient.exists_rep (C.e _ π).1
  have hmk : CG.mk π₀ = (C.e _ π).1 := hπ₀
  have hc₀ : π₀.IsCsd := by
    have h1 := (C.csd _ π).1 hc
    rw [CGu.IsCsd, ← hmk] at h1
    exact h1
  have hpar : ∀ v, T.e v (D.naut.locG π v) = _root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.mk π₀) (D.nd.plOm.2 v) := fun v => by
    rw [C.loc, hmk]
    rfl
  rw [sep_iff T, hpar] at k ⊢
  obtain ⟨γ, hγ⟩ := GlobalTheory.exists_tameGenAt_of_isPlaceOver _ _ _ _ (D.nd.plOm.2 w')
  obtain ⟨γ', ⟨c, hcE, hcA, -⟩, -⟩ := GlobalTheory.conjGen_transport_exists D w' w γ (GlobalTheory.TwistDet.isConjPl_symm hw) hγ
  have hcp : ConjPl (IsCMField.complexConj D.host.E).toRingEquiv w w' :=
    (conjPl_iff_mem _ _ _).2 fun x y e => hw x y (e.trans (host_complexConj D.host _))
  obtain rfl : w' = conjSrc (IsCMField.complexConj D.host.E).toRingEquiv w := eq_conjSrc fun x => by
    simpa using (hcp (IsCMField.complexConj D.host.E x)).symm
  obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp hF _ a π₀ w
  have good : ∀ (v : PlE D.host) (τ : SmIrr (GL (Fin a) (v.adicCompletion D.host.E))), π₀.IsLocComp v τ →
      UpperTheory.Zero.LLC.Good (cls (ParLaws.toRep τ)) := fun v τ hτ => by
    have g := _root_.UpperTheory.One.M.New.cgGood sw C _ π v
    have h1 : (CG.mk π₀).IsLoc v (Quotient.mk _ τ) := hτ
    rw [← hmk, CG.IsLoc.unique _ a _ v _ _ h1.loc h1] at g
    exact g
  rw [_root_.GlobalTheory.CuspRep.ParLaws.local_parameter_eq_reciprocity_of_is_local_component hL hσ] at k
  rw [_root_.GlobalTheory.CuspRep.ParLaws.local_parameter_eq_reciprocity_of_is_local_component hL (ParLaws.isLocComp_flip hc₀ hσ)]
  let π₁ : IrrRep (GL (Fin a) (w.adicCompletion D.host.E)) :=
    ⟨σ.V, σ.ρ.comp (GlobalTheory.TypeTame.invTranspose a), fun v => (σ.smooth v).preimage (GlobalTheory.TypeTame.continuous_invTranspose a),
      GlobalTheory.GelfandKazhdan.isIrreducible_comp _ (fun g => ⟨_, GlobalTheory.TypeTame.invTranspose_invTranspose a g⟩) σ.irred⟩
  have hE := GlobalTheory.GelfandKazhdan.equiv_contra _ a σ.V σ.ρ
    (PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top _ a σ.V σ.ρ σ.smooth σ.irred) σ.irred
  have hr := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 w)
  let cc := (IsCMField.complexConj D.host.E).toRingEquiv
  let i := RingEquiv.ofBijective (conjLoc cc w) ⟨(conjLoc cc w).injective, ParLaws.conjLoc_surjective cc w⟩
  let L := longElt a (w.adicCompletion D.host.E)
  obtain ⟨b', b, h1, h2, -, h4⟩ := _root_.UpperTheory.One.M.New.field hL (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 (conjSrc cc w))) hr c
    (D.host.conj : D.host.E →+* D.host.E) i (fun z => (hcA z).symm) hcE (conjLoc_spec cc w).1
    (fun x => ((conjLoc_spec cc w).2.1 x).trans (congrArg _ (host_complexConj D.host x))) a
    (ParLaws.toRep ⟨σ.V, σ.ρ.comp (ParLaws.flip (conjLoc cc w) a),
        isSmooth_comp σ.smooth _ (ParLaws.continuous_flip (conjLoc_spec _ w).1),
        ParLaws.isIrreducible_comp σ.irred _ (ParLaws.flip_surjective (ParLaws.conjLoc_surjective _ w))⟩) π₁
    (LinearMap.GeneralLinearGroup.toLinearEquiv (σ.ρ.asGroupHom L)) (fun g v => by
      change σ.ρ L (σ.ρ (invRevT (Matrix.GeneralLinearGroup.map (conjLoc cc w) g)) v) =
        σ.ρ (invT a _ (Matrix.GeneralLinearGroup.map (conjLoc cc w) g)) (σ.ρ L v)
      have e : ∀ (x y : GL (Fin a) (w.adicCompletion D.host.E)) (u : σ.V), σ.ρ x (σ.ρ y u) = σ.ρ (x * y) u :=
        fun x y u => by rw [map_mul]; rfl
      refine (e _ _ v).trans (Eq.trans ?_ (e _ _ v).symm)
      rw [ParLaws.invRevT_eq, inv_mul_cancel_right]) (good _ _ (ParLaws.isLocComp_flip hc₀ hσ))
  first | (have hOpn := UpperTheory.One.M.opn _ (hr); obtain ⟨_, _, _, H⟩ := hOpn) | obtain ⟨_, _, _, -, H⟩ := hr
  have kd := k.dual
  rw [← _root_.UpperTheory.One.M.LawsM.dual H a (ParLaws.toRep σ) π₁ (good _ _ hσ) hE, ← h2] at kd
  exact h1 ▸ kd.transport c (D.host.conj : D.host.E ≃+* D.host.E) hcE hcA h4
end UpperTheory.GalS
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SeriesRestageOfCarry
section
set_option synthInstance.maxHeartbeats 200000

section
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
namespace GlobalTheory.HeightCounting.SerCarry
open GlobalTheory.HeightCounting.SerMove GlobalTheory.Mem.R3.Tr
theorem series_restage_of_carry_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {K : Ctx} {B' : Base} {f' : Top.Fr B'.toPre} {T' : TwDat B'} {w' : ColW B' f' T'}, KPx B' f' → Forced K B' T' → Start K B' f' T' w' → K.Over B'.toPre → (∀ X : Stages, K.Over X.B.toPre → Formalism.IndefR.Links.HostHyp X.toD7 ∧ 8 * X.toD7.R.f * X.toD7.R.r + 4 ≤ X.toD7.R.nV) → ∀ (B : Base) (f : Top.Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl B B' → HEq f' f → Start K B f T w → HEq w'.px w.px → HEq w'.I.sel w.I.sel → HEq w'.I.J w.I.J → HEq w'.δ w.δ → ∀ (P : Pre2 K w) (x : St P) (lb : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (P' : Pre2 K w'), Ext P.z P'.z → ∀ (x' : St P') (l' : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x'), SameGal (Dof x) (Dof x') → ∀ (N : TwNew (Dof x')) (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0), CopyN (Dof x) N ι e → ∀ (x'' : St P') (l'' : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x''), x''.o = oTw x' N → HEq x''.m.z.R.toRealDat.toLevCh (GlobalTheory.Mem.R3.Tr.levCh (a := x'.o.Z) (oTw x' N).Z x'.m.z.R.toRealDat.toLevCh) → HEq l''.a.A.row (N.row l'.a.A.row) → HEq l''.Pq l'.Pq → HEq l''.rat.S (N.rat l'.rat.S) → HEq l''.rat.In.Sb l'.rat.In.Sb → HEq l''.rat.In.hL l'.rat.In.hL → HEq l''.rat.In.eig l'.rat.In.eig → HEq l''.rat.In.θ l'.rat.In.θ → ∀ (cHk : ∀ (i : (Dof x'').ntw.Tw) (_b : Bool) (_P : PlE (Dof x'').host), ((Dof x'').ntw.O i)ˣ), (∀ (i : (Dof x).ntw.Tw) (i' : (Dof x'').ntw.Tw) (b : Bool) (P : PlE (Dof x).host) (P' : PlE (Dof x'').host), HEq i i' → HEq P P' → HEq (cHk i' b P') (lb.b.Bs.cHk i b P)) → ∃ (YS : NExpRealS x''.m.z.R x''.m.z.cG l''.rat.S) (X : NExpTied (Dof x'')), (∀ i j b k Q ψ (h1 : 1 ≤ j) (h2 : j ≤ (Dof x'').R.m) (hadm : NX.AdmTw (Dof x'') i k Q ψ), (X.mtV i j b k Q ψ h1 h2 hadm).QP = qpOf (Dof x'') l''.Pq Q ∧ (X.mtV i j b k Q ψ h1 h2 hadm).DP = qpOf (Dof x'') l''.Pq ((Dof x'').ntw.pD i)) ∧ (∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ (Dof x'').R.m) (k : ℕ) (P : PlE (Dof x'').host) (y : (Dof x'').nexp.Fm i j b), P ∉ (Dof x'').ntw.S0 i → IsSplitPl (Dof x'').host P → k ≤ (Dof x'').R.r → YS.eF i j b h1 h2 ((Dof x'').nexp.hkF i j b k P y) = algebraMap ((Dof x'').ntw.O i) (FractionRing ((Dof x'').ntw.O i)) (cHk i b P) ^ k • hkF (Dof x'') l''.rat.S i j b (l''.rat.In.hL j) (l''.rat.In.hs j h1 h2) k P (YS.eF i j b h1 h2 y)) ∧ (∀ i x, HEq ((YS.fi i).e x) x) ∧ Nonempty (SerAt YS x''.m.z.geo.v₀ X l''.mt.ad.PV (cfOf x'') l''.Pq) ∧ TauTrue X := by
  intro hPr hSer hL K B' f' T' w' hKP hF hS' hO hB B f T w hE hf hSt hpx hsel hJ hδ P x lb P' hExt x' l' hG N ι e hN x'' l'' ho _ _ _ _ _ _ _ _ cHk hc
  obtain ⟨ι', e', h, hcf, hPq, g, g'', hg, hg'', a, a'', ⟨m⟩⟩ := _root_.GlobalTheory.HeightCounting.SerGlue.exists_move_alt hKP hF hS' hO hB hE hf hSt hpx hsel hJ hδ
    x lb.toLI.toLA hExt x' hG N hN x'' l''.toLA ho
  obtain ⟨H, hp⟩ := _root_.GlobalTheory.HeightCounting.SerCarry.st_facts_alt lb.toLI g hg a
  obtain ⟨H', hp'⟩ := _root_.GlobalTheory.HeightCounting.SerCarry.st_facts_alt l'' g'' hg'' a''
  obtain ⟨L, hl, hq⟩ := sideB_facts lb.b.Bs lb.b.eF
  exact (by with_unfolding_all exact ((series_move h m ((x.m.z.geo)) ((x''.m.z.geo)) (kKs := (lb.rat.kKs)) (hk := (lb.rat.hk)) ((l''.rat.kKs))
    ((l''.rat.hk)) ((lb.b.YS)) ((lb.b.fi)) hl lb.rat.rat.Sb_le l''.rat.rat.Sb_le H H' (hs := (lb.b.Bs.hs)) (c := lb.b.Bs.cHk)
    ((l''.rat.In.hs)) (c' := cHk) hc ((L)) hcf lb.a.A.chr l''.a.A.chr hp hp' hPq hq lb.b.tau ((lb.b.ser))) : _))
end GlobalTheory.HeightCounting.SerCarry
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_of_series_carry_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {K : Ctx} {B' : Base} {f' : Top.Fr B'.toPre} {T' : TwDat B'} {w' : ColW B' f' T'}, KPx B' f' → Forced K B' T' → Start K B' f' T' w' → K.Over B'.toPre → (∀ X : Stages, K.Over X.B.toPre → Formalism.IndefR.Links.HostHyp X.toD7 ∧ 8 * X.toD7.R.f * X.toD7.R.r + 4 ≤ X.toD7.R.nV) → ∀ (B : Base) (f : Top.Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl B B' → HEq f' f → Start K B f T w → HEq w'.px w.px → HEq w'.I.sel w.I.sel → HEq w'.I.J w.I.J → HEq w'.δ w.δ → ∀ (P : Pre2 K w) (x : St P) (lb : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (P' : Pre2 K w'), Ext P.z P'.z → ∀ (x' : St P') (l' : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x'), SameGal (Dof x) (Dof x') → ∀ (N : TwNew (Dof x')) (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0), CopyN (Dof x) N ι e → ∀ (x'' : St P') (l'' : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x''), x''.o = oTw x' N → HEq x''.m.z.R.toRealDat.toLevCh (GlobalTheory.Mem.R3.Tr.levCh (a := x'.o.Z) (oTw x' N).Z x'.m.z.R.toRealDat.toLevCh) → HEq l''.a.A.row (N.row l'.a.A.row) → HEq l''.Pq l'.Pq → HEq l''.rat.S (N.rat l'.rat.S) → HEq l''.rat.In.Sb l'.rat.In.Sb → HEq l''.rat.In.hL l'.rat.In.hL → HEq l''.rat.In.eig l'.rat.In.eig → HEq l''.rat.In.θ l'.rat.In.θ → ∀ (cHk : ∀ (i : (Dof x'').ntw.Tw) (_b : Bool) (_P : PlE (Dof x'').host), ((Dof x'').ntw.O i)ˣ), (∀ (i : (Dof x).ntw.Tw) (i' : (Dof x'').ntw.Tw) (b : Bool) (P : PlE (Dof x).host) (P' : PlE (Dof x'').host), HEq i i' → HEq P P' → HEq (cHk i' b P') (lb.b.Bs.cHk i b P)) → ∃ (YS : NExpRealS x''.m.z.R x''.m.z.cG l''.rat.S) (X : NExpTied (Dof x'')), (∀ i j b k Q ψ (h1 : 1 ≤ j) (h2 : j ≤ (Dof x'').R.m) (hadm : NX.AdmTw (Dof x'') i k Q ψ), (X.mtV i j b k Q ψ h1 h2 hadm).QP = qpOf (Dof x'') l''.Pq Q ∧ (X.mtV i j b k Q ψ h1 h2 hadm).DP = qpOf (Dof x'') l''.Pq ((Dof x'').ntw.pD i)) ∧ (∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ (Dof x'').R.m) (k : ℕ) (P : PlE (Dof x'').host) (y : (Dof x'').nexp.Fm i j b), P ∉ (Dof x'').ntw.S0 i → IsSplitPl (Dof x'').host P → k ≤ (Dof x'').R.r → YS.eF i j b h1 h2 ((Dof x'').nexp.hkF i j b k P y) = algebraMap ((Dof x'').ntw.O i) (FractionRing ((Dof x'').ntw.O i)) (cHk i b P) ^ k • hkF (Dof x'') l''.rat.S i j b (l''.rat.In.hL j) (l''.rat.In.hs j h1 h2) k P (YS.eF i j b h1 h2 y)) ∧ (∀ i x, HEq ((YS.fi i).e x) x) ∧ Nonempty (SerAt YS x''.m.z.geo.v₀ X l''.mt.ad.PV (cfOf x'') l''.Pq) ∧ TauTrue X := by
  first | exact @_root_.GlobalTheory.HeightCounting.SerCarry.series_restage_of_carry_alt | exact _root_.GlobalTheory.HeightCounting.SerCarry.series_restage_of_carry_alt | (intros; apply _root_.GlobalTheory.HeightCounting.SerCarry.series_restage_of_carry_alt <;> assumption)
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SpecializationAtMemberOfLayer
section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.PinLayer
set_option maxHeartbeats 4000000 in
theorem specialization_at_member_of_layer_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists,
    _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => ∃ P : _root_.GlobalTheory.NPin.CharacterChoiceData hL (w.D Z), _root_.GlobalTheory.HeightCounting.Up.PinnedAtCharacterChoice c.a P := by
  intro hP hL
  refine GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun K B f T _ w Z Wt p0 t nch n xd c hE _ _ => ?_
  obtain ⟨e⟩ := hE
  have e' : _root_.GlobalTheory.HeightCounting.RealExpansionExtraData (D := (w.st Z).toD7) c.row t.r.z.geo xd := e
  have hT : TypesTrue (w.D Z).ntypes (TC.cf w.I w.l Z).P (TC.cf w.I w.l Z).W := by
    show TypesTrue _ w.I.C.P w.I.C.W
    rw [w.C_eq]
    exact t.grp
  have hEl : Elem (w.D Z) := by
    refine ⟨fun y => ?_, fun j g => ((w.D Z).hc ((w.D Z).eTau.symm g)).e_int j, fun v hv => ?_⟩
    · exact (IntermediateField.normal_iff_forall_map_le.1 B.coeffGaloisSubfield_isGalois.to_normal
        (starRingEnd (w.D Z).what₂.LL).toRatAlgHom) ⟨_, y.2, rfl⟩
    · have hc : ∀ p ∈ (w.D Z).host.levelPrimes, p.Prime ∧ p % ((w.D Z).host.QS * (w.D Z).host.q * (w.D Z).host.d) = 1 :=
        (w.st Z).B.level_cond
      rcases hv with hv | hv
      · exact GlobalTheory.HeightCounting.Up.isSplitPl_of_mem_levelPrimes _ hc (w.D Z).host.pde_level.1 v hv
      · exact GlobalTheory.HeightCounting.Up.isSplitPl_of_mem_levelPrimes _ hc (w.D Z).host.pde_level.2 v hv
  exact _root_.GlobalTheory.PinLayer.pinAt_of_side_alt c.a hP.greenC hT (GlobalTheory.HeightCounting.Up.valLL0_colW w Z)
    (fun σ => Formalism.IndefR.principalLevelFrame.rowRepR t.r.z.R.θ (t.r.Y.eFT σ)) c.row.rep_eq
    (fun σ σ' h => t.r.Y.eFT.injective (Formalism.IndefR.principalLevelFrame.rowRepR_inj _ _ _ h)) hEl
    (GlobalTheory.ChebSplitDense.chebSplit_nd hP.what₂.cheb _) e'.labc e'.zeta
end GlobalTheory.PinLayer
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_character_choice_pin_at_of_third_layer : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => ∃ P : _root_.GlobalTheory.NPin.CharacterChoiceData hL (w.D Z), _root_.GlobalTheory.HeightCounting.Up.PinnedAtCharacterChoice c.a P := by
  first | exact @_root_.GlobalTheory.PinLayer.specialization_at_member_of_layer_alt | exact _root_.GlobalTheory.PinLayer.specialization_at_member_of_layer_alt | (intros; apply _root_.GlobalTheory.PinLayer.specialization_at_member_of_layer_alt <;> assumption)
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SphericalLocalComponentAwayFromLevel
section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000
section SphOffSec
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
open Formalism.IndefR.principalLevelFrame Formalism.IndefR.Mult
namespace GlobalTheory.RowSphOff
end GlobalTheory.RowSphOff
end SphOffSec
namespace GlobalTheory.RowSphOff
theorem spherical_localComponent_away_from_level_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → OverRows fun _ _ _ _ w Z _ _ z _ Y => ∀ (σ : (w.st Z).toD7.what₂.FT) (s : ReciprocityTheory.Aut.SplitPlace (w.st Z).toD7.host.E), (∀ k : Fin 2, s.w ∉ placesOver (w.st Z).toD7.host.E ((w.st Z).toD7.host.g k)) → ∃ τ, IsLocS (repOf Y σ).S s τ ∧ GlobalTheory.SmGL.IsSpherical τ.ρ := by
  intro hPr
  refine evG_all fun K => lg_all K fun B f T _ => ?_
  intro hKP w hpin Z Wt hX z p0 Y hH hEx hGeo hGrp hGA σ s hoff
  obtain ⟨h, hh⟩ := levS_of_kO_conj _ _ _ _ _ _ _ z.R z.F z.cG p0 Y z.pins s hoff
  obtain ⟨φ, hφS, hφ0, hφfix⟩ := exists_fixed_of_level _ _ _ _ _ _ _ z.R z.F p0 Y σ
    {κ | ReciprocityTheory.Aut.TrivOutside {s.v} κ ∧ h⁻¹ * s.loc _ κ * h ∈ GlobalTheory.SplitWeil.KO (s.v.adicCompletion (maximalRealSubfield (w.st Z).toD7.host.E)) (Fin (w.st Z).toD7.R.r)}
    (fun b κ hκ => hh b κ hκ.1 hκ.2)
  obtain ⟨τ, hτ⟩ := exists_isLocS_rows hPr.hc hPr.decay _ _ _ _ _ _ _ z.R z.F z.cG p0 Y z.pins σ s
  refine ⟨τ, hτ, ?_⟩
  obtain ⟨x, hx, e⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq _ s h
  have hmul : ∀ (a b : Formalism.AUTREP.GAf (w.st Z).toD7.host.E (w.st Z).toD7.R.r) (g : Formalism.AUTREP.GAf (w.st Z).toD7.host.E (w.st Z).toD7.R.r → ℂ),
      NG.rt _ _ (a * b) g = NG.rt _ _ a (NG.rt _ _ b g) := by
    intro a b g
    funext c
    simp [NG.rt, mul_assoc]
  have hone : ∀ g : Formalism.AUTREP.GAf (w.st Z).toD7.host.E (w.st Z).toD7.R.r → ℂ, NG.rt _ _ 1 g = g := by
    intro g
    funext c
    simp [NG.rt]
  have hT : ∀ a b : Formalism.AUTREP.GAf (w.st Z).toD7.host.E (w.st Z).toD7.R.r, ReciprocityTheory.Aut.TrivOutside {s.v} a →
      ReciprocityTheory.Aut.TrivOutside {s.v} b → ReciprocityTheory.Aut.TrivOutside {s.v} (a * b) :=
    fun a b ha hb v hv => by
      simp only [Subgroup.coe_mul, Units.val_mul, Matrix.map_mul, ha v hv, hb v hv, mul_one]
  refine fixed_kO_ne_bot _ _ (repOf Y σ) s τ hτ (NG.rt _ _ x⁻¹ φ) ((repOf Y σ).stable _ φ hφS) ?_ ?_
  · intro h0
    apply hφ0
    rw [← hone φ, ← mul_inv_cancel x, hmul, h0, map_zero]
  · intro κ hκ hk
    have h1 := hφfix (x * κ * x⁻¹) ⟨hT _ _ (hT _ _ hx hκ) (GlobalTheory.RowLevelSplit.trivOutside_inv hx), by
      rw [map_mul, map_mul, map_inv, e, show h⁻¹ * (h * s.loc _ κ * h⁻¹) * h = s.loc _ κ by group]
      exact hk⟩
    rw [← hmul, show κ * x⁻¹ = x⁻¹ * (x * κ * x⁻¹) by group, hmul, h1]
end GlobalTheory.RowSphOff
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_spherical_loc_comp_at_split_place_off_g : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → OverRows fun _ _ _ _ w Z _ _ z _ Y => ∀ (σ : (w.st Z).toD7.what₂.FT) (s : ReciprocityTheory.Aut.SplitPlace (w.st Z).toD7.host.E), (∀ k : Fin 2, s.w ∉ placesOver (w.st Z).toD7.host.E ((w.st Z).toD7.host.g k)) → ∃ τ, IsLocS (repOf Y σ).S s τ ∧ GlobalTheory.SmGL.IsSpherical τ.ρ := by
  first | exact @_root_.GlobalTheory.RowSphOff.spherical_localComponent_away_from_level_alt | exact _root_.GlobalTheory.RowSphOff.spherical_localComponent_away_from_level_alt | (intros; apply _root_.GlobalTheory.RowSphOff.spherical_localComponent_away_from_level_alt <;> assumption)
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SplitsAtAllStages
section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
namespace GlobalTheory.HeightCounting.Up
theorem splits_at_all_stages_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → AllSt fun _ _ _ _ _ _ x => ∀ v : HeightOneSpectrum (𝓞 (Dof x).host.E), v ∈ placesOver (Dof x).host.E (Dof x).host.pde ∨ v ∈ placesOver (Dof x).host.E (Dof x).host.pde' → IsSplitPl (Dof x).host v := by
  intro _
  refine StepW.of_all fun K B f T w _ _ _ P x v hv => ?_
  have hc : ∀ p ∈ (Dof x).host.levelPrimes, p.Prime ∧ p % ((Dof x).host.QS * (Dof x).host.q * (Dof x).host.d) = 1 :=
    (w.st x.o.Z).B.level_cond
  rcases hv with hv | hv
  · exact isSplitPl_of_mem_levelPrimes _ hc (Dof x).host.pde_level.1 v hv
  · exact isSplitPl_of_mem_levelPrimes _ hc (Dof x).host.pde_level.2 v hv
end GlobalTheory.HeightCounting.Up
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.is_split_pl_of_places_over_pde : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → AllSt fun _ _ _ _ _ _ x => ∀ v : HeightOneSpectrum (𝓞 (Dof x).host.E), v ∈ placesOver (Dof x).host.E (Dof x).host.pde ∨ v ∈ placesOver (Dof x).host.E (Dof x).host.pde' → IsSplitPl (Dof x).host v := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.splits_at_all_stages_alt | exact _root_.GlobalTheory.HeightCounting.Up.splits_at_all_stages_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.splits_at_all_stages_alt <;> assumption)
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThirdComponentFitsIntegralLattice
section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 4000000
namespace GlobalTheory.HeightCounting.Up.ThirdFits
theorem third_component_fits_integral_lattice_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → _root_.GlobalTheory.NRows.GeometricGaloisRepCompatibility → AllSt fun _ _ _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) (big : (Dof x).what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 (Dof x))), _root_.GlobalTheory.CoefDuty.BuiltAlt l.a.A l.mt.M l.c.ch l.c.tp.tup big L → SumRepresentations.hypO (withLoc L) → (GlobalTheory.HeightCounting.Fin3.oL x L).Fits :=
  fun _ _ _ => GlobalTheory.Mem.Top.Bl.StepW.of_all fun _ _ _ _ _ _ _ _ _ x _ _ L _ _ => GlobalTheory.HeightCounting.Fin3.fitsL (x := x) L
end GlobalTheory.HeightCounting.Up.ThirdFits
end
end
end

