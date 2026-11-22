import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0026
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0388
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0606
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0192
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1739
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0019
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0386
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0385
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.Bundle0003
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.Bundle0001
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.Bundle0004
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.Bundle0002
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0650
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0349
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0610
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0515
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitSumTensorDualOfWachMonoidal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HasLevel
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0384
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0269
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0381
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1322
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0382
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.AdTransfer
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0030
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0053
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0311
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HoldsSGoodDROfCsd
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RoadU

theorem holdsS_good_dR_of_csd : Inputs → SphericalLevelCondition .csd .dR → SphericalLevelCondition .good .dR := by
  intro hI hC E Ω _ _ _ _ _ _ l _ ι a ha π χ hs r hr w hw B hB
  have hF := GlobalTheory.automorphicFormsFiniteGL
  have hA := hI.hk
  obtain ⟨κ, m, hκ, hu, hcs⟩ := GlobalTheory.T.exists_good_conjSelfDual_twist_split_unramified hF E l a ha π χ hs w hw
  obtain ⟨art, hart, hμ⟩ := (GlobalTheory.Published.GlobalArtinReciprocity.heckeLAdicCharacter_and_principalIdealSt
    GlobalTheory.globalArtinReciprocity_holds).1 E Ω
  have hκp : GlobalTheory.HeckeGal.IsAlgPos κ m := GlobalTheory.HeckeGal.isAlgPos_of_isAlg hκ
  obtain ⟨μ, ⟨hμc, hL⟩, -⟩ := hμ l ι κ m hκp
  have htc : Continuous (UpperTheory.V.Af.tw r μ) := UpperTheory.galoisRep_irreducibility_criterion.2 _ _ a r μ hr.1 hμc
  have hW : Weak (π.twist κ) ι (UpperTheory.V.Af.tw r μ) :=
    ⟨htc, UpperTheory.V.Af.Cq.attTwist E Ω l ι a r π hr.2 art κ m μ hart hL⟩
  have hB' : (CG.mk (π.twist κ)).HasSat w (B.map (· * κ.val w)) := by
    rw [CG.hasSat_mk] at hB ⊢
    exact GlobalTheory.SphGal.hasSatGL_twist E a π κ w B hu hB
  have hcl : ClauseAt .dR (π.twist κ) ι (UpperTheory.V.Af.tw r μ) w :=
    hC E Ω l ι a ha (π.twist κ) _ hcs (UpperTheory.V.Af.tw r μ) hW w hw _ hB'
  show ClauseAt .dR π ι r w
  intro P AI hT A hAw O _ _ _ Bw hj
  obtain ⟨hdR', hJ'⟩ := hcl P AI hT A hAw O Bw hj
  have hμic : Continuous (μ⁻¹) := hμc.inv
  have hch := GlobalTheory.Published.heckeLAdicCharacterAbove_iff.1 hA E Ω l P AI hT ι art hart κ⁻¹ (-m) μ⁻¹
    (GlobalTheory.GalChar.isAlgPos_inv hκp) hμic hL.inv w A hAw O Bw hj
  have key := GlobalTheory.TwistAbove.twist_above l P AI hT E Ω (Dec (F := E) A) O Bw a
    ((UpperTheory.V.Af.tw r μ).comp (Dec (F := E) A).subtype) (r.comp (Dec (F := E) A).subtype)
    (μ⁻¹.comp (Dec (F := E) A).subtype) (fun g => by
      change ((r g.1 : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)) =
        (((μ g.1)⁻¹ : (Qbar l)ˣ) : Qbar l) • ((UpperTheory.V.Af.tw r μ g.1 : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))
      rw [UpperTheory.V.Af.tw_val, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul])
  refine ⟨key.1 hdR' hch.1, fun τ LL' τ' hτ J hJ => ?_⟩
  set m0 := m (ι.toRingHom.comp τ) with hm0
  have e : expo κ (ι.toRingHom.comp τ) = m0 := (GlobalTheory.CuspRep.InfType.expo_of_infType E κ).1 m hκ _
  have hinf : (CG.mk (π.twist κ)).infChar (ι.toRingHom.comp τ) =
      ((CG.mk π).infChar (ι.toRingHom.comp τ)).map (· + (m0 : ℂ)) := by
    rw [← e]
    exact ((GlobalTheory.CuspRep.ParLaws.hasInfChar_infChar (CG.mk π) _).twist κ).infChar_eq
  have h1 := hJ' τ LL' τ' hτ (J.map (· - m0)) (by
    rw [hinf, Multiset.map_map, Multiset.map_map]
    have e1 : ((CG.mk π).infChar (ι.toRingHom.comp τ)).map ((fun z : ℂ => ((a : ℂ) - 1) / 2 - z) ∘ (· + (m0 : ℂ))) =
        (((CG.mk π).infChar (ι.toRingHom.comp τ)).map (fun z : ℂ => ((a : ℂ) - 1) / 2 - z)).map (· - (m0 : ℂ)) := by
      rw [Multiset.map_map]
      refine Multiset.map_congr rfl fun z _ => ?_
      simp only [Function.comp_apply]
      ring
    rw [e1, ← hJ, Multiset.map_map]
    refine Multiset.map_congr rfl fun n _ => ?_
    simp only [Function.comp_apply]
    push_cast
    ring)
  have h2 := key.2.2.2 τ _ _ h1 (hch.2.2.2 τ LL' τ' hτ)
  have e2 : (J.map (· - m0)).map (· + -((-m) (ι.toRingHom.comp τ))) = J := by
    rw [Multiset.map_map]
    conv_rhs => rw [← Multiset.map_id J]
    refine Multiset.map_congr rfl fun n _ => ?_
    simp only [Function.comp_apply, Pi.neg_apply, neg_neg, id, hm0]
    ring
  rw [e2] at h2
  exact h2

end GlobalTheory.RoadU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPstOfIsSst
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

noncomputable section

namespace GlobalTheory.GalCut.IwaAll

open Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PMon Module

theorem isSst_resQ {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l} {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
    [FiniteDimensional ℚ_[l] LL] {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    (ρ : Representation LL ↥(GK K) V) (h : IsSst P ρ) : IsSst P (GlobalTheory.PstCoeff.resQ ρ) := by
  have hD : Dst P (GlobalTheory.PstCoeff.resQ ρ) = (Dst P ρ).restrictScalars ℚ_[l] := by
    ext x
    simp [mem_Dst, GlobalTheory.PstCoeff.stRep_resQ]
  have e : finrank ℚ_[l] ↥(Dst P (GlobalTheory.PstCoeff.resQ ρ)) = finrank ℚ_[l] LL * finrank LL ↥(Dst P ρ) := by
    rw [hD, finrank_mul_finrank]
    rfl
  rw [IsSst, e, h, ← finrank_mul_finrank ℚ_[l] LL V]
  ring

theorem isPst_of_isSst {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) {K : FinExt l}
    {LL : Type} [Field LL] [Algebra ℚ_[l] LL] [FiniteDimensional ℚ_[l] LL] {V : Type} [AddCommGroup V] [Module LL V]
    [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V] [FiniteDimensional ℚ_[l] V]
    (ρ : Representation LL ↥(GK K) V) (h : IsSst P ρ) : IsPst P ρ := by
  rw [← GlobalTheory.PstCoeff.isPst_resQ_iff]
  apply GlobalTheory.PMon.isPst_of_isSst_resTo l P AI T K K le_rfl V
  have hD : Dst P (resTo (GlobalTheory.PstCoeff.resQ ρ) (le_refl K.1)) = Dst P (GlobalTheory.PstCoeff.resQ ρ) := by
    ext x
    rw [mem_Dst_resTo, mem_Dst]
    exact ⟨fun H g => H g g.2, fun H g _ => H g⟩
  have := isSst_resQ P ρ h
  rw [IsSst] at this ⊢
  rw [hD]
  exact this

theorem isPstAt_of_isSstAt {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (hT : Nonempty (LocTied l P AI))
    {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O]
    [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) {a : ℕ} (r : ↥Gw →* GL (Fin a) (Om l)) :
    IsSstAt P Bw r → IsPstAt P Bw r := by
  rintro ⟨LL', r', hm, hs⟩
  obtain ⟨T⟩ := hT
  haveI := LL'.2
  exact ⟨LL', r', hm, isPst_of_isSst P AI T _ hs⟩

end GlobalTheory.GalCut.IwaAll

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSphericalTwistOfUnr
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

namespace GlobalTheory.CrysTwistBack

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {a : ℕ}

theorem isCrysAt_of_tw {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type}
    [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (c : ↥Gw →* (Om l)ˣ)
    (r : ↥Gw →* GL (Fin a) (Om l)) (h : IsCrysAt P Bw (UpperTheory.V.Af.tw r c))
    (hc : IsCrysAt P Bw (GlobalTheory.TripleGal.rk1 c)) : IsCrysAt P Bw r := by
  obtain ⟨L₁, r₁, m₁, hr₁⟩ := h
  obtain ⟨L₂, c₂, m₂, hc₂⟩ := hc
  have l₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
  have l₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
  have m₁' := m₁.enlarge l₁
  have m₂' := m₂.enlarge l₂
  have hp := (local_ext P Bw l₁ r₁).1.2 hr₁
  have hq := (local_ext P Bw l₂ c₂).1.2 hc₂
  set L := supExt L₁ L₂ with hL
  set r₁' := Formalism.MainNotions.N.mapRep (IntermediateField.inclusion l₁).toRingHom r₁ with hr₁'
  set c₂' := Formalism.MainNotions.N.mapRep (IntermediateField.inclusion l₂).toRingHom c₂ with hc₂'
  let d : ↥Gw →* (↥L.1)ˣ := Matrix.GeneralLinearGroup.det.comp c₂'
  have hd : ∀ g, ((c₂' g : GL (Fin 1) ↥L.1) : Matrix (Fin 1) (Fin 1) ↥L.1) 0 0 = (d g : ↥L.1) := fun g => by
    change _ = Matrix.det _
    rw [Matrix.det_fin_one]
  have hcd : ∀ g, ((d g : ↥L.1) : Om l) = (c g : Om l) := fun g => by
    have e := congrArg (fun f : ↥Gw →* GL (Fin 1) (Om l) => ((f g : GL (Fin 1) (Om l)) : Matrix (Fin 1) (Fin 1) (Om l)) 0 0) m₂'.2
    rw [← hd]
    refine e.trans ?_
    simp [GlobalTheory.TripleGal.rk1]
  have hM : IsModel Bw r L (UpperTheory.V.Af.tw r₁' d⁻¹) := by
    refine ⟨m₁'.1, ?_⟩
    ext g i j
    have e : algebraMap ↥L.1 (Om l) (((r₁' g : GL (Fin a) ↥L.1) : Matrix (Fin a) (Fin a) ↥L.1) i j) =
        ((UpperTheory.V.Af.tw r c g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j :=
      congrArg (fun f : ↥Gw →* GL (Fin a) (Om l) => ((f g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j) m₁'.2
    change algebraMap ↥L.1 (Om l) (((UpperTheory.V.Af.tw r₁' d⁻¹ g : GL (Fin a) ↥L.1) : Matrix (Fin a) (Fin a) ↥L.1) i j) =
      ((r g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j
    rw [UpperTheory.V.Af.tw_val, Matrix.smul_apply, smul_eq_mul, map_mul, e, UpperTheory.V.Af.tw_val, Matrix.smul_apply, smul_eq_mul,
      MonoidHom.inv_apply, Units.val_inv_eq_inv_val, map_inv₀,
      show algebraMap ↥L.1 (Om l) (d g : ↥L.1) = (c g : Om l) from hcd g, ← mul_assoc, inv_mul_cancel₀ (Units.ne_zero _), one_mul]
  refine ⟨L, _, hM, ?_⟩
  let θ : ↥(GK Bw.Kw) →* (↥L.1)ˣ := d.comp Bw.e.symm.toMonoidHom
  refine (GlobalTheory.TopSteps.CrysRules.isCrys_iff T Bw.Kw L (Bw.repE L (UpperTheory.V.Af.tw r₁' d⁻¹)) (Bw.repE L r₁') θ
    (fun g x => ?_) ?_).2 hp
  · rw [GlobalTheory.ConjLocal.repE_apply, GlobalTheory.ConjLocal.repE_apply, UpperTheory.V.Af.tw_val, Matrix.smul_mulVec, smul_smul]
    change _ = ((d (Bw.e.symm g) : ↥L.1) * ((d⁻¹ (Bw.e.symm g) : (↥L.1)ˣ) : ↥L.1)) • _
    rw [MonoidHom.inv_apply, Units.mul_inv, one_smul]
  · refine GlobalTheory.Cmp.WachMonoidal.isCrys_of_equiv (P.PD Bw.Kw) (LinearEquiv.funUnique (Fin 1) ↥L.1 ↥L.1) (fun g x => ?_) hq
    change (Bw.repE L c₂' g x) 0 = ((θ g : (↥L.1)ˣ) : ↥L.1) * x 0
    rw [GlobalTheory.ConjLocal.repE_apply]
    simp only [Matrix.mulVec, dotProduct, Finset.univ_unique, Finset.sum_singleton]
    exact congrArg (· * x 0) (hd (Bw.e.symm g))

end GlobalTheory.CrysTwistBack

namespace GlobalTheory.CrysTwistBack

theorem isSpherical_twist_of_unr {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) (κ : HChar E) (hκ : κ.UnrAt w)
    (h : GlobalTheory.SmGL.IsSpherical σ.ρ) :
    GlobalTheory.SmGL.IsSpherical (σ.twist (CuspSub.locDet a κ w) (CuspSub.isOpen_ker_locDet κ w)).ρ := by
  have hK : GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin a) = GlobalTheory.LFun.KGL w a :=
    GlobalTheory.SmGL.SphCompletion.KO_completion w a
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 h
  refine (Submodule.ne_bot_iff _).2 ⟨v, fun g => ?_, hv0⟩
  have hg : g.1 ∈ GlobalTheory.LFun.KGL w a := hK ▸ g.2
  have h1 : CuspSub.locDet a κ w g.1 = 1 := hκ _ (GlobalTheory.SphGal.isUnitAt_det_of_mem hg)
  have h3 := hv g
  show ((CuspSub.locDet a κ w g.1 : ℂˣ) : ℂ) • σ.ρ g.1 v = _
  rw [h1, Units.val_one, one_smul]
  exact h3

theorem holds_good_crys : AutomorphicFormsFiniteGL → HeckeLAdicCharacterAbove → Holds .csd .crys → Holds .good .crys := by
  intro hF hA hC E Ω _ _ _ _ _ _ l _ ι a ha π χ hs r hr w hw
  intro P AI hT A hAw O _ _ _ Bw hj σ hσ hsph
  obtain ⟨κ, m, hκ, hκu, hcs⟩ := GlobalTheory.T.exists_good_conjSelfDual_twist_split_unramified hF E l a ha π χ hs w hw
  obtain ⟨art, hart, hch⟩ := (GlobalArtinReciprocity.heckeLAdicCharacter_and_principalIdealSt
    GlobalTheory.globalArtinReciprocity_holds).1 E Ω
  obtain ⟨μ, ⟨hμc, hμ⟩, -⟩ := hch l ι κ m (fun k _ => hκ k)
  have hw' : Weak (π.twist κ) ι (UpperTheory.V.Af.tw r μ) :=
    ⟨UpperTheory.galoisRep_irreducibility_criterion.2 _ _ a _ μ hr.1 hμc, UpperTheory.V.Af.Cq.attTwist E Ω l ι a r π hr.2 art κ m μ hart hμ⟩
  have h1 := hC E Ω l ι a ha (π.twist κ) (quadChar E ^ a) hcs (UpperTheory.V.Af.tw r μ) hw' w hw P AI hT A hAw O Bw hj _
    (hσ.twist κ) (isSpherical_twist_of_unr a w σ κ hκu hsph)
  have h2 := (hA E Ω l P AI hT ι art hart κ m μ (fun k _ => hκ k) hμc hμ w A hAw O Bw hj).2.2.1 hκu
  obtain ⟨T⟩ := hT
  exact isCrysAt_of_tw T Bw (μ.comp (Dec (F := E) A).subtype) (r.comp (Dec (F := E) A).subtype) h1 h2

end GlobalTheory.CrysTwistBack

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSplitAtOfDegOne
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

noncomputable section
namespace GlobalTheory.CongEx

open UpperTheory.V.Af

theorem exists_place_over (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] :
    ∃ w : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w.asIdeal := by
  have hp : (Ideal.span {(l : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Int.prime_iff_natAbs_prime.2 (by simpa using (Fact.out : l.Prime))).irreducible
  have hker : RingHom.ker (algebraMap ℤ (𝓞 E)) ≤ Ideal.span {(l : ℤ)} := by
    intro x hx
    rw [RingHom.mem_ker] at hx
    have : x = 0 := by exact_mod_cast (algebraMap ℤ (𝓞 E)).injective_int (hx.trans (map_zero _).symm)
    rw [this]; exact zero_mem _
  obtain ⟨Q, hQ, hQc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 E) _ hker
  have hl : ((l : ℕ) : 𝓞 E) ∈ Q := by
    have : (l : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 E)) := by rw [hQc]; exact Ideal.mem_span_singleton_self _
    simpa using this
  refine ⟨⟨Q, hQ.isPrime, fun h => ?_⟩, hl⟩
  rw [h] at hQc
  have h0 : (l : ℤ) ∈ Ideal.span {(l : ℤ)} := Ideal.mem_span_singleton_self _
  rw [← hQc, Ideal.comap_bot_of_injective _ (algebraMap ℤ (𝓞 E)).injective_int] at h0
  have := (Fact.out : l.Prime).ne_zero
  simp_all

theorem eventually_not_mem_l (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] :
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ((l : ℕ) : 𝓞 E) ∉ w.asIdeal := by
  have h0 : Ideal.span {((l : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  exact (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (not_not.1 hv)

end GlobalTheory.CongEx

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteFrameValuesStepZero
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

namespace GlobalTheory.TwV.StepZero

theorem del_zero : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S =>
    J.Dict std → S.Pair → S.Pos → S.Law → S.Del 0) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hP hPos hL
  exact GlobalTheory.T.kernelSite_frameValues_all_steps_lt_m S hD hP hPos hL 0 (by have := GlobalTheory.TwU.m_eq t μ; omega)

end GlobalTheory.TwV.StepZero
end

