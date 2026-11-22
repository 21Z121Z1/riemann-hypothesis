import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsAdelicChain
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0331
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0078
import Formalism.LocalToGlobal.Divisibility.QLocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0390
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0389
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0228
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0219
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1317
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0017
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceCharacterEqReferenceIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0393
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfCongSet
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0392
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
import Formalism.LocalRingCardinality.DataLatDefs
import Formalism.LocalRingCardinality.Lemmas
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IndexAtLevelIffOuterClausesAnd
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0314
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0394
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0009
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FamilyClassSevenDutiesAndStableLattices
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLiftFlagGroupInv
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped InnerProductSpace

namespace GlobalTheory.ProjectorAdjoint

open Formalism.IndefR.Lev

section Act

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {β : GL (Fin V.rank) (Lev.EAf D)}
  {L : LevDat D.host.E ℂ V.rank} {G : Type} [Group G] [Fintype G] {μ : Measure (GA D V)} {𝓕 : Set (GA D V)}

theorem isLiftFlagGroup_inv {g : G0 L.Pg L.r} {κ : GA D V} (h : IsLevelLift V β L g κ) : IsLevelLift V β L g⁻¹ κ⁻¹ := by
  refine ⟨(GfC V).inv_mem h.1, ?_, ?_⟩
  · rw [map_inv]; exact Subgroup.inv_mem _ h.2.1
  · rw [map_inv, rTup_inv h.2.1, h.2.2]

theorem levChi_inv {g : G0 L.Pg L.r} {κ : GA D V} (h : IsLevelLift V β L g κ) :
    (levChi V β (flagL L) κ⁻¹)⁻¹ = star (levChi V β (flagL L) κ)⁻¹ := by
  have h1 : κ ∈ levG V β (flagL L) := ⟨h.1, h.2.1, Subgroup.mem_top _⟩
  have hn := GlobalTheory.norm_levChi_flagL_eq_one V β L κ h1
  have h2 : levChi V β (flagL L) κ⁻¹ * levChi V β (flagL L) κ = 1 := by
    have a := levFn_flag_mul (V := V) (β := β) (L := L) (isLiftFlagGroup_inv h).2.1 h.2.1
    have b := levFn_flag_mul (V := V) (β := β) (L := L) (Subgroup.one_mem _) (Subgroup.one_mem _)
    rw [mul_one, left_eq_mul] at b
    rw [← map_mul, inv_mul_cancel, map_one, b] at a
    unfold levChi
    rw [← Units.val_mul, ← a, Units.val_one]
  rw [inv_eq_of_mul_eq_one_right h2, Complex.inv_def, Complex.normSq_eq_norm_sq, hn]
  simp

theorem integral_act (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) (g : G0 L.Pg L.r) {φ ψ : GA D V → ℂ}
    (hφ : ∀ γ ∈ GQ V, ∀ x, φ (γ * x) = φ x) (hψ : ∀ γ ∈ GQ V, ∀ x, ψ (γ * x) = ψ x) (ht : HasType V β (flag1L L) ψ) :
    ∫ x in 𝓕, star (actG0 V β L g φ x) * ψ x ∂μ = ∫ x in 𝓕, star (φ x) * actG0 V β L g⁻¹ ψ x ∂μ := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA D.sp.cm.sig V.gram
  have : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig V.gram
  have : SecondCountableTopology (GA D V) := (GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V).2.1
  have := GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D V μ hμ
  by_cases hk : ∃ κ, IsLevelLift V β L g κ
  · have hκ := hk.choose_spec
    have h1 := level_action_spec ht ⟨_, isLiftFlagGroup_inv hκ⟩ _ (isLiftFlagGroup_inv hκ)
    have h2 := (GlobalTheory.fundamentalDomain_integral_mul_right μ (GQ V) 𝓕 (fun x => star (φ x) * actG0 V β L g⁻¹ ψ x) hk.choose h𝓕
      fun γ hγ x => by rw [h1, h1, mul_assoc γ, hφ γ hγ, hψ γ hγ]).2
    rw [← h2]
    refine integral_congr_ae (.of_forall fun x => ?_)
    show star (actG0 V β L g φ x) * ψ x = star (φ (x * hk.choose)) * actG0 V β L g⁻¹ ψ (x * hk.choose)
    rw [h1, levChi_inv hκ, mul_inv_cancel_right, actG0, dif_pos hk, star_mul']
    ring
  · have hk' : ¬ ∃ κ, IsLevelLift V β L g⁻¹ κ := fun ⟨κ, h⟩ => hk ⟨κ⁻¹, by simpa using isLiftFlagGroup_inv h⟩
    simp [actG0, dif_neg hk, dif_neg hk']

theorem ipM_gaL (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ) (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ)
    (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ) (hc : ∀ g, c g⁻¹ = star (c g)) {X Y : MMap M}
    (hX : X ∈ Mult θ M (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L)))
    (hY : Y ∈ Mult θ M (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L))) :
    ipM M μ 𝓕 (postOn M (gaL V β L eG c) X) Y = ipM M μ 𝓕 X (postOn M (gaL V β L eG c) Y) := by
  have hs := GlobalTheory.MultFinite.schurMult (θ := θ) (M := M) (J := (levG V β (flag1L L) : Set (GA D V))) (χ := levChi V β (flag1L L))
    hP μ 𝓕 hθ hμ h𝓕
  have ha : ∀ g, ∀ Z ∈ Mult θ M (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L)),
      postOn M (actL V β L g) Z ∈ Mult θ M (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L)) :=
    fun g Z hZ => GlobalTheory.FlagAction.finiteGroupAction_preserves_principalFlagMultiplicity θ M hθ β L g Z hZ _ fun _ => rfl
  obtain ⟨v, hv⟩ := GlobalTheory.SchurConst.exists_vec M (GlobalTheory.GardingVec.sm_ne_bot D _ _ M)
  have h1 := (ipM_spec M μ 𝓕 _ _ (hs _ (GlobalTheory.ProjectedLift.postOn_gaL_mem hθ eG c hX) _ hY) v v).2
  have h2 := (ipM_spec M μ 𝓕 _ _ (hs _ hX _ (GlobalTheory.ProjectedLift.postOn_gaL_mem hθ eG c hY)) v v).2
  refine mul_right_cancel₀ hv (h1.symm.trans (Eq.trans ?_ h2))
  have e1 : ∀ x, star (postOn M (gaL V β L eG c) X v x) * Y v x =
      ∑ g, c g⁻¹ * (star (actG0 V β L (eG g) (X v) x) * Y v x) := fun x => by
    simp only [gaL, postOn_apply, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, star_sum,
      star_mul', Finset.sum_mul, hc, mul_assoc]
    rfl
  have e2 : ∀ x, star (X v x) * postOn M (gaL V β L eG c) Y v x =
      ∑ g, c g⁻¹ * (star (X v x) * actG0 V β L (eG g)⁻¹ (Y v) x) := fun x => by
    simp only [gaL, postOn_apply, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.inv G) _ _ fun g => ?_
    rw [Equiv.inv_apply, inv_inv, map_inv, inv_inv, mul_left_comm]
    rfl
  have hX' := (GlobalTheory.MultMem.mem_mult_iff D θ V S M _ _ X).1 hX
  have hY' := (GlobalTheory.MultMem.mem_mult_iff D θ V S M _ _ Y).1 hY
  simp only [e1, e2]
  rw [integral_finsetSum, integral_finsetSum]
  · refine Finset.sum_congr rfl fun g _ => ?_
    rw [integral_const_mul, integral_const_mul, integral_act hμ h𝓕 _ (hX'.aut v).left (hY'.aut v).left
      (GlobalTheory.hasType_of_mem_mult θ M β _ Y hY v)]
  · exact fun g _ => ((hs _ hX _ (ha (eG g)⁻¹ _ hY)).choose_spec v v).1.const_mul _
  · exact fun g _ => ((hs _ (ha (eG g) _ hX) _ hY).choose_spec v v).1.const_mul _

end Act

theorem eC_inv {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (hr : R.grp_record) (g : G) :
    RealDat.eC (A := A) D.what₂.embLL g⁻¹ = star (RealDat.eC (A := A) D.what₂.embLL g) := by
  obtain ⟨eR, _, _, h, _⟩ := hr
  have : Finite (G0g D.nd) := Finite.of_equiv G eR.toEquiv
  obtain ⟨h1, h2⟩ := GlobalTheory.GoodLatCompare.goodSeriesIdempotent_central_idempotent D
  unfold RealDat.eC
  rw [h, h, map_inv]
  exact GlobalTheory.RowLev.GroupAlgPos.isSA_central _ h2 (fun a => (Subalgebra.mem_center_iff.1 h1 a).symm) _

theorem ipM_e0 : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ F : Face D A, R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∀ U ∈ Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (Formalism.IndefR.Lev.levChi _ (R.βY 0) (R.dat0 R.triv)), ∀ U' ∈ R.EEat R.triv, ipM (R.MY 0) R.ν0 R.fd0 (postOn (R.MY 0) R.e0 U) U' = ipM (R.MY 0) R.ν0 R.fd0 U U' := by
  intro hP D G _ _ Pl0 T A Ks _ _ _ R F _ hG hM U hU U' hU'
  have h : postOn (R.MY 0) R.e0 U' = U' := sub_eq_zero.1 (LinearMap.mem_ker.1 hU'.2)
  exact (ipM_gaL (L := R.dat0 R.triv) hP hM.inf hM.ν0.1.1 hM.ν0.2 R.eG _ (eC_inv R hG.record) hU hU'.1).trans
    (congrArg (ipM (R.MY 0) R.ν0 R.fd0 U) h)

end GlobalTheory.ProjectorAdjoint

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenIsCompactParahoricGLCompletion
section
open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

namespace GlobalTheory.ParahoricTopo

theorem isClopen_OP {L : Type} [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) :
    IsClopen ((OP P : Subring (P.adicCompletion L)) : Set (P.adicCompletion L)) :=
  Valued.isClopen_valuationSubring (P.adicCompletion L)

theorem isClopen_mulSet {L : Type} [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L))
    (ϖ : P.adicCompletion L) (hϖ : ϖ ≠ 0) :
    IsClopen {y : P.adicCompletion L | ∃ o ∈ OP P, y = ϖ * o} := by
  have e : {y : P.adicCompletion L | ∃ o ∈ OP P, y = ϖ * o} =
      (fun y => ϖ⁻¹ * y) ⁻¹' ((OP P : Subring (P.adicCompletion L)) : Set (P.adicCompletion L)) := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe]
    constructor
    · rintro ⟨o, ho, rfl⟩
      rwa [← mul_assoc, inv_mul_cancel₀ hϖ, one_mul]
    · intro h
      exact ⟨_, h, by rw [← mul_assoc, mul_inv_cancel₀ hϖ, one_mul]⟩
  rw [e]
  exact (isClopen_OP P).preimage (continuous_const.mul continuous_id)

theorem isOpen_isCompact_parJ : ∀ (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) (r c : ℕ), IsOpen (parJ (OP P) (piP P : P.adicCompletion L) r c) ∧ IsCompact (parJ (OP P) (piP P : P.adicCompletion L) r c) := by
  intro L _ _ P r c
  letI := GlobalTheory.LocalData.complRel P
  haveI := GlobalTheory.LocalData.isLocalField P
  haveI : (Valued.v : Valuation (P.adicCompletion L) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := ValuativeRel.isEquiv (ValuativeRel.valuation (P.adicCompletion L))
    (Valued.v : Valuation (P.adicCompletion L) (WithZero (Multiplicative ℤ)))
  have hK : GlobalTheory.SplitWeil.KO (P.adicCompletion L) (Fin (r + c)) = GLint (OP P) (r + c) := by
    ext g
    rw [GlobalTheory.SplitFlip.mem_KO_iff]
    simp only [he.le_one_iff_le_one, Valuation.mem_integer_iff]
    exact Iff.rfl
  have hS := isClopen_mulSet P (piP P : P.adicCompletion L) (Units.ne_zero _)
  set B : Set (GL (Fin (r + c)) (P.adicCompletion L)) :=
    {k | bDA (k : Matrix (Fin (r + c)) (Fin (r + c)) (P.adicCompletion L)) ∈
      IIset (t := c) (a := r) (OP P) (piP P : P.adicCompletion L)} with hB
  have hBe : B = ⋂ i : Fin c, ⋂ j : Fin r,
      (fun k : GL (Fin (r + c)) (P.adicCompletion L) =>
        (k : Matrix (Fin (r + c)) (Fin (r + c)) (P.adicCompletion L)) (Fin.natAdd r i) (Fin.castAdd c j)) ⁻¹'
        {y : P.adicCompletion L | ∃ o ∈ OP P, y = (piP P : P.adicCompletion L) * o} := by
    ext k
    simp only [hB, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, IIset, bDA, Matrix.submatrix_apply]
  have hcont : ∀ (i : Fin (r + c)) (j : Fin (r + c)), Continuous fun k : GL (Fin (r + c)) (P.adicCompletion L) =>
      (k : Matrix (Fin (r + c)) (Fin (r + c)) (P.adicCompletion L)) i j := fun i j =>
    (Units.continuous_val (M := Matrix (Fin (r + c)) (Fin (r + c)) (P.adicCompletion L))).matrix_elem i j
  have hBc : IsClopen B := by
    rw [hBe]
    exact isClopen_iInter_of_finite fun i => isClopen_iInter_of_finite fun j => hS.preimage (hcont _ _)
  have hP : parJ (OP P) (piP P : P.adicCompletion L) r c =
      (GlobalTheory.SplitWeil.KO (P.adicCompletion L) (Fin (r + c)) : Set _) ∩ B := by
    rw [hK]; rfl
  rw [hP]
  exact ⟨GlobalTheory.SplitFlip.isOpen_KO.inter hBc.isOpen, GlobalTheory.SplitFlip.isCompact_KO.inter_right hBc.isClosed⟩

end GlobalTheory.ParahoricTopo
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KerEqThetaKO
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped InnerProductSpace

namespace GlobalTheory.Mem.OrientedKer

variable {D : D7}

theorem toTWsmall_zero (S T : HSp D) : toTWsmall S T 0 = 0 := by
  unfold toTWsmall
  rw [Matrix.zero_mul, Matrix.transpose_zero]

theorem ker_eq_thetaKO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (Wf : WeilFun D ψ) (S T : HSp D) (χS χT : IdC D), S.rank < T.rank → admitted T S χT χS → ∀ om, IsWeilDatumO ψ S T χS χT om → ∀ f, IsThetaFunO ψ S T f → ∃ Φ : ThS ψ T S, (f ≠ 0 → Φ ≠ 0) ∧ ∀ g h, Wf.ker T S χT χS Φ h g = thetaKO om g h f := by
  intro D ψ hψ Wf S T χS χT hr ha om H f hf
  have ha' : admitted S T χS χT := ⟨ha.1.symm, ha.2.2.1, ha.2.1, ha.2.2.2.2, ha.2.2.2.1⟩
  obtain ⟨omO, H', e⟩ := GlobalTheory.Mem.WeilOriented.exists_isWeilDatumO D ψ hψ S T χS χT _ ha' hr (Wf.core.weil S T χS χT ha')
  obtain ⟨E, -, -, hE, -, -, -, h7, -⟩ := GlobalTheory.OrientedCoord.exists_coord D S T hr.le

  have hf0 : IsThetaFun ψ S T fun y => f (E.symm y) := by
    refine (h7 ψ _).1 ?_
    simp only [AddEquiv.symm_apply_apply]
    exact hf
  let Φ₀ : ThS ψ S T := ⟨fun y => f (E.symm y), mem_ThS.2 hf0⟩
  have hfΦ : f = fun x => Φ₀.1 (toTWsmall S T x) := by
    funext x
    simp only [Φ₀, ← hE, AddEquiv.symm_apply_apply]

  have hΦt : IsThetaFun ψ T S fun x => Φ₀.1 x.transpose :=
    (GlobalTheory.Mem.ThetaClosed.thetaFun_closed D ψ hψ S T Φ₀.1).2.2 hr.ne (mem_ThS.1 Φ₀.2)
  let Φ : ThS ψ T S := ⟨fun x => Φ₀.1 x.transpose, mem_ThS.2 hΦt⟩
  refine ⟨Φ, fun h0 hΦ => h0 ?_, fun g h => ?_⟩
  · funext x
    have := congrFun (congrArg Subtype.val hΦ) (E x).transpose
    simp only [Φ, Φ₀, Matrix.transpose_transpose, AddEquiv.symm_apply_apply, Submodule.coe_zero, Pi.zero_apply] at this
    exact this
  · have hs := Wf.om_swap S T χS χT ha' g h Φ₀ Φ (fun x => congrArg Φ₀.1 (Matrix.transpose_transpose x)) 0
    rw [Matrix.transpose_zero] at hs
    have e1 := congrFun (e (g, h) Φ₀) 0
    rw [toTWsmall_zero, ← hfΦ] at e1
    have e2 := GlobalTheory.WeilUniq.weilDatum_unique D ψ hψ S T χS χT omO om H' H (g, h) f hf
    unfold WeilFun.ker thetaKO
    rw [hs, ← e2]
    exact e1.symm

end GlobalTheory.Mem.OrientedKer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelColumnsGoodRowsLePrincipalAndFiniteDimensio
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SRe

theorem levCols_le_triv_and_finite : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → R.EEat (R.levR F true) ≤ R.EEat R.triv ∧ FiniteDimensional ℂ (MultR R F) := by
  intro hF _ D G' _ _ Pl0 T A Ks _ _ _ R F _ hi _
  refine ⟨GlobalTheory.Mem.Th.EEat_le_triv R _, ?_⟩
  obtain ⟨U, hU, hJ⟩ := GlobalTheory.DefiniteEnd.exists_open_level (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))
  exact GlobalTheory.MultFinite.hcFinite hF hi ⟨U, hU, fun k hk hk' => by
    obtain ⟨h1, h2⟩ := hJ k hk
    have hm : k ∈ levS (Yc D 0) (R.βY 0) (flag1L (R.dat0 (R.levR F true))) := ⟨hk', h1⟩
    have hc : levChi (Yc D 0) (R.βY 0) (flag1L (R.dat0 (R.levR F true))) k = 1 := congrArg Units.val h2
    obtain ⟨h3, h4⟩ := GlobalTheory.Mem.Th.principal_le_level (R.βY 0) (R.dat0 (R.levR F true)) (R.dat0 (R.levR F true)).P k hm
    exact ⟨h3, h4.trans hc⟩⟩

end GlobalTheory.Mem.SRe

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelRowsReadingEmbeddingGoodRowsModelWithNorm
section
namespace MultiplicativeInnerProducts
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace CompanionTheory.Member.InnerProductScaling

theorem isMultiplicityInner_smul_measure {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (μ : Measure (GA D V))
    (𝓕 : Set (GA D V)) (T T' : MMap M) (c : ℝ) (hc : 0 ≤ c) (a : ℂ) (h : IsMultIP M μ 𝓕 T T' a) :
    IsMultIP M (ENNReal.ofReal c • μ) 𝓕 T T' ((c : ℂ) * a) := by
  intro v v'
  obtain ⟨h1, h2⟩ := h v v'
  refine ⟨?_, ?_⟩
  · unfold IntegrableOn at h1 ⊢
    rw [Measure.restrict_smul]
    exact h1.smul_measure ENNReal.ofReal_ne_top
  · rw [Measure.restrict_smul, integral_smul_measure, h2, ENNReal.toReal_ofReal hc, Complex.real_smul, mul_assoc]

theorem ipM_smul {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (μ : Measure (GA D V))
    (𝓕 : Set (GA D V)) (T T' : MMap M) (c : ℝ) (hc : 0 ≤ c) (a : ℂ) (h : IsMultIP M μ 𝓕 T T' a) :
    ipM M (ENNReal.ofReal c • μ) 𝓕 T T' = (c : ℂ) * a := by
  obtain ⟨v, hv⟩ := GlobalTheory.SchurConst.exists_vec M (GlobalTheory.GardingVec.sm_ne_bot D V S M)
  have h' := isMultiplicityInner_smul_measure M μ 𝓕 T T' c hc a h
  exact hasPeterssonInner_unique M _ 𝓕 T T' v hv (ipM_spec M _ 𝓕 T T' ⟨_, h'⟩) h'

theorem main {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (μ : Measure (GA D V))
    (𝓕 : Set (GA D V)) (H : HMod (MMap M)) (W W0 : Submodule ℂ (MMap M)) (hW : W ≤ W0)
    (hH : H.Is W0 (ipM M μ 𝓕)) (n : ℝ) (hn : 0 < n)
    {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE]
    (j : EE ≃ₗ[ℂ] (W.map (PiTensorProduct.lift : MMap M ≃ₗ[ℂ] AmbT M).toLinearMap))
    (hj : HilbTie (W.map (PiTensorProduct.lift : MMap M ≃ₗ[ℂ] AmbT M).toLinearMap)
      (ipMT M (ENNReal.ofReal n⁻¹ • μ) 𝓕) j) :
    ∃ eE : EE →ₗ[ℂ] H.H, LinearMap.range eE = W.comap H.e ∧ (∀ x, ‖eE x‖ ^ 2 = n * ‖x‖ ^ 2) ∧
      ∀ x, ((j x : W.map (PiTensorProduct.lift : MMap M ≃ₗ[ℂ] AmbT M).toLinearMap) : AmbT M) =
        PiTensorProduct.lift (H.e (eE x)) := by
  let L : MMap M ≃ₗ[ℂ] AmbT M := PiTensorProduct.lift
  let f : EE →ₗ[ℂ] MMap M := L.symm.toLinearMap ∘ₗ (W.map L.toLinearMap).subtype ∘ₗ j.toLinearMap
  have hf : ∀ x, f x = L.symm (j x : AmbT M) := fun _ => rfl
  have hfW : ∀ x, f x ∈ W := fun x => by
    obtain ⟨y, hy, e⟩ := (j x).2
    have e' : L y = (j x : AmbT M) := e
    rw [hf, ← e', L.symm_apply_apply]
    exact hy
  obtain ⟨g, hg⟩ := GlobalTheory.Mem.Th.exists_factor H.e hH.1 f fun x => by
    rw [hH.2.1]; exact hW (hfW x)
  refine ⟨g, ?_, fun x => ?_, fun x => ?_⟩
  · ext u
    constructor
    · rintro ⟨x, rfl⟩
      show H.e (g x) ∈ W
      rw [hg]; exact hfW x
    · intro hu
      refine ⟨j.symm ⟨L (H.e u), Submodule.mem_map_of_mem hu⟩, hH.1 ?_⟩
      rw [hg, hf, j.apply_symm_apply]
      exact L.symm_apply_apply _
  · have h1 : IsMultIP M μ 𝓕 (H.e (g x)) (H.e (g x)) (1 * ⟪g x, g x⟫_ℂ) :=
      GlobalTheory.Mem.Th.isMultiplicityInner_mul_inner H.e one_ne_zero (fun a b => by rw [one_mul]; exact (hH.2.2 a b).symm) _ _
    have h2 := ipM_smul M μ 𝓕 _ _ n⁻¹ (inv_pos.2 hn).le _ h1
    have h3 : ⟪x, x⟫_ℂ = ipM M (ENNReal.ofReal n⁻¹ • μ) 𝓕 (f x) (f x) := hj x x
    rw [← hg, h2, one_mul, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h3
    have h4 : ‖x‖ ^ 2 = n⁻¹ * ‖g x‖ ^ 2 := by
      have h5 : ((‖x‖ ^ 2 : ℝ) : ℂ) = ((n⁻¹ * ‖g x‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_pow]
        exact h3
      exact Complex.ofReal_injective h5
    rw [h4, ← mul_assoc, mul_inv_cancel₀ hn.ne', one_mul]
  · rw [hg, hf]
    exact (L.apply_symm_apply _).symm

end CompanionTheory.Member.InnerProductScaling

theorem CompanionTheory.Member.levelRowsReading_hilbert_embedding_goodRows : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : TopMultH R) (b : Bool) (EE : Type) [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] (X : RowSide D EE) (I : RowIds X (toChainReal R F tupT hm hTop) b), R.models_HE → HilbTie ((toChainReal R F tupT hm hTop).EEc b) ((toChainReal R F tupT hm hTop).ipE b) I.jE → ∃ eE : EE →ₗ[ℂ] R.HE.H, LinearMap.range eE = (R.EEat (R.levR F b)).comap R.HE.e ∧ (∀ x, ‖eE x‖ ^ 2 = RealDat.nP F b * ‖x‖ ^ 2) ∧ ∀ x, ((I.jE x : (toChainReal R F tupT hm hTop).EEc b) : (toChainReal R F tupT hm hTop).Amb 0) = PiTensorProduct.lift (R.HE.e (eE x)) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F tupT hm hTop b EE _ _ _ X I hE hj
  exact CompanionTheory.Member.InnerProductScaling.main (R.MY 0) R.ν0 R.fd0 R.HE (R.EEat (R.levR F b)) (R.EEat R.triv)
    (GlobalTheory.Mem.Th.EEat_le_triv R _) hE (RealDat.nP F b) (RealDat.nP_pos b) I.jE hj

end

end MultiplicativeInnerProducts
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
theorem _root_.GlobalTheory.Adopt.levelRowsReading_embedding_goodRowsModel_with_norm : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : TopMultH R) (b : Bool) (EE : Type) [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] (X : RowSide D EE) (I : RowIds X (toChainReal R F tupT hm hTop) b), R.models_HE → HilbTie ((toChainReal R F tupT hm hTop).EEc b) ((toChainReal R F tupT hm hTop).ipE b) I.jE → ∃ eE : EE →ₗ[ℂ] R.HE.H, LinearMap.range eE = (R.EEat (R.levR F b)).comap R.HE.e ∧ (∀ x, ‖eE x‖ ^ 2 = RealDat.nP F b * ‖x‖ ^ 2) ∧ ∀ x, ((I.jE x : (toChainReal R F tupT hm hTop).EEc b) : (toChainReal R F tupT hm hTop).Amb 0) = PiTensorProduct.lift (R.HE.e (eE x)) := by
  first | exact @MultiplicativeInnerProducts.CompanionTheory.Member.levelRowsReading_hilbert_embedding_goodRows | exact MultiplicativeInnerProducts.CompanionTheory.Member.levelRowsReading_hilbert_embedding_goodRows | (intros; apply MultiplicativeInnerProducts.CompanionTheory.Member.levelRowsReading_hilbert_embedding_goodRows <;> assumption)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftDefiniteFormsEqUnitaryFormsClassSumPairingStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftDefiniteForms_eq_unitaryForms_classSumPairing : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), (∀ o : D.what₂.O, ∃ k : Ks, algebraMap Ks D.what₂.LL k = D.what₂.OtoLL o) → Inputs D → Pins R F cG → Holds R F → ∀ (y : Hd R.toRealDat) (i : Fin D.R.m) (t : T) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (j : (Fin (lDim D A3.A F.lv2.P0 F.lv2.ψ0 i t) → D.what₂.LL) →ₛₗ[D.what₂.embLL] W), LinearIndependent ℂ (fun k => j (Pi.single k 1)) → Submodule.span ℂ (Set.range fun k => j (Pi.single k 1)) = ⊤ → (∀ x x', ⟪j x, j x'⟫_ℂ = D.what₂.embLL (Formalism.DivisionValues.hform (lH D A3.A F.lv2.P0 F.lv2.ψ0 i t) x x')) → ∃ J : W →ₗ[ℂ] (GA D ((y.L F.lv2).V i) → (y.L F.lv2).TauV i), Function.Injective J ∧ LinearMap.range J = (y.L F.lv2).Amt (y.tup t) i ∧ (∀ x x', ⟪x, x'⟫_ℂ = (y.L F.lv2).ipA (y.tup t) i (J x) (J x')) ∧ ∀ x, J (j x) = R.toRealDat.extV i t (R.toRealDat.jV i t (liftForm A3.A F.lv2.P0 F.lv2.ψ0 i t x)) := by
  first | exact @GlobalTheory.Mem.R3.Rw.LiftForms.lift_forms_embed | exact GlobalTheory.Mem.R3.Rw.LiftForms.lift_forms_embed | (intros; apply GlobalTheory.Mem.R3.Rw.LiftForms.lift_forms_embed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemOfOrderDvd
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Mem GlobalTheory.Mem.Fld GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.Mem.ValFin

theorem locInf_eq_one {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (χ : HChar E) {n : ℕ} (hn : 0 < n)
    (h : χ.OrderDvd n) (w : InfinitePlace E) (x : (w.Completion)ˣ) : χ.1 (ReciprocityTheory.Neutral.Bridge.HCFR.infIdele E w x) = 1 := by
  let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (e x) hn
  have hz' : (e.symm z) ^ n = x := by rw [← map_pow, hz, e.symm_apply_apply]
  have h0 : e.symm z ≠ 0 := fun h0 => x.ne_zero (by rw [← hz', h0, zero_pow hn.ne'])
  have hx : x = Units.mk0 _ h0 ^ n := Units.ext hz'.symm
  rw [hx, map_pow, map_pow]
  exact congrArg (fun χ : HChar E => χ.1 (ReciprocityTheory.Neutral.Bridge.HCFR.infIdele E w (Units.mk0 _ h0))) h

theorem inf_eq_one {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (χ : HChar E) {n : ℕ} (hn : 0 < n)
    (h : χ.OrderDvd n) (k : Eˣ) : χ.inf k = 1 := by
  show χ.1 (infDiag k) = 1
  rw [infDiag, MonoidHom.finset_prod_apply, map_prod]
  exact Finset.prod_eq_one fun w _ => locInf_eq_one χ hn h w _

theorem mem_of_orderDvd : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (χ : HChar E) (M : IntermediateField ℚ ℂ), (∃ n : ℕ, 0 < n ∧ χ.OrderDvd n) → valueField χ 0 ≤ M → ∀ x, ((χ.1 x : ℂˣ) : ℂ) ∈ M := by
  intro E _ _ _ χ M hn hM x
  obtain ⟨n, hn0, hord⟩ := hn
  have hinf : ∀ k : Eˣ, ((χ.inf k : ℂˣ) : ℂ) ∈ M := fun k => by
    rw [inf_eq_one χ hn0 hord k, Units.val_one]
    exact one_mem M
  rw [← GlobalTheory.Mem.ReadEx.map_finPartI hn0 hord x]
  exact GlobalTheory.T.heckeCharacter_finiteIdele_value_mem_field E χ M hM hinf (GlobalTheory.Mem.Chr.finPartI E x) fun w => by
    rw [GlobalTheory.Mem.Chr.finPartI_fst]; rfl

end GlobalTheory.Mem.ValFin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RamifiedFormsCommensurableOfUStableInjectiveStatement
section
open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ramifiedForms_commensurable_of_U_stable_injective : ∀ (D : D7) (u : D.what₂.Word), (∀ v, ∀ x ∈ (D.fm u).ramSub, ∃ y ∈ (D.fm u).ramSub, (D.fm u).emb 0 y = LT.Uop D u 0 v ((D.fm u).emb 0 x)) → (∀ v, ∀ φ ∈ (D.mem u).A.Mram, LT.Uop D u 0 v φ = 0 → φ = 0) → ∀ w : D.what₂.places.Pl, ∃ n : ℕ, n ≠ 0 ∧ (∀ x ∈ DV.MramL D u, D.nuIn u (n • x) ∈ LT.Nlam D u w) ∧ ∀ x, D.nuIn u x ∈ LT.Nlam D u w → InLoc (D.plEq w) (DV.MramL D u) (n • x) := by
  first | exact @GlobalTheory.LevelCommensurable.commensurable | exact GlobalTheory.LevelCommensurable.commensurable | (intros; apply GlobalTheory.LevelCommensurable.commensurable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RatIsomOfInducedHermitianBundlesStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.HermIsom Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ratIsom_of_induced_hermitian_bundles : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y) (N : TrueGeo.Model Y), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme N.X → ∀ (L L' : HermLB N.p) (k : ℕ+) (cf : HeightOneSpectrum (𝓞 F) → ℝ), A.Induced N L k cf → A.Induced N L' k cf → (haveI := N.ar.isIntegral; RatIsom L L') := by
  first | exact @GlobalTheory.TrueGeo.InducedIsom.ratIsom_of_induced | exact GlobalTheory.TrueGeo.InducedIsom.ratIsom_of_induced | (intros; apply GlobalTheory.TrueGeo.InducedIsom.ratIsom_of_induced <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayFieldLeAndExistsBaseStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Fld GlobalTheory.Mem.HD NumberField IsDedekindDomain
open scoped nonZeroDivisors IntermediateField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rayField_le_and_exists_base : RayField → PrincipalIdealSt → ∀ (P : Pre) (f : Fr P) (δ : FieldDat P), listField δ f ≤ δ.Om ∧ ∃ B : Base, B.toPre = P ∧ B.KsC = listField δ f := by
  first | exact @GlobalTheory.Mem.KsBase.exists_base_listField | exact GlobalTheory.Mem.KsBase.exists_base_listField | (intros; apply GlobalTheory.Mem.KsBase.exists_base_listField <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayFieldTopMaximalUnramified
section
noncomputable section

open Formalism.L2.Host GlobalTheory.Published GlobalTheory.NT GlobalTheory.Mem.Fld GlobalTheory.Mem.HD NumberField IsDedekindDomain

namespace GlobalTheory.HilbertInClosure

theorem rayField_top_maximal_unramified : GlobalArtinReciprocity → ∀ (E : Type) [Field E] [NumberField E]
    [IsTotallyComplex E] (j : E →ₐ[ℚ] Qb) (ι : Qb →+* ℂ) (M : IntermediateField ℚ ℂ),
    IsRayFieldIn (ι.comp j.toRingHom) ⊤ M →
    ∃ _ : NumberField (qb ι M),
      (j.fieldRange ≤ qb ι M ∧
        (∀ σ : Qb ≃ₐ[ℚ] Qb, (∀ x ∈ j.fieldRange, σ x = x) → ∀ y ∈ qb ι M, σ y ∈ qb ι M) ∧
        ∀ σ τ : Qb ≃ₐ[ℚ] Qb, (∀ x ∈ j.fieldRange, σ x = x) → (∀ x ∈ j.fieldRange, τ x = x) →
          ∀ y ∈ qb ι M, σ (τ y) = τ (σ y)) ∧
      (discr (qb ι M)).natAbs = (discr E).natAbs ^ (Module.finrank ℚ (qb ι M) / Module.finrank ℚ E) ∧
      ∀ (L : Fld) [NumberField L],
        (j.fieldRange ≤ L ∧ (∀ σ : Qb ≃ₐ[ℚ] Qb, (∀ x ∈ j.fieldRange, σ x = x) → ∀ y ∈ L, σ y ∈ L) ∧
          ∀ σ τ : Qb ≃ₐ[ℚ] Qb, (∀ x ∈ j.fieldRange, σ x = x) → (∀ x ∈ j.fieldRange, τ x = x) →
            ∀ y ∈ L, σ (τ y) = τ (σ y)) →
        (discr L).natAbs = (discr E).natAbs ^ (Module.finrank ℚ L / Module.finrank ℚ E) → L ≤ qb ι M := by
  intro H E _ _ _ j ι M hM
  obtain ⟨hN, h, hst, hc, hd, hmax⟩ := hilbert_qb_aut H E j ι M hM
  have hm : ∀ σ : Qb ≃ₐ[ℚ] Qb, σ ∈ GalOf j.fieldRange ↔ ∀ x ∈ j.fieldRange, σ x = x := fun σ =>
    IntermediateField.mem_fixingSubgroup_iff _ _
  exact ⟨hN, ⟨h, fun σ hσ => hst σ ((hm σ).2 hσ), fun σ τ hσ hτ => hc σ ((hm σ).2 hσ) τ ((hm τ).2 hτ)⟩, hd,
    fun L _ hL => hmax L hL.1 fun σ hσ τ hτ => hL.2.2 σ τ ((hm σ).1 hσ) ((hm τ).1 hτ)⟩

end GlobalTheory.HilbertInClosure

end
end

