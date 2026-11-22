import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0311
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0315
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
import Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.LatSOfLocBasis
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0314
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DualLatticeLocalCharacterization
import Formalism.LocalToGlobal.GlobalTheory.GL6.Bundle0007
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0009
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharacteristicFunctionIntegralApply
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EmbRelExistsUnique
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0012
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrincipalCongruenceLevelContained
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0080
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0956
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.LinearIndependentWave
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0213
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0912
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0206
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0313
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0307
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0312
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0316
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TwistEmptyOfChartsEx
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.LocalProductMeasures.MqRowSGUnif
import Formalism.SharpRestriction.GlobalSchurBounds.Joints
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0026
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008
import Formalism.LocalToGlobal.GroupLattices.Joint0
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0301
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0538

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardFramesReadSplitPlaceUnitaryGroup
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitFrameRead

theorem tensCast_one_tmul {E : Type} [Field E] [NumberField E] {F1 F2 : Subfield E} (h : F1 = F2) (x : E) :
    GlobalTheory.NJoin.tensCast h ((1 : FiniteAdeleRing (𝓞 F1) F1) ⊗ₜ[F1] x) = x ⊗ₜ[F2] (1 : FiniteAdeleRing (𝓞 F2) F2) := by
  subst h; rfl

theorem gen_supp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (fin : A →+* B) (Ψ : B →+* C) {m k : ℕ}
    (M : Matrix (Fin m) (Fin m) A) (β : Matrix (Fin m) (Fin k) B) (K : Matrix (Fin k) (Fin k) B) (β' : Matrix (Fin k) (Fin m) B)
    (h1 : β * β' = 1) (hM : M.map fin = β * K * β') (hK : K.map Ψ = 1) : ((M - 1).map fin).map Ψ = 0 := by
  rw [Matrix.map_sub _ (map_sub _), hM, Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_sub _ (map_sub _),
    Matrix.map_mul, Matrix.map_mul, hK, Matrix.mul_one, ← Matrix.map_mul, h1, sub_self]

set_option maxHeartbeats 1000000 in

theorem side_loc (D : D7) (s : SplitPlace D.host.E) (hF : D.host.F = maximalRealSubfield D.host.E)
    (p : GlobalTheory.LocMod.Place D (s.w.adicCompletion D.host.E))
    (c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E)
    (hπ : ∀ a : Formalism.L2.Theta.AE D, p.π a = c (s.proj (GlobalTheory.NJoin.tensCast hF (Formalism.L2.Theta.finPart D a))))
    (V : Formalism.BasicNotions.TH.HSp D) (n : ℕ) (PV : Formalism.IndefR.principalLevelFrame.RowPsi V n) (hV : GlobalTheory.NJoin.StdFrame hF PV) :
    ∃ FS : GlobalTheory.LocMod.Frame (s.w.adicCompletion D.host.E) V.rank (Fin n), ∀ h, TrivOutside {s.v} h →
      p.IsLoc FS (PV.ψ h) (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n h)) := by
  obtain ⟨⟨β, β', h1, h2, hm⟩, -⟩ := hV
  let Φ := c.toRingHom.comp (s.proj.comp (GlobalTheory.NJoin.tensCast hF).toRingHom)
  refine ⟨⟨β.map Φ, β'.map Φ, ?_, ?_⟩, fun h hh => ⟨?_, ?_⟩⟩
  · rw [← Matrix.map_mul, h1]; exact Matrix.map_one _ (map_zero Φ) (map_one Φ)
  · rw [← Matrix.map_mul, h2]; exact Matrix.map_one _ (map_zero Φ) (map_one Φ)
  · intro i j
    apply GlobalTheory.T.splitPlaceIdempotent_mul_eq_self_of_supported D s hF p c hπ
    · have hk := MonoidHom.mem_ker.1 (PV.into h)
      have e2 : ((Formalism.L2.Theta.mt V (PV.ψ h)) - 1).map (Formalism.L2.Theta.infPart D) = 0 := by
        rw [Matrix.map_sub _ (map_sub (Formalism.L2.Theta.infPart D)),
          Matrix.map_one _ (map_zero (Formalism.L2.Theta.infPart D)) (map_one (Formalism.L2.Theta.infPart D))]
        have e3 : (Formalism.L2.Theta.mt V (PV.ψ h)).map (Formalism.L2.Theta.infPart D) = (Formalism.L2.Theta.infHom V (PV.ψ h)).val := rfl
        rw [e3, hk, Units.val_one, sub_self]
      exact congrFun (congrFun e2 i) j
    · intro v' hv'
      have hh' := hh v' (by simpa using hv')
      have e4 := gen_supp (Formalism.L2.Theta.finPart D) ((ReciprocityTheory.Aut.compAt D.host.E v').comp (GlobalTheory.NJoin.tensCast hF).toRingHom)
        (Formalism.L2.Theta.mt V (PV.ψ h)) β _ β' h1 (hm h) (by
          rw [← hh']
          ext a b
          exact congrArg (ReciprocityTheory.Aut.compAt D.host.E v') (RingEquiv.apply_symm_apply _ _))
      exact congrFun (congrFun e4 i) j
  · have e7 : (Formalism.L2.Theta.mt V (PV.ψ h)).map p.π = ((Formalism.L2.Theta.mt V (PV.ψ h)).map (Formalism.L2.Theta.finPart D)).map Φ :=
      Matrix.ext fun a b => hπ _
    have e5 : (Formalism.L2.Theta.mt V (PV.ψ h)).map (Formalism.L2.Theta.finPart D) = _ := hm h
    have hK : ((h.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL D.host.E)).map (GlobalTheory.NJoin.tensCast hF).symm).map Φ =
        (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n h)).val := by
      refine Matrix.ext fun a b => ?_
      exact congrArg (fun y => c (s.proj y)) (RingEquiv.apply_symm_apply _ _)
    rw [e7, e5, ← hK]
    exact (Matrix.map_mul).trans (congrArg (· * β'.map Φ) Matrix.map_mul)

theorem main : ∀ (D : D7) (V W : Formalism.BasicNotions.TH.HSp D) (n r : ℕ) (PV : Formalism.IndefR.principalLevelFrame.RowPsi V n) (PW : Formalism.IndefR.principalLevelFrame.RowPsi W r) (hF : D.host.F = maximalRealSubfield D.host.E), GlobalTheory.NJoin.StdFrame hF PV → GlobalTheory.NJoin.StdFrame hF PW → ∀ (s : SplitPlace D.host.E), ∃ (p : GlobalTheory.LocMod.Place D (s.w.adicCompletion D.host.E)), Formalism.L2.JoinChr.IsPlIdem D p.e s.w ∧ (∀ x : D.host.E, p.pr x = algebraMap D.host.E (s.w.adicCompletion D.host.E) x) ∧ ∃ (FS : GlobalTheory.LocMod.Frame (s.w.adicCompletion D.host.E) V.rank (Fin n)) (FT : GlobalTheory.LocMod.Frame (s.w.adicCompletion D.host.E) W.rank (Fin r)) (c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E), Continuous c ∧ (∀ x : D.host.E, c (s.i x) = algebraMap D.host.E (s.w.adicCompletion D.host.E) x) ∧ (∀ h, TrivOutside {s.v} h → p.IsLoc FS (PV.ψ h) (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n h))) ∧ ∀ g, TrivOutside {s.v} g → p.IsLoc FT (PW.ψ g) (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc r g)) := by
  intro D V W n r PV PW hF hV hW s
  obtain ⟨p, c, hId, hc, hci, hπ⟩ := GlobalTheory.T.exists_splitLocalPlaceData_at_splitPlace D s hF
  have hpr : ∀ x : D.host.E, p.pr x = algebraMap D.host.E (s.w.adicCompletion D.host.E) x := by
    intro x
    unfold GlobalTheory.LocMod.Place.pr
    rw [hπ]
    have e1 : Formalism.L2.Theta.finPart D (Formalism.L2.Theta.incA D x) =
        (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] x := by
      simp [Formalism.L2.Theta.finPart, Formalism.L2.Theta.incA, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR, Algebra.TensorProduct.map_tmul]
    rw [e1, tensCast_one_tmul, ← hci x]
    congr 1
    simp [ReciprocityTheory.Aut.SplitPlace.proj]
  obtain ⟨FS, hFS⟩ := side_loc D s hF p c hπ V n PV hV
  obtain ⟨FT, hFT⟩ := side_loc D s hF p c hπ W r PW hW
  exact ⟨p, hId, hpr, FS, FT, c, hc, hci, hFS, hFT⟩

end GlobalTheory.SplitFrameRead
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepPointPulledDualVectorMemLocalBaseLattice
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open Formalism.UG (bc prV)
open Matrix Formalism.UG Formalism.L2.PairingIndexBounds.F Formalism.L2.Forms Formalism.MainNotions.G.KAat
open scoped TensorProduct

namespace GlobalTheory.ZDual

section Gen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {N : ℕ}

theorem pullV_dual_mem_latS_gen (σ : E →ₐ[F] E) (J : Matrix (Fin N) (Fin N) E) (hJ : IsUnit J.det)
    (Lb : Submodule (𝓞 E) (Fin N → E)) (hfin : Module.Finite (𝓞 E) Lb)
    (hspan : Submodule.span E (Lb : Set (Fin N → E)) = ⊤)
    (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (hx : x ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (v : HeightOneSpectrum (𝓞 F)) (l : Fin N → E) (hl : l ∈ dualSet (σ : E →+* E) J (latAd x Lb)) :
    (fun k => prV (E := E) v (pullV (F := F) x l k)) ∈ latS (F := F) (v.adicCompletion F) (intV E v)
        (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J Lb)) := by
  have hU : cT (sigR σ (v.adicCompletion F)) (bc (prV (E := E) v) x).val *
      J.map (inclE (F := F) (v.adicCompletion F)) * (bc (prV (E := E) v) x).val =
      J.map (inclE (F := F) (v.adicCompletion F)) := Formalism.UG.P.afsplit_bc_mem σ J v x hx
  have hy : (fun k => prV (E := E) v (pullV (F := F) x l k)) =
      ((bc (prV (E := E) v) x)⁻¹).val *ᵥ (fun k => inclE (F := F) (v.adicCompletion F) (l k)) := by
    rw [GlobalTheory.LocCarry.coe_bc_inv]
    funext k
    unfold pullV
    rw [RingHom.map_mulVec]
    rfl
  rw [hy]
  refine GlobalTheory.St.G.Dual.bwd_loc σ J hJ.ne_zero Lb ⟨hfin, hspan⟩ v _ fun b hb => ?_
  unfold GlobalTheory.St.G.hR
  have key := Formalism.UG.P.hform_mulVec (sigR σ (v.adicCompletion F)) (J.map (inclE (F := F) (v.adicCompletion F)))
    (bc (prV (E := E) v) x).val (fun k => inclE (F := F) (v.adicCompletion F) (b k))
    (((bc (prV (E := E) v) x)⁻¹).val *ᵥ (fun k => inclE (F := F) (v.adicCompletion F) (l k)))
  rw [hU, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec] at key
  rw [← key]
  refine Formalism.L2.G.RelativeIndexFlags.pair_int v σ J (latAd x Lb) l hl _ ?_
  rw [GlobalTheory.LocCarry.mem_latS_latAd_iff x Lb hfin hspan v, Matrix.mulVec_mulVec, ← Units.val_mul,
    inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  exact Submodule.subset_span ⟨b, hb, rfl⟩

end Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar in

theorem pullV_dual_mem_latS : ∀ {D : D7} (i : ℕ) (hi : i ≤ D.R.m) {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
    (lev : StepLevel D.host.F D.host.E (sigD D) (gramN D i hi) T f bad) (x : UA D i hi) (v : HeightOneSpectrum (𝓞 D.host.F))
    (l : Fin (D.R.N i) → D.host.E), l ∈ dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) (latAd x.1 lev.Lb) →
    (fun k => prV (E := D.host.E) v (pullV (F := D.host.F) x.1 l k)) ∈ latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v)
        (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) lev.Lb)) := by
  intro D i hi T f bad lev x v l hl
  exact pullV_dual_mem_latS_gen (sigD D) (gramN D i hi) (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D i hi) lev.Lb lev.Lb_fin
    lev.Lb_span x.1 x.2 v l hl

end GlobalTheory.ZDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaFunctionContinuousInvariant
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct ComplexOrder
open MeasureTheory Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

noncomputable section

namespace GlobalTheory.ThetaFormV

open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR GlobalTheory.ThetaTri
open scoped Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Frame

variable {D : D7} {V : HSp D} {n : ℕ}

theorem fin_preF (PV : principalLevelFrame.RowPsi V n) (k : Bridge.Gf V) :
    (finHom V).rangeRestrict (PV.ψ (preF PV k)) = k := by
  have hex : ∃ κ, (finHom V).rangeRestrict (PV.ψ κ) = k := by
    obtain ⟨κ, hκ, e⟩ := Formalism.IndefR.Eqv.Act.exists_finLift V k
    obtain ⟨h, rfl⟩ := PV.onto κ hκ
    exact ⟨h, Subtype.ext e⟩
  unfold preF
  rw [dif_pos hex]
  exact hex.choose_spec

theorem preF_fin (PV : principalLevelFrame.RowPsi V n) (x : Formalism.AUTREP.GAf D.host.E n) :
    preF PV ((finHom V).rangeRestrict (PV.ψ x)) = x := by
  apply PV.inj
  have e1 : finHom V (PV.ψ (preF PV ((finHom V).rangeRestrict (PV.ψ x)))) = finHom V (PV.ψ x) :=
    congrArg Subtype.val (fin_preF PV _)
  refine inv_mul_eq_one.1 (GlobalTheory.AutFunCounterexample.GfC_inf_GinfC V
    ((GfC V).mul_mem ((GfC V).inv_mem (PV.into _)) (PV.into _)) ?_)
  show finHom V _ = 1
  rw [map_mul, map_inv, e1, inv_mul_cancel]

theorem preF_mul (PV : principalLevelFrame.RowPsi V n) (k₁ k₂ : Bridge.Gf V) :
    preF PV (k₁ * k₂) = preF PV k₁ * preF PV k₂ := by
  have h := preF_fin PV (preF PV k₁ * preF PV k₂)
  rwa [map_mul, map_mul, fin_preF, fin_preF] at h

theorem ext_apply (c : CoefA V) (f : Bridge.Gf V → c.W) (h : GA D V) :
    c.ext f h = c.ρ h⁻¹ (f ((finHom V).rangeRestrict h)) := rfl

theorem mem_adForms_one (c : CoefA V) (f : Bridge.Gf V → c.W)
    (hf : ∀ γ ∈ GQ V, ∀ k, f ((finHom V).rangeRestrict γ * k) = c.ρ γ (f k))
    (J : Subgroup (Bridge.Gf V)) (hJ : ∀ q ∈ J, ∀ k, f (k * q) = f k) :
    f ∈ Bridge.AdForms ((finHom V).rangeRestrict.comp (GQ V).subtype) (c.ρ.comp (GQ V).subtype) J 1 := by
  intro γ h k
  have e1 := hJ k k.2 ((finHom V).rangeRestrict (γ : GA D V) * h)
  have e2 := hf γ γ.2 h
  simp only [MonoidHom.one_apply, Units.val_one, one_smul, MonoidHom.comp_apply, Subgroup.coe_subtype]
  exact e1.trans e2

end Frame

section Forms

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {P : Pin hL D} {X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp}

theorem eW_cast_wt (A : GlobalTheory.NJoin.Agree X P.M P.rep) {μ : D.what₂.Tup} (hμ : Formalism.IndefR.RecTie.Used0 D μ)
    (j : Fin D.R.m) (k : ℕ) (hk : j.1 + 1 = k) (p1 : 1 ≤ k) (p2 : k ≤ D.R.m)
    (h : ReciprocityTheory.Aut.GQ D.host.E D.R.nV) {γ : GA D (Vc D j)} (hγ : γ ∈ GQ (Vc D j))
    (he : finHom (Vc D j) γ = finHom (Vc D j) ((A.PV j).ψ ((A.a j)⁻¹ * h * A.a j))) (v : (X.R.cV j).W) :
    (Eq.ndrec (motive := fun k => (p1 : 1 ≤ k) → (p2 : k ≤ D.R.m) →
        (X.R.cV j).W ≃ₗ[ℂ] (P.M μ k p1 p2).wt.W) (fun _ _ => A.eW μ hμ j) hk p1 p2) ((X.R.cV j).ρ γ v) =
      (P.M μ k p1 p2).wt.ρ h ((Eq.ndrec (motive := fun k => (p1 : 1 ≤ k) → (p2 : k ≤ D.R.m) →
        (X.R.cV j).W ≃ₗ[ℂ] (P.M μ k p1 p2).wt.W) (fun _ _ => A.eW μ hμ j) hk p1 p2) v) := by
  subst hk
  exact A.wt μ hμ j h γ hγ he v

theorem eWloc_wt (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (h : ReciprocityTheory.Aut.GQ D.host.E D.R.nV) {γ : GA D (Vc D j)}
    (hγ : γ ∈ GQ (Vc D j))
    (he : finHom (Vc D j) γ = finHom (Vc D j) ((A.PV j).ψ ((A.a j)⁻¹ * h * A.a j))) (v : (X.R.cV j).W) :
    eWloc A i j hj hμ ((X.R.cV j).ρ γ v) = (P.M.loc i).wt.ρ h (eWloc A i j hj hμ v) :=
  eW_cast_wt A hμ j _ hj _ _ h hγ he v

end Forms

section Main

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {P : Pin hL D} {X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp}

def fFin (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (F : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ)) :
    Bridge.Gf (Vc D j) → (X.R.cV j).W :=
  fun k => (eWloc A i j hj hμ).symm ((F : GAf D.host.E D.R.nV → (P.M.loc i).wt.W) (A.a j * preF (A.PV j) k))

theorem fFin_apply (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (F : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ))
    (k : Bridge.Gf (Vc D j)) : fFin A i j hj hμ F k =
      (eWloc A i j hj hμ).symm ((F : GAf D.host.E D.R.nV → (P.M.loc i).wt.W) (A.a j * preF (A.PV j) k)) := rfl

theorem fV_eq_ext (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (F : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ)) :
    fV A i j hj hμ F = (X.R.cV j).ext (fFin A i j hj hμ F) := rfl

theorem fFin_rat (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (F : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ))
    {γ : GA D (Vc D j)} (hγ : γ ∈ GQ (Vc D j)) (k : Bridge.Gf (Vc D j)) :
    fFin A i j hj hμ F ((finHom (Vc D j)).rangeRestrict γ * k) = (X.R.cV j).ρ γ (fFin A i j hj hμ F k) := by
  set x := preF (A.PV j) ((finHom (Vc D j)).rangeRestrict γ) with hxdef
  have hx : finHom (Vc D j) γ = finHom (Vc D j) ((A.PV j).ψ x) :=
    (congrArg Subtype.val (GlobalTheory.ThetaFormV.fin_preF (A.PV j) ((finHom (Vc D j)).rangeRestrict γ))).symm
  have e0 : (A.a j)⁻¹ * (A.a j * x * (A.a j)⁻¹) * A.a j = x := by group
  have hrat : A.a j * x * (A.a j)⁻¹ ∈ ReciprocityTheory.Aut.GQ D.host.E D.R.nV :=
    (A.rat j _).2 ⟨γ, hγ, by rw [e0]; exact hx⟩
  have he : finHom (Vc D j) γ =
      finHom (Vc D j) ((A.PV j).ψ ((A.a j)⁻¹ * ((⟨_, hrat⟩ : ReciprocityTheory.Aut.GQ D.host.E D.R.nV) : GAf D.host.E D.R.nV) * A.a j)) := by
    rw [e0]; exact hx
  have e1 : A.a j * preF (A.PV j) ((finHom (Vc D j)).rangeRestrict γ * k) =
      (A.a j * x * (A.a j)⁻¹) * (A.a j * preF (A.PV j) k) := by
    rw [GlobalTheory.ThetaFormV.preF_mul, ← hxdef]; group
  have hF := F.2.1 ⟨_, hrat⟩ (A.a j * preF (A.PV j) k)
  unfold fFin
  rw [e1]
  refine (LinearEquiv.symm_apply_eq _).2 ?_
  rw [eWloc_wt A i j hj hμ ⟨_, hrat⟩ hγ he, LinearEquiv.apply_symm_apply]
  exact hF

theorem fV_invariant (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (F : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ)) :
    ∀ γ ∈ GQ (Vc D j), ∀ h, fV A i j hj hμ F (γ * h) = fV A i j hj hμ F h := by
  intro γ hγ h
  rw [fV_eq_ext, GlobalTheory.ThetaFormV.ext_apply, GlobalTheory.ThetaFormV.ext_apply, map_mul, fFin_rat A i j hj hμ F hγ]
  have e : (X.R.cV j).ρ (γ * h)⁻¹ * (X.R.cV j).ρ γ = (X.R.cV j).ρ h⁻¹ := by
    rw [← map_mul]; congr 1; group
  exact congrArg (fun T : Module.End ℂ (X.R.cV j).W => T _) e

end Main

theorem eventually_cong_preF {D : D7} {V : HSp D} {n : ℕ} (PV : principalLevelFrame.RowPsi V n)
    (hF : D.host.F = maximalRealSubfield D.host.E) (hstd : GlobalTheory.NJoin.StdFrame hF PV) {N : ℕ} (hN : 0 < N) :
    ∀ᶠ κ in 𝓝 (1 : GA D V), NG.Cong D.host.E n N (preF PV ((finHom V).rangeRestrict κ)) := by
  obtain ⟨N', hN', himg⟩ := GlobalTheory.LatCongImage.finCong_mem_levN D V n PV hF hstd N hN
  filter_upwards [GlobalTheory.Member.PrincLevel.finCong_mem_nhds V hN'] with κ hκ
  obtain ⟨κ', hκ', e⟩ := Formalism.IndefR.Eqv.Act.exists_finLift V ((finHom V).rangeRestrict κ)
  have hc : GlobalTheory.Member.FinCong V N' κ' := by
    intro z hz
    have e' : finHom V κ' = finHom V κ := e
    rw [e']
    exact hκ z hz
  obtain ⟨x, hx, hxe⟩ := himg κ' hκ' hc
  have e2 : (finHom V).rangeRestrict κ = (finHom V).rangeRestrict (PV.ψ x) := by
    rw [hxe]; exact (Subtype.ext e).symm
  rw [e2, GlobalTheory.ThetaFormV.preF_fin]
  exact hx

section Cont

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {P : Pin hL D} {X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp}

theorem fV_continuous (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (F : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ)) :
    Continuous (fV A i j hj hμ F) := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  haveI : IsTopologicalGroup (GA D (Vc D j)) :=
    inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig (Vc D j).gram))
  obtain ⟨N, hN, hlev⟩ := F.2.2
  let J : Subgroup (Bridge.Gf (Vc D j)) :=
    { carrier := {q | ∀ k, fFin A i j hj hμ F (k * q) = fFin A i j hj hμ F k}
      mul_mem' := fun {a b} ha hb k => by simp only [Set.mem_setOf_eq] at ha hb ⊢; rw [← mul_assoc, hb, ha]
      one_mem' := fun k => by rw [mul_one]
      inv_mem' := fun {a} ha k => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [← ha (k * a⁻¹), inv_mul_cancel_right] }
  have hfJ : fFin A i j hj hμ F ∈ Bridge.AdForms ((finHom (Vc D j)).rangeRestrict.comp (GQ (Vc D j)).subtype)
      ((X.R.cV j).ρ.comp (GQ (Vc D j)).subtype) J 1 := by
    exact GlobalTheory.ThetaFormV.mem_adForms_one _ _ (fun γ hγ k => fFin_rat A i j hj hμ F hγ k) J (fun q hq => hq)
  have hJ : ∀ᶠ κ in 𝓝 (1 : GA D (Vc D j)), ∃ h : (finHom (Vc D j)).rangeRestrict κ ∈ J,
      (1 : J →* ℂˣ) ⟨_, h⟩ = 1 := by
    filter_upwards [eventually_cong_preF (A.PV j) A.hF (A.stdV j) hN] with κ hκ
    refine ⟨fun k => ?_, rfl⟩
    show fFin A i j hj hμ F (k * (finHom (Vc D j)).rangeRestrict κ) = fFin A i j hj hμ F k
    rw [fFin_apply, fFin_apply, GlobalTheory.ThetaFormV.preF_mul, ← mul_assoc, hlev _ hκ]
  exact (GlobalTheory.ThetaIntegrand.form_continuous (finHom (Vc D j)).rangeRestrict (GQ (Vc D j)) (X.R.cV j).ρ
    ((X.given.core.models.cV j).2.2.1) hJ hfJ).congr fun g => (GlobalTheory.ThetaFormV.ext_apply _ _ _).symm

end Cont

theorem fV_continuous_invariant : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D) (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp)
    (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (F : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ)),
    Continuous (GlobalTheory.ThetaTri.fV A i j hj hμ F) ∧
      ∀ γ ∈ GQ (Vc D j), ∀ h, GlobalTheory.ThetaTri.fV A i j hj hμ F (γ * h) = GlobalTheory.ThetaTri.fV A i j hj hμ F h :=
  fun _ _ _ _ A i j hj hμ F => ⟨fV_continuous A i j hj hμ F, fV_invariant A i j hj hμ F⟩

end GlobalTheory.ThetaFormV

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaFunctionMemSpanLocalSchrodingerModelsSplit
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.LocMod GlobalTheory.PlaceModel ValuativeRel
namespace GlobalTheory.LocMod.SpanModels

theorem mem_iSup_range_isModel : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.LocMod.Place D k) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : Formalism.BasicNotions.TH.HSp D) (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ), Formalism.L2.Theta.IsStdChar D ψ (-1) → ∀ f, Formalism.IndefR.Datum.IsThetaFunO ψ S T f → f ∈ ⨆ (Tm : GlobalTheory.SplitWeil.SB (Matrix Y Y' k) →ₗ[ℂ] (Formalism.IndefR.Datum.WO S T → ℂ)) (_ : p.IsModel ψ FS FT Tm), LinearMap.range Tm := by
  intro D k _ _ _ _ p Y Y' _ _ _ _ S T FS FT ψ hψ f hf
  classical
  obtain ⟨U, hUo, hUf⟩ := hf.level
  obtain ⟨c, hc, L', K, hL, hL'e, hK, ⟨R, hR⟩, hL'K, hsep⟩ := GlobalTheory.T.exists_split_rescaled_lattice_and_dual D k p Y Y' S T FS FT ψ hψ U hUo
  have hinf : Formalism.L2.Theta.infPart D p.e = 0 := GlobalTheory.PlaceCoord.infPart_split p.split
  have hinf' : Formalism.L2.Theta.infPart D (Formalism.L2.Theta.cA D p.e) = 0 := GlobalTheory.PlaceDatum.infPart_cA hinf
  have hec : p.e * Formalism.L2.Theta.cA D p.e = 0 := p.split.2.1
  let I : AddSubgroup (Matrix Y Y' k) :=
    { carrier := {x | ∀ i j, x i j ∈ 𝒪[k]}
      add_mem' := fun ha hb i j => add_mem (ha i j) (hb i j)
      zero_mem' := fun i j => zero_mem _
      neg_mem' := fun ha i j => neg_mem (ha i j) }
  let L : AddSubgroup (Formalism.IndefR.Datum.WO S T) :=
    I.map ((Witness.upH p FS FT).comp (DistribMulAction.toAddMonoidHom (Matrix Y Y' k) c))
  have memL : ∀ t, t ∈ L ↔ ∃ x : Matrix Y Y' k, (∀ i j, x i j ∈ 𝒪[k]) ∧ p.up FS FT (c • x) = t := fun t => Iff.rfl
  let W : Submodule ℂ (Formalism.IndefR.Datum.WO S T → ℂ) :=
    { carrier := {g | Formalism.IndefR.Datum.IsThetaFunO ψ S T g}
      add_mem' := fun ha hb => GlobalTheory.LocMod.LinSpace.isThetaFunO_add ha hb
      zero_mem' := GlobalTheory.LocMod.LinSpace.isThetaFunO_zero ψ S T
      smul_mem' := fun c _ hg => GlobalTheory.LocMod.LinSpace.isThetaFunO_smul c hg }
  have key := GlobalTheory.T.mem_span_translates_of_fixed_lattice (fun x y => ψ (Formalism.IndefR.Datum.symplO S T x y)) (isBichar_symplO S T ψ) (heisL S T ψ)
    (half S T p.e) (half S T (Formalism.L2.Theta.cA D p.e)) L L' K
    (by rintro _ ⟨x, hx, rfl⟩; exact (hL x hx).1)
    (fun t ht => (isHalf_iff S T).1 (hL'e t ht))
    (fun y hy => (isHalf_iff S T).1 (hK y hy).1)
    (fun v => by
      funext w
      change ψ (Formalism.IndefR.Datum.symplOH S T w 0) * v (w + 0) = v w
      simp [Formalism.IndefR.Datum.symplOH, symplO_zero_right])
    (fun x hx x' hx' v => heisL_half S T ψ (by rw [mul_comm]; exact hec) x hx x' hx' v)
    (fun y hy y' hy' v => heisL_half S T ψ (by rw [Formalism.L2.Theta.cA_cA, hec]) y hy y' hy' v)
    (fun x _ y _ v => heisL_comm S T ψ x y v)
    ⟨R, fun t ht => by
      obtain ⟨r, hr, x, hx, e⟩ := hR t ht
      exact ⟨r, hr, x, hx, e.symm⟩⟩
    hL'K (fun y hy h => hsep y ((isHalf_iff S T).2 hy) h) W
    (fun v hv x _ => GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hv x)
    (fun v hv y _ => GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hv y)
    f hf
    (by
      rintro _ ⟨x, hx, rfl⟩
      exact hUf _ (hL x hx).2 (GlobalTheory.PlaceDatum.infPart_of_half hinf (Witness.up_half p FS FT _)))
    (fun y hy => hUf y (hK y hy).2 (GlobalTheory.PlaceDatum.infPart_of_half hinf' (hK y hy).1))
  refine Submodule.span_le.2 ?_ key
  rintro _ ⟨r, hr, g, hg, hgL, hgY, rfl⟩
  exact GlobalTheory.T.heisenbergOperator_fixedVector_mem_localModelImage D k p Y Y' S T FS FT ψ hψ c hc g hg (fun x hx => hgL _ ⟨x, hx, rfl⟩)
    (fun y hy hyL => hgY y ((isHalf_iff S T).1 hy) (by rintro _ ⟨x, hx, rfl⟩; exact hyL x hx)) r ((isHalf_iff S T).2 hr)

end GlobalTheory.LocMod.SpanModels
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftSpacesRankConstAndLocalisationScalarsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLiftSpaces_rank_const_and_localisation_scalars : ∀ D : D7, Formalism.MainNotions.SumRepresentations.adm8 D → GlobalTheory.NRows.LamUsed D → (∀ i : D.nd.Loc, GlobalTheory.RowCopy.LamPos D (D.nd.mu i) (D.nd.j i)) ∧ ∀ L : SizeData₂ D, Formalism.MainNotions.TwistedPlaces.adm3 L := by
  first | exact @GlobalTheory.RankTw.main | exact GlobalTheory.RankTw.main | (intros; apply GlobalTheory.RankTw.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TransportedLatticeOfLinearAutImageEqMatrixImageStatement
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transportedLattice_of_linearAutImage_eq_matrixImage : ∀ {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} (g : Sp X.E n ≃ₗ[X.E] Sp X.E n) (N : Submodule (𝓞 X.E) (Sp X.E n)), s.lat (Formalism.HermitianLatticesTheory.gmap g N) = Formalism.MainNotions.G.KAat.mvL (seamGL s g) (s.lat N) := by
  first | exact @GlobalTheory.RatLat.lat_gmap | exact GlobalTheory.RatLat.lat_gmap | (intros; apply GlobalTheory.RatLat.lat_gmap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueColumnsGoodChartsMiddleSteps
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU.AtTrue

set_option maxHeartbeats 4000000 in

theorem goodCharts_mid : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch0 : ℕ → Type} {chOf0 : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch0 i} (F : FormsTiedSym (I.rec7 l Z) u Ch0 chOf0) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))), (∀ v, v ∈ Q ↔ I.UnderQ a v) → I.StdF l Z u F → ∀ (i : ℕ) (hi : i ≤ B.R.m), 1 ≤ i → i < B.R.m → ∃ (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a i).Cl → Ch) (Kc : Fam I l Z u a i hi (badQ (I.rec7 l Z) Q) chOf), ReadsOne I l Z u a i hi chOf Kc ∧ ∀ β, FunKilled (Kc β).lev (X.piT u) ∧ ∃ n : ℕ, 0 < n ∧ ∀ κ, (Kc β).lev.chi κ ^ n = 1 := by
  intro B X I hI hP l Z u Ch0 chOf0 F a Q hQ hF i hi h1 h2
  have h2' : i + 1 ≤ B.R.m := h2
  obtain ⟨Ch, hCh, chOf, K, g, hK, hKb⟩ :=
    GlobalTheory.T.tupleChain_middleStage_charts_joined_member I hI hP l Z u a Q i hi (Ch0 i) (chOf0 i) (F.ch i h1 h2') h1 h2 hQ (hF.mid i h1 h2')
  obtain ⟨Kc, hR, hKc⟩ := GlobalTheory.T.charts_rebased_one_off_levelPrime_killed I hI hP l Z u a i hi (badQ (I.rec7 l Z) Q) Ch chOf K hK
    (fun β => (hKb β).2.1)
  exact ⟨Ch, hCh, chOf, Kc, hR, hKc⟩

end GlobalTheory.TwU.AtTrue
end

