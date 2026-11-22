import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0291
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.StabilizerSymmMapsOrthogonal
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0414
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0773
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0013
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Volumes
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.SiegelWeilNarrowOfWide
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSubgroupUnitriangularPairsKeepingDoubleCos
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0415
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0071
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.FamilyGroupSumFactorsWeightAmplitude
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalHaarMeasuresPullbackRealGroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0294
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0037
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0143
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0326
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0408
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0409
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0327

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardRowAutomorphismsEqLatticeStabilizer
section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowsOrbCard

open GlobalTheory.RowsOrb

section Gen
variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

theorem frF_Xa' (F : FlagG S r T) (hT : T ≠ 0) (k : ℕ) : (GlobalTheory.TypeAsm.frF F hT).Xa k = F.Xa k := by
  unfold Formalism.HermitianLatticeCounting.S6.FlagD.Xa FlagG.Xa
  have h : (fun b : Fin r => (GlobalTheory.TypeAsm.frF F hT).e b.castSucc) = F.e := funext fun b => GlobalTheory.TypeAsm.fv_cast F b
  rw [h]

theorem frF_X' (F : FlagG S r T) (hT : T ≠ 0) : (GlobalTheory.TypeAsm.frF F hT).X = F.X := by
  unfold Formalism.HermitianLatticeCounting.S6.FlagD.X
  rw [frF_Xa']
  unfold FlagG.Xa FlagG.X
  congr 1
  ext x; simp

end Gen

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem fixedFrameOfWord_X : (GlobalTheory.TypeAsm.F0 X u).X = (X.Fu u).X := frF_X' _ _

theorem FuX_eq : (X.Fu u).X = Submodule.span D.host.E (Set.range X.eX) := by
  rw [FlagG.X, X.Fu_e]

theorem Wb_le (w : Wb X) : (w : (VS D).V) ∈ perpS (VS D) (X.Fu u).X := by
  intro y hy
  rw [FuX_eq] at hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    exact (w.2 a).1
  | zero => simp
  | add y v _ _ h1 h2 => simp [h1, h2]
  | smul c y _ h => simp [h]

def iotaL : Wb X →ₗ[D.host.E] WbQ D (X.Fu u) :=
  (PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.nX D (X.Fu u)).mkQ ∘ₗ
    Submodule.inclusion (fun v hv => Wb_le X u ⟨v, hv⟩)

theorem iotaL_apply (w : Wb X) :
    iotaL X u w = Submodule.Quotient.mk ⟨(w : (VS D).V), Wb_le X u w⟩ := rfl

theorem iotaL_bij : Function.Bijective (iotaL X u) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro w hw
    rw [LinearMap.mem_ker, iotaL_apply, Submodule.Quotient.mk_eq_zero] at hw
    have hwX : (w : (VS D).V) ∈ Submodule.span D.host.E (Set.range X.eX) := by
      rw [← FuX_eq]; exact hw
    have h1 := Formalism.L2.SG.Pf.pj_X (f := X.fY) X.ee X.ef _ hwX
    rw [Formalism.L2.SG.Pf.pj_perp _ (fun a => w.2 a)] at h1
    exact Subtype.ext h1
  · intro q
    induction q using Submodule.Quotient.induction_on with | H a => ?_
    refine ⟨⟨Formalism.L2.SG.Pf.pj X.eX X.fY (a : (VS D).V), fun b =>
      ⟨Formalism.L2.SG.Pf.hT_e_pj X.ee X.ef _ b, Formalism.L2.SG.Pf.hT_f_pj X.ff X.ef _ b⟩⟩, ?_⟩
    rw [iotaL_apply, PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowMPf.mk_eq_mk]
    show Formalism.L2.SG.Pf.pj X.eX X.fY (a : (VS D).V) - (a : (VS D).V) ∈ (X.Fu u).X
    have h := Formalism.L2.SG.Pf.pj_sub_mem (e := X.eX) (f := X.fY) (a : (VS D).V)
      (fun b => a.2 _ (by rw [FuX_eq]; exact Submodule.subset_span ⟨b, rfl⟩))
    rw [← FuX_eq] at h
    exact h

def iota : Wb X ≃ₗ[D.host.E] WbQ D (X.Fu u) := LinearEquiv.ofBijective (iotaL X u) (iotaL_bij X u)

theorem iota_apply (w : Wb X) : iota X u w = Submodule.Quotient.mk ⟨(w : (VS D).V), Wb_le X u w⟩ := rfl

theorem iota_h (x y : Wb X) : PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.hWb D (X.Fu u) (iota X u x) (iota X u y) = hb X x y := rfl

theorem definiteInclusion_orthogonal_negativeVector : iota X u (zb X u) = PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.zbar D (X.Fu u) := by
  rw [iota_apply, PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.zbar]
  congr 1
  apply Subtype.ext
  exact (X.flagZVector u).symm

theorem iota_mem (Λ : Submodule (𝓞 D.host.E) (VS D).V) (w : Wb X) :
    iota X u w ∈ PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.Mof D (X.Fu u) Λ ↔ w ∈ Lmap X u Λ := by
  rw [PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowMPf.mem_Mof, mem_Lmap, fixedFrameOfWord_X]
  constructor
  · rintro ⟨a, haΛ, hmk⟩
    rw [iota_apply, PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowMPf.mk_eq_mk] at hmk
    refine Submodule.mem_sup.2 ⟨a, haΛ, (w : (VS D).V) - a, ?_, by abel⟩
    have := Submodule.neg_mem _ hmk
    rw [neg_sub] at this
    exact this
  · intro hw
    obtain ⟨l, hl, x, hx, hlx⟩ := Submodule.mem_sup.1 hw
    have hxX : x ∈ (X.Fu u).X := hx
    have hlp : l ∈ perpS (VS D) (X.Fu u).X := by
      have : l = (w : (VS D).V) - x := by rw [← hlx]; abel
      rw [this]
      exact Submodule.sub_mem _ (Wb_le X u w) (PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowMPf.X_le_perp D (X.Fu u) hxX)
    refine ⟨⟨l, hlp⟩, hl, ?_⟩
    rw [iota_apply, PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowMPf.mk_eq_mk]
    have : l - (w : (VS D).V) = -x := by rw [← hlx]; abel
    show l - (w : (VS D).V) ∈ _
    rw [this]
    exact Submodule.neg_mem _ hxX

end GlobalTheory.RowsOrbCard

namespace GlobalTheory.RowsOrbCard

open GlobalTheory.RowsOrb

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

def conj (g : Wb X ≃ₗ[D.host.E] Wb X) : WbQ D (X.Fu u) ≃ₗ[D.host.E] WbQ D (X.Fu u) :=
  (iota X u).symm.trans (g.trans (iota X u))

def unconj (σ : WbQ D (X.Fu u) ≃ₗ[D.host.E] WbQ D (X.Fu u)) : Wb X ≃ₗ[D.host.E] Wb X :=
  (iota X u).trans (σ.trans (iota X u).symm)

theorem conj_iota (g : Wb X ≃ₗ[D.host.E] Wb X) (w : Wb X) : conj X u g (iota X u w) = iota X u (g w) := by
  simp [conj]

theorem conj_unconj (σ : WbQ D (X.Fu u) ≃ₗ[D.host.E] WbQ D (X.Fu u)) : conj X u (unconj X u σ) = σ := by
  ext q; simp [conj, unconj]

theorem unconj_conj (g : Wb X ≃ₗ[D.host.E] Wb X) : unconj X u (conj X u g) = g := by
  ext w; simp [conj, unconj]

theorem conj_isom (g : Wb X ≃ₗ[D.host.E] Wb X) (hg : ∀ x y, hb X (g x) (g y) = hb X x y)
    (x y : WbQ D (X.Fu u)) :
    PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.hWb D (X.Fu u) (conj X u g x) (conj X u g y) =
      PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.hWb D (X.Fu u) x y := by
  have e : ∀ q, conj X u g q = iota X u (g ((iota X u).symm q)) := fun q => rfl
  have e2 : ∀ q, iota X u ((iota X u).symm q) = q := fun q => (iota X u).apply_symm_apply q
  rw [e, e, iota_h, hg, ← iota_h, e2, e2]

theorem gmap_conj (Λ : Submodule (𝓞 D.host.E) (VS D).V) (g : Wb X ≃ₗ[D.host.E] Wb X) :
    Formalism.HermitianLatticesTheory.gmap (conj X u g) (PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.Mof D (X.Fu u) Λ) =
              PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.Mof D (X.Fu u) Λ ↔
      Formalism.HermitianLatticesTheory.gmap g (Lmap X u Λ) = Lmap X u Λ := by
  have key : ∀ w, iota X u w ∈ Formalism.HermitianLatticesTheory.gmap (conj X u g) (PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.Mof D (X.Fu u) Λ) ↔
      w ∈ Formalism.HermitianLatticesTheory.gmap g (Lmap X u Λ) := by
    intro w
    simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨y, hy, h⟩
      refine ⟨(iota X u).symm y, (iota_mem X u Λ _).1 (by simpa using hy), ?_⟩
      apply (iota X u).injective
      rw [← h, ← conj_iota]
      simp
    · rintro ⟨y, hy, h⟩
      refine ⟨iota X u y, (iota_mem X u Λ y).2 hy, ?_⟩
      rw [conj_iota, h]
  constructor
  · intro h
    ext w
    rw [← key, h, iota_mem]
  · intro h
    ext q
    rw [← (iota X u).apply_symm_apply q, key, h, iota_mem]

theorem conj_mem (Λ : Submodule (𝓞 D.host.E) (VS D).V) (g : MulAction.stabilizer (Gz X u) (Lmap X u Λ)) :
    conj X u (((g : Gz X u) : Formalism.HermitianLatticesTheory.isom (hb X)) : Wb X ≃ₗ[D.host.E] Wb X) ∈
      PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.stabZ (PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.hWb D (X.Fu u))
        (PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.zbar D (X.Fu u)) (PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.Mof D (X.Fu u) Λ) := by
  have hz : (((g : Gz X u) : Formalism.HermitianLatticesTheory.isom (hb X)) : Wb X ≃ₗ[D.host.E] Wb X) (zb X u) = zb X u :=
    MulAction.mem_stabilizer_iff.1 (g : Gz X u).2
  have hL : Formalism.HermitianLatticesTheory.gmap (((g : Gz X u) : Formalism.HermitianLatticesTheory.isom (hb X)) : Wb X ≃ₗ[D.host.E] Wb X) (Lmap X u Λ) =
      Lmap X u Λ := MulAction.mem_stabilizer_iff.1 g.2
  have hg : ∀ x y, hb X ((((g : Gz X u) : Formalism.HermitianLatticesTheory.isom (hb X)) : Wb X ≃ₗ[D.host.E] Wb X) x)
      ((((g : Gz X u) : Formalism.HermitianLatticesTheory.isom (hb X)) : Wb X ≃ₗ[D.host.E] Wb X) y) = hb X x y :=
    ((g : Gz X u) : Formalism.HermitianLatticesTheory.isom (hb X)).2
  refine ⟨⟨conj_isom X u _ hg, ?_⟩, (gmap_conj X u Λ _).2 hL⟩
  have e := conj_iota X u (((g : Gz X u) : Formalism.HermitianLatticesTheory.isom (hb X)) : Wb X ≃ₗ[D.host.E] Wb X) (zb X u)
  rw [hz, definiteInclusion_orthogonal_negativeVector] at e
  exact e

theorem unconj_mem (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (σ : PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.stabZ (PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.hWb D (X.Fu u))
        (PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.zbar D (X.Fu u)) (PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.Mof D (X.Fu u) Λ)) :
    ∃ (h1 : unconj X u σ.1 ∈ Formalism.HermitianLatticesTheory.isom (hb X)) (h2 : (⟨unconj X u σ.1, h1⟩ : Formalism.HermitianLatticesTheory.isom (hb X)) ∈ Gz X u),
      (⟨⟨unconj X u σ.1, h1⟩, h2⟩ : Gz X u) ∈ MulAction.stabilizer (Gz X u) (Lmap X u Λ) := by
  obtain ⟨⟨hi, hz⟩, hM⟩ := σ.2
  have h1 : unconj X u σ.1 ∈ Formalism.HermitianLatticesTheory.isom (hb X) := by
    intro x y
    rw [← iota_h, ← iota_h]
    have e : ∀ w, iota X u (unconj X u σ.1 w) = σ.1 (iota X u w) := fun w => by simp [unconj]
    rw [e, e]
    exact hi _ _
  refine ⟨h1, ?_, ?_⟩
  · rw [MulAction.mem_stabilizer_iff]
    show unconj X u σ.1 (zb X u) = zb X u
    apply (iota X u).injective
    simp only [unconj, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, definiteInclusion_orthogonal_negativeVector]
    exact hz
  · rw [MulAction.mem_stabilizer_iff]
    show Formalism.HermitianLatticesTheory.gmap (unconj X u σ.1) (Lmap X u Λ) = Lmap X u Λ
    rw [← gmap_conj, conj_unconj]
    exact hM

theorem card_stab (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    Nat.card (PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.stabZ (PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.hWb D (X.Fu u))
        (PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.zbar D (X.Fu u)) (PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.Mof D (X.Fu u) Λ)) =
      Nat.card (MulAction.stabilizer (Gz X u) (Lmap X u Λ)) := by
  refine (Nat.card_congr
    { toFun := fun g => ⟨conj X u (((g : Gz X u) : Formalism.HermitianLatticesTheory.isom (hb X)) : Wb X ≃ₗ[D.host.E] Wb X), conj_mem X u Λ g⟩
      invFun := fun σ => ⟨⟨⟨unconj X u σ.1, (unconj_mem X u Λ σ).1⟩, (unconj_mem X u Λ σ).2.1⟩,
        (unconj_mem X u Λ σ).2.2⟩
      left_inv := fun g => by
        apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
        exact unconj_conj X u _
      right_inv := fun σ => by
        apply Subtype.ext
        exact conj_unconj X u _ }).symm

end GlobalTheory.RowsOrbCard

namespace GlobalTheory.RowsOrb

theorem card_autLz : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), GlobalTheory.TypeAsm.Std D large₂ →
    ∀ Λ ∈ Y.what₂ u, Nat.card (autLz D (X.Fu u) Λ) =
      Nat.card (MulAction.stabilizer (GlobalTheory.RowsOrb.Gz X u) (GlobalTheory.RowsOrb.Lmap X u Λ)) := by
  intro D large₂ X Y u _ Λ hΛ
  rw [PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.row_weight_formula D u (X.Fu u) Λ ((Y.rowsOK u).1 Λ hΛ)]
  exact GlobalTheory.RowsOrbCard.card_stab X u Λ

end GlobalTheory.RowsOrb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DepthZeroIdentityFiniteTypeOfTypePrimeComponentStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depthZeroIdentity_finiteType_of_typePrimeComponent : ∀ (D : D7) (I : Ident D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (cp : GlobalTheory.GoodTypes.Comp D), IsComp I rep cp → ∀ σ k v (a : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k)))), (∀ y ∈ fixK1 (cp σ k v).ρ, actK (cp σ k v).ρ a y = y) → ∀ s : SplitPlace D.host.E, s.w = D.naut.plGw k v → GlobalTheory.LabPin.SerFix (rep σ) s a := by
  first | exact @GlobalTheory.DepthZeroSer.serFix_of_comp | exact GlobalTheory.DepthZeroSer.serFix_of_comp | (intros; apply GlobalTheory.DepthZeroSer.serFix_of_comp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFrameStabilizerHaarNormalisedFibreMeasureStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frameStabilizerHaar_normalised_fibreMeasure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → Formalism.MainNotions.UnusedSlot34.SWa1 F E σ n J → Formalism.L2.SG.Pf.NcWeil.StabilizerFirstChernCompatibility F E σ n J → ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → Formalism.L2.SG.LocVol.IsStdChar ψ → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → 2 * (r + 1) < n → ∀ μG : Measure (HA (Fv F v) σ J), μG.IsHaarMeasure → ∃ μS : Measure (Ssub (Fv F v) σ J P), μS.IsHaarMeasure ∧ Formalism.L2.SG.LocVol.LocTieW σ J ψ v P μG μS := by
  first | exact @GlobalTheory.LocalStabiliserTie.exists_tied_haar | exact GlobalTheory.LocalStabiliserTie.exists_tied_haar | (intros; apply GlobalTheory.LocalStabiliserTie.exists_tied_haar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSubgroupUnitriangularPairsKeepingDoubleCosStatement
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_subgroup_unitriangular_pairs_keeping_doubleCoset : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (t : TauC Y u u'), ∃ B : Subgroup (GV D × GV D), (∀ b, b ∈ B ↔ b.1 ∈ Aut0 (lf D (X.Fu u)) t.lam ∧ b.2 ∈ Aut0 (lf D (X.Fu u')) t.lam' ∧ KeyEq (lf D (X.Fu u)) (lf D (X.Fu u')) t.lam t.lin (b.1 * t.lin * b.2⁻¹)) ∧ (∀ n ∈ NLam t.lam (lf D (X.Fu u)), ∀ n' ∈ NLam t.lam' (lf D (X.Fu u')), (n, n') ∈ B) ∧ ∀ a₁ ∈ Aut0 (lf D (X.Fu u)) t.lam, ∀ a₂ ∈ Aut0 (lf D (X.Fu u)) t.lam, ∀ a₁' ∈ Aut0 (lf D (X.Fu u')) t.lam', ∀ a₂' ∈ Aut0 (lf D (X.Fu u')) t.lam', (KeyEq (lf D (X.Fu u)) (lf D (X.Fu u')) t.lam (a₁ * t.lin * a₁'⁻¹) (a₂ * t.lin * a₂'⁻¹) ↔ (a₁⁻¹ * a₂, a₁'⁻¹ * a₂') ∈ B) := by
  first | exact @GlobalTheory.KeyGroup.keyStab_subgroup | exact GlobalTheory.KeyGroup.keyStab_subgroup | (intros; apply GlobalTheory.KeyGroup.keyStab_subgroup <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagTermInvariantsConstOnRationalDoubleCosetStatement
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagTerm_invariants_const_on_rationalDoubleCoset : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → ∀ (t₀ t : TauC Y u u') (n m : ((VS D).V ≃ₗ[D.host.E] (VS D).V)), t₀.relevant → t₀.G ≠ 0 → n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m → t.relevant ∧ t.G = t₀.G ∧ Formalism.L2.SG.PairVal.ptOf t.toTerm = Formalism.L2.SG.PairVal.ptOf t₀.toTerm ∧ nmlOf Y u u' t = nmlOf Y u u' t₀ ∧ ((Y.tO u u').rowOf t = (Y.tO u u').rowOf t₀ → (Y.tO u u').s0 t₀ t = 1 ∧ (Y.tO u u').scal t₀ t) := by
  first | exact @GlobalTheory.HL.CosetConst.coset_const | exact GlobalTheory.HL.CosetConst.coset_const | (intros; apply GlobalTheory.HL.CosetConst.coset_const <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenericRowFamilyStepOfLeavesStatement
section
open GlobalTheory.SnFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericRow_familyStep_of_leaves : (∀ D : Formalism.BasicNotions.D7, 4 * D.R.rS + 7 ≤ D.R.k → Formalism.L2.SG.FamDefs.LocalLowerBoundAllCosets D.R.k D.R.rS 9) → Formalism.L2.SG.FamDefs.HTie → FamGen → FamilyWeightSumUnfoldingIdentity → WeightsFam → FamilyGroupSumFactorsWeightAmplitude → ExistFam → Formalism.L2.SG.Pf.MainEqFam.StepFamG := by
  first | exact @GlobalTheory.SnFam.Gen.stepFamG_of_fam | exact GlobalTheory.SnFam.Gen.stepFamG_of_fam | (intros; apply GlobalTheory.SnFam.Gen.stepFamG_of_fam <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenericScalarClassTermsFormFamilyStatement
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.SnFam
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericScalarClassTerms_formFamily : GlobalTheory.SnFam.FamGen := by
  first | exact @GlobalTheory.SnFamGenAll.famGen | exact GlobalTheory.SnFamGenAll.famGen | (intros; apply GlobalTheory.SnFamGenAll.famGen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFundImage
section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.CovFund

variable {D : D7} {X : HidaSetting D} (C : Choice X 1)

def reix (X : HidaSetting D) : (∀ τ : D.what₂.Tau, Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) ≃ᵐ X.B.I.Ginf :=
  MeasurableEquiv.piCongrLeft (fun v => Formalism.REAL.UJ (X.B.I.ε v)) X.pl.symm

theorem reix_apply (p : ∀ τ : D.what₂.Tau, Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) (τ : D.what₂.Tau) :
    reix X p (vOf X τ) = p τ := by
  exact MeasurableEquiv.piCongrLeft_apply_apply (β := fun v => Formalism.REAL.UJ (X.B.I.ε v)) X.pl.symm p τ

theorem reix_symm (x : X.B.I.Ginf) (τ : D.what₂.Tau) : (reix X).symm x τ = x (vOf X τ) := by
  conv_rhs => rw [← (reix X).apply_symm_apply x]
  exact (reix_apply _ τ).symm

theorem trI_apply (x : X.B.I.Ginf) (τ : D.what₂.Tau) : trI C x τ = GlobalTheory.PullbackComparison.eM C τ (x (vOf X τ)) := rfl

theorem trI_emb : MeasurableEmbedding (trI C) := by
  choose g hg hgf using fun τ : D.what₂.Tau =>
    (GlobalTheory.PullbackComparison.eM_emb C τ).exists_measurable_extend (g := id) measurable_id (fun _ => ⟨1⟩)
  refine MeasurableEmbedding.of_measurable_inverse
    (g := fun m => reix X (fun τ => g τ (m τ))) ?_ ?_ ?_ ?_
  · exact measurable_pi_lambda _ fun τ =>
      (GlobalTheory.PullbackComparison.eM_emb C τ).measurable.comp (measurable_pi_apply (vOf X τ))
  · have hR : Set.range (trI C) = Set.univ.pi fun τ => Set.range (GlobalTheory.PullbackComparison.eM C τ) := by
      ext m
      constructor
      · rintro ⟨x, rfl⟩ τ _
        exact ⟨x (vOf X τ), (trI_apply C x τ).symm⟩
      · intro hm
        choose a ha using fun τ => hm τ (Set.mem_univ τ)
        refine ⟨reix X a, funext fun τ => ?_⟩
        rw [trI_apply, reix_apply, ha]
    rw [hR]
    exact MeasurableSet.univ_pi fun τ => (GlobalTheory.PullbackComparison.eM_emb C τ).measurableSet_range
  · exact (reix X).measurable.comp
      (measurable_pi_lambda _ fun τ => (hg τ).comp (measurable_pi_apply τ))
  · intro x
    have h1 : (fun τ => g τ (trI C x τ)) = (reix X).symm x := by
      funext τ
      rw [trI_apply, reix_symm]
      exact congrFun (hgf τ) _
    simp only [h1, MeasurableEquiv.apply_symm_apply]

theorem trI_mul (q y : X.B.I.Ginf) : GlobalTheory.DegVol.mulP (trI C q) (trI C y) = trI C (q * y) := by
  funext τ
  have hv : (q * y) (vOf X τ) = q (vOf X τ) * y (vOf X τ) := rfl
  rw [trI_apply C (q * y), hv, GlobalTheory.PullbackComparison.eM_mul]
  rfl

theorem exists_pre {Y : Full X} {u : D.what₂.Word} (t : GT Y u) {x : D.what₂.Tau → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS}
    (hx : x ∈ GlobalTheory.DegVol.RP D.R.k D.R.rS (fun τ => (gamT C t τ)⁻¹)) :
    ∃ y ∈ Formalism.L2.SG.TermOp.Vanish.Rset t, trI C y = x := by
  have hr : ∀ τ, x τ ∈ Set.range (GlobalTheory.PullbackComparison.eM C τ) := fun τ =>
    GlobalTheory.PullbackComparison.uh_range C τ (hx τ).1.1
  choose a ha using hr
  refine ⟨reix X a, ?_, funext fun τ => ?_⟩
  · rw [GlobalTheory.PullbackComparison.rset_iff C t]
    intro τ
    rw [reix_apply, ha]
    exact hx τ
  · rw [trI_apply, reix_apply, ha]

theorem isFund_image : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (C : Choice X 1) (t : GT Y u) (K : Set X.B.I.Ginf), FundR t K → GlobalTheory.DegVol.IsFund (trI C '' Formalism.L2.SG.TermOp.ROinf t) (GlobalTheory.DegVol.RP D.R.k D.R.rS (fun τ => (gamT C t τ)⁻¹)) (trI C '' K) := by
  intro D X Y u C t K hK
  refine ⟨(trI_emb C).measurableSet_image.2 hK.1, ?_⟩
  intro x hx
  obtain ⟨y, hy, rfl⟩ := exists_pre C t hx
  obtain ⟨q, ⟨hq, hqK⟩, huniq⟩ := hK.2 y hy
  refine ⟨trI C q, ⟨⟨q, hq, rfl⟩, ?_⟩, ?_⟩
  · rw [trI_mul]
    exact ⟨q * y, hqK, rfl⟩
  · rintro m ⟨⟨q', hq', rfl⟩, hm⟩
    rw [trI_mul] at hm
    obtain ⟨z, hz, hzq⟩ := hm
    have hzq' : z = q' * y := (trI_emb C).injective hzq
    rw [huniq q' ⟨hq', by rw [← hzq']; exact hz⟩]

end GlobalTheory.CovFund
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalHaarMeasuresPullbackRealGroupStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localHaarMeasures_pullback_realGroup : GlobalTheory.TypeAsm.PullC := by
  first | exact @GlobalTheory.PullbackComparison.pullC_holds | exact GlobalTheory.PullbackComparison.pullC_holds | (intros; apply GlobalTheory.PullbackComparison.pullC_holds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalIdentificationEqOfGlobalLatticesEqStatement
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_identification_eq_of_global_lattices_eq : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (Tn T'n : ℕ) (F : LFlag (VS D) D.R.rS (Tn : D.host.E)) (F' : LFlag (VS D) D.R.rS (T'n : D.host.E)), Based Z FP Tn T'n F F' → ∀ Λ₁ Λ₂ : LV D, Submodule.IsLattice D.host.E Λ₁ → Submodule.IsLattice D.host.E Λ₂ → Lsub Λ₁ F = Lsub Λ₂ F → Lsub Λ₁ F' = Lsub Λ₂ F' → (gdat F F' Λ₁).2.2 = (gdat F F' Λ₂).2.2 → ∀ (p : PlF D) (g : Loc.SplitG (Z.M p).L), (Z.M p).split = some g → (locH Z p).iotaGraph g ⟨lattice₂ D Z.M p Λ₁, (FP p).A.f, (FP p).B.f, (FP p).A.T, (FP p).B.T⟩ = (locH Z p).iotaGraph g ⟨lattice₂ D Z.M p Λ₂, (FP p).A.f, (FP p).B.f, (FP p).A.T, (FP p).B.T⟩ := by
  first | exact @GlobalTheory.Unfold.IotaLocal.iotaGraph_eq_of_gdat | exact GlobalTheory.Unfold.IotaLocal.iotaGraph_eq_of_gdat | (intros; apply GlobalTheory.Unfold.IotaLocal.iotaGraph_eq_of_gdat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassGenusLocalDataProductLocalWeights
section
noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HL

namespace GlobalTheory.Unfold

theorem mass_genus_local_weights : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ d0 : Dat Z FP, (∀ p, ∃ τ, LocNG.IsTermOver (FP p) (d0 p) τ) → (∃ Λ₀ : LV D, Submodule.IsLattice D.host.E Λ₀ ∧ {p | ¬ ∃ τ, LocNG.IsTermOver (FP p) (d0 p) τ ∧ τ.abelian₂ = lattice₂ D Z.M p Λ₀}.Finite) → ∃ V1 : ℝ, 0 < V1 ∧ ∀ d : Dat Z FP, (∀ p, ∃ τ, LocNG.IsTermOver (FP p) (d p) τ) → {p | d p ≠ d0 p}.Finite → massA F F' d = ENNReal.ofReal (V1 * ∏ᶠ p, LocNG.Datum.wt (d0 p) (d p)) := by
  intro D X Y u u' F F' w hw hG Z FP hB hR d0 hd0 hΛ
  obtain ⟨φ, hφi, hφE⟩ := GlobalTheory.T.frameFixingIsometries_embed_prod_localUnitary D X Y u u' F F' w hw hG Z FP hB hR
  obtain ⟨Λ₀, hLO⟩ := GlobalTheory.T.exists_globalLattice_over_localInnerData D Z FP d0 hd0 hΛ
  have hrk : ∀ p : PlF D, Module.finrank (D.s.atP p).Ep (Vp D p) = D.R.k + 2 * D.R.rS + 1 := by
    intro p
    have hm : D.R.m = 2 * D.R.rS + 2 := by
      have := D.R.two_le_m; obtain ⟨a, ha⟩ := D.R.m_even; unfold Ranks.rS; omega
    rw [finrank_Vp]; unfold Ranks.r; omega
  have hact : ∀ p : PlF D, ∃ act : MulAction ↥(FP p).UW0 (LocNG.Datum (FP p)),
      (∀ (g : ↥(FP p).UW0) d d', LocNG.Datum.Moves g.1 d d' ↔ act.smul g d = d') ∧
      ∀ d (g : ↥(FP p).UW0), g.1 ∈ LocNG.Datum.Stab d ↔ act.smul g d = d :=
    fun p => GlobalTheory.T.exists_complementUnitary_mulAction_localInnerDatum (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS D.R.k (FP p) (hrk p) (hR p)
  choose act hMv hSt using hact
  letI : ∀ p, MulAction ↥(FP p).UW0 (LocNG.Datum (FP p)) := act
  have hMv' : ∀ p (g : ↥(FP p).UW0) (d d' : LocNG.Datum (FP p)), LocNG.Datum.Moves g.1 d d' ↔ g • d = d' := hMv
  have hSt' : ∀ p (d : LocNG.Datum (FP p)) (g : ↥(FP p).UW0), g.1 ∈ LocNG.Datum.Stab d ↔ g • d = d := hSt
  obtain ⟨hc0, hfin, hdd⟩ := GlobalTheory.T.localLatticeStabilisers_commensurable_almostEverywhere D X Y u u' F F' w hw hG Z FP hB hR hMv' hSt' Λ₀ d0 hLO
  have hlat : Submodule.IsLattice D.host.E Λ₀ := hLO.1
  obtain ⟨V1, hV1, hmain⟩ := GlobalTheory.T.mass_genus_restricted_product (fun p => ↥(FP p).UW0) (fun p => LocNG.Datum (FP p))
    (fun p => (LocNG.Aut (lattice₂ D Z.M p Λ₀)).comap (FP p).UW0.subtype) ↥(FlagPairStabilizer F F') φ hφi
    (GlobalTheory.T.frameFixingIsometry_ext_preserves_completions_ae D X Y u u' F F' w hw hG Z FP hB hR φ hφE Λ₀ hlat)
    (GlobalTheory.T.finite_doubleCosets_rational_localLatticeStabilizers D X Y u u' F F' w hw hG Z FP hB hR φ hφE Λ₀ hlat)
    (GlobalTheory.T.finite_rationalIsometries_fixing_frames_conjStabilizer D X Y u u' F F' w hw hG Z FP hB hR φ hφE Λ₀ hlat) d0 hc0 hfin
  refine ⟨V1, hV1, fun d hd hfd => ?_⟩
  have h3 := hdd d hd
  rw [GlobalTheory.T.genusMass_eq_sum_over_rationalGroup_orbits D X Y u u' F F' w hw hG Z FP hB hR φ hφE hφi hMv' d]
  have hm2 := hmain d (fun p => ⟨(h3 p).1, (h3 p).2.1⟩) hfd
  have e : (∏ᶠ p, LocNG.Datum.wt (d0 p) (d p)) = ∏ᶠ p, invVol (MulAction.stabilizer ↥(FP p).UW0 (d0 p)) (MulAction.stabilizer ↥(FP p).UW0 (d p)) := finprod_congr fun p => ((h3 p).2.2).symm
  refine hm2.trans ?_
  rw [e]

end GlobalTheory.Unfold
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermRowDoubleCosetEqIffIsometriesStatement
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.term_row_double_coset_eq_iff_isometries : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ t t' : TauC Y u u', key t = key t' ↔ t.lam = t'.lam ∧ t.lam' = t'.lam' ∧ KeyEq (lf D (X.Fu u)) (lf D (X.Fu u')) t.lam t.lin t'.lin := by
  first | exact @GlobalTheory.Unfold.KeyIff.key_eq_iff | exact GlobalTheory.Unfold.KeyIff.key_eq_iff | (intros; apply GlobalTheory.Unfold.KeyIff.key_eq_iff <;> assumption)
end

