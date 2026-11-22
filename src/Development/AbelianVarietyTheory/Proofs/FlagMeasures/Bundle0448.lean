import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0017
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0233
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RedBasicsPf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodAtReductionConjugatedUnitaryElement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0223
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0131
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0401
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1216
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0260
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteCosetsHeckeSetAtSplitPlaceOutsideLevel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.DataInst
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FormulaExplicitAtOfEta
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0052
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0425
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0048
import Formalism.HermitianCurvature.HeisenbergConjugationMeasurePreserving
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLitG
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0014
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdCons
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.OmegaDensityUnique
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.Bundle0008
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.Bundle0008
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Bundle0005
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0446
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowLatticesMeanEqGenusMean
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsDegreeOnePrimeFrameReducedMatrices
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
open scoped Matrix

namespace GlobalTheory.RowLev

theorem exists_coords_of_frame {A κ : Type} [CommRing A] [CommRing κ] {n : ℕ} (R : Subring A)
    (L : Submodule R (Fin n → A)) (β : GL (Fin n) A)
    (hβ : ∀ y, y ∈ L ↔ ∀ i, ((β⁻¹ : GL (Fin n) A).1 *ᵥ y) i ∈ R) (r : R →+* κ) (hr : Function.Surjective r) :
    ∃ c : L →ₛₗ[r] (Fin n → κ), Function.Surjective c ∧
      (∀ y : L, c y = 0 ↔ (y : Fin n → A) ∈ RingHom.ker r • L) ∧
      ∀ (X : GL (Fin n) A) (M : Matrix (Fin n) (Fin n) κ),
        (∀ y ∈ L, X.1 *ᵥ y ∈ L) →
        (∀ i j (h : (β⁻¹ * X * β : GL (Fin n) A).1 i j ∈ R), r ⟨_, h⟩ = M i j) →
        ∀ (y : L) (h : X.1 *ᵥ (y : Fin n → A) ∈ L), c ⟨_, h⟩ = M *ᵥ c y := by
  classical
  set B : Matrix (Fin n) (Fin n) A := (β⁻¹ : GL (Fin n) A).1 with hB
  have hBβ : B * β.1 = 1 := by rw [hB]; exact Units.inv_mul β
  have hβB : β.1 * B = 1 := by rw [hB]; exact Units.mul_inv β
  have hmem : ∀ y : L, ∀ i, (B *ᵥ (y : Fin n → A)) i ∈ R := fun y => (hβ y).1 y.2

  have hcol : ∀ j, (fun k => β.1 k j) ∈ L := by
    intro j
    refine (hβ _).2 fun i => ?_
    have e : (B *ᵥ fun k => β.1 k j) i = (B * β.1) i j := by
      simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
    change (B *ᵥ fun k => β.1 k j) i ∈ R
    rw [e, hBβ, Matrix.one_apply]
    split_ifs
    · exact R.one_mem
    · exact R.zero_mem

  have hexp : ∀ v : Fin n → A, v = ∑ j, (B *ᵥ v) j • (fun k => β.1 k j) := by
    intro v
    have h1 : β.1 *ᵥ (B *ᵥ v) = v := by rw [Matrix.mulVec_mulVec, hβB, Matrix.one_mulVec]
    conv_lhs => rw [← h1]
    funext k
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  let c : L →ₛₗ[r] (Fin n → κ) :=
    { toFun := fun y i => r ⟨(B *ᵥ (y : Fin n → A)) i, hmem y i⟩
      map_add' := by
        intro y z
        funext i
        have e : (⟨(B *ᵥ ((y + z : L) : Fin n → A)) i, hmem (y + z) i⟩ : R) =
            ⟨_, hmem y i⟩ + ⟨_, hmem z i⟩ := Subtype.ext (by simp [Matrix.mulVec_add])
        simp only [Pi.add_apply]
        rw [e, map_add]
      map_smul' := by
        intro a y
        funext i
        have e : (⟨(B *ᵥ ((a • y : L) : Fin n → A)) i, hmem (a • y) i⟩ : R) = a * ⟨_, hmem y i⟩ := by
          apply Subtype.ext
          change (B *ᵥ ((a : A) • (y : Fin n → A))) i = (a : A) * (B *ᵥ (y : Fin n → A)) i
          rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [e, map_mul] }
  have hc : ∀ (y : L) i, c y i = r ⟨(B *ᵥ (y : Fin n → A)) i, hmem y i⟩ := fun _ _ => rfl
  refine ⟨c, ?_, ?_, ?_⟩
  ·
    intro v
    choose x hx using fun i => hr (v i)
    set y0 : Fin n → A := β.1 *ᵥ fun i => (x i : A) with hy0
    have hc0 : ∀ i, (B *ᵥ y0) i = x i := by
      intro i
      rw [hy0, Matrix.mulVec_mulVec, hBβ, Matrix.one_mulVec]
    have hm : y0 ∈ L := (hβ y0).2 fun i => by rw [hc0 i]; exact (x i).2
    refine ⟨⟨y0, hm⟩, ?_⟩
    funext i
    rw [hc, ← hx i]
    congr 1
    exact Subtype.ext (hc0 i)
  · intro y
    constructor
    · intro hy
      have hk : ∀ j, (⟨_, hmem y j⟩ : R) ∈ RingHom.ker r := by
        intro j
        rw [RingHom.mem_ker, ← hc]
        exact congrFun hy j
      have e : (y : Fin n → A) = ∑ j, (⟨_, hmem y j⟩ : R) • (fun k => β.1 k j) := hexp _
      rw [e]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem_smul (hk j) (hcol j)
    · intro hy
      have key : ∀ i, ∃ h : (B *ᵥ (y : Fin n → A)) i ∈ R, r ⟨_, h⟩ = 0 := by
        refine Submodule.smul_induction_on
          (p := fun z : Fin n → A => ∀ i, ∃ h : (B *ᵥ z) i ∈ R, r ⟨_, h⟩ = 0) hy ?_ ?_
        · intro a ha m hm i
          have e : (B *ᵥ (a • m)) i = (a : A) * (B *ᵥ m) i := by
            change (B *ᵥ ((a : A) • m)) i = _
            rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
          have hm' : (B *ᵥ m) i ∈ R := (hβ m).1 hm i
          refine ⟨e ▸ R.mul_mem a.2 hm', ?_⟩
          have e2 : (⟨(B *ᵥ (a • m)) i, e ▸ R.mul_mem a.2 hm'⟩ : R) = a * ⟨_, hm'⟩ := Subtype.ext e
          rw [e2, map_mul, (RingHom.mem_ker).1 ha, zero_mul]
        · intro u v hu hv i
          obtain ⟨h1, e1⟩ := hu i
          obtain ⟨h2, e2⟩ := hv i
          have e : (B *ᵥ (u + v)) i = (B *ᵥ u) i + (B *ᵥ v) i := by
            rw [Matrix.mulVec_add, Pi.add_apply]
          refine ⟨e ▸ R.add_mem h1 h2, ?_⟩
          have e3 : (⟨(B *ᵥ (u + v)) i, e ▸ R.add_mem h1 h2⟩ : R) = ⟨_, h1⟩ + ⟨_, h2⟩ := Subtype.ext e
          rw [e3, map_add, e1, e2, add_zero]
      funext i
      obtain ⟨_, h⟩ := key i
      rw [hc]
      exact h
  · intro X M hXL hM y h
    have hP : ∀ i j, (β⁻¹ * X * β : GL (Fin n) A).1 i j ∈ R := by
      intro i j
      have hXc : X.1 *ᵥ (fun k => β.1 k j) ∈ L := hXL _ (hcol j)
      have e : (β⁻¹ * X * β : GL (Fin n) A).1 i j = (B *ᵥ (X.1 *ᵥ fun k => β.1 k j)) i := by
        rw [Units.val_mul, Units.val_mul, ← hB, Matrix.mulVec_mulVec]
        simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
      rw [e]
      exact (hβ _).1 hXc i
    have hPv : B *ᵥ (X.1 *ᵥ (y : Fin n → A)) =
        (β⁻¹ * X * β : GL (Fin n) A).1 *ᵥ (B *ᵥ (y : Fin n → A)) := by
      rw [Units.val_mul, Units.val_mul, ← hB, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        Matrix.mul_assoc (B * X.1), hβB, Matrix.mul_one]
    funext i
    have e : (⟨(B *ᵥ (X.1 *ᵥ (y : Fin n → A))) i, hmem ⟨_, h⟩ i⟩ : R) =
        ∑ j, (⟨_, hP i j⟩ : R) * ⟨_, hmem y j⟩ := by
      apply Subtype.ext
      change (B *ᵥ (X.1 *ᵥ (y : Fin n → A))) i = _
      rw [hPv]
      simp [Matrix.mulVec, dotProduct]
    rw [hc]
    change r ⟨(B *ᵥ (X.1 *ᵥ (y : Fin n → A))) i, hmem ⟨_, h⟩ i⟩ = _
    rw [e, map_sum]
    simp only [map_mul, hM, Matrix.mulVec, dotProduct, hc]

private theorem hatL_eq_Lf' (I : Formalism.MainNotions.S.AutInst) : Formalism.L2.Herm.hatL (F := I.F) I.L = I.Lf := by
  unfold Formalism.L2.Herm.hatL Formalism.UG.latS Formalism.MainNotions.S.AutInst.Lf Formalism.MainNotions.S.lamAf
  rw [Set.image_eq_range]
  rfl

theorem exists_plFrame_of_isFrame : ∀ (I : Formalism.MainNotions.S.AutInst) (β₀ : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)), Formalism.L2.DIV.IsFrame β₀ I.L → ∀ (N p : ℕ) (hN : I.n = N) (w : IsDedekindDomain.HeightOneSpectrum (𝓞 I.E)), p.Prime → Nat.card (𝓞 I.E ⧸ w.asIdeal) = p → ∃ fr : GlobalTheory.RowLev.PlFrame I N p w, ∀ k ∈ I.Kset, ∀ M : Matrix (Fin N) (Fin N) (ZMod p), (∀ (i j : Fin N) (hij : ((β₀⁻¹ * (k : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) * β₀ : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) (Fin.cast hN.symm i) (Fin.cast hN.symm j) ∈ Formalism.L2.Herm.intAf I.F I.E), Formalism.L2.DIV.resS I.F w ⟨_, hij⟩ = ((M i j).val : Formalism.L2.DIV.kP w)) → fr.ActsAs k M := by
  intro I β₀ hF N p hN w hp hcard
  subst hN
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hL : ∀ y, y ∈ I.Lf ↔
      ∀ i, ((β₀⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)).1 *ᵥ y) i ∈ Formalism.MainNotions.S.IntAf I.F I.E := by
    intro y
    rw [← hatL_eq_Lf' I]
    exact hF y

  have : Finite (Formalism.L2.DIV.kP w) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.ne_zero)
  let : Fintype (Formalism.L2.DIV.kP w) := Fintype.ofFinite _
  have hcard' : Fintype.card (Formalism.L2.DIV.kP w) = p := by rw [Fintype.card_eq_nat_card]; exact hcard
  have : CharP (Formalism.L2.DIV.kP w) p := charP_of_card_eq_prime hcard'
  let e : ZMod p ≃+* Formalism.L2.DIV.kP w := ZMod.ringEquiv (Formalism.L2.DIV.kP w) hcard'
  let r : Formalism.MainNotions.S.IntAf I.F I.E →+* ZMod p :=
    (e.symm : Formalism.L2.DIV.kP w →+* ZMod p).comp (Formalism.L2.DIV.resS I.F w)
  have hr : ∀ s, r s = e.symm (Formalism.L2.DIV.resS I.F w s) := fun _ => rfl
  have hres : ∀ a : 𝓞 I.E, r (Formalism.L2.DIV.oToS I.F I.E a) = 0 ↔ a ∈ w.asIdeal := by
    intro a
    rw [hr, Formalism.L2.DIV.resS_oToS, map_eq_zero_iff _ e.symm.injective, Ideal.Quotient.eq_zero_iff_mem]
  have hrs : Function.Surjective r := by
    intro q
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (I := w.asIdeal) (e q)
    refine ⟨Formalism.L2.DIV.oToS I.F I.E a, ?_⟩
    rw [hr, Formalism.L2.DIV.resS_oToS, ha, RingEquiv.symm_apply_apply]
  obtain ⟨c, hcs, hck, hca⟩ := exists_coords_of_frame (Formalism.MainNotions.S.IntAf I.F I.E) I.Lf β₀ hL r hrs
  have hker : RingHom.ker r = extId I w.asIdeal := by
    refine Inhab.ker_eq_extId hp.ne_zero r fun a => ?_
    have e1 : Inhab.psi I.F I.E a = Formalism.L2.DIV.oToS I.F I.E a := Subtype.ext rfl
    rw [e1]
    exact hres a
  refine ⟨{ r := r, r_ker := fun a h => ?_, c := c, c_surj := hcs, c_ker := fun y => ?_ }, ?_⟩
  · have e1 : (⟨_, h⟩ : Formalism.MainNotions.S.IntAf I.F I.E) = Formalism.L2.DIV.oToS I.F I.E a := Subtype.ext rfl
    rw [e1]
    exact hres a
  · rw [hck y, hker]
  · intro k hk M hM y h
    refine hca (k : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) M (fun y hy => Inhab.mulVec_mem hk hy)
      (fun i j hij => ?_) y h
    have h1 : Formalism.L2.DIV.resS I.F w ⟨_, hij⟩ = ((M i j).val : Formalism.L2.DIV.kP w) := hM i j hij
    rw [hr, h1, map_natCast, ZMod.natCast_zmod_val]

end GlobalTheory.RowLev
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GluedLatticeWeightedCountLeExplicit
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
open ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.GlueCount

def locSpOf {D : D7} (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (hA : ∀ p, Agree δ M p) : Formalism.L2.SG.CntLocal.LocSp D M where
  V := Vp D
  H p := locHerm M p (hA p).2.2.1
  rank := finrank_Vp
  bc := baseChange₂ D
  bc_smul := baseChange_smul₂
  bc_span := span_baseChange_eq_top
  bc_form p x y := baseChangeAt_form M p (hA p).2.2.1 x y

theorem exists_unif_at {D : D7} (p : PlF D) : ∃ ϖ : 𝒪[(D.s.atP p).Fp], Irreducible ϖ := by
  haveI := (D.s.atP p).lf
  exact IsDiscreteValuationRing.exists_irreducible _

theorem exists_unifs (D : D7) : ∃ ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp], ∀ p, Irreducible (ϖ p) :=
  ⟨fun p => (exists_unif_at p).choose, fun p => (exists_unif_at p).choose_spec⟩

theorem one_mem_stabFix {D : D7} (U : Submodule D.host.E (VS D).V) (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) ∈ Formalism.L2.SG.Pf.Cnt.stabFix (VS D).hT U Λ := by
  refine ⟨(Formalism.L2.SG.Pf.Cnt.isomFix (VS D).hT U).one_mem, ?_⟩
  ext x
  simp [Formalism.HermitianLatticesTheory.gmap]

section Reps
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.Asm Formalism.L2.SG.CntLocal Module

theorem exists_glueReps (D : D7) (u u' : D.what₂.Word) (hT : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (gS D) ^ 2])
    (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (hR : IsRowReps D F0 what₂)
    (G' : LFlag (VS D) D.R.rS (Tn u')) (hz : G'.zt = G'.fl.z) (hP : Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (Tn u) (Tn u') (ZhatL (lf D F0) G'))) :
    ∃ s, IsGlueReps (VS D).hT (UPair D F0 G') (MMof D F0 G') s := by
  haveI : Fact HermRepUnram := ⟨GlobalTheory.BinaryRep.represents_totallyPositive⟩
  obtain ⟨hLat, -⟩ := mmChar_of local_unimodular_holds D u u' hT F0 what₂ hR _ G' hz rfl hP
  by_cases hI : Formalism.HermitianLatticesTheory.IsIntegralLat (VS D).hT (MMof D F0 G')
  · obtain ⟨hK, hF, hN⟩ := field_dictionary_holds D
    obtain ⟨hC, hPD, hUr, hWr⟩ := perpendicular_definition_holds D u u' hT F0 what₂ hR _ G' hz rfl hP
    have hk : D.R.m + 3 ≤ D.R.k := D.R.m_add_three_le_k
    have hcJ : ∀ 𝔭 : Ideal (𝓞 D.host.F), 𝔭.IsMaximal →
        cJ (VS D).hT (UPair D F0 G') (MMof D F0 G') 𝔭 < finrank D.host.E (orthK (VS D).hT (UPair D F0 G')) := by
      intro 𝔭 _
      have := cJ_le (VS D).hT (UPair D F0 G') (MMof D F0 G') 𝔭
      rw [hWr]
      omega
    have hne := glueExists_holds D.host.E D.host.F (VS D).V hK hF (VS D).hT (VS D).herm hN (UPair D F0 G') hC hPD
      ⟨(VS D).L0, (VS D).standardTuple_isLattice, (VS D).baseLattice_isUnimodular⟩ (MMof D F0 G') hLat hI hcJ
    have hMC : MassConst D.host.E D.host.F (finrank D.host.E (orthK (VS D).hT (UPair D F0 G')))
        (cMass D.host.E D.host.F (D.R.k - 1)) := by
      rw [hWr]
      exact (cMass_spec hK hF (D.R.k - 1) (by omega)).2
    obtain ⟨s, hs1, hs2, hs3, -⟩ := gluing_mass_holds D.host.E D.host.F (VS D).V hK hF (VS D).hT (VS D).herm hN
      (UPair D F0 G') hC hPD (MMof D F0 G') hLat hI hne _ hMC
    exact ⟨s, hs1, hs2, hs3⟩
  · exact ⟨∅, isGlueReps_empty (glueSet_eq_empty (U := UPair D F0 G') hI)⟩

end Reps

theorem glueSum_le : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.L2.SG.Pf.LocCP.LocTied D → 2 * D.R.rS + 2 + D.R.f + 5 ≤ D.R.k → (D.mem u).A.T ≡ (D.mem u').A.T [MOD (gS D) ^ 2] → ∀ G' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E), G'.zt = G'.fl.z → TotPos (Gval (lf D (X.Fu u)) G') → ∃ s : Finset (LV D), Glue (lf D (X.Fu u)) G' s ∧ (s.Nonempty → (∃ Λ, IsRowLat D (X.Fu u) Λ ∧ G' ∈ Formalism.L2.SG.CntLocal.EZ ((Tu D u' : ℕ) : D.host.E) (X.Fu u) Λ (ZhatL (lf D (X.Fu u)) G')) ∧ glueSum (lf D (X.Fu u)) G' s ≤ 2 * (Formalism.L2.SG.Pf.Cnt.cExpl D (X.Fu u) (Y.what₂ u) * Formalism.MainNotions.S.Cnt.massRows D (X.Fu u) (Y.what₂ u) * ∏' p, Formalism.L2.SG.DataInst.alpD u u' p) * Formalism.L2.SG.CntLocal.sqrtAbsNormOfScaledGram ((Tu D u : ℕ) : D.host.E) ((Tu D u' : ℕ) : D.host.E) (ZhatL (lf D (X.Fu u)) G') ^ (D.R.k - 1)) := by
  intro D X Y u u' hTied hk hT G' hz hTP
  haveI : Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram := ⟨GlobalTheory.BinaryRep.represents_totallyPositive⟩
  have hR : IsRowReps D (X.Fu u) (Y.what₂ u) := Y.rowsOK u
  have hP : Formalism.MainNotions.S.LocalSplitGroups.TotPos (Formalism.L2.SG.CntLocal.GZ (Formalism.L2.SG.CntLocal.Tn u) (Formalism.L2.SG.CntLocal.Tn u')
      (ZhatL (lf D (X.Fu u)) G')) := hTP
  obtain ⟨s, hs⟩ := exists_glueReps D u u' hT (X.Fu u) (Y.what₂ u) hR G' hz hP
  obtain ⟨-, hchar⟩ := Formalism.L2.SG.Pf.Cnt.mmChar_of Formalism.L2.SG.Pf.Cnt.local_unimodular_holds D u u' hT (X.Fu u) (Y.what₂ u) hR _ G'
    hz rfl hP
  have e4 := Formalism.L2.SG.Pf.Cnt.lattice_groupoid_holds D u u' hT (X.Fu u) (Y.what₂ u) hR _ G' hz rfl hP s hs
  refine ⟨s, hs, fun hne => ?_⟩
  obtain ⟨Λ, hΛ⟩ := hne
  refine ⟨⟨Λ, (hchar Λ).2 (hs.1 Λ hΛ)⟩, ?_⟩
  have hsum : glueSum (lf D (X.Fu u)) G' s = Formalism.L2.SG.CntLocal.nu (Formalism.L2.SG.CntLocal.Tn u') (X.Fu u) (Y.what₂ u)
      (ZhatL (lf D (X.Fu u)) G') * Formalism.MainNotions.S.Cnt.massRows D (X.Fu u) (Y.what₂ u) := by
    exact e4.symm
  have hpos : 0 < glueSum (lf D (X.Fu u)) G' s := by
    unfold glueSum
    refine Finset.sum_pos (fun Λ' hΛ' => ?_) ⟨Λ, hΛ⟩
    haveI : Finite (Formalism.L2.SG.Pf.Cnt.stabFix (VS D).hT (Formalism.L2.SG.Pf.Cnt.UPair D (X.Fu u) G') Λ') :=
      (hs.2.2 Λ' hΛ').to_subtype
    haveI : Nonempty (Formalism.L2.SG.Pf.Cnt.stabFix (VS D).hT (Formalism.L2.SG.Pf.Cnt.UPair D (X.Fu u) G') Λ') :=
      ⟨⟨1, one_mem_stabFix _ _⟩⟩
    exact inv_pos.2 (Nat.cast_pos.2 Nat.card_pos)
  have hnu : Formalism.L2.SG.CntLocal.nu (Formalism.L2.SG.CntLocal.Tn u') (X.Fu u) (Y.what₂ u) (ZhatL (lf D (X.Fu u)) G') ≠ 0 := by
    intro h0
    rw [hsum, h0, zero_mul] at hpos
    exact lt_irrefl _ hpos
  have hrow : ∃ Λ₁ ∈ Y.what₂ u,
      (Formalism.L2.SG.CntLocal.EZ (Formalism.L2.SG.CntLocal.Tn u') (X.Fu u) Λ₁ (ZhatL (lf D (X.Fu u)) G')).Nonempty := by
    by_contra hno
    push_neg at hno
    apply hnu
    unfold Formalism.L2.SG.CntLocal.nu
    rw [Finset.sum_eq_zero (fun Λ₁ h1 => by simp [Formalism.L2.SG.CntLocal.cntE, hno Λ₁ h1]), zero_div]
  obtain ⟨ϖ, hϖ⟩ := exists_unifs D
  have hfe := Formalism.L2.SG.Pf.formulaExplicitAt_of_eta D Formalism.L2.SG.Pf.Cnt.DualityBasisChange.frameBasisL_holds
    (fun p => Formalism.L2.SG.Pf.AlTieLG.etaLoc_of_tied hTied p) Y.δ Y.M Y.agree (locSpOf Y.δ Y.M Y.agree) u u' hT
    (X.Fu u) (Y.what₂ u) hR ϖ hϖ _ hP
  obtain ⟨-, hbdd, -, hαpos, hDI⟩ := Formalism.L2.SG.Pf.Cnt.densInputT_holds D hTied hk Y.δ Y.M Y.agree
    (locSpOf Y.δ Y.M Y.agree) u u' hT (X.Fu u) (Y.what₂ u) hR ϖ hϖ
  obtain ⟨hk2, P, q, l, hl, hS, hx⟩ := hDI
  have hsd := (Formalism.FourierDecayAlt.Final.tc_densChain Formalism.FourierDecayAlt.Final.tc_densSum Formalism.FourierDecayAlt.Final.tc_densLeTwo
    Formalism.FourierDecayAlt.Final.tc_densSize P q l _ _ _ _ hk2 hl hS hx).2
  have hdle : ∏' p, Formalism.L2.SG.CntLocal.densP (locSpOf Y.δ Y.M Y.agree) Y.δ ϖ (Formalism.L2.SG.CntLocal.Tn u)
      (Formalism.L2.SG.CntLocal.Tn u') (ZhatL (lf D (X.Fu u)) G') p ≤ 2 * ∏' p, Formalism.L2.SG.DataInst.alpD u u' p :=
    (le_csSup hbdd ⟨_, hrow, rfl⟩).trans ((div_le_iff₀ hαpos).1 hsd)
  obtain ⟨Λ₁, hΛ₁, -⟩ := hrow
  have hc : 0 < Formalism.L2.SG.Pf.Cnt.cExpl D (X.Fu u) (Y.what₂ u) :=
    Formalism.L2.SG.Pf.Cnt.cExpl_pos' D u (X.Fu u) (Y.what₂ u) hR ⟨Λ₁, hΛ₁⟩
  have hm : 0 ≤ Formalism.MainNotions.S.Cnt.massRows D (X.Fu u) (Y.what₂ u) :=
    Finset.sum_nonneg (fun _ _ => by unfold Formalism.MainNotions.S.wRow; positivity)
  have hN : 0 ≤ Formalism.L2.SG.CntLocal.sqrtAbsNormOfScaledGram ((Tu D u : ℕ) : D.host.E) ((Tu D u' : ℕ) : D.host.E)
      (ZhatL (lf D (X.Fu u)) G') := Real.sqrt_nonneg _
  have hfe' : Formalism.L2.SG.CntLocal.nu (Formalism.L2.SG.CntLocal.Tn u') (X.Fu u) (Y.what₂ u) (ZhatL (lf D (X.Fu u)) G') =
      Formalism.L2.SG.Pf.Cnt.cExpl D (X.Fu u) (Y.what₂ u) * Formalism.L2.SG.CntLocal.sqrtAbsNormOfScaledGram ((Tu D u : ℕ) : D.host.E)
        ((Tu D u' : ℕ) : D.host.E) (ZhatL (lf D (X.Fu u)) G') ^ (D.R.k - 1) *
      ∏' p, Formalism.L2.SG.CntLocal.densP (locSpOf Y.δ Y.M Y.agree) Y.δ ϖ (Formalism.L2.SG.CntLocal.Tn u)
        (Formalism.L2.SG.CntLocal.Tn u') (ZhatL (lf D (X.Fu u)) G') p := hfe
  rw [hsum, hfe']
  calc _ = (Formalism.L2.SG.Pf.Cnt.cExpl D (X.Fu u) (Y.what₂ u) * Formalism.MainNotions.S.Cnt.massRows D (X.Fu u) (Y.what₂ u) *
        Formalism.L2.SG.CntLocal.sqrtAbsNormOfScaledGram ((Tu D u : ℕ) : D.host.E) ((Tu D u' : ℕ) : D.host.E)
          (ZhatL (lf D (X.Fu u)) G') ^ (D.R.k - 1)) *
        ∏' p, Formalism.L2.SG.CntLocal.densP (locSpOf Y.δ Y.M Y.agree) Y.δ ϖ (Formalism.L2.SG.CntLocal.Tn u)
          (Formalism.L2.SG.CntLocal.Tn u') (ZhatL (lf D (X.Fu u)) G') p := by ring
    _ ≤ (Formalism.L2.SG.Pf.Cnt.cExpl D (X.Fu u) (Y.what₂ u) * Formalism.MainNotions.S.Cnt.massRows D (X.Fu u) (Y.what₂ u) *
        Formalism.L2.SG.CntLocal.sqrtAbsNormOfScaledGram ((Tu D u : ℕ) : D.host.E) ((Tu D u' : ℕ) : D.host.E)
          (ZhatL (lf D (X.Fu u)) G') ^ (D.R.k - 1)) * (2 * ∏' p, Formalism.L2.SG.DataInst.alpD u u' p) :=
      mul_le_mul_of_nonneg_left hdle (by positivity)
    _ = _ := by ring

end GlobalTheory.GlueCount
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HarishChandraFormalDegreeCompactDualLargeGaps
section
noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S

namespace GlobalTheory.FdegGap

def plusFirst {N : ℕ} (ε : Fin N → Bool) :
    Fin (Fintype.card {a // ε a = true}) ⊕ Fin (Fintype.card {a // ¬ ε a = true}) ≃ Fin N :=
  (Equiv.sumCongr (Fintype.equivFin _).symm (Fintype.equivFin _).symm).trans
    (Equiv.sumCompl (fun a => ε a = true))

theorem plusFirst_inl {N : ℕ} (ε : Fin N → Bool) (i) : ε (plusFirst ε (Sum.inl i)) = true := by
  simp only [plusFirst, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl]
  exact ((Fintype.equivFin {a // ε a = true}).symm i).2

theorem plusFirst_inr {N : ℕ} (ε : Fin N → Bool) (j) : ε (plusFirst ε (Sum.inr j)) = false := by
  simp only [plusFirst, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr, Equiv.sumCompl_apply_inr]
  simpa using ((Fintype.equivFin {a // ¬ ε a = true}).symm j).2

theorem muCD_eq_scaled (cd : CDHaar) (sc : ∀ n : ℕ, (Fin n → Bool) → NNReal)
    (hc : ∀ (n : ℕ) (ε : Fin n → Bool) (P Q : ℕ) (e : Fin P ⊕ Fin Q ≃ Fin n),
      (∀ i, ε (e (Sum.inl i)) = true) → (∀ j, ε (e (Sum.inr j)) = false) →
      ∀ A : Set (Formalism.REAL.UJ ε), MeasurableSet A →
        ((sc n ε : ENNReal) • Formalism.REAL.muG ε) A =
          cd.cd P Q {g | ∃ a ∈ A, umat a = Matrix.reindex e e (UpqT.mat g)})
    {N : ℕ} (ε : Fin N → Bool) :
    ReciprocityTheory.ChartRestriction.DS.muCD ε = (sc N ε : ENNReal) • Formalism.REAL.muG ε := by
  ext A hA
  rw [ReciprocityTheory.ChartRestriction.DS.muCD_eq_cd_vol cd (plusFirst ε) (plusFirst_inl ε) (plusFirst_inr ε) A hA]
  exact (hc N ε _ _ (plusFirst ε) (plusFirst_inl ε) (plusFirst_inr ε) A hA).symm

theorem one_le_p {N : ℕ} {ε : Fin N → Bool} (h : ∃ a, ε a = true) : 1 ≤ ReciprocityTheory.ChartRestriction.DS.pOf ε := by
  obtain ⟨a, ha⟩ := h
  exact Finset.card_pos.mpr ⟨a, by simp [ha]⟩

theorem one_le_q {N : ℕ} {ε : Fin N → Bool} (h : ∃ a, ε a = false) : 1 ≤ ReciprocityTheory.ChartRestriction.DS.qOf ε := by
  obtain ⟨a, ha⟩ := h
  exact Finset.card_pos.mpr ⟨a, by simp [ha]⟩

theorem thrStar_eq {N : ℕ} (ε : Fin N → Bool) : ReciprocityTheory.ChartRestriction.DS.thrStar ε = Formalism.MainNotions.GapDS.thrE ε := by
  unfold ReciprocityTheory.ChartRestriction.DS.thrStar Formalism.MainNotions.GapDS.thrE Formalism.MainNotions.GapDS.thrDS
  rfl

theorem fdeg_gap : ∀ (cd : CDHaar) (sc : ∀ n : ℕ, (Fin n → Bool) → NNReal),
    (∀ (n : ℕ) (ε : Fin n → Bool) (P Q : ℕ) (e : Fin P ⊕ Fin Q ≃ Fin n),
      (∀ i, ε (e (Sum.inl i)) = true) → (∀ j, ε (e (Sum.inr j)) = false) →
      ∀ A : Set (Formalism.REAL.UJ ε), MeasurableSet A →
        ((sc n ε : ENNReal) • Formalism.REAL.muG ε) A =
          cd.cd P Q {g | ∃ a ∈ A, umat a = Matrix.reindex e e (UpqT.mat g)}) →
    ∀ (N : ℕ) (ε : Fin N → Bool) (lam : Fin N → ℝ) (h : ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
      (∃ a, ε a = true) → (∃ a, ε a = false) → Formalism.QuantumDeterminants.GapAtLeast ε lam h → Formalism.MainNotions.GapDS.thrE ε + 1 < h →
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)), IsDS ε lam σ →
        IsFdeg ((sc N ε : ENNReal) • Formalism.REAL.muG ε) σ (Formalism.QuantumDeterminants.fdegHC lam) := by
  intro cd sc hc N ε lam h hlam hp hq hgap hh H _ _ σ hσ
  haveI : CompleteSpace H := hσ.1
  haveI : Nontrivial H := hσ.2.1
  have hCD := muCD_eq_scaled cd sc hc ε
  have hp1 := one_le_p hp
  have hq1 := one_le_q hq
  have hh' : ReciprocityTheory.ChartRestriction.DS.thrStar ε + 1 < h := by rw [thrStar_eq]; exact hh
  have hq0 : 1 ≤ ReciprocityTheory.ChartRestriction.DS.S7.q0 ε := le_min hp1 hq1
  have h8 : 8 * (N : ℝ) * ReciprocityTheory.ChartRestriction.DS.S7.q0 ε < h := by
    have hm : 16 * (N : ℝ) * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ) + 8 * Real.sqrt (2 * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ))
        ≤ ReciprocityTheory.ChartRestriction.DS.thrStar ε := le_max_right _ _
    have h0 : (0 : ℝ) ≤ (N : ℝ) * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ) := by positivity
    have hs : (0 : ℝ) ≤ Real.sqrt (2 * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ)) := Real.sqrt_nonneg _
    nlinarith
  have hΨ : ∀ μ : Fin N → ℝ, ReciprocityTheory.ChartRestriction.DS.S7.IsHCParam μ → ReciprocityTheory.ChartRestriction.DS.GapAtLeast ε μ h →
      ∃ (T : ReciprocityTheory.ChartRestriction.DS.S7.KType ε (ReciprocityTheory.ChartRestriction.DS.lowK ε μ))
        (Ψ : Matrix (Fin N) (Fin N) ℂ → (T.V →L[ℂ] T.V)), ReciprocityTheory.ChartRestriction.DS.IsPsiFor ε μ T Ψ := by
    intro μ hμ hμg
    obtain ⟨T⟩ := ReciprocityTheory.ChartRestriction.DS.HW.kType_exists ε μ hμ
    obtain ⟨m, hm⟩ := ReciprocityTheory.ChartRestriction.DS.Lap.LemK.exists_isMu hμ
    exact ⟨T, _, (ReciprocityTheory.ChartRestriction.DS.Lap.Base.psiFor N ε μ h T m hμ hm hμg hq0 h8).1⟩
  obtain ⟨w, hw⟩ := exists_ne (0 : H)
  have hdim : fdegOf (ReciprocityTheory.ChartRestriction.DS.muCD ε) σ w = ReciprocityTheory.ChartRestriction.DS.dimVlam lam :=
    ReciprocityTheory.ChartRestriction.DS.fdCons_cd hp1 hq1 hlam hgap hh' hΨ hσ hw
  obtain ⟨d, hd⟩ := Formalism.MainNotions.BridgeCSchur.fdeg_of_DS lam σ hσ
  have hpos : (0 : ℝ) < (sc N ε : ℝ) := by
    rcases (sc N ε).coe_nonneg.lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      haveI := ReciprocityTheory.ChartRestriction.DS.muCD_isHaar ε
      have hz : sc N ε = 0 := by exact_mod_cast heq.symm
      have hne := (isOpen_univ (X := Formalism.REAL.UJ ε)).measure_ne_zero (ReciprocityTheory.ChartRestriction.DS.muCD ε) Set.univ_nonempty
      rw [hCD, hz] at hne
      simp at hne
  have hsc : IsFdeg ((sc N ε : ENNReal) • Formalism.REAL.muG ε) σ (d / (sc N ε : ℝ)) := by
    have := ReciprocityTheory.ChartRestriction.DS.isFdeg_smul hpos hd
    rwa [ENNReal.ofReal_coe_nnreal] at this
  have hval : d / (sc N ε : ℝ) = Formalism.QuantumDeterminants.fdegHC lam := by
    have h1 := ReciprocityTheory.ChartRestriction.DS.fdegOf_of_isFdeg' (hCD ▸ hsc) hw
    rw [h1] at hdim
    rw [hdim, ReciprocityTheory.ChartRestriction.DS.dimVlam_eq_vand hlam.1, Formalism.MainNotions.BridgeLemma.szh_fdegHC lam hlam.1]
    rfl
  rwa [hval] at hsc

end GlobalTheory.FdegGap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimitiveSublatticeMeanCountBoundStatement
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitiveSublattice_mean_count_bound : MaxMass → ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → (∀ (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (k : W →ₗ⋆[K] W →ₗ[K] K), k.IsSymm → PD k → (∃ L : Submodule (𝓞 K) W, Submodule.IsLattice K L ∧ IsUnimodular k L) → ∃ I : Submodule (𝓞 K) W, IsOrthoLattice k I (Module.finrank K W)) → ∀ (j s : ℕ), 1 ≤ j → 1 ≤ s → j + s = Module.finrank K V → ∀ (V₁ : Type) [AddCommGroup V₁] [Module K V₁] [FiniteDimensional K V₁] [Module (𝓞 K) V₁] [IsScalarTower (𝓞 K) K V₁] (h₁ : V₁ →ₗ⋆[K] V₁ →ₗ[K] K) (I₁ : Submodule (𝓞 K) V₁), h₁.IsSymm → IsOrthoLattice h₁ I₁ j → ∀ (V₂ : Type) [AddCommGroup V₂] [Module K V₂] [FiniteDimensional K V₂] [Module (𝓞 K) V₂] [IsScalarTower (𝓞 K) K V₂] (h₂ : V₂ →ₗ⋆[K] V₂ →ₗ[K] K) (I₂ : Submodule (𝓞 K) V₂), h₂.IsSymm → IsOrthoLattice h₂ I₂ s → ∀ (n N₀ : ℕ), 1 ≤ n → 1 ≤ N₀ → ∀ 𝒢 : Set (Submodule (𝓞 K) V), Stable (isom h) 𝒢 → (∀ L ∈ 𝒢, IsIntLat h L ∧ discN h L = N₀ ∧ (∃ t : Finset V, t.card ≤ 1 ∧ dual h L = L ⊔ Submodule.span (𝓞 K) (t : Set V))) → orbSum (isom h) 𝒢 (fun L => (((primSp h L j n).encard : ℕ∞) : ℝ≥0∞)) ≤ ENNReal.ofReal (mass h₁ I₁ * mass h₂ I₂ * (n : ℝ) ^ ((j : ℝ) / 2) * ((n : ℝ) * N₀) ^ ((9 * (s : ℝ) + 8 + 4 * Real.logb 2 (Module.finrank ℚ K)) / 2)) := by
  first | exact @GlobalTheory.Mass.PrimMean.main | exact GlobalTheory.Mass.PrimMean.main | (intros; apply GlobalTheory.Mass.PrimMean.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalCompatibilityOfLocalIdentificationsStatement
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalCompatibility_of_local_identifications : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (t₀ t : TauC Y u u'), t.lam = t₀.lam → t.lam' = t₀.lam' → (∀ p : PlF D, (Y.M p).split ≠ none → ∀ gβ, Ext p (t.lin * t₀.lin⁻¹) gβ → ∀ x' ∈ lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam, ∀ x ∈ lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam, x' ∈ (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).perp ((locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).X (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame t₀.frame))) → x ∈ (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).perp ((locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).X (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame (lf D (X.Fu u))))) → (Cong (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) (lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam) (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame (lf D (X.Fu u)))) (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame t₀.frame)) (x - x') ↔ Cong (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) (lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam) (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame (lf D (X.Fu u)))) (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame t.frame)) (x - gβ x'))) → IotaCompat t₀.lam (lf D (X.Fu u)) t₀.frame t.frame (t.lin * t₀.lin⁻¹) (gS D) := by
  first | exact @GlobalTheory.IotaLocConv.iotaCompat_of_local | exact GlobalTheory.IotaLocConv.iotaCompat_of_local | (intros; apply GlobalTheory.IotaLocConv.iotaCompat_of_local <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowLatticesMeanEqGenusMeanStatement
section
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowLattices_mean_eq_genus_mean : ∀ (D : D7) (u : D.what₂.Word), (Tu D u).Prime → 3 ≤ Tu D u → SplitsCompletely (E := D.host.E) (Tu D u) → ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u → ∀ what₂ : Finset (LatV D), IsRowReps D F0 what₂ → ∀ Λ₀ : LatV D, IsRowLat D F0 Λ₀ → ∀ reps : Finset (LatW D), Formalism.ThetaLiftIndependence.IsClassReps (D.sp.X 0).hT (L0X D Λ₀ (lf D F0)) reps → ∀ N : LatW D → ℕ∞, (∀ γ ∈ Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT, ∀ L, N (Formalism.HermitianLatticesTheory.gmap γ L) = N L) → (∑ Λ ∈ what₂, ENNReal.ofReal (wRow D F0 Λ) * (N (L0X D Λ (lf D F0)) : ℝ≥0∞)) * ENNReal.ofReal (Formalism.HermitianLatticesTheory.mass (D.sp.X 0).hT (L0X D Λ₀ (lf D F0))) = (∑ Λ ∈ what₂, ENNReal.ofReal (wRow D F0 Λ)) * ∑ L' ∈ reps, ENNReal.ofReal ((Nat.card (Formalism.ThetaLiftIndependence.autL (D.sp.X 0).hT L') : ℝ))⁻¹ * (N L' : ℝ≥0∞) := by
  first | exact @GlobalTheory.MeanGenus.mean_rows_eq_mean_genus | exact GlobalTheory.MeanGenus.mean_rows_eq_mean_genus | (intros; apply GlobalTheory.MeanGenus.mean_rows_eq_mean_genus <;> assumption)
end

