import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0027
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AtTauExUniqueHolds
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0005
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0305
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1046
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1051
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0991
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotInhAbsOfGamLe
import Formalism.LocalRingCardinality.Bundle0005
import Formalism.SharpRestriction.GlobalSchurBounds.FiniteModelOfAdmissibleTransports
import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.SlopeLineRamifiedFormula
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ModelIdentificationRespectsRealAndFinite
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open Formalism.MainNotions.StandardLattice

namespace GlobalTheory.Core.Mi.SeeReal

variable {D : D7}

theorem isAtTau_atTau (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau)
    (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hg : gᴴ * gramAt D V τ * g = gramAt D V τ) :
    IsAtTau θ V τ g (atTau θ V τ g) := by
  have hex := (Formalism.IndefR.Eqv.atTauExUnique_holds D θ hθ V τ g hg).exists
  unfold atTau
  rw [dif_pos hex]
  exact hex.choose_spec

theorem eq_of_conj {n : ℕ} {P A B : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P.det) (e : P * A * P⁻¹ = B) :
    A = P⁻¹ * B * P := by
  rw [← e]
  simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul P hP, Matrix.mul_one, Matrix.nonsing_inv_mul_cancel_left P A hP]

theorem phi_inst (v : InfinitePlace D.host.F) (x : D.host.E) :
    (Formalism.IndefR.RationalEmbedding.inst D).φ v x = embS D ((Formalism.L2.Host.tauPl D).symm v) x := rfl

theorem realSplit_gen {I : Formalism.MainNotions.S.AutInst} (h : I = Formalism.L2.SG.InstExistsPf.instOf D)
    (ιE : I.E ≃+* D.host.E) (hιE : ∀ x : I.E, HEq (ιE x) x) (pl : InfinitePlace I.F ≃ D.what₂.Tau)
    (hφ : ∀ v (x : I.E), I.φ v x = embS D (pl v) (ιE x)) (θ : InfFam D) (hθ : IsInfFam θ) :
    (∀ k : GA D (D.sp.Y 0), k ∈ GfC (D.sp.Y 0) ↔ ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm) k).1 = 1) ∧
    (∀ k : GA D (D.sp.Y 0), k ∈ GinfC (D.sp.Y 0) ↔ ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm) k).2 = 1) ∧
    (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ),
      ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm) (atTau θ (D.sp.Y 0) τ g)).2 = 1 ∧
      (∀ v, v ≠ pl.symm τ → ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm) (atTau θ (D.sp.Y 0) τ g)).1 v = 1) ∧
      HEq (uMat (((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm) (atTau θ (D.sp.Y 0) τ g)).1 (pl.symm τ)))
        ((fun Pm : Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) ℂ => Pm⁻¹ * g * Pm)
          ((Formalism.L2.SG.InstExistsPf.instOf D).P (Formalism.L2.Host.tauPl D τ)))) ∧
    ∀ τ (y : Formalism.REAL.UJ (I.ε (pl.symm τ))), ∃ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ),
      ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm) (atTau θ (D.sp.Y 0) τ g)).1 (pl.symm τ) = y := by
  subst h
  obtain rfl := Formalism.IndefR.Eqv.eq_thetaC D hθ
  have hι : ∀ x, ιE x = x := fun x => eq_of_heq (hιE x)
  have key : ∀ τ τ' : D.what₂.Tau, embS D τ = embS D τ' → τ = τ' :=
    fun τ τ' e => D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 e))
  have hpl : pl = (Formalism.L2.Host.tauPl D).symm := Equiv.ext fun v => key _ _ (RingHom.ext fun x => by
    have e := hφ v x
    have e2 : embS D (pl v) (ιE x) = embS D (pl v) x := congrArg _ (hι x)
    exact (e2.symm.trans e.symm).trans (phi_inst v x))
  subst hpl
  have hT : ∀ k, ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA (rfl : Formalism.L2.SG.InstExistsPf.instOf D = _).symm)) k =
      Formalism.IndefR.RationalEmbedding.iota D k := fun _ => rfl
  have hP : ∀ v, IsUnit ((Formalism.IndefR.RationalEmbedding.inst D).P v).det :=
    fun v => (Matrix.isUnit_iff_isUnit_det _).mp ((Formalism.IndefR.RationalEmbedding.inst D).P_unit v)
  refine ⟨fun k => ?_, fun k => ?_, fun τ g hg => ?_, fun τ y => ?_⟩
  · rw [hT]
    have e := Formalism.L2.SG.EvalTIota.brg_mem_GfC_i (Formalism.IndefR.RationalEmbedding.iota D k)
    rwa [ContinuousMulEquiv.symm_apply_apply] at e
  · rw [hT]
    have e := Formalism.L2.SG.EvalTIota.iota_symm_mem_GinfC (Formalism.IndefR.RationalEmbedding.iota D k)
    rwa [ContinuousMulEquiv.symm_apply_apply] at e
  · have hg' : gᴴ * gramAt D (D.sp.Y 0) τ * g = gramAt D (D.sp.Y 0) τ := hg
    have hk := isAtTau_atTau (Formalism.IndefR.Eqv.thetaC D) (Formalism.IndefR.Eqv.isInfFam_thetaC D) _ τ g hg'
    rw [hT]
    generalize atTau (Formalism.IndefR.Eqv.thetaC D) (D.sp.Y 0) τ g = k at hk ⊢
    obtain ⟨x, rfl⟩ := (Formalism.IndefR.RationalEmbedding.iota D).symm.surjective k
    rw [ContinuousMulEquiv.apply_symm_apply]
    have hbr := Formalism.L2.SG.EvalTIota.infMat_brg_i x
    refine ⟨(Formalism.L2.SG.EvalTIota.iota_symm_mem_GinfC x).1 hk.1, fun v hv => ?_, heq_of_eq ?_⟩
    · obtain ⟨ρ, rfl⟩ := (Formalism.L2.Host.tauPl D).surjective v
      have hρ : ρ ≠ τ := fun e => hv (by rw [e]; rfl)
      have e0 : Formalism.L2.SG.EvalTIota.Pi (Formalism.L2.Host.tauPl D ρ) * Formalism.L2.SG.EvalTIota.uM' x (Formalism.L2.Host.tauPl D ρ) *
          (Formalism.L2.SG.EvalTIota.Pi (Formalism.L2.Host.tauPl D ρ))⁻¹ = (1 : Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) ℂ) := by
        rw [← hbr ρ, hk.2.2 ρ hρ]
      have e1 := eq_of_conj (hP _) e0
      simp only [Formalism.L2.SG.EvalTIota.Pi, Formalism.L2.SG.EvalTIota.uM'] at e1
      have e2 : uMat (x.1 (Formalism.L2.Host.tauPl D ρ)) = 1 := by
        rw [e1]
        erw [Matrix.mul_one]
        exact Matrix.nonsing_inv_mul _ (hP _)
      exact Subtype.ext (Units.ext e2)
    · exact eq_of_conj (hP _) ((hbr τ).symm.trans hk.2.1)
  · classical
    let x0 : (Formalism.IndefR.RationalEmbedding.inst D).GA :=
      (Pi.mulSingle (M := fun v => Formalism.REAL.UJ ((Formalism.IndefR.RationalEmbedding.inst D).ε v)) (Formalism.L2.Host.tauPl D τ) y, 1)
    have hbr := Formalism.L2.SG.EvalTIota.infMat_brg_i x0
    let g : Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) ℂ :=
      (Formalism.IndefR.RationalEmbedding.inst D).P (Formalism.L2.Host.tauPl D τ) * uMat y * ((Formalism.IndefR.RationalEmbedding.inst D).P (Formalism.L2.Host.tauPl D τ))⁻¹
    have hk0 : IsAtTau (Formalism.IndefR.Eqv.thetaC D) (D.sp.Y 0) τ g ((Formalism.IndefR.RationalEmbedding.iota D).symm x0) := by
      refine ⟨(Formalism.L2.SG.EvalTIota.iota_symm_mem_GinfC x0).2 rfl, ?_, fun ρ hρ => ?_⟩
      · rw [hbr τ]
        have hy : x0.1 (Formalism.L2.Host.tauPl D τ) = y :=
          Pi.mulSingle_eq_same (M := fun v => Formalism.REAL.UJ ((Formalism.IndefR.RationalEmbedding.inst D).ε v)) (Formalism.L2.Host.tauPl D τ) y
        have hy' : Formalism.L2.SG.EvalTIota.uM' x0 (Formalism.L2.Host.tauPl D τ) = uMat y := by
          show uMat (x0.1 (Formalism.L2.Host.tauPl D τ)) = uMat y
          rw [hy]
        rw [hy']
        rfl
      · rw [hbr ρ]
        have hne : Formalism.L2.Host.tauPl D ρ ≠ Formalism.L2.Host.tauPl D τ := (Formalism.L2.Host.tauPl D).injective.ne hρ
        have h1 : x0.1 (Formalism.L2.Host.tauPl D ρ) = 1 := Pi.mulSingle_eq_of_ne hne _
        have h1' : Formalism.L2.SG.EvalTIota.uM' x0 (Formalism.L2.Host.tauPl D ρ) = 1 := by
          show uMat (x0.1 (Formalism.L2.Host.tauPl D ρ)) = 1
          rw [h1]
          rfl
        rw [h1']
        erw [Matrix.mul_one]
        exact Matrix.mul_nonsing_inv _ (hP _)
    have hgU : gᴴ * gramAt D (D.sp.Y 0) τ * g = gramAt D (D.sp.Y 0) τ :=
      Formalism.IndefR.Eqv.atTauUnitary_holds D _ (Formalism.IndefR.Eqv.isInfFam_thetaC D) _ τ g _ hk0
    refine ⟨g, hgU, ?_⟩
    have hu := (Formalism.IndefR.Eqv.atTauExUnique_holds D _ (Formalism.IndefR.Eqv.isInfFam_thetaC D) _ τ g hgU).unique
      (isAtTau_atTau _ (Formalism.IndefR.Eqv.isInfFam_thetaC D) _ τ g hgU) hk0
    rw [hT, hu, ContinuousMulEquiv.apply_symm_apply]
    exact Pi.mulSingle_eq_same (M := fun v => Formalism.REAL.UJ ((Formalism.IndefR.RationalEmbedding.inst D).ε v)) _ _

theorem realSplit_of_idE : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (θ : InfFam D), IsInfFam θ → IdE X → RealSplit X h θ :=
  fun _ X h θ hθ hE => realSplit_gen h X.ιE hE X.pl X.φ_eq θ hθ

end GlobalTheory.Core.Mi.SeeReal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MulVecPairVecDiag
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section

namespace GlobalTheory.Core.Rk.Dich

open Matrix

section Mat

variable {A B : Type} [CommRing A] [CommRing B] {n : ℕ}

def diagSnd (M : Matrix (Fin (n + n)) (Fin (n + n)) A) : Matrix (Fin n) (Fin n) A :=
  (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ + (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂

theorem mulVec_pairVec_diag (M : Matrix (Fin (n + n)) (Fin (n + n)) A) (x : Fin n → A) :
    M *ᵥ pairVec finSumFinEquiv x x =
      pairVec finSumFinEquiv (leviMat finSumFinEquiv M *ᵥ x) (diagSnd M *ᵥ x) := by
  rw [mulVec_pairVec, leviMat, diagSnd, add_mulVec, add_mulVec]

theorem diagSnd_map (f : A →+* B) (M : Matrix (Fin (n + n)) (Fin (n + n)) A) :
    diagSnd (M.map f) = (diagSnd M).map f := by
  ext i j; simp [diagSnd, toBlocks₂₁, toBlocks₂₂]

theorem isotropic_diag {σ : A →+* A} {J : Matrix (Fin n) (Fin n) A} {M : Matrix (Fin (n + n)) (Fin (n + n)) A}
    (hM : Formalism.UG.cT σ M * dblGram finSumFinEquiv J * M = dblGram finSumFinEquiv J) :
    Formalism.UG.cT σ (leviMat finSumFinEquiv M) * J * leviMat finSumFinEquiv M =
      Formalism.UG.cT σ (diagSnd M) * J * diagSnd M := by
  have h1 : Formalism.UG.cT σ (M.submatrix finSumFinEquiv finSumFinEquiv) * fromBlocks J 0 0 (-J) *
      M.submatrix finSumFinEquiv finSumFinEquiv = fromBlocks J 0 0 (-J) := by
    rw [← submatrix_blkMat finSumFinEquiv,
      show Formalism.UG.cT σ (M.submatrix finSumFinEquiv finSumFinEquiv) =
        (Formalism.UG.cT σ M).submatrix finSumFinEquiv finSumFinEquiv from rfl, submatrix_mul_equiv, submatrix_mul_equiv]
    exact congrArg (fun X => X.submatrix finSumFinEquiv finSumFinEquiv) hM
  rw [← fromBlocks_toBlocks (M.submatrix finSumFinEquiv finSumFinEquiv)] at h1
  simp only [Formalism.UG.cT, fromBlocks_map, fromBlocks_transpose, fromBlocks_multiply, Matrix.mul_zero, add_zero,
    zero_add, Matrix.mul_neg, Matrix.neg_mul, fromBlocks_inj] at h1
  obtain ⟨h11, h12, h21, h22⟩ := h1
  simp only [Formalism.UG.cT, leviMat, diagSnd, Matrix.map_add _ (map_add σ), transpose_add, Matrix.add_mul, Matrix.mul_add]
  set a := (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁
  set b := (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂
  set c := (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁
  set d := (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂
  rw [← sub_eq_zero]
  have := congrArg₂ (fun a b => a + b) (congrArg₂ (fun a b => a + b) h11 h12) (congrArg₂ (fun a b => a + b) h21 h22)
  simp only [add_zero, add_neg_cancel] at this
  rw [← sub_eq_zero] at this
  rw [← this]
  abel

end Mat

section Rat

open Formalism.BasicNotions Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem exists_rat (W : HSp D) {γ : GA D W} (hγ : γ ∈ GQ W) :
    ∃ g : GL (Fin W.rank) D.host.E, g ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) W.gram ∧
      (matHom W γ).1 = g.1.map (incA D) ∧ (matHom W γ⁻¹).1 = (g⁻¹).1.map (incA D) := by
  obtain ⟨g, hg, e⟩ := hγ
  have e' : matHom W γ = Formalism.UG.bc (incA D) g := e.symm
  refine ⟨g, hg, congrArg Units.val e', ?_⟩
  rw [map_inv, e', ← map_inv]
  rfl

theorem exists_of_rat (W : HSp D) {g : GL (Fin W.rank) D.host.E}
    (hg : g ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) W.gram) :
    ∃ δ ∈ GQ W, (matHom W δ).1 = g.1.map (incA D) := by
  have hm : Formalism.UG.bc (incA D) g ∈ HR (AF D.host.F) D.sp.cm.sig W.gram := by
    have hc : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) ((g : Matrix (Fin W.rank) (Fin W.rank) D.host.E).map (incA D)) =
        (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E)).map (incA D) := by
      ext i j; simp [Formalism.UG.cT, sigR, inclR]
    have hg' : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E) * W.gram *
        (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E) = W.gram := hg
    change Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) ((g : Matrix (Fin W.rank) (Fin W.rank) D.host.E).map (incA D)) *
      W.gram.map (incA D) * (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E).map (incA D) = W.gram.map (incA D)
    rw [hc, ← Matrix.map_mul, ← Matrix.map_mul, hg']
  exact ⟨⟨_, hm⟩, ⟨g, hg, rfl⟩, rfl⟩

end Rat

end GlobalTheory.Core.Rk.Dich
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultTApplyRapidDec
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto.MultRapid

theorem multT_apply_rapidDec : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (θ : InfFam D), IsInfFam θ → ∀ (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ F ∈ MultT θ M J χ, ∀ v : SmT M, IsAutFunSm θ V (F v) ∧ IsCuspFun V (F v) ∧ GlobalTheory.Grow.RapidDec V (F v) := by
  intro hP D V S M θ hθ J χ F hF v
  obtain ⟨ha, hc⟩ := GlobalTheory.PairLift.LowAllPf.multT_apply_smooth_cusp θ M J χ F hF v
  exact ⟨ha, hc, GlobalTheory.Grow.rapidDec_of_cuspForm hP hθ ha hc⟩

end GlobalTheory.ChainOnto.MultRapid
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultiplicitySpaceEquivariantRealPoints
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

theorem mult_equiv_real : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (Sp : D.what₂.Tau → SPar) (M : DSModel V Sp) (J : Set (GA D V)) (χ : GA D V → ℂ), IsInfFam θ → ∀ (v : M.Vec) (b : GinfC V), ∃ w : M.Vec, (∀ τ, (w τ : M.H τ) = M.rep τ (infMat D.sp.cm.sig V.gram (θ τ) (b : GA D V)) (v τ : M.H τ)) ∧ ∀ U ∈ Mult θ M J χ, U w = rTr V (b : GA D V) (U v) := by
  intro D θ V Sp M J χ hθ v b
  classical
  let g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ := fun τ => infMat D.sp.cm.sig V.gram (θ τ) (b : GA D V)
  have hg : ∀ τ, g τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := fun τ =>
    GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V (b : GA D V) τ
  have hsm : ∀ τ, M.rep τ (g τ) (v τ : M.H τ) ∈ M.sm τ := fun τ =>
    GlobalTheory.SmoothStable.rep_mem_sm D V Sp M τ (g τ) (hg τ) _ (v τ).2
  have hb : GlobalTheory.AdelicScalar.realElt θ V g = (b : GA D V) := by
    have hR := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V
    refine hR.2.2.1 _ (GlobalTheory.RealLift.prodAt_mem θ V _ g) _ b.2 fun τ => ?_
    have e := GlobalTheory.RealLift.infMat_prodAt hθ V (u := g) hg τ _ (Finset.nodup_toList Finset.univ)
    rw [if_pos (Finset.mem_toList.2 (Finset.mem_univ _))] at e
    exact e
  refine ⟨fun τ => ⟨_, hsm τ⟩, fun τ => rfl, fun U hU => ?_⟩
  rw [GlobalTheory.RealEquiv.mult_realElt D V Sp θ M J χ U hU g hg v _ (fun τ => rfl), hb]

end GlobalTheory.ChainOnto
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PartialNormalizingFactorProductAnalyticNeZero
section
noncomputable section

namespace GlobalTheory.LFun

open NumberField IsDedekindDomain

section Ext

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem one_lt_re_dv_arg {a i : ℕ} (hi : i ∈ Finset.range a) {s : ℂ} (hs : 0 < s.re) :
    1 < (2 * s + a - i : ℂ).re := by
  have : (i : ℝ) + 1 ≤ a := by exact_mod_cast Finset.mem_range.1 hi
  simp
  linarith

theorem dv_ne_zero_of_re_pos (a b : ℕ) (v : HeightOneSpectrum (𝓞 F)) {s : ℂ} (hs : 0 < s.re) :
    dv E a b v s ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun i hi =>
    inv_ne_zero ((converges_etaFam (E := E) ∅ (b + i) (one_lt_re_dv_arg hi hs)).1 v (Set.notMem_empty v))

theorem dSfun_ne_zero_of_re_pos (S : Set (HeightOneSpectrum (𝓞 F))) (a b : ℕ) {s : ℂ} (hs : 0 < s.re) :
    dSfun E S a b s ≠ 0 := by
  rw [dSfun_eq S a b hs]
  exact Finset.prod_ne_zero_iff.2 fun i hi => (converges_etaFam S (b + i) (one_lt_re_dv_arg hi hs)).ne_zero

theorem differentiableOn_dSfun (S : Set (HeightOneSpectrum (𝓞 F))) (a b : ℕ) :
    DifferentiableOn ℂ (dSfun E S a b) {s | 0 < s.re} := by
  have h : DifferentiableOn ℂ (fun s : ℂ => ∏ i ∈ Finset.range a, etaL E S (b + i) (2 * s + a - i))
      {s | 0 < s.re} := by
    refine DifferentiableOn.fun_finsetProd fun i hi => ?_
    refine (bounded_etaFam (E := E) S (b + i)).differentiableOn.comp
      (f := fun s : ℂ => 2 * s + a - i) (by fun_prop) fun s hs => ?_
    simpa only [zero_add, Set.mem_ofPred_eq] using one_lt_re_dv_arg hi hs
  exact h.congr fun s hs => dSfun_eq S a b hs

end Ext

end GlobalTheory.LFun

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP

theorem dSfun_analytic_ne_zero : ∀ (D : D7) (S : Set (FinPl D)) (a b : ℕ), AnalyticOnNhd ℂ (GlobalTheory.LFun.dSfun (F := D.host.F) D.host.E S a b) (rightOf 0) ∧ ∀ s : ℂ, 0 < s.re → GlobalTheory.LFun.dSfun (F := D.host.F) D.host.E S a b s ≠ 0 ∧ (∀ v : FinPl D, GlobalTheory.LFun.dv D.host.E a b v s ≠ 0) ∧ HasProd (fun v : {v : FinPl D // v ∉ S} => GlobalTheory.LFun.dv D.host.E a b v.1 s) (GlobalTheory.LFun.dSfun (F := D.host.F) D.host.E S a b s) := fun _ S a b =>
  ⟨(GlobalTheory.LFun.differentiableOn_dSfun S a b).analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re),
    fun _ hs => ⟨GlobalTheory.LFun.dSfun_ne_zero_of_re_pos S a b hs, fun v => GlobalTheory.LFun.dv_ne_zero_of_re_pos a b v hs,
      (GlobalTheory.LFun.hasProd_dv S a b hs).multipliable.hasProd⟩⟩

end GlobalTheory.Core.Rk.IP

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeterssonCoefficientBoundedSphericalUnramified
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section

namespace GlobalTheory.Core.Rk.SphCoef

variable {D : D7}

theorem mem_l2_add {A : HSp D} {m : Measure (GA D A)} {φ ψ : GA D A → ℂ} (h : MemL2Quotient (GQ A) m φ)
    (h' : MemL2Quotient (GQ A) m ψ) : MemL2Quotient (GQ A) m (φ + ψ) :=
  ⟨fun γ hγ g => by simp only [Pi.add_apply, h.1 γ hγ g, h'.1 γ hγ g], h.2.add h'.2⟩

theorem mem_l2_smul {A : HSp D} {m : Measure (GA D A)} {φ : GA D A → ℂ} (c : ℂ) (h : MemL2Quotient (GQ A) m φ) :
    MemL2Quotient (GQ A) m (c • φ) :=
  ⟨fun γ hγ g => by simp only [Pi.smul_apply, h.1 γ hγ g], h.2.const_smul c⟩

theorem mem_l2_zero {A : HSp D} {m : Measure (GA D A)} : MemL2Quotient (GQ A) m (0 : GA D A → ℂ) :=
  ⟨fun _ _ _ => rfl, MemLp.zero⟩

theorem isSphCoef_rcoef : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (θ : InfFam D) (A : HSp D) (cA : CptF A) (L : Lat A), IsInfFam θ → ∀ (m : Measure (GA D A)), m.IsHaarMeasure → ∀ (Sf : Finset (FinPl D)), ∀ u₁ ∈ A0 θ A cA, ∀ u₂ ∈ A0 θ A cA, ∀ par : GlobalTheory.LFun.Fam D.host.E, GlobalTheory.LFun.IsParamFun D.sp.cm.sig A.gram L (Sf : Set (FinPl D)) u₁ par → SphFun A L Sf u₂ → ∀ v ∉ Sf, ∀ x : GA D A, proj D.sp.cm.sig A.gram v x = 1 → IsSphCoef A L v par fun y => rcoef m u₁ u₂ (x * emb D.sp.cm.sig A.gram v y) := by
  intro hP D θ A cA L hθ m hm Sf u₁ hu₁ u₂ hu₂ par hpar hsph v hv x hx
  have : m.IsMulRightInvariant := GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D A m hm
  have h1 : MemL2Quotient (GQ A) m u₁ := memL2_of_cusp_form hP hθ (mem_cuspForms.1 hu₁).1
  have h2 : MemL2Quotient (GQ A) m u₂ := memL2_of_cusp_form hP hθ (mem_cuspForms.1 hu₂).1
  have hR : ∀ g, MemL2Quotient (GQ A) m (rTr A g u₁) := fun g => h1.mul_right g
  let p : Submodule ℂ (GA D A → ℂ) :=
    { carrier := {F | MemL2Quotient (GQ A) m (rTr A x F)}
      zero_mem' := mem_l2_zero
      add_mem' := fun ha hb => mem_l2_add ha hb
      smul_mem' := fun c _ hF => mem_l2_smul c hF }
  let ℓ₀ : p →ₗ[ℂ] ℂ :=
    { toFun := fun F => petersson A m (rTr A x F) u₂
      map_add' := fun F G => petersson_add_left F.2 G.2 h2
      map_smul' := fun c F => petersson_smul_left c _ _ }
  obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend ℓ₀
  let ρ : Representation ℂ (Gv A v) (GA D A → ℂ) :=
    (GlobalTheory.PRep.rightReg ℂ (GA D A) ℂ).comp (emb D.sp.cm.sig A.gram v)
  have hρ : ∀ y g, ρ y u₁ g = u₁ (g * emb D.sp.cm.sig A.gram v y) := fun _ _ => rfl
  have htr : ∀ y, rTr A x (ρ y u₁) = rTr A (x * emb D.sp.cm.sig A.gram v y) u₁ := fun y => funext fun g => by
    simp only [rTr, hρ, mul_assoc]
  have hmem : ∀ y, ρ y u₁ ∈ p := fun y => by
    show MemL2Quotient _ _ (rTr A x (ρ y u₁))
    rw [htr]; exact hR _
  have hval : ∀ y, ℓ (ρ y u₁) = petersson A m (rTr A (x * emb D.sp.cm.sig A.gram v y) u₁) u₂ := fun y => by
    have e := LinearMap.congr_fun hℓ ⟨_, hmem y⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at e
    rw [e, ← htr]; rfl
  have hnorm : ∀ g, ‖(hR g).toL2‖ = ‖h1.toL2‖ := fun g => by
    have e1 := (hR g).inner_toL2_eq_theta_pairing (hR g)
    have e2 := h1.inner_toL2_eq_theta_pairing h1
    have e3 : pet (GQ A) m (rTr A g u₁) (rTr A g u₁) = pet (GQ A) m u₁ u₁ := by
      have := petersson_rTr (μ := m) h1 h1 g
      exact this
    rw [e3, ← e2, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at e1
    have e4 : ‖(hR g).toL2‖ ^ 2 = ‖h1.toL2‖ ^ 2 := by exact_mod_cast e1
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 e4
  refine ⟨⟨‖h2.toL2‖ * ‖h1.toL2‖, fun y => ?_⟩, GA D A → ℂ, inferInstance, inferInstance, ρ, u₁, ℓ,
    fun w h => hpar v (by simpa using hv) w h, fun k hk y => ?_, fun y => (hval y).symm⟩
  · show ‖petersson A m (rTr A (x * emb D.sp.cm.sig A.gram v y) u₁) u₂‖ ≤ _
    rw [petersson, ← (hR _).inner_toL2_eq_theta_pairing h2, ← hnorm (x * emb D.sp.cm.sig A.gram v y)]
    exact norm_inner_le_norm _ _
  · rw [hval, hval, map_mul]
    have hc : emb D.sp.cm.sig A.gram v k * x = x * emb D.sp.cm.sig A.gram v k :=
      (GlobalTheory.AdelicU.commute_emb (σ := D.sp.cm.sig) (J := A.gram) k hx).eq
    have e1 : rTr A (x * (emb D.sp.cm.sig A.gram v k * emb D.sp.cm.sig A.gram v y)) u₁ =
        rTr A (emb D.sp.cm.sig A.gram v k) (rTr A (x * emb D.sp.cm.sig A.gram v y) u₁) := funext fun g => by
      simp only [rTr]
      rw [← mul_assoc x, ← hc]
      simp only [mul_assoc]
    have e2 : u₂ = rTr A (emb D.sp.cm.sig A.gram v k) u₂ := funext fun g => (hsph v hv k hk g).symm
    rw [e1]
    conv_lhs => rw [e2]
    exact petersson_rTr (hR _) h2 _

end GlobalTheory.Core.Rk.SphCoef

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamShareOfFreeT
section
open Formalism.BasicNotions Formalism.MainNotions.S GlobalTheory.Core.Rk

noncomputable section

namespace GlobalTheory.Core.Rk

theorem ramShare_of_freeT {D : D7} {u : D.what₂.Word} (W : Formalism.MainNotions.product_first_zeroth_parts.FreeT D u) : RamShare D u := by
  have h := Formalism.MainNotions.product_first_zeroth_parts.rank_nat W
  have hT2 : 2 ≤ (D.mem u).A.T := ((D.mem u).A.T_prime).two_le
  unfold RamShare dU
  rw [d0_eq]
  have h' : ((D.mem u).A.du : ℝ) * (((D.mem u).A.T : ℝ) - 1) ^ D.R.f =
      (D.duS u : ℝ) * (((D.mem u).A.T : ℝ) - 2) ^ D.R.f := by
    have e2 : (D.mem u).A.T - 1 - 1 = (D.mem u).A.T - 2 := by omega
    rw [e2] at h
    have := congrArg (fun n : ℕ => (n : ℝ)) h
    simp only [Nat.cast_mul, Nat.cast_pow] at this
    rw [Nat.cast_sub (by omega : 1 ≤ (D.mem u).A.T), Nat.cast_sub hT2] at this
    push_cast at this
    exact this
  have hpos : (0 : ℝ) < ((D.mem u).A.T : ℝ) - 1 := by
    have : (2 : ℝ) ≤ ((D.mem u).A.T : ℝ) := by exact_mod_cast hT2
    linarith
  have e : (1 - 1 / (((D.mem u).A.T : ℝ) - 1)) = (((D.mem u).A.T : ℝ) - 2) / (((D.mem u).A.T : ℝ) - 1) := by
    field_simp; ring
  rw [e, div_pow]
  have hne : (((D.mem u).A.T : ℝ) - 1) ^ D.R.f ≠ 0 := pow_ne_zero _ hpos.ne'
  field_simp
  linarith [h']

theorem ramShare_of_trueD (D : D7) (u : D.what₂.Word) (hD : TrueD D) : RamShare D u :=
  TrueD.elim (Q := fun D => ∀ u : D.what₂.Word, RamShare D u)
    (fun _ _ _ _ _ w u => ramShare_of_freeT (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.freeT_0 (w.C.forms u).to0).some) hD u

end GlobalTheory.Core.Rk
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.VolQAndIntegrableIff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.QuotFundDom

theorem volQ_and_integrable_iff : ∀ (D : D7) (V : HSp D) (ν : Measure (GA D V)) (X : Set (GA D V)), ν.IsHaarMeasure → IsFundamentalDomain (GQ V) X ν → GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ V ν = (ν X).toReal ∧ ∀ F : GA D V → ℂ, (∀ γ ∈ GQ V, ∀ g, F (γ * g) = F g) → AEStronglyMeasurable F ν → (Integrable (GlobalTheory.AutomorphicL2Unitary.descend (GQ V) F) (GlobalTheory.AutomorphicL2Unitary.autMeasure V ν) ↔ IntegrableOn F X ν) := by
  intro D V ν X hν hX
  refine ⟨?_, fun F hF _ => ?_⟩
  · rw [GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ, Measure.real, GlobalTheory.AutomorphicL2Unitary.autMeasure, GlobalTheory.AutomorphicL2Unitary.quotMeasure_univ hX]
  · have hL : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) F := hF
    rw [← memLp_one_iff_integrable, GlobalTheory.AutomorphicL2Unitary.autMeasure, GlobalTheory.AutomorphicL2Unitary.memLp_quotMeasure_iff hX, hL.lift_descend,
      memLp_one_iff_integrable]
    rfl

end GlobalTheory.QuotFundDom
end

