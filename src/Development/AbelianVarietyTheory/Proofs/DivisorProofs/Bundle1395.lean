import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0162
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1237
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1361
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1217
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1275
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1331
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1366
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0169
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import ReciprocityTheory.SemistableReduction.Bundle0025
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1152
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSlotsGlobal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1182
import Formalism.PieriBlockIdeals.PieriColumnMinors.HeckeLFunctionIdealEulerProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1225
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1312
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1333

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitLatticeStableIffConjIntegral
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb

noncomputable section

namespace GlobalTheory.InertUnitOrb.LatStable

theorem mulVec_int_iff {E : Type} [Field E] [NumberField E] {n : ℕ} (w : Pl E)
    (M : Matrix (Fin n) (Fin n) (w.adicCompletion E)) :
    (∀ v : Fin n → w.adicCompletion E, (∀ i, Valued.v (v i) ≤ 1) → ∀ i, Valued.v ((M *ᵥ v) i) ≤ 1) ↔
      ∀ i j, Valued.v (M i j) ≤ 1 := by
  have hmem : ∀ x : w.adicCompletion E, Valued.v x ≤ 1 ↔ x ∈ Formalism.UG.Ov E w := fun x =>
    (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 E) (K := E) (v := w)).symm
  constructor
  · intro h i j
    have := h (Pi.single j 1) (fun k => by
      by_cases hk : k = j
      · subst hk; simp
      · simp [Pi.single_apply, hk]) i
    simpa [Matrix.mulVec_single] using this
  · intro h v hv i
    rw [hmem]
    simp only [Matrix.mulVec, dotProduct]
    exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ ((hmem _).1 (h i k)) ((hmem _).1 (hv k))

theorem mem_KGL_of_int {E : Type} [Field E] [NumberField E] {n : ℕ} (w : Pl E) (M : GLw n w)
    (h1 : ∀ i j, Valued.v ((M : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ 1)
    (h2 : ∀ i j, Valued.v (((M⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ 1) :
    M ∈ GlobalTheory.LFun.KGL w n := by
  have hmem : ∀ x : w.adicCompletion E, Valued.v x ≤ 1 ↔ x ∈ Formalism.UG.Ov E w := fun x =>
    (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 E) (K := E) (v := w)).symm
  let N : Matrix (Fin n) (Fin n) (Formalism.UG.Ov E w) := fun i j => ⟨_, (hmem _).1 (h1 i j)⟩
  let N' : Matrix (Fin n) (Fin n) (Formalism.UG.Ov E w) := fun i j => ⟨_, (hmem _).1 (h2 i j)⟩
  have hinj : Function.Injective ((Formalism.UG.Ov E w).subtype.mapMatrix :
      Matrix (Fin n) (Fin n) (Formalism.UG.Ov E w) →+* Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
    intro a b hab
    exact Matrix.ext fun i j => Subtype.ext (congrFun (congrFun hab i) j)
  have hN : (Formalism.UG.Ov E w).subtype.mapMatrix N = (M : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
    ext i j; rfl
  have hN' : (Formalism.UG.Ov E w).subtype.mapMatrix N' = ((M⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
    ext i j; rfl
  refine ⟨⟨N, N', hinj ?_, hinj ?_⟩, ?_⟩
  · rw [map_mul, hN, hN', map_one]; exact M.mul_inv
  · rw [map_mul, hN, hN', map_one]; exact M.inv_mul
  · apply Units.ext
    simp only [Formalism.UG.bc, Units.coe_map, MonoidHom.coe_coe]
    exact hN

end GlobalTheory.InertUnitOrb.LatStable

namespace GlobalTheory.InertUnitOrb.LatStable

theorem mem_KGL_of_unitary {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : Unr E) {n : ℕ} (w : Pl E)
    (hw : ¬ IsSplitAt w) (M : GLw n w) (hM : M ∈ UL n w)
    (h1 : ∀ i j, Valued.v ((M : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ 1) :
    M ∈ GlobalTheory.LFun.KGL w n := by
  have hcj := (GlobalTheory.ConjAtPlace.main E hU w).2.2.1
  rw [UL, if_neg hw] at hM
  have hM' : Formalism.UG.cT (cj w) (M : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * 1 *
      (M : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = 1 := hM
  have hinv : ((M⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) =
      Formalism.UG.cT (cj w) (M : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
    have := congrArg (· * ((M⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E))) hM'
    simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv] at this
    exact this.symm
  refine mem_KGL_of_int w M h1 fun i j => ?_
  rw [hinv]
  simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply]
  rw [hcj]
  exact h1 j i

theorem e_mulVec {K F : Type} [Field K] [Field F] (e : K ≃+* F) {n : ℕ} (Q : Matrix (Fin n) (Fin n) F)
    (u : Fin n → K) (i : Fin n) : e ((Q.map e.symm *ᵥ u) i) = (Q *ᵥ fun j => e (u j)) i := by
  simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

end GlobalTheory.InertUnitOrb.LatStable

namespace GlobalTheory.InertUnitOrb.LatStable

theorem unitLat_stable_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ (γ : UL n w), (∀ y, ψ (B.g * y) = ((((γ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) *ᵥ ψ y) → ∀ q : UL n w, ((∀ y ∈ unitLat e B ψ q, B.g * y ∈ unitLat e B ψ q) ↔ q⁻¹ * γ * q ∈ KL n w) := by
  intro E _ _ _ hU w hw K e _ hint n B ψ γ hg q
  let ψ' : B.A → Fin n → w.adicCompletion E := fun y i => e (ψ y i)
  have hsurj : Function.Surjective ψ' := fun u => ⟨ψ.symm fun i => e.symm (u i), by funext i; simp [ψ']⟩
  set Qi := (((q⁻¹ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) with hQi
  set Qm := (((q : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) with hQm
  set Gm := (((γ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) with hGm
  set Mm := (((q⁻¹ * γ * q : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) with hMm'
  have hMm : Mm = Qi * Gm * Qm := rfl
  have hQiQm : Qi * Qm = 1 := by
    rw [hQi, hQm, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
  have hQmQi : Qm * Qi = 1 := by
    rw [hQi, hQm, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]; rfl
  have hmemL : ∀ y, y ∈ unitLat e B ψ q ↔ ∀ i, Valued.v ((Qi *ᵥ ψ' y) i) ≤ 1 := by
    intro y
    show (∀ i, ((Qi.map e.symm) *ᵥ ψ y) i ∈ (algebraMap K.O K.E).range) ↔ _
    refine forall_congr' fun i => ?_
    rw [hint, e_mulVec]
  have hgψ : ∀ y, ψ' (B.g * y) = Gm *ᵥ ψ' y := by
    intro y; funext i
    simp only [ψ']
    rw [hg, e_mulVec]
  have hstab : (∀ y ∈ unitLat e B ψ q, B.g * y ∈ unitLat e B ψ q) ↔
      ∀ v : Fin n → w.adicCompletion E, (∀ i, Valued.v (v i) ≤ 1) → ∀ i, Valued.v ((Mm *ᵥ v) i) ≤ 1 := by
    constructor
    · intro hst v hv
      obtain ⟨y, hy⟩ := hsurj (Qm *ᵥ v)
      have hyL : y ∈ unitLat e B ψ q := (hmemL y).2 (by rw [hy, Matrix.mulVec_mulVec, hQiQm, Matrix.one_mulVec]; exact hv)
      have := (hmemL _).1 (hst y hyL)
      rw [hgψ, hy, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at this
      rw [hMm]; exact this
    · intro h y hy
      rw [hmemL] at hy ⊢
      rw [hgψ]
      have key : Qi *ᵥ (Gm *ᵥ ψ' y) = Mm *ᵥ (Qi *ᵥ ψ' y) := by
        simp only [hMm, Matrix.mulVec_mulVec, Matrix.mul_assoc, hQmQi, Matrix.mul_one]
      rw [key]
      exact h _ hy
  rw [hstab, mulVec_int_iff, KL, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    exact mem_KGL_of_unitary hU w hw _ (q⁻¹ * γ * q).2 h
  · rintro ⟨N, hN⟩ i j
    have hmem : ∀ x : w.adicCompletion E, Valued.v x ≤ 1 ↔ x ∈ Formalism.UG.Ov E w := fun x =>
      (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 E) (K := E) (v := w)).symm
    rw [hmem, hMm', ← hN]
    exact ((N : Matrix (Fin n) (Fin n) (Formalism.UG.Ov E w)) i j).2

end GlobalTheory.InertUnitOrb.LatStable
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryWeylCellHaarRightTranslateInvariant
section
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG GlobalTheory.WeylCell.WeylUnipotentShell

namespace GlobalTheory.WeylCell.WeylUnipotentShell

theorem cellU_haar_rightInv : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L)
    (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q →
    ∀ (n : ℕ) (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → ¬ Even n →
    ∀ y : GU σ n, y ∈ KU σ n → IsWeylRep (simpleU k) (y : GL (Fin n) L) →
    ∀ [MeasurableSpace (cellU y)] [BorelSpace (cellU y)] (μ : Measure (cellU y)) [μ.IsHaarMeasure],
      μ ((KU σ n).subgroupOf (cellU y)) = 1 →
    ∀ p : cellU y,
      (∀ F : GU σ n → ℂ, ∫ u : cellU y, F ((u * p : cellU y) : GU σ n) ∂μ = ∫ u : cellU y, F (u : GU σ n) ∂μ) ∧
      (∀ F : GU σ n → ENNReal,
        ∫⁻ u : cellU y, F ((u * p : cellU y) : GU σ n) ∂μ = ∫⁻ u : cellU y, F (u : GU σ n) ∂μ) := by
  intro L _ _ _ ϖ σ q hU n k hk hn y hy hw _ _ μ _ _ p
  have hS := GlobalTheory.T.unitaryWeylCellShell_isOpenCompactSubgroup L ϖ σ q hU n k hk hn y hy hw
  haveI : LocallyCompactSpace (cellU y) :=
    (hS.1 0).2.1.locallyCompactSpace_of_mem_nhds_of_group ((hS.1 0).1.mem_nhds (hS.1 0).2.2.1)
  let e : cellU y ≃ᵐ cellU y := (Homeomorph.mulRight p).toMeasurableEquiv
  have he : ∀ u, e u = u * p := fun _ => rfl
  let ν : Measure (cellU y) := μ.map e
  haveI : ν.IsMulLeftInvariant := by
    have : ν = μ.map (fun x => x * p) := rfl
    rw [this]; exact isMulLeftInvariant_map_mul_right p
  haveI : IsFiniteMeasureOnCompacts ν := by
    refine ⟨fun K hK => ?_⟩
    show μ.map e K < ⊤
    rw [e.map_apply]
    exact ((hK.image (Homeomorph.mulRight p).symm.continuous)).measure_lt_top.trans_le' (by
      apply le_of_eq; congr 1; ext x; simp [e, Homeomorph.mulRight, Equiv.mulRight])

  set j : ℕ := depthU k (p : GU σ n)
  have hp : p ∈ shellU k y (j : ℤ) := mem_shellU_depth k y p
  obtain ⟨ho, hc, h1, hmul, hinv⟩ := hS.1 (j : ℤ)
  have hνS : ν (shellU k y j) = 1 * μ (shellU k y j) := by
    rw [one_mul]
    show μ.map e _ = _
    rw [e.map_apply]
    congr 1
    ext u
    simp only [Set.mem_preimage, he]
    constructor
    · intro h
      simpa using hmul _ _ h (hinv p hp)
    · intro h; exact hmul _ _ h hp
  have hνμ : ν = μ := by
    have := GlobalTheory.T.haarMeasure_unique_sigmaCompact_normalised_compactOpen (cellU y) μ ν (fun i : ℕ => shellU k y (i : ℤ))
      (fun i => ⟨(hS.1 i).2.1, (hS.1 i).1.measurableSet⟩)
      (Set.eq_univ_of_forall fun u => Set.mem_iUnion.2 ⟨_, mem_shellU_depth k y u⟩)
      _ 1 ho hc ⟨1, h1⟩ hνS
    rwa [one_smul] at this
  have hmp : MeasurePreserving e μ μ := ⟨e.measurable, hνμ⟩
  refine ⟨fun F => ?_, fun F => ?_⟩
  · exact hmp.integral_comp' (g := fun u : cellU y => F (u : GU σ n))
  · exact hmp.lintegral_comp_emb e.measurableEmbedding (fun u : cellU y => F (u : GU σ n))

end GlobalTheory.WeylCell.WeylUnipotentShell
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacTheta
section
noncomputable section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG)

namespace GlobalTheory.NormDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ}

structure Frame (P : Pair D cc δ t0 Q) where

  A : HSp D

  B : HSp D
  rkA : A.rank = P.a
  rkB : B.rank = P.d

  ιA : Formalism.MainNotions.StandardLatticesGL3.GA D P.a →* GA D A

  ιB : Formalism.MainNotions.StandardLatticesGL3.GA D P.d →* GA D B

  KA : Subgroup (GL (Fin A.rank) (Lev.EAf D))

  KB : Subgroup (GL (Fin B.rank) (Lev.EAf D))

  m : Measure (GA D A)

  mH : Measure (GA D B)

structure IsFrame (P : Pair D cc δ t0 Q) (Y : Frame P) : Prop where
  gramA : Y.A.gram = 1
  gramB : Y.B.gram = 1
  defA : GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsDefiniteSpace Y.A
  defB : GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsDefiniteSpace Y.B
  injA : Function.Injective Y.ιA
  injB : Function.Injective Y.ιB
  rangeA : Y.ιA.range = GfC Y.A
  rangeB : Y.ιB.range = GfC Y.B
  ratA : ∀ x, (∃ γ ∈ GQ Y.A, finHom Y.A γ = finHom Y.A (Y.ιA x)) ↔ x ∈ ratG D P.a
  ratB : ∀ h, (∃ γ ∈ GQ Y.B, finHom Y.B γ = finHom Y.B (Y.ιB h)) ↔ h ∈ ratG D P.d
  levA : GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsOpenCompactLevel Y.A Y.KA
  levB : GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsOpenCompactLevel Y.B Y.KB
  levA_iff : ∀ x, Lev.finE Y.A (Y.ιA x) ∈ Y.KA ↔ x ∈ intG D P.a
  levB_iff : ∀ h, Lev.finE Y.B (Y.ιB h) ∈ Y.KB ↔ h ∈ P.J
  haarA : Y.m.IsHaarMeasure
  haarB : Y.mH.IsHaarMeasure
  measA : ∃ 𝓕, Links.IsMeasDef Y.A Y.KA Y.m 𝓕
  measB : ∃ 𝓕, Links.IsMeasDef Y.B Y.KB Y.mH 𝓕

structure Data (P : Pair D cc δ t0 Q) extends Frame P where

  ψ : AddChar (AF D.host.F) ℂ

  θ : InfFam D

  χA : (AE D)ˣ →* Circle

  χB : (AE D)ˣ →* Circle

  om : GlobalTheory.Core.Rk.IP.WRep A B

  vac : WO A B → ℂ

  c₁ : ℂ

namespace Data

variable {P : Pair D cc δ t0 Q} (X : Data P)

def var (k : Formalism.MainNotions.GL3Theta.Idx D P.a P.d) : FVar D X.B.rank X.A.rank :=
  (k.1, Fin.cast X.rkB.symm k.2.1, Fin.cast X.rkA.symm k.2.2)

def fock (T : Tup D P.a P.d P.n) : WO X.A X.B → ℂ :=
  pureTensorL (aPlusAll (heisO X.ψ X.A X.B) X.θ (fun _ => cplxO 1 1) (fun _ => 1) (fun _ => 1)) X.vac
    (MvPolynomial.rename X.var (minorPol D T))

def lift (T : Tup D P.a P.d P.n) : GA D X.B → ℂ := GlobalTheory.Core.Rk.IP.up X.om X.m (X.fock T) 1

end Data

structure IsWeilOf (P : Pair D cc δ t0 Q) (X : Data P) : Prop where
  inf : IsInfFam X.θ
  weil : IsWeilDatumO X.ψ X.A X.B X.χA X.χB X.om
  vac_theta : IsThetaFunO X.ψ X.A X.B X.vac
  vac_fock : ∀ τ, IsFockVacAt (heisO X.ψ X.A X.B) X.θ τ (cplxO 1 1) X.vac
  c₁_ne : X.c₁ ≠ 0
  ker : ∀ x h T, thetaKO X.om (X.ιA x) (X.ιB h) (X.fock T) = X.c₁ * P.term x h T

  fixA : ∀ k ∈ intG D P.a, ∀ T, X.om (X.ιA k, 1) (X.fock T) = X.fock T

  eigB : ∀ j ∈ P.J, ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ T, X.om (1, X.ιB j) (X.fock T) = c • X.fock T

  infB : ∀ τ, HasInfExp D X.χB τ (-((P.n τ : ℚ) + (P.d : ℚ) / 2))

def IsDict (P : Pair D cc δ t0 Q) (X : Data P) : Prop := IsFrame P X.toFrame ∧ IsWeilOf P X

end GlobalTheory.NormDict
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationOneUnitsNhds
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun MeasureTheory Topology
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

open ValuativeRel

theorem units_valuation_eq_one_mem_nhds_one {k : Type} [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    {x : kˣ | ValuativeRel.valuation k (x : k) = 1} ∈ 𝓝 (1 : kˣ) := by
  have hset : {x : kˣ | ValuativeRel.valuation k (x : k) = 1} =
      (fun x : kˣ => (x : k)) ⁻¹' (𝒪[k] : Set k) ∩
        (fun x : kˣ => ((x⁻¹ : kˣ) : k)) ⁻¹' (𝒪[k] : Set k) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, SetLike.mem_coe,
      Valuation.mem_integer_iff, Units.val_inv_eq_inv_val, map_inv₀]
    rw [inv_le_one₀ (by simp [zero_lt_iff])]
    exact le_antisymm_iff
  have hopen : IsOpen {x : kˣ | ValuativeRel.valuation k (x : k) = 1} := by
    rw [hset]
    exact ((Valuation.isOpen_integer (R := k)).preimage Units.continuous_val).inter
      ((Valuation.isOpen_integer (R := k)).preimage Units.continuous_coe_inv)
  exact hopen.mem_nhds (by simp)

example : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    {x : kˣ | ValuativeRel.valuation k (x : k) = 1} ∈ 𝓝 (1 : kˣ) :=
  GlobalTheory.units_valuation_eq_one_mem_nhds_one

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishTransferOfVanishOverAlgebraicClosureStatement
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vanish_transfer_of_vanish_over_algebraicClosure : ∀ (F σ : Type) [Field F] [Finite σ] (J : Ideal (MvPolynomial σ F)) (f : MvPolynomial σ F), (∀ x : σ → AlgebraicClosure F, (∀ g ∈ J, aeval x g = 0) → aeval x f = 0) → ∀ (Ω : Type) [Field Ω] [Algebra F Ω] (x : σ → Ω), (∀ g ∈ J, aeval x g = 0) → aeval x f = 0 := by
  first | exact @GlobalTheory.vanish_transfer_of_algClosure | exact GlobalTheory.vanish_transfer_of_algClosure | (intros; apply GlobalTheory.vanish_transfer_of_algClosure <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WachLatticesRankOneModelsReducedFiltration
section
set_option autoImplicit false

noncomputable section

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace

private theorem lau_eq_vecL {F : Type} [Field F] {n : ℕ} (y : Fin n → F⟦X⟧) :
    GlobalTheory.WachBlock.lau y = GlobalTheory.WachPlace.vecL y := by
  funext a
  rfl

private theorem unConst : UnConst := by
  exact unit_series_constant_holds

private theorem lau_mem_iff_vecL_mem {F : Type} [Field F] {n : ℕ}
    {S : Submodule (LaurentSeries F) (Fin n → LaurentSeries F)} {y : Fin n → F⟦X⟧} :
    GlobalTheory.WachBlock.lau y ∈ S ↔ GlobalTheory.WachPlace.vecL y ∈ S := by
  rw [lau_eq_vecL]

private theorem map_comp_rk1_eq_rk1_map {Γ : Type} [Group Γ] {l : ℕ} [Fact l.Prime] (LL : FinExt l)
    (χ : Γ →* (↥(OL LL))ˣ) :
    (Matrix.GeneralLinearGroup.map (toOm LL)).comp (GlobalTheory.TripleGal.rk1 χ) =
      GlobalTheory.TripleGal.rk1 ((Units.map (GlobalTheory.WachBlock.ofOL l LL).toMonoidHom).comp χ) := by
  ext g i j
  simp [GlobalTheory.TripleGal.rk1, toOm, GlobalTheory.WachBlock.ofOL]
  obtain rfl := Subsingleton.elim i j
  simp

open NumberField GlobalTheory.ExpFrame in

theorem GlobalTheory.WachPlace.wach_lattices : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ¬ (l : ℤ) ∣ NumberField.discr E → ∀ (σ : Equiv.Perm (E →+* PadicAlgCl l)), IsFrobPerm σ → ∀ (n t h : ℕ) (J : (E →+* PadicAlgCl l) → Fin n → ℤ) (bot : (E →+* PadicAlgCl l) → ℤ), (∀ i a, 0 ≤ J i a ∧ J i a ≤ h) → (∀ i (s : Fin t), 0 ≤ bot i + ((s : ℕ) : ℤ) ∧ bot i + ((s : ℕ) : ℤ) ≤ h) → GlobalTheory.WachBlock.IntegralBlock E Ω l n t J bot → ∃ (O' F L' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : Algebra ℤ_[l] O') (_ : Field F) (_ : CharP F l) (_ : Field L') (I : Ideal O') (_ : IsAdicComplete I O') (red : O' →+* F) (un : PowerSeries O') (N : Formalism.CohomologicalDescent.FrobeniusPeriodChange.Lat (E →+* PadicAlgCl l) n O') (Npsi : Fin t → Formalism.CohomologicalDescent.FrobeniusPeriodChange.Lat (E →+* PadicAlgCl l) 1 O') (u : ℤ_[l]ˣ) (c : ℤ_[l]) (ζ : O') (em : O' →+* L') (jj : ℕ → PowerSeries O' →+* PowerSeries L'), ((u : ℤ_[l]) = 1 + (l : ℤ_[l]) * c ∧ IsUnit c ∧ Formalism.CohomologicalDescent.FrobeniusPeriodChange.IsUn l O' (u : ℤ_[l]) un) ∧ (IsPrimitiveRoot ζ l ∧ ζ - 1 ∈ I ∧ Function.Injective em ∧ ∀ b ∈ Finset.Ioo 0 l, Formalism.CohomologicalDescent.FrobeniusPeriodChange.IsLocExp l O' L' em (ζ ^ b - 1) (u : ℤ_[l]) (jj b)) ∧ Formalism.CohomologicalDescent.FrobeniusPeriodChange.LatN l N h u J em jj ∧ (∀ s, Formalism.CohomologicalDescent.FrobeniusPeriodChange.LatN l (Npsi s) h u (fun i _ => bot i + ((s : ℕ) : ℤ)) em jj) ∧ GlobalTheory.WachBlock.RedFilt σ l (PowerSeries.map red un) (fun i => (N.P i).map (PowerSeries.map red)) (fun i => (N.D i).map (PowerSeries.map red)) (fun s i => PowerSeries.map red ((Npsi s).P i 0 0)) (fun s i => PowerSeries.map red ((Npsi s).D i 0 0)) := by
  intro hBS E Ω _ _ _ _ _ _ l _ hl hd σ hσ n t h J bot hJ hbot hIB
  obtain ⟨LL, r, ψ, ϖ, R, M, rs, hz, hE, hcr, hψcr, hirr, hM0, hMtop, hmono, hstab, hrs, hlines⟩ := hIB
  obtain ⟨_, _, _⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
  haveI : CharP (ResidueField ↥(OL LL)) l := GlobalTheory.WachMap.charP_residueField_of_irreducible LL
  obtain ⟨x, dim, hx, hd0, hdR, hds⟩ :=
    GlobalTheory.T.stable_lattice_chain_with_lines_matrix_form _ ↥(OL LL) n t R r ψ ϖ M rs hirr hM0 hMtop hmono hstab hlines
  obtain ⟨u, c, ζ, jj, hu, hc, hζ, hζm, hjj⟩ := GlobalTheory.T.exists_unit_root_cyclotomicExpExpansions l LL hl hz
  obtain ⟨un, hun⟩ := (unConst l ↥(OL LL) hl (u : ℤ_[l]) c hu).1
  have hψ' : ∀ s, GlobalTheory.ExpFrame.CrysWith
      ((Matrix.GeneralLinearGroup.map (toOm LL)).comp (GlobalTheory.TripleGal.rk1 (ψ s)))
      fun τ => {bot τ + ((s : ℕ) : ℤ)} := by
    intro s
    rw [map_comp_rk1_eq_rk1_map]
    exact hψcr s
  obtain ⟨N, Nψ, y, hN, hNψ, hy⟩ := GlobalTheory.WachPlace.exists_positions_global hBS hl hd hσ
    (J := J) (wt := fun s i => bot i + ((s : ℕ) : ℤ)) hJ (fun s i => hbot i s) hz hE
    (r := r) (ψ := fun s => GlobalTheory.TripleGal.rk1 (ψ s)) hcr hψ' hx hu hun hζ (fun a ha => (hjj a ha).2)
  obtain ⟨V, e, m, hV0, hVrk, hVphi, hVgam, hVe, hVphie, hVgame⟩ :=
    GlobalTheory.WachPlace.filtration_of_chain σ (Fact.out : l.Prime).pos
      (PowerSeries.map (residue ↥(OL LL)) un)
      (fun i => (N.P i).map (PowerSeries.map (residue ↥(OL LL))))
      (fun i => (N.D i).map (PowerSeries.map (residue ↥(OL LL))))
      (fun s i => ((Nψ s).P i).map (PowerSeries.map (residue ↥(OL LL))))
      (fun s i => ((Nψ s).D i).map (PowerSeries.map (residue ↥(OL LL)))) rs dim y hd0 hdR hds hy
  refine ⟨↥(OL LL), ResidueField ↥(OL LL), ↥LL.1, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, maximalIdeal ↥(OL LL), inferInstance,
    residue ↥(OL LL), un, N, Nψ, u, c, ζ, (OL LL).val.toRingHom, jj, ⟨hu, hc, hun⟩,
    ⟨hζ, hζm, Subtype.val_injective, fun b hb => (hjj b hb).1⟩, hN, hNψ, ?_⟩
  unfold GlobalTheory.WachBlock.RedFilt
  refine ⟨R, V, rs, e, m, hrs, hV0, hVrk, ?_, ?_, ?_, ?_, ?_⟩
  · intro i k v hv
    exact lau_mem_iff_vecL_mem.2 (hVphi i k v (lau_mem_iff_vecL_mem.1 hv))
  · intro i k v hv
    exact lau_mem_iff_vecL_mem.2 (hVgam i k v (lau_mem_iff_vecL_mem.1 hv))
  · intro i s
    simp only [lau_eq_vecL]
    exact hVe i s
  · intro i s
    simp only [lau_eq_vecL]
    exact hVphie i s
  · intro i s
    simp only [lau_eq_vecL]
    exact hVgame i s

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameEigenvectorColumnFormStatement
section
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar GlobalTheory.IdTorus
open Formalism.UG (cT)
open GlobalTheory.Doubling (absE conjUnit)
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_frame_eigenvector_column_form : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ {g : GAd σ J} {k : Fin r} (γ : AF F ⊗[F] E),
    (matHom _ σ J g⁻¹).1 *ᵥ (fun i => adMat F Y i k) = γ • (fun i => adMat F Y i k) → ∀ i,
    (adMat F (cT (σ : E →+* E) Y * J) * (matHom _ σ J g).1) k i =
      (adMat F (cT (σ : E →+* E) Y * J) * (matHom _ σ J g).1 * adMat F X) k k * adMat F (cT (σ : E →+* E) Y * J) k i := by
  first | exact @GlobalTheory.TorusCentRow.row_scalar | exact GlobalTheory.TorusCentRow.row_scalar | (intros; apply GlobalTheory.TorusCentRow.row_scalar <;> assumption)
end

