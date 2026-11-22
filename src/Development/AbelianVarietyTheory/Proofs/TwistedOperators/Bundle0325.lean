import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0200
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0170
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0055
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0309
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0169
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0306
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0266
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0307
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0323
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0325
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0332
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0342
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0128
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0147
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0136
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0190
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0327
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0125
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0079
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0148
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0155
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0151
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0304
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0305

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedFormTorusTranslateVacuumValue
section
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.SphTheta.TorusVac

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

def lmulI {n' n : ℕ} (A : Matrix (Fin n') (Fin n') L) : Matrix (Fin n') (Fin n) L →ₗ[intL L] Matrix (Fin n') (Fin n) L where
  toFun x := A * x
  map_add' := Matrix.mul_add A
  map_smul' r x := Matrix.mul_smul A r x

def ex (n' : ℕ) (k : Fin (n' / 2)) (i : Fin n') : ℤ :=
  if i = lo n' k then 1 else if i = (lo n' k).rev then -1 else 0

theorem tMat_single (ϖ : L) (n' : ℕ) (k : Fin (n' / 2)) :
    tMat ϖ n' (n' / 2) (Pi.single k 1) = Matrix.diagonal (fun i => ϖ ^ ex n' k i) := by
  unfold tMat
  congr 1
  funext i
  simp only [ex, lo, Fin.ext_iff, Fin.val_rev, Pi.single_apply]
  have hk := k.2
  have hi := i.2
  split_ifs <;> first | (exfalso; omega) | simp_all

variable {σ : L →+* L} {δ : L} {ψ : AddChar L ℂ} {n n' : ℕ}

theorem pairing_unitary (h : GU σ n') (x y : Matrix (Fin n') (Fin n) L) :
    pairing σ δ ψ (h.1.1 * x) (h.1.1 * y) = pairing σ δ ψ x y := by
  have hu : cT σ h.1.1 * antiJ L n' * h.1.1 = antiJ L n' := h.2
  have hl : locH σ δ (antiG L n) (antiG L n') (h.1.1 * x) (h.1.1 * y) = locH σ δ (antiG L n) (antiG L n') x y := by
    unfold locH
    congr 1
    have e1 : ((h.1.1 * y).map σ)ᵀ = (y.map σ)ᵀ * cT σ h.1.1 := by
      rw [Matrix.map_mul, Matrix.transpose_mul]; rfl
    have e2 : ((antiG L n' : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) = antiJ L n' := rfl
    rw [e1, e2]
    congr 1
    calc _ = (((antiG L n)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (y.map σ)ᵀ * (cT σ h.1.1 * antiJ L n' * h.1.1) * x := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hu]
  have e3 : ∀ a b : Matrix (Fin n') (Fin n) L, pairing σ δ ψ a b =
      ψ (locH σ δ (antiG L n) (antiG L n') a b + σ (locH σ δ (antiG L n) (antiG L n') a b)) := by
    intro a b; rw [locH_antiG]; rfl
  rw [e3, e3, hl]

theorem mul_inv_val (t : GU σ n') : t.1.1 * (t⁻¹).1.1 = 1 := by
  rw [show t.1.1 * (t⁻¹).1.1 = (t * t⁻¹).1.1 from rfl, mul_inv_cancel]; rfl

theorem selfDual_map (t : GU σ n') {A : Submodule (intL L) (Matrix (Fin n') (Fin n) L)}
    (hA : SelfDual (pairing σ δ ψ) A) : SelfDual (pairing σ δ ψ) (A.map (lmulI t.1.1)) := by
  intro x
  constructor
  · rintro ⟨y, hy, rfl⟩ _ ⟨b, hb, rfl⟩
    show pairing σ δ ψ (t.1.1 * y) (t.1.1 * b) = 1
    rw [pairing_unitary]
    exact (hA y).1 hy b hb
  · intro H
    have hy : (t⁻¹).1.1 * x ∈ A := by
      refine (hA _).2 fun b hb => ?_
      rw [← pairing_unitary t, ← Matrix.mul_assoc, mul_inv_val, Matrix.one_mul]
      exact H _ ⟨b, hb, rfl⟩
    refine ⟨_, hy, ?_⟩
    show t.1.1 * ((t⁻¹).1.1 * x) = x
    rw [← Matrix.mul_assoc, mul_inv_val, Matrix.one_mul]

theorem idx_translate_ne {ϖ : L} {q : ℕ} (hU : IsUnramInv ϖ σ q) (t : GU σ n') (d : Fin n' → ℤ)
    (ht : t.1.1 = Matrix.diagonal fun i => ϖ ^ d i) :
    idx (intMat L (Fin n') (Fin n)) ((intMat L (Fin n') (Fin n)).map (lmulI t.1.1)) ≠ 0 := by
  have h := GlobalTheory.LatIdx.relIndex_intMat_translate ϖ σ q hU n' n d t ht 1 (one_mem _) 1 (one_mem _)
  simp only [one_mul, mul_one] at h
  have e1 : (intMat L (Fin n') (Fin n)).toAddSubgroup = GlobalTheory.InertHomIdx.intMat L n' n :=
    AddSubgroup.ext fun _ => Iff.rfl
  have e2 : ((intMat L (Fin n') (Fin n)).map (lmulI (n := n) t.1.1)).toAddSubgroup =
      AddSubgroup.map (GlobalTheory.InertHomIdx.lmul t.1.1) (GlobalTheory.InertHomIdx.intMat L n' n) :=
    AddSubgroup.ext fun _ => Iff.rfl
  unfold idx
  rw [e1, e2, h]
  exact pow_ne_zero _ (pow_ne_zero _ (by have := hU.2.2.2.2.2.1; omega))

theorem mem_of_mixLat {ϖ : L} (hϖ : Valued.v ϖ ≤ 1) (k : Fin (n' / 2)) (t : GU σ n')
    (hT : t.1.1 = Matrix.diagonal fun i => ϖ ^ ex n' k i) {x a : Matrix (Fin n') (Fin n) L}
    (hx : x ∈ (intMat L (Fin n') (Fin n)).map (lmulI t.1.1)) (ha : a ∈ mixLat L n' n)
    (hxa : x - a ∈ intMat L (Fin n') (Fin n)) : x ∈ intMat L (Fin n') (Fin n) := by
  obtain ⟨y, hy, rfl⟩ := hx
  intro r c
  by_cases hr : r = (lo n' k).rev
  · have hk := k.2
    have h0 : a r c = 0 := (ha r c).1 (Or.inl (by subst hr; simp only [lo, Fin.val_rev]; omega))
    have := hxa r c
    rwa [Matrix.sub_apply, h0, sub_zero] at this
  · show (t.1.1 * y) r c ∈ intL L
    rw [hT, Matrix.diagonal_mul]
    have hp : ϖ ^ ex n' k r ∈ intL L := by
      have he : ex n' k r = 1 ∨ ex n' k r = 0 := by
        unfold ex; split_ifs <;> simp_all
      rcases he with he | he <;> rw [he]
      · simpa using mem_intL.2 hϖ
      · simpa using one_mem (intL L)
    exact mul_mem hp (hy r c)

end GlobalTheory.SphTheta.TorusVac

open GlobalTheory.SphTheta.TorusVac in

theorem GlobalTheory.SphTheta.mixed_torus_value : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (ψ : AddChar L ℂ) (n n' : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : GU σ n × GU σ n' →* Module.End ℂ M) (s : M), IsStd ϖ σ q δ ψ ρ ω s → CayleyRule q n ρ (ω.comp (MonoidHom.inr _ _)) s → ∀ ℓ : M →ₗ[ℂ] ℂ, ℓ s = 1 → (∀ a ∈ mixLat L n' n, ∀ v, ℓ (ρ a v) = ℓ v) → (∀ x, (¬ ∃ a ∈ mixLat L n' n, x - a ∈ intMat L (Fin n') (Fin n)) → ℓ (ρ x s) = 0) → ∀ (k : Fin (n' / 2)) (t : GU σ n'), t.1.1 = tMat ϖ n' (n' / 2) (Pi.single k 1) → ℓ (ω (1, t) s) = (-1) ^ n * (q : ℂ) ^ (-(n : ℤ)) := by
  intro L _ _ ϖ σ q δ ψ n n' M _ _ ρ ω s hS hC ℓ hℓs hℓmix hℓzero k t ht
  have hU := hS.1.unr
  have hH := hS.isHeis
  have hΛ := hS.selfDual
  have hϖle : Valued.v ϖ ≤ 1 := by
    rw [hU.2.2.2.1]; exact_mod_cast (by decide : (Multiplicative.ofAdd (-1:ℤ)) ≤ 1)
  have hT : t.1.1 = Matrix.diagonal (fun i => ϖ ^ ex n' k i) := ht.trans (tMat_single ϖ n' k)
  have hΛ' := selfDual_map (n := n) (δ := δ) (ψ := ψ) t hΛ
  have hidx := idx_translate_ne (n := n) hU t _ hT
  obtain ⟨e, he1, heinv⟩ := GlobalTheory.T.exists_heisenbergInvariant_linearForm_isotropic_vacuum hH _ hΛ s hS.2.1 hS.fixes hS.2.2.2 _ (fun a ha b hb => hH.iso hΛ ha hb)
  have hv : Fixes ρ ((intMat L (Fin n') (Fin n)).map (lmulI t.1.1)) (ω (1, t) s) := by
    rintro _ ⟨y, hy, rfl⟩
    have h1 := congrArg (fun F : Module.End ℂ M => F s) (hS.1.norm 1 t y)
    simp only [Module.End.mul_apply] at h1
    rw [hS.fixes y hy] at h1
    simp at h1
    exact h1.symm
  have hsum : ℓ (sumOp ρ (intMat L (Fin n') (Fin n)) ((intMat L (Fin n') (Fin n)).map (lmulI t.1.1)) s) = 1 := by
    obtain ⟨N, f, hf, hu⟩ := ((GlobalTheory.T.sumOp_transversal_fixes_linear_and_of_le hH _ _ hΛ').2.1 hidx).1
    rw [((GlobalTheory.T.sumOp_transversal_fixes_linear_and_of_le hH _ _ hΛ').1 s hS.fixes (Fin N) f hf hu).1, map_sum]
    obtain ⟨i0, hi0, huniq⟩ := hu 0 (zero_mem _)
    have key : ∀ i, ℓ (ρ (f i) s) = if i = i0 then 1 else 0 := by
      intro i
      by_cases hfi : f i ∈ intMat L (Fin n') (Fin n)
      · have : i = i0 := huniq i (by show 0 - f i ∈ _; rw [zero_sub]; exact neg_mem hfi)
        rw [if_pos this, hS.fixes _ hfi, hℓs]
      · have hne : i ≠ i0 := by
          rintro rfl
          apply hfi
          have := neg_mem hi0
          rwa [zero_sub, neg_neg] at this
        rw [if_neg hne]
        apply hℓzero
        rintro ⟨a, ha, hxa⟩
        exact hfi (mem_of_mixLat hϖle k t hT (hf i) ha hxa)
    simp only [key, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  obtain ⟨hd, hint, hord⟩ := GlobalTheory.T.cayley_unitaryTorus_inv_det_integral_order L ϖ σ q hU hS.v_two n' k t ht
  have hev := hC e heinv t⁻¹ hd hint
  rw [inv_inv, hord, he1, mul_one] at hev
  have hco := (GlobalTheory.T.heisenbergQuotientOpSum_vacuum_commensurable_selfDualLattice hH _ hΛ s hS.2.1 hS.fixes hS.2.2.2 _ hΛ' hidx).2 e he1 heinv _ hv
  rw [hco, map_smul, hsum, smul_eq_mul, mul_one]
  simp only [MonoidHom.comp_apply, MonoidHom.inr_apply] at hev
  rw [hev, _root_.zpow_neg, zpow_one, mul_inv, _root_.zpow_neg, zpow_natCast, ← inv_pow, inv_neg, inv_one]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelHeisenbergPhaseEqCexpRealPointsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedModelHeisenbergPhase_eq_cexp_realPoints : ∀ (D : D7) (V W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E), adj D C * V.gram * C' = 1 → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (y : Matrix (Fin W.rank) (Fin r) D.host.E) (κ : Mx D W.rank r), κ.map (finPart D) = 0 → phase ψ V W C C' y κ = Complex.exp (2 * Real.pi * Complex.I * ((∑ τ, 2 * (Matrix.trace ((pairQ W y).map (tauE D τ) * compAt θ τ κ)).re : ℝ) : ℂ)) := by
  first | exact @GlobalTheory.PhaseReal.phase_eq | exact GlobalTheory.PhaseReal.phase_eq | (intros; apply GlobalTheory.PhaseReal.phase_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelTermHeisenbergIsotropicCharacterStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedModelTerm_heisenbergIsotropic_character : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ G : WO V W → ℂ, IsThetaFunO ψ V W G → ∀ (y : Matrix (Fin W.rank) (Fin r) D.host.E) (κ : Mx D W.rank r), term ψ V V' W C C' B μ 𝓨 (heisO ψ V W (isoPart V W C κ) G) y = phase ψ V W C C' y κ * term ψ V V' W C C' B μ 𝓨 G y := by
  first | exact @GlobalTheory.MixedTermTranslate.term_heisO_isoPart | exact GlobalTheory.MixedTermTranslate.term_heisO_isoPart | (intros; apply GlobalTheory.MixedTermTranslate.term_heisO_isoPart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelTermLinearThetaFunctionsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedModelTerm_linear_thetaFunctions : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ y : Matrix (Fin W.rank) (Fin r) D.host.E, (∀ G H : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W H → term ψ V V' W C C' B μ 𝓨 (G + H) y = term ψ V V' W C C' B μ 𝓨 G y + term ψ V V' W C C' B μ 𝓨 H y) ∧ ∀ (c : ℂ) (G : WO V W → ℂ), IsThetaFunO ψ V W G → term ψ V V' W C C' B μ 𝓨 (c • G) y = c * term ψ V V' W C C' B μ 𝓨 G y := by
  first | exact @GlobalTheory.MixedTerm.term_linear | exact GlobalTheory.MixedTerm.term_linear | (intros; apply GlobalTheory.MixedTerm.term_linear <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModulusInfConjLeSpanTypePrimesProductStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace nonZeroDivisors Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modulus_inf_conj_le_span_typePrimes_product : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc), G.modul ⊓ D.host.conj • G.modul ≤ Ideal.span {((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E)} := by
  first | exact @GlobalTheory.ModulConj.modul_inf_conj_le | exact GlobalTheory.ModulConj.modul_inf_conj_le | (intros; apply GlobalTheory.ModulConj.modul_inf_conj_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NcardRationalPointsInTranslateLeHeightPow
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory Set Filter NumberField
open scoped Topology ContDiff TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open GlobalTheory.AdelicU Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain Formalism.UG
open scoped NNReal

namespace GlobalTheory.RatCount

theorem gl_count (hA : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∃ (C : ℝ) (k : ℕ), ∀ B : ℝ, 1 ≤ B → {x : E | ∀ j, Height.mulHeight₁ ((minpoly F x).coeff j) ≤ B}.Finite ∧ (({x : E | ∀ j, Height.mulHeight₁ ((minpoly F x).coeff j) ≤ B}.ncard : ℕ) : ℝ) ≤ C * B ^ k) (hB : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∃ (c : ℝ) (a : ℕ), ∀ (x : E) (j : ℕ), Height.mulHeight₁ ((minpoly F x).coeff j) ≤ c * (GlobalTheory.RatCount.htE F x : ℝ) ^ a) (hC : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ) (γ : GL (Fin N) E) (i j : Fin N), GlobalTheory.RatCount.htE F ((γ : Matrix (Fin N) (Fin N) E) i j) ≤ GlobalTheory.AdelicU.heightGL F (Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)) γ))
    (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ) :
    ∃ (C : ℝ) (A : ℕ), ∀ T : ℝ, 1 ≤ T →
      {γ : GL (Fin N) E | (heightGL F (bc (inclR (F := F) (AF F)) γ) : ℝ) ≤ T}.Finite ∧
      (({γ : GL (Fin N) E | (heightGL F (bc (inclR (F := F) (AF F)) γ) : ℝ) ≤ T}.ncard : ℕ) : ℝ) ≤ C * T ^ A := by
  obtain ⟨C0, k, hk⟩ := hA F E
  obtain ⟨c, a, ha⟩ := hB F E
  refine ⟨C0 ^ (N * N) * (max 1 c) ^ (k * (N * N)), a * k * (N * N), fun T hT => ?_⟩
  set B : ℝ := max 1 c * T ^ a with hBdef
  have hB1 : 1 ≤ B := one_le_mul_of_one_le_of_one_le (le_max_left _ _) (one_le_pow₀ hT)
  obtain ⟨hXf, hXc⟩ := hk B hB1
  set X := {x : E | ∀ j, Height.mulHeight₁ ((minpoly F x).coeff j) ≤ B} with hXdef
  set S := {γ : GL (Fin N) E | (heightGL F (bc (inclR (F := F) (AF F)) γ) : ℝ) ≤ T} with hSdef
  have hmem : ∀ γ ∈ S, ∀ p : Fin N × Fin N, (γ : Matrix (Fin N) (Fin N) E) p.1 p.2 ∈ X := by
    intro γ hγ p j
    refine (ha _ j).trans ?_
    have h1 : (htE F ((γ : Matrix (Fin N) (Fin N) E) p.1 p.2) : ℝ) ≤ T :=
      (NNReal.coe_le_coe.2 (hC F E N γ p.1 p.2)).trans hγ
    calc c * (htE F ((γ : Matrix (Fin N) (Fin N) E) p.1 p.2) : ℝ) ^ a
        ≤ max 1 c * (htE F ((γ : Matrix (Fin N) (Fin N) E) p.1 p.2) : ℝ) ^ a :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
      _ ≤ B := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h1 a)
          (zero_le_one.trans (le_max_left _ _))
  let f : GL (Fin N) E → (Fin N × Fin N → E) := fun γ p => (γ : Matrix (Fin N) (Fin N) E) p.1 p.2
  have hinj : Set.InjOn f S := fun γ _ δ _ h => Units.ext (Matrix.ext fun i j => congrFun h (i, j))
  set P : Finset (Fin N × Fin N → E) := Fintype.piFinset fun _ => hXf.toFinset with hPdef
  have hmaps : ∀ γ ∈ S, f γ ∈ (P : Set (Fin N × Fin N → E)) := fun γ hγ => by
    simp only [P, Finset.mem_coe, Fintype.mem_piFinset, Set.Finite.mem_toFinset]
    exact fun p => hmem γ hγ p
  have hSf : S.Finite := Set.Finite.of_finite_image ((P.finite_toSet).subset (by
    rintro _ ⟨γ, hγ, rfl⟩; exact hmaps γ hγ)) hinj
  refine ⟨hSf, ?_⟩
  have h1 : S.ncard ≤ (P : Set (Fin N × Fin N → E)).ncard :=
    Set.ncard_le_ncard_of_injOn f hmaps hinj P.finite_toSet
  rw [Set.ncard_coe_finset, hPdef, Fintype.card_piFinset] at h1
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at h1
  rw [← Set.ncard_eq_toFinset_card X hXf] at h1
  have hC0 : 0 ≤ C0 := by
    have := (Nat.cast_nonneg (α := ℝ) _).trans hXc
    exact nonneg_of_mul_nonneg_left this (by positivity)
  calc ((S.ncard : ℕ) : ℝ) ≤ ((X.ncard : ℝ)) ^ (N * N) := by exact_mod_cast h1
    _ ≤ (C0 * B ^ k) ^ (N * N) := pow_le_pow_left₀ (by positivity) hXc _
    _ = C0 ^ (N * N) * (max 1 c) ^ (k * (N * N)) * T ^ (a * k * (N * N)) := by
        rw [hBdef]; ring

theorem gq_count (hA : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∃ (C : ℝ) (k : ℕ), ∀ B : ℝ, 1 ≤ B → {x : E | ∀ j, Height.mulHeight₁ ((minpoly F x).coeff j) ≤ B}.Finite ∧ (({x : E | ∀ j, Height.mulHeight₁ ((minpoly F x).coeff j) ≤ B}.ncard : ℕ) : ℝ) ≤ C * B ^ k) (hB : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∃ (c : ℝ) (a : ℕ), ∀ (x : E) (j : ℕ), Height.mulHeight₁ ((minpoly F x).coeff j) ≤ c * (GlobalTheory.RatCount.htE F x : ℝ) ^ a) (hC : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ) (γ : GL (Fin N) E) (i j : Fin N), GlobalTheory.RatCount.htE F ((γ : Matrix (Fin N) (Fin N) E) i j) ≤ GlobalTheory.AdelicU.heightGL F (Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)) γ)) {D : D7} (V : HSp D) :
    ∃ (C : ℝ) (A : ℕ), ∀ T : ℝ, 1 ≤ T →
      {γ : GQ V | GlobalTheory.Grow.height V (γ : GA D V) ≤ T}.Finite ∧
      (({γ : GQ V | GlobalTheory.Grow.height V (γ : GA D V) ≤ T}.ncard : ℕ) : ℝ) ≤ C * T ^ A := by
  obtain ⟨C, A, h⟩ := gl_count hA hB hC D.host.F D.host.E V.rank
  refine ⟨C, A, fun T hT => ?_⟩
  obtain ⟨hf, hc⟩ := h T hT
  have hex : ∀ γ : GQ V, ∃ δ : GL (Fin V.rank) D.host.E,
      bc (inclR (F := D.host.F) (AF D.host.F)) δ = matHom V (γ : GA D V) := by
    intro γ
    have h1 := γ.2
    simp only [GQ, HFinIn, HFin, Subgroup.mem_subgroupOf, Subgroup.mem_map] at h1
    obtain ⟨δ, -, hδ⟩ := h1
    exact ⟨δ, hδ⟩
  choose φ hφ using hex
  have hmaps : ∀ γ ∈ {γ : GQ V | GlobalTheory.Grow.height V (γ : GA D V) ≤ T},
      φ γ ∈ {δ : GL (Fin V.rank) D.host.E | (heightGL D.host.F (bc (inclR (F := D.host.F) (AF D.host.F)) δ) : ℝ) ≤ T} := by
    intro γ hγ
    simp only [Set.mem_setOf_eq] at hγ ⊢
    rw [hφ]
    exact hγ
  have hinj : Set.InjOn φ {γ : GQ V | GlobalTheory.Grow.height V (γ : GA D V) ≤ T} := by
    intro a _ b _ hab
    have h2 : matHom V (a : GA D V) = matHom V (b : GA D V) := by rw [← hφ, ← hφ, hab]
    unfold Formalism.L2.Theta.matHom at h2
    exact Subtype.ext (Subgroup.subtype_injective _ h2)
  refine ⟨Set.Finite.of_finite_image (hf.subset (by rintro _ ⟨γ, hγ, rfl⟩; exact hmaps γ hγ)) hinj, ?_⟩
  exact (Nat.cast_le.2 (Set.ncard_le_ncard_of_injOn φ hmaps hinj hf)).trans hc

theorem ncard_rat_mem_translate_le : ∀ {D : D7} {V : HSp D} {Ω : Set (GA D V)}, IsCompact Ω → ∃ (A : ℕ) (C : ℝ), ∀ g x : GA D V, {γ : GQ V | (γ : GA D V) * x ∈ (g * ·) '' Ω}.Finite ∧ ({γ : GQ V | (γ : GA D V) * x ∈ (g * ·) '' Ω}.ncard : ℝ) ≤ C * GlobalTheory.Grow.height V g ^ (2 * A) := by
  intro D V Ω hΩ
  obtain ⟨C, A, hcount⟩ := gq_count GlobalTheory.T.finite_and_ncard_minpoly_coeff_height_le GlobalTheory.T.exists_mulHeight_minpoly_coeff_le_relativeHeight GlobalTheory.T.relativeHeight_entry_le_adelicHeightGL V
  have hK : IsCompact ((fun p : GA D V × GA D V => p.1 * p.2⁻¹) '' (Ω ×ˢ Ω)) :=
    (hΩ.prod hΩ).image (by fun_prop)
  obtain ⟨C₀, hC₀⟩ := GlobalTheory.Grow.exists_height_le_of_isCompact V hK
  have hC : 0 ≤ C := by
    have := (Nat.cast_nonneg (α := ℝ) _).trans (hcount 1 le_rfl).2
    simpa using this
  refine ⟨A, C * max C₀ 1 ^ A, fun g x => ?_⟩
  rcases Set.eq_empty_or_nonempty {γ : GQ V | (γ : GA D V) * x ∈ (g * ·) '' Ω} with hS | ⟨γ₀, hγ₀⟩
  · rw [hS]
    refine ⟨Set.finite_empty, ?_⟩
    simp only [Set.ncard_empty, Nat.cast_zero]
    have := GlobalTheory.Grow.height_pos V g
    positivity
  · set T : ℝ := max C₀ 1 * GlobalTheory.Grow.height V g ^ 2 with hTdef
    have hT : 1 ≤ T := one_le_mul_of_one_le_of_one_le (le_max_right _ _)
      (one_le_pow₀ (GlobalTheory.Grow.one_le_height V g))
    obtain ⟨hf, hc⟩ := hcount T hT
    let φ : GQ V → GQ V := fun γ => γ * γ₀⁻¹
    obtain ⟨y₀, hy₀, e₀⟩ := hγ₀
    have hmaps : ∀ γ ∈ {γ : GQ V | (γ : GA D V) * x ∈ (g * ·) '' Ω},
        φ γ ∈ {δ : GQ V | GlobalTheory.Grow.height V (δ : GA D V) ≤ T} := by
      intro γ hγ
      obtain ⟨y, hy, e⟩ := hγ
      have h1 : ((φ γ : GQ V) : GA D V) = g * (y * y₀⁻¹) * g⁻¹ := by
        have e' : (γ : GA D V) = g * y * x⁻¹ := by
          rw [show g * y = (γ : GA D V) * x from e, mul_inv_cancel_right]
        have e₀' : (γ₀ : GA D V) = g * y₀ * x⁻¹ := by
          rw [show g * y₀ = (γ₀ : GA D V) * x from e₀, mul_inv_cancel_right]
        simp only [φ, Subgroup.coe_mul, Subgroup.coe_inv, e', e₀']
        group
      have hyy : GlobalTheory.Grow.height V (y * y₀⁻¹) ≤ max C₀ 1 :=
        (hC₀ _ ⟨(y, y₀), ⟨hy, hy₀⟩, rfl⟩).trans (le_max_left _ _)
      show GlobalTheory.Grow.height V ((φ γ : GQ V) : GA D V) ≤ T
      rw [h1]
      calc GlobalTheory.Grow.height V (g * (y * y₀⁻¹) * g⁻¹)
          ≤ GlobalTheory.Grow.height V g * GlobalTheory.Grow.height V (y * y₀⁻¹) * GlobalTheory.Grow.height V g⁻¹ :=
            (GlobalTheory.Grow.height_mul_le V _ _).trans (mul_le_mul_of_nonneg_right (GlobalTheory.Grow.height_mul_le V _ _)
              (GlobalTheory.Grow.height_pos V _).le)
        _ ≤ GlobalTheory.Grow.height V g * max C₀ 1 * GlobalTheory.Grow.height V g := by
            rw [GlobalTheory.Grow.height_inv]
            have := GlobalTheory.Grow.height_pos V g
            gcongr
        _ = T := by rw [hTdef]; ring
    have hinj : Set.InjOn φ {γ : GQ V | (γ : GA D V) * x ∈ (g * ·) '' Ω} :=
      fun a _ b _ hab => mul_right_cancel hab
    refine ⟨Set.Finite.of_finite_image (hf.subset (by rintro _ ⟨γ, hγ, rfl⟩; exact hmaps γ hγ)) hinj, ?_⟩
    calc (({γ : GQ V | (γ : GA D V) * x ∈ (g * ·) '' Ω}.ncard : ℕ) : ℝ)
        ≤ (({δ : GQ V | GlobalTheory.Grow.height V (δ : GA D V) ≤ T}.ncard : ℕ) : ℝ) :=
          Nat.cast_le.2 (Set.ncard_le_ncard_of_injOn φ hmaps hinj hf)
      _ ≤ C * T ^ A := hc
      _ = C * max C₀ 1 ^ A * GlobalTheory.Grow.height V g ^ (2 * A) := by rw [hTdef]; ring

end GlobalTheory.RatCount
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoExcludedParameterOfLiftParameters
section
open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Links
open GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains GlobalTheory.PRep GlobalTheory.LFun
open Formalism.UG (IsCommensurated Hecke)
open Formalism.MainNotions.SchurIrreducible (IsSplit)

noncomputable section

namespace GlobalTheory.NoExcl

open Formalism.MainNotions.StandardLattice Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.IndefR.Lift GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem isHermND_gram (V : HSp D) : IsHermND D.sp.cm.sig V.gram :=
  (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm).2 V

theorem chart (V : HSp D) {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}
    (h : w.under (𝓞 D.host.F) = v) (hv : IsSplit (E := D.host.E) v) :
    (∃ e, IsSplitChart D.sp.cm.sig V.gram (frameLat V) h e) ∧ Ideal.absNorm w.asIdeal = Formalism.UG.qV D.host.F v := by
  obtain ⟨⟨e, he, -⟩, w', -, -, h1, -⟩ := SplitChart.split_chart_and_places (isCMExt_host D) (isHermND_gram V)
    (frameLat_fg V) (SelfDual.isLattice_frameLat V).span_eq_top h hv (SelfDual.isSelfDualAt_frameLat D V v)
  exact ⟨⟨e, he⟩, h1⟩

section Param

variable {V : HSp D} {ν : Measure (GA D V)} [ν.IsHaarMeasure] [ν.IsMulRightInvariant] {W : Submodule ℂ (DividedPowerChartLift V ν)}

end Param

section Chars

open Formalism.L2.Host

variable {T : Type} {L : LevCh D T} {t₀ : T}

end Chars

def liftParam (μ : ℕ → (AE D)ˣ →* Circle) (η : (AE D)ˣ →* Circle) (k : ℕ) (w : HeightOneSpectrum (𝓞 D.host.E))
    (B : Multiset ℂˣ) : Multiset ℂˣ :=
  (B + ∑ i ∈ Finset.range k, seg w (val (μ (i + 1)) w) D.R.t).map (· * if Odd k then (val η w)⁻¹ else 1)

def LiftParameters (D : D7) : Prop :=
  (∃ N : ℕ, D.R.rankY D.R.m + 1 ≤ N ∧ D.NodeGap ((D.R.t : ℝ) + 2 * (N : ℝ) ^ 3 + 1)) →
  ∀ (T : Type) (L : LevCh D T) (t₀ : T), L.Is t₀ → ∀ (t : T) (θ : InfFam D), IsInfFam θ →
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
  ∀ (th : ∀ k, GA D (Yc D k) → GA D (Yc D (k + 1)) → (WO (Yc D k) (Yc D (k + 1)) → ℂ) → ℂ),
    IsChainKernel ψ (L.mu t) L.eta D.R.m (Yc D) th →
  ∀ (ν : ∀ k, Measure (GA D (Yc D k))) [∀ k, (ν k).IsHaarMeasure] [∀ k, (ν k).IsMulRightInvariant]
    (𝓕 : ∀ k, Set (GA D (Yc D k))), (∀ k, IsFundamentalDomain (GQ (Yc D k)) (𝓕 k) (ν k)) →
  ∀ (σ : Submodule ℂ (DividedPowerChartLift (Yc D 0) (ν 0))) (hσ : IsCuspIrr (Yc D 0) (ν 0) σ),
    HasRealType σ θ (parA (tparRec D) 0) → (∀ v ∉ typePlaces D, SphAt hσ v) →
  ∀ k, 1 ≤ k → k < D.R.m → ∀ (π : Submodule ℂ (DividedPowerChartLift (Yc D k) (ν k))) (hπ : IsCuspIrr (Yc D k) (ν k) π),
    MeetsLift θ ψ th ν 𝓕 σ k π →
  ∀ v ∉ badPlaces L t, IsSplit (E := D.host.E) v →
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v) (B : Multiset ℂˣ),
    HasParam D.sp.cm.sig (Yc D 0).gram (frameLat (Yc D 0)) h (locRep hσ v) B →
    HasParam D.sp.cm.sig (Yc D k).gram (frameLat (Yc D k)) h (locRep hπ v) (liftParam (L.mu t) L.eta k w B)

section Zero

variable {V : HSp D} {ν : Measure (GA D V)} [ν.IsHaarMeasure] [ν.IsMulRightInvariant]
  {σ π : Submodule ℂ (DividedPowerChartLift V ν)}

def funsOf (σ : Submodule ℂ (DividedPowerChartLift V ν)) : Submodule ℂ (GA D V → ℂ) where
  carrier := {F | ∃ h : MemL2Quotient (GQ V) ν F, h.toL2 ∈ σ}
  zero_mem' := ⟨⟨fun _ _ _ => rfl, MemLp.zero⟩, by
    convert σ.zero_mem using 1
    exact MemLp.toLp_zero _⟩
  add_mem' := fun ⟨h, e⟩ ⟨h', e'⟩ => ⟨⟨fun γ hγ g => congrArg₂ (· + ·) (h.1 γ hγ g) (h'.1 γ hγ g), h.2.add h'.2⟩,
    σ.add_mem e e'⟩
  smul_mem' := fun c _ ⟨h, e⟩ => ⟨⟨fun γ hγ g => congrArg (c • ·) (h.1 γ hγ g), h.2.const_smul c⟩, σ.smul_mem c e⟩

end Zero

end GlobalTheory.NoExcl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoInvariantPairingSmallerFockDiscreteSeriesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.no_invariant_pairing_smaller_fock_discreteSeries : ∀ (X : ProvA) (p q r s : ℕ) (lam' : Ix r s → ℚ), Formalism.MainNotions.SchurIrreducible.AdmGK (X.ds r s lam').HK → NoLow X p q lam' → ∀ i : ℕ, 1 ≤ i → i ≤ p → i ≤ q → ∀ b : Formalism.BasicNotions.TH.Pol (p - i) (q - i) r s →ₗ[ℂ] (X.ds r s lam').HK.V →ₛₗ[starRingEnd ℂ] ℂ, (∀ Z ∈ upq r s, ∀ P y, b (fockAct2 (p - i) (q - i) r s Z P) y + b P ((X.ds r s lam').HK.act Z y) = 0) → b = 0 := by
  first | exact @GlobalTheory.NoLowPairing.no_pairing_of_noLow | exact GlobalTheory.NoLowPairing.no_pairing_of_noLow | (intros; apply GlobalTheory.NoLowPairing.no_pairing_of_noLow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormLevelIndicatorCoefficientTestLeDecayStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_levelIndicatorCoefficientTest_le_decay : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (v : ∀ τ, M.H τ), KDecay M v → ∀ b : ∀ τ, M.H τ, (∀ τ, b τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) → ∃ C : ℝ, 0 ≤ C ∧ ∀ x : GA D V, ‖coef θ M K v b x‖ ≤ C * ∏ τ, ((1 + hsn (cmp θ τ x)) ^ (2 * V.rank ^ 2 + 1))⁻¹ := by
  first | exact @GlobalTheory.PoinTerm.norm_coef_le | exact GlobalTheory.PoinTerm.norm_coef_le | (intros; apply GlobalTheory.PoinTerm.norm_coef_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneLeNormRationalTranslateStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_le_norm_rational_translate : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (B : Fr V) (x : GA D Y) (γ : GA D V) (z : Fin V.rank → D.host.E), γ ∈ GQ V → mt V γ *ᵥ ratV (zv d) = ratV z → ∀ τ, 1 ≤ nrm θ B (stabilizerEmbedding d x) τ z := by
  first | exact @GlobalTheory.SepPer.MajDom.one_le_nrm | exact GlobalTheory.SepPer.MajDom.one_le_nrm | (intros; apply GlobalTheory.SepPer.MajDom.one_le_nrm <;> assumption)
end

