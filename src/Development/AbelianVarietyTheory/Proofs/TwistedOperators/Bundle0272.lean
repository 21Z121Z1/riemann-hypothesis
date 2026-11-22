import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0182
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFinWeil
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHomLatticeIffIntegralMatrixSplitChart
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0328
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0327
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0179
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0206
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0331
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0216
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0257
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0260
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0254
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0259
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.Bundle0003
import Formalism.RealPlaceAnalysis.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0253
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0255
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianSkewAdjointMemAdjointHomLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.AdjLatO

variable {D : D7}

theorem incA_mul_tmul' (g e : D.host.E) (x : AF D.host.F) :
    incA D g * (x ⊗ₜ[D.host.F] e) = x ⊗ₜ[D.host.F] (g * e) := by
  change ((1 : AF D.host.F) ⊗ₜ[D.host.F] g) * _ = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem tmul_mul_incA' (g e : D.host.E) (x : AF D.host.F) :
    (x ⊗ₜ[D.host.F] e) * incA D g = x ⊗ₜ[D.host.F] (e * g) := by
  change _ * ((1 : AF D.host.F) ⊗ₜ[D.host.F] g) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]

def tensM (x : AF D.host.F) {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) : Mx D m n :=
  M.map fun e => x ⊗ₜ[D.host.F] e

theorem rat_mul_tensM (x : AF D.host.F) {l m n : ℕ} (G : Matrix (Fin l) (Fin m) D.host.E)
    (M : Matrix (Fin m) (Fin n) D.host.E) : rat G ⬝ tensM x M = tensM x (G * M) := by
  ext i j
  simp only [tensM, rat, Matrix.mul_apply, Matrix.map_apply, incA_mul_tmul', TensorProduct.tmul_sum]

theorem tensM_mul_rat (x : AF D.host.F) {l m n : ℕ} (M : Matrix (Fin l) (Fin m) D.host.E)
    (G : Matrix (Fin m) (Fin n) D.host.E) : tensM x M ⬝ rat G = tensM x (M * G) := by
  ext i j
  simp only [tensM, rat, Matrix.mul_apply, Matrix.map_apply, tmul_mul_incA', TensorProduct.tmul_sum]

theorem adj_tensM (x : AF D.host.F) {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) :
    adj (tensM x M) = tensM x Mᴴ := by
  ext i j; rfl

theorem xi0_inv_smul_starAdj (S T : HSp D) (x : WO S T) :
    incA D D.host.xi0⁻¹ • GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj S T x = giA S ⬝ (adj x ⬝ gA T) := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj, smul_smul, ← map_mul, inv_mul_cancel₀ GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero, map_one, one_smul]

def genT (T : HSp D) {n : ℕ} (x : AF D.host.F) (t : Fin T.rank → D.host.E) (u : Fin n → D.host.E) :
    Matrix (Fin n) (Fin T.rank) (AE D) :=
  Matrix.of fun p q => x ⊗ₜ[D.host.F] (u p * ∑ i, star (t i) * T.gram i q)

theorem genT_add (T : HSp D) {n : ℕ} (x : AF D.host.F) (t : Fin T.rank → D.host.E) (u v : Fin n → D.host.E) :
    genT T x t (u + v) = genT T x t u + genT T x t v := by
  ext p q
  simp only [genT, Matrix.of_apply, Matrix.add_apply, Pi.add_apply, add_mul, TensorProduct.tmul_add]

theorem genT_zero (T : HSp D) {n : ℕ} (x : AF D.host.F) (t : Fin T.rank → D.host.E) :
    genT T x t (0 : Fin n → D.host.E) = 0 := by
  ext p q
  simp only [genT, Matrix.of_apply, Pi.zero_apply, zero_mul, TensorProduct.tmul_zero, Matrix.zero_apply]

theorem starAdj_gen (S T : HSp D) (x : AF D.host.F) (a : D.host.E) (s : Fin S.rank → D.host.E)
    (t : Fin T.rank → D.host.E) :
    incA D D.host.xi0⁻¹ • GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj S T
        (Matrix.of fun i j => x ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j)) =
      genT T x t (star a • s) := by
  have e : (Matrix.of fun i j => x ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) : WO S T) =
      tensM x ((Matrix.of fun i k => a * t i * star (s k)) * S.gram) := by
    ext i j
    simp only [tensM, Matrix.map_apply, Matrix.mul_apply, Matrix.of_apply, Finset.mul_sum, mul_assoc]
  rw [xi0_inv_smul_starAdj, e, adj_tensM, Matrix.conjTranspose_mul, gram_conjTranspose, gA, tensM_mul_rat, giA,
    rat_mul_tensM, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (gram_isUnit_det S), Matrix.one_mul]
  ext p q
  simp only [tensM, genT, Matrix.map_apply, Matrix.mul_apply, Matrix.of_apply, Matrix.conjTranspose_apply,
    Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [star_mul', star_star]
  ring

theorem genT_mem_of_mem_span (S T : HSp D) (LS' : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (P : GlobalTheory.FinPl.Pl D → Prop)
    (α : Af D.host.F) (hα : α ∈ intAf D.host.F) (hP : ∀ v, ¬ P v → evalV D.host.F v α = 0)
    (t : Fin T.rank → D.host.E) (ht : t ∈ LT) (u : Fin S.rank → D.host.E)
    (hu : u ∈ Submodule.span (𝓞 D.host.E) {y | ∃ a' ∈ D.host.AA, ∃ s' ∈ LS', y = a' • s'}) :
    genT T (pairA D.host.F 0 α) t u ∈ latO T S (LT : Set _) (LS' : Set _) P := by
  suffices h : ∀ c : 𝓞 D.host.E, genT T (pairA D.host.F 0 α) t (c • u) ∈ latO T S (LT : Set _) (LS' : Set _) P by
    simpa using h 1
  induction hu using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a', ha', s', hs', rfl⟩ := hy
    intro c
    apply AddSubgroup.subset_closure
    refine ⟨α, hα, hP, a', ha', t, ht, c • s', LS'.smul_mem c hs', ?_⟩
    ext p q
    simp only [genT, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
    congr 1
    rw [Algebra.smul_def, Algebra.smul_def]
    ring
  | zero => intro c; rw [smul_zero, genT_zero]; exact zero_mem _
  | add y z _ _ hy hz => intro c; rw [smul_add, genT_add]; exact add_mem (hy c) (hz c)
  | smul r y _ hy => intro c; rw [smul_smul]; exact hy (c * r)

theorem incA_inv_xi0_smul_starAdj_mem_latO : ∀ (D : D7) (S T : HSp D) (LS LS' : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (P : GlobalTheory.FinPl.Pl D → Prop), (∀ a ∈ D.host.AA, ∀ s ∈ LS, star a • s ∈ Submodule.span (𝓞 D.host.E) {y | ∃ a' ∈ D.host.AA, ∃ s' ∈ LS', y = a' • s'}) → ∀ x ∈ latO S T (LS : Set _) (LT : Set _) P, incA D D.host.xi0⁻¹ • GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj S T x ∈ latO T S (LT : Set _) (LS' : Set _) P := by
  intro D S T LS LS' LT P hA x hx
  induction hx using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hw
    rw [starAdj_gen]
    exact genT_mem_of_mem_span S T LS' LT P α hα hP t ht _ (hA a ha s hs)
  | zero =>
    rw [xi0_inv_smul_starAdj, adj_zero, Matrix.zero_mul, Matrix.mul_zero]; exact zero_mem _
  | add y z _ _ hy hz =>
    rw [xi0_inv_smul_starAdj] at hy hz ⊢
    rw [adj_add, Matrix.add_mul, Matrix.mul_add]; exact add_mem hy hz
  | neg y _ hy =>
    rw [xi0_inv_smul_starAdj] at hy ⊢
    rw [adj_neg, Matrix.neg_mul, Matrix.mul_neg]; exact neg_mem hy

end GlobalTheory.AdjLatO
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IndexMovedHomLatticeSplitPlaceChart
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open GlobalTheory.SplitHecke GlobalTheory.LFun.ConjPlace GlobalTheory.AdelicU GlobalTheory.LFun.SplitTie

namespace GlobalTheory.SplitIdx

theorem half_index : ∀ (D : D7) (S T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsSplit (E := D.host.E) v → ∀ e, IsSplitChart D.sp.cm.sig T.gram (frameLat T) h e → ∀ ϖ, IsUnifV D.host.E w ϖ → ∀ (d : Fin T.rank → ℤ) (t : GL (Fin T.rank) (w.adicCompletion D.host.E)), t.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KGL w T.rank, ∀ k₂ ∈ KGL w T.rank, ∀ ε : AE D, Formalism.L2.NTheta.IsIdemAt ε w → (halfLat S T ε).relIndex ((halfLat S T ε).map (actL S T (embV T v (e.symm (k₁ * t * k₂))))) = qV D.host.E w ^ (S.rank * (∑ i, max (-d i) 0).toNat) := by
  intro D S T v w h hs e he ϖ hϖ d t ht k₁ hk₁ k₂ hk₂ ε hε
  obtain ⟨φ, hφ, ⟨BS, hBS⟩, BT, hBT, ψ, hψ, hq, κ, hκ, hco⟩ := GlobalTheory.T.splitPlace_chart_frames_conj_maximalCompact D S T v w h hs e he ε hε
  rw [GlobalTheory.T.relIndex_half_action_splitPlace_frames D S T v φ ε hφ BS BT hBS hBT, hco, ← hq]
  have hback : ∀ x : GL (Fin T.rank) (w.adicCompletion D.host.E),
      GlobalTheory.LFun.SplitTie.glEquiv T.rank ψ
        (Matrix.GeneralLinearGroup.map (ψ.symm : w.adicCompletion D.host.E →+* Fv D.host.F v) x) = x := by
    intro x
    ext i j
    simp [GlobalTheory.LFun.SplitTie.glEquiv]
  have hK : ∀ x ∈ KGL w T.rank,
      Matrix.GeneralLinearGroup.map (ψ.symm : w.adicCompletion D.host.E →+* Fv D.host.F v) x ∈ KGL v T.rank := by
    intro x hx
    rw [GlobalTheory.LFun.SplitTie.mem_KGL_iff hψ, hback]
    exact hx
  have hunif : IsUnifV D.host.F v (ψ.symm ϖ) := by
    have h1 := hψ (ψ.symm ϖ)
    rw [RingEquiv.apply_symm_apply] at h1
    show Valued.v _ = _
    rw [← h1]
    exact hϖ
  have hdiag : (Matrix.GeneralLinearGroup.map (ψ.symm : w.adicCompletion D.host.E →+* Fv D.host.F v) t).1 =
      Matrix.diagonal (fun i => ψ.symm ϖ ^ d i) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [ht, map_zpow₀]
    · simp [ht, Matrix.diagonal_apply, hij]
  have hsplit : ∀ a b c : GL (Fin T.rank) (w.adicCompletion D.host.E),
      κ⁻¹ * Matrix.GeneralLinearGroup.map (ψ.symm : w.adicCompletion D.host.E →+* Fv D.host.F v) (a * b * c) * κ =
        (κ⁻¹ * Matrix.GeneralLinearGroup.map (ψ.symm : w.adicCompletion D.host.E →+* Fv D.host.F v) a) *
          Matrix.GeneralLinearGroup.map (ψ.symm : w.adicCompletion D.host.E →+* Fv D.host.F v) b *
          (Matrix.GeneralLinearGroup.map (ψ.symm : w.adicCompletion D.host.E →+* Fv D.host.F v) c * κ) := by
    intro a b c
    simp only [map_mul, mul_assoc]
  rw [hsplit]
  exact GlobalTheory.T.relIndex_integralMatrices_cartanDouble_coset v T.rank S.rank (ψ.symm ϖ) hunif d _ hdiag _ (mul_mem (inv_mem hκ) (hK k₁ hk₁)) _
    (mul_mem (hK k₂ hk₂) hκ)

theorem index_moved_split : ∀ (D : D7) (S T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsSplit (E := D.host.E) v → ∀ e, IsSplitChart D.sp.cm.sig T.gram (frameLat T) h e → ∀ ϖ, IsUnifV D.host.E w ϖ → ∀ (d : Fin T.rank → ℤ) (t : GL (Fin T.rank) (w.adicCompletion D.host.E)), t.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KGL w T.rank, ∀ k₂ ∈ KGL w T.rank, GlobalTheory.FinWeil.idx (GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)) ((GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)).map (GlobalTheory.FinWeilO.rhoF S T (1, embV T v (e.symm (k₁ * t * k₂))))) = qV D.host.E w ^ (S.rank * (∑ i, |d i|).toNat) := by
  intro D S T v w h hs e he ϖ hϖ d t ht k₁ hk₁ k₂ hk₂
  obtain ⟨τ, hτ⟩ := GlobalTheory.LFun.SplitChart.exists_splitPrime_eq (GlobalTheory.AdelicU.isCMExt_host D) hs h
  obtain ⟨ε, hε, -⟩ := GlobalTheory.EmbChart.exists_isIdemAt_chart (D := D) τ
  rw [hτ] at hε
  obtain ⟨w', hne, hunder, -⟩ := GlobalTheory.LFun.SplitChart.exists_conj_place (GlobalTheory.AdelicU.isCMExt_host D) h hs
  have h' : w'.under (𝓞 D.host.F) = v := (hunder w').2 (Or.inr rfl)
  obtain ⟨c, hc, hq', -, he'⟩ := GlobalTheory.LFun.ConjPlace.exists_conj_chart (GlobalTheory.AdelicU.isCMExt_host D)
    (GlobalTheory.Mem.VolExists.isHermND D.sp.cm T) (GlobalTheory.AdelicU.SelfDual.isSelfDualAt_frameLat D T v) hne h h' he
  have hε' := GlobalTheory.T.isIdemAt_conj_of_other_prime_over_split D v w w' hne h h' ε hε
  rw [GlobalTheory.T.relIndex_movedHomLattice_eq_prod_halves_splitPlace D S T ε hε.1 _ (GlobalTheory.T.suppAt_unitaryGroupLocalToAdelicEmbedding D T v w h ε hε (e.symm (k₁ * t * k₂))),
    half_index D S T v w h hs e he ϖ hϖ d t ht k₁ hk₁ k₂ hk₂ ε hε]
  have hO := GlobalTheory.LFun.ConjPlace.map_mem_Ov_iff c hc
  have hk : ∀ k ∈ KGL w T.rank, GlobalTheory.LFun.ConjPlace.invT c T.rank k ∈ KGL w' T.rank := fun k hk =>
    (GlobalTheory.LFun.ConjPlace.mem_iff_invT c hO k).1 hk
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    simp [IsUnifV] at hϖ
  have hmul : t.1 * Matrix.diagonal (fun i => ϖ ^ (-d i)) = 1 := by
    rw [ht, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [← zpow_add₀ hϖ0, add_neg_cancel, zpow_zero]
  have hinv : (t⁻¹).1 = Matrix.diagonal (fun i => ϖ ^ (-d i)) := Units.inv_eq_of_mul_eq_one_right hmul
  have hdiag : (GlobalTheory.LFun.ConjPlace.invT c T.rank t).1 = Matrix.diagonal (fun i => c ϖ ^ (-d i)) := by
    ext i j
    rw [GlobalTheory.LFun.ConjPlace.invT_val, hinv]
    by_cases hij : i = j
    · subst hij
      simp [map_zpow₀]
    · simp [Matrix.diagonal_apply, hij, Ne.symm hij]
  have hunif : IsUnifV D.host.E w' (c ϖ) := by
    show Valued.v (c ϖ) = _
    rw [hc]
    exact hϖ
  have hsym : e.symm (k₁ * t * k₂) = (e.trans (GlobalTheory.LFun.ConjPlace.invT c T.rank)).symm
      (GlobalTheory.LFun.ConjPlace.invT c T.rank k₁ * GlobalTheory.LFun.ConjPlace.invT c T.rank t *
        GlobalTheory.LFun.ConjPlace.invT c T.rank k₂) := by
    rw [MulEquiv.symm_trans_apply, ← map_mul, ← map_mul, MulEquiv.symm_apply_apply]
  have hconj := half_index D S T v w' h' hs _ he' (c ϖ) hunif (fun i => -d i) _ hdiag _ (hk k₁ hk₁) _ (hk k₂ hk₂)
    (cA D ε) hε'
  rw [← hsym] at hconj
  rw [hconj, hq']
  simp only [neg_neg]
  rw [← pow_add, ← mul_add]
  have hA : 0 ≤ ∑ i, max (-d i) 0 := Finset.sum_nonneg fun i _ => le_max_right _ _
  have hB : 0 ≤ ∑ i, max (d i) 0 := Finset.sum_nonneg fun i _ => le_max_right _ _
  rw [← Int.toNat_add hA hB, ← Finset.sum_add_distrib]
  congr 3
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [add_comm]
  exact max_zero_add_max_neg_zero_eq_abs_self (d i)

end GlobalTheory.SplitIdx

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InducedIntertwiningIntegralNonzero
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace

noncomputable section
namespace GlobalTheory.IntertwiningDense
variable {n : ℕ} {ε : Fin n → Bool}

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem inG_of_exp_mem {X : Matrix (Fin n) (Fin n) ℂ} (h : ∀ t : ℝ, NormedSpace.exp (t • X) ∈ UJset ε) :
    inG ε X := by
  have h1 := hasDerivAt_exp_smul_const (𝕂 := ℝ) Xᴴ (0 : ℝ)
  have h2 := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  have h3 : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • Xᴴ) * Jm ε * NormedSpace.exp (t • X)) _ 0 :=
    (h1.mul_const (Jm ε)).mul h2
  have hc : (fun t : ℝ => NormedSpace.exp (t • Xᴴ) * Jm ε * NormedSpace.exp (t • X)) = fun _ => Jm ε := by
    funext t
    have := h t
    rw [show t • Xᴴ = (t • X)ᴴ by rw [conjTranspose_smul, star_trivial], Matrix.exp_conjTranspose]
    exact this
  rw [hc] at h3
  have := h3.unique (hasDerivAt_const (0 : ℝ) (Jm ε))
  simpa [inG] using this
end

section Finite

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def transl (f : UJ ε → V) : Submodule ℂ (UJ ε → V) :=
  Submodule.span ℂ {φ | ∃ k ∈ KG ε, φ = fun g => f (g * k)}

theorem transl_mem (f : UJ ε → V) {k : UJ ε} (hk : k ∈ KG ε) : (fun g => f (g * k)) ∈ transl f :=
  Submodule.subset_span ⟨k, hk, rfl⟩

theorem isKFinFun_of_mem {f : UJ ε → V} (U : Submodule ℂ (UJ ε → V)) [FiniteDimensional ℂ U]
    (h : ∀ k ∈ KG ε, (fun g => f (g * k)) ∈ U) : IsKFinFun f :=
  Submodule.finiteDimensional_of_le (Submodule.span_le.2 (by rintro φ ⟨k, hk, rfl⟩; exact h k hk))

theorem isKFinFun_add {f f' : UJ ε → V} (h : IsKFinFun f) (h' : IsKFinFun f') : IsKFinFun (f + f') := by
  haveI : FiniteDimensional ℂ (transl f) := h
  haveI : FiniteDimensional ℂ (transl f') := h'
  exact isKFinFun_of_mem (transl f ⊔ transl f') fun k hk =>
    Submodule.add_mem_sup (transl_mem f hk) (transl_mem f' hk)

theorem isKFinFun_smul {f : UJ ε → V} (h : IsKFinFun f) (c : ℂ) : IsKFinFun (c • f) := by
  haveI : FiniteDimensional ℂ (transl f) := h
  exact isKFinFun_of_mem (transl f) fun k hk => (transl f).smul_mem c (transl_mem f hk)

theorem isKFinFun_transl {f : UJ ε → V} (h : IsKFinFun f) {k₀ : UJ ε} (hk₀ : k₀ ∈ KG ε) :
    IsKFinFun fun g => f (g * k₀) := by
  haveI : FiniteDimensional ℂ (transl f) := h
  exact isKFinFun_of_mem (transl f) fun k hk => by
    simpa only [mul_assoc] using transl_mem f ((KG ε).mul_mem hk hk₀)

end Finite

section Integral

variable (D : Datum ε) (ν : Measure (UJ ε))

theorem isIntegral_zero : D.IsIntegral ν 0 0 := fun x v _ => by simp

variable {D ν}

theorem IsIntegral.add {f h f' h' : UJ ε → D.V} (a : D.IsIntegral ν f h) (b : D.IsIntegral ν f' h') :
    D.IsIntegral ν (f + f') (h + h') := fun x v hv => by
  obtain ⟨i1, e1⟩ := a x v hv
  obtain ⟨i2, e2⟩ := b x v hv
  refine ⟨by simp only [Pi.add_apply, inner_add_right]; exact i1.add i2, ?_⟩
  simp only [Pi.add_apply, inner_add_right, e1, e2]
  exact (integral_add i1 i2).symm

theorem IsIntegral.smul {f h : UJ ε → D.V} (a : D.IsIntegral ν f h) (c : ℂ) :
    D.IsIntegral ν (c • f) (c • h) := fun x v hv => by
  obtain ⟨i1, e1⟩ := a x v hv
  refine ⟨by simpa only [Pi.smul_apply, inner_smul_right] using i1.const_mul c, ?_⟩
  simp only [Pi.smul_apply, inner_smul_right, e1]
  exact (integral_const_mul c _).symm

theorem IsIntegral.transl {f h : UJ ε → D.V} (a : D.IsIntegral ν f h) (k : UJ ε) :
    D.IsIntegral ν (fun g => f (g * k)) (fun g => h (g * k)) := fun x v hv => by
  simpa only [mul_assoc] using a (x * k) v hv

end Integral

def oppDatum (D : Datum ε) : Datum ε where
  a := D.a
  j := D.j
  W := opp ε D.W
  flag := isIsoFlag_opp D.flag
  pos := D.pos
  V := D.V
  σ := D.σ
  temp := by rw [leviOne_opp]; exact D.temp
  s := -D.s

theorem oppDatum_M (D : Datum ε) : (oppDatum D).M = D.M := leviOne_opp

theorem isKFinIn_one {D : Datum ε} {h : UJ ε → D.V} (hh : h ∈ D.oppFns) (hk : IsKFinFun h) :
    IsKFinIn D.M D.σ (h 1) := by
  have := (GlobalTheory.T.induced_k_finite_restriction n ε (oppDatum D) h hh hk).2.1
  rwa [oppDatum_M] at this

theorem exists_ne_zero_K {D : Datum ε} {h : UJ ε → D.V} (hh : h ∈ D.oppFns) (hk : IsKFinFun h) (h0 : h ≠ 0) :
    ∃ k ∈ KG ε, h k ≠ 0 :=
  (GlobalTheory.T.induced_k_finite_restriction n ε (oppDatum D) h hh hk).2.2 h0

theorem eq_zero_of_K {D : Datum ε} {φ : UJ ε → D.V} (hφ : φ ∈ D.fns) (h : ∀ k ∈ KG ε, φ k = 0) : φ = 0 := by
  funext g
  obtain ⟨k, hk, hp⟩ := GlobalTheory.RealIwasawa.exists_stab_mul_compact D.flag g
  obtain ⟨u, hu, m, hm, x, t, ht, e⟩ := exists_langlands_decomp D.flag D.pos hp
  have hkK : k ∈ KG ε := by rw [← SetLike.mem_coe, KG_eq]; exact hk
  have : g = u * m * t * k := by rw [← e]; group
  rw [this, (mem_indFun_top.1 hφ).2 u hu m hm x t ht k, h k hkK, map_zero, smul_zero]
  rfl

theorem ι_injective (I : IndModule ε) : Function.Injective I.ι := by
  haveI : IsProbabilityMeasure (muK ε) := ⟨Measure.haarMeasure_self⟩
  intro a b hab
  have h0 : I.ι (a - b) = 0 := by rw [map_sub, hab, sub_self]
  have hn := I.model.norm_sq (a - b)
  rw [h0, norm_zero] at hn
  have hc : Continuous fun k : KG ε => ‖(a - b).1 k‖ ^ 2 :=
    (((mem_indFun_top.1 (a - b).2).1.comp continuous_subtype_val).norm.pow 2)
  have hK : ∀ k ∈ KG ε, (a - b).1 k = 0 := fun k hk => by
    by_contra hne
    have := hc.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := muK ε) (x := ⟨k, hk⟩)
      (isClosed_tsupport _).isCompact (fun _ => by positivity) (by simpa using hne)
    linarith
  have := eq_zero_of_K (D := I.toDatum) (a - b).2 hK
  exact sub_eq_zero.1 (Subtype.ext this)

def valSpace (I : IndModule ε) (ν : Measure (UJ ε)) : Submodule ℂ I.V where
  carrier := {w | ∃ f ∈ I.fns, IsKFinFun f ∧ ∃ h ∈ I.oppFns, IsKFinFun h ∧ I.IsIntegral ν f h ∧ h 1 = w}
  zero_mem' := ⟨0, zero_mem _, isKFinFun_of_mem ⊥ fun _ _ => (Submodule.mem_bot ℂ).2 (funext fun _ => rfl),
    0, zero_mem _, isKFinFun_of_mem ⊥ fun _ _ => (Submodule.mem_bot ℂ).2 (funext fun _ => rfl),
    isIntegral_zero _ _, rfl⟩
  add_mem' := by
    rintro _ _ ⟨f, hf, hfk, h, hh, hhk, hi, rfl⟩ ⟨f', hf', hfk', h', hh', hhk', hi', rfl⟩
    exact ⟨f + f', add_mem hf hf', isKFinFun_add hfk hfk', h + h', add_mem hh hh', isKFinFun_add hhk hhk',
      IsIntegral.add hi hi', rfl⟩
  smul_mem' := by
    rintro c _ ⟨f, hf, hfk, h, hh, hhk, hi, rfl⟩
    exact ⟨c • f, Submodule.smul_mem _ c hf, isKFinFun_smul hfk c, c • h, Submodule.smul_mem _ c hh,
      isKFinFun_smul hhk c, IsIntegral.smul hi c, rfl⟩

theorem one_mem_flagN {a : ℕ} (W : Flag n a) : (1 : UJ ε) ∈ flagN ε W :=
  have h1 : uMat (1 : UJ ε) = 1 := rfl
  ⟨fun i y _ => by simp [h1], fun y _ => by simp [h1]⟩

theorem intertwining_values_dense : GlobalTheory.Published.HarishChandraAnalyticity → GlobalTheory.Published.LanglandsClassification →
    ∀ (n : ℕ) (ε : Fin n → Bool) (I : IndModule ε), I.Positive → ∀ ν : Measure (UJ ε), IsHaarSub I.Nbar ν →
      ∀ v : I.V, v ≠ 0 → ∃ f ∈ I.fns, IsKFinFun f ∧ ∃ h ∈ I.oppFns, I.IsIntegral ν f h ∧ ⟪v, h 1⟫_ℂ ≠ 0 := by
  intro hHC hLC n ε I hpos ν hν v hv
  obtain ⟨hInd, hQuot, -⟩ := hLC
  obtain ⟨-, -, hgk, hiff, hder, -⟩ := hInd n ε I
  obtain ⟨hex, hrd, Z, hZ, hZgk, hZne, -, -⟩ := hQuot n ε I hpos ν hν
  have hS0 : valSpace I ν ≠ ⊥ := by
    obtain ⟨w, hw, hwZ⟩ : ∃ w ∈ kFinVec ε I.ρ, w ∉ Z := by
      by_contra hcon
      push_neg at hcon
      exact hZne (le_antisymm (fun w hw => hZgk.kFin w hw) hcon)
    obtain ⟨f, hfk, rfl⟩ := (hiff w).1 hw
    obtain ⟨h, hh, hhk, hi⟩ := hex f.1 f.2 hfk
    have hne : h ≠ 0 := by
      rintro rfl
      apply hwZ
      have : I.ι f ∈ (Z : Set I.H) := by rw [hZ]; exact ⟨f, hfk, rfl, hi⟩
      exact this
    obtain ⟨k, hk, hhk0⟩ := exists_ne_zero_K hh hhk hne
    intro hbot
    have hmem : h k ∈ valSpace I ν := ⟨fun g => f.1 (g * k), indFun_mul_right f.2 trivial,
      isKFinFun_transl hfk hk, fun g => h (g * k), indFun_mul_right hh trivial, isKFinFun_transl hhk hk,
      IsIntegral.transl hi k, by simp⟩
    rw [hbot, Submodule.mem_bot] at hmem
    exact hhk0 hmem
  have hlie : ∀ X : Matrix (Fin n) (Fin n) ℂ, (∀ t : ℝ, NormedSpace.exp (t • X) ∈ mats (leviOne ε I.W)) →
      ∀ w ∈ valSpace I ν, ∃ w' ∈ valSpace I ν,
        HasDerivAt (fun t : ℝ => I.σ (NormedSpace.exp (t • X)) w) w' 0 := by
    rintro X hX _ ⟨f, hf, hfk, h, hh, hhk, hi, rfl⟩
    have hXg : X ∈ lieSet ε := inG_of_exp_mem fun t => by
      obtain ⟨y, -, hy⟩ := hX t
      rw [← hy]
      exact y.2
    obtain ⟨f', hrf, hdf⟩ := hder ⟨f, hf⟩ hfk X hXg
    have hf'k : IsKFinFun f'.1 := by
      have h1 : IsKFin ε I.ρ (I.ι ⟨f, hf⟩) := (hiff _).2 ⟨⟨f, hf⟩, hfk, rfl⟩
      have h2 : IsKFin ε I.ρ (I.ι f') := by rw [← hdf]; exact hgk.lieStable X hXg _ h1
      obtain ⟨f'', hk'', he⟩ := (hiff _).1 h2
      rwa [ι_injective I he] at hk''
    obtain ⟨h', hh', hh'k, hi'⟩ := hex f'.1 f'.2 hf'k
    have hrh := hrd f hf hfk X hXg f'.1 h h' hrf hi hi'
    refine ⟨h' 1, ⟨f'.1, f'.2, hf'k, h', hh', hh'k, hi', rfl⟩, ?_⟩
    have e : (fun t : ℝ => h (1 * expG ε X t)) = fun t : ℝ => I.σ (NormedSpace.exp (t • X)) (h 1) := by
      funext t
      obtain ⟨y, hy, hyX⟩ := hX t
      have hyt : expG ε X t = y := by
        apply Subtype.ext
        apply Units.ext
        have := toM_expG ε X t hXg
        rw [Complex.coe_smul] at this
        exact this.trans hyX.symm
      rw [one_mul, hyt, ← hyX]
      have hy' : y ∈ leviOne ε (opp ε I.W) := by rw [leviOne_opp]; exact hy
      have := (mem_indFun_top.1 hh).2 1 (one_mem_flagN _) y hy' 0 1 isSplit_one 1
      simpa [pairing] using this
    have := hrh 1
    rwa [e] at this
  have hd := hHC.2 n ε I.a I.j I.W I.flag I.pos I.V I.σ I.temp.2.2.1 I.temp.2.1 (valSpace I ν) hS0
    (fun w ⟨f, hf, hfk, h, hh, hhk, hi, hw⟩ => hw ▸ isKFinIn_one hh hhk) hlie
  by_contra hcon
  push_neg at hcon
  have hz : ((valSpace I ν : Submodule ℂ I.V) : Set I.V) ⊆ {w | ⟪v, w⟫_ℂ = 0} :=
    fun w ⟨f, hf, hfk, h, hh, hhk, hi, hw⟩ => hw ▸ hcon f hf hfk h hh hi
  have hcl : IsClosed {w : I.V | ⟪v, w⟫_ℂ = 0} :=
    isClosed_eq (continuous_const.inner continuous_id) continuous_const
  have : ⟪v, v⟫_ℂ = 0 := closure_minimal hz hcl (hd v)
  exact hv (inner_self_eq_zero.1 this)

end GlobalTheory.IntertwiningDense

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralSiegelConeInvModulusLtTopWeilStatement
section
open MeasureTheory
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_siegelCone_inv_modulus_lt_top_weil : ∀ (F : Type) [Field F] [NumberField F] (n r d : ℕ) {c : ℝ}, 0 < c → d < 2 * (n - r) → ∫⁻ t in GlobalTheory.SiegelSet.cone r c, ENNReal.ofReal (∏ i, t i ^ (Module.finrank ℚ F * d)) * ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus F n t * ∏ i, t i)⁻¹) < ⊤ := by
  first | exact @GlobalTheory.SiegelSet.lintegral_cone_modulus_lt_top | exact GlobalTheory.SiegelSet.lintegral_cone_modulus_lt_top | (intros; apply GlobalTheory.SiegelSet.lintegral_cone_modulus_lt_top <;> assumption)
end

