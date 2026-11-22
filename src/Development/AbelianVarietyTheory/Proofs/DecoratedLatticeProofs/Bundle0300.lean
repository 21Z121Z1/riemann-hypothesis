import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0107
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0100
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TraceInverseGramConjSmulEq
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0289
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1516
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0916
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1557
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0294
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateHalfLineMultipleMemIffIntegral
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.ConjHalf

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem vecMul_jA_eq_zero (p : SplitPt D k) {S₀ A L : HSp D} (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E) :
    (fun i => p.pr (incA D (star ((HSpace.gram S₀ *ᵥ vecB o ζ) i)))) ᵥ* o.jA.map p.pr = 0 := by
  have h0 : o.iAᴴ * HSpace.gram S₀ * o.iB = 0 := by
    have := congrArg Matrix.conjTranspose o.orth
    simpa [Matrix.conjTranspose_mul, Matrix.mul_assoc, gram_conjTranspose] using this
  have h1 : o.iAᴴ *ᵥ (HSpace.gram S₀ *ᵥ vecB o ζ) = 0 := by
    rw [vecB, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h0, Matrix.zero_mulVec]
  funext l
  have h2 : ∑ i, star ((HSpace.gram S₀ *ᵥ vecB o ζ) i) * o.iA i l =
      star ((o.iAᴴ *ᵥ (HSpace.gram S₀ *ᵥ vecB o ζ)) l) := by
    rw [Matrix.mulVec, dotProduct, star_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.conjTranspose_apply, star_mul', star_star, mul_comm]
  have h3 : ((fun i => p.pr (incA D (star ((HSpace.gram S₀ *ᵥ vecB o ζ) i)))) ᵥ* o.jA.map p.pr) l =
      (p.pr.comp (incA D)) (∑ i, star ((HSpace.gram S₀ *ᵥ vecB o ζ) i) * o.iA i l) := by
    show ∑ i, (p.pr.comp (incA D)) (star ((HSpace.gram S₀ *ᵥ vecB o ζ) i)) * (p.pr.comp (incA D)) (o.iA i l) = _
    rw [map_sum]
    simp only [map_mul]
  rw [h3, h2, h1, Pi.zero_apply, star_zero, map_zero]
  rfl

theorem sum_mul_star_eq {S₀ A L : HSp D} (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E) :
    ∑ i, vecB o ζ i * star ((HSpace.gram S₀ *ᵥ vecB o ζ) i) = star ζ ⬝ᵥ HSpace.gram L *ᵥ ζ := by
  have e1 : ∑ i, vecB o ζ i * star ((HSpace.gram S₀ *ᵥ vecB o ζ) i) = vecB o ζ ⬝ᵥ star (HSpace.gram S₀ *ᵥ vecB o ζ) := rfl
  rw [e1, Matrix.star_mulVec, gram_conjTranspose, dotProduct_comm, ← Matrix.dotProduct_mulVec, vecB,
    Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, o.isoB]

theorem sumFrame_dot (p : SplitPt D k) {n : Type} [Fintype n] [DecidableEq n] {S₀ A L : HSp D} (o : OrthDec S₀ A L)
    (ζ : Fin L.rank → D.host.E) (α : Frame p A n) (α₀ : Frame p S₀ (n ⊕ Fin 1)) (hsum : IsSumFrame o ζ α α₀)
    (x' : n ⊕ Fin 1 → k) :
    (α₀.b *ᵥ x') ⬝ᵥ (fun i => p.pr (incA D (star ((HSpace.gram S₀ *ᵥ vecB o ζ) i)))) =
      x' (Sum.inr 0) * p.pr (incA D (star ζ ⬝ᵥ HSpace.gram L *ᵥ ζ)) := by
  have e2 : ((o.jA.map p.pr * α.b) *ᵥ (x' ∘ Sum.inl)) ⬝ᵥ
      (fun i => p.pr (incA D (star ((HSpace.gram S₀ *ᵥ vecB o ζ) i)))) = 0 := by
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.vecMul_vecMul, vecMul_jA_eq_zero]
    simp only [Matrix.zero_vecMul, zero_dotProduct]
  have e3 : ((replicateCol (Fin 1) fun i => p.pr (ratV (vecB o ζ) i)) *ᵥ (x' ∘ Sum.inr)) ⬝ᵥ
      (fun i => p.pr (incA D (star ((HSpace.gram S₀ *ᵥ vecB o ζ) i)))) =
        x' (Sum.inr 0) * p.pr (incA D (star ζ ⬝ᵥ HSpace.gram L *ᵥ ζ)) := by
    rw [← sum_mul_star_eq]
    show ∑ i, (∑ j : Fin 1, (p.pr.comp (incA D)) (vecB o ζ i) * x' (Sum.inr j)) *
        (p.pr.comp (incA D)) (star ((HSpace.gram S₀ *ᵥ vecB o ζ) i)) =
      x' (Sum.inr 0) * (p.pr.comp (incA D)) (∑ i, vecB o ζ i * star ((HSpace.gram S₀ *ᵥ vecB o ζ) i))
    rw [map_sum, Finset.mul_sum]
    simp only [Fin.sum_univ_one, map_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hsum, Matrix.fromCols_mulVec, add_dotProduct, e2, e3]
  exact zero_add _

theorem pair_eq (p : SplitPt D k) (S₀ : HSp D) (z : Fin S₀.rank → D.host.E) (c : AE D) (x : Fin S₀.rank → k) :
    ∑ i, ∑ j, x i * p.pr (cA D (incA D (HSpace.gram S₀ i j))) * (p.pr (cA D c) * p.pr (incA D (star (z j))))
      = p.pr (cA D c) * (x ⬝ᵥ fun i => p.pr (incA D (star ((HSpace.gram S₀ *ᵥ z) i)))) := by
  simp only [dotProduct, Finset.mul_sum, Matrix.mulVec, star_sum, map_sum, FrameLat.cA_incA, star_mul', map_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem conj_half : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (S₀ A L : HSp D) (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E) (α : Frame p A n) (α₀ : Frame p S₀ (n ⊕ Fin 1)) (M : Lat S₀) (Λ : Submodule 𝒪[k] (n → k)), IsSelfDualC S₀ M → IsSumFrame o ζ α α₀ → α₀.IsLat M (lastKer Λ) → ∀ c : AE D, ((fun r => cA D p.e * (c * incA D (vecB o ζ r))) ∈ latV S₀ M (· = p.v) ↔ p.pr (cA D c) * p.pr (incA D (star ζ ⬝ᵥ HSpace.gram L *ᵥ ζ)) ∈ 𝒪[k]) := by
  intro D k _ _ _ _ p n _ _ S₀ A L o ζ α α₀ M Λ hM hsum hlat c
  have hy : (fun r => cA D p.e * (c * incA D (vecB o ζ r))) =
      fun r => cA D (p.sec (p.pr (cA D c) * p.pr (incA D (star (vecB o ζ r))))) := by
    funext r
    have : p.pr (cA D c) * p.pr (incA D (star (vecB o ζ r))) = p.pr (cA D (c * incA D (vecB o ζ r))) := by
      simp only [map_mul, FrameLat.cA_incA]
    rw [this, p.sec_pr, map_mul, cA_cA]
  rw [hy, FrameLat.csec_mem_iff hM]
  constructor
  · intro H
    obtain ⟨x1, hx1l, hx1r⟩ : ∃ x1 : n ⊕ Fin 1 → k, x1 ∘ Sum.inl = 0 ∧ x1 (Sum.inr 0) = 1 :=
      ⟨Sum.elim 0 (fun _ => 1), Sum.elim_comp_inl _ _, rfl⟩
    have hx' : x1 ∈ lastKer Λ := by
      rw [GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer, hx1l, hx1r]
      exact ⟨zero_mem _, one_mem _⟩
    have hx := H (α₀.b *ᵥ x1) ((hlat _).1 hx')
    rw [pair_eq, sumFrame_dot p o ζ α α₀ hsum, hx1r, one_mul] at hx
    exact hx
  · intro H x hx
    have hxx : x = α₀.b *ᵥ (α₀.b' *ᵥ x) := by rw [Matrix.mulVec_mulVec, α₀.bb', Matrix.one_mulVec]
    rw [hxx] at hx ⊢
    have hl := ((GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer).1 ((hlat _).2 hx)).2
    rw [pair_eq, sumFrame_dot p o ζ α α₀ hsum]
    convert mul_mem hl H using 1
    ring

end GlobalTheory.FinPl.ConjHalf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateHalfPointNegMultipliesByCharacter
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.LineAct.ConjModul

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem e_mul_sec (p : SplitPt D k) (a : k) : p.e * p.sec a = p.sec a := by
  rw [← p.sec_pr, p.pr_sec]

theorem pr_trace (p : SplitPt D k) {m : ℕ} (M : Mx D m m) : p.pr M.trace = (M.map p.pr).trace := by
  simp only [Matrix.trace, Matrix.diag, map_sum, Matrix.map_apply]

theorem map_rat (p : SplitPt D k) {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) :
    (rat M).map p.pr = M.map (iota p) := by
  ext i j; rfl

open GlobalTheory.FinPl.LineAct in
set_option maxHeartbeats 1600000 in

theorem conj_half_modul : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ) (χ : AddChar k Circle), p.IsChar ψ χ → ∀ (n n'' : Type) [Fintype n] [DecidableEq n] [Fintype n''] [DecidableEq n''] (S₀ A L W₀ : HSp D) (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (β : Frame p W₀ n) (γ : Frame p A n'') (γ₀ : Frame p S₀ (n'' ⊕ Fin 1)), IsSumFrame o ζ γ γ₀ → ∀ t : n → k, IsHalf (cA D p.e) ((o.resT W₀).symm (0, -GlobalTheory.FinPl.LineAct.wCol p ζ β t)) ∧ ∀ x : WO W₀ S₀, IsHalf p.e x → ψ (symplO W₀ S₀ x ((o.resT W₀).symm (0, -GlobalTheory.FinPl.LineAct.wCol p ζ β t))) = (χ (-((fun j => rd β γ₀ x (Sum.inr 0) j) ⬝ᵥ t)) : ℂ) := by
  intro D k _ _ _ _ p ψ χ hχ n n'' _ _ _ _ S₀ A L W₀ o ζ hζ β γ γ₀ hγ t
  refine ⟨fun i j => ?_, fun x _ => ?_⟩
  · rw [OrthDec.resT_symm_apply]
    simp only [Matrix.mul_zero, zero_add, Matrix.mul_neg, Matrix.neg_apply, mul_neg, Matrix.mul_apply, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [wCol, Matrix.of_apply]
    rw [mul_left_comm, ← map_mul, e_mul_sec]
  · have hy : (o.resT W₀) ((o.resT W₀).symm (0, -wCol p ζ β t)) = (0, -wCol p ζ β t) := AddEquiv.apply_symm_apply _ _
    rw [OrthDec.symplO_resT, hy]
    have h0 : symplO W₀ A ((o.resT W₀) x).1 0 = 0 := by
      rw [symplO_eq, hO_eq_trace, adj_zero, Matrix.zero_mul, Matrix.mul_zero, Matrix.trace_zero, mul_zero, map_zero]
    rw [h0, zero_add, symplO_eq, OrthDec.resT_apply, hO_eq_trace]
    set T := (giA W₀ ⬝ (adj (-wCol p ζ β t) ⬝ (gA L ⬝ (o.pB ⬝ x)))).trace with hT
    set u' : Fin L.rank → k := dualPick ((L.gram.map (iota p)) *ᵥ fun i => iota p (ζ i)) with hu'
    set v : Fin W₀.rank → k := fun j => (iota p D.host.xi0)⁻¹ * ((W₀.gram.map (iota p)) *ᵥ (β.b *ᵥ t)) j with hv
    have hadj : adj (-wCol p ζ β t) = Matrix.of fun i j => -p.sec (u' j * v i) := by
      ext i j
      simp only [adj, wCol, Matrix.transpose_apply, Matrix.map_apply, Matrix.neg_apply, Matrix.of_apply, map_neg,
        Formalism.L2.Theta.cA_cA, hu', hv]
    have hZ : p.e • adj (-wCol p ζ β t) = adj (-wCol p ζ β t) := by
      rw [hadj]
      ext i j
      simp only [Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, mul_neg, e_mul_sec]
    have heT : p.e * T = T := by
      conv_rhs => rw [hT, ← hZ]
      rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    have hc : p.e * (incA D D.host.xi0 * T) = incA D D.host.xi0 * T := by rw [mul_left_comm, heT]
    have key : ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * T)) =
        (χ (p.pr (incA D D.host.xi0 * T)) : ℂ) := by
      rw [hχ, p.sec_pr, hc]; rfl
    rw [key]
    have hxi : iota p D.host.xi0 ≠ 0 := (map_ne_zero (iota p)).2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)
    set ζb : Fin L.rank → k := fun i => iota p (ζ i) with hζb
    set R := rd β γ₀ x with hR
    set η : n → k := fun j => R (Sum.inr 0) j with hη
    have hx : x.map p.pr = γ₀.b * R * β.b' := by
      rw [hR, rd, ← Matrix.mul_assoc, ← Matrix.mul_assoc, γ₀.bb', Matrix.one_mul, Matrix.mul_assoc, β.bb',
        Matrix.mul_one]
    have hvec : (fun m => p.pr (ratV (vecB o ζ) m)) = (o.iB.map (iota p)) *ᵥ ζb := by
      funext m
      exact RingHom.map_mulVec (iota p) o.iB ζ m
    have hQ : o.qB.map (iota p) * γ₀.b = fromCols 0 (replicateCol (Fin 1) ζb) := by
      rw [hγ, Matrix.mul_fromCols, OrthDec.jA, map_rat, ← Matrix.mul_assoc, ← Matrix.map_mul, o.qB_iA,
        Matrix.map_zero _ (map_zero _), Matrix.zero_mul]
      congr 1
      ext i j
      simp only [Matrix.mul_apply, Matrix.replicateCol_apply]
      change (o.qB.map (iota p) *ᵥ fun m => p.pr (ratV (vecB o ζ) m)) i = ζb i
      rw [hvec, Matrix.mulVec_mulVec, ← Matrix.map_mul, o.qB_iB, Matrix.map_one _ (map_zero _) (map_one _),
        Matrix.one_mulVec]
    have hQR : fromCols (0 : Matrix (Fin L.rank) n'' k) (replicateCol (Fin 1) ζb) * R = vecMulVec ζb η := by
      ext i j
      simp [Matrix.mul_apply, Fintype.sum_sum_type, vecMulVec_apply, hη]
    have hqx : o.qB.map (iota p) * x.map p.pr = vecMulVec ζb (η ᵥ* β.b') := by
      rw [hx, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQ, hQR, vecMulVec_mul]
    have hg : L.gram.map (iota p) *ᵥ ζb ≠ 0 := by
      intro h0
      apply hζ.2
      have h1 : L.gram *ᵥ ζ = 0 := by
        funext i
        apply (iota p).injective
        rw [RingHom.map_mulVec, Pi.zero_apply, map_zero]
        exact congrFun h0 i
      rw [h1, dotProduct_zero]
    have hu1 : u' ⬝ᵥ (L.gram.map (iota p) *ᵥ ζb) = 1 := dualPick_dot _ hg
    have hZb : (Matrix.of fun i j => -p.sec (u' j * v i)).map p.pr = -vecMulVec v u' := by
      ext i j
      simp only [Matrix.map_apply, Matrix.of_apply, map_neg, p.pr_sec, Matrix.neg_apply, vecMulVec_apply, mul_comm]
    have hv' : v = (iota p D.host.xi0)⁻¹ • ((W₀.gram.map (iota p)) *ᵥ (β.b *ᵥ t)) := rfl
    have hGi : (W₀.gram⁻¹).map (iota p) * W₀.gram.map (iota p) = 1 := by
      rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (gram_isUnit_det W₀), Matrix.map_one _ (map_zero _) (map_one _)]
    have hval : p.pr (incA D D.host.xi0 * T) = -(η ⬝ᵥ t) := by
      rw [map_mul, hT, pr_trace, hadj]
      simp only [Matrix.map_mul, giA, gA, OrthDec.pB, map_rat, hZb]
      rw [hqx, Matrix.mul_vecMulVec, Matrix.neg_mul, Matrix.vecMulVec_mul_vecMulVec, hu1, one_smul, Matrix.mul_neg,
        Matrix.mul_vecMulVec, Matrix.trace_neg, Matrix.trace_vecMulVec, hv', Matrix.mulVec_smul, Matrix.mulVec_mulVec,
        hGi, Matrix.one_mulVec, smul_dotProduct, smul_eq_mul, dotProduct_comm, Matrix.dotProduct_mulVec,
        Matrix.vecMul_vecMul, β.b'b, Matrix.vecMul_one]
      change iota p D.host.xi0 * -((iota p D.host.xi0)⁻¹ * (η ⬝ᵥ t)) = -(η ⬝ᵥ t)
      field_simp
    rw [hval]

end GlobalTheory.FinPl.LineAct.ConjModul
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousIdempotentCutIsClosedScaledKernel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.SetCut

variable {D : D7}

theorem continuous_mt_cutTop (V : HSp D) : Continuous (fun g : GA D V => Formalism.L2.Theta.mt V g) :=
  Units.continuous_val.comp continuous_subtype_val

theorem continuous_mt_cutG (V : HSp D) (ε : AF D.host.F) (hε : ε * ε = ε) :
    Continuous (fun g : GA D V => Formalism.L2.Theta.mt V (cutG V ε hε g)) := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : ContinuousAdd (AE D) := IsModuleTopology.toContinuousAdd (AF D.host.F) (AE D)
  haveI hs : ContinuousSMul (AF D.host.F) (AE D) := IsModuleTopology.toContinuousSMul (AF D.host.F) (AE D)
  haveI : ContinuousConstSMul (AF D.host.F) (AE D) :=
    @ContinuousSMul.continuousConstSMul (AF D.host.F) (AE D) _ _ _ hs
  refine continuous_matrix fun i j => ?_
  have h : (fun g : GA D V => Formalism.L2.Theta.mt V (cutG V ε hε g) i j) = fun g : GA D V =>
      ε • Formalism.L2.Theta.mt V g i j +
        ((1 - algebraMap (AF D.host.F) (AE D) ε) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))) i j := by
    funext g
    rw [mt_cutG, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Algebra.smul_def ε]
  rw [h]
  exact (((continuous_mt_cutTop V).matrix_elem i j).const_smul ε).add continuous_const

theorem continuous_cutG (V : HSp D) (ε : AF D.host.F) (hε : ε * ε = ε) : Continuous (cutG V ε hε) := by
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨continuous_mt_cutG V ε hε, ?_⟩)
  have h := (continuous_mt_cutG V ε hε).comp (continuous_inv (G := GA D V))
  refine h.congr fun g => ?_
  rw [Function.comp_apply, map_inv]
  rfl

theorem isClosed_smul_sub_one_eq_zero (V : HSp D) (c : AF D.host.F) :
    IsClosed {g : GA D V | ∀ i j, algebraMap (AF D.host.F) (AE D) c * (Formalism.L2.Theta.mt V g - 1) i j = 0} := by
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField D.host.F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E) (AF D.host.F)
  haveI : T2Space (AE D) := e.isEmbedding.t2Space
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI hs : ContinuousSMul (AF D.host.F) (AE D) := IsModuleTopology.toContinuousSMul (AF D.host.F) (AE D)
  haveI : ContinuousConstSMul (AF D.host.F) (AE D) :=
    @ContinuousSMul.continuousConstSMul (AF D.host.F) (AE D) _ _ _ hs
  have h : {g : GA D V | ∀ i j, algebraMap (AF D.host.F) (AE D) c * (Formalism.L2.Theta.mt V g - 1) i j = 0} =
      ⋂ i, ⋂ j, {g : GA D V | c • Formalism.L2.Theta.mt V g i j =
        c • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    refine forall_congr' fun i => forall_congr' fun j => ?_
    rw [Matrix.sub_apply, mul_sub, sub_eq_zero, Algebra.smul_def, Algebra.smul_def]
  rw [h]
  exact isClosed_iInter fun i => isClosed_iInter fun j =>
    isClosed_eq (((continuous_mt_cutTop V).matrix_elem i j).const_smul c) continuous_const

theorem continuous_cutG_and_isClosed : ∀ (D : D7) (V : HSp D), (∀ (ε : AF D.host.F) (hε : ε * ε = ε), Continuous (GlobalTheory.FinPl.SetCut.cutG V ε hε)) ∧ ∀ c : AF D.host.F, IsClosed {g : GA D V | ∀ i j, algebraMap (AF D.host.F) (AE D) c * (Formalism.L2.Theta.mt V g - 1) i j = 0} :=
  fun _ V => ⟨continuous_cutG V, isClosed_smul_sub_one_eq_zero V⟩

end GlobalTheory.FinPl.SetCut
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousLocHom
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.Fam ValuativeRel IsLocalRing
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LevIdx

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {Y : Type} [Fintype Y] [DecidableEq Y]

theorem mt_mul (S : HSp D) (g h : GA D S) : mt S (g * h) = mt S g * mt S h := by
  simp [Formalism.L2.Theta.mt]

theorem mt_one (S : HSp D) : mt S 1 = 1 := by
  simp [Formalism.L2.Theta.mt]

def locHom (q : SplitPt D k) (S : HSp D) (F : GlobalTheory.LocMod.Frame k S.rank Y) : GA D S →* GL Y k where
  toFun g := ⟨F.γ * (mt S g).map q.pr * F.β, F.γ * (mt S g⁻¹).map q.pr * F.β, by
      rw [show F.γ * (mt S g).map q.pr * F.β * (F.γ * (mt S g⁻¹).map q.pr * F.β) =
        F.γ * ((mt S g).map q.pr * (F.β * F.γ) * (mt S g⁻¹).map q.pr) * F.β by simp only [Matrix.mul_assoc],
        F.βγ, Matrix.mul_one, ← Matrix.map_mul, ← mt_mul, mul_inv_cancel, mt_one, Matrix.map_one _ (map_zero _) (map_one _),
        Matrix.mul_one, F.γβ], by
      rw [show F.γ * (mt S g⁻¹).map q.pr * F.β * (F.γ * (mt S g).map q.pr * F.β) =
        F.γ * ((mt S g⁻¹).map q.pr * (F.β * F.γ) * (mt S g).map q.pr) * F.β by simp only [Matrix.mul_assoc],
        F.βγ, Matrix.mul_one, ← Matrix.map_mul, ← mt_mul, inv_mul_cancel, mt_one, Matrix.map_one _ (map_zero _) (map_one _),
        Matrix.mul_one, F.γβ]⟩
  map_one' := by
    ext1; simp only [mt_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, F.γβ]; rfl
  map_mul' g h := by
    ext1
    change F.γ * (mt S (g * h)).map q.pr * F.β = F.γ * (mt S g).map q.pr * F.β * (F.γ * (mt S h).map q.pr * F.β)
    rw [mt_mul, Matrix.map_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc F.β F.γ, F.βγ, Matrix.one_mul]

theorem locHom_val (q : SplitPt D k) (S : HSp D) (F : GlobalTheory.LocMod.Frame k S.rank Y) (g : GA D S) :
    (locHom q S F g).val = F.γ * (mt S g).map q.pr * F.β := rfl

theorem eq_locHom_iff (q : SplitPt D k) (S : HSp D) (F : GlobalTheory.LocMod.Frame k S.rank Y) (g : GA D S) (x : GL Y k) :
    (mt S g).map q.pr = F.β * x.val * F.γ ↔ x = locHom q S F g := by
  constructor
  · intro h
    ext1
    rw [locHom_val, h]
    simp only [Matrix.mul_assoc, F.γβ, Matrix.mul_one]
    rw [← Matrix.mul_assoc, F.γβ, Matrix.one_mul]
  · rintro rfl
    rw [locHom_val]
    simp only [← Matrix.mul_assoc, F.βγ, Matrix.one_mul]
    rw [Matrix.mul_assoc, F.βγ, Matrix.mul_one]

theorem continuous_locHom (q : SplitPt D k) (S : HSp D) (F : GlobalTheory.LocMod.Frame k S.rank Y) :
    Continuous (locHom q S F) := by
  rw [Units.continuous_iff]
  have hm : Continuous fun g : GA D S => (mt S g).map q.pr :=
    (GlobalTheory.MixModel.continuous_mt S).matrix_map q.cont_pr
  refine ⟨(continuous_const.matrix_mul hm).matrix_mul continuous_const, ?_⟩
  have hi : Continuous fun g : GA D S => (mt S g⁻¹).map q.pr :=
    ((GlobalTheory.MixModel.continuous_mt S).comp continuous_inv).matrix_map q.cont_pr
  exact (continuous_const.matrix_mul hi).matrix_mul continuous_const

theorem vol_mul_relIndex {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] (H H' : Subgroup G) (hle : H' ≤ H)
    (hc : IsCompact (H : Set G)) (ho : IsOpen (H' : Set G)) : μ.real H' * (H'.relIndex H : ℝ) = μ.real H := by
  haveI : CompactSpace H := isCompact_iff_compactSpace.1 hc
  have hHo : IsOpen (H : Set G) := Subgroup.isOpen_mono hle ho
  have ho' : IsOpen ((H'.subgroupOf H : Subgroup H) : Set H) := ho.preimage continuous_subtype_val
  haveI : Finite (H ⧸ H'.subgroupOf H) := (H'.subgroupOf H).quotient_finite_of_isOpen ho'
  haveI : (H'.subgroupOf H).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hemb : MeasurableEmbedding (H.subtype : H → G) := MeasurableEmbedding.subtype_coe hHo.measurableSet
  have : (μ.comap (H.subtype : H → G)).IsMulLeftInvariant := Measure.IsMulLeftInvariant.comap μ hemb
  have key := (H'.subgroupOf H).index_mul_measure ho'.measurableSet (μ.comap (H.subtype : H → G))
  rw [hemb.comap_apply, hemb.comap_apply] at key
  have e1 : (H.subtype : H → G) '' Set.univ = (H : Set G) := by ext x; simp
  have e2 : (H.subtype : H → G) '' ((H'.subgroupOf H : Subgroup H) : Set H) = (H' : Set G) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hle hx⟩, hx, rfl⟩
  rw [e1, e2] at key
  rw [Subgroup.relIndex, Measure.real, Measure.real, ← key, ENNReal.toReal_mul, mul_comm]
  simp

end GlobalTheory.LevIdx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DefiniteRealGroupFixesSplitSpaceWeilVacuum
section
noncomputable section
open scoped Matrix ComplexOrder
open Formalism.IndefR.Datum

namespace GlobalTheory.VacuumSplitReal

theorem trace_cartan_of_sig {k t : ℕ} (G s : Matrix (Fin k) (Fin k) ℂ) (hs : IsCartanInv G s)
    (hG : Formalism.UG.HasSignature G t t) (hk : k = 2 * t) : s.trace = 0 := by
  obtain ⟨e, P, hP⟩ := hG
  obtain ⟨Q, hQ⟩ : ∃ Q : Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) ℂ, Q = (P : Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) ℂ) := ⟨_, rfl⟩
  obtain ⟨Q', hQ'⟩ : ∃ Q' : Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) ℂ,
      Q' = ((P⁻¹ : GL (Fin t ⊕ Fin t) ℂ) : Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) ℂ) := ⟨_, rfl⟩
  have hQQ : Q' * Q = 1 := by rw [hQ, hQ', ← Units.val_mul, inv_mul_cancel, Units.val_one]
  let B0 : Matrix (Fin t ⊕ Fin t) (Fin t) ℂ := Matrix.fromRows 1 1
  let C0 : Matrix (Fin t) (Fin t ⊕ Fin t) ℂ := Matrix.fromCols 1 0
  have hC0 : C0 * B0 = 1 := by
    simp [C0, B0, Matrix.fromCols_mul_fromRows]
  have hPP : Qᴴ * G.reindex e e * Q = Formalism.UG.Jpq t t := by
    rw [← hP, hQ]; rfl
  have hB0 : B0ᴴ * Formalism.UG.Jpq t t * B0 = 0 := by
    simp [B0, Formalism.UG.Jpq, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromCols_mul_fromBlocks,
      Matrix.fromCols_mul_fromRows]
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin k) (Fin t) ℂ, B = (Q * B0).submatrix e id := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : Matrix (Fin t) (Fin k) ℂ, C = (C0 * Q').submatrix id e := ⟨_, rfl⟩
  have h1 : C * B = 1 := by
    rw [hB, hC, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id, Matrix.mul_assoc, ← Matrix.mul_assoc Q', hQQ,
      Matrix.one_mul, hC0]
  have h2 : Bᴴ * G * B = 0 := by
    have hG' : G = (G.reindex e e).submatrix e e := by
      ext i j; simp [Matrix.reindex_apply]
    rw [hB, Matrix.conjTranspose_submatrix, hG', Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_id_id]
    have h3 : (Q * B0)ᴴ * G.reindex e e * (Q * B0) = B0ᴴ * (Qᴴ * G.reindex e e * Q) * B0 := by
      rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    rw [h3, hPP, hB0]
  exact GlobalTheory.SplitVacSum.trace_eq_zero hs.1 hs.2.2 (m := t) (by rw [Fintype.card_fin, hk]) B C h1 h2

end GlobalTheory.VacuumSplitReal

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

namespace GlobalTheory.VacuumSplitReal

theorem vacuum_fixed : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A H : HSp D) (t : ℕ) (χA : (AE D)ˣ →* Circle) (om : WRep A H) (sH : RealMat H), IsInfFam θ → (∃ η, GlobalTheory.WeilParts.IsEtaTilde D η) → IsWeilDatumO ψ A H χA 1 om → (∀ τ, IsCartanInv (gramAt D A τ) 1) → (∀ τ, IsCartanInv (gramAt D H τ) (sH τ)) → HSpace.SigOK H → H.rank = 2 * t → (∀ τ, H.sig τ = (t, t)) → ∀ f, IsThetaFunO ψ A H f → (∀ τ, IsFockVacAt (heisO ψ A H) θ τ (cplxO 1 (sH τ)) f) → ∀ b ∈ GinfC A, om (b, 1) f = f := by
  intro D ψ θ A H t χA om sH hθ ⟨η, hη⟩ hW hA hH hsig hrank hsigt f hf hv b hb
  have hdet : ∀ {k : ℕ} {G s : Matrix (Fin k) (Fin k) ℂ}, IsCartanInv G s → G.det ≠ 0 := fun {k G s} hG => by
    have := hG.2.2.det_pos.ne'
    rw [Matrix.det_mul] at this
    exact left_ne_zero_of_mul this
  obtain ⟨x, hx, hxv⟩ := GlobalTheory.VacuumCharacter.exists_root hθ A (fun τ => hdet (hA τ)) b hb
  have mt1 : ∀ τ, compAt θ τ (Formalism.L2.Theta.mt H 1) = 1 := fun τ => by
    unfold Formalism.L2.Theta.mt compAt
    rw [map_one, Units.val_one]
    exact Matrix.map_one _ (by simp) (by simp)
  have h1 : ∀ τ, HasInfExp D 1 τ 0 := fun τ => ⟨0, by norm_num, ⟨θ, hθ⟩, fun _ _ _ _ _ => by simp⟩
  have hexp : ∀ τ, HasInfExp D (1 * (η ^ H.rank)⁻¹) τ ((-(t : ℤ) : ℤ) : ℚ) := fun τ => by
    have h := GlobalTheory.VacuumCharacter.hasInfExp_twist (h1 τ) (hη.2.2.2 τ) H.rank
    convert h using 1
    rw [hrank]; push_cast; ring
  have hν := hxv _ (fun _ => -(t : ℤ)) hexp
  rw [GlobalTheory.WeilVacChar.vacuum_character D ψ hW.std A H θ hθ χA 1 om η hη hW (fun _ => 1) sH hA hH b hb 1 (one_mem _)
    (fun τ => by rw [one_mul, mul_one]) (fun τ => by rw [mt1, one_mul, mul_one]) x 1 hx ?_ f hf hv]
  · conv_rhs => rw [← one_smul ℂ f]
    congr 1
    rw [Circle.coe_mul, Circle.coe_inv, hν, MonoidHom.map_one, Circle.coe_one, mul_one, ← Finset.prod_inv_distrib,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun τ _ => ?_
    obtain ⟨p, hp, hd⟩ := GlobalTheory.VacuumCharacter.detPlus_one (n := A.rank) (sH τ) (hH τ).1
    have htr : (sH τ).trace = 0 := by
      have hs := hsig (tauE D τ)
      rw [hsigt] at hs
      exact trace_cartan_of_sig (gramAt D H τ) (sH τ) (hH τ) hs hrank
    have hpt : p = t := by
      have : (p : ℂ) = t := by
        rw [htr, hrank] at hp; push_cast at hp; linear_combination -hp / 2
      exact_mod_cast this
    have inv : (compAt θ τ (Formalism.L2.Theta.mt A b)).det * (compAt θ τ (Formalism.L2.Theta.mt A b⁻¹)).det = 1 := by
      rw [GlobalTheory.VacuumCharacter.det_compAt, GlobalTheory.VacuumCharacter.det_compAt, ← map_mul, ← map_mul, ← Matrix.det_mul]
      unfold Formalism.L2.Theta.mt
      rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.det_one, map_one, map_one]
    have d0 := left_ne_zero_of_mul_eq_one inv
    rw [mt1, (hd _ 1 (by rw [one_mul, mul_one])).1, eq_inv_of_mul_eq_one_right inv, hpt, mul_one,
      show (1 / 2 : ℂ) • (1 + sH τ) + (1 / 2 : ℂ) • (1 - sH τ) = 1 by module, Matrix.det_one, one_pow, one_mul,
      zpow_neg, inv_inv, zpow_natCast, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ d0)]
  · unfold Formalism.L2.Theta.IsDetRoot
    simp

end GlobalTheory.VacuumSplitReal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDoubleStepKernelLocalModelsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_doubleStep_kernel_localModels : ∀ (D : D7), LastLoc D := by
  first | exact @GlobalTheory.LastKerLoc.lastLoc | exact GlobalTheory.LastKerLoc.lastLoc | (intros; apply GlobalTheory.LastKerLoc.lastLoc <;> assumption)
end

