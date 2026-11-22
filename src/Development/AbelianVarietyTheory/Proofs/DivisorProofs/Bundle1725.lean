import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1702
import Formalism.SharpRestriction.Divisibility.KudlaSiegelWeil
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0159
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0155
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.Bundle0002
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0081
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1693
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1611
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformFinitenessOfReproducingPolynomialAveragin
import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.MeasurePreservingMulRight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Smooth

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdmissibleCMBaseDataOfSquareTupleStanding
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.BaseGoodPlace

open GlobalTheory.Idele WithZero
open GlobalTheory.StdDual (codiff codiff_ne_zero)

theorem psiUnr_of_not_le {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    (v : HeightOneSpectrum (𝓞 D.host.F)) (hv : ¬ differentIdeal ℤ (𝓞 D.host.F) ≤ v.asIdeal) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PsiUnr ψ v := by
  classical
  intro x
  have hc := GlobalTheory.SplitUnram.count_codiff_eq_zero v (fun h => hv (Ideal.le_of_dvd h))
  set α : Af D.host.F := GlobalTheory.AdelicU.singleFin v x with hα
  have hαv : α v = x := GlobalTheory.AdelicU.evalV_singleFin_self v x
  have hαw : ∀ w, w ≠ v → α w = 0 := fun w hw => GlobalTheory.AdelicU.evalV_singleFin_ne hw x
  have h := GlobalTheory.SplitUnram.mem_adelicIdeal_codiff_iff hψ.1.1 (GlobalTheory.StdRat.stdChar_fin_rat D ψ hψ) α
  have key : (∀ y ∈ v.adicCompletionIntegers D.host.F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.psiLoc ψ v (x * y) = 1) ↔
      ∀ β : Af D.host.F, (∀ w, β w ∈ w.adicCompletionIntegers D.host.F) → ψ (pairA D.host.F 0 (β * α)) = 1 := by
    constructor
    · intro H β hβ
      have e : β * α = GlobalTheory.AdelicU.singleFin v (x * β v) := by
        apply GlobalTheory.AdelicU.af_ext
        intro u
        by_cases hu : u = v
        · subst hu
          rw [map_mul, hα, GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self]
          change β u * x = x * β u
          ring
        · rw [map_mul, hα, GlobalTheory.AdelicU.evalV_singleFin_ne hu, GlobalTheory.AdelicU.evalV_singleFin_ne hu, mul_zero]
      rw [e]
      exact H _ (hβ v)
    · intro H y hy
      have e : GlobalTheory.AdelicU.singleFin v y * α = GlobalTheory.AdelicU.singleFin v (x * y) := by
        rw [hα, ← GlobalTheory.AdelicU.singleFin_mul, mul_comm]
      have := H (GlobalTheory.AdelicU.singleFin v y) (fun w => by
        by_cases hw : w = v
        · subst hw
          change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV _ w (GlobalTheory.AdelicU.singleFin w y) ∈ _
          rw [GlobalTheory.AdelicU.evalV_singleFin_self]
          exact hy
        · change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV _ w (GlobalTheory.AdelicU.singleFin v y) ∈ _
          rw [GlobalTheory.AdelicU.evalV_singleFin_ne hw]
          exact zero_mem _)
      rw [e] at this
      exact this
  rw [key, ← h, mem_adelicIdeal_iff codiff_ne_zero, HeightOneSpectrum.mem_adicCompletionIntegers]
  constructor
  · intro H
    have := H v
    rwa [hc, neg_zero, exp_zero, hαv] at this
  · intro H w
    by_cases hw : w = v
    · subst hw
      rw [hc, neg_zero, exp_zero, hαv]
      exact H
    · rw [hαw w hw, map_zero]
      exact zero_le

end GlobalTheory.BaseGoodPlace

namespace GlobalTheory.BaseGoodPlace

theorem trInf_eq_trace (D : D7) (x : Ainf D.host.F) :
    GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices.trInf D x = Algebra.trace ℝ (mixedEmbedding.mixedSpace D.host.F)
      (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F x) := by
  classical
  rw [Algebra.trace_prod_apply, PI.ProdFormulaE.Tr.trace_pi, PI.ProdFormulaE.Tr.trace_pi,
    InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  simp only [Algebra.trace_complex_apply]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices.trInf
  rw [← Fintype.sum_subtype_add_sum_subtype (fun w : InfinitePlace D.host.F => w.IsReal)]
  congr 1
  · refine Fintype.sum_congr _ _ fun w => ?_
    rw [InfinitePlace.mult_isReal, Nat.cast_one, one_mul, ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply w.2,
      Complex.ofReal_re]
    simp
  · refine Fintype.sum_equiv (Equiv.subtypeEquivRight fun w => InfinitePlace.not_isReal_iff_isComplex) _ _ fun w => ?_
    have h := InfinitePlace.mult_isComplex ⟨w.1, InfinitePlace.not_isReal_iff_isComplex.1 w.2⟩
    simp only at h
    rw [h]
    push_cast
    rfl

end GlobalTheory.BaseGoodPlace

namespace GlobalTheory.BaseGoodPlace

theorem isStd_of_isStdChar {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := by
  refine ⟨hψ.1.1, hψ.1.2.2.1, fun a ha => ?_⟩
  have h2 : a.2 = 0 := by
    have h0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F (pairA D.host.F 0 1) = 0 := by
      show InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F (0 : Ainf D.host.F) = 0
      exact map_zero _
    have := congrArg Prod.snd (ha (pairA D.host.F 0 1) h0)
    rw [smul_eq_mul] at this
    have e : (1 : Af D.host.F) * a.2 = 0 := this
    simpa using e
  have ha' : a = pairA D.host.F a.1 0 := Prod.ext rfl h2
  obtain ⟨θ, hθ⟩ := hψ.2.1
  have h := hψ.2.2 θ hθ a.1
  rw [GlobalTheory.DualPairCompare.sum_infFam θ hθ, trInf_eq_trace] at h
  rw [ha']
  change psiInf D.host.F ψ a.1 = _
  rw [h]
  congr 1
  push_cast
  change _ = -(2 * ↑Real.pi * Complex.I) * ((Algebra.trace ℝ (mixedEmbedding.mixedSpace D.host.F)
      (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F a.1) : ℝ) : ℂ)
  ring

end GlobalTheory.BaseGoodPlace

namespace GlobalTheory.BaseGoodPlace

theorem exists_ram_prime_of_le (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F))
    (hle : differentIdeal ℤ (𝓞 D.host.F) ≤ v.asIdeal) :
    ∃ p : ℕ, p ∣ D.host.QS * D.host.q * D.host.d ∧ (p : 𝓞 D.host.F) ∈ v.asIdeal := by
  obtain ⟨p, -, h1, h2⟩ := UpperTheory.Ram.Fun.exists_prime_of_different_le D.host v hle
  exact ⟨p, h1, h2⟩

end GlobalTheory.BaseGoodPlace

namespace GlobalTheory.FunObj

theorem base_isGood_of_standing : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (W : G.Weil) (t : T),
    SquareStanding G t → ∀ B : Base D.host.F D.host.E, B.ψ = W.ψ →
      (∀ v ∈ B.P, ∃ w ∈ locPl G t, w.under (𝓞 D.host.F) = v) → B.IsGood D.sp.cm.sig := by
  intro D T L sc G μ₀ _hL W t hS B hB hP
  have hψ : IsStdChar D B.ψ (-1) := hB ▸ W.ψ_std
  refine { cm := GlobalTheory.AdelicU.isCMExt_host D
           galois := D.host.hostE_isGalois
           unram := GlobalTheory.InertOfConj.unram D
           std := GlobalTheory.BaseGoodPlace.isStd_of_isStdChar hψ
           inert := ?_
           psiP := ?_ }
  · intro v w hw
    have hns : ¬ Formalism.MainNotions.KudlaSiegelWeil.Split D v := by
      rintro ⟨w1, w2, hne, h1, h2⟩
      apply hne
      have key : ∀ u : HeightOneSpectrum (𝓞 D.host.E), Formalism.MainNotions.KudlaSiegelWeil.Over D u v → u = w := fun u hu => by
        have hle : w.asIdeal ≤ u.asIdeal := by
          rw [← hw]
          exact Ideal.map_le_iff_le_comap.2 (le_of_eq hu.symm)
        exact HeightOneSpectrum.ext (w.isMaximal.eq_of_le u.isPrime.ne_top hle).symm
      rw [key w1 h1, key w2 h2]
    obtain ⟨h2, h3, hd, -⟩ := Formalism.MainNotions.KudlaSiegelWeil.inert_conditions_hold D v hns
    exact ⟨h2, h3, GlobalTheory.BaseGoodPlace.psiUnr_of_not_le hψ v hd⟩
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := hP v hv
    refine GlobalTheory.BaseGoodPlace.psiUnr_of_not_le hψ _ fun hle => ?_
    obtain ⟨p, hp, hpv⟩ := GlobalTheory.BaseGoodPlace.exists_ram_prime_of_le D _ hle
    have hpw : (p : 𝓞 D.host.E) ∈ w.asIdeal := by
      have h := hpv
      change (p : 𝓞 D.host.F) ∈ w.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) at h
      rwa [Ideal.mem_comap, map_natCast] at h
    apply hS.2 w hw
    obtain ⟨c, hc⟩ := hp
    rw [hc]
    push_cast
    exact w.asIdeal.mul_mem_right _ (w.asIdeal.mul_mem_right _ hpw)

end GlobalTheory.FunObj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCartanInvolutionHermitianSmulBlockDiagonalRein
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open scoped nonZeroDivisors

open scoped ComplexOrder

namespace GlobalTheory.CartanBlocks

theorem posDef_fromBlocks_diag {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {A : Matrix m m ℂ} {D : Matrix n n ℂ} (hA : A.PosDef) (hD : D.PosDef) :
    (Matrix.fromBlocks A 0 0 D).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x hx => ?_⟩
  · rw [Matrix.IsHermitian, Matrix.fromBlocks_conjTranspose, hA.1.eq, hD.1.eq, Matrix.conjTranspose_zero, Matrix.conjTranspose_zero]
  · have key : star x ⬝ᵥ (Matrix.fromBlocks A 0 0 D *ᵥ x) =
        star (x ∘ Sum.inl) ⬝ᵥ (A *ᵥ (x ∘ Sum.inl)) + star (x ∘ Sum.inr) ⬝ᵥ (D *ᵥ (x ∘ Sum.inr)) := by
      simp [dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks_mulVec, Function.comp_def, Matrix.mulVec,
        Pi.star_apply]
    rw [key]
    by_cases h1 : x ∘ Sum.inl = 0
    · have h2 : x ∘ Sum.inr ≠ 0 := by
        intro h2; apply hx; funext i; rcases i with i | i
        · exact congrFun h1 i
        · exact congrFun h2 i
      rw [h1]; simpa using hD.dotProduct_mulVec_pos h2
    · exact add_pos_of_pos_of_nonneg (hA.dotProduct_mulVec_pos h1) (hD.posSemidef.dotProduct_mulVec_nonneg _)

theorem posDef_blk {p q d : ℕ} (e : Fin p ⊕ Fin q ≃ Fin d) {A : Matrix (Fin p) (Fin p) ℂ}
    {D : Matrix (Fin q) (Fin q) ℂ} (hA : A.PosDef) (hD : D.PosDef) : (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e A D).PosDef := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk
  rw [Matrix.reindex_apply]
  exact (posDef_fromBlocks_diag hA hD).submatrix e.symm.injective

theorem blk_conjTranspose {p q d : ℕ} (e : Fin p ⊕ Fin q ≃ Fin d) (A : Matrix (Fin p) (Fin p) ℂ)
    (D : Matrix (Fin q) (Fin q) ℂ) : (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e A D)ᴴ = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e Aᴴ Dᴴ := by
  simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk, Matrix.conjTranspose_reindex, Matrix.fromBlocks_conjTranspose]

theorem isCartan_blk : ∀ {a b d : ℕ} (e : Fin a ⊕ Fin b ≃ Fin d) (GA sA : Matrix (Fin a) (Fin a) ℂ) (GB sB : Matrix (Fin b) (Fin b) ℂ) {κ : ℝ},
    0 < κ → Formalism.IndefR.Datum.IsCartanInv GA sA → Formalism.IndefR.Datum.IsCartanInv GB sB →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan ((κ : ℂ) • GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e GA GB) ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e sA sB).map (starRingEnd ℂ)) := by
  intro a b d e GA sA GB sB κ hκ hA hB
  obtain ⟨hA1, hA2, hA3⟩ := hA
  obtain ⟨hB1, hB2, hB3⟩ := hB
  set S := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e sA sB with hS
  set G := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e GA GB with hG
  have hSS : S * S = 1 := by rw [hS, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk_mul, hA1, hB1, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk_one]
  have hSGS : Sᴴ * G * S = G := by
    rw [hS, hG, blk_conjTranspose, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk_mul, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk_mul, hA2, hB2]
  have hGS : (G * S).PosDef := by
    rw [hS, hG, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk_mul]; exact posDef_blk e hA3 hB3

  have hGH : Gᴴ = G := by
    have h4 : Sᴴ * Gᴴ = G * S := by rw [← Matrix.conjTranspose_mul]; exact hGS.1.eq
    have h5 : Sᴴ * Sᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hSS, Matrix.conjTranspose_one]
    calc Gᴴ = Sᴴ * (Sᴴ * Gᴴ) := by rw [← Matrix.mul_assoc, h5, Matrix.one_mul]
      _ = G := by rw [h4, ← Matrix.mul_assoc, hSGS]
  have hSG : Sᴴ * G = G * S := by
    have := hGS.1.eq
    rw [Matrix.conjTranspose_mul, hGH] at this
    exact this
  have hT : (S.map (starRingEnd ℂ))ᵀ = Sᴴ := by
    ext i j; simp [Matrix.conjTranspose_apply]
  have hMM : (S.map (starRingEnd ℂ)).map star = S := by
    ext i j; simp
  refine ⟨?_, ?_, ?_⟩
  · rw [← Matrix.map_mul, hSS, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [hT, hMM, Matrix.mul_smul, Matrix.smul_mul, hSGS]
  · intro x hx
    have hy : star x ≠ 0 := by simpa using hx
    have hv : S.map (starRingEnd ℂ) *ᵥ x = star (S *ᵥ star x) := by
      ext i; simp [Matrix.mulVec, dotProduct, star_sum, Pi.star_apply, mul_comm]
    have hpos : ((κ : ℂ) • (G * S)).PosDef := hGS.smul (by exact_mod_cast hκ)
    have key : (S.map (starRingEnd ℂ) *ᵥ x) ⬝ᵥ ((κ : ℂ) • G) *ᵥ star x =
        star (star x) ⬝ᵥ (((κ : ℂ) • (G * S)) *ᵥ star x) := by
      rw [hv, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mul_smul, hSG]
    rw [key]
    have := hpos.dotProduct_mulVec_pos hy
    exact (Complex.lt_def.1 this).1

end GlobalTheory.CartanBlocks
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactLevelHeightScalesIsotropicFrame
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ResidueEisenstein.HtCont

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n k : ℕ} {J : Matrix (Fin n) (Fin n) E} {X : Matrix (Fin n) (Fin k) E}

omit [NumberField E] in

theorem scalesBy_mul {p q : GAd σ J} {β γ : GL (Fin k) (AF F ⊗[F] E)} (e : ScalesBy σ J X p β)
    (e' : ScalesBy σ J X q γ) : ScalesBy σ J X (p * q) (β * γ) := by
  unfold ScalesBy at *
  rw [map_mul, Units.val_mul, Matrix.mul_assoc, e', ← Matrix.mul_assoc, e, Units.val_mul, Matrix.mul_assoc]

omit [NumberField E] in

theorem scalesBy_inv {p : GAd σ J} {β : GL (Fin k) (AF F ⊗[F] E)} (e : ScalesBy σ J X p β) :
    ScalesBy σ J X p⁻¹ β⁻¹ := by
  unfold ScalesBy at *
  calc (matHom _ σ J p⁻¹).1 * adMat F X = (matHom _ σ J p⁻¹).1 * (adMat F X * β.1 * (β⁻¹).1) := by
        rw [Matrix.mul_assoc (adMat F X), ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
    _ = (matHom _ σ J p⁻¹).1 * (matHom _ σ J p).1 * adMat F X * (β⁻¹).1 := by
        rw [← e]; simp only [Matrix.mul_assoc]
    _ = adMat F X * (β⁻¹).1 := by
        rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mul]

theorem absE_pos (u : (AF F ⊗[F] E)ˣ) : (0 : ℝ) < absE F E u := by
  have h : absE F E u * absE F E u⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have : absE F E u ≠ 0 := fun h0 => by rw [h0, zero_mul] at h; exact zero_ne_one h
  exact_mod_cast pos_iff_ne_zero.2 this

theorem isCompact_isHt_scales : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), DataJ σ J X Y L a h → IsCompact (levelAll σ J L a : Set (GAd σ J)) ∧ IsHt (levelAll σ J L a) h ∧ ∀ p β, ScalesBy σ J X p β → ∀ g, h (p * g) = absE F E (Matrix.GeneralLinearGroup.det β) * h g := by
  intro F E _ _ _ _ _ σ n J r X Y L a h H
  haveI := H.lat
  obtain ⟨_, _⟩ := GlobalTheory.StdPar.ring_facts (F := F) (E := E)
  have hK : IsCompact (levelAll σ J L a : Set (GAd σ J)) := GlobalTheory.Doubling.isCompact_levelAll H.cm J L a
  have hyx : Formalism.UG.cT (σ : E →+* E) Y * J * X = 1 := GlobalTheory.StdPar.yx H.cm H.herm H.witt
  have hsc : ∀ p β, ScalesBy σ J X p β → ∀ g, h (p * g) = absE F E (Matrix.GeneralLinearGroup.det β) * h g := by
    intro p β e g
    obtain ⟨q, γ, e', k, hk, rfl⟩ := H.iwa g
    rw [← mul_assoc, H.ht _ _ (scalesBy_mul e e') _ hk, H.ht _ _ e' _ hk, map_mul, map_mul, NNReal.coe_mul]
  let φ : GAd σ J → Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E) := fun p =>
    adMat F (Formalism.UG.cT (σ : E →+* E) Y * J) * ((matHom _ σ J p).1 * adMat F X)
  have h1 : adMat F (Formalism.UG.cT (σ : E →+* E) Y * J) * adMat F X = 1 := by
    simp only [adMat, ← Matrix.map_mul, hyx]; simp
  have hφ : ∀ p β, ScalesBy σ J X p β → φ p = β.1 := fun p β e => by
    unfold ScalesBy at e
    show adMat F (Formalism.UG.cT (σ : E →+* E) Y * J) * ((matHom _ σ J p).1 * adMat F X) = β.1
    rw [e, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  have cφ : Continuous φ := continuous_const.matrix_mul (GlobalTheory.StdPar.continuous_mat.matrix_mul continuous_const)
  let P := GlobalTheory.StdPar.frameStab σ J X (⊤ : Subgroup (GL (Fin (r + 1)) (AF F ⊗[F] E)))
  have cP : IsClosed (P : Set (GAd σ J)) := GlobalTheory.StdPar.isClosed_frameStab hyx isClosed_univ
  have hP : ∀ p : P, ScalesBy σ J X p.1 p.2.choose := fun p => p.2.choose_spec.2
  let u : P → (AF F ⊗[F] E)ˣ := fun p => Matrix.GeneralLinearGroup.det p.2.choose
  have cu : Continuous u := Units.continuous_iff.2
    ⟨((cφ.comp continuous_subtype_val).matrix_det).congr fun p => by
        simp only [Function.comp, u, hφ _ _ (hP p)]; rfl,
      ((cφ.comp (continuous_subtype_val.inv)).matrix_det).congr fun p => by
        show (φ (p.1⁻¹)).det = _
        rw [hφ _ _ (scalesBy_inv (hP p)), ← map_inv, Matrix.GeneralLinearGroup.val_det_apply]⟩
  refine ⟨hK, ⟨fun g => ?_, ?_, fun k hk => by simpa using H.ht 1 1 (by simp [ScalesBy]) k hk, fun g => ?_⟩, hsc⟩
  · obtain ⟨p, β, e, k, hk, rfl⟩ := H.iwa g
    rw [H.ht _ _ e _ hk]; exact absE_pos _
  · refine GlobalTheory.Doubling.continuous_of_prod cP hK
      (fun g => let ⟨p, β, e, k, hk, e'⟩ := H.iwa g; ⟨⟨p, β, trivial, e⟩, k, hk, e'⟩) ?_
    exact (NNReal.continuous_coe.comp (GlobalTheory.Doubling.continuous_absE.comp (cu.comp continuous_fst))).congr
      fun x => (H.ht _ _ (hP x.1) _ x.2.2).symm
  · obtain ⟨p, β, e, k, hk, rfl⟩ := H.iwa g
    refine ⟨k, hk, fun x => ?_⟩
    rw [mul_assoc, hsc _ _ e, H.ht _ _ e _ hk]

end GlobalTheory.ResidueEisenstein.HtCont

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDiscreteValuationRingFixedFieldInertia
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.InertiaFixedDVR

theorem isDiscreteValuationRing_fixedField_inertia : ∀ (R K Ω : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K]
    [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring →
    IsDiscreteValuationRing (V.comap (algebraMap (IntermediateField.fixedField (inertia K V)) Ω)) := by
  intro R K Ω _ _ _ _ _ _ _ _ _ _ V hV
  classical
  set K' := IntermediateField.fixedField (inertia K V) with hK'
  set W := V.comap (algebraMap K' Ω) with hW
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  set c : Ω := algebraMap K Ω (algebraMap R K π) with hc
  have hπK : algebraMap R K π ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact hπ.ne_zero
  have hc0 : c ≠ 0 := (map_ne_zero _).2 hπK
  have hcV : c ∈ V := by
    have h : algebraMap R K π ∈ V.toSubring.comap (algebraMap K Ω) := by rw [hV]; exact ⟨π, rfl⟩
    exact h
  have hcinv : c⁻¹ ∉ V := by
    intro h
    have h' : (algebraMap R K π)⁻¹ ∈ V.toSubring.comap (algebraMap K Ω) := by
      change algebraMap K Ω (algebraMap R K π)⁻¹ ∈ V
      rw [map_inv₀]; exact h
    rw [hV] at h'
    obtain ⟨r, hr⟩ := h'
    apply hπ.not_isUnit
    refine isUnit_iff_exists_inv.2 ⟨r, IsFractionRing.injective R K ?_⟩
    rw [map_mul, hr, map_one, mul_inv_cancel₀ hπK]
  have hcK' : c ∈ K' := K'.algebraMap_mem _

  let j : W → Ω := fun w => ((w : K') : Ω)
  have hjinj : Function.Injective j := fun a b h => Subtype.ext (Subtype.ext h)
  have hjV : ∀ w : W, j w ∈ V := fun w => w.2
  have hjK : ∀ w : W, j w ∈ K' := fun w => (w : K').2
  have hj_mul : ∀ a b : W, j (a * b) = j a * j b := fun _ _ => rfl
  have hj_zero : j 0 = 0 := rfl
  have hj_one : j 1 = 1 := rfl
  have hj_pow : ∀ (a : W) (n : ℕ), j (a ^ n) = j a ^ n := by
    intro a n
    induction n with
    | zero => simpa using hj_one
    | succ n ih => rw [pow_succ, hj_mul, ih, pow_succ]
  let mk : (y : Ω) → y ∈ K' → y ∈ V → W := fun y h1 h2 => ⟨⟨y, h1⟩, h2⟩
  have hunit : ∀ w : W, j w ≠ 0 → (j w)⁻¹ ∈ V → IsUnit w := by
    intro w h0 hinv
    refine isUnit_iff_exists_inv.2 ⟨mk (j w)⁻¹ (K'.inv_mem (hjK w)) hinv, hjinj ?_⟩
    rw [hj_mul, hj_one]
    exact mul_inv_cancel₀ h0
  have hdvd : ∀ w : W, ¬ IsUnit w → ∃ u : W, w = mk c hcK' hcV * u := by
    intro w hw
    have hnu : j w ∈ V.nonunits := by
      rw [GlobalTheory.FixInertUnram.mem_nonunits_iff']
      by_cases h0 : j w = 0
      · exact Or.inl h0
      · exact Or.inr fun h => hw (hunit w h0 h)
    have hq := GlobalTheory.FixInertUnram.div_uniformizer_mem R K Ω V hV π hπ (j w) (hjK w) hnu
    refine ⟨mk (j w / c) (K'.div_mem (hjK w) hcK') hq, hjinj ?_⟩
    rw [hj_mul]
    change j w = c * (j w / c)
    field_simp
  set ϖ : W := mk c hcK' hcV with hϖ
  have hϖnu : ¬ IsUnit ϖ := by
    intro h
    obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.1 h
    apply hcinv
    have e : c * j v = 1 := by
      have := congrArg j hv
      rw [hj_mul, hj_one] at this
      exact this
    rw [inv_eq_of_mul_eq_one_right e]
    exact hjV v
  have hϖ0 : ϖ ≠ 0 := fun h => hc0 (by have := congrArg j h; rw [hj_zero] at this; exact this)
  have hirr : Irreducible ϖ := by
    refine ⟨hϖnu, fun a b hab => ?_⟩
    by_contra hne
    push_neg at hne
    obtain ⟨a', rfl⟩ := hdvd a hne.1
    obtain ⟨b', rfl⟩ := hdvd b hne.2
    apply hϖnu
    have e : ϖ * 1 = ϖ * (ϖ * (a' * b')) := by
      rw [_root_.mul_one]
      calc ϖ = ϖ * a' * (ϖ * b') := hab
        _ = ϖ * (ϖ * (a' * b')) := by ring
    have h1 := mul_left_cancel₀ hϖ0 e
    exact isUnit_iff_exists_inv.2 ⟨a' * b', h1.symm⟩
  refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨ϖ, hirr, fun {x} hx => ?_⟩
  have hx0 : j x ≠ 0 := fun h => hx (hjinj (h.trans hj_zero.symm))
  have hex : ∃ n : ℕ, j x / c ^ n ∉ V := GlobalTheory.not_mem_div_uniformizer_pow R K Ω V hV π hπ (j x) hx0
  obtain ⟨n, hn, hmin⟩ : ∃ n : ℕ, j x / c ^ n ∉ V ∧ ∀ k < n, j x / c ^ k ∈ V :=
    ⟨Nat.find hex, Nat.find_spec hex, fun k hk => by simpa using Nat.find_min hex hk⟩
  have hn0 : n ≠ 0 := by
    rintro rfl
    apply hn
    rw [pow_zero, div_one]
    exact hjV x
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hmV : j x / c ^ m ∈ V := hmin m (by omega)
  have hyK : j x / c ^ m ∈ K' := K'.div_mem (hjK x) (pow_mem hcK' m)
  have hy0 : j x / c ^ m ≠ 0 := div_ne_zero hx0 (pow_ne_zero _ hc0)
  have hyinv : (j x / c ^ m)⁻¹ ∈ V := by
    by_contra hyi
    have hq := GlobalTheory.FixInertUnram.div_uniformizer_mem R K Ω V hV π hπ (j x / c ^ m) hyK
      ((GlobalTheory.FixInertUnram.mem_nonunits_iff' V _).2 (Or.inr hyi))
    apply hn
    rw [pow_succ, ← div_div]
    exact hq
  have hu : IsUnit (mk (j x / c ^ m) hyK hmV) := hunit _ hy0 hyinv
  refine ⟨m, hu.unit, hjinj ?_⟩
  rw [IsUnit.unit_spec, hj_mul, hj_pow]
  change c ^ m * (j x / c ^ m) = j x
  field_simp

end GlobalTheory.InertiaFixedDVR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformFinitenessOfReproducingPolynomialAveraginStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformFiniteness_of_reproducingPolynomial_averaging : GlobalTheory.PsCo.Pc3.Repro → (∀ (n : ℕ) (ε : Fin n → Bool) (d : ℕ), ∃ A : Set (Fin n → ℝ), A.Finite ∧ ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), ReciprocityTheory.ChartRestriction.DS.IsURepOn (ReciprocityTheory.ChartRestriction.DS.UJset ε) σ → ∀ u : H, ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ Formalism.MainNotions.S.IsKStableOn ε σ S ∧ (∀ P : GlobalTheory.PsCo.Pc1.Poly n, P.totalDegree ≤ d → ∫ k : Formalism.REAL.KG ε, GlobalTheory.PsCo.Pc1.ev (Formalism.REAL.toMK k) P • σ (Formalism.REAL.toMK k) u ∂(Formalism.REAL.muK ε) ∈ S) ∧ ∀ (μ : Fin n → ℝ) (s : H), s ∈ S → s ≠ 0 → Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) σ μ s → μ ∈ A) → GlobalTheory.PsCo.Pc3.UFin := by
  first | exact @GlobalTheory.PsCo.Pc3.uFin_of' | exact GlobalTheory.PsCo.Pc3.uFin_of' | (intros; apply GlobalTheory.PsCo.Pc3.uFin_of' <;> assumption)
end

