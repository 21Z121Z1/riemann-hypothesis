import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0330
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0170
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDoubledHermitianSpaceRealPlace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0345
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1388
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1481
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1449
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1503
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1554
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEqZeroOfReal
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaSeriesTestFunctionHolomorphicWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0921
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0929
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0913
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1548
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Formalism.LocalToGlobal.IndefiniteReal.DatumF

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactAndIwasawaOf
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling

noncomputable section
namespace GlobalTheory.DblIwasawa

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem transpose_dblGram {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    (dblGram finSumFinEquiv J)ᵀ = dblGram finSumFinEquiv Jᵀ := by
  ext i j
  obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective i <;> obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective j <;>
    simp only [dblGram, blkMat, Matrix.transpose_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.zero_apply, Matrix.neg_apply]

theorem hasIwasawa_fin (hcm : IsCMExt F E σ) (hun : Algebra.Unramified (𝓞 F) (𝓞 E)) {n : ℕ} (X : Spc F E n)
    (hX : IsHermND σ X.J) (hL : X.L.IsLattice E)
    (hd : ∀ y, y ∈ X.L ↔ ∀ x ∈ X.L, IsIntegral ℤ (form σ X.J y x)) {Q : Matrix (Fin (n + n)) (Fin (n + n)) E}
    (hQ : Q = dblGram finSumFinEquiv X.Jᵀ) (v : HeightOneSpectrum (𝓞 F)) :
    HasIwasawa σ Q (KFin σ Q X.L v) := by
  haveI : Submodule.IsLattice E X.L := hL
  have hJt : IsHermND σ X.Jᵀ := ⟨fun i j => hX.1 j i, by rw [Matrix.det_transpose]; exact hX.2⟩
  have hSD : IsSelfDualAt σ X.Jᵀ X.L v := by
    refine (GlobalTheory.AdelicU.SelfDual.forall_isSelfDualAt_iff hJt.2 hL).2 (fun y => ?_) v
    rw [hd y]
    simp only [GlobalTheory.HermSelfDualLoc.hE_transpose, GlobalTheory.HermSelfDualLoc.isIntegral_iff_mem_range]
  have hQ' : IsHermND σ Q := hQ ▸ GlobalTheory.GraphIwSplit.isHermND_dblGram σ hJt
  haveI := hun
  have hU : Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) v :=
    GlobalTheory.LFun.isUnram_iff.2 fun w _ => Ideal.ramificationIdx_eq_one w.asIdeal (𝓞 F)
  rcases GlobalTheory.LFun.InertChart.isSplit_or_isInertAt hU with hs | ⟨w, hw⟩
  · obtain ⟨w, w', hne, h1, h2⟩ := GlobalTheory.LFun.isSplit_iff.1 hs
    exact GlobalTheory.Core.Rk.IwSplit.hasIwasawa_of_algHom hcm hQ hJt hQ'
      (GlobalTheory.AdelicU.existsUnique_splitPrime_eq hcm hne h1 h2).exists.choose X.L hSD
  · exact GlobalTheory.InertIwasawaGen.hasIwasawa_of_inertAt hcm hJt hQ hw hSD

section Arch

open Formalism.UG (bc UJ cT)

theorem arch (hcm : IsCMExt F E σ) (B : Base F E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (θ : InfinitePlace F → Matrix (Fin n) (Fin n) ℂ) (hJ : ∀ i j, σ (J j i) = J i j)
    (hθ : ∀ w, IsCartan (J.map (B.emb w).1) (θ w)) {Q : Matrix (Fin (n + n)) (Fin (n + n)) E}
    (hQ : Q = dblGram finSumFinEquiv Jᵀ) :
    ∃ a : GL (Fin n) (AF F ⊗[F] E), IsMajorantFrame σ Jᵀ a ∧ ∀ (w : InfinitePlace F) (k : GArch σ Q w),
      k ∈ KArch σ Q w (Formalism.UG.bc (compInf F E w) a) ↔
        Commute ((matHom w.Completion σ Q k).1.map (infEmb (B.emb w))) (blkMat finSumFinEquiv (θ w) (-θ w)) := by
  have hM : ∀ w : InfinitePlace F, (J.map (B.emb w).1)ᴴ = J.map (B.emb w).1 := fun w => by
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.map_apply]
    rw [← hcm.2.2.2 (B.emb w).1, hJ]
  have hC : ∀ w : InfinitePlace F, Formalism.IndefR.Datum.IsCartanInv (Jᵀ.map (B.emb w).1) (θ w) := fun w => by
    rw [Matrix.transpose_map]
    exact GlobalTheory.MajFrameCartan.isCartanInv_transpose (hM w) (hθ w)
  choose b ε h1 h2 using fun w => GlobalTheory.Doubling.exists_frame_of_isCartanInv (hC w)
  let e := fun w : InfinitePlace F => RingEquiv.ofBijective _ (infEmb_bijective hcm (B.emb w))
  let c : ∀ w : InfinitePlace F, GL (Fin n) (w.Completion ⊗[F] E) := fun w => bc (e w).symm.toRingHom (b w)
  have hc : ∀ w, (c w).1.map (infEmb (B.emb w)) = (b w).1 := fun w =>
    Matrix.ext fun i j => (e w).apply_symm_apply _
  have hc' : ∀ w, ((c w)⁻¹).1.map (infEmb (B.emb w)) = ((b w)⁻¹).1 := fun w => by
    rw [show (c w)⁻¹ = bc (e w).symm.toRingHom (b w)⁻¹ from (map_inv _ _).symm]
    exact Matrix.ext fun i j => (e w).apply_symm_apply _
  obtain ⟨a, -, ha⟩ := GlobalTheory.AdelicU.Frames.exists_GL_of_components (F := F) (E := E) (n := n) ∅ (fun _ => 1)
    (fun _ _ => rfl) c
  refine ⟨a, fun w => ⟨ε w, ?_⟩, fun w k => ?_⟩
  · rw [ha w, GlobalTheory.Doubling.frame_local_iff hcm (B.emb w) Jᵀ (c w).1 (ε w), hc]
    exact h1 w
  · have hK : ((matHom w.Completion σ Q k).1.map (infEmb (B.emb w)))ᴴ * Q.map (B.emb w).1 *
        (matHom w.Completion σ Q k).1.map (infEmb (B.emb w)) = Q.map (B.emb w).1 :=
      (archEquiv Q hcm (B.emb w) k).2
    have key : ∀ x : GL (Fin (n + n)) (w.Completion ⊗[F] E), x ∈ UJ (sigR w.Completion σ) 1 ↔
        (x.1.map (infEmb (B.emb w)))ᴴ * x.1.map (infEmb (B.emb w)) = 1 := fun x => by
      change cT _ x.1 * 1 * x.1 = 1 ↔ _
      rw [← (Matrix.map_injective (infEmb_bijective hcm (B.emb w)).1).eq_iff]
      beta_reduce
      rw [mul_one, Matrix.map_mul, Frames.map_cT_sigR hcm, Matrix.map_one _ (map_zero _) (map_one _)]
    have hcT : ∀ x y : Matrix (Fin n) (Fin n) ℂ,
        (blkMat finSumFinEquiv x y)ᴴ = blkMat finSumFinEquiv xᴴ yᴴ := fun x y => by
      simp [blkMat, Matrix.fromBlocks_conjTranspose]
    have hbc : blkMat finSumFinEquiv (b w).1 (b w).1 * blkMat finSumFinEquiv ((b w)⁻¹).1 ((b w)⁻¹).1 = 1 := by
      rw [blkMat_mul, Units.mul_inv, blkMat_one]
    have hQw : Q.map (B.emb w).1 =
        blkMat finSumFinEquiv (Jᵀ.map (B.emb w).1) (-(Jᵀ.map (B.emb w).1)) := by
      rw [hQ, dblGram, blkMat_map _ _ (map_zero _), Matrix.map_neg _ (map_neg _)]
    set D : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun i => if ε w i then 1 else -1 with hD
    have hd : (blkMat finSumFinEquiv (b w).1 (b w).1)ᴴ * Q.map (B.emb w).1 *
        blkMat finSumFinEquiv (b w).1 (b w).1 = blkMat finSumFinEquiv D (-D) := by
      rw [hcT, hQw, blkMat_mul, blkMat_mul, Matrix.mul_neg, Matrix.neg_mul, h1 w]
    have hdd : blkMat finSumFinEquiv D (-D) * blkMat finSumFinEquiv D (-D) = 1 := by
      rw [blkMat_mul, neg_mul_neg, hD, GlobalTheory.Doubling.diagonal_sign_mul_self, blkMat_one]
    have hs : blkMat finSumFinEquiv (b w).1 (b w).1 * (blkMat finSumFinEquiv (b w).1 (b w).1)ᴴ *
        Q.map (B.emb w).1 = blkMat finSumFinEquiv (θ w) (-θ w) := by
      rw [hcT, hQw, blkMat_mul, blkMat_mul, Matrix.mul_neg, h2 w]
    rw [← hs, ← GlobalTheory.Doubling.unitary_iff_commute hbc hd hdd hK]
    show _ ∈ stabArch σ Q w (blkGL finSumFinEquiv (_, _)) ↔ _
    rw [mem_stabArch, ha w, key, ← map_inv, Prod.inv_mk, Units.val_mul, Units.val_mul, val_blkGL, val_blkGL,
      Matrix.map_mul, Matrix.map_mul, blkMat_map _ _ (map_zero _), blkMat_map _ _ (map_zero _), hc, hc']

end Arch

theorem isCompact_and_iwasawaOf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ (B : Base F E) (n : ℕ) (X : Spc F E n),
    IsHermND σ X.J → X.L.IsLattice E → (∀ y, y ∈ X.L ↔ ∀ x ∈ X.L, IsIntegral ℤ (form σ X.J y x)) →
    (∀ w, IsCartan (X.J.map (B.emb w).1) (X.θ w)) → ∀ X₂ : Spc F E (n + n), X₂.J = dblGram finSumFinEquiv X.J →
    X₂.L = sumLat finSumFinEquiv X.L X.L → (∀ w, X₂.θ w = blkMat finSumFinEquiv (X.θ w) (-X.θ w)) →
    ∀ K : Subgroup (UA σ X₂.J), IsStab B K → IsCompact (K : Set (UA σ X₂.J)) ∧
      IwasawaOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype (absE F E) K := by
  intro F E _ _ _ _ _ σ hcm hun B n X hX hL hd hθ X₂ hJ₂ hL₂ hθ₂ K hK
  haveI : Submodule.IsLattice E X.L := hL
  have hQ : X₂.Jᵀ = dblGram finSumFinEquiv X.Jᵀ := by rw [hJ₂, transpose_dblGram]
  obtain ⟨a, hmaj, harch⟩ := arch hcm B X.J X.θ hX.1 hθ hQ
  have hI : HasIwasawa σ X₂.Jᵀ (KAd σ X₂.Jᵀ X.L a) := by
    refine HasIwasawa.adelic (fun v => hasIwasawa_fin hcm hun X hX hL hd hQ v) (fun w => ?_)
    obtain ⟨ε, hε⟩ := hmaj w
    exact GlobalTheory.Core.Rk.IwArch.hasIwasawa_KArch hcm hQ w _ ε hε
  have hL₂' : X₂.L.IsLattice E := by rw [hL₂]; infer_instance
  have key : ∀ g : GAd σ X₂.Jᵀ, GlobalTheory.IwLine.ofGAd σ X₂.J g ∈ K ↔ g ∈ KAd σ X₂.Jᵀ X.L a := by
    intro g
    rw [(hK _).trans (GlobalTheory.StabHaar.isStab_stabK (σ := σ) B X₂ _).symm, mem_KAd]
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := GlobalTheory.T.stabilizer_commutes_majorant F E σ B (n + n) X₂ hL₂' g h
      refine ⟨fun v => ?_, fun w => ?_⟩
      · have := h2 v; rwa [hL₂] at this
      · rw [harch w, ← hθ₂ w]; exact h1 w
    · rintro ⟨h2, h1⟩
      refine GlobalTheory.KBridge.ofGAd_mem_stabK F E σ B (n + n) X₂ hL₂' g (fun w => ?_) (fun v => ?_)
      · rw [hθ₂ w, ← harch w]; exact h1 w
      · rw [hL₂]; exact h2 v
  have hcont : Continuous (GlobalTheory.IwLine.ofGAd σ X₂.J) := Continuous.subtype_mk continuous_subtype_val _
  have hKset : (K : Set (UA σ X₂.J)) =
      GlobalTheory.IwLine.ofGAd σ X₂.J '' (KAd σ X₂.Jᵀ X.L a : Set (GAd σ X₂.Jᵀ)) := by
    ext g
    constructor
    · intro hg
      refine ⟨(GlobalTheory.IwLine.ofGAd σ X₂.J).symm g, (key _).1 (by rwa [MulEquiv.apply_symm_apply]),
        MulEquiv.apply_symm_apply _ _⟩
    · rintro ⟨g', hg', rfl⟩
      exact (key g').2 hg'
  have hKc : IsCompact (K : Set (UA σ X₂.J)) := by
    rw [hKset]; exact (isCompact_KAd hcm).image hcont
  refine ⟨hKc, ?_⟩
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : T2Space (AE F E) := t2Space_tensorProduct_finiteExtension (F := F) (E := E) (R := AF F)
  refine iwasawaOf_of_isCompact continuous_subtype_val continuous_absE hKc fun g => ?_
  obtain ⟨p, k, hk, e⟩ := hI ((GlobalTheory.IwLine.ofGAd σ X₂.J).symm g)
  have hp : (GlobalTheory.IwLine.ofGAd σ X₂.J p) ∈ siegelOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype := p.2
  refine ⟨⟨_, hp⟩, GlobalTheory.IwLine.ofGAd σ X₂.J k, (key k).2 hk, ?_⟩
  have := congrArg (GlobalTheory.IwLine.ofGAd σ X₂.J) e
  rw [MulEquiv.apply_symm_apply, map_mul] at this
  exact this

end GlobalTheory.DblIwasawa

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDblCoordDblD
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DblSchr

open Matrix

section Gen

variable {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem hTens_dbl (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α (β ⊕ β) E) :
    GlobalTheory.WeilM.hTens c JA (GlobalTheory.WeilM.dbl JB) x y =
      GlobalTheory.WeilM.hTens c JA JB x.toCols₁ y.toCols₁ - GlobalTheory.WeilM.hTens c JA JB x.toCols₂ y.toCols₂ := by
  unfold GlobalTheory.WeilM.hTens GlobalTheory.WeilM.dbl
  simp only [Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.toCols₁_apply, Matrix.toCols₂_apply, Matrix.zero_apply, Matrix.neg_apply,
    mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add, mul_neg, neg_mul, Finset.sum_neg_distrib,
    Finset.sum_add_distrib, sub_eq_add_neg]

theorem symp_dbl (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α (β ⊕ β) E) :
    GlobalTheory.WeilM.symp c ξ JA (GlobalTheory.WeilM.dbl JB) x y =
      GlobalTheory.WeilM.symp c ξ JA JB x.toCols₁ y.toCols₁ - GlobalTheory.WeilM.symp c ξ JA JB x.toCols₂ y.toCols₂ := by
  unfold GlobalTheory.WeilM.symp
  rw [hTens_dbl, mul_sub, map_sub]

theorem toCols₁_add' (x y : Matrix α (β ⊕ β) E) : (x + y).toCols₁ = x.toCols₁ + y.toCols₁ := rfl
theorem toCols₂_add' (x y : Matrix α (β ⊕ β) E) : (x + y).toCols₂ = x.toCols₂ + y.toCols₂ := rfl
theorem toCols₁_smul' (r : R) (x : Matrix α (β ⊕ β) E) : (r • x).toCols₁ = r • x.toCols₁ := rfl
theorem toCols₂_smul' (r : R) (x : Matrix α (β ⊕ β) E) : (r • x).toCols₂ = r • x.toCols₂ := rfl

variable [Invertible (2 : R)]

def dblD {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} {κ : Type} [Fintype κ]
    (d : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ JA JB) κ) :
    GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ JA (GlobalTheory.WeilM.dbl JB)) (κ ⊕ κ) where
  e :=
    { toFun := fun x => (Sum.elim (d.e x.toCols₁).1 (d.e x.toCols₂).1, Sum.elim (d.e x.toCols₁).2 (-(d.e x.toCols₂).2))
      invFun := fun q => Matrix.fromCols (d.e.symm (q.1 ∘ Sum.inl, q.2 ∘ Sum.inl))
        (d.e.symm (q.1 ∘ Sum.inr, -(q.2 ∘ Sum.inr)))
      map_add' := fun x y => by
        ext (i | i) <;> simp [toCols₁_add', toCols₂_add'] <;> abel
      map_smul' := fun r x => by
        ext (i | i) <;> simp [toCols₁_smul', toCols₂_smul']
      left_inv := fun x => by
        conv_rhs => rw [← Matrix.fromCols_toCols x]
        beta_reduce
        congr 1
        · exact d.e.symm_apply_apply x.toCols₁
        · have h : (((Sum.elim (d.e x.toCols₁).1 (d.e x.toCols₂).1) ∘ Sum.inr,
              -((Sum.elim (d.e x.toCols₁).2 (-(d.e x.toCols₂).2)) ∘ Sum.inr)) : (κ → R) × (κ → R)) =
              d.e x.toCols₂ := Prod.ext rfl (funext fun i => neg_neg _)
          exact (congrArg d.e.symm h).trans (d.e.symm_apply_apply _)
      right_inv := fun q => by
        ext (i | i) <;> simp }
  form w w' := by
    rw [symp_dbl, d.form, d.form]
    simp only [LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, dotProduct, Fintype.sum_sum_type, Sum.elim_inl,
      Sum.elim_inr, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
    ring

theorem isDblCoord_dblD {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} {κ : Type} [Fintype κ]
    (d : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ JA JB) κ) : GlobalTheory.WeilM.IsDblCoord c ξ JA JB d (dblD c d) := by
  intro w₁ w₂
  simp [dblD]

end Gen

section Reindex

variable {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
variable {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]

theorem symp_submatrix (e : γ ≃ β) (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α γ E) :
    GlobalTheory.WeilM.symp c ξ JA (JB.submatrix e e) x y =
      GlobalTheory.WeilM.symp c ξ JA JB (x.submatrix id e.symm) (y.submatrix id e.symm) := by
  unfold GlobalTheory.WeilM.symp GlobalTheory.WeilM.hTens
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← e.symm.sum_comp]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← e.symm.sum_comp]
  simp

variable [Invertible (2 : R)]

def reD (e : γ ≃ β) {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} {J' : Matrix γ γ E} (h : J' = JB.submatrix e e)
    {κ : Type} [Fintype κ] (d : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ JA JB) κ) :
    GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ JA J') κ where
  e := (Matrix.reindexLinearEquiv R E (Equiv.refl α) e).trans d.e
  form w w' := by
    rw [h, symp_submatrix, d.form]
    rfl

theorem reD_e (e : γ ≃ β) {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} {J' : Matrix γ γ E} (h : J' = JB.submatrix e e)
    {κ : Type} [Fintype κ] (d : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ JA JB) κ) (x : Matrix α γ E) :
    (reD c e h d).e x = d.e (x.submatrix id e.symm) := rfl

end Reindex

section Group

variable {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
variable {β γ : Type} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]

def reG (e : γ ≃ β) {J : Matrix β β E} {J' : Matrix γ γ E} (h : J' = J.submatrix e e) :
    GlobalTheory.WeilM.UG c J →* GlobalTheory.WeilM.UG c J' :=
  ((Units.map (Matrix.reindexAlgEquiv E E e.symm).toAlgHom.toMonoidHom).comp (GlobalTheory.WeilM.UG c J).subtype).codRestrict
    (GlobalTheory.WeilM.UG c J') fun g => by
      have hg : ((g : GL β E) : Matrix β β E)ᵀ * J * ((g : GL β E) : Matrix β β E).map c = J := g.2
      show (((g : GL β E) : Matrix β β E).submatrix e e)ᵀ * J' * (((g : GL β E) : Matrix β β E).submatrix e e).map c = J'
      rw [h, Matrix.transpose_submatrix, ← Matrix.submatrix_map, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, hg]

theorem reG_val (e : γ ≃ β) {J : Matrix β β E} {J' : Matrix γ γ E} (h : J' = J.submatrix e e) (g : GlobalTheory.WeilM.UG c J) :
    ((reG c e h g : GL γ E) : Matrix γ γ E) = ((g : GL β E) : Matrix β β E).submatrix e e := rfl

end Group

section Host

variable {D : D7}

def JBd (S : HSp D) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E) :
    Matrix (Fin (GlobalTheory.Doubling.dblSp S).rank) (Fin (GlobalTheory.Doubling.dblSp S).rank) D.host.E :=
  (GlobalTheory.WeilM.dbl JB).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

theorem incM_JBd (S : HSp D) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E) :
    incM D.host.F (JBd S JB) =
      (GlobalTheory.WeilM.dbl (incM D.host.F JB)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
  ext i j
  rcases h1 : finSumFinEquiv.symm i with i' | i' <;> rcases h2 : finSumFinEquiv.symm j with j' | j' <;>
    simp [JBd, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, GlobalTheory.WeilM.dbl, h1, h2]

variable [Invertible (2 : AF D.host.F)]

def ddr {S T : HSp D} {ξ : AF D.host.F ⊗[D.host.F] D.host.E} {JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E}
    {JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E} {κ : Type} [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ) :
    GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F (JBd S JB)))
      (κ ⊕ κ) :=
  reD _ finSumFinEquiv.symm (incM_JBd S JB) (dblD _ co)

end Host

section HostGroup

variable {D : D7}

def omdOf {S T : HSp D} {JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E}
    {JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E} {X : Type} [AddCommGroup X] [Module ℂ X]
    (omd₀ : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F (JBd S JB)) →* Module.End ℂ X) :
    GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.dbl (incM D.host.F JB)) →* Module.End ℂ X :=
  omd₀.comp ((MonoidHom.inr _ _).comp (reG _ finSumFinEquiv.symm (incM_JBd S JB)))

end HostGroup

end GlobalTheory.DblSchr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockVacAtOfReads
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.FockVac

theorem hasDerivAt_translate {n g : ℕ} (c : Fin g → ℝ) (H : (Fin g → ℂ) → (Fin g → ℂ) → ℂ)
    (hH : ∀ z w, H z w = ∑ j, (c j : ℂ) * z j * conj (w j)) (F : (Fin n → Fin g → ℂ) → ℂ) (hF : Differentiable ℂ F)
    (Z A : Fin n → Fin g → ℂ) :
    HasDerivAt (fun t : ℝ => cexp (Real.pi * I * ((∑ b, (H (Z b) (((t : ℂ) • A) b)).im : ℝ) : ℂ)) *
      (cexp (-(Real.pi / 2 : ℂ) * ∑ b, H ((Z + (t : ℂ) • A) b) ((Z + (t : ℂ) • A) b)) * F (Z + (t : ℂ) • A)))
      (cexp (-(Real.pi / 2 : ℂ) * ∑ b, H (Z b) (Z b)) *
        (-(Real.pi * ∑ b, H (A b) (Z b)) * F Z + fderiv ℂ F Z A)) 0 := by
  have hc : ∀ z w, conj (H z w) = H w z := fun z w => by
    simp only [hH, map_sum, map_mul, conj_ofReal, conj_conj]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have e : (fun t : ℝ => cexp (Real.pi * I * ((∑ b, (H (Z b) (((t : ℂ) • A) b)).im : ℝ) : ℂ)) *
      (cexp (-(Real.pi / 2 : ℂ) * ∑ b, H ((Z + (t : ℂ) • A) b) ((Z + (t : ℂ) • A) b)) * F (Z + (t : ℂ) • A))) =
      fun t : ℝ => (fun u : ℂ => cexp (-(Real.pi / 2 : ℂ) * ∑ b, H (Z b) (Z b) + (-(Real.pi * ∑ b, H (A b) (Z b)) * u +
        -(Real.pi / 2 : ℂ) * (∑ b, H (A b) (A b)) * u ^ 2)) * F (Z + u • A)) t := by
    funext t
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    have h1 : ∀ b, I * ((H (Z b) (((t : ℂ) • A) b)).im : ℂ) = t * (H (Z b) (A b) - H (A b) (Z b)) / 2 := fun b => by
      have h2 : H (Z b) (((t : ℂ) • A) b) = t * H (Z b) (A b) := by
        simp only [hH, Pi.smul_apply, smul_eq_mul, map_mul, conj_ofReal, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring
      rw [h2, ← hc (Z b) (A b), Complex.sub_conj, Complex.im_ofReal_mul]
      push_cast
      ring
    have h3 : ∀ b, H ((Z + (t : ℂ) • A) b) ((Z + (t : ℂ) • A) b) =
        H (Z b) (Z b) + t * H (Z b) (A b) + t * H (A b) (Z b) + t ^ 2 * H (A b) (A b) := fun b => by
      simp only [hH, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_mul, map_add, conj_ofReal, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [Complex.ofReal_sum, mul_assoc, Finset.mul_sum]
    simp only [h1, h3, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div, Finset.sum_sub_distrib]
    ring
  rw [e]
  refine HasDerivAt.comp_ofReal (e := fun u : ℂ => cexp (-(Real.pi / 2 : ℂ) * ∑ b, H (Z b) (Z b) +
    (-(Real.pi * ∑ b, H (A b) (Z b)) * u + -(Real.pi / 2 : ℂ) * (∑ b, H (A b) (A b)) * u ^ 2)) * F (Z + u • A)) ?_
  rw [Complex.ofReal_zero]
  have h1 : HasDerivAt (fun u : ℂ => Z + u • A) A 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const A).const_add Z
  have h2 : HasDerivAt (fun u : ℂ => F (Z + u • A)) (fderiv ℂ F Z A) 0 := by
    have := (hF (Z + (0 : ℂ) • A)).hasFDerivAt.comp_hasDerivAt (0 : ℂ) h1
    rwa [zero_smul, add_zero] at this
  have h3 := ((((hasDerivAt_id (0 : ℂ)).const_mul (-(Real.pi * ∑ b, H (A b) (Z b)))).fun_add
    ((hasDerivAt_pow 2 (0 : ℂ)).const_mul (-(Real.pi / 2 : ℂ) * (∑ b, H (A b) (A b))))).const_add
      (-(Real.pi / 2 : ℂ) * ∑ b, H (Z b) (Z b))).cexp.fun_mul h2
  refine h3.congr_deriv ?_
  simp only [id, zero_smul, add_zero, mul_zero, mul_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    Nat.add_one_sub_one, pow_one]
  ring

theorem isFockVacAt_of_reads : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsStdChar D ψ (-1) → IsInfFam θ → V.gram = 1 → Even V.rank → IsMod W hr X → IsSympl X bas → ∀ (x : Frame X.Ψ r) (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ), IsONFr X x → IsInvOf W hr X x s → ∀ (f : WO V W → ℂ) (φ : TF V.rank g), IsThetaFunO ψ V W f → Reads θ V W hr X bas idx f φ x → ∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO 1 (s τ)) f := by
  intro D ψ θ V W r g hr X bas idx hψ hθ hV hev hm hs x s hx0 hinv f φ hf hR τ z
  obtain ⟨hd, -, hH⟩ := hx_of_isONFr _ r g V.rank X bas idx hs hev x hx0
  obtain ⟨-, hadd, hline, -⟩ := RealCoord.zOf_coordinates D ψ θ V W r g hr X bas idx hψ hθ hV hev hm hs x
  have hJ := (GlobalTheory.FrameCplx.cplx_of_frame D ψ θ V W r g hr X bas idx hψ hθ hV hev hm hs x s hx0 hinv).2.2 τ z
  have hF := GlobalTheory.SW.ThetaHol.differentiable_thA idx hs hR.1 hd
  refine GlobalTheory.TwistFactorCompare.theta_eq_zero_of_real (WeilVacMove.isTheta_add (WeilVacMove.isTheta_dRho hψ hθ τ z hf)
    (WeilVacMove.isTheta_smul I (WeilVacMove.isTheta_dRho hψ hθ τ _ hf))) fun w hw => ?_
  have hw' : w.map (finPart D) = 0 := hw
  have key : ∀ u, Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ u f w =
      cexp (-(Real.pi / 2 : ℂ) * ∑ b, hx X bas idx x (zOf θ V W hr X idx x w b) (zOf θ V W hr X idx x w b)) *
        (-(Real.pi * ∑ b, hx X bas idx x (zOf θ V W hr X idx x (lineAt θ τ u 1) b) (zOf θ V W hr X idx x w b)) *
          thA X bas idx φ x (zOf θ V W hr X idx x w) +
          fderiv ℂ (thA X bas idx φ x) (zOf θ V W hr X idx x w) (zOf θ V W hr X idx x (lineAt θ τ u 1))) := fun u => by
    rw [← (hasDerivAt_translate _ _ hH _ hF _ _).deriv]
    unfold Formalism.IndefR.Datum.dRho
    congr 1
    funext t
    have h0 : (w + lineAt θ τ u t).map (finPart D) = 0 := by
      rw [Matrix.map_add _ (finPart D).map_add, hw', (WeilVacMove.isLineAt_lineAt hθ τ u).2.1 t, add_zero]
    rw [heisO, GlobalTheory.AdThSympl.psi_symplOH_eq_of_isONFr D ψ θ V W r g hr X bas idx hψ hθ hV hev hm hs x hx0 w _ hw', hR.2 _ h0, hadd, hline]
  have hI : ∀ a b : Fin g → ℂ, hx X bas idx x (I • a) b = I * hx X bas idx x a b := fun a b => by
    simp only [hH, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [annih, Pi.add_apply, Pi.smul_apply, key, key, hJ, map_smul]
  simp only [Pi.smul_apply, hI, ← Finset.mul_sum, smul_eq_mul]
  linear_combination (cexp (-(Real.pi / 2 : ℂ) * ∑ b, hx X bas idx x (zOf θ V W hr X idx x w b) (zOf θ V W hr X idx x w b)) *
        (-(Real.pi * ∑ b, hx X bas idx x (zOf θ V W hr X idx x (lineAt θ τ z 1) b) (zOf θ V W hr X idx x w b)) *
          thA X bas idx φ x (zOf θ V W hr X idx x w) +
          fderiv ℂ (thA X bas idx φ x) (zOf θ V W hr X idx x w) (zOf θ V W hr X idx x (lineAt θ τ z 1)))) * I_mul_I

end GlobalTheory.AdTh.FockVac
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralBaseChangeRationalFunctionFieldFiniteVStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic
open GlobalTheory.ThickeningDetermines (secIdeal)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_baseChange_rationalFunctionField_finiteVars : ∀ (k : Type) [Field k] (N : ℕ) (X X' : Scheme.{0}) [IsIntegral X] (f : X ⟶ Sp k) (f' : X' ⟶ Sp (FractionRing (MvPolynomial (Fin N) k))) (π : X' ⟶ X), IsPullback π f' f (spMap (algebraMap k (FractionRing (MvPolynomial (Fin N) k)))) → IsIntegral X' := by
  first | exact @GlobalTheory.PureTransc.isIntegral_of_isPullback | exact GlobalTheory.PureTransc.isIntegral_of_isPullback | (intros; apply GlobalTheory.PureTransc.isIntegral_of_isPullback <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransportF
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.WeilSchrodinger

open Formalism.IndefR.DatumF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def IsTransportF (σ : E →ₐ[F] E) {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
    (ψ : AddChar (AF F) ℂ) {ξ : AF F ⊗[F] E} {JA : Matrix (Fin nT) (Fin nT) E} {JB : Matrix (Fin nS) (Fin nS) E}
    {κ : Type} [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ)
    (ω : GAF σ JS × GAF σ JT →* Module.End ℂ (WOF F E nS nT → ℂ))
    (om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ)) : Prop :=
  ∀ (a : UG (cA σ) (incM F JA)) (b : UG (cA σ) (incM F JB)) (g : GAF σ JS) (h : GAF σ JT),
    mtF σ JT h = a.1.1 → mtF σ JS g = (b⁻¹).1.1ᵀ →
    ∀ Φ ∈ schA F κ, om (a, b) Φ ∈ schA F κ ∧ thetaTr F co ψ (om (a, b) Φ) = ω (g, h) (thetaTr F co ψ Φ)

end GlobalTheory.WeilSchrodinger

end
end

