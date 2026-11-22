import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0176
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0013
import Formalism.LocalToGlobal.IndefiniteReal.LinksExist
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0174
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FactTypePrime
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0173
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0175
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstAddCommGroupTwo

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentBesselCharacterLaws
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CharLaws

variable {D : D7}

section Conj

variable {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

theorem embedded_anisotropic_inv_fixes_isotropic (k : GA D S₀) : mt S (d.emb0 k)⁻¹ ⬝ d.jX = d.jX := by
  rw [← map_inv]; exact d.wittDecomp_anisotropicEmbedding_inclX k⁻¹

theorem witt_isotropic_projection_embedded_anisotropic_mul {m : ℕ} (k : GA D S₀) (x : Mx D S.rank m) : d.pX ⬝ (mt S (d.emb0 k) ⬝ x) = d.pX ⬝ x := by
  rw [← Matrix.mul_assoc, d.wittDecomp_projX_anisotropicEmbedding]

theorem blockX_conj (k : GA D S₀) (n : GA D S) :
    blockX d (d.emb0 k * n * (d.emb0 k)⁻¹) = blockX d n := by
  rw [blockX, blockX, mt_mul, mt_mul]
  simp only [Matrix.mul_assoc]
  rw [embedded_anisotropic_inv_fixes_isotropic, witt_isotropic_projection_embedded_anisotropic_mul]

theorem coefX_conj (k : GA D S₀) (n : GA D S) (z : Fin S₀.rank → D.host.E)
    (hz : mt S₀ k⁻¹ *ᵥ ratV z = ratV z) :
    coefX d z (d.emb0 k * n * (d.emb0 k)⁻¹) = coefX d z n := by
  rw [coefX, coefX, mt_mul, mt_mul, ← map_inv]
  simp only [Matrix.mul_assoc]
  rw [d.wittDecomp_anisotropicEmbedding_inclAnisotropic, witt_isotropic_projection_embedded_anisotropic_mul]
  have e : d.pX ⬝ (mt S n ⬝ (d.j0 ⬝ mt S₀ k⁻¹)) = d.pX ⬝ (mt S n ⬝ d.j0) ⬝ mt S₀ k⁻¹ := by
    simp only [Matrix.mul_assoc]
  rw [e, ← Matrix.mulVec_mulVec, hz]

theorem conj_mem_flagN (k : GA D S₀) {n : GA D S} (hn : n ∈ flagN d) :
    d.emb0 k * n * (d.emb0 k)⁻¹ ∈ flagN d := by
  have hi := (isIsoSub_e d).1
  change n ∈ NFlag S d.e at hn
  change _ ∈ NFlag S d.e
  rw [GlobalTheory.BesselChar.mem_NFlag_iff S d.e hi] at hn ⊢
  have he : mt S (d.emb0 k) ⬝ d.e.map (incA D) = d.e.map (incA D) := d.wittDecomp_anisotropicEmbedding_inclX k
  have he' : mt S (d.emb0 k)⁻¹ ⬝ d.e.map (incA D) = d.e.map (incA D) := embedded_anisotropic_inv_fixes_isotropic d k
  rw [mt_mul, mt_mul]
  exact hn.conj he he' (mt_mul_inv S _) (GlobalTheory.BesselChar.perp_fixed d.e _ he')

end Conj

section Cont

variable (ψ : AddChar (AF D.host.F) ℂ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

theorem continuous_psiBes (hψ : Continuous ψ) (θ : D.host.E) (z : Fin S₀.rank → D.host.E) :
    Continuous (psiBes ψ d θ z) := by
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have ht : Continuous (Algebra.trace (AF D.host.F) (AE D)) := IsModuleTopology.continuous_of_linearMap _
  have hm : Continuous (mt S) := GlobalTheory.MixModel.continuous_mt S
  have hb : Continuous fun g => blockX d g := continuous_const.matrix_mul (hm.matrix_mul continuous_const)
  have hc : Continuous fun g => coefX d z g :=
    (continuous_const.matrix_mul (hm.matrix_mul continuous_const)).matrix_mulVec continuous_const
  have hu : Continuous fun g => upSum (blockX d g) := by
    unfold upSum
    refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
    split_ifs
    · exact (continuous_apply j).comp ((continuous_apply i).comp hb)
    · exact continuous_const
  have hd : Continuous fun g => ell D ρ ⬝ᵥ coefX d z g := continuous_const.dotProduct hc
  exact hψ.comp (ht.comp (continuous_const.mul (hu.add hd)))

end Cont

end GlobalTheory.CharLaws

namespace GlobalTheory.CharLaws

variable {D : D7}

section Rat

variable (ψ : AddChar (AF D.host.F) ℂ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

theorem upSum_rat (N : Matrix (Fin ρ) (Fin ρ) D.host.E) :
    upSum (rat N) = incA D (∑ i : Fin ρ, ∑ j : Fin ρ, if j.1 = i.1 + 1 then N i j else 0) := by
  simp only [upSum, rat, Matrix.map_apply, map_sum, apply_ite (incA D), map_zero]

theorem ratV_dotProduct {m : ℕ} (a b : Fin m → D.host.E) : ratV a ⬝ᵥ ratV b = incA D (a ⬝ᵥ b) := by
  simp only [dotProduct, ratV, map_sum, map_mul]

theorem ell_eq : ell D ρ = ratV (fun i : Fin ρ => if i.1 + 1 = ρ then (1 : D.host.E) else 0) := by
  funext i
  simp only [ell, ratV]
  split_ifs <;> simp

theorem simpleSum_rat (z : Fin S₀.rank → D.host.E) {γ : GA D S} (hγ : γ ∈ GQ S) :
    ∃ x : D.host.E, simpleSum d z γ = incA D x := by
  obtain ⟨M, hM⟩ := (mem_GQ_iff S γ).1 hγ
  have hM' : rat M = mt S γ := hM
  have hb : blockX d γ = rat (d.qX * (M * d.e)) := by
    rw [blockX, ← hM', rat_mul, rat_mul]; rfl
  have hc : coefX d z γ = ratV ((d.qX * (M * d.i₀)) *ᵥ z) := by
    rw [coefX, ← hM', ratV_mulVec, rat_mul, rat_mul]; rfl
  rw [simpleSum, hb, hc, upSum_rat, ell_eq, ratV_dotProduct, ← map_add]
  exact ⟨_, rfl⟩

theorem psiBes_rat (hψ : ∀ a : D.host.F, ψ (algebraMap D.host.F (AF D.host.F) a) = 1) (θ : D.host.E)
    (z : Fin S₀.rank → D.host.E) {γ : GA D S} (hγ : γ ∈ GQ S) : psiBes ψ d θ z γ = 1 := by
  obtain ⟨x, hx⟩ := simpleSum_rat d z hγ
  rw [psiBes, hx, ← map_mul, psiE, GlobalTheory.BesselChar.trace_incA]
  exact hψ _

end Rat

end GlobalTheory.CharLaws

namespace GlobalTheory.CharLaws

variable {D : D7}

section Bes

variable (ψ : AddChar (AF D.host.F) ℂ) {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L)

theorem emb_vecB (a : GA D A) (ζ : Fin L.rank → D.host.E) :
    mt S₀ (o.emb (a, 1)) *ᵥ ratV (vecB o ζ) = ratV (vecB o ζ) := by
  rw [vecB, ratV_mulVec, Matrix.mulVec_mulVec]
  change (mt S₀ (o.emb (a, 1)) ⬝ o.jB) *ᵥ _ = o.jB *ᵥ _
  rw [o.emb_jB, mt_one, Matrix.mul_one]

theorem psiBes_conj (θ : D.host.E) (ζ : Fin L.rank → D.host.E) (n : GA D S) (h : GA D A) :
    psiBes ψ d θ (vecB o ζ) (embA d o h * n * (embA d o h)⁻¹) = psiBes ψ d θ (vecB o ζ) n := by
  have hz : mt S₀ (o.emb (h, 1))⁻¹ *ᵥ ratV (vecB o ζ) = ratV (vecB o ζ) := by
    rw [← map_inv, Prod.inv_mk, inv_one]; exact emb_vecB o h⁻¹ ζ
  rw [embA_apply, psiBes, psiBes, simpleSum, simpleSum, blockX_conj, coefX_conj d _ n _ hz]

theorem psiFlag_conj (n : GA D S) (h : GA D S₀) :
    psiFlag ψ d (d.emb0 h * n * (d.emb0 h)⁻¹) = psiFlag ψ d n := by
  rw [psiFlag, psiFlag, blockX_conj]

theorem embA_conj_mem (h : GA D A) {n : GA D S} (hn : n ∈ flagN d) :
    embA d o h * n * (embA d o h)⁻¹ ∈ flagN d :=
  conj_mem_flagN d _ hn

theorem mem_besGrp (g : GA D S) : g ∈ besGrp d o ↔ ∃ n ∈ flagN d, ∃ h, g = n * embA d o h := by
  constructor
  · intro hg
    let K : Subgroup (GA D S) :=
      { carrier := {g | ∃ n ∈ flagN d, ∃ h, g = n * embA d o h}
        one_mem' := ⟨1, one_mem _, 1, by rw [map_one, mul_one]⟩
        mul_mem' := by
          rintro _ _ ⟨n₁, hn₁, h₁, rfl⟩ ⟨n₂, hn₂, h₂, rfl⟩
          refine ⟨n₁ * (embA d o h₁ * n₂ * (embA d o h₁)⁻¹), mul_mem hn₁ (embA_conj_mem d o h₁ hn₂), h₁ * h₂, ?_⟩
          rw [map_mul]; group
        inv_mem' := by
          rintro _ ⟨n, hn, h, rfl⟩
          refine ⟨embA d o h⁻¹ * n⁻¹ * (embA d o h⁻¹)⁻¹, embA_conj_mem d o h⁻¹ (inv_mem hn), h⁻¹, ?_⟩
          rw [map_inv]; group }
    have hle : besGrp d o ≤ K := sup_le (fun n hn => ⟨n, hn, 1, by rw [map_one, mul_one]⟩)
      (by rintro _ ⟨h, rfl⟩; exact ⟨1, one_mem _, h, (one_mul _).symm⟩)
    exact hle hg
  · rintro ⟨n, hn, h, rfl⟩
    exact mul_mem (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right ⟨h, rfl⟩)

theorem embRel_embA (ι : A.V →ₗ[D.host.E] S.V) (hι : frameMat S A ι = d.i₀ * o.iA) (h : GA D A) :
    EmbRel S A ι (embA d o h) h := by
  rw [EmbRel, hι]
  refine ⟨?_, fun x hx => ?_⟩
  · change mt S (d.emb0 (o.emb (h, 1))) ⬝ rat (d.i₀ * o.iA) = rat (d.i₀ * o.iA) ⬝ mt A h
    rw [rat_mul]
    change mt S (d.emb0 (o.emb (h, 1))) ⬝ (d.j0 ⬝ o.jA) = d.j0 ⬝ o.jA ⬝ mt A h
    rw [← Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, Matrix.mul_assoc, o.emb_jA, Matrix.mul_assoc]
  · have hι₂ : frameMat S₀ A (Matrix.toLin A.frame S₀.frame o.iA) = o.iA := LinearMap.toMatrix_toLin _ _ _
    have hA := (o.embRel_left _ hι₂ h).2
    rw [hι₂] at hA
    have hw : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) o.iA * S₀.gram) *ᵥ (d.q0 *ᵥ x) = 0 := by
      rw [Matrix.mulVec_mulVec, cT_sig, HypDec.q0]
      have e : o.iAᴴ * S₀.gram * (S₀.gram⁻¹ * (d.i₀ᴴ * S.gram)) = (d.i₀ * o.iA)ᴴ * S.gram := by
        rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc S₀.gram,
          Matrix.mul_nonsing_inv _ (gram_isUnit_det S₀), Matrix.one_mul, Matrix.mul_assoc]
      rw [e, ← cT_sig]; exact hx
    have h1 : mt S₀ (o.emb (h, 1)) *ᵥ ratV (d.q0 *ᵥ x) = ratV (d.q0 *ᵥ x) := hA _ hw
    have h2 : d.p0 *ᵥ ratV x = ratV (d.q0 *ᵥ x) := (ratV_mulVec _ _).symm
    have h3 := congrArg (· *ᵥ ratV x) d.sum_eq_one
    change mt S (d.emb0 (o.emb (h, 1))) *ᵥ ratV x = ratV x
    simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, Matrix.one_mulVec] at h3
    rw [d.unitaryMatrix_wittCoreEmbedding]
    simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec]
    rw [h2, h1, ← h2]
    exact h3

end Bes

end GlobalTheory.CharLaws

namespace GlobalTheory.MixPer

theorem charLaws : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (S S₀ A L : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E) (θ : D.host.E), (∀ z, Continuous (psiBes ψ d θ z)) ∧ (∀ z, ∀ γ ∈ GQ S, psiBes ψ d θ z γ = 1) ∧ (∀ n h, psiBes ψ d θ (vecB o ζ) (embA d o h * n * (embA d o h)⁻¹) = psiBes ψ d θ (vecB o ζ) n) ∧ (∀ n h, psiFlag ψ d (d.emb0 h * n * (d.emb0 h)⁻¹) = psiFlag ψ d n) ∧ (∀ g, g ∈ besGrp d o ↔ ∃ n ∈ flagN d, ∃ h, g = n * embA d o h) ∧ ∀ ι : A.V →ₗ[D.host.E] S.V, frameMat S A ι = d.i₀ * o.iA → ∀ h, EmbRel S A ι (embA d o h) h := by
  intro D ψ hψ S S₀ A L ρ d o ζ θ
  exact ⟨fun z => GlobalTheory.CharLaws.continuous_psiBes ψ d hψ.1 θ z,
    fun z γ hγ => GlobalTheory.CharLaws.psiBes_rat ψ d hψ.2.2.1 θ z hγ,
    fun n h => GlobalTheory.CharLaws.psiBes_conj ψ d o θ ζ n h,
    fun n h => GlobalTheory.CharLaws.psiFlag_conj ψ d n h,
    fun g => GlobalTheory.CharLaws.mem_besGrp d o g,
    fun ι hι h => GlobalTheory.CharLaws.embRel_embA d o ι hι h⟩

end GlobalTheory.MixPer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockNormMinorProductDeltaAtEmbeddingPos
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockDelta

variable {D : D7}

theorem minor_ne_zero {m n : ℕ} (τ : D.what₂.Tau) (a b k : ℕ) (ha : a + k ≤ m) (hb : b + k ≤ n) :
    (Matrix.of fun α β : Fin k =>
      (varF τ (a + (β : ℕ)) (b + (α : ℕ)) : MvPolynomial (FVar D m n) ℂ)).det ≠ 0 := by
  intro h
  have hev := congrArg (MvPolynomial.eval fun y : FVar D m n =>
    if (y.2.1 : ℕ) + b = (y.2.2 : ℕ) + a then (1 : ℂ) else 0) h
  rw [RingHom.map_det, map_zero] at hev
  have hI : (MvPolynomial.eval fun y : FVar D m n =>
      if (y.2.1 : ℕ) + b = (y.2.2 : ℕ) + a then (1 : ℂ) else 0).mapMatrix
      (Matrix.of fun α β : Fin k => (varF τ (a + (β : ℕ)) (b + (α : ℕ)) : MvPolynomial (FVar D m n) ℂ)) = 1 := by
    ext α β
    have hα := α.isLt
    have hβ := β.isLt
    have hc : a + (β : ℕ) < m ∧ b + (α : ℕ) < n := ⟨by omega, by omega⟩
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.one_apply]
    unfold varF
    rw [dif_pos hc, MvPolynomial.eval_X]
    dsimp only
    split_ifs with h1 h2 h2
    · rfl
    · exact (h2 (Fin.ext (by omega))).elim
    · exact (h1 (by subst h2; omega)).elim
    · rfl
  rw [hI, Matrix.det_one] at hev
  exact one_ne_zero hev

theorem minorPlus_ne_zero {m n : ℕ} (τ : D.what₂.Tau) (k : ℕ) (hm : k ≤ m) (hn : k ≤ n) :
    (minorPlus τ k : MvPolynomial (FVar D m n) ℂ) ≠ 0 := by
  unfold minorPlus
  have h := minor_ne_zero (D := D) (m := m) (n := n) τ 0 0 k (by omega) (by omega)
  simpa only [zero_add] using h

theorem minorMinus_ne_zero {m n : ℕ} (τ : D.what₂.Tau) (p k : ℕ) (hm : p + k ≤ m) (hn : k ≤ n) :
    (minorMinus τ p k : MvPolynomial (FVar D m n) ℂ) ≠ 0 := by
  unfold minorMinus
  exact minor_ne_zero τ p (n - k) k hm (by omega)

theorem deltaAt_ne_zero {m n : ℕ} (τ : D.what₂.Tau) (p : ℕ) (ap : ℕ → ℕ) (q : ℕ) (am : ℕ → ℕ)
    (hpq : p + q ≤ m) (hmn : m ≤ n) :
    (deltaAt τ p ap q am : MvPolynomial (FVar D m n) ℂ) ≠ 0 := by
  unfold deltaAt
  refine mul_ne_zero ?_ ?_
  · refine Finset.prod_ne_zero_iff.mpr fun i hi => pow_ne_zero _ (minorPlus_ne_zero τ (i + 1) ?_ ?_)
    · have := Finset.mem_range.mp hi
      omega
    · have := Finset.mem_range.mp hi
      omega
  · refine Finset.prod_ne_zero_iff.mpr fun i hi => pow_ne_zero _ (minorMinus_ne_zero τ p (i + 1) ?_ ?_)
    · have := Finset.mem_range.mp hi
      omega
    · have := Finset.mem_range.mp hi
      omega

theorem delta_ne_zero {m n : ℕ} (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ)
    (hpq : ∀ τ, p τ + q τ ≤ m) (hmn : m ≤ n) :
    (delta p q ap am : MvPolynomial (FVar D m n) ℂ) ≠ 0 := by
  unfold delta
  exact Finset.prod_ne_zero_iff.mpr fun τ _ => deltaAt_ne_zero τ _ _ _ _ (hpq τ) hmn

theorem fock_self_pos {σ : Type*} (P : MvPolynomial σ ℂ) (hP : P ≠ 0) :
    ∃ a : ℝ, 0 < a ∧ Formalism.E.fock P P = (a : ℂ) := by
  refine ⟨∑ m ∈ P.support, Complex.normSq (P.coeff m) * (Formalism.A.mfact m : ℝ), ?_, ?_⟩
  · refine Finset.sum_pos (fun m hm => mul_pos ?_ ?_) ?_
    · exact Complex.normSq_pos.mpr (MvPolynomial.mem_support_iff.mp hm)
    · unfold Formalism.A.mfact
      exact Nat.cast_pos.mpr (Finset.prod_pos fun i _ => Nat.factorial_pos _)
    · exact Finset.nonempty_iff_ne_empty.mpr fun he => hP (MvPolynomial.support_eq_empty.mp he)
  · unfold Formalism.E.fock
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Complex.ofReal_mul, Complex.star_def, Complex.mul_conj, Complex.ofReal_natCast]

end GlobalTheory.FockDelta

open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues in

theorem GlobalTheory.FockDelta.fock_deltaAtEmb_pos :
    ∀ (D : D7) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), ∃ a : ℝ, 0 < a ∧
      Formalism.E.fock (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.deltaAtEmb D i σ) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.deltaAtEmb D i σ) = (a : ℂ) := by
  intro D i σ
  apply GlobalTheory.FockDelta.fock_self_pos
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.deltaAtEmb
  have hi := i.isLt
  have hW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (by omega) (by omega)
  apply GlobalTheory.FockDelta.delta_ne_zero
  · intro ρ
    exact le_of_eq (Formalism.BasicNotions.sig_sum _ (D.sp.W_sig _) _)
  · rw [hW]
    exact r_le_V i
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameAdjointMapReframedHermitianSpace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open GlobalTheory.AdSpan.ReVec
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdSpan.ReVec.FrMap

variable {D : D7}

theorem gram_reS (S : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) :
    (reS S b).gram = (frP S b)ᴴ * S.gram * frP S b := by
  funext i j
  have hb : ∀ k, b k = ∑ l, frP S b l k • S.frame l := fun k => by
    unfold frP
    simp only [Module.Basis.toMatrix_apply]
    exact (S.frame.sum_repr (b k)).symm
  show S.hT (b i) (b j) = ∑ l, (∑ k, star (frP S b k i) * S.hT (S.frame k) (S.frame l)) * frP S b l j
  rw [hb i, hb j]
  simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Finset.sum_mul, Finset.mul_sum, RingHom.id_apply, starRingEnd_apply]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem inv_eq_of_gram_conjTranspose_change {n : ℕ} {K : Type} [Field K] [StarRing K] (G G' P Q : Matrix (Fin n) (Fin n) K)
    (hG : G' = Pᴴ * G * P) (hQP : Q * P = 1) (hPQ : P * Q = 1) : G'⁻¹ = Q * G⁻¹ * Qᴴ := by
  have h1 : P⁻¹ = Q := Matrix.inv_eq_left_inv hQP
  have h2 : (Pᴴ)⁻¹ = Qᴴ := by
    apply Matrix.inv_eq_left_inv
    rw [← Matrix.conjTranspose_mul, hPQ, Matrix.conjTranspose_one]
  rw [hG, Matrix.mul_inv_rev, Matrix.mul_inv_rev, h1, h2, Matrix.mul_assoc]

theorem gram_reS_inv (S : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) :
    (reS S b).gram⁻¹ = frPinv S b * S.gram⁻¹ * (frPinv S b)ᴴ :=
  inv_eq_of_gram_conjTranspose_change (n := S.rank) S.gram (reS S b).gram (frP S b) (frPinv S b) (gram_reS S b)
    (frPinv_mul_frP S b) (frameMatrix_mul_frameMatrixInv S b)

end GlobalTheory.AdSpan.ReVec.FrMap

theorem GlobalTheory.AdSpan.ReVec.FrMap.cA_incA_star {D : D7} (e : D.host.E) : cA D (incA D e) = incA D (star e) := rfl

namespace GlobalTheory.AdSpan.ReVec.FrMap

variable {D : D7}

theorem map_eToEAf_eq (n m : ℕ) (M : Matrix (Fin n) (Fin m) D.host.E) :
    M.map (eToEAf D) = (M.map (incA D)).map (toEAf D) := by
  funext i j; rfl

theorem complex_units_mul_eq_one_of_mul_eq_one {R : Type} [Ring R] {n m : ℕ} (B Pf : Matrix (Fin n) (Fin n) R) (M' M : Matrix (Fin n) (Fin m) R)
    (C : Matrix (Fin m) (Fin m) R) (h : Pf * M' = M) : B * Pf * M' * C = B * M * C := by
  rw [Matrix.mul_assoc B, h]

theorem frP_mul_adj_finPart (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V)
    (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (Gi : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
    (hGi : Gi = frPinv S b * S.gram⁻¹ * (frPinv S b)ᴴ) :
    HMul.hMul ((frP S b).map (eToEAf D))
      ((HMul.hMul (HMul.hMul (Gi.map (incA D))
        (x.map (cA D)).transpose) (T.gram.map (incA D))).map (toEAf D)) =
    (HMul.hMul (HMul.hMul ((S.gram⁻¹).map (incA D))
        ((HMul.hMul (α := Matrix (Fin T.rank) (Fin S.rank) (AE D)) x ((frPinv S b).map (incA D))).map (cA D)).transpose)
        (T.gram.map (incA D))).map (toEAf D) := by
  rw [map_eToEAf_eq, ← Matrix.map_mul]
  congr 1
  have e1 := Matrix.map_mul (L := x) (M := (frPinv S b).map (incA D)) (f := cA D)
  have e2 : (frPinv S b * S.gram⁻¹ * (frPinv S b)ᴴ).map (incA D) =
      (frPinv S b).map (incA D) * (S.gram⁻¹).map (incA D) * ((frPinv S b)ᴴ).map (incA D) := by
    rw [Matrix.map_mul, Matrix.map_mul]
  have e4 : (((frPinv S b).map (incA D)).map (cA D))ᵀ = ((frPinv S b)ᴴ).map (incA D) := by
    funext i j
    exact cA_incA_star _
  have h5 : (frP S b).map (incA D) * (frPinv S b).map (incA D) = 1 := by
    rw [← Matrix.map_mul, frameMatrix_mul_frameMatrixInv]; exact Matrix.map_one _ (map_zero _) (map_one _)
  rw [e1, hGi, e2, Matrix.transpose_mul, e4]
  simp only [← Matrix.mul_assoc]
  simp only [h5, Matrix.one_mul]

theorem frMapAdj_reS (D : D7) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V)
    (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (x : WO (reS S b) T) :
    frMapAdj (reS S b) T (frPinvGL S b * βS) βT x = frMapAdj S T βS βT (reW S T b x) := by
  have h1 : ((frPinvGL S b * βS)⁻¹ : GL (Fin S.rank) (Lev.EAf D)).val =
      (βS⁻¹ : GL (Fin S.rank) (Lev.EAf D)).val * (frP S b).map (eToEAf D) := by
    rw [_root_.mul_inv_rev, Units.val_mul, frPinvGL_inv_val]
  unfold frMapAdj reW
  erw [h1]
  exact complex_units_mul_eq_one_of_mul_eq_one _ _ _ _ _ (frP_mul_adj_finPart S T b x _ (gram_reS_inv S b))

end GlobalTheory.AdSpan.ReVec.FrMap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodFormsDefiniteExist
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftRows

theorem goodForms_definite_exist : GlobalTheory.IndefiniteRowSideFullHecke.DegreeClassification.GoodVectorsDefinite → ∀ eps : ℝ, 0 < eps → ∃ x₀ : ℝ, ∀ (D : D7) (L : SizeData₂ D) (_ : ParameterChoice' D L), L.sc.eps = eps → x₀ ≤ L.sc.x → Formalism.MainNotions.SizesAt L → ∀ {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → ∀ b, ∃ i, R.Wat i (sg0 D A) (R.levL F b (sg0 D A)) ≠ ⊥ := by
  intro hGV eps heps
  obtain ⟨x₀, hx₀⟩ := hGV.2 eps heps
  refine ⟨x₀, ?_⟩
  intro D L hP heps' hxL hSz G _ _ Pl0 T A Ks _ _ _ R F hGiv b

  have hTie : GlobalTheory.GLq.ESerTie D := by
    intro k
    obtain ⟨LD, hT, hE, _⟩ := hGiv.types k
    exact ⟨LD, hT, hE⟩

  obtain ⟨kap, lam, hScal⟩ := Formalism.IndefR.Links.scal_exists (F := F) R
  have hSet : GlobalTheory.IndefiniteRowSideFullHecke.DegreeClassification.HidaSetting (R.upd6 kap lam) F :=
    { lev := hGiv.core.lev
      grp := { hGiv.core.grp with }
      fam := { hGiv.core.fam with }
      models := { hGiv.core.models with }
      chain := Formalism.IndefR.Links.RealDat.chain_of_scalar_update hGiv.core.chain kap lam
      thP := Formalism.IndefR.Links.RealDat.theta_props_of_scalar_update hGiv.core.thP kap lam
      scal := hScal }

  obtain ⟨i, hi⟩ := GlobalTheory.IndefiniteRowSideFullHecke.DegreeClassification.exists_last D
  have hShare := hx₀ D L hP heps' hxL hSz hTie G Pl0 T A Ks (R.upd6 kap lam) F hSet i hi b
  exact ⟨i, GlobalTheory.IndefiniteRowSideFullHecke.DegreeClassification.GoodShare.ne_bot (R.upd6 kap lam) F hShare⟩

end GlobalTheory.LiftRows

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsDefiniteSelfDualOfBaseFramePosDefStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDefiniteSelfDual_of_baseFrame_posDef : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), V.SigOK → V.IsPosDef → IsBaseFrame V β Λ N → IsDefUnimod D.sp.cm V.gram Λ := by
  first | exact @GlobalTheory.BaseFrameUnimod.isDefUnimod_of_isBaseFrame | exact GlobalTheory.BaseFrameUnimod.isDefUnimod_of_isBaseFrame | (intros; apply GlobalTheory.BaseFrameUnimod.isDefUnimod_of_isBaseFrame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsOfFinOrderOfConjMemSelfDualLatticeStabilizerStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOfFinOrder_of_conj_mem_selfDualLatticeStabilizer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E)) (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)), IsDefUnimod hc J Λ → IsFrame β Λ → ∀ (u : UR hc J) (x : UA hc J), conjIn hc J (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) u ∈ St β → IsOfFinOrder u := by
  first | exact @GlobalTheory.DefFree.isOfFinOrder_of_conjIn_mem_St | exact GlobalTheory.DefFree.isOfFinOrder_of_conjIn_mem_St | (intros; apply GlobalTheory.DefFree.isOfFinOrder_of_conjIn_mem_St <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JordanHolderMultiplicityJacquetEqBorelJacquetOfSStatement
section
open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jordanHolderMultiplicity_jacquet_eq_borelJacquet_of_small : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (β n : Type) [Fintype β] [LinearOrder β] [Fintype n] [DecidableEq n] [LinearOrder n] (c : β → Type) [∀ j, Fintype (c j)] [∀ j, DecidableEq (c j)] (f : (Σ j, c j) ≃ n), StrictMono (blk f) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL n k) V) (χ : β → kˣ →* ℂˣ), jhMult (ofChar (leviChar c χ)) (jac f π) = jhMult (ofChar (torusChar fun i => χ (blk f i))) (jacB π) := by
  first | exact @GlobalTheory.SmGL.EmptyBlocks.jhMult_jac_eq_jacB | exact GlobalTheory.SmGL.EmptyBlocks.jhMult_jac_eq_jacB | (intros; apply GlobalTheory.SmGL.EmptyBlocks.jhMult_jac_eq_jacB <;> assumption)
end

