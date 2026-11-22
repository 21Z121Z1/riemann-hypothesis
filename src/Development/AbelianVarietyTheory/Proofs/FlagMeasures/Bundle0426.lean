import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasSignatureComplement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointLatticeIntersectionSelfDualProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0159
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0421
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0135
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0131
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0155
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0422
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.StepLocGenPinnedGP
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0081
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0291
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SplitRowLatticeMiddleIffGluedLattice
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.DataInst
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0239
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0256
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0089
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0293
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0396
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0234
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NumberFieldLatticeDeterminedByLocalLattices
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0415
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0418
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0386
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0323
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0267
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerDilationWeightsDualIsotropicVector
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0250
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0249
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0290
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0423
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0416

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdaptedBasisSaturatedIsotropicFlag
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

namespace GlobalTheory.AdaptedExists

theorem exists_complement (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (p q : ℕ) (he : ∀ y, e (star y) = star (e y))
    {κ : Type} [Fintype κ] [DecidableEq κ] (hI : HasSig I p q)
    (hI₀ : HasSig I₀ (p - Fintype.card κ) (q - Fintype.card κ)) (hn : I.n = I₀.n + 2 * Fintype.card κ)
    (Λ : Submodule (𝓞 I.E) (Fin I.n → I.E)) (hΛ : Submodule.IsLattice I.E Λ)
    (hdual : ∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, star y ⬝ᵥ (I.J *ᵥ x) ∈ (algebraMap (𝓞 I.E) I.E).range)
    (T T' : Matrix (Fin I.n) κ I.E) (B : Matrix (Fin I.n) (Fin I₀.n) I.E)
    (h1 : Tᴴ * I.J * T = 0) (h2 : T'ᴴ * I.J * T' = 0) (h3 : Tᴴ * I.J * T' = 1) (h4 : Tᴴ * I.J * B = 0)
    (h5 : T'ᴴ * I.J * B = 0) (h6 : (Bᴴ * I.J * B).det ≠ 0)
    (h7 : ∀ z ∈ Λ, ∃ y, B *ᵥ y ∈ Λ ∧ (Bᴴ * I.J) *ᵥ (z - B *ᵥ y) = 0) :
    ∃ (γ : GL (Fin I₀.n) I.E) (x₀ : I₀.Gf), (B * γ.1)ᴴ * I.J * (B * γ.1) = I₀.J.map e ∧
      ∀ y, y ∈ lamX I₀ (1, x₀) ↔ ((B * γ.1) *ᵥ fun l => e (y l)) ∈ Λ := by
  have he' : ∀ y, e.symm (star y) = star (e.symm y) := fun y => e.injective (by simp [he])
  set G : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E := (Bᴴ * I.J * B).map e.symm with hG
  have hGe : Bᴴ * I.J * B = G.map e := by ext r s; exact (e.apply_symm_apply _).symm
  have hGd : G.det ≠ 0 := fun h => h6 (by
    rw [hGe]; exact ((e : I₀.E →+* I.E).map_det G).symm.trans (by rw [h, map_zero]))
  have hGh : Gᴴ = G := by
    rw [hG, ← Matrix.conjTranspose_map _ he', ← gram_swap (J_herm I)]
  obtain ⟨L, hL, -, hLd⟩ := exists_factor_lattice I.E I₀.E e he _ _ I.J B G Λ (J_herm I) hGe hGd hΛ hdual h7
  obtain ⟨γ, hγ⟩ := GlobalTheory.FlagMeas.sameKindIsometric I₀.E I₀.cm.cmUnram I₀.n G I₀.J hGh (J_herm I₀) hGd I₀.J_det ⟨L, hL, hLd⟩
    ⟨I₀.L, ⟨I₀.L_fg, I₀.L_span⟩, by simpa only [hform_eq] using I₀.L_dual⟩ (fun φ => by
      refine ⟨_, _, ?_, hasSignature_map I₀ _ _ hI₀ φ⟩
      set ψ : I.E →+* ℂ := φ.comp e.symm.toRingHom
      have hψ : ∀ x, ψ (star x) = star (ψ x) := I.cm.cmUnram.2.1 ψ
      have hm : G.map φ = (B.map ψ)ᴴ * I.J.map ψ * B.map ψ := by rw [map_gram ψ hψ]; rfl
      rw [hm]
      refine hasSignature_complement _ _ p q κ _ (T.map ψ) (T'.map ψ) _ ?_ (hasSignature_map I p q hI ψ) hn ?_ ?_ ?_ ?_ ?_ ?_
      · rw [← Matrix.conjTranspose_map _ hψ, J_herm]
      · rw [map_gram ψ hψ, h1, Matrix.map_zero _ (map_zero ψ)]
      · rw [map_gram ψ hψ, h2, Matrix.map_zero _ (map_zero ψ)]
      · rw [map_gram ψ hψ, h3, Matrix.map_one _ (map_zero ψ) (map_one ψ)]
      · rw [map_gram ψ hψ, h4, Matrix.map_zero _ (map_zero ψ)]
      · rw [map_gram ψ hψ, h5, Matrix.map_zero _ (map_zero ψ)]
      · rw [← hm]
        exact fun h => hGd (φ.injective ((φ.map_det G).trans (h.trans (map_zero φ).symm))))
  set γ' : GL (Fin I₀.n) I.E := Matrix.GeneralLinearGroup.map (e : I₀.E →+* I.E) γ
  have hγ' : γ'.1 = γ.1.map (e : I₀.E →+* I.E) := rfl
  have hT : (B * γ'.1)ᴴ * I.J * (B * γ'.1) = I₀.J.map e := by
    have := map_gram (e : I₀.E →+* I.E) he G γ.1 γ.1
    rw [hγ, ← hγ'] at this
    refine Eq.trans ?_ this
    rw [show G.map (e : I₀.E →+* I.E) = _ from hGe.symm]
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  obtain ⟨L', hL', hm, hLd'⟩ := exists_factor_lattice I.E I₀.E e he _ _ I.J (B * γ'.1) I₀.J Λ (J_herm I) hT I₀.J_det hΛ hdual
    fun z hz => by
      obtain ⟨y, hy, hy'⟩ := h7 z hz
      have : (B * γ'.1) *ᵥ (γ'⁻¹.1 *ᵥ y) = B *ᵥ y := by
        rw [mulVec_mulVec, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
      refine ⟨γ'⁻¹.1 *ᵥ y, by rwa [this], ?_⟩
      rw [this, conjTranspose_mul, Matrix.mul_assoc, ← mulVec_mulVec, hy', mulVec_zero]
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.SelfDualPoint.exists_lamX_eq I₀ L' hL' (by simpa only [hform_eq] using hLd')
  exact ⟨γ', x₀, hT, by rwa [hx₀]⟩

theorem exists_isAdapted : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (p q a : ℕ) (j : Fin a → ℕ), (∀ y, e (star y) = star (e y)) → HasSig I p q → ∑ i, j i ≤ p → ∑ i, j i ≤ q → HasSig I₀ (p - ∑ i, j i) (q - ∑ i, j i) → ∀ (xf : I.Gf) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)), IsSatFlag I (lamX I (1, xf)) j S → ∃ Λ x₀ T T' T₀, IsAdapted I I₀ e xf j S Λ x₀ T T' T₀ := by
  intro I I₀ e p q a j he hI hp hq hI₀ xf S ⟨h0, hmono, hrk, hsat, hiso⟩
  obtain ⟨-, hfg, hspan, hdual, -⟩ := GlobalTheory.PointLattice.lamX_selfDual I (1, xf)
  simp only [hform_eq] at hdual hiso
  have hn : I.n = I₀.n + 2 * ∑ i, j i := by
    have h1 := (GlobalTheory.FlagMeas.instance_numbers I).2.2.2.2.2 _ _ hI
    have h2 := (GlobalTheory.FlagMeas.instance_numbers I₀).2.2.2.2.2 _ _ hI₀
    omega
  have hle : ∀ k, S k ≤ lamX I (1, xf) := fun k y hy => ((hsat k y).1 hy).1
  have hSfg : (S (Fin.last a)).FG := hfg.of_le (hle _)
  obtain ⟨A, hA⟩ := GlobalTheory.saturatedFlag_splits I.E I.n a S h0 hmono hSfg fun i y hy h => (hsat i y).2 ⟨hle _ hy, h⟩
  obtain ⟨Λ, Ti, hΛ, hS⟩ := exists_blocks I.E I.n a j S A h0 hmono hSfg hrk hA
  set κ := Σ i, Fin (j i)
  have hκ : Fintype.card κ = ∑ i, j i := by simp [κ]
  have hsum : ∀ (M : Matrix (Fin I.n) κ I.E) (u : κ → I.E),
      M *ᵥ u = ∑ i, M.submatrix id (Sigma.mk i) *ᵥ fun s => u ⟨i, s⟩ := fun M u => by
    ext r
    simp [mulVec, dotProduct, Finset.sum_apply, κ, Fintype.sum_sigma]
  obtain ⟨T, hT⟩ : ∃ T : Matrix (Fin I.n) κ I.E, ∀ i, Ti i = T.submatrix id (Sigma.mk i) :=
    ⟨fun r s => Ti s.1 r s.2, fun _ => rfl⟩
  have hlast : ∀ z, z ∈ S (Fin.last a) ↔ ∃ u : κ → I.E, (∀ i, (fun s => u ⟨i, s⟩) ∈ Λ i) ∧ z = T *ᵥ u := fun z => by
    rw [hS]
    refine ⟨fun ⟨u, hu, _, hz⟩ => ⟨fun s => u s.1 s.2, hu, by rw [hsum, hz]; simp only [hT]⟩,
      fun ⟨u, hu, hz⟩ => ⟨_, hu, fun i hi => absurd (Fin.castSucc_lt_last i) hi, by rw [hz, hsum]; simp only [hT]⟩⟩
  have hone : ∀ i, ∀ t ∈ Λ i, Ti i *ᵥ t ∈ S (Fin.last a) := fun i t ht => by
    refine (hS _ _).2 ⟨Pi.single i t, fun k => ?_, fun i hi => absurd (Fin.castSucc_lt_last i) hi, ?_⟩
    · by_cases h : k = i
      · subst h; simpa using ht
      · simp [h]
    · rw [Finset.sum_eq_single i] <;> simp +contextual
  set W := Submodule.span I.E (S (Fin.last a) : Set (Fin I.n → I.E)) with hW
  have hrange : LinearMap.range T.mulVecLin = W := by
    refine le_antisymm ?_ (Submodule.span_le.2 fun z hz => ?_)
    · rintro _ ⟨u, rfl⟩
      rw [mulVecLin_apply, hsum]
      refine Submodule.sum_mem _ fun i _ => ?_
      have : Submodule.span I.E (Λ i : Set (Fin (j i) → I.E)) ≤ W.comap (Ti i).mulVecLin :=
        Submodule.span_le.2 fun t ht => Submodule.subset_span (hone i t ht)
      rw [← hT]
      exact this ((hΛ i).span_eq_top ▸ Submodule.mem_top)
    · obtain ⟨u, -, rfl⟩ := (hlast z).1 hz
      exact ⟨u, rfl⟩
  have hdim : Module.finrank I.E W = Fintype.card κ := by
    have := telescope a j (fun k => Formalism.HN.rkK (S k)) hrk
    simp only [h0] at this
    rw [hκ]
    rw [show Formalism.HN.rkK (⊥ : Submodule (𝓞 I.E) (Fin I.n → I.E)) = 0 by
      rw [Formalism.HN.rkK, Submodule.bot_coe, Submodule.span_zero_singleton, finrank_bot], zero_add] at this
    exact this
  have hWiso : ∀ x ∈ W, ∀ y ∈ W, star x ⬝ᵥ (I.J *ᵥ y) = 0 := fun x hx y hy => by
    induction hx, hy using Submodule.span_induction₂ with
    | mem_mem x y hx hy => exact hiso x hx y hy
    | zero_left => simp
    | zero_right => simp
    | add_left x y z _ _ _ h h' => simp [h, h']
    | add_right x y z _ _ _ h h' => simp [mulVec_add, h, h']
    | smul_left c x y _ _ h => simp [h]
    | smul_right c x y _ _ h => simp [mulVec_smul, h]
  obtain ⟨W', hW'iso, hW'dim, hW'nd, hsplit⟩ := GlobalTheory.WittInt.main I.E I.cm.cmUnram I.n I.J (J_herm I) I.J_det _
    ⟨hfg, hspan⟩ hdual W hWiso
  obtain ⟨T', B, hrange', h3, h6, hB⟩ := exists_witt I.E I.n I₀.n κ I.J T W W' (J_herm I) I.J_det (hκ ▸ hn) hrange hdim
    (hW'dim.trans hdim) hWiso hW'iso hW'nd
  have mT : ∀ u, T *ᵥ u ∈ W := fun u => hrange ▸ ⟨u, rfl⟩
  have mT' : ∀ u, T' *ᵥ u ∈ W' := fun u => hrange' ▸ ⟨u, rfl⟩
  have h1 : Tᴴ * I.J * T = 0 := gram_eq_zero _ _ _ fun x y => hWiso _ (mT x) _ (mT y)
  have h2 : T'ᴴ * I.J * T' = 0 := gram_eq_zero _ _ _ fun x y => hW'iso _ (mT' x) _ (mT' y)
  have h4 : Tᴴ * I.J * B = 0 := gram_eq_zero _ _ _ fun x y =>
    (hB _).1 ⟨y, rfl⟩ _ (Submodule.mem_sup_left (mT x))
  have h5 : T'ᴴ * I.J * B = 0 := gram_eq_zero _ _ _ fun x y =>
    (hB _).1 ⟨y, rfl⟩ _ (Submodule.mem_sup_right (mT' x))
  have hdec : ∀ z ∈ lamX I (1, xf), ∃ u u' y, T *ᵥ u ∈ S (Fin.last a) ∧ T' *ᵥ u' ∈ lamX I (1, xf) ∧
      B *ᵥ y ∈ lamX I (1, xf) ∧ z = T *ᵥ u + T' *ᵥ u' + B *ᵥ y := fun z hz => by
    obtain ⟨x, hx, y, hy, hxW, hyW, h⟩ := hsplit z hz
    obtain ⟨w, hw⟩ := (hB _).2 h
    have hxS := (hsat _ x).2 ⟨hx, hxW⟩
    rw [← hrange] at hxW
    rw [← hrange'] at hyW
    obtain ⟨u, rfl⟩ := hxW
    obtain ⟨u', rfl⟩ := hyW
    simp only [mulVecLin_apply] at hw hx hy hxS
    exact ⟨u, u', w, hxS, hy, hw ▸ sub_mem (sub_mem hz hx) hy, by rw [hw]; abel⟩
  obtain ⟨γ, x₀, hG, hx₀⟩ := exists_complement I I₀ e p q he hI (hκ ▸ hI₀) (hκ ▸ hn) _ ⟨hfg, hspan⟩ hdual T T' B
    h1 h2 h3 h4 h5 h6 fun z hz => by
      obtain ⟨u, u', y, -, -, hy, rfl⟩ := hdec z hz
      refine ⟨y, hy, ?_⟩
      rw [add_sub_cancel_right, mulVec_add, mulVec_mulVec, mulVec_mulVec, gram_swap (J_herm I) T,
        gram_swap (J_herm I) T', h4, h5]
      simp
  have hsub : ∀ {l : Type} (M : Matrix (Fin I.n) κ I.E) (N : Matrix (Fin I.n) l I.E) {k₁ k₂ : Type}
      (f : k₁ → κ) (g : k₂ → l),
      (M.submatrix id f)ᴴ * I.J * N.submatrix id g = (Mᴴ * I.J * N).submatrix f g := fun M N _ _ f g => by
    ext r s
    simp [Matrix.mul_apply]
  have hpair : ∀ i t u', star (Ti i *ᵥ t) ⬝ᵥ (I.J *ᵥ (T' *ᵥ u')) = star t ⬝ᵥ fun s => u' ⟨i, s⟩ := fun i t u' => by
    rw [form_mulVec, hT, ← Matrix.submatrix_id_id T', hsub, h3]
    congr 1
    ext s
    simp [mulVec, dotProduct, Matrix.one_apply]
  refine ⟨Λ, x₀, Ti, fun i => T'.submatrix id fun s => ⟨i, s⟩, B * γ.1, he, hn, hΛ, fun i k => ⟨?_, ?_, fun h => ?_⟩,
    fun i => ⟨?_, ?_, ?_⟩, hG, fun z => ⟨fun hz => ?_, ?_⟩, hS⟩
  · rw [hT, hT, hsub, h1]; rfl
  · rw [hsub, h2]; rfl
  · rw [hT, hsub, h3]
    ext r s
    simp [h]
  · rw [hT, hsub, h3]
    ext r s
    simp [Matrix.one_apply]
  · rw [← Matrix.mul_assoc, hT, ← Matrix.submatrix_id_id B, hsub, h4]
    simp
  · rw [← Matrix.mul_assoc, ← Matrix.submatrix_id_id B, hsub, h5]
    simp
  · obtain ⟨u, u', y, hu, hu', hy, rfl⟩ := hdec z hz
    obtain ⟨v, hv, hv'⟩ := (hlast _).1 hu
    have hy' : ((B * γ.1) *ᵥ fun l => e (e.symm ((γ⁻¹.1 *ᵥ y) l))) = B *ᵥ y := by
      simp only [e.apply_symm_apply]
      rw [mulVec_mulVec, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    refine ⟨fun i s => v ⟨i, s⟩, fun i s => u' ⟨i, s⟩, fun l => e.symm ((γ⁻¹.1 *ᵥ y) l), hv, fun i t ht => ?_,
      (hx₀ _).2 (hy' ▸ hy), ?_⟩
    · rw [← hpair]
      exact (hdual _).1 hu' _ (hle _ (hone i t ht))
    · rw [hy', hv', hsum T, hsum T']
      simp only [hT]
  · rintro ⟨u, u', y, hu, hu', hy, rfl⟩
    refine add_mem (add_mem (Submodule.sum_mem _ fun i _ => hle _ (hone i _ (hu i))) ?_) ((hx₀ y).1 hy)
    have e1 := hsum T' fun s => u' s.1 s.2
    refine e1 ▸ (hdual _).2 fun w hw => ?_
    obtain ⟨v, v', y', hv, -, -, rfl⟩ := hdec w hw
    obtain ⟨t, ht, ht'⟩ := (hlast _).1 hv
    rw [star_add, star_add, add_dotProduct, add_dotProduct, form_mulVec _ T', form_mulVec _ B, h2,
      gram_swap (J_herm I) T', h5, ht', hsum T, star_sum, sum_dotProduct]
    simp only [← hT, hpair, conjTranspose_zero, zero_mulVec, dotProduct_zero, add_zero]
    exact Subring.sum_mem _ fun i _ => hu' i _ (ht i)

end GlobalTheory.AdaptedExists
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenericHeightBoundOfLocalEstimatesStatement
section
open Formalism.FourierDecayAlt Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna GlobalTheory.SnPos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_height_bound_of_local_estimates : StepSizes → StepClassG → StepNormalsG → StepPointsG → StepHeightG → StepAnalyticGP → GenCutP := by
  first | exact @GlobalTheory.SnPos.genCutP_of_steps | exact GlobalTheory.SnPos.genCutP_of_steps | (intros; apply GlobalTheory.SnPos.genCutP_of_steps <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlueIsLatticeUnimodular
section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowsOrb.Glue

open GlobalTheory.LoopC.RowGlue

theorem glue_isLattice_unimodular : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D), GlobalTheory.TypeAsm.Std D large₂ → ∀ L : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Wb X), Submodule.IsLattice D.host.E L → Formalism.HermitianLatticesTheory.IsUnimodular (GlobalTheory.RowsOrb.hb X) L → Submodule.IsLattice D.host.E (latSpanS (fun a => aaD D a) X.eX ⊔ L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)) ⊔ latSpanS (fun a => (aaD D a)⁻¹) X.fY) ∧ Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT (latSpanS (fun a => aaD D a) X.eX ⊔ L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)) ⊔ latSpanS (fun a => (aaD D a)⁻¹) X.fY) := by
  intro D large₂ X _ L hL hU
  have H : IsHypFrame (VS D).hT X.eX X.fY := ⟨(VS D).herm, X.ee, X.ff, X.ef⟩
  have h0 : ∀ a, aaD D a ≠ 0 := fun a => zpow_ne_zero _ (ddS_ne_zero D)
  have hs : ∀ a, StarStable (aaD D a) := fun a => (ddS_stable D).zpow (ddS_ne_zero D) _
  have hmid : ∀ w ∈ L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)),
      Mid (VS D).hT X.eX X.fY w := by
    rintro _ ⟨w, -, rfl⟩
    exact w.2
  refine ⟨H.isLattice (A := fun a => aaD D a) (B := fun a => (aaD D a)⁻¹) h0 (fun a => inv_ne_zero (h0 a))
    (hL.fg.map _) ?_, (H.unimodular_iff (A := fun a => aaD D a) (B := fun a => (aaD D a)⁻¹) hmid
      (fun a => inv_ne_zero (h0 a)) (fun a => (hs a).inv (h0 a)) (fun a => (inv_inv _).symm)).2 ?_⟩
  · intro w hw
    have h1 : (⟨w, hw⟩ : GlobalTheory.RowsOrb.Wb X) ∈ Submodule.span D.host.E (L : Set (GlobalTheory.RowsOrb.Wb X)) := by
      rw [hL.span_eq_top]; trivial
    have h2 := Submodule.mem_map_of_mem (f := (GlobalTheory.RowsOrb.Wb X).subtype) h1
    rw [Submodule.map_span] at h2
    exact h2
  · intro w hw
    have key : (⟨w, hw⟩ : GlobalTheory.RowsOrb.Wb X) ∈ Formalism.HermitianLatticesTheory.dual (GlobalTheory.RowsOrb.hb X) L ↔
        (⟨w, hw⟩ : GlobalTheory.RowsOrb.Wb X) ∈ L := by
      rw [show Formalism.HermitianLatticesTheory.dual (GlobalTheory.RowsOrb.hb X) L = L from hU]
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap] at key ⊢
    constructor
    · intro h
      exact ⟨⟨w, hw⟩, key.1 fun y hy => h y ⟨y, hy, rfl⟩, rfl⟩
    · rintro ⟨w', hw', e⟩ _ ⟨y, hy, rfl⟩
      have e' : (⟨w, hw⟩ : GlobalTheory.RowsOrb.Wb X) = w' := Subtype.ext e.symm
      exact key.2 (e' ▸ hw') y hy

end GlobalTheory.RowsOrb.Glue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GluedLatticesLocalDataUnimodular
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GlueDat

variable {D : D7}

theorem finrank_loc (p : PlF D) :
    Module.finrank (D.s.atP p).Ep (Vp D p) = D.R.k + 2 * D.R.rS + 1 := by
  rw [finrank_Vp]
  have h1 := D.R.m_even
  have h2 := D.R.two_le_m
  have h3 := D.R.m_add_three_le_k
  obtain ⟨c, hc⟩ := h1
  simp only [Ranks.r, Ranks.rS]
  omega

theorem localLattice_fg (Z : LocDat D) (Λ : LV D) (h : Submodule.IsLattice D.host.E Λ) (p : PlF D) :
    (lattice₂ D Z.M p Λ).FG := by
  have := (GlobalTheory.HL.PlacesRec.lattice_local (GlobalTheory.HL.placesOf Z) (nV D) (LatLoc.cL Λ)
    (LatLoc.isLattice_map _ _ h)).2.1 p
  rw [LatLoc.localLattice_eq]
  exact this.1

theorem orbit (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) {Tn T'n : ℕ}
    (F G : LFlag (VS D) D.R.rS (Tn : D.host.E)) (F' G' : LFlag (VS D) D.R.rS (T'n : D.host.E))
    (hB : Based Z FP Tn T'n F F') (hR : ∀ p, (FP p).RelG (LocNG.theta (Z.M p)))
    (hG : Tri D.host.E (frame F) (frame G)) (hG' : Tri D.host.E (frame F') (frame G')) (p : PlF D) :
    (∃ n ∈ (FP p).A.N, scaled Z p (frame G) = fun b => n ((FP p).A.f b)) ∧
    (∃ n ∈ (FP p).B.N, scaled Z p (frame G') = fun b => n ((FP p).B.f b)) := by
  obtain ⟨A, hA, hAc⟩ := hG
  obtain ⟨A', hA', hAc'⟩ := hG'
  obtain ⟨Ap, hAp, -⟩ := GlobalTheory.T.rational_unitriangular_frame_change_local_scalings D Z _ _ A hA hAc
  obtain ⟨Ap', hAp', -⟩ := GlobalTheory.T.rational_unitriangular_frame_change_local_scalings D Z _ _ A' hA' hAc'
  have hN := (hR p).2.2.2.2.2.2
  have hfA : (FP p).A.f = scaled Z p (frame F) := (hB p).1
  have hfB : (FP p).B.f = scaled Z p (frame F') := (hB p).2.1
  refine ⟨?_, ?_⟩
  · exact (GlobalTheory.T.frameDual_unipotentGroup_acts_unitriangular_onto (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS (FP p).A hN.2.1).2.2 (scaled Z p (frame G))
      (by rw [hfA]; exact ⟨Ap p, (hAp p).1, (hAp p).2⟩)
  · exact (GlobalTheory.T.frameDual_unipotentGroup_acts_unitriangular_onto (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS (FP p).B hN.2.2.2.1).2.2 (scaled Z p (frame G'))
      (by rw [hfB]; exact ⟨Ap' p, (hAp' p).1, (hAp' p).2⟩)

theorem mem_iff_of_img {α : Type*} {S S' : Set α} {f : α → α} (hf : Function.Injective f) (hS : f '' S = S')
    {a b : α} (hb : b = f a) : a ∈ S ↔ b ∈ S' := by
  subst hb; rw [← hS]; exact (hf.mem_set_image).symm

end GlobalTheory.GlueDat

open GlobalTheory.GlueDat in

theorem GlobalTheory.GlueDat.glued_data : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (u u' : D.what₂.Word) (F G : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' G' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (P : Finset (PlF D)) (d0 : Dat Z FP), 4 * D.R.rS + 7 ≤ D.R.k → BaseOK (Tu D u) (Tu D u') F F' P d0 → StdOff Z P F G F' G' → ∀ Λ : LV D, (Λ ∈ Formalism.L2.SG.Pf.Cnt.GlueSet (VS D).hT (Formalism.L2.SG.Pf.Cnt.UPair D G.fl G') (Formalism.L2.SG.Pf.Cnt.MMof D G.fl G') ↔ ∃ y : Dat Z FP, Λ ∈ globSet G G' y) ∧ (∀ y y' : Dat Z FP, Λ ∈ globSet G G' y → Λ ∈ globSet G G' y' → y = y') ∧ (∀ y : Dat Z FP, Λ ∈ globSet G G' y → (∀ p, p ∉ P → LocNG.Datum.Rel (d0 p) (y p)) ∧ {p | y p ≠ d0 p}.Finite) ∧ ∀ (y y' : Dat Z FP), ∀ h ∈ H0 F F', RMoves h y y' → (Λ ∈ globSet G G' y ↔ Formalism.HermitianLatticesTheory.gmap h Λ ∈ globSet G G' y') := by
  intro D Z FP u u' F G F' G' P d0 hk hB hS Λ
  have hOK : ∀ p, (Z.M p).OK := fun p => (Z.agree p).1
  have hR := hB.2.1
  have hO := fun p => orbit Z FP F G F' G' hB.1 hR hS.1 hS.2.1 p
  have hLM := fun p (L : Submodule (Z.M p).L.O (Vp D p)) =>
    GlobalTheory.T.generic_local_terms_selfDual_lattices (Z.M p) (hOK p) (locH Z p) D.R.rS D.R.k (FP p) (finrank_loc p) (hR p)
      (scaled Z p (frame G)) (scaled Z p (frame G')) (hO p).1 (hO p).2 L
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [GlobalTheory.T.glued_unimodular_lattice_iff_local_completions D Z FP u u' G G' (GlobalTheory.T.linearIndependent_changedRationalFrames_of_unitriangular D Z FP _ _ F G F' G' hB.1 hR hS.1 hS.2.1) Λ]
    constructor
    · rintro ⟨hL, hp⟩
      have : ∀ p, ∃ d, lattice₂ D Z.M p Λ ∈ locSet G G' p d := fun p =>
        (hLM p _).1.1 ⟨(hp p).1, localLattice_fg Z Λ hL p, (hp p).2.1, (hp p).2.2⟩
      choose y hy using this
      exact ⟨y, hL, hy⟩
    · rintro ⟨y, hL, hy⟩
      refine ⟨hL, fun p => ?_⟩
      obtain ⟨h1, -, h3, h4⟩ := (hLM p _).1.2 ⟨y p, hy p⟩
      exact ⟨h1, h3, h4⟩
  · intro y y' h h'
    funext p
    exact (hLM p _).2 (y p) (y' p) (h.2 p).1 (h'.2 p).1
  · intro y hy
    refine ⟨fun p hp => ?_, ?_⟩
    · obtain ⟨A, A', hA, hA', hint, hc, hc'⟩ := hS.2.2.2.2 p hp
      have := GlobalTheory.T.hermitian_orbit_unique_lattice_integral_frames (Z.M p) (hOK p) (locH Z p) D.R.rS D.R.k (FP p) hk (finrank_loc p) (hR p)
        (hB.2.2.1 p hp) A A' (fun a b hab => ⟨hA.1 a b hab, hA'.1 a b hab⟩) (fun a => ⟨hA.2 a, hA'.2 a⟩) hint
        (scaled Z p (frame G)) (scaled Z p (frame G'))
        (fun j => by rw [(hB.1 p).1]; exact hc j) (fun j => by rw [(hB.1 p).2.1]; exact hc' j)
        (d0 p) (hB.2.2.2.1 p) (y p)
      exact this.2 ⟨_, (hy.2 p).1⟩
    · obtain ⟨Λ₀, hΛ₀, hΛ₀p⟩ := hB.2.2.2.2
      refine (((LatLoc.lattices_local_global D Z).1 Λ Λ₀ hy.1 hΛ₀).1.union P.finite_toSet).subset ?_
      intro p hp
      by_contra hc
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not, Finset.mem_coe] at hc
      apply hp
      exact (GlobalTheory.T.hermitianDatum_of_term_read_on_lattice (Z.M p) (hOK p) (locH Z p) D.R.rS D.R.k (FP p) (finrank_loc p) (hR p)).2
        (y p) (d0 p) _ _ (hy.2 p).1 (hΛ₀p p hc.2) (by dsimp only [tm]; rw [hc.1]) (by dsimp only [tm]; rw [hc.1])
        (fun g _ => by dsimp only [tm]; rw [hc.1])
  · intro y y' h hh hmv
    have hloc : ∀ p, ∃ g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p, g ∈ (FP p).UW0 ∧
        LocNG.Datum.Moves g (y p) (y' p) ∧
        lattice₂ D Z.M p (Formalism.HermitianLatticesTheory.gmap h Λ) = LocNG.img g (lattice₂ D Z.M p Λ) := by
      intro p
      obtain ⟨g, hext, hU, huniq, himg, -⟩ := GlobalTheory.T.rational_isometry_extends_local_isometry D Z p h hh.1
      obtain ⟨g', hext', hm⟩ := hmv p
      obtain rfl : g' = g := huniq g' hext'
      refine ⟨g', Subgroup.subset_closure ⟨hU, fun b => ⟨?_, ?_⟩⟩, hm, (himg Λ).symm⟩
      · rw [(hB.1 p).1]
        show g' (frFac Z.δ p b • baseChange₂ D p (frame F b)) = _
        rw [map_smul, hext', hh.2.1 b]
      · rw [(hB.1 p).2.1]
        show g' (frFac Z.δ p b • baseChange₂ D p (frame F' b)) = _
        rw [map_smul, hext', hh.2.2 b]
    choose g hgU hgm hgimg using hloc
    have hset := fun p => (GlobalTheory.T.unitaryComplement_moves_hermitianTerms (Z.M p) (hOK p) (locH Z p) D.R.rS D.R.k (FP p) (finrank_loc p) (hR p)
      (scaled Z p (frame G)) (scaled Z p (frame G')) (hO p).1 (hO p).2 (g p) (hgU p) (y p) (y' p) (hgm p)).2
    have hlat : Submodule.IsLattice D.host.E (Formalism.HermitianLatticesTheory.gmap h Λ) ↔ Submodule.IsLattice D.host.E Λ := by
      constructor
      · intro hl
        have e : Λ = Formalism.HermitianLatticesTheory.gmap h.symm (Formalism.HermitianLatticesTheory.gmap h Λ) := by
          ext x; simp [Formalism.HermitianLatticesTheory.gmap]
        rw [e]; exact LatLoc.isLattice_map _ _ hl
      · exact LatLoc.isLattice_map _ _
    show (Submodule.IsLattice D.host.E Λ ∧ ∀ p, lattice₂ D Z.M p Λ ∈ locSet G G' p (y p)) ↔
      (Submodule.IsLattice D.host.E (Formalism.HermitianLatticesTheory.gmap h Λ) ∧ ∀ p, lattice₂ D Z.M p (Formalism.HermitianLatticesTheory.gmap h Λ) ∈ locSet G G' p (y' p))
    rw [hlat]
    refine and_congr_right fun _ => forall_congr' fun p => ?_
    have e := hgimg p
    have key : ∀ L, L ∈ LocNG.img (g p) '' locSet G G' p (y p) ↔ L ∈ locSet G G' p (y' p) :=
      fun L => Set.ext_iff.mp (hset p) L
    have hinj : Function.Injective (LocNG.img (M := Z.M p) (g p)) := fun L₁ L₂ e =>
      Submodule.map_injective_of_injective (f := ((g p : Vp D p →ₗ[(D.s.atP p).Ep] Vp D p).restrictScalars (Z.M p).L.O))
        (g p).injective e
    exact mem_iff_of_img hinj (Set.ext key) e
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralStabiliserCovolumeLeIndexWeight
section
noncomputable section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals

namespace GlobalTheory.TypeAsm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem covTC_holds : CovTC := by
  intro D large₂ X Y u C hStd t N hAd μ K hμ hK
  obtain ⟨hCM, hPl, hvI, hv1, -, hcard, -, -, -, hnorm, hrk, hg2, -⟩ := GlobalTheory.T.unitaryHostFieldArithmeticConditions D large₂ hStd
  have hTerm := GlobalTheory.T.rowLattice_term_adaptedNormalForm D large₂ X Y u hStd t N hAd
  obtain ⟨β, n₁, g, n₂, hF⟩ := GlobalTheory.T.adaptedNormalForm_gives_real_normal_form D large₂ X Y u C hStd t N hAd
  have hι : Nonempty D.what₂.Tau := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace D.host.E) := inferInstance
    exact ⟨(hPl.2 w).choose⟩
  obtain ⟨τ0⟩ := id hι

  have hμeq : ∀ τ, μ τ = (GlobalTheory.Amp.lebR0 D.R.k D.R.rS N.j β).map (Formalism.QuantumDeterminants.conjM (n₂ τ)⁻¹) ∧
      SigmaFinite (GlobalTheory.Amp.lebR0 D.R.k D.R.rS N.j β) := fun τ => by
    obtain ⟨h1, h2, hinv, hFr⟩ := hF τ
    obtain ⟨-, -, -, -, ⟨c, hc⟩, -⟩ := hFr
    have hm := hμ τ
    rw [hinv] at hm
    exact GlobalTheory.Amp.StabHaar.normalFormStabilizerMeasure_eq_any_normalForm _ _ _ N.j_le _ _ _ _ _ β c _ h1 h2 hc hm
  haveI : SigmaFinite (GlobalTheory.Amp.lebR0 D.R.k D.R.rS N.j β) := (hμeq τ0).2

  have hrat := GlobalTheory.TypeAsm.gam_iff_nLam D large₂ X Y u hStd t N hAd
  have hGiso : ∀ n ∈ (N.Gam t.lam : Set ((VS D).V ≃ₗ[D.host.E] (VS D).V)), n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT :=
    fun n hn => ((hrat n).1 hn).1.1.1
  have hpts : GlobalTheory.DegVol.realPts (phiV C) (N.Gam t.lam : Set ((VS D).V ≃ₗ[D.host.E] (VS D).V)) = trI C '' ROinf t := by
    rw [GlobalTheory.TypeAsm.RatIsomReal.realPts_eq_image D X C _ hGiso]
    congr 1
    ext y
    constructor
    · rintro ⟨x, n, hx, rfl, hn⟩
      obtain ⟨h1, h2⟩ := (hrat n).1 hn
      exact ⟨x, n, hx, rfl, h1, h2⟩
    · rintro ⟨x, n, hx, rfl, h1, h2⟩
      exact ⟨x, n, hx, rfl, (hrat n).2 ⟨h1, h2⟩⟩
  have hfund0 := GlobalTheory.CovFund.isFund_image D X Y u C t K hK
  rw [← hpts] at hfund0
  have hRP : GlobalTheory.DegVol.RP D.R.k D.R.rS (fun τ => (gamT C t τ)⁻¹) =
      GlobalTheory.DegVol.RP D.R.k D.R.rS (fun τ => n₁ τ * g τ * n₂ τ) := by
    congr 1; funext τ; exact (hF τ).2.2.1
  rw [hRP] at hfund0

  have hunit : ∀ τ, n₁ τ ∈ Formalism.QuantumDeterminants.Nset D.R.k D.R.rS ∧ n₂ τ ∈ Formalism.QuantumDeterminants.Nset D.R.k D.R.rS ∧ IsUnit (g τ).det :=
    fun τ => ⟨(hF τ).1, (hF τ).2.1, GlobalTheory.Amp.StabHaar.unit_of_GG (hF τ).2.2.2.2.2.2.2.1.choose_spec.1⟩
  obtain ⟨hFund, hvol⟩ := GlobalTheory.DegVol.UnipConj.isFund_conj_and_measure D.host.E (VS D).V D.R.k D.R.rS D.what₂.Tau
    (phiV C) (N.Gam t.lam : Set ((VS D).V ≃ₗ[D.host.E] (VS D).V)) n₁ g n₂ (trI C '' K)
    (GlobalTheory.Amp.lebR0 D.R.k D.R.rS N.j β) inferInstance hunit hfund0
  have hF' : ∀ τ, GlobalTheory.DegVol.IsFrameOf N D.R.k (embS D τ) (2 * Formalism.HermitianLatticesTheory.vInv D.host.E) β
      (fun y => n₂ τ *ᵥ phiV C τ y) (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u τ) (g τ) := fun τ => by
    rw [hvI]; exact (hF τ).2.2.2
  have hle := GlobalTheory.T.hermitian_stabiliser_covolume_le D.host.E (VS D).V (HV D) hCM D.R.rS N D.R.k D.what₂.Tau (embS D) β
    (fun τ y => n₂ τ *ᵥ phiV C τ y) (fun τ => zB X (C.Qi τ) u τ) (fun τ => zB X (C.Qi τ) u τ) g hPl hrk hF'
    (by rw [hAd.1, hnorm, hvI, hcard]) (by rw [hvI]; exact hv1) (gS D) t.lam _ (by omega) hTerm hFund
  have hμpi : Measure.pi μ = Measure.pi fun τ => (GlobalTheory.Amp.lebR0 D.R.k D.R.rS N.j β).map (Formalism.QuantumDeterminants.conjM (n₂ τ)⁻¹) := by
    congr 1; funext τ; exact (hμeq τ).1
  rw [hμpi, hvol]
  refine hle.trans (le_of_eq ?_)
  rw [hvI, hcard]
  rfl

end GlobalTheory.TypeAsm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsHermitianIsometryMatrixIffMemIsometriesStatement
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom GlobalTheory.CovDomGrp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHermitianIsometryMatrix_iff_mem_isometries : ∀ {D : D7} (X : HidaSetting D) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E), (∀ y, crdH X (n y) = γ *ᵥ crdH X y) → (GlobalTheory.SgAlg.IsUn (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) γ ↔ n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) := by
  first | exact @GlobalTheory.CovDomGrp.isUn_iff_mem_isom | exact GlobalTheory.CovDomGrp.isUn_iff_mem_isom | (intros; apply GlobalTheory.CovDomGrp.isUn_iff_mem_isom <;> assumption)
end

