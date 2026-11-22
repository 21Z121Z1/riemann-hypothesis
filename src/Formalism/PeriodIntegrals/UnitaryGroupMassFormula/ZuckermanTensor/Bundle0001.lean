import Mathlib
import Formalism.PeriodIntegrals.UpqRep
import Formalism.PeriodIntegrals.Bundle0015
import Formalism.PeriodIntegrals.ZuckTensor
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ZuckermanTensor.DualDefs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ZuckermanTensor.DualChoice

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ZuckermanTensor.DualTop
section
open Matrix Finset
open scoped InnerProductSpace
noncomputable section
namespace PI.ZuckTensorWork
open PI.UpqRep PI.ZuckTensor

def RevUJ : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ), g ∈ UJset (revE ε) → revM g ∈ UJset ε

def DualVec : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ), g ∈ UJset ε → ∀ x y : Fin n → ℂ,
    (starRingEnd ℂ) (star y ⬝ᵥ (revM g *ᵥ x)) =
      star (Jm ε *ᵥ (x ∘ Fin.rev)) ⬝ᵥ (g⁻¹ *ᵥ (Jm ε *ᵥ (y ∘ Fin.rev)))

def JJ : Prop := ∀ (n : ℕ) (ε : Fin n → Bool) (x : Fin n → ℂ), Jm ε *ᵥ (Jm ε *ᵥ x) = x

def RevSingle : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℝ) (s : Fin n), revP (lam + Pi.single s 1) = revP lam - Pi.single (Fin.rev s) 1

section Eq
variable {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [NormedAddCommGroup B] [InnerProductSpace ℂ B]

def cjEquivInv (U : Cj A ≃ₗᵢ[ℂ] Cj B) : A ≃ₗᵢ[ℂ] B where
  toFun x := Cj.un (U (Cj.mk x))
  invFun y := Cj.un (U.symm (Cj.mk y))
  left_inv x := by
    show Cj.un (U.symm (U (Cj.mk x))) = x
    rw [U.symm_apply_apply]; rfl
  right_inv y := by
    show Cj.un (U (U.symm (Cj.mk y))) = y
    rw [U.apply_symm_apply]; rfl
  map_add' x y := by
    show Cj.un (U (Cj.mk x + Cj.mk y)) = _
    rw [map_add]; rfl
  map_smul' c x := by
    have e : Cj.mk (c • x) = (starRingEnd ℂ) c • Cj.mk x := by
      show c • x = (starRingEnd ℂ) ((starRingEnd ℂ) c) • x
      rw [Complex.conj_conj]
    show Cj.un (U (Cj.mk (c • x))) = c • Cj.un (U (Cj.mk x))
    rw [e, map_smul, Cj.un_smul, Complex.conj_conj]
  norm_map' x := U.norm_map (Cj.mk x)

end Eq

end PI.ZuckTensorWork
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ZuckermanTensor.RevNum
section
open Matrix Finset
noncomputable section
namespace PI.ZuckTensorWork
open PI.UpqRep PI.ZuckTensor

variable {n : ℕ}

private lemma revNum_single (s x : Fin n) :
    (Pi.single (Fin.rev s) (1 : ℝ) : Fin n → ℝ) x = (Pi.single s (1 : ℝ) : Fin n → ℝ) (Fin.rev x) := by
  simp only [Pi.single_apply, Fin.rev_eq_iff]

theorem revNum_rhoC (ε : Fin n → Bool) (a : Fin n) : rhoC (revE ε) a = - rhoC ε (Fin.rev a) := by
  have h1 : #(univ.filter fun b => a < b ∧ revE ε b = revE ε a) =
      #(univ.filter fun b => b < Fin.rev a ∧ ε b = ε (Fin.rev a)) := by
    apply Finset.card_nbij' Fin.rev Fin.rev
    · intro b hb
      rw [Finset.mem_coe, Finset.mem_filter] at hb ⊢
      exact ⟨mem_univ _, Fin.rev_lt_rev.mpr hb.2.1, hb.2.2⟩
    · intro b hb
      rw [Finset.mem_coe, Finset.mem_filter] at hb ⊢
      exact ⟨mem_univ _, Fin.lt_rev_iff.mpr hb.2.1, by simp only [revE, Fin.rev_rev]; exact hb.2.2⟩
    · intro b _; exact Fin.rev_rev b
    · intro b _; exact Fin.rev_rev b
  have h2 : #(univ.filter fun b => b < a ∧ revE ε b = revE ε a) =
      #(univ.filter fun b => Fin.rev a < b ∧ ε b = ε (Fin.rev a)) := by
    apply Finset.card_nbij' Fin.rev Fin.rev
    · intro b hb
      rw [Finset.mem_coe, Finset.mem_filter] at hb ⊢
      exact ⟨mem_univ _, Fin.rev_lt_rev.mpr hb.2.1, hb.2.2⟩
    · intro b hb
      rw [Finset.mem_coe, Finset.mem_filter] at hb ⊢
      exact ⟨mem_univ _, Fin.rev_lt_iff.mpr hb.2.1, by simp only [revE, Fin.rev_rev]; exact hb.2.2⟩
    · intro b _; exact Fin.rev_rev b
    · intro b _; exact Fin.rev_rev b
  simp only [rhoC]
  rw [h1, h2]
  ring

theorem revNum_rhoN (ε : Fin n → Bool) (a : Fin n) : rhoN (revE ε) a = - rhoN ε (Fin.rev a) := by
  have h1 : #(univ.filter fun b => a < b ∧ revE ε b ≠ revE ε a) =
      #(univ.filter fun b => b < Fin.rev a ∧ ε b ≠ ε (Fin.rev a)) := by
    apply Finset.card_nbij' Fin.rev Fin.rev
    · intro b hb
      rw [Finset.mem_coe, Finset.mem_filter] at hb ⊢
      exact ⟨mem_univ _, Fin.rev_lt_rev.mpr hb.2.1, hb.2.2⟩
    · intro b hb
      rw [Finset.mem_coe, Finset.mem_filter] at hb ⊢
      exact ⟨mem_univ _, Fin.lt_rev_iff.mpr hb.2.1, by simp only [revE, Fin.rev_rev]; exact hb.2.2⟩
    · intro b _; exact Fin.rev_rev b
    · intro b _; exact Fin.rev_rev b
  have h2 : #(univ.filter fun b => b < a ∧ revE ε b ≠ revE ε a) =
      #(univ.filter fun b => Fin.rev a < b ∧ ε b ≠ ε (Fin.rev a)) := by
    apply Finset.card_nbij' Fin.rev Fin.rev
    · intro b hb
      rw [Finset.mem_coe, Finset.mem_filter] at hb ⊢
      exact ⟨mem_univ _, Fin.rev_lt_rev.mpr hb.2.1, hb.2.2⟩
    · intro b hb
      rw [Finset.mem_coe, Finset.mem_filter] at hb ⊢
      exact ⟨mem_univ _, Fin.rev_lt_iff.mpr hb.2.1, by simp only [revE, Fin.rev_rev]; exact hb.2.2⟩
    · intro b _; exact Fin.rev_rev b
    · intro b _; exact Fin.rev_rev b
  simp only [rhoN]
  rw [h1, h2]
  ring

theorem harish_chandra_holds : HCRev := by
  intro n lam ⟨hs, hz⟩
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · show -lam (Fin.rev b) < -lam (Fin.rev a)
    exact neg_lt_neg (hs (Fin.rev_lt_rev.mpr hab))
  · obtain ⟨m, hm⟩ := hz (Fin.rev a)
    refine ⟨-m - (n : ℤ) + 1, ?_⟩
    simp only [revP]
    push_cast
    linarith

theorem spectral_gap_holds : GapRev := by
  intro n ε lam h hg a b hab
  have := hg (Fin.rev a) (Fin.rev b) hab
  have e : revP lam a - revP lam b = -(lam (Fin.rev a) - lam (Fin.rev b)) := by
    simp only [revP]; ring
  rw [e, abs_neg]
  exact this

theorem lowest_k_type_holds : LowKRev := by
  intro n ε lam
  funext a
  simp only [lowK, revP, Pi.add_apply, Pi.sub_apply, revNum_rhoC, revNum_rhoN]
  ring

theorem revNum_nsq (u : Fin n → ℝ) : nsq (revP u) = nsq u := by
  simp only [nsq, dot, revP, neg_mul_neg]
  exact Equiv.sum_comp Fin.revPerm (fun a => u a * u a)

theorem vector_norm_holds : VNormRev := by
  intro n ε ν
  have e : revP ν + (2 : ℝ) • rhoC (revE ε) = revP (ν + (2 : ℝ) • rhoC ε) := by
    funext a
    simp only [revP, Pi.add_apply, Pi.smul_apply, smul_eq_mul, revNum_rhoC]
    ring
  simp only [vNormSq]
  rw [e, revNum_nsq]

theorem compact_dominant_holds : CDomRev := by
  intro n ε μ Λ ⟨c, hc, hsum⟩
  refine ⟨fun a b => c (Fin.rev b) (Fin.rev a), fun a b h => ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := hc _ _ h
    exact ⟨Fin.rev_lt_rev.mp h1, h2.symm⟩
  · funext x
    have key : ∀ a b : Fin n, root (Fin.rev b) (Fin.rev a) x = - root a b (Fin.rev x) := by
      intro a b
      simp only [root, Pi.sub_apply, revNum_single]
      ring
    have hx := congrFun hsum (Fin.rev x)
    simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hx
    have re : (∑ a : Fin n, ∑ b : Fin n, (c (Fin.rev b) (Fin.rev a) : ℝ) * root a b x) =
        ∑ a : Fin n, ∑ b : Fin n, (c a b : ℝ) * root (Fin.rev b) (Fin.rev a) x := by
      rw [Finset.sum_comm]
      refine Fintype.sum_equiv Fin.revPerm _ _ (fun b => ?_)
      refine Fintype.sum_equiv Fin.revPerm _ _ (fun a => ?_)
      simp only [Fin.revPerm_apply, Fin.rev_rev]
    simp only [Pi.sub_apply, revP, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [re]
    simp only [key, mul_neg, Finset.sum_neg_distrib, ← hx]
    ring

end PI.ZuckTensorWork
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ZuckermanTensor.SquareIntegrableConj
section
open MeasureTheory Matrix Finset
open scoped InnerProductSpace NNReal ENNReal
noncomputable section
namespace PI.ZuckTensorWork
open PI.UpqRep PI.ZuckTensor

namespace SqInt

variable {n : ℕ}

theorem revM_mul (A B : Matrix (Fin n) (Fin n) ℂ) : revM (A * B) = revM A * revM B := by
  unfold revM
  exact (Matrix.submatrix_mul_equiv A B Fin.rev Fin.revPerm Fin.rev).symm

theorem revM_one : revM (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  ext i j
  simp [revM, Matrix.one_apply]

theorem revM_revM (A : Matrix (Fin n) (Fin n) ℂ) : revM (revM A) = A := by
  ext i j
  simp [revM]

theorem revM_conjTranspose (A : Matrix (Fin n) (Fin n) ℂ) : revM Aᴴ = (revM A)ᴴ := by
  unfold revM
  exact (Matrix.conjTranspose_submatrix A Fin.rev Fin.rev).symm

theorem revM_Jm (ε : Fin n → Bool) : revM (Jm ε) = Jm (revE ε) := by
  unfold revM Jm revE
  exact Matrix.submatrix_diagonal _ Fin.rev Fin.rev_injective

theorem inUJ_rev (ε : Fin n → Bool) {g : Matrix (Fin n) (Fin n) ℂ} (h : inUJ ε g) :
    inUJ (revE ε) (revM g) := by
  unfold inUJ at *
  rw [← revM_Jm, ← revM_conjTranspose, ← revM_mul, ← revM_mul, h]

def revHom : Matrix (Fin n) (Fin n) ℂ →* Matrix (Fin n) (Fin n) ℂ where
  toFun := revM
  map_one' := revM_one
  map_mul' := revM_mul

theorem mem_fwd (ε : Fin n → Bool) (g : UJ (revE ε)) :
    Units.map (revHom (n := n)) (g : (Matrix (Fin n) (Fin n) ℂ)ˣ) ∈ UJ ε := by
  show inUJ ε (revM (umat g))
  have h := inUJ_rev (revE ε) (g.2 : inUJ (revE ε) (umat g))
  rwa [revE_revE] at h

theorem mem_bwd (ε : Fin n → Bool) (g : UJ ε) :
    Units.map (revHom (n := n)) (g : (Matrix (Fin n) (Fin n) ℂ)ˣ) ∈ UJ (revE ε) := by
  show inUJ (revE ε) (revM (umat g))
  exact inUJ_rev ε (g.2 : inUJ ε (umat g))

def phiE (ε : Fin n → Bool) : UJ (revE ε) ≃* UJ ε where
  toFun g := ⟨Units.map revHom (g : (Matrix (Fin n) (Fin n) ℂ)ˣ), mem_fwd ε g⟩
  invFun g := ⟨Units.map revHom (g : (Matrix (Fin n) (Fin n) ℂ)ˣ), mem_bwd ε g⟩
  left_inv g := by
    apply Subtype.ext; apply Units.ext
    exact revM_revM (umat g)
  right_inv g := by
    apply Subtype.ext; apply Units.ext
    exact revM_revM (umat g)
  map_mul' g h := by
    apply Subtype.ext; apply Units.ext
    exact revM_mul (umat g) (umat h)

theorem phiE_cont (ε : Fin n → Bool) : Continuous (phiE ε) := by
  rw [(isClosedEmbeddingMatrix n ε).1.isInducing.continuous_iff]
  show Continuous (fun g : UJ (revE ε) => (coeMatrixAlt (revE ε) g).submatrix Fin.rev Fin.rev)
  exact (continuous_coeMatrix (revE ε)).matrix_submatrix Fin.rev Fin.rev

theorem phiE_symm_cont (ε : Fin n → Bool) : Continuous (phiE ε).symm := by
  rw [(isClosedEmbeddingMatrix n (revE ε)).1.isInducing.continuous_iff]
  show Continuous (fun g : UJ ε => (coeMatrixAlt ε g).submatrix Fin.rev Fin.rev)
  exact (continuous_coeMatrix ε).matrix_submatrix Fin.rev Fin.rev

end SqInt

open SqInt in
theorem square_integrable_conj : SqIntConj := by
  intro n ε H _ _ σ hs v w
  have hmap : (Measure.map (phiE ε) (muG (revE ε))).IsHaarMeasure :=
    (phiE ε).isHaarMeasure_map (muG (revE ε)) (phiE_cont ε) (phiE_symm_cont ε)
  have heq := Measure.isMulLeftInvariant_eq_smul (Measure.map (phiE ε) (muG (revE ε))) (muG ε)
  have h1 : MemLp (coefOn (ε := ε) σ (Cj.un v) (Cj.un w)) 2 (Measure.map (phiE ε) (muG (revE ε))) := by
    rw [heq, ENNReal.smul_def]
    exact (hs _ _).smul_measure ENNReal.coe_ne_top
  have h2 := (memLp_map_measure_iff h1.1 (phiE_cont ε).measurable.aemeasurable).1 h1
  have e : coefOn (ε := revE ε) (sigC σ) v w = star (coefOn (ε := ε) σ (Cj.un v) (Cj.un w) ∘ phiE ε) := by
    funext g
    show ⟪w, cjOp (σ (revM (umat g))) v⟫_ℂ = star ⟪Cj.un w, σ (revM (umat g)) (Cj.un v)⟫_ℂ
    rw [Cj.inner_def, cjOp_apply]
    exact (inner_conj_symm _ _).symm
  rw [e]
  exact h2.star

end PI.ZuckTensorWork
end
end

