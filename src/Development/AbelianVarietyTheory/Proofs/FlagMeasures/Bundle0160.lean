import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormPosOfIsUnit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0134
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0064
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0061
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0139
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0091
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0144
import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemMaxCompactInterLeviIffFrame

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IpLEqZeroOfMemSpan
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas Formalism.REAL

noncomputable section

namespace GlobalTheory.NilCov

variable {n : ℕ} {ε : Fin n → Bool}

def ipL (Y : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℝ where
  toFun X := ((X * Yᴴ).trace).re
  map_add' X X' := by simp [add_mul]
  map_smul' a X := by simp

theorem ipL_apply (X Y : Matrix (Fin n) (Fin n) ℂ) : ipL Y X = ((X * Yᴴ).trace).re := rfl

theorem ipL_comm (X Y : Matrix (Fin n) (Fin n) ℂ) : ipL Y X = ipL X Y := by
  rw [ipL_apply, ipL_apply]

  have hswap : Y * Xᴴ = (X * Yᴴ)ᴴ := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose]
  rw [hswap, trace_conjTranspose, Complex.star_def, Complex.conj_re]

private theorem Jm_sq_lemma : Jm ε * Jm ε = 1 := by
  rw [Jm, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext a
  by_cases ha : ε a <;> simp [ha]

private theorem Jm_conjTransposeFlagMeasures' : (Jm ε)ᴴ = Jm ε := by
  rw [Jm, diagonal_conjTranspose]
  congr 1
  funext a
  by_cases ha : ε a <;> simp [ha]

private theorem Jm_mul_Jm_mulFlagMeasures (M : Matrix (Fin n) (Fin n) ℂ) : Jm ε * (Jm ε * M) = M := by
  rw [← Matrix.mul_assoc, Jm_sq_lemma, Matrix.one_mul]

theorem inv_eq_neg_of_inG {Y : Matrix (Fin n) (Fin n) ℂ} (h : inG ε Y) : Jm ε * Yᴴ * Jm ε = -Y := by
  have h0 : Yᴴ * Jm ε + Jm ε * Y = 0 := h
  have h1 : Yᴴ * Jm ε = -(Jm ε * Y) := eq_neg_of_add_eq_zero_left h0
  rw [Matrix.mul_assoc, h1, Matrix.mul_neg, Jm_mul_Jm_mulFlagMeasures]

theorem inG_sub_inv (X : Matrix (Fin n) (Fin n) ℂ) : inG ε (X - Jm ε * Xᴴ * Jm ε) := by
  show (X - Jm ε * Xᴴ * Jm ε)ᴴ * Jm ε + Jm ε * (X - Jm ε * Xᴴ * Jm ε) = 0
  simp only [conjTranspose_sub, conjTranspose_mul, conjTranspose_conjTranspose, Jm_conjTransposeFlagMeasures',
    Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, Jm_sq_lemma, Jm_mul_Jm_mulFlagMeasures, Matrix.mul_one]
  abel

theorem ipL_inv {Y : Matrix (Fin n) (Fin n) ℂ} (h : inG ε Y) (X : Matrix (Fin n) (Fin n) ℂ) :
    ipL Y (Jm ε * Xᴴ * Jm ε) = -ipL Y X := by
  have h0 : Yᴴ * Jm ε + Jm ε * Y = 0 := h
  have h1 : Jm ε * Y = -(Yᴴ * Jm ε) := eq_neg_of_add_eq_zero_right h0

  have hY : Jm ε * Y * Jm ε = -Yᴴ := by
    rw [h1, Matrix.neg_mul, Matrix.mul_assoc, Jm_sq_lemma, Matrix.mul_one]
  have hstar : (Jm ε * Xᴴ * Jm ε)ᴴ = Jm ε * X * Jm ε := by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, Jm_conjTransposeFlagMeasures', Matrix.mul_assoc]
  have htr : (Y * (Jm ε * X * Jm ε)).trace = -(X * Yᴴ).trace :=
    calc (Y * (Jm ε * X * Jm ε)).trace = ((Y * (Jm ε * X)) * Jm ε).trace := by
          simp only [Matrix.mul_assoc]
      _ = (Jm ε * (Y * (Jm ε * X))).trace := Matrix.trace_mul_comm _ _
      _ = (Jm ε * Y * Jm ε * X).trace := by simp only [Matrix.mul_assoc]
      _ = (-Yᴴ * X).trace := by rw [hY]
      _ = -(X * Yᴴ).trace := by rw [Matrix.neg_mul, Matrix.trace_neg, Matrix.trace_mul_comm]
  rw [ipL_comm, ipL_apply, ipL_apply, hstar, htr, Complex.neg_re]

theorem ipL_sub_inv {Y : Matrix (Fin n) (Fin n) ℂ} (h : inG ε Y) (X : Matrix (Fin n) (Fin n) ℂ) :
    ipL Y (X - Jm ε * Xᴴ * Jm ε) = 2 * ipL Y X := by
  rw [map_sub, ipL_inv h]
  ring

theorem add_inv_eq (g : UJ ε) :
    (uMat g - 1) + Jm ε * (uMat g - 1)ᴴ * Jm ε = -(Jm ε * (uMat g - 1)ᴴ * Jm ε * (uMat g - 1)) := by
  have hg : (uMat g)ᴴ * Jm ε * uMat g = Jm ε := g.2

  have key : Jm ε * (uMat g)ᴴ * Jm ε * uMat g = 1 := by
    calc Jm ε * (uMat g)ᴴ * Jm ε * uMat g = Jm ε * ((uMat g)ᴴ * Jm ε * uMat g) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg, Jm_sq_lemma]
  have e : Jm ε * (uMat g - 1)ᴴ * Jm ε = Jm ε * (uMat g)ᴴ * Jm ε - 1 := by
    rw [conjTranspose_sub, conjTranspose_one, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Jm_sq_lemma]
  rw [e, Matrix.sub_mul, Matrix.mul_sub, key, Matrix.mul_one, Matrix.one_mul]
  abel

variable {d : ℕ} {E : Fin d → Matrix (Fin n) (Fin n) ℂ}

theorem ipL_eq_zero_of_mem_span
    (hE : ∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) {s : Set (Fin d)} {i : Fin d}
    (hi : i ∉ s) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ Submodule.span ℝ (E '' s)) : ipL (E i) X = 0 := by
  have hle : Submodule.span ℝ (E '' s) ≤ LinearMap.ker (ipL (E i)) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, hj, rfl⟩
    have hji : j ≠ i := fun e => hi (e ▸ hj)
    simp [LinearMap.mem_ker, ipL_apply, hE, hji]
  exact hle hX

theorem eq_sum_of_mem_span
    (hE : ∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X ∈ Submodule.span ℝ (Set.range E)) : X = ∑ i, ipL (E i) X • E i := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hX
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1

  simp [map_sum, ipL_apply, hE]

theorem ipL_eq_zero_of_mem
    (hE : ∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) (hG : ∀ i, inG ε (E i))
    {B : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)} (hB : ∀ X ∈ B, Jm ε * Xᴴ * Jm ε ∈ B) {s : Set (Fin d)}
    (hs : ∀ X, X ∈ B ∧ inG ε X → X ∈ Submodule.span ℝ (E '' s)) {i : Fin d} (hi : i ∉ s)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ B) : ipL (E i) X = 0 := by
  have hZ : X - Jm ε * Xᴴ * Jm ε ∈ Submodule.span ℝ (E '' s) :=
    hs _ ⟨B.sub_mem hX (hB X hX), inG_sub_inv X⟩
  have h0 := ipL_eq_zero_of_mem_span hE hi hZ
  rw [ipL_sub_inv (hG i)] at h0
  linarith

theorem sub_mem_of_coord_eq {A : ℕ → Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)} {deg : Fin d → ℕ}
    (hmul : ∀ c, ∀ X ∈ A c, ∀ Y ∈ A 0, X * Y ∈ A (c + 1) ∧ Y * X ∈ A (c + 1))
    (hinv : ∀ c, ∀ X ∈ A c, Jm ε * Xᴴ * Jm ε ∈ A c)
    (hE : ∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0)
    (hsp : ∀ c X, (X ∈ A c ∧ inG ε X) ↔ X ∈ Submodule.span ℝ (E '' {i | c ≤ deg i}))
    {g h : UJ ε} (hg : uMat g - 1 ∈ A 0) (hh : uMat h - 1 ∈ A 0) (c : ℕ)
    (hc : ∀ i, deg i < c → ipL (E i) (uMat g - 1) = ipL (E i) (uMat h - 1)) :
    uMat g - uMat h ∈ A c := by

  have hGi : ∀ i, inG ε (E i) := fun i =>
    ((hsp 0 (E i)).2 (Submodule.subset_span ⟨i, Nat.zero_le _, rfl⟩)).2
  have eX := add_inv_eq g
  have eY := add_inv_eq h
  have hgX : uMat g - 1 ∈ A 0 := hg
  have hhY : uMat h - 1 ∈ A 0 := hh
  revert hc
  generalize uMat g = G at eX eY hgX ⊢
  generalize uMat h = H at eX eY hhY ⊢
  induction c with
  | zero =>
    intro _
    have h0 := (A 0).sub_mem hgX hhY
    rwa [sub_sub_sub_cancel_right] at h0
  | succ c ih =>
    intro hc
    have hD : G - H ∈ A c := ih fun i hi => hc i (Nat.lt_succ_of_lt hi)
    have hθD : Jm ε * (G - H)ᴴ * Jm ε ∈ A c := hinv c _ hD
    have hDXY : G - H = (G - 1) - (H - 1) := (sub_sub_sub_cancel_right G H 1).symm

    have hsym : (G - H) + Jm ε * (G - H)ᴴ * Jm ε ∈ A (c + 1) := by
      have hθ : Jm ε * (G - H)ᴴ * Jm ε = Jm ε * (G - 1)ᴴ * Jm ε - Jm ε * (H - 1)ᴴ * Jm ε := by
        rw [hDXY, conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul]
      have hprod : (G - H) + Jm ε * (G - H)ᴴ * Jm ε =
          -(Jm ε * (G - 1)ᴴ * Jm ε * (G - H) + Jm ε * (G - H)ᴴ * Jm ε * (H - 1)) := by
        rw [hθ, hDXY, Matrix.mul_sub, Matrix.sub_mul]
        calc (G - 1) - (H - 1) + (Jm ε * (G - 1)ᴴ * Jm ε - Jm ε * (H - 1)ᴴ * Jm ε)
            = ((G - 1) + Jm ε * (G - 1)ᴴ * Jm ε) - ((H - 1) + Jm ε * (H - 1)ᴴ * Jm ε) := by abel
          _ = -(Jm ε * (G - 1)ᴴ * Jm ε * (G - 1)) - -(Jm ε * (H - 1)ᴴ * Jm ε * (H - 1)) := by
            rw [eX, eY]
          _ = _ := by abel
      rw [hprod]
      refine (A (c + 1)).neg_mem ((A (c + 1)).add_mem ?_ ?_)
      · exact (hmul c _ hD _ (hinv 0 _ hgX)).2
      · exact (hmul c _ hθD _ hhY).1

    have hW : (G - H) - Jm ε * (G - H)ᴴ * Jm ε ∈ A (c + 1) := by
      have hWc : (G - H) - Jm ε * (G - H)ᴴ * Jm ε ∈ A c := (A c).sub_mem hD hθD
      have hWsp := (hsp c _).1 ⟨hWc, inG_sub_inv (G - H)⟩
      have hWr : (G - H) - Jm ε * (G - H)ᴴ * Jm ε ∈ Submodule.span ℝ (Set.range E) :=
        Submodule.span_mono (Set.image_subset_range _ _) hWsp
      have hcoord : ∀ i, deg i < c + 1 → ipL (E i) ((G - H) - Jm ε * (G - H)ᴴ * Jm ε) = 0 := by
        intro i hi
        rw [ipL_sub_inv (hGi i), hDXY, map_sub, hc i hi, sub_self, mul_zero]
      have hsum := eq_sum_of_mem_span hE hWr
      have hspan : (G - H) - Jm ε * (G - H)ᴴ * Jm ε ∈ Submodule.span ℝ (E '' {i | c + 1 ≤ deg i}) := by
        rw [hsum]
        refine Submodule.sum_mem _ fun i _ => ?_
        by_cases hi : c + 1 ≤ deg i
        · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
        · rw [hcoord i (by omega), zero_smul]
          exact Submodule.zero_mem _
      exact ((hsp (c + 1) _).2 hspan).1
    have h2 : (2 : ℝ) • (G - H) ∈ A (c + 1) := by
      have hs2 := (A (c + 1)).add_mem hsym hW
      convert hs2 using 1
      rw [two_smul]
      abel
    have h1 := (A (c + 1)).smul_mem (1 / 2 : ℝ) h2
    rwa [smul_smul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul] at h1

end GlobalTheory.NilCov
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsTotallyIsotropicFlagComplexifiedSaturatedFlag
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas

private theorem finrank_span_map_ringHom_eq_finrank {K : Type*} [Field K] {n : ℕ} (φ : K →+* ℂ)
    (U : Submodule K (Fin n → K)) :
    Module.finrank ℂ (Submodule.span ℂ ((fun y : Fin n → K => fun l => φ (y l)) '' (U : Set (Fin n → K)))) =
      Module.finrank K U := by

  have hle : ∀ V : Submodule K (Fin n → K),
      Module.finrank ℂ (Submodule.span ℂ ((fun y : Fin n → K => fun l => φ (y l)) '' (V : Set (Fin n → K)))) ≤
        Module.finrank K V := by
    intro V
    let b := Module.finBasis K V
    have hsub : (fun y : Fin n → K => fun l => φ (y l)) '' (V : Set (Fin n → K)) ⊆
        Submodule.span ℂ (Set.range fun k => fun l => φ ((b k : Fin n → K) l)) := by
      rintro _ ⟨u, hu, rfl⟩
      simp only [SetLike.mem_coe]
      have hu' : u = ∑ k, b.repr ⟨u, hu⟩ k • (b k : Fin n → K) := by
        have h := congrArg Subtype.val (b.sum_repr ⟨u, hu⟩)
        simp only [Submodule.coe_sum, SetLike.val_smul] at h
        exact h.symm
      have hφ : (fun l => φ (u l)) = ∑ k, φ (b.repr ⟨u, hu⟩ k) • fun l => φ ((b k : Fin n → K) l) := by
        conv_lhs => rw [hu']
        ext l
        simp [Finset.sum_apply, map_sum, map_mul]
      rw [hφ]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    calc Module.finrank ℂ (Submodule.span ℂ ((fun y : Fin n → K => fun l => φ (y l)) '' (V : Set (Fin n → K))))
        ≤ Module.finrank ℂ (Submodule.span ℂ (Set.range fun k => fun l => φ ((b k : Fin n → K) l))) :=
          Submodule.finrank_mono (Submodule.span_le.2 hsub)
      _ ≤ Fintype.card (Fin (Module.finrank K V)) := finrank_range_le_card _
      _ = Module.finrank K V := Fintype.card_fin _
  have hsup : ∀ V V' : Submodule K (Fin n → K), V ⊔ V' = ⊤ →
      Submodule.span ℂ ((fun y : Fin n → K => fun l => φ (y l)) '' (V : Set (Fin n → K))) ⊔
        Submodule.span ℂ ((fun y : Fin n → K => fun l => φ (y l)) '' (V' : Set (Fin n → K))) = ⊤ := by
    intro V V' h
    rw [eq_top_iff]
    intro z _
    have hz : z = ∑ i, z i • (Pi.single i (1 : ℂ) : Fin n → ℂ) := by
      ext l
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hz]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    have hsingle : (fun l => φ ((Pi.single i (1 : K) : Fin n → K) l)) = (Pi.single i (1 : ℂ) : Fin n → ℂ) := by
      ext l
      by_cases hl : l = i
      · subst hl; simp
      · simp [Pi.single_eq_of_ne hl]
    rw [← hsingle]
    have hmem : (Pi.single i (1 : K) : Fin n → K) ∈ V ⊔ V' := by rw [h]; exact Submodule.mem_top
    obtain ⟨u, hu, u', hu', hsum⟩ := Submodule.mem_sup.1 hmem
    rw [← hsum]
    have hadd : (fun l => φ ((u + u') l)) = (fun l => φ (u l)) + fun l => φ (u' l) := by
      ext l; simp
    rw [hadd]
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨u, hu, rfl⟩) (Submodule.subset_span ⟨u', hu', rfl⟩)
  obtain ⟨U', hU'⟩ := Submodule.exists_isCompl U
  have h1 := hle U
  have h2 := hle U'
  have h3 : Module.finrank K U + Module.finrank K U' = n := by
    have := Submodule.finrank_add_eq_of_isCompl hU'
    simpa using this
  have h4 := Submodule.finrank_add_le_finrank_add_finrank
    (Submodule.span ℂ ((fun y : Fin n → K => fun l => φ (y l)) '' (U : Set (Fin n → K))))
    (Submodule.span ℂ ((fun y : Fin n → K => fun l => φ (y l)) '' (U' : Set (Fin n → K))))
  rw [hsup U U' hU'.sup_eq_top, finrank_top, Module.finrank_fin_fun] at h4
  omega

private theorem span_map_ringHom_span_eq_span_map {K : Type*} [Field K] {n : ℕ} (φ : K →+* ℂ) (X : Set (Fin n → K)) :
    Submodule.span ℂ ((fun y : Fin n → K => fun l => φ (y l)) '' (Submodule.span K X : Set (Fin n → K))) =
      Submodule.span ℂ ((fun y : Fin n → K => fun l => φ (y l)) '' X) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    induction hy using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero =>
      have h0 : (fun l => φ ((0 : Fin n → K) l)) = 0 := by ext; simp
      change (fun l => φ ((0 : Fin n → K) l)) ∈ Submodule.span ℂ ((fun y : Fin n → K => fun l => φ (y l)) '' X)
      rw [h0]; exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      have h : (fun l => φ ((x + y) l)) = (fun l => φ (x l)) + fun l => φ (y l) := by ext; simp
      change (fun l => φ (x l)) ∈ Submodule.span ℂ ((fun y : Fin n → K => fun l => φ (y l)) '' X) at hx
      change (fun l => φ (y l)) ∈ Submodule.span ℂ ((fun y : Fin n → K => fun l => φ (y l)) '' X) at hy
      change (fun l => φ ((x + y) l)) ∈ Submodule.span ℂ ((fun y : Fin n → K => fun l => φ (y l)) '' X)
      rw [h]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx =>
      have h : (fun l => φ ((c • x) l)) = φ c • fun l => φ (x l) := by ext; simp
      change (fun l => φ (x l)) ∈ Submodule.span ℂ ((fun y : Fin n → K => fun l => φ (y l)) '' X) at hx
      change (fun l => φ ((c • x) l)) ∈ Submodule.span ℂ ((fun y : Fin n → K => fun l => φ (y l)) '' X)
      rw [h]; exact Submodule.smul_mem _ _ hx
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

theorem isIsoFlag_flagAt_of_isSatFlag :
    ∀ (I : AutInst) (Λ : Submodule (𝓞 I.E) (Fin I.n → I.E)) (a : ℕ) (j : Fin a → ℕ)
      (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)),
      IsSatFlag I Λ j S → ∀ v, IsIsoFlag (I.ε v) j (flagAt I S v) := by
  intro I Λ a j S hS v
  obtain ⟨h0, hmono, hrk, -, hiso⟩ := hS
  have hdet : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  have hPQ : I.P v * (I.P v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hinj : Function.Injective (Matrix.mulVecLin (I.P v)⁻¹) := by
    intro x y hxy
    have h := congrArg (fun z => I.P v *ᵥ z) hxy
    simpa [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hPQ] using h

  have hspan : ∀ i, flagAt I S v i =
      (Submodule.span ℂ ((fun y : Fin I.n → I.E => fun l => I.φ v (y l)) '' (S i : Set _))).map
        (Matrix.mulVecLin (I.P v)⁻¹) := by
    intro i
    rw [Submodule.map_span, Set.image_image]
    rfl
  have hfr : ∀ i, Module.finrank ℂ (flagAt I S v i) = Formalism.HN.rkK (S i) := by
    intro i
    rw [hspan i, ← (Submodule.equivMapOfInjective _ hinj _).finrank_eq]
    show _ = Module.finrank I.E (Submodule.span I.E (S i : Set (Fin I.n → I.E)))
    rw [← span_map_ringHom_span_eq_span_map, finrank_span_map_ringHom_eq_finrank]

  have hstar : ∀ x : I.E, I.φ v (starRingEnd I.E x) = starRingEnd ℂ (I.φ v x) := fun x =>
    I.cm.cmUnram.2.1 (I.φ v) x
  have hJ : ((I.P v)⁻¹)ᴴ * (Formalism.REAL.Jm (I.ε v) * (I.P v)⁻¹) = I.J.map (I.φ v) := by
    rw [← I.P_spec v]
    calc ((I.P v)⁻¹)ᴴ * ((I.P v)ᴴ * I.J.map (I.φ v) * I.P v * (I.P v)⁻¹)
        = (I.P v * (I.P v)⁻¹)ᴴ * I.J.map (I.φ v) * (I.P v * (I.P v)⁻¹) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = I.J.map (I.φ v) := by rw [hPQ]; simp
  have hgen : ∀ x y : Fin I.n → ℂ, star ((I.P v)⁻¹ *ᵥ x) ⬝ᵥ (Formalism.REAL.Jm (I.ε v) *ᵥ ((I.P v)⁻¹ *ᵥ y)) =
      star x ⬝ᵥ (I.J.map (I.φ v) *ᵥ y) := by
    intro x y
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
    simp only [Matrix.mulVec_mulVec, hJ]
  have hpair : ∀ s ∈ S (Fin.last a), ∀ t ∈ S (Fin.last a),
      star (fun l => I.φ v (s l)) ⬝ᵥ (I.J.map (I.φ v) *ᵥ fun l => I.φ v (t l)) = 0 := by
    intro s hs t ht
    have h := hiso s hs t ht
    have h' := congrArg (I.φ v) h
    rw [map_zero] at h'
    rw [← h']
    simp [Formalism.UG.hform, dotProduct, Matrix.mulVec, map_sum, map_mul, hstar, Finset.mul_sum, mul_assoc]
  refine ⟨?_, ?_, ?_, ?_⟩
  · show Submodule.span ℂ _ = ⊥
    rw [Submodule.span_eq_bot]
    rintro _ ⟨y, hy, rfl⟩
    rw [h0] at hy
    have hy0 : y = 0 := by simpa using hy
    subst hy0
    ext l
    simp [Matrix.mulVec, dotProduct]
  · intro i k hik
    exact Submodule.span_mono (Set.image_mono (SetLike.coe_subset_coe.2 (hmono hik)))
  · intro i
    rw [hfr, hfr]
    exact hrk i
  · intro x hx y hy
    rw [hspan] at hx hy
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hx
    obtain ⟨w', hw', rfl⟩ := Submodule.mem_map.1 hy
    rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, hgen]
    clear hx hy

    have hgen1 : ∀ g ∈ (fun y : Fin I.n → I.E => fun l => I.φ v (y l)) '' (S (Fin.last a) : Set (Fin I.n → I.E)),
        ∀ z ∈ Submodule.span ℂ
          ((fun y : Fin I.n → I.E => fun l => I.φ v (y l)) '' (S (Fin.last a) : Set (Fin I.n → I.E))),
          star g ⬝ᵥ (I.J.map (I.φ v) *ᵥ z) = 0 := by
      rintro _ ⟨s, hs, rfl⟩ z hz
      induction hz using Submodule.span_induction with
      | mem u hu =>
        obtain ⟨t, ht, rfl⟩ := hu
        exact hpair s hs t ht
      | zero => simp
      | add u u' _ _ hu hu' => rw [Matrix.mulVec_add, dotProduct_add, hu, hu', add_zero]
      | smul c u _ hu => rw [Matrix.mulVec_smul, dotProduct_smul, hu, smul_zero]
    induction hw using Submodule.span_induction with
    | mem u hu => exact hgen1 u hu w' hw'
    | zero => simp
    | add u u' _ _ hu hu' => rw [star_add, add_dotProduct, hu, hu', add_zero]
    | smul c u _ hu => rw [star_smul, smul_dotProduct, hu, smul_zero]

end GlobalTheory.FlagMeas
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LogSingularValuesEuclidNormCartanProperties
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.Count.CartanSize

open GlobalTheory.Count.Cartan

theorem cartan_size : ∀ (n : ℕ) (ε : Fin n → Bool), Continuous (fun g : UJ ε => dHS (uMat g)) ∧ (∀ g : UJ ε, 0 ≤ dHS (uMat g) ∧ dOp (uMat g) ≤ dHS (uMat g)) ∧ (∀ g : UJ ε, ∃ k ∈ Kset ε, ∃ X, inP ε X ∧ uMat g = k * NormedSpace.exp X ∧ dHS (uMat g) = Real.sqrt (hs X)) ∧ (rkR ε = 0 → ∀ g : UJ ε, dHS (uMat g) = 0) := by
  intro n ε
  have hU : ∀ g : UJ ε, Formalism.REAL.inUJ ε (uMat g) := fun g => g.2
  have hnn : ∀ g : Matrix (Fin n) (Fin n) ℂ, 0 ≤ dHS g := fun g => Real.sqrt_nonneg _
  obtain ⟨-, hB, -, hC, -⟩ := GlobalTheory.Count.Cartan.cartan_distances n ε
  refine ⟨hC, ?_, ?_, ?_⟩
  · intro g
    refine ⟨hnn _, ?_⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [GlobalTheory.Dec.dOp_fin_zero]
      exact hnn _
    · obtain ⟨h0, -, -, h2, -⟩ := hB g g (by omega)
      have h1 : (1 : ℝ) ≤ Real.sqrt 2 := by
        rw [show (1 : ℝ) = Real.sqrt 1 by simp]
        exact Real.sqrt_le_sqrt (by norm_num)
      nlinarith
  · intro g
    exact ⟨uMat g * NormedSpace.exp (-Formalism.REAL.polarLog (uMat g)), Formalism.REAL.mul_exp_neg_polarLog_mem_compact (hU g),
      Formalism.REAL.polarLog (uMat g), Formalism.REAL.polarLog_mem_hermitian_part (hU g), Formalism.REAL.polar_decomposition_eq,
      GlobalTheory.Count.Cartan.dHS_eq_log (hU g)⟩
  · intro hr g
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [dHS]
    · obtain ⟨-, -, -, -, h3⟩ := hB g g (by omega)
      simp only [hr, Nat.cast_zero, mul_zero, Real.sqrt_zero, zero_mul] at h3
      exact le_antisymm h3 (hnn _)

end GlobalTheory.Count.CartanSize
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassDefectOrderLe
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DefectShare

theorem mass_defect_order_le : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ β : ℕ, 1 ≤ β → (S.sumData fun d => S.mass d fun Λ => S.be d Λ = β) ≤ ENNReal.ofReal ((4 * S.Hp ^ (4 * (r + 1))) * ((β : ℝ) ^ (k - 1))⁻¹) * S.nn := by
  intro F _ _ _ _ _ E _ _ _ L r k S hk β hβ
  by_cases hex : ∃ d Λ, S.IsTerm d Λ
  swap
  · have h0 : (S.sumData fun d => S.mass d fun Λ => S.be d Λ = β) = 0 := by
      have : ∀ d Λ, ¬ S.IsTerm d Λ := fun d Λ h => hex ⟨d, Λ, h⟩
      simp [Frames.sumData, Frames.mass, this]
    rw [h0]; exact zero_le
  obtain ⟨d0, Λ0, h0⟩ := hex
  obtain ⟨-, -, -, hq, -⟩ := GlobalTheory.T.term_exponents_nonneg_and_defect_group_bound L r k S d0 Λ0 h0
  have hconst : 4 * (S.q : ℝ) ^ (2 * S.a * (2 * r + 2)) * ((β : ℝ) ^ (k - 1))⁻¹ ≤
      (4 * S.Hp ^ (4 * (r + 1))) * ((β : ℝ) ^ (k - 1))⁻¹ := by
    have e : (S.q : ℝ) ^ (2 * S.a * (2 * r + 2)) = ((S.q : ℝ) ^ S.a) ^ (4 * (r + 1)) := by
      rw [← zpow_natCast, ← zpow_mul]
      congr 1
      push_cast
      ring
    rw [e]
    have hn : (0 : ℝ) ≤ (S.q : ℝ) ^ S.a := zpow_nonneg (Nat.cast_nonneg _) _
    gcongr
  have s1 := (GlobalTheory.T.hermitianDataMass_eq_sum_frameClasses L r k S (fun d Λ => S.be d Λ = β) (fun h hh d Λ hT hP => by
    have := (GlobalTheory.T.hermitianFrames_stabilizer_acts_on_terms L r k S d Λ hT h hh).2.2.2.2.2.1
    exact this.trans hP)).1
  have s2 := (GlobalTheory.T.hermitianDataMass_eq_sum_frameClasses L r k S (fun _ _ => True) (fun _ _ _ _ _ _ => trivial)).1
  unfold Frames.nn
  rw [s1, s2]
  unfold Frames.sumCls
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun o => ?_
  split_ifs with hC
  · rw [mul_left_comm]
    refine mul_le_mul_right ?_ _
    refine (GlobalTheory.T.hermitianFrames_defectOrder_share_le L r k S hk _ hC.1 β hβ).trans ?_
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal hconst) ?_
    unfold Frames.sumData
    refine ENNReal.tsum_le_tsum fun o' => mul_le_mul' le_rfl ?_
    unfold Frames.nT
    exact ENat.toENNReal_le.mpr (Set.encard_le_encard fun Λ h => ⟨h.1, trivial, h.2.2⟩)
  · exact zero_le

end GlobalTheory.DefectShare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableHsNormSqAmplitudeBesselUnitaryStatement
section
open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurable_hsNormSq_amplitude_besselUnitary : ∀ (k r : ℕ) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (μG : Measure (Mt k r)) (c : ℝ) (Φ : Mat k r → Wp) (Φ' : Mat k r → Wq), IsHaarOn (GG k r) μG → ContinuousOn Φ (GG k r) → ContinuousOn Φ' (GG k r) → Measurable (Set.indicator {x : Mt k r | Matrix.of x ∈ GG k r} fun γ => hsNormSq (ampJ μG c Φ Φ' (Matrix.of γ))) := by
  first | exact @GlobalTheory.Amp.AmpMeas.measurable_hsNormSq_ampJ | exact GlobalTheory.Amp.AmpMeas.measurable_hsNormSq_ampJ | (intros; apply GlobalTheory.Amp.AmpMeas.measurable_hsNormSq_ampJ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemMaxCompactInterLeviIffFrameStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_maxCompact_inter_levi_iff_frame : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) (p' q' : ℕ) (T : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (P : Matrix (Fin n) (Fin p') ℂ) (Q : Matrix (Fin n) (Fin q') ℂ), ((∀ i, (T i)ᴴ * T i = 1) ∧ (∀ i k, i ≠ k → (T i)ᴴ * T k = 0) ∧ (∀ i k, (T i)ᴴ * Formalism.REAL.Jm ε * T k = 0) ∧ (∀ i, (T i)ᴴ * P = 0) ∧ (∀ i, (T i)ᴴ * Q = 0) ∧ Pᴴ * P = 1 ∧ Qᴴ * Q = 1 ∧ Formalism.REAL.Jm ε * P = P ∧ Formalism.REAL.Jm ε * Q = -Q ∧ (∑ i, (T i * (T i)ᴴ + Formalism.REAL.Jm ε * T i * (T i)ᴴ * Formalism.REAL.Jm ε)) + P * Pᴴ + Q * Qᴴ = 1 ∧ ∀ (l : Fin (a + 1)) (y : Fin n → ℂ), y ∈ W l ↔ (∑ i ∈ univ.filter (fun i : Fin a => i.val < l.val), T i * (T i)ᴴ) *ᵥ y = y) → ∀ g : Formalism.REAL.UJ ε, g ∈ maxK ε ∩ flagM ε W ↔ ∃ (k : ∀ i, Formalism.REAL.UJ (allPos (j i))) (u : Formalism.REAL.UJ (allPos p')) (v : Formalism.REAL.UJ (allPos q')), uMat g = (∑ i, (T i * uMat (k i) * (T i)ᴴ + Formalism.REAL.Jm ε * T i * uMat (k i) * (T i)ᴴ * Formalism.REAL.Jm ε)) + P * uMat u * Pᴴ + Q * uMat v * Qᴴ := by
  first | exact @GlobalTheory.FlagLeviRange.mem_maxK_inter_flagM_iff | exact GlobalTheory.FlagLeviRange.mem_maxK_inter_flagM_iff | (intros; apply GlobalTheory.FlagLeviRange.mem_maxK_inter_flagM_iff <;> assumption)
end

