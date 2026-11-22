import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0211
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
import Formalism.SharpRestriction.ParamsHeightRankConstant
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SettingBlocks
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0005
import Formalism.PeriodIntegrals.Bundle0010
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0214
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FirstSlotSliceSlotMixedCasimirZero
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0004
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0216
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0218
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalFrameOfIsotropicBlocks
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
open Formalism.REAL (Jm UJ Jm_mul_self Jm_conjTranspose)

noncomputable section

namespace GlobalTheory.FrameCompletion

theorem resolution {n n₀ : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ] (hn : n = n₀ + 2 * Fintype.card κ)
    (J : Matrix (Fin n) (Fin n) ℂ) (J₀ : Matrix (Fin n₀) (Fin n₀) ℂ) (hJ : Jᴴ = J) (hJJ : J * J = 1)
    (hJ₀ : J₀ * J₀ = 1) (P : Matrix (Fin n) κ ℂ) (C : Matrix (Fin n) (Fin n₀) ℂ)
    (h1 : Pᴴ * P = 1) (h2 : Pᴴ * J * P = 0) (h3 : Pᴴ * C = 0) (h4 : Pᴴ * J * C = 0) (h5 : Cᴴ * J * C = J₀) :
    P * Pᴴ + J * (P * Pᴴ) * J + C * J₀ * Cᴴ * J = 1 := by

  have a2 : Pᴴ * (J * P) = 0 := by rw [← Matrix.mul_assoc]; exact h2
  have a4 : Pᴴ * (J * (J * P)) = 1 := by rw [← Matrix.mul_assoc J, hJJ, Matrix.one_mul, h1]
  have a6 : Pᴴ * (J * C) = 0 := by rw [← Matrix.mul_assoc]; exact h4
  have hCP : Cᴴ * P = 0 := by
    have := congrArg conjTranspose h3
    simpa [conjTranspose_mul] using this
  have hCJP : Cᴴ * (J * P) = 0 := by
    have := congrArg conjTranspose h4
    simpa [conjTranspose_mul, hJ, Matrix.mul_assoc] using this
  have a7 : J₀ * (Cᴴ * (J * P)) = 0 := by rw [hCJP, Matrix.mul_zero]
  have a8 : J₀ * (Cᴴ * (J * (J * P))) = 0 := by
    rw [← Matrix.mul_assoc J J, hJJ, Matrix.one_mul, hCP, Matrix.mul_zero]
  have a9 : J₀ * (Cᴴ * (J * C)) = 1 := by rw [← Matrix.mul_assoc Cᴴ, h5, hJ₀]
  have hLM : fromRows (fromRows Pᴴ (Pᴴ * J)) (J₀ * Cᴴ * J) * fromCols (fromCols P (J * P)) C = 1 := by
    rw [fromRows_mul_fromCols, fromRows_mul_fromCols, fromRows_mul, mul_fromCols]
    simp only [Matrix.mul_assoc]
    rw [h1, a2, a4, h3, a6, a7, a8, a9, fromRows_zero, fromCols_zero, fromBlocks_one, fromBlocks_one]
  have hcard : Fintype.card ((κ ⊕ κ) ⊕ Fin n₀) = Fintype.card (Fin n) := by
    simp only [Fintype.card_sum, Fintype.card_fin, hn]
    ring
  have hML := (mul_eq_one_comm_of_card_eq ((κ ⊕ κ) ⊕ Fin n₀) (Fin n) ℂ hcard).mp hLM
  rw [← hML]
  simp only [fromCols_mul_fromRows, Matrix.mul_assoc]

theorem exists_square {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℂ) :
    ∃ D : Matrix (Fin m) (Fin m) ℂ, Dᴴ * D = Cᴴ * C := by
  open ComplexOrder MatrixOrder in
  have h0 : (0 : Matrix (Fin m) (Fin m) ℂ) ≤ Cᴴ * C := (posSemidef_conjTranspose_mul_self C).nonneg
  open ComplexOrder MatrixOrder in
  refine ⟨CFC.sqrt (Cᴴ * C), ?_⟩
  open ComplexOrder MatrixOrder in
  rw [← star_eq_conjTranspose, (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (Cᴴ * C))).star_eq]
  open ComplexOrder MatrixOrder in
  exact CFC.sqrt_mul_sqrt_self (Cᴴ * C) h0

theorem exists_isFrame : ∀ (n n₀ a : ℕ) (j : Fin a → ℕ) (ε : Fin n → Bool) (ε₀ : Fin n₀ → Bool) (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (A₀ : Matrix (Fin n) (Fin n₀) ℂ), n = n₀ + 2 * ∑ i, j i → (∀ i, (B i)ᴴ * B i = 1) → (∀ i k, i ≠ k → (B i)ᴴ * B k = 0) → (∀ i k, (B i)ᴴ * Formalism.REAL.Jm ε * B k = 0) → (∀ i, (B i)ᴴ * Formalism.REAL.Jm ε * A₀ = 0) → A₀ᴴ * Formalism.REAL.Jm ε * A₀ = Formalism.REAL.Jm ε₀ → ∃ (B₀ : Matrix (Fin n) (Fin n₀) ℂ) (s : Formalism.REAL.UJ ε₀) (d : ∀ k, Matrix (Fin (j k)) (Fin n₀) ℂ), IsFrame ε ε₀ B B₀ ∧ A₀ = B₀ * uMat s + ∑ k, B k * d k := by
  intro n n₀ a j ε ε₀ B A₀ hn h1 h2 h3 h4 h5
  classical
  have hJJ : Jm ε * Jm ε = 1 := Jm_mul_self ε
  have hJh : (Jm ε)ᴴ = Jm ε := Jm_conjTranspose ε
  have hJ₀J₀ : Jm ε₀ * Jm ε₀ = 1 := Jm_mul_self ε₀
  have hJ₀h : (Jm ε₀)ᴴ = Jm ε₀ := Jm_conjTranspose ε₀
  have hJJX : ∀ {m : Type} [Fintype m] (X : Matrix (Fin n) m ℂ), Jm ε * (Jm ε * X) = X := by
    intro m _ X
    rw [← Matrix.mul_assoc, hJJ, Matrix.one_mul]

  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin n) (Σ i, Fin (j i)) ℂ, P = Matrix.of fun r x => B x.1 r x.2 := ⟨_, rfl⟩
  have hPe : ∀ {m : Type} [Fintype m] (X : Matrix (Fin n) m ℂ) (x : Σ i, Fin (j i)) (d : m),
      (Pᴴ * X) x d = ((B x.1)ᴴ * X) x.2 d := by
    intro m _ X x d
    simp [hP, Matrix.mul_apply, Matrix.conjTranspose_apply]
  have hPc : ∀ {m : Type} [Fintype m] (X : Matrix m (Fin n) ℂ) (c : m) (x : Σ i, Fin (j i)),
      (X * P) c x = (X * B x.1) c x.2 := by
    intro m _ X c x
    simp [hP, Matrix.mul_apply]
  have hPPX : ∀ {m : Type} [Fintype m] (X : Matrix (Fin n) m ℂ),
      P * (Pᴴ * X) = ∑ i, B i * ((B i)ᴴ * X) := by
    intro m _ X
    ext r d
    simp only [Matrix.mul_apply, Matrix.sum_apply, Fintype.sum_sigma, hP, Matrix.of_apply,
      Matrix.conjTranspose_apply]
  have hPP : Pᴴ * P = 1 := by
    ext ⟨i, c⟩ ⟨k, d⟩
    rw [hPc, hPe]
    by_cases hik : i = k
    · subst hik
      simp [h1, Matrix.one_apply]
    · simp [h2 i k hik, hik]
  have hPJP : Pᴴ * Jm ε * P = 0 := by
    ext ⟨i, c⟩ ⟨k, d⟩
    rw [hPc, Matrix.mul_assoc, hPe, ← Matrix.mul_assoc]
    simp [h3 i k]
  have hPJA : Pᴴ * (Jm ε * A₀) = 0 := by
    ext ⟨i, c⟩ d
    rw [hPe, ← Matrix.mul_assoc]
    simp [h4 i]

  obtain ⟨C, hC⟩ : ∃ C : Matrix (Fin n) (Fin n₀) ℂ, C = A₀ - P * (Pᴴ * A₀) := ⟨_, rfl⟩
  have hPC : Pᴴ * C = 0 := by
    rw [hC, Matrix.mul_sub, ← Matrix.mul_assoc Pᴴ P, hPP, Matrix.one_mul, sub_self]
  have hJC0 : Jm ε * C = Jm ε * A₀ - Jm ε * P * (Pᴴ * A₀) := by
    rw [hC, Matrix.mul_sub, Matrix.mul_assoc]
  have hPJC : Pᴴ * (Jm ε * C) = 0 := by
    have hPJP' : Pᴴ * (Jm ε * P) = 0 := by rw [← Matrix.mul_assoc]; exact hPJP
    rw [hJC0, Matrix.mul_sub, hPJA, ← Matrix.mul_assoc Pᴴ, hPJP', Matrix.zero_mul, sub_zero]
  have hCJP : Cᴴ * (Jm ε * P) = 0 := by
    have := congrArg conjTranspose hPJC
    simpa [conjTranspose_mul, hJh, Matrix.mul_assoc] using this
  have hAJP : A₀ᴴ * (Jm ε * P) = 0 := by
    have := congrArg conjTranspose hPJA
    simpa [conjTranspose_mul, hJh, Matrix.mul_assoc] using this
  have hCJC : Cᴴ * (Jm ε * C) = Jm ε₀ := by
    rw [hJC0, Matrix.mul_sub, ← Matrix.mul_assoc Cᴴ (Jm ε * P), hCJP, Matrix.zero_mul, sub_zero, hC,
      conjTranspose_sub, Matrix.sub_mul, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
      Matrix.mul_assoc, Matrix.mul_assoc, hPJA, Matrix.mul_zero, Matrix.mul_zero, sub_zero,
      ← Matrix.mul_assoc, h5]
  have hcard : n = n₀ + 2 * Fintype.card (Σ i, Fin (j i)) := by
    simp [Fintype.card_sigma, hn]
  have hres := resolution hcard (Jm ε) (Jm ε₀) hJh hJJ hJ₀J₀ P C hPP hPJP hPC
    (by rw [Matrix.mul_assoc]; exact hPJC) (by rw [Matrix.mul_assoc]; exact hCJC)

  have hJC : Jm ε * C = C * (Jm ε₀ * (Cᴴ * C)) := by
    calc Jm ε * C
        = (P * Pᴴ + Jm ε * (P * Pᴴ) * Jm ε + C * Jm ε₀ * Cᴴ * Jm ε) * (Jm ε * C) := by
          rw [hres, Matrix.one_mul]
      _ = P * (Pᴴ * (Jm ε * C)) + Jm ε * (P * (Pᴴ * (Jm ε * (Jm ε * C))))
          + C * (Jm ε₀ * (Cᴴ * (Jm ε * (Jm ε * C)))) := by
          simp only [Matrix.add_mul, Matrix.mul_assoc]
      _ = C * (Jm ε₀ * (Cᴴ * C)) := by
          rw [hPJC, hJJX, hPC]
          simp
  have hCJ : Cᴴ * Jm ε = Cᴴ * (C * (Jm ε₀ * Cᴴ)) := by
    have := congrArg conjTranspose hJC
    simpa [conjTranspose_mul, hJh, hJ₀h, Matrix.mul_assoc] using this
  have hHJH : (Cᴴ * C) * Jm ε₀ * (Cᴴ * C) = Jm ε₀ := by
    calc (Cᴴ * C) * Jm ε₀ * (Cᴴ * C) = Cᴴ * (C * (Jm ε₀ * (Cᴴ * C))) := by simp only [Matrix.mul_assoc]
      _ = Cᴴ * (Jm ε * C) := by rw [hJC]
      _ = Jm ε₀ := hCJC
  obtain ⟨D, hD⟩ := exists_square C
  have hdetJ₀ : (Jm ε₀).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hJ₀J₀
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have hdet : D.det ≠ 0 := by
    intro h0
    have hH : (Cᴴ * C).det = 0 := by rw [← hD, Matrix.det_mul, h0, mul_zero]
    have := congrArg Matrix.det hHJH
    rw [Matrix.det_mul, Matrix.det_mul, hH, zero_mul, zero_mul] at this
    exact hdetJ₀ this.symm
  obtain ⟨s, hsh, hss⟩ := GlobalTheory.T.exists_hermitian_sqrt_in_signedUnitaryGroup n₀ ε₀ D hdet (by rw [hD]; exact hHJH)
  rw [hD] at hss
  obtain ⟨S, hS⟩ : ∃ S, S = uMat s := ⟨_, rfl⟩
  obtain ⟨S', hS'⟩ : ∃ S' : Matrix (Fin n₀) (Fin n₀) ℂ,
      S' = (((s : (Matrix (Fin n₀) (Fin n₀) ℂ)ˣ)⁻¹ : (Matrix (Fin n₀) (Fin n₀) ℂ)ˣ) : Matrix (Fin n₀) (Fin n₀) ℂ) :=
    ⟨_, rfl⟩
  have hSS' : S * S' = 1 := by rw [hS, hS']; exact Units.mul_inv _
  have hS'S : S' * S = 1 := by rw [hS, hS']; exact Units.inv_mul _
  rw [← hS] at hsh hss
  have hsJ : Sᴴ * Jm ε₀ * S = Jm ε₀ := by rw [hS]; exact s.2
  rw [hsh] at hsJ
  have hSS'h : S * S'ᴴ = 1 := by
    have := congrArg conjTranspose hS'S
    simpa [conjTranspose_mul, hsh] using this
  have hS'h : S'ᴴ = S' := by
    calc S'ᴴ = S' * S * S'ᴴ := by rw [hS'S, Matrix.one_mul]
      _ = S' := by rw [Matrix.mul_assoc, hSS'h, Matrix.mul_one]
  have hJ₀S : Jm ε₀ * S = S' * Jm ε₀ := by
    calc Jm ε₀ * S = S' * S * Jm ε₀ * S := by rw [hS'S, Matrix.one_mul]
      _ = S' * (S * Jm ε₀ * S) := by simp only [Matrix.mul_assoc]
      _ = S' * Jm ε₀ := by rw [hsJ]
  have hBC : ∀ i, (B i)ᴴ * C = 0 := by
    intro i
    ext c d
    have := congrFun (congrFun hPC ⟨i, c⟩) d
    rw [hPe] at this
    simpa using this
  refine ⟨C * S', s, fun k => (B k)ᴴ * A₀, ?_, ?_⟩
  · refine ⟨h1, h2, h3, ?_, ?_, ?_, ?_⟩
    · intro i
      rw [← Matrix.mul_assoc, hBC i, Matrix.zero_mul]
    · calc (C * S')ᴴ * (C * S') = S'ᴴ * ((Cᴴ * C) * S') := by
            simp only [conjTranspose_mul, Matrix.mul_assoc]
        _ = 1 := by
            rw [hS'h, ← hss, Matrix.mul_assoc, hSS', Matrix.mul_one, hS'S]
    · calc Jm ε * (C * S') = C * (Jm ε₀ * (Cᴴ * C)) * S' := by
            rw [← Matrix.mul_assoc, hJC]
        _ = C * (Jm ε₀ * S) * (S * S') := by
            rw [← hss]; simp only [Matrix.mul_assoc]
        _ = C * S' * Jm ε₀ := by
            rw [hSS', Matrix.mul_one, hJ₀S, Matrix.mul_assoc]
    · have hsum : ∑ i, B i * (B i)ᴴ = P * Pᴴ := by
        have := hPPX (1 : Matrix (Fin n) (Fin n) ℂ)
        simpa using this.symm
      have hsumJ : ∑ i, Jm ε * B i * (B i)ᴴ * Jm ε = Jm ε * (P * Pᴴ) * Jm ε := by
        rw [← hsum, Finset.mul_sum, Finset.sum_mul]
        simp only [Matrix.mul_assoc]
      have hlast : C * S' * (C * S')ᴴ = C * Jm ε₀ * Cᴴ * Jm ε := by
        calc C * S' * (C * S')ᴴ = C * (S' * S') * Cᴴ := by
              simp only [conjTranspose_mul, hS'h, Matrix.mul_assoc]
          _ = C * (Jm ε₀ * (S * (S * Jm ε₀))) * Cᴴ := by
              congr 2
              symm
              rw [← Matrix.mul_assoc (Jm ε₀) S, hJ₀S, Matrix.mul_assoc S', ← Matrix.mul_assoc (Jm ε₀) S, hJ₀S,
                Matrix.mul_assoc S', hJ₀J₀, Matrix.mul_one]
          _ = C * Jm ε₀ * Cᴴ * Jm ε := by
              rw [Matrix.mul_assoc (C * Jm ε₀), hCJ, ← Matrix.mul_assoc Cᴴ C, ← hss]
              simp only [Matrix.mul_assoc]
      rw [hsum, hsumJ, hlast]
      exact hres
  · have hsum : ∑ k, B k * ((B k)ᴴ * A₀) = P * (Pᴴ * A₀) := (hPPX A₀).symm
    simp only [hsum, Matrix.mul_assoc]
    rw [← hS, hS'S, Matrix.mul_one, hC, sub_add_cancel]

end GlobalTheory.FrameCompletion
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsTotallyIsotropicDualFamilyInLattice
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

namespace GlobalTheory.IsotropicDual

section Herm

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
  [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Model F E} {V : Type}
  [AddCommGroup V] [Module E V] (H : HermSp M V)

theorem h_sum_left {ι : Type} (s : Finset ι) (v : ι → V) (y : V) :
    H.h (∑ i ∈ s, v i) y = ∑ i ∈ s, H.h (v i) y := by
  let φ : V →+ E := AddMonoidHom.mk' (fun x => H.h x y) (fun x x' => H.h_add_left x x' y)
  exact map_sum φ v s

theorem h_add_right (x y y' : V) : H.h x (y + y') = H.h x y + H.h x y' := by
  rw [H.h_herm (y + y') x, H.h_add_left, map_add, ← H.h_herm y x, ← H.h_herm y' x]

theorem h_smul_right (a : E) (x y : V) : H.h x (a • y) = M.L.cj a * H.h x y := by
  rw [H.h_herm (a • y) x, H.h_smul_left, map_mul, ← H.h_herm y x]

theorem h_sum_right {ι : Type} (s : Finset ι) (x : V) (v : ι → V) :
    H.h x (∑ i ∈ s, v i) = ∑ i ∈ s, H.h x (v i) := by
  rw [H.h_herm (∑ i ∈ s, v i) x, h_sum_left, map_sum]
  exact Finset.sum_congr rfl fun i _ => (H.h_herm (v i) x).symm

end Herm

theorem isotropic_dual : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ) (Fr : FrameD H r) (Λ : Submodule M.L.O V), H.IsSelfDual Λ → H.IsFrame Λ r Fr.f Fr.T → ∀ y : Fin r → V, (∀ a, y a ∈ Λ) → (∀ a b, H.h (y a) (Fr.f b) = if b = a.castSucc then 1 else 0) → ∃ y' : Fin r → V, (∀ a, y' a ∈ Λ) ∧ (∀ a b, H.h (y' a) (Fr.f b) = if b = a.castSucc then 1 else 0) ∧ ∀ a b, H.h (y' a) (y' b) = 0 := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r Fr Λ hSD hFr y hy hyf
  letI := hM.loc
  haveI := hM.char0
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨htr, -, -, -, hmem, -⟩ := GlobalTheory.UnramOrder.order_facts M.L ϖ hϖ
  have hint : ∀ a b, H.h (y a) (y b) ∈ M.L.O := fun a b => (hSD.2.2 (y a)).1 (hy a) (y b) (hy b)
  have hdiag : ∀ a, ∃ x ∈ M.L.O, x + M.L.cj x = -H.h (y a) (y a) := by
    intro a
    obtain ⟨c, hc⟩ := (M.L.cj_fix (H.h (y a) (y a))).1 (H.h_herm (y a) (y a)).symm
    have hc' : c ∈ 𝒪[F] := (hmem c).1 (hc ▸ hint a a)
    obtain ⟨x, hx, hxe⟩ := htr (-⟨c, hc'⟩)
    refine ⟨x, hx, ?_⟩
    rw [hxe, ← hc]
    simp
  choose x hxO hxe using hdiag
  obtain ⟨m, hmO, hm⟩ : ∃ m : Fin r → Fin r → E, (∀ a k, m a k ∈ M.L.O) ∧
      ∀ a b, m a b + M.L.cj (m b a) = -H.h (y a) (y b) := by
    refine ⟨fun a k => if a < k then -H.h (y a) (y k) else if a = k then x a else 0, ?_, ?_⟩
    · intro a k
      dsimp only
      split_ifs
      · exact M.L.O.neg_mem (hint a k)
      · exact hxO a
      · exact M.L.O.zero_mem
    · intro a b
      dsimp only
      rcases lt_trichotomy a b with h | rfl | h
      · rw [if_pos h, if_neg (not_lt.2 h.le), if_neg h.ne', map_zero, add_zero]
      · rw [if_neg (lt_irrefl a), if_pos rfl]
        exact hxe a
      · rw [if_neg (not_lt.2 h.le), if_neg h.ne', if_pos h, map_neg, ← H.h_herm (y b) (y a),
          zero_add]
  have he : ∀ k : Fin r, Fr.f k.castSucc ∈ Λ := fun k => hFr.1.1 k.castSucc
  have hEf : ∀ (k : Fin r) b, H.h (Fr.f k.castSucc) (Fr.f b) = 0 := fun k b =>
    hFr.2.1 _ _ (Or.inl (Fin.castSucc_lt_last k).ne)
  have hyE : ∀ a k : Fin r, H.h (y a) (Fr.f k.castSucc) = if k = a then 1 else 0 := by
    intro a k
    rw [hyf a k.castSucc]
    simp only [Fin.castSucc_inj]
  have hEy : ∀ k b : Fin r, H.h (Fr.f k.castSucc) (y b) = if k = b then 1 else 0 := by
    intro k b
    rw [H.h_herm (y b) (Fr.f k.castSucc), hyE]
    split_ifs <;> simp
  refine ⟨fun a => y a + ∑ k, m a k • Fr.f k.castSucc, fun a => ?_, fun a b => ?_, fun a b => ?_⟩
  · refine Λ.add_mem (hy a) (Λ.sum_mem fun k _ => ?_)
    exact Λ.smul_mem ⟨m a k, hmO a k⟩ (he k)
  · simp only [H.h_add_left, h_sum_left, H.h_smul_left, hEf, mul_zero, Finset.sum_const_zero,
      add_zero, hyf]
  · simp only [H.h_add_left, h_add_right, h_sum_left, h_sum_right, H.h_smul_left, h_smul_right,
      hyE, hEy, hEf, mul_zero, mul_ite, mul_one, Finset.sum_const_zero, add_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    linear_combination hm a b

end GlobalTheory.IsotropicDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamPSizesRecord
section
open Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory

theorem sizes_record_at {D : D7} (L : SizeData₂ D) (h : SizesAt L) (Cs : ℝ) (hCs : 5 ≤ Cs)
    (hx : 16 ≤ L.sc.x) (j : Fin 2) :
    Real.exp (8 * L.sc.x ^ L.sc.eps) ≤ (D.host.g j : ℝ) ∧ L.sc.x ^ 2 ≤ (D.R.f : ℝ) ∧
      (D.R.f : ℝ) ≤ L.sc.x ^ Cs ∧ (D.R.m : ℝ) ≤ L.sc.x ^ Cs ∧ 100 ≤ D.R.r ∧
      (D.R.r : ℝ) ≤ L.sc.x ^ Cs ∧
      Real.exp (L.sc.x ^ (L.sc.ez / 6)) ≤ ((min D.host.q D.host.d : ℕ) : ℝ) := by
  obtain ⟨hN, -, hK, -, -, -, hQ, -, -, -, -, -, -, -, -, -, -, -, -, -, hG, -⟩ := h
  have hx1 := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have he0 := L.sc.eps_pos
  have he1 := L.sc.eps_lt
  have hmk := D.R.m_add_three_le_k
  have hm2 := D.R.two_le_m
  have hfk : D.R.f ≤ D.R.k := D.R.f_le_k
  have hk1 : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hkb : (D.R.k : ℝ) ≤ L.sc.x ^ (19 / 4 : ℝ) := by
    refine hK.2.trans (Real.rpow_le_rpow_of_exponent_le hx1.le ?_)
    unfold szTh
    linarith
  have h2 : (2 : ℝ) ≤ L.sc.x ^ (1 / 4 : ℝ) := by
    have e : (2 : ℝ) = (16 : ℝ) ^ (1 / 4 : ℝ) := by
      rw [show (16 : ℝ) = 2 ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [e]
    exact Real.rpow_le_rpow (by norm_num) hx (by norm_num)
  have h2k : 2 * (D.R.k : ℝ) ≤ L.sc.x ^ Cs := by
    calc 2 * (D.R.k : ℝ) ≤ L.sc.x ^ (1 / 4 : ℝ) * L.sc.x ^ (19 / 4 : ℝ) :=
          mul_le_mul h2 hkb (by linarith) (by linarith)
      _ = L.sc.x ^ (5 : ℝ) := by rw [← Real.rpow_add hx0]; norm_num
      _ ≤ L.sc.x ^ Cs := Real.rpow_le_rpow_of_exponent_le hx1.le hCs
  have hn : L.sc.x ^ 2 ≤ (D.R.n : ℝ) := by
    refine le_trans ?_ hN.1
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hx1.le
    unfold szTh
    push_cast
    linarith
  have hf : L.sc.x ^ 2 ≤ (D.R.f : ℝ) := by
    refine hn.trans ?_
    exact_mod_cast (by unfold Ranks.f; omega : D.R.n ≤ D.R.f)
  have hfk' : (D.R.f : ℝ) ≤ D.R.k := by exact_mod_cast hfk
  have hmk' : (D.R.m : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : D.R.m ≤ D.R.k)
  have hr : (D.R.r : ℝ) ≤ 2 * (D.R.k : ℝ) := by
    exact_mod_cast (by unfold Ranks.r; omega : D.R.r ≤ 2 * D.R.k)
  have hf100 : 100 ≤ D.R.f := by
    have : (100 : ℝ) ≤ D.R.f := by nlinarith
    exact_mod_cast this
  refine ⟨?_, hf, by linarith, by linarith, by unfold Ranks.r; omega, by linarith, ?_⟩
  · refine le_trans ?_ (hG j j).1
    have e : Real.exp (8 * L.sc.x ^ L.sc.eps) = L.sc.b ^ 8 := by
      unfold Scale.b Scale.L
      rw [← Real.exp_nat_mul]
      norm_num
    have hb : 0 < L.sc.b := Real.exp_pos _
    rw [e]
    exact pow_le_pow_left₀ hb.le (le_mul_of_one_le_left hb.le hk1) 8
  · have hq : (0 : ℝ) < D.host.q := by
      have := D.host.qd_big.1
      exact_mod_cast (by omega : 0 < D.host.q)
    have hd : (0 : ℝ) < D.host.d := by
      have := D.host.qd_big.2
      exact_mod_cast (by omega : 0 < D.host.d)
    rw [Nat.cast_min]
    refine le_min ((Real.le_log_iff_exp_le hq).1 hQ.1) ((Real.le_log_iff_exp_le hd).1 ?_)
    refine le_trans (Real.rpow_le_rpow_of_exponent_le hx1.le ?_) hQ.2.2.2.1
    have := L.sc.ez_pos
    linarith

theorem family_eventually_size_bounds : ∀ (eps : ℝ) (Fm : FamP eps) (Cs : ℝ), 5 ≤ Cs → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) (j : Fin 2), Real.exp (8 * x ^ eps) ≤ ((Fm.D x i).host.g j : ℝ) ∧ x ^ 2 ≤ ((Fm.D x i).R.f : ℝ) ∧ ((Fm.D x i).R.f : ℝ) ≤ x ^ Cs ∧ ((Fm.D x i).R.m : ℝ) ≤ x ^ Cs ∧ 100 ≤ (Fm.D x i).R.r ∧ ((Fm.D x i).R.r : ℝ) ≤ x ^ Cs ∧ Real.exp (x ^ (Fm.ez / 6)) ≤ ((min (Fm.D x i).host.q (Fm.D x i).host.d : ℕ) : ℝ) := by
  intro eps Fm Cs hCs
  refine ⟨max 16 (Fm.x1 + 1), fun x hx i j => ?_⟩
  have h16 : 16 ≤ x := (le_max_left _ _).trans hx
  have hx1 : Fm.x1 < x := by linarith [(le_max_right _ _).trans hx]
  have := sizes_record_at (Fm.L x i) (Fm.sizes x hx1 i) Cs hCs (by rw [Fm.L_x x i hx1]; exact h16) j
  rw [Fm.L_x x i hx1, Fm.L_eps x i, Fm.L_ez x i] at this
  exact this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GapBigOfComparison
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.SplitPrimeNormLemmas

namespace GlobalTheory.GapAtRealPlaces

theorem gapBig_of_comparison (h : PI.ScGapBig.ScGapBig) (D : Formalism.BasicNotions.D7) :
    Formalism.L2.SG.SplitPrimeNormLemmas.GapBigOfGapHyp D := by
  intro hm hG τ

  have hr : PI.ScGapBig.rk48 D.R.k D.R.rS = D.R.r := by
    simp only [PI.ScGapBig.rk48, Formalism.BasicNotions.Ranks.r]
    omega

  have hgaps : ∀ (j : Fin (2 * D.R.rS + 2)) (hj : j.val + 1 < 2 * D.R.rS + 2),
      16 * (PI.ScGapBig.rk48 D.R.k D.R.rS : ℝ) ^ 19 ≤
        ((D.hc τ).b (Fin.cast hm.symm ⟨j.val + 1, hj⟩) : ℝ) - ((D.hc τ).b (Fin.cast hm.symm j) : ℝ) := by
    intro j hj
    have hlt : (Fin.cast hm.symm j).val + 1 < D.R.m := by
      rw [Fin.val_cast]
      omega
    have key := hG.2 τ (Fin.cast hm.symm j) hlt
    have hidx : (⟨(Fin.cast hm.symm j).val + 1, hlt⟩ : Fin D.R.m) = Fin.cast hm.symm ⟨j.val + 1, hj⟩ :=
      Fin.ext rfl
    rw [hidx] at key
    rw [hr]
    exact_mod_cast key
  obtain ⟨t, hto, ht5, ht1801, hgap⟩ :=
    h D.R.k D.R.rS (fun j => ((D.hc τ).b (Fin.cast hm.symm j) : ℝ)) (hr ▸ hG.1) hgaps
  exact ⟨t, hto, ht5, ht1801, hgap⟩

theorem gapBigOfGapHyp : ∀ D : D7, GapBigOfGapHyp D := by
  intro D
  exact gapBig_of_comparison scGapBig D

end GlobalTheory.GapAtRealPlaces
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HighestWeightDerivativeSumZeroStatement
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.highest_weight_derivative_sum_zero : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ V) (lam : Fin n → ℝ) (u : V), IsHCParam lam → IsDS ε lam σ → IsDer ε σ V E → KHighest ε E (LamOf ε lam) u → FiniteDimensional ℂ (kSpan ε E u) → ∀ G ∈ Vminus ε E (LamOf ε lam) u, ∑ a, ∑ b, E a b (at1 G a b) = 0 := by
  first | exact @GlobalTheory.Jet.Schmid.mul_vminus_eq_zero | exact GlobalTheory.Jet.Schmid.mul_vminus_eq_zero | (intros; apply GlobalTheory.Jet.Schmid.mul_vminus_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImportsBisTail
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.OrthoMass

theorem main : ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K → ∃ ms : ℕ → ℝ, (∀ n, 0 < ms n) ∧ ∀ (n : ℕ) (W : Type) [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (h : W →ₗ⋆[K] W →ₗ[K] K) (I : Submodule (𝓞 K) W), h.IsSymm → Formalism.HermitianLatticesTheory.IsOrthoLattice h I n → Formalism.HermitianLatticesTheory.mass h I = ms n := by
  intro K _ _ _ hK
  refine ⟨fun n => Formalism.HermitianLatticesTheory.mass (Formalism.MainNotions.StandardLattice.stdForm K n) (Formalism.MainNotions.StandardLattice.stdLat K n), fun n => ?_, ?_⟩
  · show 0 < Formalism.HermitianLatticesTheory.mass (Formalism.MainNotions.StandardLattice.stdForm K n) (Formalism.MainNotions.StandardLattice.stdLat K n)
    rw [Formalism.MainNotions.StandardLattice.standard_form_eq_telescope_form, Formalism.MainNotions.StandardLattice.standard_lattice_eq_telescope_lattice]
    exact Formalism.HermitianLatticesTheory.massTelescope_std_pos K hK n
  · intro n W _ _ _ _ h I _ ho
    exact Formalism.MainNotions.StandardLattice.mass_ortho K hK n W h I ho

end GlobalTheory.OrthoMass
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatDetHMapInjectiveIsometryStatement
section
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latDetH_map_injective_isometry : ∀ (K U V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup U] [Module K U] [Module (𝓞 K) U] [IsScalarTower (𝓞 K) K U] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (hU : U →ₗ⋆[K] U →ₗ[K] K) (hV : V →ₗ⋆[K] V →ₗ[K] K) (i : U →ₗ[K] V), Function.Injective i → (∀ x y, hV (i x) (i y) = hU x y) → ∀ N : Submodule (𝓞 K) U, latDetH hV (N.map (i.restrictScalars (𝓞 K))) = latDetH hU N := by
  first | exact @GlobalTheory.LoopC.DetMap.latDetH_map | exact GlobalTheory.LoopC.DetMap.latDetH_map | (intros; apply GlobalTheory.LoopC.DetMap.latDetH_map <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeftQuotientCovolumeWithDensityDetNormSqStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leftQuotientCovolume_withDensity_detNormSq : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ (j : ℕ), 1 ≤ j → ∀ Λ : Submodule (𝓞 E) (Fin j → E), Submodule.IsLattice E Λ → ∀ F : ℝ → ENNReal, Measurable F → covol (autGL E j Λ) ((haarGL E j).withDensity fun x => F (detNorm E j x)) {x | 0 < detNorm E j x} = covol (autGL E j Λ) (haarGL E j) {x | 1 ≤ detNorm E j x ∧ detNorm E j x < Real.exp 1} * ∫⁻ t in Set.Ioi (0 : ℝ), F t / ENNReal.ofReal t := by
  first | exact @GlobalTheory.DetSlab.covol_withDensity_detNorm | exact GlobalTheory.DetSlab.covol_withDensity_detNorm | (intros; apply GlobalTheory.DetSlab.covol_withDensity_detNorm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeviChartMapHaarCarriedInvariantStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_chart_map_haar_carried_invariant : ∀ (n n₀ a : ℕ) (j : Fin a → ℕ) (ε : Fin n → Bool) (ε₀ : Fin n₀ → Bool) (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (B₀ : Matrix (Fin n) (Fin n₀) ℂ), IsFrame ε ε₀ B B₀ → ∀ W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ), SpansFlag B W → ∀ θ : (∀ i, Fin (j i) → Fin (j i) → ℂ) × Formalism.REAL.UJ ε₀ → Formalism.REAL.UJ ε, Measurable θ → (∀ z, (∀ i, (Matrix.of (z.1 i)).det ≠ 0) → uMat (θ z) = lev ε B B₀ (fun i => Matrix.of (z.1 i)) (uMat z.2)) → ∀ c : ℝ, (((Measure.pi fun i => ENNReal.ofReal (2 ^ (j i ^ 2)) • haarLoc (j i)).prod (ENNReal.ofReal c • Formalism.REAL.muG ε₀)).map θ) (flagM ε W)ᶜ = 0 ∧ ∀ s ∈ flagM ε W, (((Measure.pi fun i => ENNReal.ofReal (2 ^ (j i ^ 2)) • haarLoc (j i)).prod (ENNReal.ofReal c • Formalism.REAL.muG ε₀)).map θ).map (fun g => s * g) = (((Measure.pi fun i => ENNReal.ofReal (2 ^ (j i ^ 2)) • haarLoc (j i)).prod (ENNReal.ofReal c • Formalism.REAL.muG ε₀)).map θ) := by
  first | exact @GlobalTheory.LeviIso.map_chart_carried_and_invariant | exact GlobalTheory.LeviIso.map_chart_carried_and_invariant | (intros; apply GlobalTheory.LeviIso.map_chart_carried_and_invariant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableTranslatedLatticeFunctionsStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurable_translatedLattice_functions : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ j : ℕ, ∀ (w : ℝ → ENNReal) (Φ : VecInf E j → ENNReal), Measurable w → Measurable Φ → ∀ Λ : Submodule (𝓞 E) (Fin j → E), Submodule.IsLattice E Λ → Measurable (fun g : MatInf E j => {g | 0 < detNorm E j g}.indicator (fun g => w (covAt E j (latAt E j Λ g))) g) ∧ Measurable (fun g : MatInf E j => {g | 0 < detNorm E j g}.indicator (fun g => ∑' x : {x : VecInf E j // x ∈ latAt E j Λ g ∧ x ≠ 0}, Φ x.1) g) ∧ Measurable (fun g : MatInf E j => {g | 0 < detNorm E j g}.indicator (fun g => ∑' x : {x : VecInf E j // x ∈ dualAt E j (latAt E j Λ g) ∧ x ≠ 0}, Φ x.1) g) := by
  first | exact @GlobalTheory.LatMeasurable.measurable_latFun | exact GlobalTheory.LatMeasurable.measurable_latFun | (intros; apply GlobalTheory.LatMeasurable.measurable_latFun <;> assumption)
end

