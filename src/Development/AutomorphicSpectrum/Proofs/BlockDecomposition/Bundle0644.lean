import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0597
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0613
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryMovingUnitVector
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStage

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypUnit

section Form

variable {K : Type} [CommRing K] {M : ℕ}

theorem fin_three {P : Fin (M + 2) → Prop} (h0 : P 0) (h1 : P 1) (h2 : ∀ i : Fin M, P i.succ.succ)
    (i : Fin (M + 2)) : P i :=
  Fin.cases h0 (fun i => Fin.cases h1 (fun i => h2 i) i) i

theorem sum_three (f : Fin (M + 2) → K) : ∑ i, f i = f 0 + f 1 + ∑ i : Fin M, f i.succ.succ := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  exact (add_assoc _ _ _).symm

variable (s : K →+* K) (A : Matrix (Fin M) (Fin M) K)

theorem hform_hypOne (x y : Fin (M + 2) → K) :
    hform s (hypOne A) x y = s (x 0) * y 1 + s (x 1) * y 0 + hform s A (tailH x) (tailH y) := by
  simp only [hform, sum_three, hypOne_zero_zero, hypOne_zero_one, hypOne_one_zero, hypOne_one_one,
    hypOne_zero_rest, hypOne_one_rest, hypOne_rest_zero, hypOne_rest_one, hypOne_rest_rest, tailH]
  simp

theorem hform_add_right (x y y' : Fin M → K) :
    hform s A x (y + y') = hform s A x y + hform s A x y' := by
  simp only [hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hform_add_left (x x' y : Fin M → K) :
    hform s A (x + x') y = hform s A x y + hform s A x' y := by
  simp only [hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem hform_smul_right (c : K) (x y : Fin M → K) :
    hform s A x (c • y) = c * hform s A x y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hform_smul_left (c : K) (x y : Fin M → K) :
    hform s A (c • x) y = s c * hform s A x y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hform_conj (hs : ∀ e, s (s e) = e) (hA : ∀ i j, s (A j i) = A i j) (x y : Fin M → K) :
    s (hform s A x y) = hform s A y x := by
  simp only [hform, map_sum, map_mul, hs]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hA]; ring

def cvK (c : K) (x v : Fin (M + 2) → K) : Fin (M + 2) → K :=
  vH (x 0 * v 0)
    (v 0 * x 1 + Ring.inverse (s (x 0)) * (v 1 - c * v 0 - hform s A (tailH x) (tailH v)))
    (fun i => v 0 * x i.succ.succ + v i.succ.succ)

def cvL (c : K) (x : Fin (M + 2) → K) : (Fin (M + 2) → K) →ₗ[K] (Fin (M + 2) → K) where
  toFun := cvK s A c x
  map_add' u v := by
    have ht : tailH (u + v) = tailH u + tailH v := rfl
    funext i
    refine fin_three (P := fun i => cvK s A c x (u + v) i = (cvK s A c x u + cvK s A c x v) i) ?_ ?_ ?_ i
    · show x 0 * (u 0 + v 0) = x 0 * u 0 + x 0 * v 0
      ring
    · show (u 0 + v 0) * x 1 + Ring.inverse (s (x 0)) *
          (u 1 + v 1 - c * (u 0 + v 0) - hform s A (tailH x) (tailH (u + v))) =
        (u 0 * x 1 + Ring.inverse (s (x 0)) * (u 1 - c * u 0 - hform s A (tailH x) (tailH u))) +
        (v 0 * x 1 + Ring.inverse (s (x 0)) * (v 1 - c * v 0 - hform s A (tailH x) (tailH v)))
      rw [ht, hform_add_right]
      ring
    · intro i
      show (u 0 + v 0) * x i.succ.succ + (u i.succ.succ + v i.succ.succ) =
        (u 0 * x i.succ.succ + u i.succ.succ) + (v 0 * x i.succ.succ + v i.succ.succ)
      ring
  map_smul' e v := by
    have ht : tailH (e • v) = e • tailH v := rfl
    funext i
    refine fin_three (P := fun i => cvK s A c x (e • v) i = (e • cvK s A c x v) i) ?_ ?_ ?_ i
    · show x 0 * (e * v 0) = e * (x 0 * v 0)
      ring
    · show (e * v 0) * x 1 + Ring.inverse (s (x 0)) *
          (e * v 1 - c * (e * v 0) - hform s A (tailH x) (tailH (e • v))) =
        e * (v 0 * x 1 + Ring.inverse (s (x 0)) * (v 1 - c * v 0 - hform s A (tailH x) (tailH v)))
      rw [ht, hform_smul_right]
      ring
    · intro i
      show (e * v 0) * x i.succ.succ + e * v i.succ.succ = e * (v 0 * x i.succ.succ + v i.succ.succ)
      ring

theorem hform_cvK (hs : ∀ e, s (s e) = e) (hA : ∀ i j, s (A j i) = A i j) (c : K)
    (x : Fin (M + 2) → K) (hx : IsUnit (x 0)) (hc : c + s c = hform s (hypOne A) x x)
    (u v : Fin (M + 2) → K) :
    hform s (hypOne A) (cvK s A c x u) (cvK s A c x v) = hform s (hypOne A) u v := by
  have hsa : IsUnit (s (x 0)) := hx.map s
  have hab : s (x 0) * Ring.inverse (s (x 0)) = 1 := Ring.mul_inverse_cancel _ hsa
  have hba : s (Ring.inverse (s (x 0))) * x 0 = 1 := by
    have := congrArg s hab
    rwa [map_mul, hs, map_one, mul_comm] at this
  have htail : ∀ w : Fin (M + 2) → K, tailH (cvK s A c x w) = w 0 • tailH x + tailH w := fun _ => rfl
  rw [hform_hypOne, hform_hypOne s A u v, htail, htail, hform_add_left, hform_add_right,
    hform_add_right, hform_smul_left, hform_smul_left, hform_smul_right, hform_smul_right]
  rw [hform_hypOne] at hc
  have hconj := hform_conj s A hs hA (tailH x) (tailH u)
  have e0 : ∀ w : Fin (M + 2) → K, cvK s A c x w 0 = x 0 * w 0 := fun _ => rfl
  have e1 : ∀ w : Fin (M + 2) → K, cvK s A c x w 1 = w 0 * x 1 + Ring.inverse (s (x 0)) *
      (w 1 - c * w 0 - hform s A (tailH x) (tailH w)) := fun _ => rfl
  rw [e0, e0, e1, e1]
  simp only [map_add, map_sub, map_mul, hconj]
  linear_combination (s (u 0) * (v 1 - c * v 0 - hform s A (tailH x) (tailH v))) * hab +
    (v 0 * (s (u 1) - s c * s (u 0) - hform s A (tailH u) (tailH x))) * hba -
    (s (u 0) * v 0) * hc

theorem cvK_surjective (c : K) (x : Fin (M + 2) → K) (hx : IsUnit (x 0)) (hs : IsUnit (s (x 0))) :
    Function.Surjective (cvK s A c x) := by
  intro w
  have ha : x 0 * Ring.inverse (x 0) = 1 := Ring.mul_inverse_cancel _ hx
  have hb : Ring.inverse (s (x 0)) * s (x 0) = 1 := Ring.inverse_mul_cancel _ hs
  set α := Ring.inverse (x 0) * w 0 with hα
  set U : Fin M → K := fun i => w i.succ.succ - α * x i.succ.succ with hU
  refine ⟨vH α (s (x 0) * (w 1 - α * x 1) + c * α + hform s A (tailH x) U) U, ?_⟩
  funext i
  refine fin_three (P := fun i => cvK s A c x
    (vH α (s (x 0) * (w 1 - α * x 1) + c * α + hform s A (tailH x) U) U) i = w i) ?_ ?_ ?_ i
  · show x 0 * α = w 0
    rw [hα, ← mul_assoc, ha, one_mul]
  · show α * x 1 + Ring.inverse (s (x 0)) *
      (s (x 0) * (w 1 - α * x 1) + c * α + hform s A (tailH x) U - c * α - hform s A (tailH x) U) = w 1
    linear_combination (w 1 - α * x 1) * hb
  · intro i
    show α * x i.succ.succ + U i = w i.succ.succ
    rw [hU]
    ring

theorem cT_mul_apply (H C : Matrix (Fin M) (Fin M) K) (i j : Fin M) :
    (Formalism.UG.cT s C * H * C) i j = hform s H (fun k => C k i) (fun k => C k j) := by
  simp only [Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, hform,
    Finset.sum_mul]
  exact Finset.sum_comm

theorem hform_single (H : Matrix (Fin M) (Fin M) K) (i j : Fin M) :
    hform s H (Pi.single i 1) (Pi.single j 1) = H i j := by
  simp [hform, Pi.single_apply, apply_ite s]

theorem exists_unitary (hs : ∀ e, s (s e) = e) (hA : ∀ i j, s (A j i) = A i j) (c : K)
    (x : Fin (M + 2) → K) (hx : IsUnit (x 0)) (hc : c + s c = hform s (hypOne A) x x) :
    ∃ g : GL (Fin (M + 2)) K, g ∈ Formalism.UG.UJ s (hypOne A) ∧
      ∀ v, (g : Matrix (Fin (M + 2)) (Fin (M + 2)) K).mulVec v = cvK s A c x v := by
  set C := LinearMap.toMatrix' (cvL s A c x) with hC
  have hmul : ∀ v, C.mulVec v = cvK s A c x v := fun v => by
    rw [hC, LinearMap.toMatrix'_mulVec]
    rfl
  have hunit : IsUnit C := by
    rw [← Matrix.mulVec_surjective_iff_isUnit]
    intro w
    obtain ⟨v, hv⟩ := cvK_surjective s A c x hx (hx.map s) w
    exact ⟨v, (hmul v).trans hv⟩
  obtain ⟨g, hg⟩ := hunit
  refine ⟨g, ?_, fun v => by rw [hg, hmul]⟩
  show Formalism.UG.cT s (g : Matrix (Fin (M + 2)) (Fin (M + 2)) K) * hypOne A * g = hypOne A
  rw [hg]
  ext i j
  rw [cT_mul_apply]
  have hcol : ∀ k, (fun l => C l k) = cvK s A c x (Pi.single k 1) := fun k => by
    rw [← hmul, Matrix.mulVec_single_one]
    rfl
  rw [hcol, hcol, hform_cvK s A hs hA c x hx hc, hform_single]

end Form

section Tensor

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem sigR_inclR_apply (σ : E →ₐ[F] E) (e : E) :
    sigR R σ (inclR (F := F) R e) = inclR R (σ e) := by
  simp [sigR, inclR]

theorem JR_hypOne {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    JR R (hypOne J) = hypOne (JR (F := F) R J) := by
  ext i j
  refine fin_three (P := fun i => JR (F := F) R (hypOne J) i j = hypOne (JR (F := F) R J) i j) ?_ ?_ ?_ i
  · refine fin_three (P := fun j => JR (F := F) R (hypOne J) 0 j = hypOne (JR (F := F) R J) 0 j) ?_ ?_ ?_ j
    · simp [JR, hypOne_zero_zero]
    · simp [JR, hypOne_zero_one]
    · intro j; simp [JR, hypOne_zero_rest]
  · refine fin_three (P := fun j => JR (F := F) R (hypOne J) 1 j = hypOne (JR (F := F) R J) 1 j) ?_ ?_ ?_ j
    · simp [JR, hypOne_one_zero]
    · simp [JR, hypOne_one_one]
    · intro j; simp [JR, hypOne_one_rest]
  · intro i
    refine fin_three (P := fun j => JR (F := F) R (hypOne J) i.succ.succ j =
      hypOne (JR (F := F) R J) i.succ.succ j) ?_ ?_ ?_ j
    · simp [JR, hypOne_rest_zero]
    · simp [JR, hypOne_rest_one]
    · intro j; simp [JR, hypOne_rest_rest]

end Tensor

theorem cvec_unitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] (x : Fin (M + 2) → R ⊗[F] E), IsUnit (x 0) → ∃ g : HA R σ (hypOne J), ∀ v : Fin (M + 2) → R ⊗[F] E, ((HA.mat R σ (hypOne J) g : GL (Fin (M + 2)) (R ⊗[F] E)) : Matrix (Fin (M + 2)) (Fin (M + 2)) (R ⊗[F] E)).mulVec v = cvec R σ J x v := by
  intro F E _ _ _ _ _ σ hcm M J hJ R _ _ x hx
  have hinv := sig_invol σ hcm
  have hs : ∀ e, sigR R σ (sigR R σ e) = e := sigR_sigR R σ hinv
  have hA : ∀ i j, sigR R σ (JR (F := F) R J j i) = JR (F := F) R J i j := fun i j => by
    show sigR R σ (inclR R (J j i)) = inclR R (J i j)
    rw [sigR_inclR_apply, hJ.1]
  have ht : hR R σ (hypOne J) x x = hform (sigR R σ) (hypOne (JR (F := F) R J)) x x := by
    rw [hR, JR_hypOne]
  have htc : sigR R σ (hR R σ (hypOne J) x x) = hR R σ (hypOne J) x x := by
    rw [ht, hform_hypOne]
    simp only [map_add, map_mul, hs, hform_conj (sigR R σ) (JR (F := F) R J) hs hA]
    ring
  have hhalf : sigR R σ (halfR (F := F) (E := E) R) = halfR (F := F) (E := E) R := by
    rw [halfR, sigR_inclR_apply, AlgHom.commutes]
  have h2 : halfR (F := F) (E := E) R + halfR (F := F) (E := E) R = 1 := by
    rw [halfR, ← map_add, ← map_add]
    norm_num
  have hc : tHalf R σ J x + sigR R σ (tHalf R σ J x) =
      hform (sigR R σ) (hypOne (JR (F := F) R J)) x x := by
    rw [tHalf, map_mul, hhalf, htc, ← ht]
    linear_combination (hR R σ (hypOne J) x x) * h2
  obtain ⟨g, hg, hv⟩ := exists_unitary (sigR R σ) (JR (F := F) R J) hs hA (tHalf R σ J x) x hx hc
  refine ⟨⟨g, ?_⟩, hv⟩
  show g ∈ Formalism.UG.UJ (sigR R σ) (JR R (hypOne J))
  rw [JR_hypOne]
  exact hg

end GlobalTheory.CompanionTheory.WeilSiegel.HypUnit
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedWhittakerNewform
section
noncomputable section

open Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.GLnLocal (integralGL mem_integralGL_iff)
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.RankinSelberg

open Ad3 Ad3.R

def lowT {F : Type} [Field F] (a d : Fˣ) (z : F) : GL (Fin 2) F :=
  ⟨!![(a : F), 0; z, (d : F)], !![((a⁻¹ : Fˣ) : F), 0; -z * ((a⁻¹ : Fˣ) : F) * ((d⁻¹ : Fˣ) : F), ((d⁻¹ : Fˣ) : F)],
    by
      have ha := a.ne_zero
      have hd := d.ne_zero
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring,
    by
      have ha := a.ne_zero
      have hd := d.ne_zero
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring⟩

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem lowT_mem {a d : Fˣ} {z : F} (ha : (a : F) ∈ 𝒪[F]) (ha' : ((a⁻¹ : Fˣ) : F) ∈ 𝒪[F])
    (hd : (d : F) ∈ 𝒪[F]) (hd' : ((d⁻¹ : Fˣ) : F) ∈ 𝒪[F]) (hz : z ∈ 𝒪[F]) :
    lowT a d z ∈ integralGL F 2 := by
  have e1 : (lowT a d z : Matrix (Fin 2) (Fin 2) F) = !![(a : F), 0; z, (d : F)] := rfl
  have e2 : ((lowT a d z)⁻¹ : GL (Fin 2) F).val =
      !![((a⁻¹ : Fˣ) : F), 0; -z * ((a⁻¹ : Fˣ) : F) * ((d⁻¹ : Fˣ) : F), ((d⁻¹ : Fˣ) : F)] := rfl
  rw [mem_integralGL_iff]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [e1]
    fin_cases i <;> fin_cases j
    · exact ha
    · exact zero_mem _
    · exact hz
    · exact hd
  · rw [e2]
    fin_cases i <;> fin_cases j
    · exact ha'
    · exact zero_mem _
    · exact mul_mem (mul_mem (neg_mem hz) ha') hd'
    · exact hd'

private theorem mem_integers_iff_ord_nonneg' {x : F} (hx : x ≠ 0) : x ∈ 𝒪[F] ↔ 0 ≤ ord x := by
  rw [← normalizedValuation_le_one_iff, normalizedValuation_eq_exp_ord hx, ← WithZero.exp_zero,
    WithZero.exp_le_exp]
  omega

theorem le_ord_sub_one {n : ℕ} (hn : 1 ≤ n) {u : Fˣ} (hu : u ∈ unitFiltrationUnits F (n - 1))
    (h1 : (u : F) - 1 ≠ 0) : (n : ℤ) - 1 ≤ ord ((u : F) - 1) := by
  obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hu
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨a, ha⟩ := exists_sub_one_eq_mul hϖ (⟨v, hv⟩ : unitFiltration F (n - 1))
  have hF : ((unitsIncl F v : Fˣ) : F) - 1 = (ϖ : F) ^ (n - 1) * (a : F) := by
    rw [coe_unitsIncl]
    have := congrArg Subtype.val ha
    exact_mod_cast this
  have hϖ0 : (ϖ : F) ≠ 0 := by
    intro h
    apply hϖ.ne_zero
    exact Subtype.ext h
  have ha0 : (a : F) ≠ 0 := by
    intro h
    apply h1
    rw [hF, h, mul_zero]
  have hpow : ∀ k : ℕ, ord ((ϖ : F) ^ k) = k := by
    intro k
    induction k with
    | zero => simp [GroundTheory.LocalField.ord]
    | succ k ih =>
      rw [pow_succ, ord_mul (pow_ne_zero _ hϖ0) hϖ0, ih, ord_uniformizer hϖ]
      push_cast
      ring
  have ha' : 0 ≤ ord (a : F) := (mem_integers_iff_ord_nonneg' ha0).mp a.2
  rw [hF, ord_mul (pow_ne_zero _ hϖ0) ha0, hpow]
  push_cast [Nat.cast_sub hn]
  linarith

theorem unit_mem_integers {u : Fˣ} (hu : ord (u : F) = 0) : (u : F) ∈ 𝒪[F] := by
  exact (mem_integers_iff_ord_nonneg' u.ne_zero).mpr hu.ge

theorem ne_zero_of_ord {y : F} (hy : ord y = -1) : y ≠ 0 := by
  rintro rfl
  simp [GroundTheory.LocalField.ord] at hy

theorem entry_mem {n : ℕ} (hn : 1 ≤ n) {u : Fˣ} (hu : u ∈ unitFiltrationUnits F (n - 1))
    (h1 : (u : F) - 1 ≠ 0) {y : F} (hy : ord y = -1) :
    (((unifUnit F)⁻¹ ^ n : Fˣ) : F) * (((u : F) - 1) * y⁻¹) ∈ 𝒪[F] ∧ ((u : F) - 1) * y⁻¹ ∈ 𝒪[F] := by
  have hy0 := ne_zero_of_ord hy
  have h0 : ((u : F) - 1) * y⁻¹ ≠ 0 := mul_ne_zero h1 (inv_ne_zero hy0)
  have hyi : ord y⁻¹ = 1 := by
    have := ord_units_inv (Units.mk0 y hy0)
    simpa [hy] using this
  have hz : (n : ℤ) ≤ ord (((u : F) - 1) * y⁻¹) := by
    rw [ord_mul h1 (inv_ne_zero hy0), hyi]
    linarith [le_ord_sub_one hn hu h1]
  have hpi : ord (((unifUnit F)⁻¹ ^ n : Fˣ) : F) = -n := by
    rw [← zpow_natCast, ord_units_zpow, ord_units_inv, ord_unifUnit]
    ring
  have hn0 : (0 : ℤ) ≤ n := by positivity
  constructor
  · rw [mem_integers_iff_ord_nonneg' (mul_ne_zero (Units.ne_zero _) h0), ord_mul (Units.ne_zero _) h0, hpi]
    linarith
  · rw [mem_integers_iff_ord_nonneg' h0]
    linarith

theorem lower_torus_conjugate_unipotent {u : Fˣ} {y : F} (hy : y ≠ 0) :
    lowT u 1 (((u : F) - 1) * y⁻¹) * uni2 y = uni2 y * lowT 1 u (((u : F) - 1) * y⁻¹) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowT, Ad3.uni2, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

theorem unipotent_conj_moves_char : Ad3.R.U2 := by
  unfold Ad3.R.U2 Ad3.R.ForF
  intro F _ _ _ _ _ _ ψ _ ω _ hc y hy
  set n := quasiCharConductor ω with hn_def
  have hn : 1 ≤ n := hc
  have hnot : ¬ (unitFiltrationUnits F (n - 1) ≤ ω.ker) := by
    intro hle
    have : n ≤ n - 1 := Nat.sInf_le hle
    omega
  obtain ⟨u, hu, hωu⟩ := SetLike.not_le_iff_exists.mp hnot
  rw [MonoidHom.mem_ker] at hωu
  have h1 : (u : F) - 1 ≠ 0 := by
    intro h
    apply hωu
    have : u = 1 := Units.ext (sub_eq_zero.mp h)
    rw [this, map_one]
  have hord : ord (u : F) = 0 := by
    obtain ⟨v, -, hv⟩ := Subgroup.mem_map.mp hu
    rw [← hv, coe_unitsIncl]
    exact ord_unit v
  have hu1 : (u : F) ∈ 𝒪[F] := unit_mem_integers hord
  have hu2 : ((u⁻¹ : Fˣ) : F) ∈ 𝒪[F] := unit_mem_integers (by rw [ord_units_inv, hord, neg_zero])
  have h11 : ((1 : Fˣ) : F) ∈ 𝒪[F] := by
    rw [Units.val_one]
    exact one_mem _
  have h12 : (((1 : Fˣ)⁻¹ : Fˣ) : F) ∈ 𝒪[F] := by
    rw [inv_one, Units.val_one]
    exact one_mem _
  have he := entry_mem hn hu h1 hy
  refine ⟨lowT u 1 (((u : F) - 1) * y⁻¹), 1, lowT 1 u (((u : F) - 1) * y⁻¹), u, ?_, ?_,
    lower_torus_conjugate_unipotent (ne_zero_of_ord hy), ?_⟩
  · unfold Ad3.R.GammaZeroLevelMembership
    exact ⟨lowT_mem hu1 hu2 h11 h12 he.2, he.1, rfl⟩
  · unfold Ad3.R.GammaZeroLevelMembership
    exact ⟨lowT_mem h11 h12 hu1 hu2 he.2, he.1, rfl⟩
  · rw [map_one]
    exact fun h => hωu h.symm

end GlobalTheory.CompanionTheory.RankinSelberg
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilRepresentationThetaIntegral
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.WzFib

theorem inner_jn {D : D7} {n r t : ℕ} (hn : r + t = n) (V : HSp D) (x : Mx D V.rank r) :
    GlobalTheory.StdUnn.inner V (jn hn x (0 : Mx D V.rank t)) (jn hn x (0 : Mx D V.rank t)) =
      bl hn (GlobalTheory.StdUnn.inner V x x) 0 0 0 := by
  set e : Fin n ≃ Fin r ⊕ Fin t := (finSumFinEquiv.trans (finCongr hn)).symm with he
  have hX : jn hn x (0 : Mx D V.rank t) = (Matrix.fromCols x (0 : Mx D V.rank t)).submatrix id e := rfl
  have hadj : adj (jn hn x (0 : Mx D V.rank t)) =
      (Matrix.fromRows (adj x) (0 : Matrix (Fin t) (Fin V.rank) (AE D))).submatrix e id := by
    ext i k
    rw [hX]
    simp only [adj, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply, id]
    rcases e i with a | b
    · simp
    · simp
  have hG : (HMul.hMul (gA V) (jn hn x (0 : Mx D V.rank t)) : Mx D V.rank n) =
      (Matrix.fromCols (HMul.hMul (gA V) x : Mx D V.rank r) (0 : Mx D V.rank t)).submatrix id e := by
    ext i j
    rw [hX]
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, id]
    rcases e j with a | b
    · simp [Matrix.mul_apply]
    · simp
  unfold GlobalTheory.StdUnn.inner
  rw [hG, hadj, ← Matrix.submatrix_mul _ _ e id e Function.bijective_id, Matrix.fromRows_mul_fromCols]
  simp [bl, he]

theorem trace_bl {R : Type} [CommRing R] {n r t : ℕ} (hn : r + t = n) (a : Matrix (Fin r) (Fin r) R)
    (b : Matrix (Fin r) (Fin t) R) (c : Matrix (Fin t) (Fin r) R) (d : Matrix (Fin t) (Fin t) R) :
    Matrix.trace (bl hn a b c d) = Matrix.trace a + Matrix.trace d := by
  unfold bl
  simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  rw [Equiv.sum_comp (finSumFinEquiv.trans (finCongr hn)).symm (fun i => Matrix.fromBlocks a b c d i i),
    Fintype.sum_sum_type]
  simp

theorem trace_nzx {D : D7} {n r t : ℕ} (hn : r + t = n) (V : HSp D) (z : Mx D r r) (x : Mx D V.rank r) :
    Matrix.trace (HMul.hMul (bl hn z 0 (adj (0 : Mx D r t)) 0 : Mx D n n)
        (GlobalTheory.StdUnn.inner V (jn hn x (0 : Mx D V.rank t)) (jn hn x (0 : Mx D V.rank t))) : Mx D n n) =
      Matrix.trace (HMul.hMul z (GlobalTheory.StdUnn.inner V x x) : Mx D r r) := by
  have h0 : adj (0 : Mx D r t) = 0 := by
    ext i j
    simp [adj]
  rw [inner_jn, h0]
  have hm : (HMul.hMul (bl hn z 0 0 0 : Mx D n n) (bl hn (GlobalTheory.StdUnn.inner V x x) 0 0 0) : Mx D n n) =
      bl hn (HMul.hMul z (GlobalTheory.StdUnn.inner V x x) : Mx D r r) 0 0 0 := by
    unfold bl
    rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp
  rw [hm, trace_bl]
  simp

theorem conj_char {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) (u : AF F) :
    conj (ψ u) = ψ (-u) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hψ.2.1 u)]

theorem wz_eq_fib : ∀ {D : D7} {n r t : ℕ} (hP : PartFT) {hn : r + t = n} (M : Maps D hn) (m : Meas D r t) (V : HSp D) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {χ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (hη : ResEta D χ V.rank) {θ : InfFam D} (hθ : IsInfFam θ) {μ : Measure (Mx D V.rank n)} (hμ : ∃ 𝓕, IsCovolOne (ratMx D V.rank n) μ 𝓕) {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} (hω : IsWeilSch ψ χ θ V μ ω) {μr : Measure (Mx D V.rank r)} (hμr : ∃ 𝓕, IsCovolOne (ratMx D V.rank r) μr 𝓕) {μt : Measure (Mx D V.rank t)} (hμt : ∃ 𝓕, IsCovolOne (ratMx D V.rank t) μt 𝓕) (b₀ : HermE D r) {fib : Measure (Mx D V.rank r)} (hfib : IsFib ψ θ V b₀ μr m.lz fib) (Φ : schwartzA θ V.rank n) (g : G D n), Wz M m ψ b₀ (fun g => (ω g Φ).1 0) g = ∫ x, (ω g Φ).1 (jn hn x 0) ∂fib := by
  intro D n r t hP hn M m V ψ hψ χ hχ hη θ hθ μ hμ ω hω μr hμr μt hμt b₀ fib hfib Φ g
  have hPF := hP D n r t hn M V ψ hψ χ hχ hη θ hθ μ hμ ω hω μr μt hμr hμt
  rw [← (hfib.int _ (hPF (ω g Φ)).2.1).2]
  unfold Wz W
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  show (ω (M.w * M.nzx z 0 * g) Φ).1 0 * conj (chz ψ b₀ z) = Jt ψ V μr _ z * ψ (-halfTr _)
  have e1 : ω (M.w * M.nzx z 0 * g) Φ = ω M.w (ω (M.nzx z 0) (ω g Φ)) := by
    simp only [map_mul, Module.End.mul_apply]
  rw [e1, (hPF (ω (M.nzx z 0) (ω g Φ))).1]
  unfold chz
  rw [conj_char hψ]
  congr 1
  unfold Jt
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  show (ω (M.nzx z 0) (ω g Φ)).1 (jn hn x 0) = (ω g Φ).1 (jn hn x 0) * ψ (halfTr _)
  rw [hω.unip _ _ (M.nzx_mat z 0), trace_nzx, mul_comm]

end GlobalTheory.CompanionTheory.WzFib

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerVanishingAtZeroStatement
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.SchwartzSpaceL2
open scoped ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_vanishing_at_zero : Ad3.SchwartzSpaceL2.SDZ := by
  first | exact @GlobalTheory.CompanionTheory.DoubleTate.sdz | exact GlobalTheory.CompanionTheory.DoubleTate.sdz | (intros; apply GlobalTheory.CompanionTheory.DoubleTate.sdz <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerWellDefinedStatement
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.SchwartzSpaceL2
open scoped ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_well_defined : Ad3.SchwartzSpaceL2.SWd := by
  first | exact @GlobalTheory.CompanionTheory.WhittakerTorus.swd | exact GlobalTheory.CompanionTheory.WhittakerTorus.swd | (intros; apply GlobalTheory.CompanionTheory.WhittakerTorus.swd <;> assumption)
end

