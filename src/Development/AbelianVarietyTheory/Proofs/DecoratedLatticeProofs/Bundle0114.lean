import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0105
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientHeightLowerBoundShortIsotropicVector
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0102
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0023
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0019
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.InfPartOfSplitIdem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0103
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceCharacterConductorIntegers

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualLatticeAtPlaceComapUnitarySupported
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
open scoped TensorProduct

namespace GlobalTheory.IwaPlace.SdComap

set_option synthInstance.maxHeartbeats 400000

variable {D : D7}

theorem exists_nat_mul_isIntegral' (e : D.host.E) : ∃ n : ℕ, 0 < n ∧ IsIntegral ℤ ((n : D.host.E) * e) := by
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := D.host.E) {e}
  have h := hy e (Finset.mem_singleton_self e)
  have hpos : 0 < y.natAbs := Int.natAbs_pos.2 hy0
  refine ⟨y.natAbs * y.natAbs, Nat.mul_pos hpos hpos, ?_⟩
  have e1 : ((y.natAbs * y.natAbs : ℕ) : D.host.E) * e = (y : D.host.E) * ((y : D.host.E) * e) := by
    have h2 := Int.natAbs_mul_self' y
    rw [← mul_assoc, ← Int.cast_natCast, Nat.cast_mul, h2, Int.cast_mul]
  rw [e1]
  rw [zsmul_eq_mul] at h
  refine IsIntegral.mul ?_ h
  simpa using (isIntegral_algebraMap (R := ℤ) (A := D.host.E) (x := y))

theorem mul_mem_intAE' {x y : Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D) (hy : y ∈ intAE D) :
    x * y ∈ intAE D := by
  refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intAE D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, v, rfl⟩
    refine AddSubgroup.subset_closure ⟨a * b, fun w => ?_, u * v, ?_⟩
    · rw [map_mul]; exact mul_mem (ha w) (hb w)
    · rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl
  · intro x _; rw [zero_mul]; exact zero_mem _
  · intro x _; rw [mul_zero]; exact zero_mem _
  · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
  · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
  · intro x y _ _ h; rw [neg_mul]; exact neg_mem h
  · intro x y _ _ h; rw [mul_neg]; exact neg_mem h

theorem natCast_mem_intAE (n : ℕ) : (n : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D := by
  rw [Algebra.TensorProduct.natCast_def]
  refine AddSubgroup.subset_closure ⟨(n : Af D.host.F), fun v => ?_, 1, ?_⟩
  · rw [map_natCast]; exact natCast_mem _ n
  · simp

theorem exists_natCast_mul_mem_intAE (z : Af D.host.F ⊗[D.host.F] D.host.E) :
    ∃ n : ℕ, 0 < n ∧ (n : Af D.host.F ⊗[D.host.F] D.host.E) * z ∈ intAE D := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨1, one_pos, by rw [mul_zero]; exact zero_mem _⟩
  | tmul a e =>
    obtain ⟨n, hn, he⟩ := exists_nat_mul_isIntegral' (D := D) e
    obtain ⟨d, hd, ha⟩ := GlobalTheory.HolDict.ShortVec.exists_denom_adele (F := D.host.F) a
    refine ⟨d * n, Nat.mul_pos hd hn, ?_⟩
    have e1 : ((d * n : ℕ) : Af D.host.F ⊗[D.host.F] D.host.E) * (a ⊗ₜ[D.host.F] e) =
        ((d : Af D.host.F) * a) ⊗ₜ[D.host.F] ((n : D.host.E) * e) := by
      rw [Nat.cast_mul, Algebra.TensorProduct.natCast_def, Algebra.TensorProduct.natCast_def',
        Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    rw [e1]
    exact AddSubgroup.subset_closure ⟨_, fun v => Subring.mem_iInf.1 ha v, ⟨_, he⟩, rfl⟩
  | add x y hx hy =>
    obtain ⟨n₁, h₁, hx⟩ := hx
    obtain ⟨n₂, h₂, hy⟩ := hy
    refine ⟨n₁ * n₂, Nat.mul_pos h₁ h₂, ?_⟩
    have e1 : ((n₁ * n₂ : ℕ) : Af D.host.F ⊗[D.host.F] D.host.E) * (x + y) =
        (n₂ : Af D.host.F ⊗[D.host.F] D.host.E) * ((n₁ : Af D.host.F ⊗[D.host.F] D.host.E) * x) +
          (n₁ : Af D.host.F ⊗[D.host.F] D.host.E) * ((n₂ : Af D.host.F ⊗[D.host.F] D.host.E) * y) := by
      push_cast; ring
    rw [e1]
    exact add_mem (mul_mem_intAE' (natCast_mem_intAE n₂) hx) (mul_mem_intAE' (natCast_mem_intAE n₁) hy)

theorem exists_natCast_mul_mem_intAt {P : Pl D → Prop} {a : AE D} (ha : a ∈ idAt D P) :
    ∃ n : ℕ, 0 < n ∧ (n : AE D) * a ∈ intAt D P := by
  obtain ⟨n, hn, h⟩ := exists_natCast_mul_mem_intAE (D := D) (finPart D a)
  refine ⟨n, hn, Ideal.mul_mem_left _ _ ha, ?_⟩
  rw [map_mul, map_natCast]; exact h

theorem intAt_add {P : Pl D → Prop} {a b : AE D} (ha : a ∈ intAt D P) (hb : b ∈ intAt D P) : a + b ∈ intAt D P :=
  ⟨add_mem ha.1 hb.1, by rw [map_add]; exact add_mem ha.2 hb.2⟩

theorem intAt_mul {P : Pl D → Prop} {a b : AE D} (ha : a ∈ intAt D P) (hb : b ∈ intAt D P) : a * b ∈ intAt D P :=
  ⟨Ideal.mul_mem_left _ _ hb.1, by rw [map_mul]; exact mul_mem_intAE' ha.2 hb.2⟩

theorem intAt_natCast_mul {P : Pl D → Prop} {a : AE D} (n : ℕ) (ha : a ∈ intAt D P) : (n : AE D) * a ∈ intAt D P :=
  ⟨Ideal.mul_mem_left _ _ ha.1, by rw [map_mul, map_natCast]; exact mul_mem_intAE' (natCast_mem_intAE n) ha.2⟩

theorem intAt_sum {P : Pl D → Prop} {ι : Type} (s : Finset ι) (f : ι → AE D) (h : ∀ i ∈ s, f i ∈ intAt D P) :
    ∑ i ∈ s, f i ∈ intAt D P := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact ⟨zero_mem _, by rw [map_zero]; exact zero_mem _⟩
  | insert a s has ih =>
    rw [Finset.sum_insert has]
    exact intAt_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem cA_mulVec {n : ℕ} (M : Mx D n n) (y : Fin n → AE D) :
    (fun i => cA D ((M *ᵥ y) i)) = Matrix.vecMul (fun i => cA D (y i)) (adj M) := by
  funext i
  simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, adj, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem hermAt_eq (S : HSp D) (x y : Fin S.rank → AE D) :
    hermAt S x y = Matrix.vecMul (fun i => cA D (y i)) (gA S) ⬝ᵥ x := by
  simp only [hermAt, Matrix.vecMul, dotProduct, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem hermAt_mt (S : HSp D) (g : GA D S) (x y : Fin S.rank → AE D) :
    hermAt S (mt S g *ᵥ x) (mt S g *ᵥ y) = hermAt S x y := by
  rw [hermAt_eq, hermAt_eq, cA_mulVec (mt S g) y, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul,
    mt_unitary]

theorem mulVec_eq_add {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (y : Fin n → R) (i : Fin n) :
    (M *ᵥ y) i = y i + ∑ j, (M i j - (1 : Matrix (Fin n) (Fin n) R) i j) * y j := by
  have h : M *ᵥ y = y + (M - 1) *ᵥ y := by rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
  rw [h]; rfl

theorem eq_mulVec_sub {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (y : Fin n → R) (i : Fin n) :
    y i = (M *ᵥ y) i - ∑ j, (M i j - (1 : Matrix (Fin n) (Fin n) R) i j) * y j := by
  rw [mulVec_eq_add, add_sub_cancel_right]

theorem smul_mulVec_apply {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (y : Fin n → R) (c : R)
    (i : Fin n) : (c • (M *ᵥ y)) i = c * y i + ∑ j, (c * (M i j - (1 : Matrix (Fin n) (Fin n) R) i j)) * y j := by
  rw [Pi.smul_apply, smul_eq_mul, mulVec_eq_add, mul_add, Finset.mul_sum]
  simp only [mul_assoc]

theorem mulVec_natCast_smul {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (y : Fin n → R) (m K : ℕ) :
    M *ᵥ (((m * K : ℕ) : R) • y) = (m : R) • ((K : R) • (M *ᵥ y)) := by
  rw [Matrix.mulVec_smul, Nat.cast_mul, mul_smul]

theorem mulVec_mulVec_of_mul_eq_one {R : Type} [CommRing R] {n : ℕ} {M N : Matrix (Fin n) (Fin n) R} (h : M * N = 1)
    (x : Fin n → R) : M *ᵥ (N *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]

theorem exists_common_natCast_mul_mem_intAt {P : Pl D → Prop} {ι : Type} [Fintype ι] (a : ι → AE D)
    (ha : ∀ i, a i ∈ idAt D P) : ∃ K : ℕ, 0 < K ∧ ∀ i, (K : AE D) * a i ∈ intAt D P := by
  classical
  choose n hn hx using fun i => exists_natCast_mul_mem_intAt (ha i)
  refine ⟨∏ p, n p, Finset.prod_pos fun p _ => hn p, fun i => ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), Nat.cast_mul, mul_assoc]
  exact intAt_natCast_mul _ (hx i)

theorem isSDAt_comap_of (S : HSp D) (v : Pl D) (M N : Mx D S.rank S.rank) (hMN : M * N = 1)
    (hM1 : ∀ i j, M i j - (1 : Mx D S.rank S.rank) i j ∈ idAt D (· = v))
    (hherm : ∀ x y, hermAt S (M *ᵥ x) (M *ᵥ y) = hermAt S x y)
    (Λ : AddSubgroup (Fin S.rank → AE D)) (hΛ : IsSDAt S v Λ) :
    IsSDAt S v (Λ.comap (Matrix.mulVecLin M).toAddMonoidHom) := by
  obtain ⟨hsupp, ⟨m, hm, hmint⟩, hsd⟩ := hΛ
  have hmem : ∀ y, y ∈ Λ.comap (Matrix.mulVecLin M).toAddMonoidHom ↔ M *ᵥ y ∈ Λ := fun y => Iff.rfl
  refine ⟨fun y hy i => ?_, ?_, ?_⟩
  · rw [eq_mulVec_sub M y i]
    exact sub_mem (hsupp _ ((hmem y).1 hy) i) (Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (hM1 i j))
  · obtain ⟨K, hK, hKint⟩ := exists_common_natCast_mul_mem_intAt
      (fun p : Fin S.rank × Fin S.rank => M p.1 p.2 - (1 : Mx D S.rank S.rank) p.1 p.2) fun p => hM1 p.1 p.2
    refine ⟨m * K, Nat.mul_pos hm hK, fun y hy => (hmem _).2 ?_⟩
    rw [mulVec_natCast_smul M y m K]
    refine hmint _ fun i => ?_
    rw [smul_mulVec_apply M y (K : AE D) i]
    exact intAt_add (intAt_natCast_mul K (hy i)) (intAt_sum _ _ fun j _ => intAt_mul (hKint (i, j)) (hy j))
  · intro y hy
    have key := hsd _ (mulVec_mem_idAt M hy)
    refine ⟨fun h x hx => ?_, fun h => (hmem y).2 (key.2 fun x hx => ?_)⟩
    · rw [← hherm y x]; exact key.1 ((hmem y).1 h) _ ((hmem x).1 hx)
    · have hx' : M *ᵥ (N *ᵥ x) = x := mulVec_mulVec_of_mul_eq_one hMN x
      have h3 := h (N *ᵥ x) ((hmem _).2 (by rw [hx']; exact hx))
      rwa [← hherm, hx'] at h3

theorem isSDAt_comap (D : D7) (S : HSp D) (v : Pl D) (g : GA D S) (hg : g ∈ grpAt S (· = v))
    (Λ : AddSubgroup (Fin S.rank → AE D)) (hΛ : IsSDAt S v Λ) :
    IsSDAt S v (Λ.comap (Matrix.mulVecLin (mt S g)).toAddMonoidHom) :=
  isSDAt_comap_of S v (mt S g) (mt S g⁻¹) (mt_mul_inv S g) ((mem_congGrp_iff S (idAt D (· = v)) g).1 hg)
    (hermAt_mt S g) Λ hΛ

end GlobalTheory.IwaPlace.SdComap

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LintegralUnfoldSumTransitiveOrbit
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ENNReal Pointwise

namespace GlobalTheory
namespace Unf

theorem lintegral_integral_unfold_transitive : ∀ (H : Type) [Group H] [MeasurableSpace H] [MeasurableMul H] (ν : Measure H) [ν.IsMulLeftInvariant] (Γ : Subgroup H) [Countable Γ] (Y : Type) [Countable Y] [MulAction Γ Y] (y₀ : Y), (∀ y, ∃ γ : Γ, γ • y₀ = y) → ∀ (𝓕 𝓖 : Set H), IsFundamentalDomain Γ 𝓕 ν → IsFundamentalDomain ((MulAction.stabilizer Γ y₀).map Γ.subtype) 𝓖 ν → ∀ Φ : Y → H → ℂ, (∀ y, Measurable (Φ y)) → (∀ (γ : Γ) y h, Φ (γ • y) ((γ : H) * h) = Φ y h) → (∫⁻ h in 𝓖, ‖Φ y₀ h‖ₑ ∂ν = ∫⁻ h in 𝓕, ∑' y, ‖Φ y h‖ₑ ∂ν) ∧ (∫⁻ h in 𝓕, ∑' y, ‖Φ y h‖ₑ ∂ν ≠ ⊤ → ∫ h in 𝓖, Φ y₀ h ∂ν = ∫ h in 𝓕, ∑' y, Φ y h ∂ν) := by
  intro H _ _ _ ν _ Γ _ Y _ _ y₀ htr 𝓕 𝓖 hF hG Φ hΦ hinv
  set S : Subgroup H := (MulAction.stabilizer Γ y₀).map Γ.subtype with hSdef
  haveI : Countable S := by
    have hle : S ≤ Γ := Subgroup.map_subtype_le _
    exact Function.Injective.countable (Subgroup.inclusion_injective hle)
  choose σ hσ using htr
  have hO : ∀ γ : Γ, γ • y₀ ∈ (Set.univ : Set Y) := fun _ => Set.mem_univ _
  have hσ' : ∀ a : (Set.univ : Set Y), σ a • y₀ = a := fun a => hσ a
  have hG' := GlobalTheory.OrbitUnfold.isFundamentalDomain_iUnion_pull hF y₀ hO (fun a => σ a) hσ'
  have hinvS : ∀ (s : S) (h : H), Φ y₀ (s • h) = Φ y₀ h := by
    rintro ⟨s, hs⟩ h
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hs
    have := hinv t y₀ h
    rw [show t • y₀ = y₀ from ht] at this
    simpa [Subgroup.smul_def] using this
  have hfun : ∀ (y : Y) (h : H), Φ y ((σ y : H) * h) = Φ y₀ h := fun y h => by
    have := hinv (σ y) y₀ h
    rwa [hσ y] at this
  have hlint : ∀ y : Y, ∫⁻ h in GlobalTheory.OrbitUnfold.pull 𝓕 (σ y : H), ‖Φ y₀ h‖ₑ ∂ν
      = ∫⁻ h in 𝓕, ‖Φ y h‖ₑ ∂ν := fun y => by
    rw [← GlobalTheory.OrbitUnfold.setLIntegral_pull (σ y : H) (fun h => ‖Φ y h‖ₑ)]
    simp only [hfun]
  have hint : ∀ y : Y, ∫ h in GlobalTheory.OrbitUnfold.pull 𝓕 (σ y : H), Φ y₀ h ∂ν
      = ∫ h in 𝓕, Φ y h ∂ν := fun y => by
    rw [← GlobalTheory.OrbitUnfold.setIntegral_pull (σ y : H) (Φ y)]
    simp only [hfun]
  have hd : Pairwise (Function.onFun (AEDisjoint ν) fun y : Y =>
      GlobalTheory.OrbitUnfold.pull 𝓕 (σ y : H)) := by
    intro a b hab
    refine GlobalTheory.OrbitUnfold.aedisjoint_pull hF fun h => hab ?_
    rw [← hσ a, ← hσ b, h]
  have hU : (⋃ a : (Set.univ : Set Y), GlobalTheory.OrbitUnfold.pull 𝓕 (σ a : H))
      = ⋃ y : Y, GlobalTheory.OrbitUnfold.pull 𝓕 (σ y : H) := by
    ext x; simp
  rw [hU] at hG'
  have hL1 : ∫⁻ h in 𝓖, ‖Φ y₀ h‖ₑ ∂ν
      = ∫⁻ h in ⋃ y : Y, GlobalTheory.OrbitUnfold.pull 𝓕 (σ y : H), ‖Φ y₀ h‖ₑ ∂ν :=
    hG.setLIntegral_eq hG' (fun h => ‖Φ y₀ h‖ₑ) (fun s h => by simp only [hinvS])
  have hL2 : ∫⁻ h in ⋃ y : Y, GlobalTheory.OrbitUnfold.pull 𝓕 (σ y : H), ‖Φ y₀ h‖ₑ ∂ν
      = ∑' y, ∫⁻ h in 𝓕, ‖Φ y h‖ₑ ∂ν := by
    rw [lintegral_iUnion₀ (fun y => GlobalTheory.OrbitUnfold.nullMeasurableSet_pull hF _) hd]
    simp only [hlint]
  have hL3 : ∫⁻ h in 𝓕, ∑' y, ‖Φ y h‖ₑ ∂ν = ∑' y, ∫⁻ h in 𝓕, ‖Φ y h‖ₑ ∂ν :=
    lintegral_tsum fun y => (hΦ y).enorm.aemeasurable
  have hmain : ∫⁻ h in 𝓖, ‖Φ y₀ h‖ₑ ∂ν = ∫⁻ h in 𝓕, ∑' y, ‖Φ y h‖ₑ ∂ν := by
    rw [hL1, hL2, hL3]
  refine ⟨hmain, fun hfin => ?_⟩
  have hfin' : ∑' y, ∫⁻ h in 𝓕, ‖Φ y h‖ₑ ∂ν ≠ ⊤ := by rwa [← hL3]
  have hI : IntegrableOn (Φ y₀) (⋃ y : Y, GlobalTheory.OrbitUnfold.pull 𝓕 (σ y : H)) ν := by
    refine ⟨(hΦ y₀).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral, hL2]
    exact lt_top_iff_ne_top.2 hfin'
  have hI1 : ∫ h in 𝓖, Φ y₀ h ∂ν
      = ∫ h in ⋃ y : Y, GlobalTheory.OrbitUnfold.pull 𝓕 (σ y : H), Φ y₀ h ∂ν :=
    hG.setIntegral_eq hG' (fun s h => hinvS s h)
  rw [hI1, integral_iUnion_ae (fun y => GlobalTheory.OrbitUnfold.nullMeasurableSet_pull hF _) hd hI]
  simp only [hint]
  exact (integral_tsum (fun y => (hΦ y).aestronglyMeasurable) hfin').symm

end Unf
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalIntegersTensorCoordsPrimeToDiscriminant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl IsDedekindDomain NumberField GlobalTheory.FixedUnitNorm
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.FixedUnitNorm.Coords

section Field

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}

theorem isIntegral_of_trace_norm (w : E) (t n : 𝓞 F) (ht : w + σ w = algebraMap F E t)
    (hn : w * σ w = algebraMap F E n) : IsIntegral ℤ w := by
  have hE : IsIntegral (𝓞 E) w := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C (algebraMap (𝓞 F) (𝓞 E) t) * Polynomial.X +
      Polynomial.C (algebraMap (𝓞 F) (𝓞 E) n), by monicity!, ?_⟩
    have h1 : algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) t) = algebraMap F E t := rfl
    have h2 : algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) n) = algebraMap F E n := rfl
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C, h1, h2, ← ht, ← hn]
    ring
  exact isIntegral_trans (R := ℤ) w hE

theorem exists_coords (h : IsCMExt F E σ) (w : E) (t n : 𝓞 F) (ht : w + σ w = algebraMap F E t)
    (hn : w * σ w = algebraMap F E n) (x : 𝓞 E) :
    ∃ a b : 𝓞 F, (x : E) * algebraMap F E ((t ^ 2 - 4 * n : 𝓞 F) : F) =
      algebraMap F E a + algebraMap F E b * w := by
  have hσ := GlobalTheory.SelfDualLatticeCompare.conj_conj h
  let W : 𝓞 E := ⟨w, isIntegral_of_trace_norm w t n ht hn⟩
  let s : 𝓞 E →+* 𝓞 E := RingOfIntegers.mapRingHom (σ : E →+* E)
  have hs : ∀ y : 𝓞 E, ((s y : 𝓞 E) : E) = σ y := fun _ => rfl
  have hW : ((W : 𝓞 E) : E) = w := rfl
  obtain ⟨a, ha⟩ := GlobalTheory.UnramifiedDiscriminant.exists_int_of_conj_eq h
    ((s x * W - x * s W) * (W - s W)) (by
      change σ ((σ (x : E) * w - (x : E) * σ w) * (w - σ w)) = (σ (x : E) * w - (x : E) * σ w) * (w - σ w)
      simp only [map_mul, map_sub, hσ]
      ring)
  obtain ⟨b, hb⟩ := GlobalTheory.UnramifiedDiscriminant.exists_int_of_conj_eq h
    ((x - s x) * (W - s W)) (by
      change σ (((x : E) - σ x) * (w - σ w)) = ((x : E) - σ x) * (w - σ w)
      simp only [map_mul, map_sub, hσ]
      ring)
  have ha' : algebraMap F E a = (σ x * w - x * σ w) * (w - σ w) := by
    exact congrArg (algebraMap (𝓞 E) E) ha
  have hb' : algebraMap F E b = (x - σ x) * (w - σ w) := by
    exact congrArg (algebraMap (𝓞 E) E) hb
  refine ⟨a, b, ?_⟩
  have hd : algebraMap F E ((t ^ 2 - 4 * n : 𝓞 F) : F) = (algebraMap F E t) ^ 2 - 4 * algebraMap F E n := by
    push_cast
    simp [map_sub, map_pow, map_mul, map_ofNat]
  rw [hd, ha', hb', ← ht, ← hn]
  ring

theorem tmul_move {K : Type} [Field K] [Algebra F K] (m : K) (r : F) (e : E) :
    (algebraMap F K r * m) ⊗ₜ[F] e = m ⊗ₜ[F] (algebraMap F E r * e) := by
  rw [← Algebra.smul_def, ← Algebra.smul_def, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]

theorem coords_add {K : Type} [Field K] [Algebra F K] (a b a' b' : K) (w : E) :
    (a ⊗ₜ[F] (1 : E) + b ⊗ₜ[F] w) + (a' ⊗ₜ[F] (1 : E) + b' ⊗ₜ[F] w) = (a + a') ⊗ₜ[F] (1 : E) + (b + b') ⊗ₜ[F] w := by
  rw [TensorProduct.add_tmul, TensorProduct.add_tmul, add_add_add_comm]

theorem coords_neg {K : Type} [Field K] [Algebra F K] (a b : K) (w : E) :
    -(a ⊗ₜ[F] (1 : E) + b ⊗ₜ[F] w) = (-a) ⊗ₜ[F] (1 : E) + (-b) ⊗ₜ[F] w := by
  rw [TensorProduct.neg_tmul, TensorProduct.neg_tmul, neg_add]

end Field

end GlobalTheory.FixedUnitNorm.Coords

namespace GlobalTheory.FixedUnitNorm.Coords

set_option maxHeartbeats 1000000 in

theorem mem_intV_coords : ∀ (D : D7) (v : Pl D) (w : D.host.E) (t n : 𝓞 D.host.F),
    w + D.sp.cm.sig w = algebraMap D.host.F D.host.E t → w * D.sp.cm.sig w = algebraMap D.host.F D.host.E n →
    t ^ 2 - 4 * n ∉ v.asIdeal → ∀ z ∈ intV D v, ∃ a ∈ v.adicCompletionIntegers D.host.F,
      ∃ b ∈ v.adicCompletionIntegers D.host.F, z = a ⊗ₜ[D.host.F] (1 : D.host.E) + b ⊗ₜ[D.host.F] w := by
  intro D v w t n ht hn hv z hz
  have hcm := GlobalTheory.AdelicU.isCMExt_host D
  have hcoe : ∀ r : 𝓞 D.host.F, ((algebraMap (𝓞 D.host.F) (v.adicCompletionIntegers D.host.F) r :
      v.adicCompletionIntegers D.host.F) : Fv D.host.F v) = algebraMap D.host.F (Fv D.host.F v) (r : D.host.F) :=
    fun r => rfl
  have hmem : ∀ r : 𝓞 D.host.F, algebraMap D.host.F (Fv D.host.F v) (r : D.host.F) ∈
      v.adicCompletionIntegers D.host.F := fun r => hcoe r ▸ (algebraMap (𝓞 D.host.F) (v.adicCompletionIntegers D.host.F) r).2
  obtain ⟨u, hu⟩ := ((GlobalTheory.SelfDualGenus.isUnit_algebraMap_iff v (t ^ 2 - 4 * n)).2 hv).exists_left_inv
  set U : Fv D.host.F v := ((u : v.adicCompletionIntegers D.host.F) : Fv D.host.F v) with hU
  have hu' : U * algebraMap D.host.F (Fv D.host.F v) ((t ^ 2 - 4 * n : 𝓞 D.host.F) : D.host.F) = 1 := by
    have := congrArg (fun y : v.adicCompletionIntegers D.host.F => (y : Fv D.host.F v)) hu
    rw [MulMemClass.coe_mul, hcoe, OneMemClass.coe_one] at this
    exact this
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨c, hc, x, rfl⟩ := hy
    obtain ⟨a, b, hab⟩ := exists_coords hcm w t n ht hn x
    refine ⟨c * U * algebraMap D.host.F (Fv D.host.F v) (a : D.host.F), mul_mem (mul_mem hc u.2) (hmem a),
      c * U * algebraMap D.host.F (Fv D.host.F v) (b : D.host.F), mul_mem (mul_mem hc u.2) (hmem b), ?_⟩
    have hc' : c = algebraMap D.host.F (Fv D.host.F v) ((t ^ 2 - 4 * n : 𝓞 D.host.F) : D.host.F) * (c * U) := by
      rw [mul_comm, mul_assoc, hu', mul_one]
    calc c ⊗ₜ[D.host.F] (x : D.host.E)
        = (algebraMap D.host.F (Fv D.host.F v) ((t ^ 2 - 4 * n : 𝓞 D.host.F) : D.host.F) * (c * U)) ⊗ₜ[D.host.F]
            (x : D.host.E) := by rw [← hc']
      _ = (c * U) ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E ((t ^ 2 - 4 * n : 𝓞 D.host.F) : D.host.F) * x) :=
          tmul_move _ _ _
      _ = (c * U) ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E (a : D.host.F) * 1 +
            algebraMap D.host.F D.host.E (b : D.host.F) * w) := by rw [mul_comm (algebraMap D.host.F D.host.E _) (x : D.host.E), hab, mul_one]
      _ = (algebraMap D.host.F (Fv D.host.F v) (a : D.host.F) * (c * U)) ⊗ₜ[D.host.F] (1 : D.host.E) +
            (algebraMap D.host.F (Fv D.host.F v) (b : D.host.F) * (c * U)) ⊗ₜ[D.host.F] w := by
          rw [TensorProduct.tmul_add, tmul_move, tmul_move]
      _ = _ := by rw [mul_comm (algebraMap D.host.F (Fv D.host.F v) (a : D.host.F)),
            mul_comm (algebraMap D.host.F (Fv D.host.F v) (b : D.host.F))]
  | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
  | add y y' _ _ h h' =>
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    obtain ⟨a', ha', b', hb', rfl⟩ := h'
    refine ⟨a + a', add_mem ha ha', b + b', add_mem hb hb', ?_⟩
    exact coords_add a b a' b' w
  | neg y _ h =>
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    refine ⟨-a, neg_mem ha, -b, neg_mem hb, ?_⟩
    exact coords_neg a b w

end GlobalTheory.FixedUnitNorm.Coords
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLatticeCompletionAtPlacesOfFinPartMemHatLatti
section
set_option synthInstance.maxHeartbeats 400000
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HatLatV

variable {D : D7}

def cut (P : Pl D → Prop) (u : Af D.host.F ⊗[D.host.F] D.host.E) : AE D :=
  Formalism.IndefR.Fin.LevelGroupLemmas.Lat.lift ((GlobalTheory.SelfDualAt.indP P ⊗ₜ[D.host.F] (1 : D.host.E)) * u)

def cutHom (P : Pl D → Prop) : (Af D.host.F ⊗[D.host.F] D.host.E) →+ AE D where
  toFun := cut P
  map_zero' := by
    show Formalism.IndefR.Fin.LevelGroupLemmas.Lat.lift _ = 0
    rw [mul_zero]; exact Formalism.IndefR.Fin.LevelGroupLemmas.Lat.lift_zero
  map_add' a b := by
    show Formalism.IndefR.Fin.LevelGroupLemmas.Lat.lift _ = Formalism.IndefR.Fin.LevelGroupLemmas.Lat.lift _ + Formalism.IndefR.Fin.LevelGroupLemmas.Lat.lift _
    rw [mul_add]; exact Formalism.IndefR.Fin.LevelGroupLemmas.Lat.lift_add _ _

theorem cut_tmul (P : Pl D → Prop) (a : Af D.host.F) (x : D.host.E) :
    cut P (a ⊗ₜ[D.host.F] x) = pairA D.host.F 0 (GlobalTheory.SelfDualAt.indP P * a) ⊗ₜ[D.host.F] x := by
  unfold cut
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rfl

set_option maxHeartbeats 800000 in

theorem cut_finPart (P : Pl D → Prop) (u : AE D) (hu : u ∈ idAt D P) : cut P (finPart D u) = u := by
  unfold idAt at hu
  rw [Ideal.mem_inf] at hu
  obtain ⟨hinf, hfin⟩ := hu
  rw [RingHom.mem_ker] at hinf
  have hoff : ∀ w : Pl D, ¬ P w → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w (finPart D u) = 0 := by
    intro w hw
    have := (Submodule.mem_iInf _).1 hfin ⟨w, hw⟩
    exact (RingHom.mem_ker).1 this
  have hcut : (GlobalTheory.SelfDualAt.indP P ⊗ₜ[D.host.F] (1 : D.host.E)) * finPart D u = finPart D u := by
    refine (sub_eq_zero.mp (GlobalTheory.SelfDualAt.eq_zero_of_compFin _ fun w => ?_)).symm
    rw [map_sub, map_mul]
    have hc : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w (GlobalTheory.SelfDualAt.indP P ⊗ₜ[D.host.F] (1 : D.host.E)) =
        evalV D.host.F w (GlobalTheory.SelfDualAt.indP P) ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
    rw [hc, GlobalTheory.SelfDualAt.evalV_indP]
    by_cases hw : P w
    · rw [if_pos hw, ← Algebra.TensorProduct.one_def, one_mul, sub_self]
    · rw [if_neg hw, TensorProduct.zero_tmul, zero_mul, sub_zero, hoff w hw]
  unfold cut
  rw [hcut]
  exact (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.eq_lift_of_infPart u hinf).symm

theorem mem_latV_of_hatL : ∀ (D : D7) (S : HSp D) (L : Lat S) (P : Pl D → Prop) (y : Fin S.rank → AE D),
    (∀ i, y i ∈ idAt D P) →
    (fun i => Formalism.IndefR.Lev.swapAE D (finPart D (y i))) ∈ Formalism.L2.Herm.hatL (F := D.host.F) L → y ∈ latV S L P := by
  intro D S L P y hy hz
  have hlat : (fun i => finPart D (y i)) ∈ latHat D.host.F D.host.E (L : Set (Fin S.rank → D.host.E)) :=
    (GlobalTheory.LevSplit.latHat_iff L _).2 hz
  have key : y = AddMonoidHom.compLeft (cutHom P) (Fin S.rank) (fun i => finPart D (y i)) :=
    funext fun i => (cut_finPart P (y i) (hy i)).symm
  rw [key]
  refine AddSubgroup.closure_induction
    (p := fun u _ => AddMonoidHom.compLeft (cutHom P) (Fin S.rank) u ∈ latV S L P) ?_ ?_ ?_ ?_ hlat
  · rintro _ ⟨a, ha, x, hx, rfl⟩
    apply AddSubgroup.subset_closure
    refine ⟨GlobalTheory.SelfDualAt.indP P * a, ?_, ?_, 1, rfl, x, hx, ?_⟩
    · intro v
      rw [map_mul, GlobalTheory.SelfDualAt.evalV_indP]
      split_ifs
      · rw [one_mul]; exact ha v
      · rw [zero_mul]; exact zero_mem _
    · intro v hv
      rw [map_mul, GlobalTheory.SelfDualAt.evalV_indP, if_neg hv, zero_mul]
    · funext i
      show cut P (a ⊗ₜ[D.host.F] x i) = _
      rw [cut_tmul, one_mul]
  · rw [map_zero]; exact zero_mem _
  · intro a b _ _ ha hb
    rw [map_add]; exact add_mem ha hb
  · intro a _ ha
    rw [map_neg]; exact neg_mem ha

end GlobalTheory.HatLatV

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalConjUnipotentRadicalIsotropicStatement
section
open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_conj_unipotentRadical_isotropic : ∀ (I : AutInst), ∀ γ ∈ I.GFset, ∀ W, I.IsIsot W → ∃ W', I.IsIsot W' ∧ ∀ m ∈ I.NA W', γ⁻¹ * m * γ ∈ I.NA W := by
  first | exact @GlobalTheory.CuspGeo.naconj | exact GlobalTheory.CuspGeo.naconj | (intros; apply GlobalTheory.CuspGeo.naconj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceCharacterConductorIntegersStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl ValuativeRel NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlaceCharacter_conductor_integers : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ) (χ : AddChar k Circle), IsStdChar D ψ (-1) → p.IsChar ψ χ → p.UnitAA → GlobalTheory.SplitWeil.HasConductor χ 1 := by
  first | exact @GlobalTheory.SplitCharCond.hasConductor_one | exact GlobalTheory.SplitCharCond.hasConductor_one | (intros; apply GlobalTheory.SplitCharCond.hasConductor_one <;> assumption)
end

