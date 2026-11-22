import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0002
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.BetaHSumSmulRight
section
set_option autoImplicit false

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.FormalCalc

section

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
  (k : Type) [CommRing k] [Algebra R k]

theorem dAct_mul (B : FB R d O) (a b : O) : dAct k B (a * b) = dAct k B a * dAct k B b := by
  ext i j
  simp only [dAct, FB.actK, coeff_map, Matrix.mul_apply]
  rw [B.A.mul_act]
  unfold comp1 ev
  rw [coeff_single_subst, Fintype.sum_prod_type, Fin.sum_univ_one, map_sum]
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul]
    rfl
  · rintro ⟨s, l⟩
    fin_cases s
    exact B.A.const b l

theorem betaH_eq_dotProduct (ξ η : (Fin d → k) × (Fin d → k)) :
    betaH k ξ η = η.2 ⬝ᵥ ξ.1 - ξ.2 ⬝ᵥ η.1 := by
  simp [betaH, dotProduct, Finset.sum_sub_distrib]

theorem betaH_OactH (B : FB R d O) (a : O) (ξ η : (Fin d → k) × (Fin d → k)) :
    betaH k (OactH k B a ξ) η = betaH k ξ (OactH k B (star a) η) := by
  simp only [betaH_eq_dotProduct, OactH, star_star, Matrix.mulVec_transpose,
    Matrix.dotProduct_mulVec]

theorem OactH_mul (B : FB R d O) (a b : O) (ξ : (Fin d → k) × (Fin d → k)) :
    OactH k B (a * b) ξ = OactH k B a (OactH k B b ξ) := by
  simp only [OactH, star_mul, dAct_mul, Matrix.transpose_mul, Matrix.mulVec_mulVec]

theorem betaH_sum_smul_left {ι : Type} (s : Finset ι) (c : ι → k)
    (v : ι → (Fin d → k) × (Fin d → k)) (η : (Fin d → k) × (Fin d → k)) :
    betaH k (∑ i ∈ s, c i • v i) η = ∑ i ∈ s, c i * betaH k (v i) η := by
  simp only [betaH_eq_dotProduct, Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd,
    dotProduct_sum, sum_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul, mul_sub,
    Finset.sum_sub_distrib]

theorem betaH_sum_smul_right {ι : Type} (s : Finset ι) (c : ι → k)
    (ξ : (Fin d → k) × (Fin d → k)) (v : ι → (Fin d → k) × (Fin d → k)) :
    betaH k ξ (∑ i ∈ s, c i • v i) = ∑ i ∈ s, c i * betaH k ξ (v i) := by
  simp only [betaH_eq_dotProduct, Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd,
    dotProduct_sum, sum_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul, mul_sub,
    Finset.sum_sub_distrib]

theorem betaH_sum_right {ι : Type} (s : Finset ι)
    (ξ : (Fin d → k) × (Fin d → k)) (v : ι → (Fin d → k) × (Fin d → k)) :
    betaH k ξ (∑ i ∈ s, v i) = ∑ i ∈ s, betaH k ξ (v i) := by
  simpa using betaH_sum_smul_right k s (fun _ => 1) ξ v

theorem OactH_sum_smul (B : FB R d O) (a : O) {ι : Type} (s : Finset ι) (c : ι → k)
    (v : ι → (Fin d → k) × (Fin d → k)) :
    OactH k B a (∑ i ∈ s, c i • v i) = ∑ i ∈ s, c i • OactH k B a (v i) := by
  refine Prod.ext ?_ ?_ <;>
  simp only [OactH, Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd,
    Matrix.mulVec_sum, Matrix.mulVec_smul]

end

theorem betaH_sesquilinear : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O]
    [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O),
    (∀ (a : O) ξ η, betaH k (OactH k B a ξ) η = betaH k ξ (OactH k B (star a) η)) ∧
    (∀ (a b : O) ξ, OactH k B (a * b) ξ = OactH k B a (OactH k B b ξ)) ∧
    (∀ (a b : O) ξ, OactH k B (a + b) ξ = OactH k B a ξ + OactH k B b ξ) ∧
    (∀ ξ, OactH k B 1 ξ = ξ) ∧
    ∀ (n n' : ℕ) (c : Fin n → k) (a : Fin n → O) (c' : Fin n' → k) (a' : Fin n' → O) ξ η,
      (∑ i, c i • OactH k B (a i) ξ = ξ) → (∑ i, c' i • OactH k B (a' i) η = η) →
      (∀ ζ, ∑ i, ∑ i', (c i * c' i') • OactH k B (star (a i) * a' i') ζ = 0) →
      betaH k ξ η = 0 := by
  intro R _ d O _ _ k _ _ _ B
  obtain ⟨hadd, hone⟩ := dAct_add_and_one R d O k B
  refine ⟨betaH_OactH k B, OactH_mul k B, fun a b ξ => ?_, fun ξ => ?_, ?_⟩
  · simp only [OactH, star_add, hadd, Matrix.transpose_add, Matrix.add_mulVec, Prod.mk_add_mk]
  · simp [OactH, hone]
  · intro n n' c a c' a' ξ η hξ hη h0
    have h1 : betaH k ξ η = ∑ i, c i * betaH k ξ (OactH k B (star (a i)) η) := by
      conv_lhs => rw [← hξ]
      rw [betaH_sum_smul_left]
      simp only [betaH_OactH]
    have h2 : ∀ i, OactH k B (star (a i)) η =
        ∑ i', c' i' • OactH k B (star (a i) * a' i') η := fun i => by
      conv_lhs => rw [← hη]
      rw [OactH_sum_smul]
      simp only [OactH_mul]
    have h3 : betaH k ξ (∑ i, ∑ i', (c i * c' i') • OactH k B (star (a i) * a' i') η) = 0 := by
      rw [h0]; simp [betaH]
    rw [h1, ← h3, betaH_sum_right]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h2, betaH_sum_smul_right, betaH_sum_smul_right, Finset.mul_sum]
    simp only [mul_assoc]

end GlobalTheory.FormalCalc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.DofIterSmulDir
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.DirScale

variable {R : Type} [CommRing R] {d : ℕ}

theorem dof_smul_dir (F : Fin d → PS R 2 d) (c : R) (u : Fin d → R) (f : PS R 1 d) :
    Dof F (c • u) f = C c * Dof F u f := by
  unfold Dof
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_assoc, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc]

theorem dof_iter_C_mul (F : Fin d → PS R 2 d) (u : Fin d → R) (n : ℕ) (r : R) (f : PS R 1 d) :
    (Dof F u)^[n] (C r * f) = C r * (Dof F u)^[n] f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, GE.dof_C_mul, ih]

theorem dof_iter_smul_dir (F : Fin d → PS R 2 d) (c : R) (u : Fin d → R) (n : ℕ) (f : PS R 1 d) :
    (Dof F (c • u))^[n] f = C (c ^ n) * (Dof F u)^[n] f := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, dof_smul_dir, dof_iter_C_mul,
      pow_succ, map_mul, mul_assoc]

theorem foldr_smul_dir (F : Fin d → PS R 2 d) {ι : Type} (c : ι → R) (u : ι → Fin d → R)
    (m : ι → ℕ) (f : PS R 1 d) (L : List ι) :
    L.foldr (fun l g => (Dof F (c l • u l))^[m l] g) f =
      C (L.map fun l => c l ^ m l).prod * L.foldr (fun l g => (Dof F (u l))^[m l] g) f := by
  induction L with
  | nil => simp
  | cons l L ih =>
    simp only [List.foldr_cons, List.map_cons, List.prod_cons]
    rw [ih, dof_iter_smul_dir, dof_iter_C_mul, map_mul, mul_assoc]

theorem dmonOf_smul_dir : ∀ (R : Type) [CommRing R] (d : ℕ) (F : Fin d → PS R 2 d) (ι : Type)
    [Fintype ι] (c : ι → R) (u : ι → Fin d → R) (m : ι →₀ ℕ) (f : PS R 1 d),
    DmonOf F (fun l => c l • u l) m f = C (∏ l, c l ^ m l) * DmonOf F u m f := by
  intro R _ d F ι _ c u m f
  unfold DmonOf
  have h : ((Finset.univ : Finset ι).toList.map fun l => c l ^ m l).prod = ∏ l, c l ^ m l :=
    Finset.prod_map_toList _ _
  rw [← h]
  exact foldr_smul_dir F c u (fun l => m l) f _

end GlobalTheory.DirScale
end
end

