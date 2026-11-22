import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0541
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0516
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0490
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0525
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0538
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0518
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitOfClosure
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0252
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0539
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0129
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0330
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0331
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0519
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0474
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BdRpToBdR
import Formalism.SharpRestriction.LevelLetterCocycles.ProdOneSubPrimitiveRoots
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0540
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0476
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0492
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0404
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0482
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0499

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacobiTrudiAlternantExpansion
section
noncomputable section

open MvPolynomial Finset Equiv

namespace GlobalTheory.JSW

def antisymHExt {A : Type*} [CommRing A] (h : ℕ → A) (z : ℤ) : A :=
  if z < 0 then 0 else h z.toNat

def antisymMat {A : Type*} [CommRing A] (m : ℕ) (h : ℕ → A) (ν : Fin m → ℕ) :
    Matrix (Fin m) (Fin m) A :=
  Matrix.of fun i j => antisymHExt h ((ν j : ℤ) - staircase m i)

theorem alternant_eq_sum_perm {A : Type*} [CommRing A] (m : ℕ) (μ : Fin m → ℕ) :
    alternant A m μ = ∑ σ : Perm (Fin m),
      ((Perm.sign σ : ℤ) : MvPolynomial (Fin m) A) * ∏ i, X i ^ μ (σ i) := by
  rw [alternant, Matrix.det_apply']
  simp [Matrix.of_apply]

theorem antisym_shift_sum {A : Type*} [CommRing A] (m d : ℕ) (h : ℕ → A) (μ : Fin m → ℕ) :
    (∏ i, (X i : MvPolynomial (Fin m) A) ^ μ i) *
        ∑ k ∈ Finset.Nat.antidiagonalTuple m d, ∏ j, C (h (k j)) * X j ^ (k j) =
      ∑ ν ∈ Finset.Nat.antidiagonalTuple m (d + ∑ i, μ i),
        (∏ j, C (antisymHExt h ((ν j : ℤ) - μ j))) * ∏ j, (X j : MvPolynomial (Fin m) A) ^ ν j := by
  classical
  set F : (Fin m → ℕ) → MvPolynomial (Fin m) A :=
    fun ν => (∏ j, C (antisymHExt h ((ν j : ℤ) - μ j))) * ∏ j, X j ^ ν j with hF
  have key : ∀ k : Fin m → ℕ, (∏ i, (X i : MvPolynomial (Fin m) A) ^ μ i) *
      ∏ j, C (h (k j)) * X j ^ (k j) = F (k + μ) := by
    intro k
    simp only [hF]
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    have e : (((k + μ) j : ℕ) : ℤ) - μ j = k j := by simp
    rw [e, antisymHExt, if_neg (not_lt.2 (Int.natCast_nonneg _)), Int.toNat_natCast, Pi.add_apply, pow_add]
    ring
  rw [Finset.mul_sum, Finset.sum_congr rfl fun k _ => key k]
  rw [← Finset.sum_image (g := fun k => k + μ) (by intro a _ b _ hab; exact add_right_cancel hab)]
  apply Finset.sum_subset
  · intro ν hν
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hν
    rw [Finset.Nat.mem_antidiagonalTuple] at hk ⊢
    simp [Finset.sum_add_distrib, hk]
  · intro ν hν hnot
    by_cases hle : ∀ j, μ j ≤ ν j
    · exfalso
      apply hnot
      refine Finset.mem_image.2 ⟨ν - μ, ?_, ?_⟩
      · rw [Finset.Nat.mem_antidiagonalTuple] at hν ⊢
        have : ∑ i, (ν - μ) i + ∑ i, μ i = ∑ i, ν i := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => Nat.sub_add_cancel (hle i)
        omega
      · funext j
        simp [Nat.sub_add_cancel (hle j)]
    · push_neg at hle
      obtain ⟨j, hj⟩ := hle
      simp only [hF]
      rw [Finset.prod_eq_zero (Finset.mem_univ j), zero_mul]
      rw [antisymHExt, if_pos (by omega), map_zero]

theorem antisym_lhs_eq {A : Type*} [CommRing A] (m d : ℕ) (h : ℕ → A) :
    alternant A m (staircase m) *
        ∑ k ∈ Finset.Nat.antidiagonalTuple m d, ∏ j, C (h (k j)) * X j ^ (k j) =
      ∑ ν ∈ Finset.Nat.antidiagonalTuple m (d + ∑ i, staircase m i),
        C (antisymMat m h ν).det * ∏ j, (X j : MvPolynomial (Fin m) A) ^ ν j := by
  rw [alternant_eq_sum_perm, Finset.sum_mul]
  have hσ : ∀ σ : Perm (Fin m), ((Perm.sign σ : ℤ) : MvPolynomial (Fin m) A) *
      (∏ i, X i ^ staircase m (σ i)) *
        ∑ k ∈ Finset.Nat.antidiagonalTuple m d, ∏ j, C (h (k j)) * X j ^ (k j) =
      ∑ ν ∈ Finset.Nat.antidiagonalTuple m (d + ∑ i, staircase m i),
        (((Perm.sign σ : ℤ) : MvPolynomial (Fin m) A) *
          ∏ j, C (antisymHExt h ((ν j : ℤ) - staircase m (σ j)))) * ∏ j, (X j : MvPolynomial (Fin m) A) ^ ν j := by
    intro σ
    rw [mul_assoc, antisym_shift_sum m d h (fun i => staircase m (σ i)),
      Equiv.sum_comp σ (staircase m), Finset.mul_sum]
    exact Finset.sum_congr rfl fun ν _ => by ring
  rw [Finset.sum_congr rfl fun σ _ => hσ σ, Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [← Finset.sum_mul, Matrix.det_apply', map_sum]
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_mul, map_intCast, map_prod]
  rfl

theorem antisymMat_comp_perm {A : Type*} [CommRing A] (m : ℕ) (h : ℕ → A) (μ : Fin m → ℕ)
    (τ : Perm (Fin m)) :
    (antisymMat m h (fun i => μ (τ i))).det = (Perm.sign τ : ℤ) * (antisymMat m h μ).det := by
  rw [← Matrix.det_permute']
  rfl

theorem antisymMat_staircase {A : Type*} [CommRing A] (m : ℕ) (h : ℕ → A) (l : Fin m → ℕ) :
    (antisymMat m h (fun i => l i + staircase m i)).det = jtDet m h l := by
  rw [jtDet, ← Matrix.det_transpose]
  congr 1
  ext i j
  have hi := i.2
  have hj := j.2
  have e : (((l i + staircase m i : ℕ)) : ℤ) - (staircase m j : ℕ) = (l i : ℤ) - i + j := by
    simp only [staircase]
    omega
  simp only [antisymMat, Matrix.of_apply, Matrix.transpose_apply, antisymHExt]
  rw [e]

theorem antisym_strictAnti {m : ℕ} {l : Fin m → ℕ} (hl : Antitone l) :
    StrictAnti (fun i => l i + staircase m i) := by
  intro i j hij
  have h1 := hl hij.le
  have h2 : (i : ℕ) < j := hij
  have := j.2
  simp only [staircase]
  omega

theorem antisym_gap {m : ℕ} {s : Fin m → ℕ} (hs : StrictAnti s) :
    ∀ (k : ℕ) (i j : Fin m), (j : ℕ) = i + k → s j + k ≤ s i := by
  first
  | exact @_root_.GlobalTheory.StrictAntiAddLe.add_le_of_strictAnti
  | exact _root_.GlobalTheory.StrictAntiAddLe.add_le_of_strictAnti
  | (apply _root_.GlobalTheory.StrictAntiAddLe.add_le_of_strictAnti <;> assumption)
  | (intros; apply _root_.GlobalTheory.StrictAntiAddLe.add_le_of_strictAnti <;> assumption)
  | (intros; apply @_root_.GlobalTheory.StrictAntiAddLe.add_le_of_strictAnti <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.StrictAntiAddLe.add_le_of_strictAnti ..)

open Classical in

theorem antisym_sum_sort {M : Type*} [AddCommMonoid M] (m d : ℕ) (g : (Fin m → ℕ) → M) :
    ∑ l ∈ antiParts m d, ∑ τ : Perm (Fin m), g (fun i => l (τ i) + staircase m (τ i)) =
      ∑ ν ∈ (Finset.Nat.antidiagonalTuple m (d + ∑ i, staircase m i)).filter Function.Injective, g ν := by
  rw [← Finset.sum_product']
  refine Finset.sum_bij (fun p _ => fun i => p.1 (p.2 i) + staircase m (p.2 i)) ?_ ?_ ?_ ?_
  · intro p hp
    obtain ⟨hl, -⟩ := Finset.mem_product.1 hp
    rw [mem_antiParts] at hl
    rw [Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple]
    refine ⟨?_, ?_⟩
    · rw [Equiv.sum_comp p.2 (fun i => p.1 i + staircase m i), Finset.sum_add_distrib, hl.1]
    · exact (antisym_strictAnti hl.2).injective.comp p.2.injective
  · intro p hp q hq hpq
    obtain ⟨hl, -⟩ := Finset.mem_product.1 hp
    obtain ⟨hl', -⟩ := Finset.mem_product.1 hq
    rw [mem_antiParts] at hl hl'
    set ν : Fin m → ℕ := fun i => p.1 (p.2 i) + staircase m (p.2 i) with hν
    have hν' : ν = fun i => q.1 (q.2 i) + staircase m (q.2 i) := hpq
    have a1 : Antitone (ν ∘ p.2.symm) := by
      have : ν ∘ p.2.symm = fun i => p.1 i + staircase m i := by funext i; simp [hν]
      rw [this]; exact (antisym_strictAnti hl.2).antitone
    have a2 : Antitone (ν ∘ q.2.symm) := by
      have : ν ∘ q.2.symm = fun i => q.1 i + staircase m i := by funext i; simp [hν']
      rw [this]; exact (antisym_strictAnti hl'.2).antitone
    have u := Tuple.unique_antitone a1 a2
    have hinj : Function.Injective ν := (antisym_strictAnti hl.2).injective.comp p.2.injective
    have hperm : p.2.symm = q.2.symm := Equiv.ext fun i => hinj (congrFun u i)
    have h2 : p.2 = q.2 := by simpa using congrArg Equiv.symm hperm
    have h1 : p.1 = q.1 := by
      funext i
      have := congrFun hν' (p.2.symm i)
      simp only [hν, h2, Equiv.apply_symm_apply] at this
      omega
    exact Prod.ext h1 h2
  · intro ν hν
    rw [Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple] at hν
    obtain ⟨hsum, hinj⟩ := hν
    set σ := Tuple.sort (fun i => OrderDual.toDual (ν i)) with hσ
    have hanti : Antitone (ν ∘ σ) := by
      have := Tuple.monotone_sort (fun i => OrderDual.toDual (ν i))
      exact monotone_toDual_comp_iff.1 this
    have hs : StrictAnti (ν ∘ σ) := hanti.strictAnti_of_injective (hinj.comp σ.injective)
    have hδ : ∀ i, staircase m i ≤ ν (σ i) := by
      intro i
      have hm : m - 1 < m := by have := i.2; omega
      have := antisym_gap hs (m - 1 - i) i ⟨m - 1, hm⟩ (by simp; have := i.2; omega)
      simp only [staircase, Function.comp] at this ⊢
      omega
    refine ⟨(fun i => ν (σ i) - staircase m i, σ.symm), ?_, ?_⟩
    · refine Finset.mem_product.2 ⟨?_, Finset.mem_univ _⟩
      rw [mem_antiParts]
      refine ⟨?_, ?_⟩
      · show ∑ i, (ν (σ i) - staircase m i) = d
        have e : ∑ i, (ν (σ i) - staircase m i) + ∑ i, staircase m i = ∑ i, ν (σ i) := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => Nat.sub_add_cancel (hδ i)
        rw [Equiv.sum_comp σ ν] at e
        omega
      · intro i j hij
        have g := antisym_gap hs (j - i) i j (by have : (i : ℕ) ≤ j := hij; omega)
        have h1 := hδ i
        have h2 := hδ j
        simp only [staircase, Function.comp] at g h1 h2 ⊢
        have := j.2
        have : (i : ℕ) ≤ j := hij
        omega
    · funext i
      have := hδ (σ.symm i)
      simp only [Equiv.apply_symm_apply] at this ⊢
      omega
  · intro p _
    rfl

theorem alternant_staircase_mul_antidiagonal {A : Type} [CommRing A] (m d : ℕ) (h : ℕ → A) :
    alternant A m (staircase m) *
        ∑ k ∈ Finset.Nat.antidiagonalTuple m d, ∏ j, MvPolynomial.C (h (k j)) * MvPolynomial.X j ^ (k j) =
      ∑ l ∈ antiParts m d,
        MvPolynomial.C (jtDet m h l) * alternant A m (fun i => l i + staircase m i) := by
  classical
  rw [antisym_lhs_eq]
  have hr : ∀ l : Fin m → ℕ, C (jtDet m h l) * alternant A m (fun i => l i + staircase m i) =
      ∑ τ : Perm (Fin m), (fun ν : Fin m → ℕ =>
        C (antisymMat m h ν).det * ∏ j, (X j : MvPolynomial (Fin m) A) ^ ν j)
        (fun i => l (τ i) + staircase m (τ i)) := by
    intro l
    rw [alternant_eq_sum_perm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    have e := antisymMat_comp_perm m h (fun i => l i + staircase m i) τ
    simp only at e ⊢
    rw [e, antisymMat_staircase, map_mul, map_intCast]
    ring
  rw [Finset.sum_congr rfl fun l _ => hr l, antisym_sum_sort m d
    (fun ν : Fin m → ℕ => C (antisymMat m h ν).det * ∏ j, (X j : MvPolynomial (Fin m) A) ^ ν j)]
  symm
  apply Finset.sum_filter_of_ne
  intro ν _ hne
  by_contra hni
  apply hne
  obtain ⟨a, b, hab, hne'⟩ : ∃ a b, ν a = ν b ∧ a ≠ b := by
    simp only [Function.Injective, not_forall] at hni
    obtain ⟨a, b, hab, hne⟩ := hni
    exact ⟨a, b, hab, hne⟩
  rw [Matrix.det_zero_of_column_eq hne' (fun k => by simp [antisymMat, hab]), map_zero, zero_mul]

example : alternant ℤ 2 (staircase 2) *
    ∑ k ∈ Finset.Nat.antidiagonalTuple 2 1, ∏ j, MvPolynomial.C ((k j : ℤ) + 1) * MvPolynomial.X j ^ (k j) =
      ∑ l ∈ antiParts 2 1, MvPolynomial.C (jtDet 2 (fun k => (k : ℤ) + 1) l) *
        alternant ℤ 2 (fun i => l i + staircase 2 i) :=
  alternant_staircase_mul_antidiagonal 2 1 (fun k => (k : ℤ) + 1)

end GlobalTheory.JSW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KummerTowerGaloisPreservesBreuilKisinModule
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.GKinfStable
variable {l : ℕ} [hl : Fact l.Prime]

theorem map_field_le (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (he : e + 1 = l ^ a) (g : GQ l)
    {x : Om l} (hx : x ∈ (ϖ.field a).1) : g x ∈ (ϖ.field a).1 := by
  have hd : e ∣ l ^ a - 1 := ⟨1, by omega⟩
  have := ϖ.isGalois_field a hd
  exact (IntermediateField.normal_iff_forall_map_le'.1 inferInstance g) ⟨x, hx, rfl⟩

theorem conj_mem (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (he : e + 1 = l ^ a) (g : GQ l) :
    ∀ h ∈ GK (ϖ.field a), g⁻¹ * h * g ∈ GK (ϖ.field a) := by
  intro h hh
  refine (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => ?_
  have h1 := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hh (g x) (map_field_le a e ϖ he g hx)
  simp only [AlgEquiv.mul_apply, h1]
  rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]

theorem res_exists (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (he : e + 1 = l ^ a) (g : GQ l) :
    ∃ σ : ↥(OL (ϖ.field a)) →+* ↥(OL (ϖ.field a)),
      ∀ x, (((σ x : ↥(ϖ.field a).1) : Om l)) = g ((x : ↥(ϖ.field a).1) : Om l) := by
  let F := (ϖ.field a).1
  let φ : ↥F →ₐ[ℚ_[l]] ↥F :=
    { toFun := fun y => ⟨g y, map_field_le a e ϖ he g y.2⟩
      map_one' := Subtype.ext (map_one g : g (1 : Om l) = 1)
      map_mul' := fun y z => Subtype.ext (map_mul g (y : Om l) (z : Om l))
      map_zero' := Subtype.ext (map_zero g : g (0 : Om l) = 0)
      map_add' := fun y z => Subtype.ext (map_add g (y : Om l) (z : Om l))
      commutes' := fun q => Subtype.ext (g.commutes q) }
  refine ⟨{ toFun := fun x => ⟨φ x, x.2.map (φ.restrictScalars ℤ_[l])⟩
            map_one' := Subtype.ext (map_one φ : φ (1 : ↥F) = 1)
            map_mul' := fun y z => Subtype.ext (map_mul φ (y : ↥F) (z : ↥F))
            map_zero' := Subtype.ext (map_zero φ : φ (0 : ↥F) = 0)
            map_add' := fun y z => Subtype.ext (map_add φ (y : ↥F) (z : ↥F)) }, fun x => rfl⟩

theorem kappa_act {LL : FinExt l} (T : QLat LL) (g : Gl l) (z : letI := zlLat T; WCb l ⊗[ℤ_[l]] ↥T.L.T) :
    letI := zlLat T
    TWact (galOW (↥(OL LL)) (sQ l g)) T g (kappa T z) =
      kappa T (TensorProduct.map (galW l (sQ l g)).toLinearMap (actZ T g) z) := by
  letI := zlLat T
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul w x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem actZ_mul_apply {LL : FinExt l} (T : QLat LL) (g h : Gl l) (x : ↥T.L.T) :
    letI := zlLat T
    actZ T g (actZ T h x) = actZ T (g * h) x :=
  Subtype.ext (LinearMap.congr_fun (map_mul T.ρ g h) (x : T.V)).symm

theorem actZ_one_apply {LL : FinExt l} (T : QLat LL) (x : ↥T.L.T) :
    letI := zlLat T
    actZ T 1 x = x :=
  Subtype.ext (LinearMap.congr_fun (map_one T.ρ) (x : T.V))

end GlobalTheory.GKinfStable

open GlobalTheory.GKinfStable in

theorem GlobalTheory.GKinfStable.main : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T), IsBK (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) → ∀ (g : Gl l) (γ : TameGal ↥LL.1 l e a), Covers ↥LL.1 (thetaW a LL) ϖ (sQ l g) γ → ∀ v : ME P, v.1 ∈ P.M → ∃ v' : ME P, v'.1 ∈ P.M ∧ I.act (sQ l g) g (toW (thetaW a LL) ϖ P v) = toW (thetaW a LL) ϖ P v' := by
  intro BS l _ a e _ _ ϖ LL _ _ ι _ _ P T I hBK g γ hcov v hv
  have he : e + 1 = l ^ a := TameDescentExponentData.succ_eq (K := ↥LL.1)
  choose σ hσ using res_exists (l := l) a e ϖ he (sQ l g)
  choose ψ hψ using GlobalTheory.T.covers_tame_acts_ringEndo_wittPowerSeries a e ϖ LL (sQ l g) γ hcov
  choose H hH using GlobalTheory.T.breuilKisinPrism_galoisLift_isPrismHom a e ϖ (sQ l g) σ hσ ψ hψ
  letI := zlLat T
  obtain ⟨E, j, hR, hiff⟩ := hBK
  let ρg : ↥T.L.T ≃ₗ[ℤ_[l]] ↥T.L.T :=
    LinearEquiv.ofLinear (actZ T g) (actZ T g⁻¹)
      (LinearMap.ext fun x => (actZ_mul_apply T g g⁻¹ x).trans
        ((congrArg (fun k => actZ T k x) (mul_inv_cancel g)).trans (actZ_one_apply T x)))
      (LinearMap.ext fun x => (actZ_mul_apply T g⁻¹ g x).trans
        ((congrArg (fun k => actZ T k x) (inv_mul_cancel g)).trans (actZ_one_apply T x)))
  have hPR := GlobalTheory.T.realisesEtaleFCrystal_pullback_galois (ϖ.field a) E ↥T.L.T _ j hR (sQ l g) σ hσ
    (conj_mem (l := l) a e ϖ he (sQ l g)) ρg (fun h h' hh x => by
      have e2 : g * inclG (ϖ.field a) h' = inclG (ϖ.field a) h * g := by
        rw [show inclG (ϖ.field a) h' = g⁻¹ * inclG (ϖ.field a) h * g from Subtype.ext hh]
        group
      exact (actZ_mul_apply T g _ x).trans ((congrArg (fun k => actZ T k x) e2).trans
        (actZ_mul_apply T _ g x).symm))
  choose gH j' hgH hR' hj' using hPR
  have hBS := (BS l (ϖ.field a) (ainfObj _) (ainfId _) (isAinf_ainfObj _)).2 ↥T.L.T ↥T.L.T _ _
    (E.pullback σ) E j' j hR' hR LinearMap.id (fun _ _ => rfl)
  choose u hu using hBS.exists
  have hx := (hiff (I.j (toW (thetaW a LL) ϖ P v))).2 ⟨v.1, hv, rfl⟩
  choose x hx using hx
  have hm := (hiff (kappa T (j (E.tr (ϖ.toAinf a) (u.u (ϖ.prism a) (E.tr H x)))))).1 ⟨_, rfl⟩
  choose m' hm' hm'eq using hm
  have e1 : gH.comp (ϖ.toAinf a) = ((ϖ.toAinf a).restrict σ).comp H :=
    Hom.ext' (RingHom.ext fun y => by
      change gH.f (ϖ.ev a y) = ϖ.ev a (H.f y)
      rw [hH]
      exact (hgH _).trans (hψ y).symm)
  have key : TensorProduct.map (galW l (sQ l g)).toLinearMap (actZ T g) (j (E.tr (ϖ.toAinf a) x)) =
      j (E.tr (ϖ.toAinf a) (u.u (ϖ.prism a) (E.tr H x))) := by
    have h2 : j (u.u (ainfObj _) ((E.pullback σ).tr (ϖ.toAinf a) (E.tr H x))) =
        j' ((E.pullback σ).tr (ϖ.toAinf a) (E.tr H x)) := by
      refine (hu _).trans ?_
      exact LinearMap.lTensor_id_apply _ _ _
    refine (hj' (E.tr (ϖ.toAinf a) x)).symm.trans ?_
    refine Eq.trans ?_ ((congrArg j (u.u_tr (ϖ.toAinf a) (E.tr H x))).symm.trans h2).symm
    refine congrArg j' ?_
    refine ((E.tr_comp _ _ x).symm).trans ?_
    refine (congrArg (fun f => E.tr f x) e1).trans ?_
    exact E.tr_comp _ _ x
  refine ⟨⟨m', mem_ME_of_mem_M hm'⟩, hm', ?_⟩
  apply I.j.injective
  refine (Ident.j_act _ _ _ _).trans ?_
  refine Eq.trans ?_ hm'eq
  refine (congrArg (TWact (galOW (↥(OL LL)) (sQ l g)) T g) hx).trans ?_
  exact (kappa_act T g _).trans (congrArg _ key)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalIntegerSpanOfImageIsStableLatticeStatement
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual GlobalTheory.Pass.LocDual.OneX
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localIntegerSpanOfImage_is_stable_lattice : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (Xs : Set (D.nd.X i)) (hr : GoodR D.nd i r) {a : ℕ} (x : Fin a → ↥Xs)
    (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i))
    (hst : ∀ γ : GE D.nd, ∀ y ∈ Y, actK i r Xs x γ y ∈ Y), Y.FG →
    ∃ LY : Lattice (O := Br.OLL D.nbr i w hw) (XG i w hw r Xs hr x Y hst).ρ, LY.T = latY i w hw Y := by
  first | exact @GlobalTheory.Pass.LocDual.OneX.latY_lattice | exact GlobalTheory.Pass.LocDual.OneX.latY_lattice | (intros; apply GlobalTheory.Pass.LocDual.OneX.latY_lattice <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LubinTatePeriodConjRatioUnramifiedStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lubinTate_period_conj_ratio_unramified : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (s : ℕ), 0 < s → ∀ (x : P.R.B), IsUnit x → P.φB^[s] x = (l : P.R.B) * x → P.ιB x ∈ Fil P 1 → P.ιB x ∉ Fil P 2 → (∀ j, 0 < j → j < s → ev P j x ∈ Fil P 0 ∧ ev P j x ∉ Fil P 1) → ∀ g : GQ l, ∃ a : ↥(MaximalUnramifiedExtension l), fr l s a = a ∧ P.actQ g x = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B a * x := by
  first | exact @GlobalTheory.PMon.lt_period_conj_ratio | exact GlobalTheory.PMon.lt_period_conj_ratio | (intros; apply GlobalTheory.PMon.lt_period_conj_ratio <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanFiltrationZeroOfIntegralTensorLatticeStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_filtrationZero_of_integral_tensorLattice : ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [NormedAlgebra ℚ_[l] K] [Algebra O K] (T : LocLat (Gl l) ℚ_[l] K O) (C : GlobalTheory.MemLoc.Core l) (w : TW (OB l O) T), TWincl (iotaO O C) T w ∈ LinearMap.range (TWincl (dRO l O) T) → w ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} := by
  first | exact @GlobalTheory.BKGal.HatVal.mem_span_filD_zero_of_integral | exact GlobalTheory.BKGal.HatVal.mem_span_filD_zero_of_integral | (intros; apply GlobalTheory.BKGal.HatVal.mem_span_filD_zero_of_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemUnramifiedFieldOfMemMaxUnramifiedSupRootStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_unramifiedField_of_mem_maxUnramified_sup_root : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (n : ℕ) (x : Om l), x ∈ MaximalUnramifiedExtension l → x ∈ Kunr l a ⊔ IntermediateField.adjoin ℚ_[l] {ϖ.seq n} → x ∈ Kunr l a := by
  first | exact @GlobalTheory.KunrDisj.mem_Kunr_of_mem_Kur_of_mem_sup | exact GlobalTheory.KunrDisj.mem_Kunr_of_mem_Kur_of_mem_sup | (intros; apply GlobalTheory.KunrDisj.mem_Kunr_of_mem_Kur_of_mem_sup <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemWachNOfMapMemSaturatedStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_wachN_of_map_mem_saturated : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; ∀ (T₀ T₁ T₂ : Lt K LL) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsCrys ((D.loc l).PD K) T₀.ρ → IsCrys ((D.loc l).PD K) T₁.ρ → IsCrys ((D.loc l).PD K) T₂.ρ → IsSESLat (Qp := ℚ_[l]) ι π → ∀ x : W.DD T₀, W.map ι x ∈ W.N T₁ → x ∈ W.N T₀ := by
  first | exact @GlobalTheory.NL.KerSat.mem_N_of_map_mem | exact GlobalTheory.NL.KerSat.mem_N_of_map_mem | (intros; apply GlobalTheory.NL.KerSat.mem_N_of_map_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonodromyTrivialEverywhereStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Formalism.L2.Host GlobalTheory.Pst GlobalTheory.GalOfCusp GlobalTheory.TripleLocal GlobalTheory.TypeLeaf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monodromy_trivial_everywhere : ∀ (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut), FrobDense D → GalHodge D T → ∀ (σ : D.what₂.FT) (π : D.naut.CG D.R.r), D.nd.goodRow σ → D.naut.csd π → D.naut.ralg π → (∀ w, (∀ k, w ∉ placesOver D.host.E (D.host.g k)) → D.naut.unr (D.naut.locG π w)) → (∀ k v, D.nd.lab k σ v = D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG π (D.naut.plGw k v))) → ∀ w, D.naut.mono0 (D.naut.locG π w) := by
  first | exact @GlobalTheory.GoodRowMono.mono0_all | exact GlobalTheory.GoodRowMono.mono0_all | (intros; apply GlobalTheory.GoodRowMono.mono0_all <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MooreDeterminantEqUnramifiedMulPeriodStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mooreDeterminant_eq_unramified_mul_period : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (h : ℕ), 0 < h → ∀ a : Fin h → P.R.B, (∀ j, P.φB^[h] (a j) = (l : P.R.B) * a j) → (∀ (i : ℕ) j, ev P i (a j) ∈ Fil P 0) → (Matrix.of fun i j : Fin h => P.φB^[i] (a j)).det ≠ 0 → P.ιB (Matrix.of fun i j : Fin h => P.φB^[i] (a j)).det ∈ Fil P 1 → ∃ κ : ↥(MaximalUnramifiedExtension l), κ ≠ 0 ∧ (Matrix.of fun i j : Fin h => P.φB^[i] (a j)).det = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B κ * P.tB := by
  first | exact @GlobalTheory.PMon.mooreDeterminant_eq_unramified_mul_period_alt | exact GlobalTheory.PMon.mooreDeterminant_eq_unramified_mul_period_alt | (intros; apply GlobalTheory.PMon.mooreDeterminant_eq_unramified_mul_period_alt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MulMemCrystallinePrismDividedPowerFamiliesStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mul_mem_crystallinePrismDividedPowerFamilies : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ x ∈ QSet t K e, ∀ y ∈ QSet t K e, x * y ∈ QSet t K e := by
  first | exact @GlobalTheory.CrysPrism.mul_mem_QSet_of_mem | exact GlobalTheory.CrysPrism.mul_mem_QSet_of_mem | (intros; apply GlobalTheory.CrysPrism.mul_mem_QSet_of_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormEisensteinMulClosedDiscEqRpowStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_eisenstein_mul_closedDisc_eq_rpow : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ : ℝ≥0), bk.ρ₀ ≤ ρ → ρ < 1 → ∀ y : bk.DS ρ, ‖toDisc l (X : bk.S) ρ bk.E * y‖ = (ρ : ℝ) ^ bk.Ep.natDegree * ‖y‖ := by
  first | exact @GlobalTheory.BSP.BK.norm_toDisc_E_mul | exact GlobalTheory.BSP.BK.norm_toDisc_E_mul | (intros; apply GlobalTheory.BSP.BK.norm_toDisc_E_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiKernelKillingElementStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
open GlobalTheory.HodgeAt

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bdR_element_normalized_killing_phi_kernel : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (σ : GQ l) (L : FinExt l) [FiniteDimensional ℚ_[l] ↥L.1] (a : ℕ), ∃ e : ↥L.1 ⊗[ℚ_[l]] P.R.BdR, phiS P σ L e = 1 ∧ ∀ x : (Fin a → ↥L.1) ⊗[ℚ_[l]] P.R.BdR, PhiS P σ L a x = 0 → GlobalTheory.DRFil.sm ℚ_[l] P.R.BdR ↥L.1 (Fin a → ↥L.1) e x = 0 := by
  first | (exact @GlobalTheory.HodgeAt.exists_idem_phiS_ker) | (exact GlobalTheory.HodgeAt.exists_idem_phiS_ker) | (intros; apply GlobalTheory.HodgeAt.exists_idem_phiS_ker  <;> assumption)
end

