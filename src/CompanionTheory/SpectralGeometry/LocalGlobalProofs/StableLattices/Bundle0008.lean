import Mathlib
import GroundTheory.AutomorphicForms.Cartan
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.InhabitedFinite

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CartanExists
section
namespace GlobalTheory.CompanionTheory.Dblock.CartanDVR

open Matrix

theorem cartan_exists : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
    [Algebra R K] [IsFractionRing R K] (n : ℕ) (ϖ : R), Irreducible ϖ →
    ∀ g : Matrix (Fin n) (Fin n) K, IsUnit g.det →
      ∃ (u v : Matrix (Fin n) (Fin n) R) (a : Fin n → ℤ), IsUnit u.det ∧ IsUnit v.det ∧ Antitone a ∧
        g = u.map (algebraMap R K) * Matrix.diagonal (fun i => (algebraMap R K ϖ) ^ (a i)) *
          v.map (algebraMap R K) := by
  intro R K _ _ _ _ _ _ n ϖ hϖ g hg
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K

  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R)
    (fun p : Fin n × Fin n => g p.1 p.2)
  have hb0 : (b : R) ≠ 0 := nonZeroDivisors.ne_zero b.2
  choose A' hA' using hb
  let A : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => A' (i, j)
  have hAg : A.map (algebraMap R K) = algebraMap R K (b : R) • g := by
    ext i j
    simpa [A, Algebra.smul_def] using hA' (i, j)
  have hbK : algebraMap R K (b : R) ≠ 0 := fun h => hb0 (hinj (by simpa using h))
  have hA : A.det ≠ 0 := by
    intro h
    have h1 : (A.map (algebraMap R K)).det = 0 := by
      have := RingHom.map_det (algebraMap R K) A
      rw [h, map_zero] at this
      simpa using this.symm
    rw [hAg, Matrix.det_smul] at h1
    exact (mul_ne_zero (pow_ne_zero _ hbK) hg.ne_zero) h1
  obtain ⟨P, Q, e, he, hPQ⟩ := GroundTheory.Automorphic.Cartan.exists_eq_mul_diagonal_pow_mul hϖ A hA
  obtain ⟨c, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  have hϖK : algebraMap R K ϖ ≠ 0 := fun h => hϖ.ne_zero (hinj (by simpa using h))
  have hwK : algebraMap R K (w : R) ≠ 0 := fun h => w.ne_zero (hinj (by simpa using h))
  have hPd : IsUnit (P : Matrix (Fin n) (Fin n) R).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 P.isUnit
  have hQd : IsUnit (Q : Matrix (Fin n) (Fin n) R).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 Q.isUnit
  refine ⟨((w⁻¹ : Rˣ) : R) • (P : Matrix (Fin n) (Fin n) R), Q, fun i => (e i : ℤ) - c, ?_, hQd, ?_, ?_⟩
  · rw [Matrix.det_smul]
    exact ((Units.isUnit _).pow _).mul hPd
  · intro i j hij
    have := he hij
    simp only
    omega
  · have hwinv : algebraMap R K ((w⁻¹ : Rˣ) : R) = (algebraMap R K (w : R))⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← map_mul]
      simp
    have hdiag : Matrix.diagonal (fun i => (algebraMap R K ϖ) ^ ((e i : ℤ) - c)) =
        ((algebraMap R K ϖ) ^ c)⁻¹ • (Matrix.diagonal (fun i => ϖ ^ e i)).map (algebraMap R K) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [zpow_sub₀ hϖK, div_eq_mul_inv, mul_comm]
      · simp [Matrix.diagonal_apply_ne _ hij]
    have hmap : A.map (algebraMap R K) = (P : Matrix (Fin n) (Fin n) R).map (algebraMap R K) *
        (Matrix.diagonal (fun i => ϖ ^ e i)).map (algebraMap R K) *
        (Q : Matrix (Fin n) (Fin n) R).map (algebraMap R K) := by
      rw [hPQ]
      simp only [Matrix.map_mul]
    have hsm : (((w⁻¹ : Rˣ) : R) • (P : Matrix (Fin n) (Fin n) R)).map (algebraMap R K) =
        (algebraMap R K (w : R))⁻¹ • (P : Matrix (Fin n) (Fin n) R).map (algebraMap R K) := by
      ext i j
      simp [hwinv]
    rw [hsm, hdiag, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, smul_smul, ← hmap, hAg,
      smul_smul, hw]
    have : (algebraMap R K (w : R))⁻¹ * ((algebraMap R K ϖ) ^ c)⁻¹ *
        algebraMap R K ((w : R) * ϖ ^ c) = 1 := by
      rw [map_mul, map_pow]
      field_simp
    rw [this, one_smul]

end GlobalTheory.CompanionTheory.Dblock.CartanDVR
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.EntryMulSubOne
section
noncomputable section

open Matrix

namespace GlobalTheory.CompanionTheory.CartGL

variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {n : ℕ}

def IsUnif (p : Lˣ) : Prop := ‖(p : L)‖ < 1 ∧ ∀ x : L, x ≠ 0 → ∃ a : ℤ, ‖x‖ = ‖(p : L)‖ ^ a

theorem entry_mul {A B : Matrix (Fin n) (Fin n) L} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : ∀ i j, ‖A i j‖ ≤ a) (hB : ∀ i j, ‖B i j‖ ≤ b) (i j : Fin n) : ‖(A * B) i j‖ ≤ a * b := by
  rw [Matrix.mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg ha hb) fun l _ => ?_
  rw [norm_mul]
  exact mul_le_mul (hA i l) (hB l j) (norm_nonneg _) ha

theorem entry_mul_sub_one {A B : Matrix (Fin n) (Fin n) L} {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1)
    (hA : ∀ i j, ‖(A - 1) i j‖ ≤ r) (hB : ∀ i j, ‖(B - 1) i j‖ ≤ r) (i j : Fin n) :
    ‖(A * B - 1) i j‖ ≤ r := by
  have e : A * B - 1 = (A - 1) * (B - 1) + (A - 1) + (B - 1) := by noncomm_ring
  rw [e, Matrix.add_apply, Matrix.add_apply]
  have h := entry_mul h0 h0 hA hB i j
  have h2 : r * r ≤ r := by nlinarith
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (hB i j))
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h.trans h2) (hA i j))

variable (L n) in

def congK (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1) : Subgroup (GL (Fin n) L) where
  carrier := {k | ∀ i j, ‖((k : Matrix (Fin n) (Fin n) L) - 1) i j‖ ≤ r ∧
    ‖(((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - 1) i j‖ ≤ r}
  mul_mem' := by
    intro a b ha hb i j
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul]
      exact entry_mul_sub_one h0 h1 (fun i j => (ha i j).1) (fun i j => (hb i j).1) i j
    · rw [_root_.mul_inv_rev, Units.val_mul]
      exact entry_mul_sub_one h0 h1 (fun i j => (hb i j).2) (fun i j => (ha i j).2) i j
  one_mem' := by
    intro i j
    simp [h0]
  inv_mem' := by
    intro a ha i j
    simpa [and_comm] using ha i j

theorem mem_congK {r : ℝ} {h0 : 0 ≤ r} {h1 : r ≤ 1} {k : GL (Fin n) L} :
    k ∈ congK L n r h0 h1 ↔ ∀ i j, ‖((k : Matrix (Fin n) (Fin n) L) - 1) i j‖ ≤ r ∧
      ‖(((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - 1) i j‖ ≤ r := Iff.rfl

def dPow (p : Lˣ) (a : Fin n → ℤ) : GL (Fin n) L where
  val := diagonal fun i => ((p ^ a i : Lˣ) : L)
  inv := diagonal fun i => ((p ^ (-a i) : Lˣ) : L)
  val_inv := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    rw [← Units.val_mul, _root_.zpow_neg, mul_inv_cancel, Units.val_one]
  inv_val := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    rw [← Units.val_mul, _root_.zpow_neg, inv_mul_cancel, Units.val_one]

theorem dPow_val (p : Lˣ) (a : Fin n → ℤ) :
    ((dPow p a : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = diagonal fun i => ((p ^ a i : Lˣ) : L) := rfl

theorem dPow_add (p : Lˣ) (a b : Fin n → ℤ) : (dPow p (a + b) : GL (Fin n) L) = dPow p a * dPow p b := by
  apply Units.ext
  rw [Units.val_mul, dPow_val, dPow_val, dPow_val, diagonal_mul_diagonal]
  congr 1
  funext i
  rw [Pi.add_apply, _root_.zpow_add, Units.val_mul]

theorem dPow_zero (p : Lˣ) : (dPow p (0 : Fin n → ℤ) : GL (Fin n) L) = 1 := by
  apply Units.ext
  simp [dPow_val]

def tExp (n : ℕ) (i : Fin (n + 2)) : Fin n → ℤ :=
  fun j => if (i : ℕ) = n + 1 then -1 else if (j : ℕ) < i then 1 else 0

def tGen (p : Lˣ) (i : Fin (n + 2)) : GL (Fin n) L := dPow p (tExp n i)

end GlobalTheory.CompanionTheory.CartGL
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FixedVectorStatement
section
open CompanionTheory.Rg.Fl

namespace GlobalTheory.CompanionTheory.RgFl

theorem exists_least_norm_unique {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {C : Set E} (hne : C.Nonempty) (hcl : IsClosed C) (hconv : Convex ℝ C) :
    ∃ u ∈ C, ∀ w ∈ C, ‖u‖ ≤ ‖w‖ ∧ (‖w‖ ≤ ‖u‖ → w = u) := by
  obtain ⟨u, hu, hmin⟩ :=
    exists_norm_eq_iInf_of_complete_convex hne hcl.isComplete hconv (0 : E)
  have hin := (norm_eq_iInf_iff_real_inner_le_zero hconv hu).1 hmin
  refine ⟨u, hu, fun w hw => ?_⟩
  have h1 := hin w hw
  have h3 : inner ℝ (0 - u) (w - u) = ‖u‖ ^ 2 - inner ℝ w u := by
    rw [zero_sub, inner_neg_left, inner_sub_right, real_inner_self_eq_norm_sq,
      real_inner_comm w u]
    ring
  have h2 : ‖w - u‖ ^ 2 = ‖w‖ ^ 2 - 2 * inner ℝ w u + ‖u‖ ^ 2 := norm_sub_sq_real w u
  have h4 : inner ℝ w u ≤ ‖w‖ * ‖u‖ := real_inner_le_norm w u
  have h5 : ‖u‖ ^ 2 ≤ ‖w‖ * ‖u‖ := by linarith
  constructor
  · rcases (norm_nonneg u).eq_or_lt with h0 | h0
    · rw [← h0]; exact norm_nonneg w
    · nlinarith
  · intro hle
    have h6 : ‖w‖ ^ 2 ≤ ‖u‖ ^ 2 := by
      have := norm_nonneg w
      nlinarith
    have h7 : ‖w - u‖ ^ 2 ≤ 0 := by nlinarith
    have h8 : ‖w - u‖ = 0 := by
      have := norm_nonneg (w - u)
      nlinarith
    exact sub_eq_zero.1 (norm_eq_zero.1 h8)

theorem stFixVec : StFixVec := by
  intro G H _ _ _ _ _ _ _ σ hiso hcont
  obtain ⟨x, hx⟩ := exists_ne (0 : H)
  obtain ⟨v, hv⟩ : ∃ v : H, ‖v‖ = 1 :=
    ⟨((‖x‖ : ℂ)⁻¹) • x, by
      have : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
      simp [norm_smul, this]⟩
  have hopen : IsOpen {g : G | ‖σ g v - v‖ < 1 / 2} :=
    isOpen_lt (((hcont v).sub continuous_const).norm) continuous_const
  have hone : (1 : G) ∈ {g : G | ‖σ g v - v‖ < 1 / 2} := by simp
  obtain ⟨V, hV⟩ := NonarchimedeanGroup.is_nonarchimedean _ (hopen.mem_nhds hone)
  letI : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  set A : Set H := Set.range (fun k : V => σ (k : G) v) with hA
  set C : Set H := closure (convexHull ℝ A) with hC
  have hvA : v ∈ A := ⟨1, by simp⟩
  have hCne : C.Nonempty := ⟨v, subset_closure (subset_convexHull ℝ A hvA)⟩
  have hCconv : Convex ℝ C := (convex_convexHull ℝ A).closure
  have hCball : C ⊆ Metric.closedBall v (1 / 2) := by
    refine closure_minimal (convexHull_min ?_ (convex_closedBall _ _)) Metric.isClosed_closedBall
    rintro _ ⟨k, rfl⟩
    have := hV k.2
    simp only [Set.mem_setOf_eq] at this
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact this.le
  have hstable : ∀ k : V, ∀ y ∈ C, σ (k : G) y ∈ C := by
    intro k y hy
    have hmaps : Set.MapsTo (σ (k : G)) (convexHull ℝ A) (convexHull ℝ A) := by
      have hconvpre : Convex ℝ ((σ (k : G)).toLinearMap.restrictScalars ℝ ⁻¹' convexHull ℝ A) :=
        (convex_convexHull ℝ A).linear_preimage _
      have hsub : A ⊆ (σ (k : G)).toLinearMap.restrictScalars ℝ ⁻¹' convexHull ℝ A := by
        rintro _ ⟨l, rfl⟩
        refine subset_convexHull ℝ A ⟨k * l, ?_⟩
        simp
      exact fun z hz => convexHull_min hsub hconvpre hz
    exact map_mem_closure (σ (k : G)).continuous hy hmaps
  obtain ⟨u, huC, hu⟩ := exists_least_norm_unique hCne isClosed_closure hCconv
  refine ⟨V.toSubgroup, u, V.isOpen, ?_, ?_⟩
  · rintro rfl
    have := hCball huC
    rw [Metric.mem_closedBall, dist_eq_norm, zero_sub, norm_neg, hv] at this
    norm_num at this
  · intro k hk
    exact (hu _ (hstable ⟨k, hk⟩ u huC)).2 (hiso k u).le

end GlobalTheory.CompanionTheory.RgFl
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HeckeOperatorsSpanAndFaithful
section
open CompanionTheory.Rg.Fl

noncomputable section

namespace GlobalTheory.CompanionTheory.HeckeBasis

variable {G : Type} [Group G] (K : Subgroup G)

theorem lam_single (g : G) (y : G ⧸ K) (c : ℂ) :
    lam K g (Finsupp.single y c) = Finsupp.single (g • y) c := by
  simp [lam, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

theorem lam_mul (g g' : G) (u : (G ⧸ K) →₀ ℂ) :
    lam K (g * g') u = lam K g (lam K g' u) := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | single y c => simp [lam_single, mul_smul]

theorem lam_one (u : (G ⧸ K) →₀ ℂ) : lam K 1 u = u := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | single y c => simp [lam_single]

theorem lam_apply_smul (g : G) (u : (G ⧸ K) →₀ ℂ) (y : G ⧸ K) :
    lam K g u (g • y) = u y :=
  Finsupp.mapDomain_apply (MulAction.injective g) u y

def IsFixed (u : (G ⧸ K) →₀ ℂ) : Prop := ∀ k ∈ K, lam K k u = u

variable {K}

theorem lam_congr {u : (G ⧸ K) →₀ ℂ} (hu : IsFixed K u) {x x' : G}
    (h : (x : G ⧸ K) = x') : lam K x u = lam K x' u := by
  have hk : x⁻¹ * x' ∈ K := QuotientGroup.eq.1 h
  have : x' = x * (x⁻¹ * x') := by group
  rw [this, lam_mul, hu _ hk]

variable (K)

def op (u : (G ⧸ K) →₀ ℂ) : Module.End ℂ ((G ⧸ K) →₀ ℂ) :=
  Finsupp.lsum ℂ fun y => LinearMap.toSpanSingleton ℂ _ (lam K (Quotient.out y) u)

theorem op_single_out (u : (G ⧸ K) →₀ ℂ) (y : G ⧸ K) (c : ℂ) :
    op K u (Finsupp.single y c) = c • lam K (Quotient.out y) u := by
  simp [op, LinearMap.toSpanSingleton_apply]

variable {K}

theorem op_single {u : (G ⧸ K) →₀ ℂ} (hu : IsFixed K u) (x : G) (c : ℂ) :
    op K u (Finsupp.single (x : G ⧸ K) c) = c • lam K x u := by
  rw [op_single_out, lam_congr hu (QuotientGroup.out_eq' (x : G ⧸ K))]

theorem op_mem {u : (G ⧸ K) →₀ ℂ} (hu : IsFixed K u) : op K u ∈ Hk K := by
  rw [Hk, Subalgebra.mem_centralizer_iff]
  rintro _ ⟨g, rfl⟩
  refine Finsupp.lhom_ext' fun y => LinearMap.ext_ring ?_
  induction y using QuotientGroup.induction_on with
  | H x =>
    have hgx : g • (x : G ⧸ K) = ((g * x : G) : G ⧸ K) := rfl
    simp only [Finsupp.lsingle_apply, Module.End.mul_apply, LinearMap.comp_apply]
    rw [op_single hu, lam_single, hgx, op_single hu, lam_mul]
    simp

variable (K)

def delta : (G ⧸ K) →₀ ℂ := Finsupp.single ((1 : G) : G ⧸ K) 1

theorem lam_delta (x : G) : lam K x (delta K) = Finsupp.single (x : G ⧸ K) 1 := by
  have : x • ((1 : G) : G ⧸ K) = (x : G ⧸ K) := by
    change ((x * 1 : G) : G ⧸ K) = x
    rw [mul_one]
  rw [delta, lam_single, this]

theorem delta_fixed_eval (h : Hk K) : IsFixed K ((h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (delta K)) := by
  intro k hk
  have hc : lam K k * (h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) = (h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) * lam K k :=
    (Subalgebra.mem_centralizer_iff ℂ).1 h.2 _ ⟨k, rfl⟩
  have hd : lam K k (delta K) = delta K := by
    have hk1 : (k : G ⧸ K) = ((1 : G) : G ⧸ K) :=
      QuotientGroup.eq.2 (by simpa using K.inv_mem hk)
    rw [lam_delta, delta, hk1]
  have := LinearMap.congr_fun hc (delta K)
  simp only [Module.End.mul_apply] at this
  rw [this, hd]

variable {K}

theorem op_delta {u : (G ⧸ K) →₀ ℂ} (hu : IsFixed K u) : op K u (delta K) = u := by
  rw [delta, op_single hu, lam_one, one_smul]

theorem eq_zero_of_delta (h : Hk K)
    (h0 : (h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (delta K) = 0) : h = 0 := by
  apply Subtype.ext
  refine Finsupp.lhom_ext' fun y => LinearMap.ext_ring ?_
  induction y using QuotientGroup.induction_on with
  | H x =>
    have hc : lam K x * (h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) = (h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) * lam K x :=
      (Subalgebra.mem_centralizer_iff ℂ).1 h.2 _ ⟨x, rfl⟩
    have := LinearMap.congr_fun hc (delta K)
    simp only [Module.End.mul_apply] at this
    rw [h0, map_zero, lam_delta] at this
    simpa using this.symm

def orbitVec (hK : IsHeckePair K) (g : G) : (G ⧸ K) →₀ ℂ :=
  ∑ y ∈ (hK g).toFinset, Finsupp.single y (1 : ℂ)

open Classical in
theorem orbitVec_apply (hK : IsHeckePair K) (g : G) (z : G ⧸ K) :
    orbitVec hK g z = if z ∈ MulAction.orbit K (g : G ⧸ K) then 1 else 0 := by
  classical
  simp [orbitVec, Finsupp.finsetSum_apply, Finsupp.single_apply]

theorem lam_apply (k : G) (u : (G ⧸ K) →₀ ℂ) (z : G ⧸ K) :
    lam K k u z = u ((k⁻¹ : G) • z) := by
  have := lam_apply_smul K k u ((k⁻¹ : G) • z)
  rwa [smul_inv_smul] at this

theorem orbitVec_fixed (hK : IsHeckePair K) (g : G) : IsFixed K (orbitVec hK g) := by
  classical
  intro k hk
  ext z
  have hmem : ((k⁻¹ : G) • z ∈ MulAction.orbit K (g : G ⧸ K)) ↔
      z ∈ MulAction.orbit K (g : G ⧸ K) := by
    have e : (k⁻¹ : G) • z = (⟨k, hk⟩ : K)⁻¹ • z := rfl
    rw [e, ← MulAction.orbit_eq_iff, ← MulAction.orbit_eq_iff (a := z), MulAction.orbit_smul]
  rw [lam_apply, orbitVec_apply, orbitVec_apply]
  simp only [hmem]

theorem IsFixed.apply_of_mem_orbit {u : (G ⧸ K) →₀ ℂ} (hu : IsFixed K u) {x z : G ⧸ K}
    (hz : z ∈ MulAction.orbit K x) : u z = u x := by
  obtain ⟨k, rfl⟩ := hz
  have h := lam_apply_smul K (k : G) u x
  rw [hu _ k.2] at h
  exact h

def heckeOp (hK : IsHeckePair K) (g : G) : Hk K :=
  ⟨op K (orbitVec hK g), op_mem (orbitVec_fixed hK g)⟩

theorem heckeOp_delta (hK : IsHeckePair K) (g : G) :
    (heckeOp hK g : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (delta K) = orbitVec hK g :=
  op_delta (orbitVec_fixed hK g)

theorem exists_mem_span_delta (hK : IsHeckePair K) (n : ℕ) :
    ∀ u : (G ⧸ K) →₀ ℂ, IsFixed K u → u.support.card ≤ n →
      ∃ t ∈ Submodule.span ℂ (Set.range (heckeOp hK)),
        (t : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (delta K) = u := by
  classical
  induction n with
  | zero =>
    intro u _ hc
    have : u = 0 := by simpa using hc
    exact ⟨0, Submodule.zero_mem _, by simp [this]⟩
  | succ n ih =>
    intro u hu hc
    by_cases h0 : u = 0
    · exact ⟨0, Submodule.zero_mem _, by simp [h0]⟩
    obtain ⟨y, hy⟩ := Finsupp.support_nonempty_iff.2 h0
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    set c := u (g : G ⧸ K) with hcdef
    have hc0 : c ≠ 0 := Finsupp.mem_support_iff.1 hy
    have hfix : IsFixed K (u - c • orbitVec hK g) := by
      intro k hk
      rw [map_sub, map_smul, hu k hk, orbitVec_fixed hK g k hk]
    have hsub : (u - c • orbitVec hK g).support ⊆ u.support.erase (g : G ⧸ K) := by
      intro z hz
      have hz' := Finsupp.mem_support_iff.1 hz
      simp only [Finsupp.coe_sub, Finsupp.coe_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        orbitVec_apply] at hz'
      refine Finset.mem_erase.2 ⟨?_, ?_⟩
      · rintro rfl
        apply hz'
        simp [MulAction.mem_orbit_self, ← hcdef]
      · refine Finsupp.mem_support_iff.2 fun hzu => hz' ?_
        have hno : z ∉ MulAction.orbit K (g : G ⧸ K) := fun hm =>
          hc0 (by rw [hcdef, ← hu.apply_of_mem_orbit hm, hzu])
        simp [hzu, hno]
    have hcard : (u - c • orbitVec hK g).support.card ≤ n := by
      have := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem hy] at this
      omega
    obtain ⟨t, ht, hte⟩ := ih _ hfix hcard
    refine ⟨t + c • heckeOp hK g,
      Submodule.add_mem _ ht (Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)), ?_⟩
    have : ((t + c • heckeOp hK g : Hk K) : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (delta K) =
        (t : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (delta K) +
          c • (heckeOp hK g : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (delta K) := rfl
    rw [this, hte, heckeOp_delta]
    abel

theorem heckeBasis : ∀ (G : Type) [Group G] (K : Subgroup G), IsHeckePair K → ∃ T : G → Hk K, (∀ (g : G) (S : Finset (G ⧸ K)), (↑S : Set (G ⧸ K)) = MulAction.orbit K (g : G ⧸ K) → (T g : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (Finsupp.single ((1 : G) : G ⧸ K) 1) = ∑ y ∈ S, Finsupp.single y (1 : ℂ)) ∧ Submodule.span ℂ (Set.range T) = ⊤ ∧ ∀ h : Hk K, (h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (Finsupp.single ((1 : G) : G ⧸ K) 1) = 0 → h = 0 := by
  intro G _ K hK
  refine ⟨heckeOp hK, ?_, ?_, fun h h0 => eq_zero_of_delta h h0⟩
  · intro g S hS
    have hSe : S = (hK g).toFinset := by
      ext z
      rw [Set.Finite.mem_toFinset, ← hS, Finset.mem_coe]
    have := heckeOp_delta hK g
    rw [orbitVec, ← hSe] at this
    exact this
  · rw [eq_top_iff]
    intro h _
    obtain ⟨t, ht, hte⟩ := exists_mem_span_delta hK _
      ((h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (delta K)) (delta_fixed_eval K h) le_rfl
    have : h - t = 0 := eq_zero_of_delta (h - t) (by
      have e : ((h - t : Hk K) : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (delta K) =
          (h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (delta K) -
            (t : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (delta K) := rfl
      rw [e, hte, sub_self])
    rw [sub_eq_zero.1 this]
    exact ht

end GlobalTheory.CompanionTheory.HeckeBasis
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.PairingStatement
section
open CompanionTheory.Rg.Fl

namespace GlobalTheory.CompanionTheory.HeckePair

theorem stPair : StPair := by
  intro G _ _ _ K hKo hKc g
  have : DiscreteTopology (G ⧸ K) := QuotientGroup.discreteTopology hKo
  have : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  have hcont : Continuous fun k : K => (((k : G) * g : G) : G ⧸ K) :=
    (QuotientGroup.continuous_mk (N := K)).comp (continuous_subtype_val.mul continuous_const)
  have hfin : (Set.range fun k : K => (((k : G) * g : G) : G ⧸ K)).Finite :=
    (isCompact_range hcont).finite_of_discrete
  refine hfin.subset ?_
  rintro _ ⟨k, rfl⟩
  exact ⟨k, rfl⟩

end GlobalTheory.CompanionTheory.HeckePair
end

