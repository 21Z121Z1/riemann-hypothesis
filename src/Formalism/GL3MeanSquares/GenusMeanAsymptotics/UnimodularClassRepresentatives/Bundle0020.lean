import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0018
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsPrimitiveNorm
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0060

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsNeZeroOfIsLattice
section
open NumberField Module nonZeroDivisors

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.RankOne

open Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem exists_ne_zero_of_isLattice {A : Submodule (𝓞 K) K} (hA : Submodule.IsLattice K A) :
    ∃ a ∈ A, a ≠ 0 := by
  by_contra hne
  push_neg at hne
  have h2 : Submodule.span K (A : Set K) = ⊥ := by
    rw [Submodule.span_eq_bot]; exact hne
  have h3 : (1 : K) ∈ Submodule.span K (A : Set K) := by
    rw [hA.span_eq_top]; exact Submodule.mem_top
  rw [h2, Submodule.mem_bot] at h3
  exact one_ne_zero h3

theorem span_eq_top_of_ne_zero {A : Submodule (𝓞 K) K} {a : K} (ha : a ∈ A) (h0 : a ≠ 0) :
    Submodule.span K (A : Set K) = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  have hx : x = (x * a⁻¹) • a := by rw [smul_eq_mul, mul_assoc, inv_mul_cancel₀ h0, mul_one]
  rw [hx]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ha)

theorem isLattice_mul {A B : Submodule (𝓞 K) K} (hA : Submodule.IsLattice K A)
    (hB : Submodule.IsLattice K B) : Submodule.IsLattice K (A * B) := by
  obtain ⟨a, ha, ha0⟩ := exists_ne_zero_of_isLattice hA
  obtain ⟨b, hb, hb0⟩ := exists_ne_zero_of_isLattice hB
  exact ⟨hA.fg.mul hB.fg, span_eq_top_of_ne_zero (Submodule.mul_mem_mul ha hb) (mul_ne_zero ha0 hb0)⟩

theorem exists_inv {A : Submodule (𝓞 K) K} (hA : Submodule.IsLattice K A) :
    ∃ A' : Submodule (𝓞 K) K, Submodule.IsLattice K A' ∧ A' * A = 1 := by
  obtain ⟨a, ha, ha0⟩ := exists_ne_zero_of_isLattice hA
  let I : FractionalIdeal (𝓞 K)⁰ K := ⟨A, FractionalIdeal.isFractional_of_fg hA.fg⟩
  have hI : I ≠ 0 := by
    intro h
    have h' : a ∈ (I : Submodule (𝓞 K) K) := ha
    rw [h, FractionalIdeal.coe_zero, Submodule.mem_bot] at h'
    exact ha0 h'
  have hmul : ((I⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) * A = 1 := by
    have e := congrArg (fun J : FractionalIdeal (𝓞 K)⁰ K => (J : Submodule (𝓞 K) K))
      (inv_mul_cancel₀ hI)
    have e2 : ((I⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) * (I : Submodule (𝓞 K) K) = 1 := by
      simpa only [FractionalIdeal.coe_mul, FractionalIdeal.coe_one] using e
    exact e2
  refine ⟨_, ⟨FractionalIdeal.fg_of_isNoetherianRing le_rfl _, ?_⟩, hmul⟩
  have hne : ((I⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) ≠ ⊥ := by
    intro hb
    rw [hb, Submodule.bot_mul] at hmul
    have h1 : (1 : K) ∈ (1 : Submodule (𝓞 K) K) := Submodule.one_le.1 le_rfl
    rw [← hmul, Submodule.mem_bot] at h1
    exact one_ne_zero h1
  obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact span_eq_top_of_ne_zero hc hc0

def mulE (I J : Submodule (𝓞 K) K) (hJI : J * I = 1) :
    Submodule (𝓞 K) K ≃ Submodule (𝓞 K) K where
  toFun M := I * M
  invFun M := J * M
  left_inv M := by change J * (I * M) = M; rw [← mul_assoc, hJI, one_mul]
  right_inv M := by change I * (J * M) = M; rw [← mul_assoc, mul_comm I J, hJI, one_mul]

theorem gmap_mul (g : K ≃ₗ[K] K) (I M : Submodule (𝓞 K) K) : I * gmap g M = gmap g (I * M) := by
  have key : ∀ x y : K, g (x * y) = x * g y := fun x y => by
    simpa only [smul_eq_mul] using g.map_smul x y
  unfold gmap
  apply le_antisymm
  · refine Submodule.mul_le.2 fun i hi y hy => ?_
    obtain ⟨m, hm, rfl⟩ := Submodule.mem_map.1 hy
    refine Submodule.mem_map.2 ⟨i * m, Submodule.mul_mem_mul hi hm, ?_⟩
    simp only [LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, key]
  · refine Submodule.map_le_iff_le_comap.2 (Submodule.mul_le.2 fun i hi m hm => ?_)
    rw [Submodule.mem_comap]
    simp only [LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, key]
    exact Submodule.mul_mem_mul hi (Submodule.mem_map_of_mem hm)

theorem ne_zero_of_mem_hcompl {p : Ideal (𝓞 K)} (hp : p.IsMaximal) {s : 𝓞 K}
    (hs : s ∈ hcompl (K := K) p) : s ≠ 0 := by
  intro h0
  exact Formalism.HermitianLatticesTheory.genusBasic_hS (K := K) p hp s hs (by rw [h0]; exact p.zero_mem)

theorem loc_mul {p : Ideal (𝓞 K)} (hp : p.IsMaximal) (I M : Submodule (𝓞 K) K) :
    I * loc (K := K) p M = loc (K := K) p (I * M) := by
  apply le_antisymm
  · refine Submodule.mul_le.2 fun i hi y hy => ?_
    have hy' : ∃ s ∈ hcompl (K := K) p, s • y ∈ M := hy
    obtain ⟨s, hs, hsy⟩ := hy'
    show ∃ s ∈ hcompl (K := K) p, s • (i * y) ∈ I * M
    refine ⟨s, hs, ?_⟩
    have e : s • (i * y) = i * (s • y) := by rw [Algebra.smul_def, Algebra.smul_def]; ring
    rw [e]
    exact Submodule.mul_mem_mul hi hsy
  · intro x hx
    have hx' : ∃ s ∈ hcompl (K := K) p, s • x ∈ I * M := hx
    obtain ⟨s, hs, hsx⟩ := hx'
    have hs0 : algebraMap (𝓞 K) K s ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)]
      exact ne_zero_of_mem_hcompl hp hs
    have hle : I * M ≤ (I * loc (K := K) p M).comap
        (LinearMap.mulLeft (𝓞 K) (algebraMap (𝓞 K) K s)⁻¹) := by
      refine Submodule.mul_le.2 fun i hi m hm => ?_
      rw [Submodule.mem_comap, LinearMap.mulLeft_apply]
      have e : (algebraMap (𝓞 K) K s)⁻¹ * (i * m) = i * ((algebraMap (𝓞 K) K s)⁻¹ * m) := by ring
      rw [e]
      refine Submodule.mul_mem_mul hi ?_
      show ∃ t ∈ hcompl (K := K) p, t • ((algebraMap (𝓞 K) K s)⁻¹ * m) ∈ M
      refine ⟨s, hs, ?_⟩
      rw [Algebra.smul_def, ← mul_assoc, mul_inv_cancel₀ hs0, one_mul]
      exact hm
    have h2 := hle hsx
    rw [Submodule.mem_comap, LinearMap.mulLeft_apply, Algebra.smul_def, ← mul_assoc,
      inv_mul_cancel₀ hs0, one_mul] at h2
    exact h2

theorem form_eq (h : K →ₗ⋆[K] K →ₗ[K] K) (x y : K) : h x y = star x * y * h 1 1 := by
  rw [show h x y = h (x • (1 : K)) (y • (1 : K)) by simp only [smul_eq_mul, mul_one],
    LinearMap.map_smulₛₗ₂, LinearMap.map_smul, starRingEnd_apply]
  simp only [smul_eq_mul]
  ring

theorem mem_isom_iff {h : K →ₗ⋆[K] K →ₗ[K] K} (h1 : h 1 1 ≠ 0) (g : K ≃ₗ[K] K) :
    g ∈ isom h ↔ star (g 1) * g 1 = 1 := by
  have hg : ∀ x, g x = x * g 1 := fun x => by
    rw [show g x = g (x • (1 : K)) by rw [smul_eq_mul, mul_one], LinearEquiv.map_smul, smul_eq_mul]
  constructor
  · intro hm
    have hm' : ∀ x y, h (g x) (g y) = h x y := hm
    have e := hm' 1 1
    rw [form_eq h (g 1) (g 1)] at e
    exact mul_right_cancel₀ h1 (by rw [one_mul]; exact e)
  · intro he
    show ∀ x y, h (g x) (g y) = h x y
    intro x y
    rw [form_eq h (g x) (g y), form_eq h x y, hg x, hg y, star_mul']
    calc star x * star (g 1) * (y * g 1) * h 1 1 = star x * y * (star (g 1) * g 1) * h 1 1 := by ring
      _ = star x * y * h 1 1 := by rw [he, mul_one]

theorem mass_eq_of_lattices {h₁ h₂ : K →ₗ⋆[K] K →ₗ[K] K} (hn₁ : h₁ 1 1 ≠ 0) (hn₂ : h₂ 1 1 ≠ 0)
    {A B : Submodule (𝓞 K) K} (hA : Submodule.IsLattice K A) (hB : Submodule.IsLattice K B)
    (hex : ∃ s, IsClassReps h₁ A s) : mass h₂ B = mass h₁ A := by
  obtain ⟨A', hA', hA'A⟩ := exists_inv hA
  obtain ⟨B', hB', hB'B⟩ := exists_inv hB
  have hC : Submodule.IsLattice K (B * A') := isLattice_mul hB hA'
  have hJ : Submodule.IsLattice K (A * B') := isLattice_mul hA hB'
  have hJC : (A * B') * (B * A') = 1 := by
    calc (A * B') * (B * A') = (A' * A) * (B' * B) := by ring
      _ = 1 := by rw [hA'A, hB'B, one_mul]
  have t1 : ∀ g : K ≃ₗ[K] K, (Equiv.refl (K ≃ₗ[K] K)) g ∈ isom h₂ ↔ g ∈ isom h₁ := fun g => by
    rw [Equiv.refl_apply, mem_isom_iff hn₂, mem_isom_iff hn₁]
  have t2 : ∀ (g : K ≃ₗ[K] K) (M : Submodule (𝓞 K) K),
      mulE (B * A') (A * B') hJC (gmap g M) =
        gmap ((Equiv.refl (K ≃ₗ[K] K)) g) (mulE (B * A') (A * B') hJC M) := fun g M =>
    gmap_mul g (B * A') M
  have t3 : ∀ (p : Ideal (𝓞 K)), p.IsMaximal → ∀ (M : Submodule (𝓞 K) K),
      mulE (B * A') (A * B') hJC (loc p M) = loc p (mulE (B * A') (A * B') hJC M) :=
    fun p hp M => loc_mul hp (B * A') M
  have t4 : ∀ (M : Submodule (𝓞 K) K),
      Submodule.IsLattice K (mulE (B * A') (A * B') hJC M) ↔ Submodule.IsLattice K M := by
    intro M
    show Submodule.IsLattice K (B * A' * M) ↔ Submodule.IsLattice K M
    constructor
    · intro hM
      have e := isLattice_mul hJ hM
      rwa [← mul_assoc, hJC, one_mul] at e
    · intro hM
      exact isLattice_mul hC hM
  have hΦA : mulE (B * A') (A * B') hJC A = B := by
    show B * A' * A = B
    rw [mul_assoc, hA'A, mul_one]
  have he := (mass_transfer (mulE (B * A') (A * B') hJC) (Equiv.refl _) t1 t2 t3 t4 hex).2
  rw [hΦA] at he
  exact he

end Formalism.HermitianLattices.Ext.L3.RankOne
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsOrthTuple
section
noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.U0

open WA

variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]

def gram (h : V →ₗ⋆[K] V →ₗ[K] K) {n : ℕ} (x : Fin n → V) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => h (x i) (x j)

def spanS (S : Subring K) {n : ℕ} (x : Fin n → V) : Submodule S V :=
  Submodule.span S (Set.range x)

variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K}

theorem mem_spanS {n : ℕ} (x : Fin n → V) (i : Fin n) : x i ∈ spanS S x :=
  Submodule.subset_span ⟨i, rfl⟩

theorem smul_mem_spanS {n : ℕ} {x : Fin n → V} {c : K} (hc : c ∈ S) {v : V} (hv : v ∈ spanS S x) :
    c • v ∈ spanS S x :=
  (spanS S x).smul_mem (⟨c, hc⟩ : S) hv

theorem spanS_induction {n : ℕ} {x : Fin n → V} {p : V → Prop} (h0 : p 0)
    (hadd : ∀ a b, p a → p b → p (a + b)) (hsmul : ∀ c ∈ S, ∀ a, p a → p (c • a))
    (hx : ∀ i, p (x i)) : ∀ v ∈ spanS S x, p v := by
  first | exact UpperTheory.Reformulated.B.Qe24.spanS_induction .. | (apply UpperTheory.Reformulated.B.Qe24.spanS_induction <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qe24.spanS_induction <;> assumption) | (apply @UpperTheory.Reformulated.B.Qe24.spanS_induction <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qe24.spanS_induction <;> assumption) | (apply @UpperTheory.Reformulated.B.Qe24.spanS_induction <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qe24.spanS_induction K V ‹_› ‹_› ‹_› ‹_› S n x p h0 hadd hsmul hx v ‹_› | exact @UpperTheory.Reformulated.B.Qe24.spanS_induction K V ‹_› ‹_› ‹_› ‹_› S n x p h0 hadd hsmul hx v | exact @UpperTheory.Reformulated.B.Qe24.spanS_induction K V ‹_› ‹_› ‹_› ‹_› S n x p h0 hadd hsmul hx | exact @UpperTheory.Reformulated.B.Qe24.spanS_induction K V ‹_› ‹_› ‹_› ‹_› S n x p h0 hadd hsmul | exact @UpperTheory.Reformulated.B.Qe24.spanS_induction K V ‹_› ‹_› ‹_› ‹_› S n x p h0 hadd | exact @UpperTheory.Reformulated.B.Qe24.spanS_induction K V ‹_› ‹_› ‹_› ‹_› S n x p h0 | exact @UpperTheory.Reformulated.B.Qe24.spanS_induction K V ‹_› ‹_› ‹_› ‹_› S n x p | exact @UpperTheory.Reformulated.B.Qe24.spanS_induction K V ‹_› ‹_› ‹_› ‹_› S n x | exact @UpperTheory.Reformulated.B.Qe24.spanS_induction K V ‹_› ‹_› ‹_› ‹_› S n | exact @UpperTheory.Reformulated.B.Qe24.spanS_induction K V ‹_› ‹_› ‹_› ‹_› S | exact @UpperTheory.Reformulated.B.Qe24.spanS_induction K V ‹_› ‹_› ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qe24.spanS_induction K V ‹_› ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qe24.spanS_induction K V ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qe24.spanS_induction K V ‹_› | exact @UpperTheory.Reformulated.B.Qe24.spanS_induction K V | exact @UpperTheory.Reformulated.B.Qe24.spanS_induction K

theorem int_spanS (hS : IsHermSemilocal S) {n : ℕ} {x : Fin n → V}
    (hx : ∀ i j, h (x i) (x j) ∈ S) : ∀ a ∈ spanS S x, ∀ b ∈ spanS S x, h a b ∈ S := by
  intro a ha
  refine spanS_induction (by simp [S.zero_mem]) (fun b c hb hc => by
    rw [map_add]; exact S.add_mem hb hc) (fun c hc b hb => by
    rw [map_smul]; exact S.mul_mem hc hb) (fun j => ?_)
  revert a
  refine spanS_induction (by simp [S.zero_mem]) (fun b c hb hc => by
    rw [map_add, LinearMap.add_apply]; exact S.add_mem hb hc) (fun c hc b hb => by
    rw [map_smulₛₗ, LinearMap.smul_apply]; exact S.mul_mem (hS.star_mem _ hc) hb)
    (fun i => hx i j)

theorem exists_coeff {n : ℕ} {y : Fin n → V} {v : V} (hv : v ∈ spanS S y) :
    ∃ c : Fin n → S, v = ∑ j, (c j : K) • y j := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun S).mp hv
  exact ⟨c, hc.symm⟩

theorem gram_det_of_le (hS : IsHermSemilocal S) {n : ℕ} {x y : Fin n → V}
    (hxy : ∀ i, x i ∈ spanS S y) : ∃ c ∈ S, (gram h x).det = c * (gram h y).det := by
  choose T hT using fun i => exists_coeff (hxy i)
  have e : gram h x = ((S.subtype.mapMatrix (Matrix.of T)).map star) * gram h y *
      (S.subtype.mapMatrix (Matrix.of T)).transpose := by
    ext i l
    simp only [gram, Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply,
      RingHom.mapMatrix_apply, Subring.subtype_apply]
    conv_lhs => rw [hT i, hT l]
    simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply, RingHom.id_apply, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  have e2 : ((S.subtype.mapMatrix (Matrix.of T)).map star).det =
      star (S.subtype.mapMatrix (Matrix.of T)).det := by
    have := (starRingEnd K).map_det (S.subtype.mapMatrix (Matrix.of T))
    rw [starRingEnd_apply] at this
    rw [this]
    rfl
  have e3 : (S.subtype.mapMatrix (Matrix.of T)).det ∈ S := by
    rw [← RingHom.map_det]
    exact (Matrix.of T).det.2
  refine ⟨star (S.subtype.mapMatrix (Matrix.of T)).det * (S.subtype.mapMatrix (Matrix.of T)).det,
    S.mul_mem (hS.star_mem _ e3) e3, ?_⟩
  rw [e, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, e2]
  ring

theorem gram_det_cons (hs : h.IsSymm) {n : ℕ} (f : V) (x : Fin n → V) (hf : ∀ k, h f (x k) = 0) :
    (gram h (Fin.cons f x : Fin (n + 1) → V)).det = h f f * (gram h x).det := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  have h1 : ∀ i : Fin n, (-1 : K) ^ (i.succ : ℕ) * gram h (Fin.cons f x : Fin (n + 1) → V) i.succ 0 *
      ((gram h (Fin.cons f x : Fin (n + 1) → V)).submatrix i.succ.succAbove Fin.succ).det = 0 := by
    intro i
    have : gram h (Fin.cons f x : Fin (n + 1) → V) i.succ 0 = 0 := by
      simp only [gram, Matrix.of_apply, Fin.cons_succ, Fin.cons_zero]
      rw [← show star (h f (x i)) = h (x i) f from hs.eq f (x i), hf, star_zero]
    rw [this]
    ring
  rw [Finset.sum_eq_zero fun i _ => h1 i, add_zero]
  have h2 : (gram h (Fin.cons f x : Fin (n + 1) → V)).submatrix (Fin.succAbove 0) Fin.succ =
      gram h x := by
    ext i j
    simp [gram]
  rw [h2]
  simp [gram]

theorem gram_det_dv (hπ : IsUnif S π) {n : ℕ} (x : Fin (n + 2) → V)
    (hx : ∀ i j, Dv S π (h (x i) (x j))) : Dv S π ((gram h x).det * π⁻¹) := by
  have e : gram h x = π • S.subtype.mapMatrix
      (Matrix.of fun i j => (⟨h (x i) (x j) * π⁻¹, hx i j⟩ : S)) := by
    ext i j
    have := hπ.ne
    simp only [gram, Matrix.of_apply, Matrix.smul_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
      Subring.subtype_apply, smul_eq_mul]
    field_simp
  rw [e, Matrix.det_smul, ← RingHom.map_det, Fintype.card_fin]
  unfold Dv
  have e2 : ∀ d : K, π ^ (n + 2) * d * π⁻¹ * π⁻¹ = π ^ n * d := by
    intro d
    have := hπ.ne
    field_simp
    ring
  rw [e2]
  exact S.mul_mem (S.pow_mem hπ.mem n) (Subtype.mem _)

theorem exists_pivot (hS : IsHermSemilocal S) (hπ : IsUnif S π) (hs : h.IsSymm) {n : ℕ}
    (x : Fin (n + 1) → V) (hx : ∀ i j, h (x i) (x j) ∈ S)
    (hnd : ∃ i j, ¬ Dv S π (h (x i) (x j))) :
    ∃ i₀ : Fin (n + 1), ∃ r ∈ spanS S (x ∘ i₀.succAbove), IsUnitIn S (h (x i₀ + r) (x i₀ + r)) := by
  obtain ⟨i, j, hij⟩ := hnd
  by_cases h1 : IsUnitIn S (h (x i) (x i))
  · exact ⟨i, 0, Submodule.zero_mem _, by simpa using h1⟩
  by_cases h2 : IsUnitIn S (h (x j) (x j))
  · exact ⟨j, 0, Submodule.zero_mem _, by simpa using h2⟩
  have d1 := dv_of_not_unit hπ (hx i i) (hs.eq _ _) h1
  have d2 := dv_of_not_unit hπ (hx j j) (hs.eq _ _) h2
  have hne : j ≠ i := by
    rintro rfl
    exact hij d1
  obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hne
  obtain ⟨s, hsS, hs1⟩ := exists_trace_mul hS hπ (hx i j) hij S.one_mem (star_one K)
  refine ⟨i, s • x j, smul_mem_spanS hsS (by rw [← hk]; exact mem_spanS (x ∘ i.succAbove) k), ?_⟩
  have hji : h (x j) (x i) = star (h (x i) (x j)) := (hs.eq _ _).symm
  have e : h (x i + s • x j) (x i + s • x j) =
      1 + (star s * s * h (x j) (x j) + h (x i) (x i)) := by
    simp only [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hji,
      starRingEnd_apply, RingHom.id_apply]
    simp only [star_mul'] at hs1
    linear_combination hs1
  rw [e]
  exact unit_add_dv hπ isUnitIn_one
    ((d2.mul_left (S.mul_mem (hS.star_mem _ hsS) hsS)).add d1)

theorem spanS_cons {n : ℕ} (f : V) (y : Fin n → V) :
    spanS S (Fin.cons f y : Fin (n + 1) → V) = Submodule.span S {f} ⊔ spanS S y := by
  unfold spanS
  rw [Fin.range_cons, Submodule.span_insert]

theorem exists_orth_tuple (hS : IsHermSemilocal S) (hπ : IsUnif S π) (hs : h.IsSymm) :
    ∀ (n : ℕ) (x : Fin n → V), (∀ i j, h (x i) (x j) ∈ S) →
      ¬ Dv S π ((gram h x).det * π⁻¹) →
      ∃ y : Fin n → V, (∀ i j, i ≠ j → h (y i) (y j) = 0) ∧ spanS S y = spanS S x := by
  intro n
  induction n with
  | zero => exact fun x _ _ => ⟨x, fun i => i.elim0, rfl⟩
  | succ n ih =>
    intro x hx hdet
    by_cases hnd : ∃ i j, ¬ Dv S π (h (x i) (x j))
    · obtain ⟨i₀, r, hr, hu⟩ := exists_pivot hS hπ hs x hx hnd
      have hrx : r ∈ spanS S x :=
        Submodule.span_mono (Set.range_comp_subset_range _ _) hr
      have hint := int_spanS hS hx
      generalize hfdef : x i₀ + r = f at hu
      have hf : f ∈ spanS S x := by
        rw [← hfdef]; exact (spanS S x).add_mem (mem_spanS x i₀) hrx
      have hc : ∀ k, h f (x (i₀.succAbove k)) * (h f f)⁻¹ ∈ S := fun k =>
        S.mul_mem (hint f hf _ (mem_spanS x _)) hu.2.2
      let x' : Fin n → V := fun k =>
        x (i₀.succAbove k) - (h f (x (i₀.succAbove k)) * (h f f)⁻¹) • f
      have hx'mem : ∀ k, x' k ∈ spanS S x := fun k =>
        (spanS S x).sub_mem (mem_spanS x _) (smul_mem_spanS (hc k) hf)
      have hfx' : ∀ k, h f (x' k) = 0 := by
        intro k
        have := hu.1
        simp only [x', map_sub, map_smul, smul_eq_mul]
        field_simp
        ring
      have hf0 : f ∈ spanS S (Fin.cons f x' : Fin (n + 1) → V) :=
        mem_spanS (Fin.cons f x' : Fin (n + 1) → V) 0
      have hge1 : ∀ k, x (i₀.succAbove k) ∈ spanS S (Fin.cons f x' : Fin (n + 1) → V) := by
        intro k
        have h1 : x' k ∈ spanS S (Fin.cons f x' : Fin (n + 1) → V) :=
          mem_spanS (Fin.cons f x' : Fin (n + 1) → V) k.succ
        have h2 := Submodule.add_mem _ h1 (smul_mem_spanS (hc k) hf0)
        simpa only [x', sub_add_cancel] using h2
      have hge : ∀ i, x i ∈ spanS S (Fin.cons f x' : Fin (n + 1) → V) := by
        intro i
        rcases Fin.eq_self_or_eq_succAbove i₀ i with rfl | ⟨k, rfl⟩
        · have h1 : r ∈ spanS S (Fin.cons f x' : Fin (n + 1) → V) := by
            refine (Submodule.span_le.mpr ?_) hr
            rintro _ ⟨k, rfl⟩
            exact hge1 k
          have h2 := Submodule.sub_mem _ hf0 h1
          have e : f - r = x i := by rw [← hfdef, add_sub_cancel_right]
          rwa [e] at h2
        · exact hge1 k
      have hspan : spanS S (Fin.cons f x' : Fin (n + 1) → V) = spanS S x := by
        apply le_antisymm
        · refine Submodule.span_le.mpr ?_
          rintro _ ⟨i, rfl⟩
          refine Fin.cases ?_ (fun k => ?_) i
          · exact hf
          · exact hx'mem k
        · refine Submodule.span_le.mpr ?_
          rintro _ ⟨i, rfl⟩
          exact hge i
      obtain ⟨c, hcS, hcdet⟩ := gram_det_of_le (h := h) hS hge
      rw [gram_det_cons hs f x' hfx'] at hcdet
      obtain ⟨y', horth, hspan'⟩ := ih x' (fun i j => hint _ (hx'mem i) _ (hx'mem j)) (by
        intro hd
        apply hdet
        have e : (gram h x).det * π⁻¹ = c * h f f * ((gram h x').det * π⁻¹) := by
          rw [hcdet]; ring
        rw [e]
        exact hd.mul_left (S.mul_mem hcS hu.2.1))
      have hfy : ∀ k, h f (y' k) = 0 := by
        intro k
        have h1 : y' k ∈ spanS S x' := by rw [← hspan']; exact mem_spanS y' k
        exact spanS_induction (p := fun v => h f v = 0) (by simp)
          (fun a b ha hb => by rw [map_add, ha, hb, add_zero])
          (fun c _ a ha => by rw [map_smul, ha, smul_zero]) hfx' _ h1
      refine ⟨Fin.cons f y', ?_, ?_⟩
      · intro i j
        refine Fin.cases ?_ (fun k => ?_) i <;> refine Fin.cases ?_ (fun l => ?_) j
        · intro hne; exact absurd rfl hne
        · intro _; simpa using hfy l
        · intro _
          simp only [Fin.cons_succ, Fin.cons_zero]
          rw [← show star (h f (y' k)) = h (y' k) f from hs.eq _ _, hfy, star_zero]
        · intro hne
          simp only [Fin.cons_succ]
          exact horth k l fun hkl => hne (by rw [hkl])
      · rw [← hspan, spanS_cons, spanS_cons, hspan']
    · push Not at hnd
      cases n with
      | zero => exact ⟨x, fun i j hij => absurd (by omega : i = j) hij, rfl⟩
      | succ m => exact absurd (gram_det_dv hπ x hnd) hdet

end Formalism.HermitianLattices.Ext.L3.U0
end
end

