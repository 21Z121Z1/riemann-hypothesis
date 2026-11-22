import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.Saturated

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.CellBase
section
noncomputable section

open scoped Classical

namespace PI.TermsAtPtFiniteW.CellW

open NumberField Formalism.MainNotions.S

variable {E : Type} [Field E] [NumberField E]

def Intg {m n : Type*} (d : 𝓞 E) (M : Matrix m n E) : Prop :=
  ∃ M' : Matrix m n (𝓞 E), M'.map (algebraMap (𝓞 E) E) = (algebraMap (𝓞 E) E d) • M

theorem intg_mul {l m n : Type*} [Fintype m] {d d' : 𝓞 E} {M : Matrix l m E} {N : Matrix m n E}
    (hM : Intg d M) (hN : Intg d' N) : Intg (d * d') (M * N) := by
  obtain ⟨M', hM'⟩ := hM
  obtain ⟨N', hN'⟩ := hN
  refine ⟨M' * N', ?_⟩
  rw [Matrix.map_mul, hM', hN', Matrix.smul_mul, Matrix.mul_smul, smul_smul, map_mul, mul_comm]

theorem intg_sub {m n : Type*} {d : 𝓞 E} {M N : Matrix m n E} (hM : Intg d M) (hN : Intg d N) :
    Intg d (M - N) := by
  obtain ⟨M', hM'⟩ := hM
  obtain ⟨N', hN'⟩ := hN
  refine ⟨M' - N', ?_⟩
  ext i j
  have h1 := congrFun (congrFun hM' i) j
  have h2 := congrFun (congrFun hN' i) j
  simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, map_sub] at h1 h2 ⊢
  rw [h1, h2]; ring

theorem intg_dvd {m n : Type*} {a D : 𝓞 E} {M : Matrix m n E} (hM : Intg a M) (h : a ∣ D) : Intg D M := by
  obtain ⟨M', hM'⟩ := hM
  obtain ⟨k, rfl⟩ := h
  refine ⟨k • M', ?_⟩
  ext i j
  have := congrFun (congrFun hM' i) j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul] at this ⊢
  rw [this]; ring

theorem intg_one {n : Type*} [DecidableEq n] (d : 𝓞 E) : Intg d (1 : Matrix n n E) := by
  refine ⟨d • (1 : Matrix n n (𝓞 E)), ?_⟩
  ext i j
  by_cases h : i = j <;> simp [h]

theorem intg_zero {m n : Type*} (d : 𝓞 E) : Intg d (0 : Matrix m n E) :=
  ⟨0, by ext i j; simp⟩

theorem intg_submatrix {m n m' n' : Type*} {d : 𝓞 E} {M : Matrix m n E} (hM : Intg d M) (f : m' → m)
    (g : n' → n) : Intg d (M.submatrix f g) := by
  obtain ⟨M', hM'⟩ := hM
  refine ⟨M'.submatrix f g, ?_⟩
  ext i j
  have h1 := congrFun (congrFun hM' (f i)) (g j)
  simpa using h1

theorem intg_fromBlocks {l m n o : Type*} {d : 𝓞 E} {A : Matrix l n E} {B : Matrix l o E}
    {C : Matrix m n E} {D : Matrix m o E} (hA : Intg d A) (hB : Intg d B) (hC : Intg d C) (hD : Intg d D) :
    Intg d (Matrix.fromBlocks A B C D) := by
  obtain ⟨A', hA'⟩ := hA
  obtain ⟨B', hB'⟩ := hB
  obtain ⟨C', hC'⟩ := hC
  obtain ⟨D', hD'⟩ := hD
  refine ⟨Matrix.fromBlocks A' B' C' D', ?_⟩
  rw [Matrix.fromBlocks_map, hA', hB', hC', hD', Matrix.fromBlocks_smul]

theorem intg_adj {k : ℕ} {d : 𝓞 E} {M : Matrix (Fin k) (Fin k) E} (hM : Intg d M) :
    Intg (d ^ (k - 1)) M.adjugate := by
  obtain ⟨M', hM'⟩ := hM
  refine ⟨M'.adjugate, ?_⟩
  have h1 := RingHom.map_adjugate (algebraMap (𝓞 E) E) M'
  simp only [RingHom.mapMatrix_apply] at h1
  rw [h1, hM', Matrix.adjugate_smul, Fintype.card_fin, map_pow]

theorem intg_of_entries {m n : Type*} {Z : Matrix m n E} (h : ∀ i j, ∃ o : 𝓞 E, (o : E) = Z i j) :
    Intg 1 Z := by
  refine ⟨fun i j => Classical.choose (h i j), ?_⟩
  ext i j
  simp only [Matrix.map_apply, map_one, one_smul]
  exact Classical.choose_spec (h i j)

theorem exists_den (x : E) :
    ∃ m : 𝓞 E, m ≠ 0 ∧ ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = algebraMap (𝓞 E) E m * x := by
  obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 E)) x
  refine ⟨s, nonZeroDivisors.ne_zero s.2, a, ?_⟩
  simp only at h
  rw [← h, mul_comm]

theorem alg_ne_zero {d : 𝓞 E} (hd : d ≠ 0) : algebraMap (𝓞 E) E d ≠ 0 := by
  intro h
  exact hd ((injective_iff_map_eq_zero (algebraMap (𝓞 E) E)).mp (IsFractionRing.injective (𝓞 E) E) d h)

section Uni

variable {K : Type*} [Field K] {k : ℕ}

theorem lo_bt {A : Matrix (Fin k) (Fin k) K} (hA : IsLoUni A) : A.BlockTriangular OrderDual.toDual :=
  fun i j h => (hA i j).1 (by simpa using h)

theorem lo_diag_mul {A B : Matrix (Fin k) (Fin k) K} (hA : A.BlockTriangular OrderDual.toDual)
    (hB : B.BlockTriangular OrderDual.toDual) (i : Fin k) : (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro c _ hc
    rcases lt_or_gt_of_ne hc with h | h
    · rw [hB (by simpa using h), mul_zero]
    · rw [hA (by simpa using h), zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem lo_mul {A B : Matrix (Fin k) (Fin k) K} (hA : IsLoUni A) (hB : IsLoUni B) : IsLoUni (A * B) := by
  have ht := (lo_bt hA).mul (lo_bt hB)
  intro i j
  refine ⟨fun h => ht (by simpa using h), fun h => ?_⟩
  subst h
  rw [lo_diag_mul (lo_bt hA) (lo_bt hB), (hA i i).2 rfl, (hB i i).2 rfl, one_mul]

theorem lo_det {A : Matrix (Fin k) (Fin k) K} (hA : IsLoUni A) : A.det = 1 := by
  rw [Matrix.det_of_isLowerTriangular A (lo_bt hA)]
  exact Finset.prod_eq_one fun i _ => (hA i i).2 rfl

theorem lo_mul_adj {A : Matrix (Fin k) (Fin k) K} (hA : IsLoUni A) : A * A.adjugate = 1 := by
  rw [Matrix.mul_adjugate, lo_det hA, one_smul]

theorem lo_adj_mul {A : Matrix (Fin k) (Fin k) K} (hA : IsLoUni A) : A.adjugate * A = 1 := by
  rw [Matrix.adjugate_mul, lo_det hA, one_smul]

theorem lo_adj {A : Matrix (Fin k) (Fin k) K} (hA : IsLoUni A) : IsLoUni A.adjugate := by
  letI : Invertible A.det := invertibleOfNonzero (by rw [lo_det hA]; exact one_ne_zero)
  letI : Invertible A := Matrix.invertibleOfDetInvertible A
  have hinv : A⁻¹ = A.adjugate := by rw [Matrix.inv_def, lo_det hA, Ring.inverse_one, one_smul]
  have ht : A.adjugate.BlockTriangular OrderDual.toDual := by
    rw [← hinv]; exact Matrix.blockTriangular_inv_of_blockTriangular (lo_bt hA)
  intro i j
  refine ⟨fun h => ht (by simpa using h), fun h => ?_⟩
  subst h
  have h1 := congrFun (congrFun (lo_mul_adj hA) i) i
  rw [lo_diag_mul (lo_bt hA) ht, (hA i i).2 rfl, one_mul, Matrix.one_apply_eq] at h1
  exact h1

theorem up_iff_lo_transpose {U : Matrix (Fin k) (Fin k) K} : IsUpUni U ↔ IsLoUni U.transpose := by
  constructor
  · intro h i j
    exact ⟨fun hij => (h j i).1 hij, fun hij => (h j i).2 hij.symm⟩
  · intro h i j
    exact ⟨fun hij => (h j i).1 hij, fun hij => (h j i).2 hij.symm⟩

theorem up_mul {A B : Matrix (Fin k) (Fin k) K} (hA : IsUpUni A) (hB : IsUpUni B) : IsUpUni (A * B) := by
  rw [up_iff_lo_transpose] at *
  rw [Matrix.transpose_mul]; exact lo_mul hB hA

theorem up_det {A : Matrix (Fin k) (Fin k) K} (hA : IsUpUni A) : A.det = 1 := by
  rw [← Matrix.det_transpose]; exact lo_det (up_iff_lo_transpose.mp hA)

theorem up_mul_adj {A : Matrix (Fin k) (Fin k) K} (hA : IsUpUni A) : A * A.adjugate = 1 := by
  rw [Matrix.mul_adjugate, up_det hA, one_smul]

theorem up_adj_mul {A : Matrix (Fin k) (Fin k) K} (hA : IsUpUni A) : A.adjugate * A = 1 := by
  rw [Matrix.adjugate_mul, up_det hA, one_smul]

theorem up_adj {A : Matrix (Fin k) (Fin k) K} (hA : IsUpUni A) : IsUpUni A.adjugate := by
  rw [up_iff_lo_transpose] at *
  rw [Matrix.adjugate_transpose]; exact lo_adj hA

end Uni

theorem quotFinite (c : 𝓞 E) (hc : c ≠ 0) : Finite (𝓞 E ⧸ Ideal.span {c}) :=
  Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hc)

theorem fin_of_cong {α ι : Type*} [Finite ι] (X : Set α) (f : α → ι → E)
    (hf : ∀ x ∈ X, ∀ i, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = f x i) (c : 𝓞 E) (hc : c ≠ 0)
    (R : α → α → Prop)
    (hR : ∀ x ∈ X, ∀ y ∈ X,
      (∀ i, ∃ o : 𝓞 E, algebraMap (𝓞 E) E c * algebraMap (𝓞 E) E o = f y i - f x i) → R x y) :
    ∃ Zs : Set α, Zs.Finite ∧ ∀ x ∈ X, ∃ y ∈ Zs, R x y := by
  have := quotFinite c hc
  let g : α → ι → (𝓞 E ⧸ Ideal.span {c}) := fun x i =>
    if h : ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = f x i then Ideal.Quotient.mk _ (Classical.choose h) else 0
  haveI : Finite {ρ : ι → (𝓞 E ⧸ Ideal.span {c}) // ∃ x ∈ X, g x = ρ} := Subtype.finite
  refine ⟨Set.range (fun ρ : {ρ : ι → (𝓞 E ⧸ Ideal.span {c}) // ∃ x ∈ X, g x = ρ} => Classical.choose ρ.2),
    Set.finite_range _, ?_⟩
  intro x hx
  have hex : ∃ x' ∈ X, g x' = g x := ⟨x, hx, rfl⟩
  refine ⟨Classical.choose hex, ⟨⟨g x, hex⟩, rfl⟩, ?_⟩
  obtain ⟨hy, hgy⟩ := Classical.choose_spec hex
  apply hR x hx _ hy
  intro i
  have h1 := hf x hx i
  have h2 := hf _ hy i
  have hg := congrFun hgy i
  simp only [g, dif_pos h1, dif_pos h2] at hg
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at hg
  obtain ⟨o, ho⟩ := hg
  refine ⟨o, ?_⟩
  rw [← map_mul, ← ho, map_sub, Classical.choose_spec h1, Classical.choose_spec h2]

end PI.TermsAtPtFiniteW.CellW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.DShort
section
noncomputable section

open scoped Classical

namespace PI.TermsAtPtFiniteW

open NumberField Formalism.BasicNotions

theorem qcs_bound {W : Type*} [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    (B : LinearMap.BilinForm ℚ W) (hs : ∀ x y, B x y = B y x) (hp : ∀ x, x ≠ 0 → 0 < B x x)
    (f : W →ₗ[ℚ] ℚ) : ∃ K : ℚ, ∀ x, f x ^ 2 ≤ K * B x x := by
  let Bl : W →ₗ[ℚ] Module.Dual ℚ W := B
  have hinj : Function.Injective Bl := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    by_contra hne
    have h1 := hp w hne
    have h0 : B w w = 0 := by simpa [Bl] using LinearMap.congr_fun hw w
    linarith
  have hsurj : Function.Surjective Bl :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (Subspace.dual_finrank_eq).symm).1 hinj
  obtain ⟨w, hw⟩ := hsurj f
  refine ⟨B w w, fun x => ?_⟩
  have hfx : f x = B w x := by rw [← hw]
  rw [hfx]
  by_cases hw0 : w = 0
  · subst hw0
    simp
  · have hww := hp w hw0
    have hyy : 0 ≤ B (B w w • x - B w x • w) (B w w • x - B w x • w) := by
      by_cases hy : B w w • x - B w x • w = 0
      · rw [hy]
        simp
      · exact le_of_lt (hp _ hy)
    have hexp : B (B w w • x - B w x • w) (B w w • x - B w x • w) =
        B w w * (B w w * B x x - B w x ^ 2) := by
      simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [hs x w]
      ring
    rw [hexp] at hyy
    have h2 := (mul_nonneg_iff_of_pos_left hww).1 hyy
    linarith

theorem trace_pos_of_re_pos {E : Type} [Field E] [NumberField E] (z : E)
    (h : ∀ τ : E →+* ℂ, 0 < (τ z).re) : 0 < Algebra.trace ℚ E z := by
  haveI : Nonempty (E →ₐ[ℚ] ℂ) := ⟨IsAlgClosed.lift⟩
  have h1 : algebraMap ℚ ℂ (Algebra.trace ℚ E z) = ∑ σ : E →ₐ[ℚ] ℂ, σ z :=
    trace_eq_sum_embeddings ℂ
  have h2 : (algebraMap ℚ ℂ (Algebra.trace ℚ E z)).re = ∑ σ : E →ₐ[ℚ] ℂ, (σ z).re := by
    rw [h1, Complex.re_sum]
  have h3 : (algebraMap ℚ ℂ (Algebra.trace ℚ E z)).re = ((Algebra.trace ℚ E z : ℚ) : ℝ) := by
    simp
  have hpos : 0 < ∑ σ : E →ₐ[ℚ] ℂ, (σ z).re := by
    apply Finset.sum_pos
    · intro σ _
      exact h σ.toRingHom
    · exact Finset.univ_nonempty
  have h4 : (0 : ℝ) < ((Algebra.trace ℚ E z : ℚ) : ℝ) := by
    rw [← h3, h2]
    exact hpos
  exact_mod_cast h4

theorem exists_common_den {E : Type} [Field E] [NumberField E] (t : Finset E) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ e ∈ t, IsIntegral ℤ ((d : E) * e) := by
  have hintC : ∀ m : ℤ, IsIntegral ℤ (m : E) := fun m => by
    simpa using isIntegral_algebraMap (R := ℤ) (A := E) (x := m)
  have hone : ∀ a : E, ∃ y : ℤ, y ≠ 0 ∧ IsIntegral ℤ ((y : E) * a) := by
    intro a
    have hbint : ∀ k, IsIntegral ℤ (integralBasis E k) := by
      intro k
      rw [integralBasis_apply]
      exact RingOfIntegers.isIntegral_coe _
    have hsum : ∀ Y : ℤ, (Y : E) * a = ∑ k, ((Y : ℚ) * (integralBasis E).repr a k) • integralBasis E k := by
      intro Y
      have h1 : (Y : E) * (∑ k, (integralBasis E).repr a k • integralBasis E k) =
          ∑ k, ((Y : ℚ) * (integralBasis E).repr a k) • integralBasis E k := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        simp only [Algebra.smul_def, map_mul, map_intCast]
        ring
      rwa [(integralBasis E).sum_repr a] at h1
    refine ⟨∏ j, (((integralBasis E).repr a j).den : ℤ), ?_, ?_⟩
    · rw [Finset.prod_ne_zero_iff]
      intro k _
      exact_mod_cast ((integralBasis E).repr a k).den_nz
    · rw [hsum]
      apply IsIntegral.sum
      intro k _
      obtain ⟨c, hc⟩ : (((integralBasis E).repr a k).den : ℤ) ∣ ∏ j, (((integralBasis E).repr a j).den : ℤ) :=
        Finset.dvd_prod_of_mem _ (Finset.mem_univ k)
      have hm : ((∏ j, (((integralBasis E).repr a j).den : ℤ) : ℤ) : ℚ) * (integralBasis E).repr a k =
          ((c * ((integralBasis E).repr a k).num : ℤ) : ℚ) := by
        rw [hc]
        push_cast
        have h2 := Rat.den_mul_eq_num ((integralBasis E).repr a k)
        linear_combination (c : ℚ) * h2
      rw [hm, Algebra.smul_def, map_intCast]
      exact (hintC _).mul (hbint k)
  induction t using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, fun e he => by simp at he⟩
  | @insert a t ha ih =>
    obtain ⟨d, hd, hdint⟩ := ih
    obtain ⟨y, hy, hyint⟩ := hone a
    refine ⟨d * y, mul_ne_zero hd hy, fun e he => ?_⟩
    rcases Finset.mem_insert.1 he with rfl | he'
    · have h1 : ((d * y : ℤ) : E) * e = (d : E) * ((y : E) * e) := by
        push_cast
        ring
      rw [h1]
      exact (hintC d).mul hyint
    · have h1 : ((d * y : ℤ) : E) * e = (y : E) * ((d : E) * e) := by
        push_cast
        ring
      rw [h1]
      exact (hintC y).mul (hdint e he')

theorem eq_of_trace_basis {E : Type} [Field E] [NumberField E] (a b : E)
    (h : ∀ k, Algebra.trace ℚ E (integralBasis E k * a) = Algebra.trace ℚ E (integralBasis E k * b)) :
    a = b := by
  have hφ : (Algebra.trace ℚ E).comp (LinearMap.mulLeft ℚ (a - b)) = 0 := by
    apply (integralBasis E).ext
    intro k
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.zero_apply]
    rw [sub_mul, map_sub, mul_comm a, mul_comm b, h k, sub_self]
  have hall : ∀ n : E, Algebra.traceForm ℚ E (a - b) n = 0 := by
    intro n
    rw [Algebra.traceForm_apply]
    exact LinearMap.congr_fun hφ n
  have hab : a - b = 0 := by
    first
    | exact (traceForm_nondegenerate ℚ E) (a - b) hall
    | exact (traceForm_nondegenerate ℚ E).1 (a - b) hall
    | exact (traceForm_nondegenerate (K := ℚ) (L := E)) (a - b) hall
  exact sub_eq_zero.1 hab

theorem trace_int_of_isIntegral {E : Type} [Field E] [NumberField E] (z : E) (hz : IsIntegral ℤ z) :
    ∃ n : ℤ, (n : ℚ) = Algebra.trace ℚ E z := by
  have h1 : IsIntegral ℤ (Algebra.trace ℚ E z) := Algebra.isIntegral_trace hz
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 h1
  exact ⟨n, by simpa using hn⟩

theorem shortFin_holds : ShortFin := by
  intro E _ _ _ S Λ hΛ P hpos c
  have hsl : ∀ (q : ℚ) (x y : S.V),
      S.hT (algebraMap ℚ E q • x) y = algebraMap ℚ E q * S.hT x y := by
    intro q x y
    rw [LinearMap.map_smulₛₗ₂, starRingEnd_apply, eq_ratCast, star_ratCast, smul_eq_mul]
  have hsr : ∀ (q : ℚ) (x y : S.V),
      S.hT x (algebraMap ℚ E q • y) = algebraMap ℚ E q * S.hT x y := by
    intro q x y
    rw [LinearMap.map_smul, smul_eq_mul]
  have htq : ∀ (q : ℚ) (z : E),
      Algebra.trace ℚ E (algebraMap ℚ E q * z) = q * Algebra.trace ℚ E z := by
    intro q z
    rw [← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]
  letI : Module ℚ P := Module.compHom P (algebraMap ℚ E)
  haveI : IsScalarTower ℚ E P := ⟨fun q e x => by
    show (q • e) • x = algebraMap ℚ E q • (e • x)
    rw [Algebra.smul_def, mul_smul]⟩
  haveI : FiniteDimensional ℚ P := Module.Finite.trans E P
  have hcoe : ∀ (q : ℚ) (x : P), ((q • x : P) : S.V) = algebraMap ℚ E q • (x : S.V) :=
    fun q x => rfl
  let B : LinearMap.BilinForm ℚ P := LinearMap.mk₂ ℚ
    (fun x y : P => Algebra.trace ℚ E (S.hT x y) + Algebra.trace ℚ E (S.hT y x))
    (fun x1 x2 y => by simp only [Submodule.coe_add, map_add, LinearMap.add_apply]; ring)
    (fun q x y => by simp only [hcoe, hsl, hsr, htq, smul_eq_mul]; ring)
    (fun x y1 y2 => by simp only [Submodule.coe_add, map_add, LinearMap.add_apply]; ring)
    (fun q x y => by simp only [hcoe, hsl, hsr, htq, smul_eq_mul]; ring)
  have hBapp : ∀ x y : P,
      B x y = Algebra.trace ℚ E (S.hT x y) + Algebra.trace ℚ E (S.hT y x) := fun x y => rfl
  have hsym : ∀ x y : P, B x y = B y x := fun x y => by rw [hBapp, hBapp]; ring
  have hp : ∀ x : P, x ≠ 0 → 0 < B x x := by
    intro x hx
    have hx' : (x : S.V) ≠ 0 := by
      intro h; apply hx; exact Subtype.ext h
    have := trace_pos_of_re_pos _ (hpos x x.2 hx')
    rw [hBapp]; linarith

  obtain ⟨sg, hsg⟩ := hΛ.fg
  obtain ⟨d, hd0, hd⟩ :=
    exists_common_den (sg.biUnion fun g => Finset.univ.image fun j => S.frame.repr g j)
  have hΛint : ∀ x ∈ Λ, ∀ j, IsIntegral ℤ ((d : E) * S.frame.repr x j) := by
    intro x hx
    rw [← hsg] at hx
    induction hx using Submodule.span_induction with
    | mem g hg =>
      intro j
      exact hd _ (Finset.mem_biUnion.2 ⟨g, hg, Finset.mem_image.2 ⟨j, Finset.mem_univ _, rfl⟩⟩)
    | zero => intro j; simpa using (isIntegral_zero : IsIntegral ℤ (0 : E))
    | add x y _ _ hx hy =>
      intro j
      simp only [map_add, Finsupp.add_apply, mul_add]
      exact (hx j).add (hy j)
    | smul a x _ hx =>
      intro j
      rw [← algebraMap_smul E a x, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_left_comm]
      exact (RingOfIntegers.isIntegral_coe a).mul (hx j)

  let Φ : S.V → Fin S.rank × Module.Free.ChooseBasisIndex ℤ (𝓞 E) → ℚ := fun x p =>
    Algebra.trace ℚ E (integralBasis E p.2 * ((d : E) * S.frame.repr x p.1))
  have hlin : ∀ p, ∃ f : P →ₗ[ℚ] ℚ, ∀ x : P, f x = Φ x p := by
    intro p
    refine ⟨{ toFun := fun x => Φ x p, map_add' := ?_, map_smul' := ?_ }, fun x => rfl⟩
    · intro x y
      simp only [Φ, Submodule.coe_add, map_add, Finsupp.add_apply, mul_add]
    · intro q x
      simp only [Φ, hcoe, map_smul, Finsupp.smul_apply, smul_eq_mul, RingHom.id_apply]
      rw [← htq]
      congr 1
      ring
  choose f hf using hlin
  choose K hK using fun p => qcs_bound B hsym hp (f p)
  have hint : ∀ x ∈ Λ, ∀ p, ∃ n : ℤ, (n : ℚ) = Φ x p := by
    intro x hx p
    have hμ : IsIntegral ℤ (integralBasis E p.2) := by
      rw [integralBasis_apply]; exact RingOfIntegers.isIntegral_coe _
    exact trace_int_of_isIntegral _ (hμ.mul (hΛint x hx p.1))
  let R : Fin S.rank × Module.Free.ChooseBasisIndex ℤ (𝓞 E) → ℤ := fun p =>
    ⌈K p * (2 * Algebra.trace ℚ E c)⌉
  refine Set.Finite.of_injOn (f := Φ)
    (t := Set.pi Set.univ fun p => ((Int.cast : ℤ → ℚ) '' Set.Icc (-R p) (R p))) ?_ ?_
    (Set.Finite.pi fun p => (Set.finite_Icc _ _).image _)
  · rintro x ⟨hxΛ, hxP, hxc⟩ p _
    obtain ⟨n, hn⟩ := hint x hxΛ p
    have hB : B ⟨x, hxP⟩ ⟨x, hxP⟩ = 2 * Algebra.trace ℚ E c := by
      rw [hBapp]; simp only [hxc]; ring
    have h1 : (Φ x p) ^ 2 ≤ K p * (2 * Algebra.trace ℚ E c) := by
      have := hK p ⟨x, hxP⟩
      rw [hf, hB] at this
      exact this
    have h2 : ((n ^ 2 : ℤ) : ℚ) ≤ (R p : ℚ) := by
      push_cast
      rw [hn]
      exact h1.trans (Int.le_ceil _)
    have h3 : n ^ 2 ≤ R p := by exact_mod_cast h2
    refine ⟨n, ⟨?_, ?_⟩, hn⟩
    · rcases le_or_gt n 0 with h | h <;> nlinarith
    · rcases le_or_gt n 0 with h | h <;> nlinarith
  · rintro x ⟨hxΛ, -, -⟩ y ⟨hyΛ, -, -⟩ hxy
    apply S.frame.ext_elem
    intro j
    have hj : (d : E) * S.frame.repr x j = (d : E) * S.frame.repr y j :=
      eq_of_trace_basis _ _ (fun k => congrFun hxy (j, k))
    exact mul_left_cancel₀ (Int.cast_ne_zero.2 hd0) hj

end PI.TermsAtPtFiniteW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.ResFin
section
noncomputable section

open scoped Classical

namespace PI.TermsAtPtFiniteW

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.Saturated

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ndS (D : D7) : ℕ :=
  (Ideal.absNorm (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F)))) ^ D.R.rS

def FInt : Prop :=
  ∀ (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (f : Fin D.R.rS → (VS D).V) (L : Submodule (𝓞 D.host.E) (VS D).V),
    (∀ a b, (VS D).hT (f a) (f b) = 0) → (∀ a b, (VS D).hT (F0.e a) (f b) = if a = b then 1 else 0) →
    (∀ x ∈ L, ∀ a, (VS D).hT (F0.e a) x = 0 ∧ (VS D).hT (f a) x = 0) →
    Λ = latSpan (aaS D) F0.e ⊔ L ⊔ latSpan (fun a => (aaS D a)⁻¹) f →
    0 < ndS D ∧ ∀ x ∈ Λ, ∀ c, ∃ o : 𝓞 D.host.E, (o : D.host.E) = (ndS D : D.host.E) * (VS D).hT (f c) x

def ResFin : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] (Λ : Submodule (𝓞 E) V), Λ.FG → ∀ c : ℕ, 0 < c →
      ∃ (R : Type) (_ : Finite R) (ρ : V → R), ∀ x ∈ Λ, ∀ y ∈ Λ, ρ x = ρ y →
        ∃ l ∈ Λ, y - x = (c : E) • l

end PI.TermsAtPtFiniteW
end
end

