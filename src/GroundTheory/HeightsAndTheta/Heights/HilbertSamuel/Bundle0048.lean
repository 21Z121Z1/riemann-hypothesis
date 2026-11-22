import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0040
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Bundle0018
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0025
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0024
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0041
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0026

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockImageArith
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace BlockImageArithmetic

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]

theorem ringKrullDim_eq (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    ringKrullDim (MRing ι ⧸ mCoordIdeal y) =
      (((Algebra.trdeg ℤ (CoordinateConeArithVar.ratioField y c)).toENat + Fintype.card K + 1 : ℕ∞) :
        WithBot ℕ∞) := by
  have hhor := CoordinateConeArithVar.horizontal y
  have : (mCoordIdeal y).IsPrime := RingHom.ker_isPrime _
  have htr := ConeTrdeg.proof K ι (CoordinateConeArithVar.ratioField y c)
    (CoordinateConeArithVar.ratioPtL y c) (CoordinateConeArithVar.birational y c hc)
    (fun k ↦ ⟨c k, fun h0 ↦ by
      have h1 := congrArg Subtype.val h0
      simp [CoordinateConeArithVar.ratioPtL, CoordinateConeArithVar.ratioPt, hc] at h1⟩)
    (by rw [CoordinateConeArithVar.mCoordIdeal_ratioPtL y c hc]; exact hhor)
  rw [CoordinateConeArithVar.mCoordIdeal_ratioPtL y c hc] at htr
  rw [IntDomainDim.proof (MRing ι ⧸ mCoordIdeal y)
    (CoordinateConeArithVar.algebraMap_injective _ hhor), htr]
  simp only [map_add, map_natCast]

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem div_mem_of_sum (F : IntermediateField ℚ Ω) {A B : Type} [Fintype B] (u : A → Ω) (v : B → Ω)
    (L : Matrix A B ℤ) (hu : ∀ a, u a = ∑ b, (L a b : Ω) * v b) (b₀ : B)
    (hF : ∀ b, v b / v b₀ ∈ F) (a : A) : u a / v b₀ ∈ F := by
  rw [hu, Finset.sum_div]
  refine sum_mem fun b _ ↦ ?_
  rw [mul_div_assoc]
  exact mul_mem (intCast_mem F _) (hF b)

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem ratio_mem_of_sum (F : IntermediateField ℚ Ω) {A B : Type} [Fintype B] (u : A → Ω) (v : B → Ω)
    (L : Matrix A B ℤ) (hu : ∀ a, u a = ∑ b, (L a b : Ω) * v b) (b₀ : B) (hv : v b₀ ≠ 0)
    (hF : ∀ b, v b / v b₀ ∈ F) (a a' : A) : u a / u a' ∈ F := by
  rw [← div_div_div_cancel_right₀ hv (u a) (u a')]
  exact div_mem (div_mem_of_sum F u v L hu b₀ hF a) (div_mem_of_sum F u v L hu b₀ hF a')

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem aeval_mem (F : IntermediateField ℚ Ω) (w : (Σ k, ι k) → Ω) (hw : ∀ p, w p ∈ F) (f : MRing ι) :
    aeval w f ∈ F := by
  induction f using MvPolynomial.induction_on with
  | C a => rw [aeval_C, algebraMap_int_eq, eq_intCast]; exact intCast_mem F a
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p q hp => rw [map_mul, aeval_X]; exact mul_mem hp (hw q)

omit [Fintype K] [CharZero Ω] in

theorem isMultiHomog_X_single [DecidableEq K] (p : Σ k, ι k) :
    IsMultiHomog (X p : MRing ι) (fun k ↦ if k = p.1 then 1 else 0) := by
  intro m hm k
  rw [support_X, Finset.mem_singleton] at hm
  subst hm
  obtain ⟨k', i'⟩ := p
  by_cases h : k = k'
  · subst h
    rw [Finset.sum_eq_single i']
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · simp [h]

omit [CharZero Ω] in

theorem aeval_mul_pow_of_block (y w : (Σ k, ι k) → Ω) (k₀ : K) (z : Ω)
    (hw : ∀ i, w ⟨k₀, i⟩ * z = y ⟨k₀, i⟩) {f : MRing ι} {d : K → ℕ} (hf : IsMultiHomog f d)
    (hd : ∀ k, k ≠ k₀ → d k = 0) : aeval w f * z ^ d k₀ = aeval y f := by
  classical
  conv_rhs => rw [f.as_sum]
  conv_lhs => rw [f.as_sum]
  rw [map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  rw [aeval_monomial, aeval_monomial, mul_assoc]
  congr 1
  have hsum : ∑ p, m p = d k₀ := by
    rw [Fintype.sum_sigma, Finset.sum_eq_single k₀]
    · exact hf m hm k₀
    · intro k _ hk
      rw [hf m hm k, hd k hk]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hzero : ∀ p : Σ k, ι k, p.1 ≠ k₀ → m p = 0 := by
    intro p hp
    have h1 := hf m hm p.1
    rw [hd _ hp] at h1
    exact (Finset.sum_eq_zero_iff.mp h1) p.2 (Finset.mem_univ _)
  rw [Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _), Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _),
    ← hsum, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p _ ↦ ?_
  rw [← mul_pow]
  by_cases hp : p.1 = k₀
  · obtain ⟨k, i⟩ := p
    simp only at hp
    subst hp
    rw [hw i]
  · rw [hzero p hp, pow_zero, pow_zero]

end BlockImageArithmetic

open BlockImageArithmetic in

theorem BlockImageArith.proof : BlockImageArith.Statement := by
  intro D K _ _ ι _ Ω _ _ y k₀ r M N x hY hbir hB _
  classical
  obtain ⟨hK, ⟨_, _, hrel⟩, _, hdim⟩ := hY
  have hnz : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ := hrel k
    refine ⟨i, fun h0 ↦ hi ?_⟩
    show mConeMap y (X ⟨k, i⟩) = 0
    simp [mConeMap, h0]
  choose c hc using hnz
  obtain ⟨j₀, hj₀⟩ : ∃ j, x j ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    apply hc k₀
    rw [hB.2 (c k₀)]
    simp [h]
  let c' : ∀ k, GlobalTheory (Fin r) k := fun _ ↦ j₀.2
  have hc' : ∀ k, x ⟨k, c' k⟩ ≠ 0 := fun _ ↦ hj₀
  set Fy := CoordinateConeArithVar.ratioField y c with hFy
  set Fx := CoordinateConeArithVar.ratioField (ι := GlobalTheory (Fin r)) x c' with hFx
  have hxF : ∀ j, x j / x j₀ ∈ Fx := fun j ↦ IntermediateField.subset_adjoin _ _ ⟨j, rfl⟩
  have hLx : Fx ≤ Fy := by
    rw [hFx, IntermediateField.adjoin_le_iff]
    rintro _ ⟨p, rfl⟩
    exact ratio_mem_of_sum Fy x (fun i ↦ y ⟨k₀, i⟩) M hB.1 (c k₀) (hc k₀)
      (fun i ↦ IntermediateField.subset_adjoin _ _ ⟨⟨k₀, i⟩, rfl⟩) p ⟨p.1, c' p.1⟩
  have hLy : Fy ≤ Fx := by
    rw [hFy, IntermediateField.adjoin_le_iff]
    rintro _ ⟨⟨k, i⟩, rfl⟩
    show y ⟨k, i⟩ / y ⟨k, c k⟩ ∈ Fx
    have hyF : ∀ i, y ⟨k₀, i⟩ / x j₀ ∈ Fx := fun i ↦
      div_mem_of_sum Fx (fun i ↦ y ⟨k₀, i⟩) x N hB.2 j₀ hxF i
    let w : (Σ k, ι k) → Ω := fun p ↦ if p.1 = k₀ then y p / x j₀ else 0
    have hwF : ∀ p, w p ∈ Fx := by
      rintro ⟨k', i'⟩
      by_cases h : k' = k₀
      · subst h
        simp only [w, if_true]
        exact hyF i'
      · simp only [w, h, if_false]
        exact zero_mem _
    have hw : ∀ i, w ⟨k₀, i⟩ * x j₀ = y ⟨k₀, i⟩ := fun i ↦ by
      simp only [w, if_true]
      exact div_mul_cancel₀ _ hj₀
    obtain ⟨n, g', h', hg', hh', hh0, heq⟩ := hbir _ (X ⟨k, i⟩) (X ⟨k, c k⟩)
      (isMultiHomog_X_single ⟨k, i⟩) (isMultiHomog_X_single ⟨k, c k⟩)
      (by rw [aeval_X]; exact hc k)
    rw [aeval_X, aeval_X] at heq
    have hd : ∀ k', k' ≠ k₀ → blockDeg k₀ n k' = 0 := fun k' hk' ↦ by simp [blockDeg, hk']
    have e1 := aeval_mul_pow_of_block y w k₀ (x j₀) hw hg' hd
    have e2 := aeval_mul_pow_of_block y w k₀ (x j₀) hw hh' hd
    have hwh : aeval w h' ≠ 0 := fun h0 ↦ hh0 (by rw [← e2, h0, zero_mul])
    have hrat : y ⟨k, i⟩ / y ⟨k, c k⟩ = aeval w g' / aeval w h' := by
      rw [div_eq_div_iff (hc k) hwh]
      apply mul_right_cancel₀ (pow_ne_zero (blockDeg k₀ n k₀) hj₀)
      linear_combination heq + y ⟨k, i⟩ * e2 - y ⟨k, c k⟩ * e1
    rw [hrat]
    exact div_mem (aeval_mem Fx w hwF g') (aeval_mem Fx w hwF h')
  have hLeq : Fy = Fx := le_antisymm hLy hLx
  have hdy := ringKrullDim_eq y c hc
  rw [hdim] at hdy
  rw [coordIdeal_eq_mCoordIdeal]
  refine ⟨⟨()⟩, ⟨RingHom.ker_isPrime _, CoordinateConeArithVar.isMultiHomogIdeal x,
    CoordinateConeArithVar.relevant x c' hc'⟩, CoordinateConeArithVar.horizontal x, ?_⟩
  rw [ringKrullDim_eq x c' hc']
  rw [← hFy, hLeq] at hdy
  generalize (Algebra.trdeg ℤ Fx).toENat = t at hdy ⊢
  have h1 : ((D + 1 + Fintype.card K : ℕ) : ℕ∞) = t + Fintype.card K + 1 := by exact_mod_cast hdy
  induction t using ENat.recTopCoe with
  | top => simp at h1
  | coe t =>
    have h2 : D + 1 + Fintype.card K = t + Fintype.card K + 1 := by exact_mod_cast h1
    have h3 : t = D := by omega
    subst h3
    rw [Fintype.card_unit]
    norm_cast

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockImageGenDeg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace BlockImageGenDeg

open GroundTheory.Heights₂.Heights.NumbersDVR (hilbFn mixedDiff diffStep eventualValue intNum)
open fwdDiff

theorem mixedDiff_line {K : Type*} (b m₀ : K → ℤ) (h : (K → ℤ) → ℤ) (D : ℕ) (t : ℤ) :
    mixedDiff (fun _ : Fin D => b) h (m₀ + t • b) = ((fwdDiff 1)^[D] fun s : ℤ => h (m₀ + s • b)) (t - D) := by
  induction D generalizing t with
  | zero => simp [mixedDiff]
  | succ D ih =>
    have hs : mixedDiff (fun _ : Fin (D + 1) => b) h = diffStep b (mixedDiff (fun _ : Fin D => b) h) := by
      simp [mixedDiff, List.ofFn_succ]
    have h1 : m₀ + t • b - b = m₀ + (t - 1) • b := by rw [sub_smul, one_smul, add_sub_assoc]
    have e1 : t - ((D + 1 : ℕ) : ℤ) + 1 = t - D := by push_cast; ring
    have e2 : t - ((D + 1 : ℕ) : ℤ) = t - 1 - D := by push_cast; ring
    rw [hs, diffStep, h1, ih, ih, Function.iterate_succ_apply', fwdDiff, e1, e2]

theorem fwdDiff_iter_eq_poly (φ : ℤ → ℤ) (q : Polynomial ℚ) (D : ℕ) (s : ℤ)
    (h : ∀ j ≤ D, (φ (s + j) : ℚ) = q.eval ((s : ℚ) + j)) :
    (((fwdDiff 1)^[D] φ) s : ℚ) = ((fwdDiff 1)^[D] q.eval) (s : ℚ) := by
  rw [fwdDiff_iter_eq_sum_shift, fwdDiff_iter_eq_sum_shift]
  push_cast
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ D := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  simp only [zsmul_eq_mul, nsmul_eq_mul, mul_one, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    Int.cast_natCast]
  rw [h j hj']

theorem fwdDiff_iter_poly (q : Polynomial ℚ) {D : ℕ} (hq : q.natDegree ≤ D) (x : ℚ) :
    ((fwdDiff 1)^[D] q.eval) x = q.coeff D * D.factorial := by
  rcases hq.lt_or_eq with h | h
  · rw [Polynomial.fwdDiff_iter_eq_zero_of_degree_lt h, Polynomial.coeff_eq_zero_of_natDegree_lt h]
    simp
  · subst h
    rw [q.fwdDiff_iter_degree_eq_factorial]
    rw [Pi.smul_apply, Pi.natCast_apply, smul_eq_mul]
    rfl

def lineRestr {K : Type*} [DecidableEq K] (p : MvPolynomial K ℚ) (k₀ : K) (m : K → ℚ) : Polynomial ℚ :=
  MvPolynomial.aeval (fun k => if k = k₀ then Polynomial.X else Polynomial.C (m k)) p

theorem eval_lineRestr {K : Type*} [DecidableEq K] (p : MvPolynomial K ℚ) (k₀ : K) (m : K → ℚ) (t : ℚ) :
    (lineRestr p k₀ m).eval t = MvPolynomial.eval (fun k => if k = k₀ then t else m k) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [lineRestr]
  | add p q hp hq => simp only [lineRestr, map_add, Polynomial.eval_add] at *; rw [hp, hq]
  | mul_X p k hp =>
    simp only [lineRestr, map_mul, Polynomial.eval_mul] at *
    rw [hp]
    by_cases hk : k = k₀ <;> simp [hk]

theorem natDegree_lineRestr_le {K : Type*} [DecidableEq K] (p : MvPolynomial K ℚ) (k₀ : K) (m : K → ℚ) :
    (lineRestr p k₀ m).natDegree ≤ p.totalDegree := by
  rw [lineRestr]
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun s hs => ?_
  rw [MvPolynomial.aeval_monomial, Polynomial.algebraMap_eq]
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  refine le_trans ?_ (MvPolynomial.le_totalDegree hs)
  refine Finset.sum_le_sum fun k _ => (Polynomial.natDegree_pow_le).trans ?_
  have : (if k = k₀ then (Polynomial.X : Polynomial ℚ) else Polynomial.C (m k)).natDegree ≤ 1 := by
    split_ifs <;> simp
  simpa using Nat.mul_le_mul_left (s k) this

theorem eventualValue_eq {K : Type*} (f : (K → ℤ) → ℤ) (e : ℚ) (h : ∀ᶠ m in Filter.atTop, (f m : ℚ) = e) :
    (eventualValue f : ℚ) = e := by
  have hex : ∃ c, ∀ᶠ m in Filter.atTop, f m = c := by
    obtain ⟨m, hm⟩ := h.exists
    exact ⟨f m, h.mono fun m' hm' => by exact_mod_cast hm'.trans hm.symm⟩
  unfold eventualValue
  rw [dif_pos hex]
  obtain ⟨m, hm1, hm2⟩ := (hex.choose_spec.and h).exists
  rw [← hm1]
  exact hm2

end BlockImageGenDeg

open GroundTheory.Heights₂.Heights.NumbersDVR (hilbFn mixedDiff eventualValue) in
open BlockImageGenDeg in

theorem BlockImageGenDeg.proof (hMHP : MultigradedHilbertPolynomial.Statement.{0})
    (hGFV : GenericFibreVar.Statement) (hHEP : GroundTheory.Heights₂.Heights.FieldNumbers.HilbEventuallyPoly.Statement.{0})
    (hHom : GenFibreHomog.Statement) (hImg : BlockImageHilb.Statement) (hBir : BlockBirationalHilbert.Statement)
    (hSand : PolySandwich.Statement) : BlockImageGenDeg.Statement := by
  intro D K _ _ ι _ Ω _ _ κ _ y k₀ M N x hA hB hI
  set PY := (mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ)) with hPY
  set PX := (coordIdeal ℤ x).map (MvPolynomial.map (Int.castRingHom ℚ)) with hPX

  obtain ⟨⟨hprime, -, hrel⟩, hdim⟩ := hGFV K ι Ω y D hA
  obtain ⟨pY, a₀, hdeg, hpY⟩ := hMHP ℚ K ι PY D ⟨hprime, hHom K ι Ω y, hrel⟩ hdim

  have hXhom : GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomogIdeal (ι := GlobalTheory κ) PX := by
    rw [hPX, coordIdeal_eq_mCoordIdeal]; exact hHom Unit (GlobalTheory κ) Ω x
  obtain ⟨pX, hpX⟩ := hHEP ℚ Unit (GlobalTheory κ) PX hXhom
  obtain ⟨aX, haX⟩ := Filter.eventually_atTop.mp hpX
  set p₁ := lineRestr pX () 0 with hp₁
  have hX1 : ∀ n : ℕ, (aX ()).toNat ≤ n → (hilbFn PX (fun _ => (n : ℤ)) : ℚ) = p₁.eval (n : ℚ) := by
    intro n hn
    rw [haX (fun _ => (n : ℤ)) (fun u => by cases u; show aX () ≤ (n : ℤ); omega), hp₁, eval_lineRestr]
    simp

  have hnz : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ := hA.2.1.2.2 k
    refine ⟨i, fun h0 => hi ?_⟩
    show mConeMap y (X ⟨k, i⟩) = 0
    simp [mConeMap, h0]

  have hY1 : ∀ (m : K → ℕ) (s : ℕ), (∀ k, k ≠ k₀ → a₀ ≤ m k) → a₀ ≤ s →
      (hilbFn PY (fun k => if k = k₀ then (s : ℤ) else m k) : ℚ) =
        (lineRestr pY k₀ fun k => (m k : ℚ)).eval (s : ℚ) := by
    intro m s hm hs
    have := hpY (fun k => if k = k₀ then s else m k) fun k => by
      by_cases hk : k = k₀ <;> simp [hk, hs, hm k]
    rw [eval_lineRestr]
    convert this using 3 <;> (funext k; by_cases hk : k = k₀ <;> simp [hk])

  have hsand : ∀ m : K → ℕ, (∀ k, k ≠ k₀ → a₀ ≤ m k) →
      p₁.natDegree ≤ D ∧ p₁.coeff D = (lineRestr pY k₀ fun k => (m k : ℚ)).coeff D := by
    intro m hm
    obtain ⟨c, hc⟩ := hBir K ι Ω y k₀ hnz hB m
    refine hSand D c _ _ ((natDegree_lineRestr_le _ _ _).trans hdeg) ?_
    filter_upwards [Filter.eventually_ge_atTop (max a₀ (aX ()).toNat)] with n hn
    have h1 := hX1 n (le_of_max_le_right hn)
    have h2 := hX1 (n + c) ((le_of_max_le_right hn).trans (Nat.le_add_right _ _))
    rw [hImg K ι Ω κ y k₀ M N x hI] at h1 h2
    rw [← hY1 m n hm (le_of_max_le_left hn)]
    push_cast at h2
    rw [← h1, ← h2]
    exact ⟨by exact_mod_cast (hc n).1, by exact_mod_cast (hc n).2⟩
  have hdegX : p₁.natDegree ≤ D := (hsand (fun _ => a₀) fun _ _ => le_rfl).1

  have key : (eventualValue (mixedDiff (fun _ : Fin D => (1 : Unit → ℤ)) (hilbFn PX)) : ℚ) =
      eventualValue (mixedDiff (fun _ : Fin D => ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg k₀) (hilbFn PY)) := by
    rw [eventualValue_eq (e := p₁.coeff D * D.factorial), eventualValue_eq (e := p₁.coeff D * D.factorial)]
    · rw [Filter.eventually_atTop]
      refine ⟨fun _ => ((a₀ : ℤ) + D), fun m hm => ?_⟩
      have hm' : ∀ k, (a₀ : ℤ) + D ≤ m k := hm
      have hline : m = (fun k => if k = k₀ then 0 else m k) + m k₀ • ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg k₀ := by
        funext k; by_cases hk : k = k₀ <;> simp [hk, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg]
      rw [hline, mixedDiff_line, fwdDiff_iter_eq_poly _ (lineRestr pY k₀ fun k => ((m k).toNat : ℚ)) D,
        fwdDiff_iter_poly _ ((natDegree_lineRestr_le _ _ _).trans hdeg),
        (hsand (fun k => (m k).toNat) fun k _ => by have := hm' k; omega).2]
      intro j hj
      have hs : 0 ≤ m k₀ - D + j := by have := hm' k₀; omega
      have hkey : (fun k => if k = k₀ then 0 else m k) + (m k₀ - D + j) • ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg k₀ =
          fun k => if k = k₀ then (((m k₀ - D + j).toNat : ℕ) : ℤ) else (((m k).toNat : ℕ) : ℤ) := by
        funext k
        by_cases hk : k = k₀
        · simp [hk, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg, Int.toNat_of_nonneg hs]
        · have := hm' k
          simp [hk, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg]
          omega
      rw [hkey, hY1 (fun k => (m k).toNat) _ (fun k _ => by have := hm' k; omega) (by have := hm' k₀; omega)]
      congr 1
      rw [show (((m k₀ - D + j).toNat : ℕ) : ℚ) = ((m k₀ - D + j : ℤ) : ℚ) by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg hs]]
      push_cast; ring
    · rw [Filter.eventually_atTop]
      refine ⟨fun _ => ((aX ()).toNat + D : ℤ), fun m hm => ?_⟩
      have hm' : ((aX ()).toNat + D : ℤ) ≤ m () := hm ()
      have hline : m = 0 + m () • (1 : Unit → ℤ) := by funext u; cases u; simp
      rw [hline, mixedDiff_line, fwdDiff_iter_eq_poly _ p₁ D, fwdDiff_iter_poly _ hdegX]
      intro j hj
      have hs : 0 ≤ m () - D + j := by omega
      have hkey : (0 : Unit → ℤ) + (m () - D + j) • (1 : Unit → ℤ) = fun _ => (((m () - D + j).toNat : ℕ) : ℤ) := by
        funext u; simp [Int.toNat_of_nonneg hs]
      rw [hkey, hX1 _ (by omega)]
      congr 1
      rw [show (((m () - D + j).toNat : ℕ) : ℚ) = ((m () - D + j : ℤ) : ℚ) by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg hs]]
      push_cast; ring

  apply Int.cast_injective (α := ℚ)
  unfold genDeg GroundTheory.Heights₂.Heights.NumbersDVR.intNum
  convert key using 6 <;> rfl

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockResolutionSupBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory Filter Topology

noncomputable section

namespace BlockResolutionSupBound

section Invariance

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem eval_torus {f : MRingOver ℂ ι} {k₀ : K} {n : ℕ} (hf : IsMultiHomog f (blockDeg k₀ n))
    (c : K → ℂ) (z : (Σ k, ι k) → ℂ) :
    eval (fun p => c p.1 * z p) f = c k₀ ^ n * eval z f := by
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg := hf m hm
  have hc : ∏ p : (Σ k, ι k), c p.1 ^ m p = c k₀ ^ n := by
    rw [Fintype.prod_sigma]
    simp_rw [Finset.prod_pow_eq_pow_sum, hdeg]
    rw [Fintype.prod_eq_single k₀ fun k hk => by simp [blockDeg, hk]]
    simp [blockDeg]
  simp_rw [mul_pow, Finset.prod_mul_distrib, hc]
  ring

theorem normRatio_torus {f : MRingOver ℂ ι} {k₀ : K} {n : ℕ} (hf : IsMultiHomog f (blockDeg k₀ n))
    (A : HermLine ι) (hA : A.a = unitDeg k₀) {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    ‖eval z f‖ / A.h z ^ n = ‖eval z' f‖ / A.h z' ^ n := by
  obtain ⟨c, hc, rfl⟩ := h
  rw [eval_torus hf, A.smul c z' hc, hA]
  have hprod : ∏ k, ‖c k‖ ^ unitDeg k₀ k = ‖c k₀‖ := by
    rw [Fintype.prod_eq_single k₀ fun k hk => by simp [unitDeg, hk]]
    simp [unitDeg]
  rw [hprod, norm_mul, norm_pow, mul_pow]
  have : ‖c k₀‖ ^ n ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 (hc k₀))
  rw [mul_div_mul_left _ _ this]

omit [DecidableEq K] [∀ k, Fintype (ι k)] in

theorem isOpen_blockNonzero : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  simp only [Set.ofPred_forall, Set.ofPred_exists]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

end Invariance

theorem proof (hI : BlockResolutionImageSup.Statement) (hN : NonvanishingDense.Statement) :
    BlockResolutionSupBound.Statement := by
  intro D K _ _ ι _ Ω _ _ d
  obtain ⟨C, hC⟩ := hI D K ι Ω d
  refine ⟨C, fun n hn f hf z hz => ?_⟩
  set g : ((Σ k, ι k) → ℂ) → ℝ := fun w => ‖eval w f‖ / d.A.h w ^ n with hg
  set M := C * (n : ℝ) ^ ((D : ℝ) / 2) * blockL2NormComplex d n f with hM

  have hoff : ∀ w ∈ mcPts (mCoordIdeal d.y), w ∉ mcPts d.J → g w ≤ M := by
    intro w hw hwJ
    obtain ⟨x, hx⟩ := d.R.surj w hw hwJ
    calc g w = g (blockPt d x) := (normRatio_torus hf d.A d.deg hx).symm
      _ ≤ M := hC n hn f hf x

  obtain ⟨F, hFJ, hFP⟩ := SetLike.not_le_iff_exists.1 d.R.nondeg
  set S := {w | w ∈ mcPts (mCoordIdeal d.y) ∧ eval w (map (Int.castRingHom ℂ) F) ≠ 0} with hSdef
  have hcl : z ∈ closure S := hN K ι (mCoordIdeal d.y) (D + 1) F d.arith hFP hz
  have hSM : ∀ w ∈ S, g w ≤ M := fun w hw => hoff w hw.1 fun hJ => hw.2 (hJ.2 F hFJ)
  have hcont : ContinuousAt g z := by
    have hh : ContinuousAt d.A.h z :=
      d.semipos.1.continuousOn.continuousAt (isOpen_blockNonzero.mem_nhds hz.1)
    exact (continuous_norm.comp (MvPolynomial.continuous_eval _)).continuousAt.div (hh.pow n)
      (pow_ne_zero _ (d.A.pos z hz.1).ne')
  have := mem_closure_iff_nhdsWithin_neBot.1 hcl
  exact le_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds) (eventually_nhdsWithin_of_forall hSM)

end BlockResolutionSupBound

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

