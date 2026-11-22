import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosOfPosMulInnerOnJointEigenvectors
section
namespace GlobalTheory

open Module.End

theorem pos_of_pos_mul_inner_on_joint_eigenvectors_finiteDimensional {E H I : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : I → E →ₗ[ℂ] E) (hT : ∀ i, (T i).IsSymmetric) (hc : ∀ i j, Commute (T i) (T j))
    (j u : E →ₗ[ℂ] H)
    (hu : ∀ (m : I → ℝ) (y : E), (∀ i, T i y = (m i : ℂ) • y) →
      ∃ c : ℝ, 0 < c ∧ ∀ x, inner ℂ (j x) (u y) = (c : ℂ) * inner ℂ x y)
    (x : E) (hx : x ≠ 0) : (inner ℂ (j x) (u x)).im = 0 ∧ 0 < (inner ℂ (j x) (u x)).re := by
  classical
  have htop : (⨆ χ : I → ℂ, ⨅ i, eigenspace (T i) (χ i)) = ⊤ :=
    LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hT (fun a b _ => hc a b)
  have hO := LinearMap.IsSymmetric.orthogonalFamily_iInf_eigenspaces hT
  have key : ∀ (χ : I → ℂ) (y : ↥(⨅ i, eigenspace (T i) (χ i))), ∃ c : ℝ, 0 < c ∧
      ∀ z, inner ℂ (j z) (u y) = (c : ℂ) * inner ℂ z (y : E) := by
    intro χ y
    apply hu (fun i => (χ i).re) (y : E)
    intro i
    have hmem : (y : E) ∈ eigenspace (T i) (χ i) := (Submodule.mem_iInf _).mp y.2 i
    have hy : T i y = χ i • (y : E) := mem_eigenspace_iff.mp hmem
    by_cases h0 : (y : E) = 0
    · simp [h0]
    · have hr := (hT i).conj_eigenvalue_eq_self (hasEigenvalue_of_hasEigenvector ⟨hmem, h0⟩)
      have hre : ((χ i).re : ℂ) = χ i := Complex.conj_eq_iff_re.mp hr
      rw [hy, hre]
  have hx' : x ∈ ⨆ χ : I → ℂ, ⨅ i, eigenspace (T i) (χ i) := by
    rw [htop]; exact Submodule.mem_top
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.mp hx'
  obtain ⟨μ, hμ⟩ := (Submodule.mem_iSup_finset_iff_exists_sum _ x).mp hs
  choose c hc0 hcx using key
  have hself : ∀ χ ∈ s, inner ℂ x (μ χ : E) = ((‖(μ χ : E)‖ ^ 2 : ℝ) : ℂ) := by
    intro χ hχ
    rw [← hμ, sum_inner, Finset.sum_eq_single χ]
    · rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
    · intro ψ _ hψ
      simpa using hO hψ (μ ψ) (μ χ)
    · intro h; exact absurd hχ h
  have hux : u x = ∑ χ ∈ s, u (μ χ : E) := by rw [← hμ, map_sum]
  have hval : inner ℂ (j x) (u x) = ((∑ χ ∈ s, c χ (μ χ) * ‖(μ χ : E)‖ ^ 2 : ℝ) : ℂ) := by
    rw [hux, inner_sum, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    rw [hcx, hself χ hχ, Complex.ofReal_mul]
  rw [hval, Complex.ofReal_im, Complex.ofReal_re]
  refine ⟨rfl, ?_⟩
  obtain ⟨χ, hχ, hne⟩ : ∃ χ ∈ s, (μ χ : E) ≠ 0 := by
    by_contra hcon
    apply hx
    rw [← hμ]
    exact Finset.sum_eq_zero fun χ hχ => by_contra fun h => hcon ⟨χ, hχ, h⟩
  exact Finset.sum_pos' (fun ψ _ => mul_nonneg (hc0 _ _).le (sq_nonneg _))
    ⟨χ, hχ, mul_pos (hc0 _ _) (pow_pos (norm_pos_iff.mpr hne) 2)⟩

theorem pos_of_pos_mul_inner_on_joint_eigenvectors :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : V →ₗ[ℂ] H), Function.Injective ι → ∀ (W : Submodule ℂ V), FiniteDimensional ℂ W → ∀ (I : Type) (T : I → Module.End ℂ V), (∀ i, ∀ w ∈ W, T i w ∈ W) → (∀ i x y, inner ℂ (ι (T i x)) (ι y) = inner ℂ (ι x) (ι (T i y))) → (∀ i j, T i * T j = T j * T i) → ∀ (u : V →ₗ[ℂ] H), (∀ (m : I → ℝ), ∀ y ∈ W, (∀ i, T i y = (m i : ℂ) • y) → ∃ c : ℝ, 0 < c ∧ ∀ x ∈ W, inner ℂ (ι x) (u y) = (c : ℂ) * inner ℂ (ι x) (ι y)) → ∀ x ∈ W, x ≠ 0 → (inner ℂ (ι x) (u x)).im = 0 ∧ 0 < (inner ℂ (ι x) (u x)).re := by
  intro V _ _ H _ _ ι hι W hW I T hTW hsym hcomm u hu x hxW hx0
  let e : W ≃ₗ[ℂ] W.map ι := Submodule.equivMapOfInjective ι hι W
  have : FiniteDimensional ℂ (W.map ι) := e.finiteDimensional
  let T' : I → (W.map ι) →ₗ[ℂ] (W.map ι) := fun i =>
    e.toLinearMap ∘ₗ (T i).restrict (hTW i) ∘ₗ e.symm.toLinearMap
  have hesymm : ∀ z : W.map ι, ι (e.symm z : V) = (z : H) := fun z =>
    congrArg Subtype.val (e.apply_symm_apply z)
  have hTe : ∀ i (z : W.map ι), (e.symm (T' i z) : V) = T i (e.symm z) := by
    intro i z
    simp [T']
  have hT'coe : ∀ i (z : W.map ι), (T' i z : H) = ι (T i (e.symm z)) := by
    intro i z
    rw [← hesymm (T' i z), hTe]
  have hsym' : ∀ i, (T' i).IsSymmetric := by
    intro i a b
    change inner ℂ (T' i a : H) (b : H) = inner ℂ (a : H) (T' i b : H)
    rw [hT'coe, hT'coe, ← hesymm a, ← hesymm b]
    exact hsym i _ _
  have hc' : ∀ i k, Commute (T' i) (T' k) := by
    intro i k
    refine LinearMap.ext fun z => e.symm.injective (Subtype.ext ?_)
    rw [Module.End.mul_apply, Module.End.mul_apply]
    simp only [hTe]
    exact LinearMap.congr_fun (hcomm i k) _
  let u' : (W.map ι) →ₗ[ℂ] H := u ∘ₗ W.subtype ∘ₗ e.symm.toLinearMap
  have hu' : ∀ (m : I → ℝ) (y : W.map ι), (∀ i, T' i y = (m i : ℂ) • y) →
      ∃ c : ℝ, 0 < c ∧ ∀ z, inner ℂ ((W.map ι).subtype z) (u' y) = (c : ℂ) * inner ℂ z y := by
    intro m y hy
    have hy' : ∀ i, T i (e.symm y) = (m i : ℂ) • (e.symm y : V) := by
      intro i
      rw [← hTe, hy i, map_smul, Submodule.coe_smul]
    obtain ⟨c, hc, hcx⟩ := hu m (e.symm y) (e.symm y).2 hy'
    refine ⟨c, hc, fun z => ?_⟩
    have h := hcx (e.symm z) (e.symm z).2
    rw [hesymm z, hesymm y] at h
    exact h
  have hne : e ⟨x, hxW⟩ ≠ 0 := by
    intro h
    apply hx0
    have h2 : ((e ⟨x, hxW⟩ : W.map ι) : H) = 0 := by rw [h]; rfl
    exact hι ((show ι x = 0 from h2).trans (map_zero ι).symm)
  have hmain := pos_of_pos_mul_inner_on_joint_eigenvectors_finiteDimensional T' hsym' hc' (W.map ι).subtype u' hu'
    (e ⟨x, hxW⟩) hne
  have h1 : (W.map ι).subtype (e ⟨x, hxW⟩) = ι x := rfl
  have h2 : u' (e ⟨x, hxW⟩) = u x := by simp [u']
  rw [h1, h2] at hmain
  exact hmain

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosSemidefQuadraticAdjointPairBound
section
namespace GlobalTheory.PosFormAdjoint

theorem int_cauchy_schwarz {X : Type} [AddCommGroup X] (F : X →+ X →+ ℤ)
    (hsym : ∀ u v, F u v = F v u) (hpos : ∀ u, 0 ≤ F u u) (u v : X) :
    F u v ^ 2 ≤ F u u * F v v := by
  have key : ∀ a b : ℤ, 0 ≤ a ^ 2 * F u u + 2 * a * b * F u v + b ^ 2 * F v v := by
    intro a b
    have h1 := hpos (a • u + b • v)
    have e : F (a • u + b • v) (a • u + b • v)
        = a ^ 2 * F u u + 2 * a * b * F u v + b ^ 2 * F v v := by
      simp only [map_add, map_zsmul, AddMonoidHom.add_apply, AddMonoidHom.smul_apply, smul_eq_mul]
      rw [hsym v u]
      ring
    rw [e] at h1
    exact h1
  rcases (hpos u).lt_or_eq with ht | ht
  · have h2 := key (-(F u v)) (F u u)
    have h3 : 0 ≤ F u u * (F u u * F v v - F u v ^ 2) := by nlinarith [h2]
    have h4 : 0 ≤ F u u * F v v - F u v ^ 2 := by
      by_contra hc
      push_neg at hc
      nlinarith [mul_neg_of_pos_of_neg ht hc]
    linarith
  · rw [← ht]
    simp only [zero_mul]
    by_contra hc
    push_neg at hc
    have hs : (1 : ℤ) ≤ F u v ^ 2 := hc
    have h2 := key (-(F v v + 1) * F u v) 1
    rw [← ht] at h2
    have hv := hpos v
    nlinarith [h2, hs, hv]

theorem seq_bound (a c : ℕ → ℤ) (n : ℕ) (hpos : ∀ k, 0 ≤ a k)
    (hlc : ∀ k, a (k + 1) ^ 2 ≤ a k * a (k + 2))
    (hrec : a n + ∑ i ∈ Finset.range n, c i * a i = 0) :
    a 1 ≤ (((∑ i ∈ Finset.range n, (c i).natAbs : ℕ) + 1 : ℕ) : ℤ) * a 0 := by
  set S : ℤ := ∑ i ∈ Finset.range n, |c i| with hS
  have hcast : (((∑ i ∈ Finset.range n, (c i).natAbs : ℕ) + 1 : ℕ) : ℤ) = S + 1 := by
    push_cast
    simp [hS, Int.natCast_natAbs]
  rw [hcast]
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  by_contra H
  push_neg at H
  have ha0 : 0 < a 0 := by
    rcases (hpos 0).lt_or_eq with h | h
    · exact h
    · exfalso
      have h1 := hlc 0
      rw [← h] at h1 H
      simp at h1 H
      nlinarith [sq_nonneg (a 1)]
  have h01 : a 0 < a 1 := by nlinarith
  have hind : ∀ k, 0 < a k ∧ a 1 * a k ≤ a (k + 1) * a 0 := by
    intro k
    induction k with
    | zero => exact ⟨ha0, by simp [mul_comm]⟩
    | succ k ih =>
      obtain ⟨hk, hk'⟩ := ih
      have hk1 : 0 < a (k + 1) := by
        by_contra hc
        push_neg at hc
        nlinarith [mul_pos (by linarith : (0:ℤ) < a 1) hk]
      refine ⟨hk1, ?_⟩
      have h2 := hlc k
      have h3 : a k * (a 1 * a (k + 1)) ≤ a k * (a (k + 2) * a 0) := by
        nlinarith [mul_le_mul_of_nonneg_left hk' hk1.le]
      exact le_of_mul_le_mul_left h3 hk
  have hmono : ∀ k, a k ≤ a (k + 1) := by
    intro k
    obtain ⟨hk, hk'⟩ := hind k
    have : a 0 * a k ≤ a 0 * a (k + 1) := by nlinarith [mul_le_mul_of_nonneg_right h01.le hk.le]
    exact le_of_mul_le_mul_left this ha0
  have hmono' : Monotone a := monotone_nat_of_le_succ hmono
  rcases n with _ | m
  · simp at hrec
    linarith
  · rw [Finset.sum_range_succ] at hrec
    obtain ⟨hm, hm'⟩ := hind m
    have hle : -(∑ i ∈ Finset.range (m + 1), c i * a i) ≤ S * a m := by
      rw [hS, Finset.sum_mul, ← Finset.sum_neg_distrib]
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have h1 : -(c i * a i) ≤ |c i| * a i := by
        have := neg_abs_le (c i)
        nlinarith [hpos i]
      have h2 : |c i| * a i ≤ |c i| * a m :=
        mul_le_mul_of_nonneg_left (hmono' hi') (abs_nonneg _)
      linarith
    have hrec' : a (m + 1) = -(∑ i ∈ Finset.range (m + 1), c i * a i) := by
      rw [Finset.sum_range_succ]; linarith
    have h5 : (S + 1) * a 0 * a m < a 1 * a m := by nlinarith
    have h6 : (S + 1) * a m * a 0 < a (m + 1) * a 0 := by nlinarith
    have h7 : (S + 1) * a m < a (m + 1) := lt_of_mul_lt_mul_right h6 ha0.le
    nlinarith

end GlobalTheory.PosFormAdjoint

namespace GlobalTheory.PosFormAdjoint

theorem pos_form_adjoint_bound : ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (h h' : X →+ X), ∃ C : ℕ, ∀ q : X → ℤ, (∀ y, 0 ≤ q y) → q 0 = 0 → (∀ y, q (-y) = q y) →
      (∀ x y z, q (x + y + z) + q x + q y + q z = q (x + y) + q (x + z) + q (y + z)) →
      (∀ y z, q (h y + z) + q y + q (h' z) = q (y + h' z) + q (h y) + q z) →
      ∀ y, q (h y) ≤ C * q y := by
  intro X _ _ _ h h'
  let T : Module.End ℤ X := h'.toIntLinearMap * h.toIntLinearMap
  have hT : ∀ u, T u = h' (h u) := fun u => rfl
  let p := T.charpoly
  refine ⟨(∑ i ∈ Finset.range p.natDegree, (-(p.coeff i)).natAbs) + 1, ?_⟩
  intro q hq hq0 hqneg hcube hadj y
  let B : X →+ X →+ ℤ := AddMonoidHom.mk' (fun u => AddMonoidHom.mk' (fun v => q (u + v) - q u - q v)
      (fun a b => by
        have := hcube u a b
        rw [← add_assoc]
        linarith))
    (fun a b => by
      ext v
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
      have := hcube a b v
      linarith)
  have hB : ∀ u v, B u v = q (u + v) - q u - q v := fun u v => rfl
  have Bsym : ∀ u v, B u v = B v u := by
    intro u v; rw [hB, hB, add_comm]; ring
  have Bdiag : ∀ u, B u u = 2 * q u := by
    intro u
    have := hcube u u (-u)
    simp only [add_neg_cancel_right, add_neg_cancel, hq0, hqneg] at this
    rw [hB]; linarith
  have Badj : ∀ u v, B (h u) v = B u (h' v) := by
    intro u v; rw [hB, hB]; have := hadj u v; linarith
  have BT : ∀ u v, B (T u) v = B u (T v) := by
    intro u v
    rw [hT, hT, Bsym, ← Badj, Bsym, Badj]
  have BTpow : ∀ k u v, B ((T ^ k) u) v = B u ((T ^ k) v) := by
    intro k
    induction k with
    | zero => intro u v; rfl
    | succ k ih =>
      intro u v
      rw [pow_succ', Module.End.mul_apply, BT, ih]
      congr 1
      rw [← Module.End.mul_apply, ← pow_succ, ← pow_succ']
  let G : X →+ X →+ ℤ := B.comp (T : X →+ X)
  have hG : ∀ u v, G u v = B (T u) v := fun u v => rfl
  have Gsym : ∀ u v, G u v = G v u := by
    intro u v; rw [hG, hG, BT, Bsym]
  have Gdiag : ∀ u, G u u = 2 * q (h u) := by
    intro u; rw [hG, hT, Bsym, ← Badj, Bdiag]
  have Bpos : ∀ u, 0 ≤ B u u := fun u => by rw [Bdiag]; linarith [hq u]
  have Gpos : ∀ u, 0 ≤ G u u := fun u => by rw [Gdiag]; linarith [hq (h u)]
  let a : ℕ → ℤ := fun k => B ((T ^ k) y) y
  have aB : ∀ i j, a (i + j) = B ((T ^ i) y) ((T ^ j) y) := by
    intro i j
    show B ((T ^ (i + j)) y) y = _
    rw [pow_add, Module.End.mul_apply, BTpow]
    exact Bsym _ _
  have aG : ∀ i j, a (i + j + 1) = G ((T ^ i) y) ((T ^ j) y) := by
    intro i j
    rw [hG, ← Module.End.mul_apply, ← pow_succ', add_right_comm, aB]
  have apos : ∀ k, 0 ≤ a k := by
    intro k
    rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
    · rw [two_mul, aB]; exact Bpos _
    · rw [two_mul, aG]; exact Gpos _
  have alc : ∀ k, a (k + 1) ^ 2 ≤ a k * a (k + 2) := by
    intro k
    rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
    · have e1 : a (2 * m + 1) = B ((T ^ m) y) ((T ^ (m + 1)) y) := by
        rw [← aB]; congr 1; ring
      have e2 : a (2 * m + 2) = B ((T ^ (m + 1)) y) ((T ^ (m + 1)) y) := by
        rw [← aB]; congr 1; ring
      rw [e1, e2, two_mul, aB]
      exact int_cauchy_schwarz B Bsym Bpos _ _
    · have e1 : a (2 * m + 1 + 1) = G ((T ^ m) y) ((T ^ (m + 1)) y) := by
        rw [← aG]; congr 1; ring
      have e2 : a (2 * m + 1 + 2) = G ((T ^ (m + 1)) y) ((T ^ (m + 1)) y) := by
        rw [← aG]; congr 1; ring
      rw [e1, e2, two_mul, aG]
      exact int_cauchy_schwarz G Gsym Gpos _ _
  have hmonic : p.Monic := LinearMap.charpoly_monic T
  have hrec : a p.natDegree + ∑ i ∈ Finset.range p.natDegree, p.coeff i * a i = 0 := by
    have hCH : (Polynomial.aeval T p) y = 0 := by
      rw [LinearMap.aeval_self_charpoly]; rfl
    rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ, hmonic.coeff_natDegree, one_smul] at hCH
    have h2 := congrArg (fun x => B x y) hCH
    simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_add,
      map_sum, map_zsmul, AddMonoidHom.add_apply, AddMonoidHom.finset_sum_apply,
      AddMonoidHom.smul_apply, smul_eq_mul, map_zero, AddMonoidHom.zero_apply] at h2
    rw [add_comm]; exact h2
  have hb := seq_bound a (fun i => p.coeff i) p.natDegree apos alc hrec
  have a0 : a 0 = 2 * q y := by show B ((T ^ 0) y) y = _; rw [pow_zero]; exact Bdiag y
  have a1 : a 1 = 2 * q (h y) := by
    have := aG 0 0
    simp only [zero_add, pow_zero] at this
    rw [this]; exact Gdiag y
  rw [a0, a1] at hb
  have habs : ∀ i, (-(p.coeff i)).natAbs = (p.coeff i).natAbs := fun i => Int.natAbs_neg _
  simp only [habs]
  linarith

end GlobalTheory.PosFormAdjoint
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowDivMemOfEsymmPowDivMem
section
open Polynomial

namespace GlobalTheory

theorem pow_div_mem_of_esymm_pow_div_mem (K : Type) [Field K] (V : ValuationSubring K)
    (A : Type) [Fintype A] (x : A → K) (D : ℕ) (c : K) (hc : c ≠ 0)
    (h : ∀ k : ℕ, 1 ≤ k → k ≤ Fintype.card A →
      k ∣ D ∧ (Finset.univ.val.map x).esymm k ^ (D / k) / c ∈ V) (a : A) :
    x a ^ D / c ∈ V := by
  classical
  set v := V.valuation with hv
  set s : Multiset K := Finset.univ.val.map x with hs
  have hcard : Multiset.card s = Fintype.card A := by simp [s, Finset.card_univ]
  have hn : 1 ≤ Multiset.card s := hcard ▸ Fintype.card_pos_iff.mpr ⟨a⟩
  have hvc : v c ≠ 0 := (Valuation.ne_zero_iff v).mpr hc
  have mem_iff : ∀ y : K, y / c ∈ V ↔ v y ≤ v c := by
    intro y
    rw [← V.valuation_le_one_iff, ← hv, map_div₀, div_le_one₀ (zero_lt_iff.mpr hvc)]
  rw [mem_iff]
  by_contra hlt
  push_neg at hlt
  rw [Valuation.map_pow] at hlt
  have key : ∀ k, 1 ≤ k → k ≤ Multiset.card s → v (s.esymm k) < v (x a) ^ k := by
    intro k hk1 hkn
    obtain ⟨hkD, hmem⟩ := h k hk1 (hcard ▸ hkn)
    rw [mem_iff, Valuation.map_pow] at hmem
    by_contra hge
    push_neg at hge
    have hp : (v (x a) ^ k) ^ (D / k) ≤ v (s.esymm k) ^ (D / k) := pow_le_pow_left₀ zero_le' hge _
    rw [← pow_mul, Nat.mul_div_cancel' hkD] at hp
    exact absurd (hp.trans hmem) (not_le.mpr hlt)
  have hpos : 0 < v (x a) := by
    have := key 1 le_rfl hn
    rw [pow_one] at this
    exact lt_of_le_of_lt zero_le' this
  have h0 : (s.map fun t => X - C t).prod.eval (x a) = 0 := by
    rw [Polynomial.eval_multiset_prod, Multiset.prod_eq_zero_iff]
    simp only [Multiset.map_map, Function.comp_def, eval_sub, eval_X, eval_C]
    exact Multiset.mem_map.mpr ⟨x a, by simp [s], sub_self _⟩
  rw [Multiset.prod_X_sub_X_eq_sum_esymm, eval_finset_sum, Finset.sum_range_succ'] at h0
  simp only [eval_mul, eval_pow, eval_neg, eval_one, eval_C, eval_X, pow_zero, one_mul,
    Nat.sub_zero] at h0
  have he0 : s.esymm 0 = 1 := by simp [Multiset.esymm, Multiset.powersetCard_zero_left]
  rw [he0, one_mul, ← eq_neg_iff_add_eq_zero] at h0
  have hlt2 : v (∑ j ∈ Finset.range (Multiset.card s),
      (-1) ^ (j + 1) * (s.esymm (j + 1) * x a ^ (Multiset.card s - (j + 1)))) < v (x a) ^ Multiset.card s := by
    apply Valuation.map_sum_lt _ (pow_ne_zero _ hpos.ne')
    intro j hj
    have hj' : j + 1 ≤ Multiset.card s := Finset.mem_range.mp hj
    rw [map_mul, map_mul, map_pow, map_pow, Valuation.map_neg, map_one, one_pow, one_mul]
    calc v (s.esymm (j + 1)) * v (x a) ^ (Multiset.card s - (j + 1))
        < v (x a) ^ (j + 1) * v (x a) ^ (Multiset.card s - (j + 1)) :=
          mul_lt_mul_of_pos_right (key (j + 1) (Nat.succ_le_succ (Nat.zero_le _)) hj') (pow_pos hpos _)
      _ = v (x a) ^ Multiset.card s := by rw [← pow_add, Nat.add_sub_cancel' hj']
  rw [h0, Valuation.map_neg, map_pow] at hlt2
  exact lt_irrefl _ hlt2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowMapsTorsionIntoSmulTop
section
namespace GlobalTheory

open Submodule in

theorem pow_maps_torsion_into_smul_top (R : Type) [CommRing R] [IsDedekindDomain R] (M : Type)
    [AddCommGroup M] [Module R M] (I J : Ideal R) (f : M →ₗ[R] M) (m : ℕ) :
    I.IsMaximal → J ≠ ⊥ → (∀ x, (f ^ m) x ∈ I • (⊤ : Submodule R M)) →
      ∃ j : ℕ, ∀ y : M, (∀ a ∈ I, a • y ∈ J • (⊤ : Submodule R M)) →
        (f ^ j) y ∈ J • (⊤ : Submodule R M) := by
  intro hI hJ hf
  obtain ⟨Q, hIQ, hJQ⟩ := Ideal.eq_prime_pow_mul_coprime hJ I
  set k := Multiset.count I (UniqueFactorizationMonoid.normalizedFactors J)

  have hstab : ∀ (n : ℕ) (z : M), z ∈ J • (⊤ : Submodule R M) → (f ^ n) z ∈ J • (⊤ : Submodule R M) := by
    intro n z hz
    have : (J • (⊤ : Submodule R M)).map (f ^ n) ≤ J • (⊤ : Submodule R M) := by
      rw [Submodule.map_smul'']
      exact Submodule.smul_mono le_rfl le_top
    exact this ⟨z, hz, rfl⟩

  have hmap : (⊤ : Submodule R M).map (f ^ m) ≤ I • (⊤ : Submodule R M) := by
    rintro _ ⟨x, -, rfl⟩
    exact hf x
  have hpow : ∀ (i : ℕ) (x : M), (f ^ (m * i)) x ∈ I ^ i • (⊤ : Submodule R M) := by
    intro i
    induction i with
    | zero => intro x; simp
    | succ i ih =>
      intro x
      have h1 : (f ^ (m * (i + 1))) x = (f ^ m) ((f ^ (m * i)) x) := by
        rw [Nat.mul_succ, add_comm, pow_add, Module.End.mul_apply]
      rw [h1]
      have h2 : (I ^ i • (⊤ : Submodule R M)).map (f ^ m) ≤ I ^ (i + 1) • (⊤ : Submodule R M) := by
        rw [Submodule.map_smul'', pow_succ, Submodule.mul_smul]
        exact Submodule.smul_mono le_rfl hmap
      exact h2 ⟨_, ih x, rfl⟩
  refine ⟨m * k, fun y hy => ?_⟩
  set Z := (f ^ (m * k)) y with hZ
  have hZk : Z ∈ I ^ k • (⊤ : Submodule R M) := hpow k y
  have hIZ : ∀ a ∈ I, a • Z ∈ J • (⊤ : Submodule R M) := by
    intro a ha
    rw [hZ, ← LinearMap.map_smul]
    exact hstab _ _ (hy a ha)
  have hJle : J ≤ Q := by rw [hJQ]; exact Ideal.mul_le_inf.trans inf_le_right
  have hZQ : Z ∈ Q • (⊤ : Submodule R M) := by
    have h1 : (1 : R) ∈ I ⊔ Q := by rw [hIQ]; trivial
    obtain ⟨t, ht, s, hs, hts⟩ := Submodule.mem_sup.1 h1
    have : Z = t • Z + s • Z := by rw [← add_smul, hts, one_smul]
    rw [this]
    refine Submodule.add_mem _ ?_ (Submodule.smul_mem_smul hs trivial)
    exact Submodule.smul_mono_left hJle (hIZ t ht)
  have hkQ : I ^ k ⊔ Q = ⊤ := by
    rw [← Ideal.isCoprime_iff_sup_eq] at hIQ ⊢
    exact hIQ.pow_left
  have h1 : (1 : R) ∈ I ^ k ⊔ Q := by rw [hkQ]; trivial
  obtain ⟨t, ht, s, hs, hts⟩ := Submodule.mem_sup.1 h1
  have : Z = t • Z + s • Z := by rw [← add_smul, hts, one_smul]
  rw [this]
  refine Submodule.add_mem _ ?_ ?_
  · have : t • Z ∈ I ^ k • Q • (⊤ : Submodule R M) := Submodule.smul_mem_smul ht hZQ
    rwa [← Submodule.mul_smul, ← hJQ] at this
  · have : s • Z ∈ Q • I ^ k • (⊤ : Submodule R M) := Submodule.smul_mem_smul hs hZk
    rwa [← Submodule.mul_smul, mul_comm, ← hJQ] at this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreirreducibleSpaceTensorOfPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem isPullback_comp_mono_right_of_isPullback {𝒞 : Type*} [Category 𝒞] {P X Y Z Z' : 𝒞} {fst : P ⟶ X} {snd : P ⟶ Y}
    {a : X ⟶ Z} {b : Y ⟶ Z} (m : Z ⟶ Z') [Mono m] (h : IsPullback fst snd a b) :
    IsPullback fst snd (a ≫ m) (b ≫ m) :=
  ⟨⟨by rw [← Category.assoc, h.w, Category.assoc]⟩, ⟨PullbackCone.IsLimit.mk _
    (fun c ↦ h.lift c.fst c.snd (by rw [← cancel_mono m]; simpa using c.condition))
    (fun c ↦ h.lift_fst _ _ _) (fun c ↦ h.lift_snd _ _ _)
    (fun c n h₁ h₂ ↦ h.hom_ext (by rw [h.lift_fst, h₁]) (by rw [h.lift_snd, h₂]))⟩⟩

theorem preirreducibleSpace_tensor_of_pullback :
    ∀ (X S : Scheme.{0}) (f : X ⟶ S) (V : S.Opens) (W : X.Opens) (h : W ≤ f ⁻¹ᵁ V)
      (hV : IsAffineOpen V) (hW : IsAffineOpen W) (k : Type) [Field k] [Algebra Γ(S, V) k]
      [Algebra Γ(S, V) Γ(X, W)], algebraMap Γ(S, V) Γ(X, W) = (f.appLE V W h).hom →
      PreirreducibleSpace ↥(pullback (W.ι ≫ f)
        (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) k)) ≫ hV.fromSpec)) →
      PreirreducibleSpace (PrimeSpectrum (k ⊗[Γ(S, V)] Γ(X, W))) := by
  intro X S f V W h hV hW k _ _ _ hA hP
  have sq := (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct Γ(S, V) k Γ(X, W))).flip
  have sq2 := sq.of_iso (fst' := Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) ≫
      hW.isoSpec.inv) (snd' := Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom))
    (f' := hW.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) Γ(X, W))))
    (g' := Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) k)))
    (Iso.refl _) hW.isoSpec.symm (Iso.refl _) (Iso.refl _)
    (by simp) (by simp) (by simp) (by simp)
  have sq3 := isPullback_comp_mono_right_of_isPullback hV.fromSpec sq2
  have e : (hW.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) Γ(X, W)))) ≫
      hV.fromSpec = W.ι ≫ f := by
    rw [hA, CommRingCat.ofHom_hom, Category.assoc, IsAffineOpen.SpecMap_appLE_fromSpec f hV hW h,
      ← hW.isoSpec_inv_ι, Category.assoc, Iso.hom_inv_id_assoc]
  rw [e] at sq3
  let φ := sq3.isoPullback
  have hsurj : Function.Surjective (Scheme.homeoOfIso φ.symm) := (Scheme.homeoOfIso φ.symm).surjective
  refine ⟨?_⟩
  have := (PreirreducibleSpace.isPreirreducible_univ (X := ↥(pullback (W.ι ≫ f)
        (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) k)) ≫ hV.fromSpec)))).image
    (Scheme.homeoOfIso φ.symm) (Scheme.homeoOfIso φ.symm).continuous.continuousOn
  rw [Set.image_univ_of_surjective hsurj] at this
  exact this

end GlobalTheory
end

