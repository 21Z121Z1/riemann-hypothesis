import Mathlib
import Formalism.PieriBlockIdeals.Bundle0001

-- bundled from Formalism.PieriBlockIdeals.PieriColumnMinors.ContentLinkageHolds
section
noncomputable section

open Finset Polynomial

namespace Formalism.CohomologicalDescent

open Classical

theorem comb_roots_prod {K : Type} [Field K] {N : ℕ} (f : Fin N → K) :
    (∏ a, (X + C (f a))).roots = Multiset.map (fun a => -f a) Finset.univ.val := by
  have h : (∏ a, (X + C (f a))) =
      ((Multiset.map (fun a => -f a) Finset.univ.val).map fun x => X - C x).prod := by
    rw [Multiset.map_map, Finset.prod_eq_multiset_prod]
    congr 1
    apply Multiset.map_congr rfl
    intro a _
    simp [sub_eq_add_neg]
  rw [h, Polynomial.roots_multiset_prod_X_sub_C]

theorem contentLinkage_holds : Linkage := by
  intro l K _ _ N U U' c hl hprod
  haveI : Fact l.Prime := ⟨hl⟩
  have hr := congrArg Polynomial.roots hprod
  have hU := comb_roots_prod (fun a => (((U a + c : ℤ)) : K))
  have hU' := comb_roots_prod (fun a => (((U' a + c : ℤ)) : K))
  rw [hU, hU'] at hr
  let ψ : ZMod l →+* K := ZMod.castHom (dvd_refl l) K
  have hψ : Function.Injective ψ := ψ.injective
  have key : ∀ V : Fin N → ℤ, Multiset.map (fun a => -(((V a + c : ℤ)) : K)) Finset.univ.val =
      Multiset.map ψ (Multiset.map (fun a => -(((V a + c : ℤ)) : ZMod l)) Finset.univ.val) := by
    intro V
    rw [Multiset.map_map]
    apply Multiset.map_congr rfl
    intro a _
    simp [ψ, map_intCast]
  rw [key U, key U'] at hr
  have h2 := Multiset.map_injective hψ hr
  have h3 := congrArg (Multiset.map fun z : ZMod l => -z - (c : ZMod l)) h2
  simp only [Multiset.map_map] at h3
  convert h3 using 2 <;> (try simp only [Function.comp_apply]; push_cast; ring)

end Formalism.CohomologicalDescent
end
end

-- bundled from Formalism.PieriBlockIdeals.PieriColumnMinors.CountLeftInvSeqAlternatingWordEven
section
noncomputable section

open Classical

namespace Formalism.CohomologicalDescent

open CoxeterSystem List

namespace ReflectionWords

variable {B : Type*} {W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

def reflStep (g : W) (p : W × ZMod 2) : W × ZMod 2 :=
  (g * p.1 * g, p.2 + if p.1 = g then 1 else 0)

lemma zmod_two_add_self (a : ZMod 2) : a + a = 0 := by fin_cases a <;> decide

lemma reflStep_involutive {g : W} (hg : g * g = 1) : Function.Involutive (reflStep g) := by
  rintro ⟨w, e⟩
  have h1 : g * (g * w * g) * g = w := by
    calc g * (g * w * g) * g = (g * g) * w * (g * g) := by group
    _ = w := by simp [hg]
  have h2 : (g * w * g = g) ↔ (w = g) := by
    constructor
    · intro h
      calc w = g * (g * w * g) * g := h1.symm
      _ = g := by rw [h, hg, one_mul]
    · rintro rfl; rw [hg, one_mul]
  simp only [reflStep, h1, h2, Prod.mk.injEq, true_and]
  rw [add_assoc, zmod_two_add_self, add_zero]

def reflPerm (i : B) : Equiv.Perm (W × ZMod 2) :=
  Function.Involutive.toPerm _ (reflStep_involutive (cs.simple_mul_simple_self i))

lemma prod_map_reflPerm (ω : List B) (w : W) (e : ZMod 2) :
    (ω.map (reflPerm cs)).prod (w, e) =
      (cs.wordProd ω * w * (cs.wordProd ω)⁻¹, e + ((cs.rightInvSeq ω).count w : ZMod 2)) := by
  induction ω with
  | nil => simp [rightInvSeq]
  | cons i ω ih =>
    rw [List.map_cons, List.prod_cons, Equiv.Perm.mul_apply, ih]
    simp only [reflPerm, Function.Involutive.coe_toPerm, reflStep, rightInvSeq, List.count_cons,
      wordProd_cons, mul_inv_rev, inv_simple]
    have key : (cs.wordProd ω)⁻¹ * cs.simple i * cs.wordProd ω = w ↔
        cs.wordProd ω * w * (cs.wordProd ω)⁻¹ = cs.simple i := by
      constructor
      · rintro rfl; group
      · intro h; rw [← h]; group
    refine Prod.ext ?_ ?_
    · simp only; group
    · by_cases h : cs.wordProd ω * w * (cs.wordProd ω)⁻¹ = cs.simple i
      · have h' := key.mpr h
        simp [h, h', add_assoc]
      · have h' : ¬ (cs.wordProd ω)⁻¹ * cs.simple i * cs.wordProd ω = w := fun hh => h (key.mp hh)
        simp [h, h']

lemma prod_map_alternatingWord {G : Type*} [Monoid G] (f : B → G) (i i' : B) (p : ℕ) :
    ((alternatingWord i i' (2 * p)).map f).prod = (f i * f i') ^ p := by
  induction p with
  | zero => simp [alternatingWord]
  | succ p ih =>
    have h : alternatingWord i i' (2 * (p + 1)) = i :: i' :: alternatingWord i i' (2 * p) := by
      rw [show 2 * (p + 1) = 2 * p + 1 + 1 by ring, alternatingWord_succ', alternatingWord_succ']
      simp
    rw [h]
    simp [ih, pow_succ', mul_assoc]

lemma reverse_alternatingWord (i i' : B) (p : ℕ) :
    (alternatingWord i i' (2 * p)).reverse = alternatingWord i' i (2 * p) := by
  induction p with
  | zero => simp [alternatingWord]
  | succ p ih =>
    have h : alternatingWord i i' (2 * (p + 1)) = i :: i' :: alternatingWord i i' (2 * p) := by
      rw [show 2 * (p + 1) = 2 * p + 1 + 1 by ring, alternatingWord_succ', alternatingWord_succ']
      simp
    rw [h, show 2 * (p + 1) = 2 * p + 1 + 1 by ring, alternatingWord_succ, alternatingWord_succ]
    simp [ih]

lemma count_leftInvSeq_alternatingWord_even (i i' : B) (w : W) :
    Even ((cs.leftInvSeq (alternatingWord i' i (2 * M i i'))).count w) := by
  set m := M i i' with hm
  set L := cs.leftInvSeq (alternatingWord i' i (2 * m)) with hL
  have hlen : L.length = 2 * m := by simp [L]
  have hper : ∀ k (hk : k < m), L[m + k]'(by omega) = L[k]'(by omega) := by
    intro k hk
    simp only [L]
    rw [cs.getElem_leftInvSeq_alternatingWord i' i m (m + k) (by omega),
      cs.getElem_leftInvSeq_alternatingWord i' i m k (by omega),
      cs.prod_alternatingWord_eq_mul_pow, cs.prod_alternatingWord_eq_mul_pow]
    have e1 : ¬ Even (2 * (m + k) + 1) := by simp
    have e2 : ¬ Even (2 * k + 1) := by simp
    simp only [e1, e2, if_false]
    rw [show (2 * (m + k) + 1) / 2 = m + k by omega, show (2 * k + 1) / 2 = k by omega, pow_add,
      hm, cs.simple_mul_simple_pow, one_mul]
  have hsplit : L = L.take m ++ L.take m := by
    conv_lhs => rw [← List.take_append_drop m L]
    congr 1
    apply List.ext_getElem
    · simp [hlen]; omega
    · intro k h1 h2
      simp only [List.getElem_drop, List.getElem_take]
      exact hper k (by simp [hlen] at h2; omega)
  rw [hsplit, List.count_append]
  exact ⟨_, rfl⟩

lemma isLiftable_reflPerm : M.IsLiftable (reflPerm cs) := by
  intro i i'
  rw [← prod_map_alternatingWord]
  refine Equiv.ext fun p => ?_
  obtain ⟨w, e⟩ := p
  rw [prod_map_reflPerm]
  have h1 : cs.wordProd (alternatingWord i i' (2 * M i i')) = 1 := by
    rw [wordProd, prod_map_alternatingWord, cs.simple_mul_simple_pow]
  have h2 : ((cs.rightInvSeq (alternatingWord i i' (2 * M i i'))).count w : ZMod 2) = 0 := by
    rw [← List.count_reverse, ← leftInvSeq_reverse, reverse_alternatingWord]
    obtain ⟨r, hr⟩ := count_leftInvSeq_alternatingWord_even cs i i' w
    rw [hr]; push_cast; exact zmod_two_add_self _
  simp [h1, h2]

def act : W →* Equiv.Perm (W × ZMod 2) := cs.lift ⟨reflPerm cs, isLiftable_reflPerm cs⟩

end ReflectionWords

universe u v

namespace ReflectionWords

lemma h11 : (1 : ZMod 2) + 1 = 0 := by decide

def transp (n : ℕ) : Finset (Equiv.Perm (Fin (n + 1))) :=
  ((Finset.univ ×ˢ Finset.univ).filter (fun p : Fin (n + 1) × Fin (n + 1) => p.1 < p.2)).image
    (fun p => Equiv.swap p.1 p.2)

end ReflectionWords

end Formalism.CohomologicalDescent
end
end

-- bundled from Formalism.PieriBlockIdeals.PieriColumnMinors.MinorValuationBoundHolds
section
noncomputable section

open Finset Polynomial

namespace Formalism.CohomologicalDescent

theorem shiftBound_holds : KapBound := by
  intro ι _ σ l h kap s hl hs hd i
  have : Nonempty ι := ⟨i⟩
  obtain ⟨j, hj⟩ := Finite.exists_max (fun x => |kap x|)
  have hL : (2 : ℤ) ≤ (l : ℤ) := by exact_mod_cast hl
  have h1 := hd (σ.symm j)
  have h2 := hs (σ.symm j)
  rw [Equiv.apply_symm_apply] at h1
  have h3 := abs_le.mp (hj (σ.symm j))
  have key : ((l : ℤ) - 1) * |kap j| ≤ (h : ℤ) := by
    rcases le_or_gt 0 (kap j) with hk | hk
    · rw [abs_of_nonneg hk] at h3 ⊢
      have e : ((l : ℤ) - 1) * kap j = (l : ℤ) * kap j - kap j := by ring
      rw [e]
      linarith [h1.2, h2.1, h3.2]
    · rw [abs_of_neg hk] at h3 ⊢
      have e : ((l : ℤ) - 1) * -kap j = -((l : ℤ) * kap j) + kap j := by ring
      rw [e]
      linarith [h1.1, h2.2, h3.1]
  have h4 : ((l : ℤ) - 1) * |kap i| ≤ ((l : ℤ) - 1) * |kap j| :=
    mul_le_mul_of_nonneg_left (hj i) (by linarith)
  exact le_trans h4 key

theorem lw_det_block {R m : Type*} [CommRing R] [DecidableEq m] [Fintype m]
    (M : Matrix m m R) (b : m → ℕ) (s : m) (hs : ∀ j, b j = b s → j = s) :
    (M.toSquareBlock b (b s)).det = M s s := by
  let _ : Unique {a // b a = b s} :=
    { default := ⟨s, rfl⟩
      uniq := fun j => Subtype.ext (hs j.1 j.2) }
  rw [Matrix.det_unique]
  rfl

theorem lw_det_inj {R m : Type*} [CommRing R] [DecidableEq m] [Fintype m]
    (M : Matrix m m R) (b : m → ℕ) (hM : M.BlockTriangular b) (hb : Function.Injective b) :
    M.det = ∏ i, M i i := by
  rw [Matrix.BlockTriangular.det hM, Finset.prod_image]
  · exact Finset.prod_congr rfl (fun i _ => lw_det_block M b i (fun j hj => hb hj))
  · intro x _ y _ hxy
    exact hb hxy

theorem charpolyDiagBlocks_holds : CharpolyBlocks := by
  intro K _ n M b S r hM hS hchar
  have hC : (Matrix.charmatrix M).BlockTriangular b := by
    intro i j hij
    have hne : i ≠ j := by
      rintro rfl
      exact lt_irrefl _ hij
    simp [hne, hM hij]
  have hdet : M.charpoly
      = ∏ a ∈ univ.image b, ((Matrix.charmatrix M).toSquareBlock b a).det :=
    Matrix.BlockTriangular.det hC
  have hdvd : ∏ s ∈ S, (X - C (M s s)) ∣ M.charpoly := by
    rw [hdet]
    have h1 : ∏ s ∈ S, (X - C (M s s))
        = ∏ a ∈ S.image b, ((Matrix.charmatrix M).toSquareBlock b a).det := by
      rw [Finset.prod_image]
      · refine Finset.prod_congr rfl (fun s hs => ?_)
        rw [lw_det_block _ b s (hS s hs), Matrix.charmatrix_apply_eq]
      · intro x hx y _ hxy
        exact (hS x hx y hxy.symm).symm
    rw [h1]
    exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.image_subset_image (Finset.subset_univ S))
  have hne : M.charpoly ≠ 0 := (Matrix.charpoly_monic M).ne_zero
  have hroots := Polynomial.roots.le_of_dvd hne hdvd
  have e1 : ∏ s ∈ S, (X - C (M s s))
      = (Multiset.map (fun a => X - C a) (S.val.map (fun s => M s s))).prod := by
    rw [Multiset.map_map]
    rfl
  have e2 : ∏ u, (X - C (r u))
      = (Multiset.map (fun a => X - C a) ((Finset.univ : Finset (Fin n)).val.map r)).prod := by
    rw [Multiset.map_map]
    rfl
  rw [e1, Polynomial.roots_multiset_prod_X_sub_C, hchar, e2,
    Polynomial.roots_multiset_prod_X_sub_C] at hroots
  exact hroots

end Formalism.CohomologicalDescent
end
end

-- bundled from Formalism.PieriBlockIdeals.PieriColumnMinors.PadicValIntProdElevenMultiples
section
noncomputable section

open Finset

namespace Formalism.CohomologicalDescent

def elevenMultiples : Finset ℤ := {11, -11, 22, -22, 33, -33, 44, -44, 55, -55, 66, -66, 77, -77}

end Formalism.CohomologicalDescent
end
end

