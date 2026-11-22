import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0054
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0045
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0048
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0053
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0055

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.FlagSpanVanishing
section
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P

namespace FlagSpanVanishing

open C2x5 C2x7

variable {k r : ℕ}

lemma flagSpan_vanish (z : Fin (2 * r + k + 1) → ℂ) (a : Fin (r + 1)) (v : Fin (2 * r + k + 1) → ℂ)
    (hv : v ∈ C2.flagSpan k r z a) (i : Fin (2 * r + k + 1)) (hi : a.val ≤ i.val) : v i = 0 := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨b, hb⟩, rfl⟩ := hx
    have hbr : b.val < r := by have := a.isLt; rw [Fin.lt_def] at hb; omega
    simp only [fvec, dif_pos hbr, bvec, Pi.single_apply, eI]
    rw [if_neg]
    intro e; rw [Fin.lt_def] at hb; have := congrArg Fin.val e; simp at this; omega
  | zero => rfl
  | add x y _ _ hx hy => simp [hx, hy]
  | smul c x _ hx => simp [hx]

lemma mulVec_bvec (M : B.Mat k r) (x : Fin (2 * r + k + 1)) : M *ᵥ bvec x = fun i => M i x := by
  funext i; simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]

def wpart (s : B.Mat k r) : B.Mat k r := fun i j =>
  if r ≤ i.val ∧ i.val ≤ r + k ∧ r ≤ j.val ∧ j.val ≤ r + k then s i j else if i = j then 1 else 0

lemma zero_block (s : B.Mat k r) (hs : s ∈ B.GV k r)
    (hcol : ∀ (a : Fin r) (i : Fin (2 * r + k + 1)), a.val ≤ i.val → s i (eI k r a) = if i = eI k r a then 1 else 0)
    (j : Fin (2 * r + k + 1)) (hj1 : r ≤ j.val) (hj2 : j.val ≤ r + k) :
    ∀ n : ℕ, ∀ a : Fin r, a.val = n → s (esI k r a) j = 0 := by
  have hU : sᴴ * Hpk k r * s = Hpk k r := hs
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a ha
    have e := congrFun (congrFun hU (eI k r a)) j
    rw [Matrix.mul_assoc, Matrix.mul_apply] at e
    simp only [C2x6.Hpk_mul_apply, Matrix.conjTranspose_apply] at e
    have hH : Hpk k r (eI k r a) j = 0 := by
      rw [GBasic.Hpk_eq, if_neg]
      intro h'; have := congrArg Fin.val h'
      rw [GBasic.sig_lo _ _ _ (by simp [eI])] at this; simp [eI] at this; omega
    rw [hH, Finset.sum_eq_single (eI k r a)] at e
    · rw [hcol a _ (by simp [eI]), if_pos rfl, star_one, one_mul] at e
      have hsig : GBasic.sig k r (eI k r a) = esI k r a := by
        apply Fin.ext; rw [GBasic.sig_lo _ _ _ (by simp [eI])]; simp [eI, esI]
      have hsg : GBasic.sgn k r (eI k r a) = 1 := by
        unfold GBasic.sgn; rw [if_neg]; simp [eI]; omega
      rw [hsig, hsg, one_mul] at e
      exact e
    · intro p _ hp
      by_cases hpa : a.val ≤ p.val
      · rw [hcol a p hpa, if_neg hp, star_zero, zero_mul]
      · push_neg at hpa
        have hpr : p.val < r := by omega
        have hsig : GBasic.sig k r p = esI k r ⟨p.val, hpr⟩ := by
          apply Fin.ext; rw [GBasic.sig_lo _ _ _ hpr]; simp [esI]
        rw [hsig, ih p.val (by omega) ⟨p.val, hpr⟩ rfl, mul_zero, mul_zero]
    · simp

end FlagSpanVanishing

namespace FlagSpanVanishing

open C2x5 C2x7

variable {k r : ℕ}

lemma sig_notW (x : Fin (2 * r + k + 1)) (hx : ¬ (r ≤ x.val ∧ x.val ≤ r + k)) :
    ¬ (r ≤ (GBasic.sig k r x).val ∧ (GBasic.sig k r x).val ≤ r + k) := by
  have := GBasic.sig_val k r x
  have hx' := x.isLt
  split_ifs at this <;> omega

lemma sig_fixes_middle_block (x : Fin (2 * r + k + 1)) (hx : r ≤ x.val ∧ x.val ≤ r + k) : GBasic.sig k r x = x :=
  GBasic.sig_mid k r x hx.1 hx.2

lemma wpart_uh (s : B.Mat k r) (hs : s ∈ B.GV k r)
    (hA : ∀ p j : Fin (2 * r + k + 1), r + k < p.val → r ≤ j.val → j.val ≤ r + k → s p j = 0) :
    wpart s ∈ UH (Hpk k r) := by
  have hU : sᴴ * Hpk k r * s = Hpk k r := hs
  show (wpart s)ᴴ * Hpk k r * wpart s = Hpk k r
  ext i j
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  simp only [C2x6.Hpk_mul_apply, Matrix.conjTranspose_apply]
  by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
  · by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
    · have e := congrFun (congrFun hU i) j
      rw [Matrix.mul_assoc, Matrix.mul_apply] at e
      simp only [C2x6.Hpk_mul_apply, Matrix.conjTranspose_apply] at e
      rw [← e]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      by_cases hp : r ≤ p.val ∧ p.val ≤ r + k
      · rw [sig_fixes_middle_block p hp]
        simp only [wpart, if_pos (And.intro hp.1 (And.intro hp.2 (And.intro hi.1 hi.2))),
          if_pos (And.intro hp.1 (And.intro hp.2 (And.intro hj.1 hj.2)))]
      · have h1 : wpart s p i = 0 := by
          simp only [wpart]; rw [if_neg (fun h => hp ⟨h.1, h.2.1⟩), if_neg]
          intro e; rw [e] at hp; exact hp hi
        rw [h1, star_zero, zero_mul]
        by_cases hpr : p.val < r
        · have : r + k < (GBasic.sig k r p).val := by rw [GBasic.sig_lo _ _ _ hpr]; omega
          rw [hA _ j this hj.1 hj.2, mul_zero, mul_zero]
        · have : r + k < p.val := by omega
          rw [hA p i this hi.1 hi.2, star_zero, zero_mul]
    · rw [Finset.sum_eq_single (GBasic.sig k r j)]
      · have h1 : wpart s (GBasic.sig k r j) i = 0 := by
          simp only [wpart]
          rw [if_neg (fun h => sig_notW j hj ⟨h.1, h.2.1⟩), if_neg]
          intro e; rw [← e] at hi; exact sig_notW j hj hi
        rw [h1, star_zero, zero_mul, GBasic.Hpk_eq, if_neg]
        intro e; rw [sig_fixes_middle_block i hi] at e; rw [e] at hj; exact hj hi
      · intro p _ hp
        have : wpart s (GBasic.sig k r p) j = 0 := by
          simp only [wpart]; rw [if_neg (fun h => hj ⟨h.2.2.1, h.2.2.2⟩), if_neg]
          intro e; apply hp; rw [← e, GBasic.sig_sig]
        rw [this, mul_zero, mul_zero]
      · simp
  · rw [Finset.sum_eq_single i]
    · have h1 : wpart s i i = 1 := by
        simp only [wpart]; rw [if_neg (fun h => hi ⟨h.1, h.2.1⟩)]; simp
      have h2 : wpart s (GBasic.sig k r i) j = if GBasic.sig k r i = j then 1 else 0 := by
        simp only [wpart]; rw [if_neg (fun h => sig_notW i hi ⟨h.1, h.2.1⟩)]
      rw [h1, star_one, one_mul, h2, GBasic.Hpk_eq]
      by_cases e : GBasic.sig k r i = j
      · rw [if_pos e, if_pos e.symm, mul_one]
      · rw [if_neg e, if_neg (fun h => e h.symm), mul_zero]
    · intro p _ hp
      have : wpart s p i = 0 := by
        simp only [wpart]; rw [if_neg (fun h => hi ⟨h.2.2.1, h.2.2.2⟩), if_neg hp]
      rw [this, star_zero, zero_mul]
    · simp

end FlagSpanVanishing

open C2x5 C2x7 FlagSpanVanishing

theorem standard_flag_property : C2.SFlag := by
  intro k r z hz
  ext s
  constructor
  · rintro ⟨hs, hfl⟩
    have hcol : ∀ (a : Fin r) (i : Fin (2 * r + k + 1)), a.val ≤ i.val →
        s i (eI k r a) = if i = eI k r a then 1 else 0 := by
      intro a i hi
      have h := flagSpan_vanish z (Fin.castSucc a) _ (hfl (Fin.castSucc a)) i (by simpa using hi)
      have hf : fvec k r z (Fin.castSucc a) = bvec (eI k r a) := by rw [fvec, dif_pos (by simp)]; rfl
      rw [hf, mulVec_bvec, Pi.sub_apply, sub_eq_zero] at h
      rw [h]; simp [bvec, Pi.single_apply]
    have hzc : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → (s *ᵥ z) i = z i := by
      intro i hi
      have h := flagSpan_vanish z (Fin.last r) _ (hfl (Fin.last r)) i (by simpa using hi)
      have hf : fvec k r z (Fin.last r) = z := by rw [fvec, dif_neg (by simp)]
      rw [hf, Pi.sub_apply, sub_eq_zero] at h; exact h
    have hA : ∀ p j : Fin (2 * r + k + 1), r + k < p.val → r ≤ j.val → j.val ≤ r + k → s p j = 0 := by
      intro p j hp hj1 hj2
      have hpa : 2 * r + k - p.val < r := by omega
      have e : esI k r ⟨2 * r + k - p.val, hpa⟩ = p := Fin.ext (by simp [esI]; omega)
      rw [← e]; exact zero_block s hs hcol j hj1 hj2 _ _ rfl
    have hhU := wpart_uh s hs hA
    set h := wpart s with hh
    have hhW : h ∈ UWset k r z := by
      refine ⟨hhU, fun a => ⟨?_, ?_⟩, ?_⟩
      · rw [mulVec_bvec]; funext i
        simp only [hh, wpart, bvec, Pi.single_apply]
        rw [if_neg (by intro h'; have := h'.2.2.1; simp only [eI] at this; omega)]
      · rw [mulVec_bvec]; funext i
        simp only [hh, wpart, bvec, Pi.single_apply]
        rw [if_neg (by intro h'; have := h'.2.2.2; simp only [esI] at this; omega)]
      · funext i
        by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
        · rw [← hzc i hi.1]
          simp only [Matrix.mulVec, dotProduct]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
          · simp only [hh, wpart, if_pos (And.intro hi.1 (And.intro hi.2 hj))]
          · have hzj : z j = 0 := hz.1 j (by omega)
            rw [hzj, mul_zero, mul_zero]
        · simp only [Matrix.mulVec, dotProduct]
          rw [Finset.sum_eq_single i]
          · simp only [hh, wpart]; rw [if_neg (fun h' => hi ⟨h'.1, h'.2.1⟩)]; simp
          · intro j _ hj
            simp only [hh, wpart]; rw [if_neg (fun h' => hi ⟨h'.1, h'.2.1⟩), if_neg (Ne.symm hj), zero_mul]
          · simp
    have hhu : IsUnit h.det := WeylGroupFacts.isUnit_of_uh hhU
    have hblk := WeylGroupFacts.uw_block (WeylGroupFacts.uw_inv hhW)
    refine ⟨h, hhW, h⁻¹ * s, ?_, ?_⟩
    · rw [WeylGroupFacts.nset_iff]
      refine ⟨WeylGroupFacts.uh_mul (WeylGroupFacts.uh_inv hhU) hs, fun i j hj hij => ?_⟩
      rw [Matrix.mul_apply]
      by_cases hjr : j.val < r
      · have e : eI k r ⟨j.val, hjr⟩ = j := Fin.ext rfl
        have hterm : ∀ p, h⁻¹ i p * s p j = (if i = p then 1 else 0) * s p j := by
          intro p
          by_cases hpr : p.val < r
          · rw [hblk.1 i p (Or.inl hpr)]
          · have := hcol ⟨j.val, hjr⟩ p (by simp; omega)
            rw [e, if_neg (fun e' => hpr (by rw [e']; exact hjr))] at this
            rw [this, mul_zero, mul_zero]
        simp only [hterm, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
        have := hcol ⟨j.val, hjr⟩ i (by simp; omega)
        rw [e] at this; exact this
      · have hir : r ≤ i.val := by omega
        have hterm : ∀ p, h⁻¹ i p * s p j = h⁻¹ i p * h p j := by
          intro p
          by_cases hpr : p.val < r
          · rw [hblk.1 i p (Or.inl hpr), if_neg (fun e' => by rw [e'] at hir; omega), zero_mul, zero_mul]
          · by_cases hpk : p.val ≤ r + k
            · simp only [hh, wpart]
              rw [if_pos ⟨by omega, hpk, by omega, hj⟩]
            · rw [hA p j (by omega) (by omega) hj]
              simp only [hh, wpart]
              rw [if_neg (fun h' => hpk h'.2.1), if_neg (fun e' => by rw [e'] at hpk; exact hpk hj)]
        simp only [hterm]
        rw [← Matrix.mul_apply, Matrix.nonsing_inv_mul _ hhu, Matrix.one_apply]
    · rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hhu, Matrix.one_mul]
  · intro hs
    refine ⟨Sset_UH hs, fun a => ?_⟩
    obtain ⟨U, hU1, hU2, hsF⟩ := S_F hz.1 hs
    rw [colEq hsF a]
    have hfa : fvec k r z a = ∑ c, (if c = a then (1 : ℂ) else 0) • fvec k r z c := by
      simp [ite_smul]
    rw [hfa, ← Finset.sum_sub_distrib]
    apply Submodule.sum_mem
    intro c _
    rw [← sub_smul]
    by_cases hca : c < a
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨c, hca⟩, rfl⟩)
    · have : U c a - (if c = a then 1 else 0) = 0 := by
        rcases eq_or_lt_of_le (not_lt.mp hca) with e | e
        · rw [← e, hU2, if_pos rfl, sub_self]
        · rw [hU1 c a e, if_neg (ne_of_gt e), sub_self]
      rw [this, zero_smul]; exact Submodule.zero_mem _

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LeDivOfMulEqLe
section
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P

open C2x2 EntryMinorBounds

lemma le_div_of_mul_eq_le (x c D Kb : ℝ) (hc : 0 < c) (hD : D ≤ Kb) (h : x * c = D) : x ≤ Kb / c := by
  rw [le_div_iff₀ hc, h]; exact hD

theorem monomial_factorization_bound : C2.MonomialFactorizationBound := by
  intro m P hP
  obtain ⟨w, d, hd, rfl⟩ := hP
  have hcn : ∀ a : Fin m, C2.minorS (C2.monoP w d) (C2.wSet w (a.val + 1)) (C2.iSet m (a.val + 1)) ≠ 0 :=
    fun a => minor_C_nonzero m w d hd (a.val + 1) a.isLt
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (Nat.factorial m : ℝ) := ⟨_, rfl⟩
  have hK1 : 1 ≤ K := by rw [hK]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero m)
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 1 + ∑ a : Fin m,
      K / ‖C2.minorS (C2.monoP w d) (C2.wSet w (a.val + 1)) (C2.iSet m (a.val + 1))‖ := ⟨_, rfl⟩
  have hterm0 : ∀ a : Fin m, 0 ≤ K / ‖C2.minorS (C2.monoP w d) (C2.wSet w (a.val + 1)) (C2.iSet m (a.val + 1))‖ :=
    fun a => div_nonneg (by linarith) (norm_nonneg _)
  have hB1 : 1 ≤ B := by rw [hB]; linarith [Finset.sum_nonneg (fun a (_ : a ∈ Finset.univ) => hterm0 a)]
  have hBa : ∀ a : Fin m, K / ‖C2.minorS (C2.monoP w d) (C2.wSet w (a.val + 1)) (C2.iSet m (a.val + 1))‖ ≤ B := by
    intro a; rw [hB]
    linarith [Finset.single_le_sum (fun a (_ : a ∈ Finset.univ) => hterm0 a) (Finset.mem_univ a)]
  refine ⟨K * B ^ m, fun l hl u' hu => ?_⟩
  obtain ⟨Y, hY⟩ : ∃ Y, Y = C2.mx (l * C2.monoP w d * u') := ⟨_, rfl⟩
  rw [← hY]
  have hY0 : 0 ≤ Y := by rw [hY]; exact norm_nonneg _
  have hY1 : 1 ≤ (1 + Y) ^ m := one_le_pow₀ (by linarith)
  have hΔ : ∀ I J : Finset (Fin m), ‖C2.minorS (l * C2.monoP w d * u') I J‖ ≤ K * (1 + Y) ^ m := by
    intro I J; rw [hK, hY]; exact minor_le _ I J
  have hEB : 0 ≤ B * (1 + Y) ^ m := by positivity
  have hfin : ∀ (a : Fin m) (x : ℝ) (J : Finset (Fin m)),
      x * ‖C2.minorS (C2.monoP w d) (C2.wSet w (a.val + 1)) (C2.iSet m (a.val + 1))‖ =
        ‖C2.minorS (l * C2.monoP w d * u') (C2.wSet w (a.val + 1)) J‖ → x ≤ B * (1 + Y) ^ m := by
    intro a x J hx
    have hcpos := norm_pos_iff.mpr (hcn a)
    calc x ≤ K * (1 + Y) ^ m / ‖C2.minorS (C2.monoP w d) (C2.wSet w (a.val + 1)) (C2.iSet m (a.val + 1))‖ :=
          le_div_of_mul_eq_le _ _ _ _ hcpos (hΔ _ _) hx
      _ = (K / ‖C2.minorS (C2.monoP w d) (C2.wSet w (a.val + 1)) (C2.iSet m (a.val + 1))‖) * (1 + Y) ^ m := by
          ring
      _ ≤ B * (1 + Y) ^ m := mul_le_mul_of_nonneg_right (hBa a) (by positivity)
  have hfin' : ∀ (a : Fin m) (x : ℝ) (J : Finset (Fin m)),
      x * ‖C2.minorS (C2.monoP w d) (C2.wSet w (a.val + 1)) (C2.iSet m (a.val + 1))‖ =
        ‖C2.minorS (l * C2.monoP w d * u') J (C2.iSet m (a.val + 1))‖ → x ≤ B * (1 + Y) ^ m := by
    intro a x J hx
    have hcpos := norm_pos_iff.mpr (hcn a)
    calc x ≤ K * (1 + Y) ^ m / ‖C2.minorS (C2.monoP w d) (C2.wSet w (a.val + 1)) (C2.iSet m (a.val + 1))‖ :=
          le_div_of_mul_eq_le _ _ _ _ hcpos (hΔ _ _) hx
      _ = (K / ‖C2.minorS (C2.monoP w d) (C2.wSet w (a.val + 1)) (C2.iSet m (a.val + 1))‖) * (1 + Y) ^ m := by
          ring
      _ ≤ B * (1 + Y) ^ m := mul_le_mul_of_nonneg_right (hBa a) (by positivity)
  have hu_ent : ∀ a b, ‖u' a b‖ ≤ B * (1 + Y) ^ m := by
    intro a b
    rcases lt_trichotomy a b with h | rfl | h
    · obtain ⟨ε, hε, hf⟩ := upper_minor_identity m w d hd a b h
      have e := hf l hl u' hu
      have hεn : ‖ε‖ = 1 := by rcases hε with rfl | rfl <;> simp
      exact hfin a _ _ (by rw [← norm_mul, e, norm_mul, hεn, one_mul])
    · rw [hu.2, norm_one]; nlinarith
    · rw [hu.1 a b h, norm_zero]; exact hEB
  have hl_ent : ∀ x y, ‖l x y‖ ≤ B * (1 + Y) ^ m := by
    intro x y
    obtain ⟨a, rfl⟩ : ∃ a, y = w a := ⟨w.symm y, by simp⟩
    by_cases hx : x ∈ C2.wSet w a.val
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      have hpa : p < a := by
        simp only [C2.iSet, Finset.mem_filter, Finset.mem_univ, true_and] at hp; rw [Fin.lt_def]; exact hp
      rw [lower_parabolic_entry_zero w d hd l hl p a hpa, norm_zero]; exact hEB
    · obtain ⟨ε, hε, hf⟩ := lower_minor_identity m w d hd a x hx
      have e := hf l hl u' hu
      have hεn : ‖ε‖ = 1 := by rcases hε with rfl | rfl <;> simp
      exact hfin' a _ _ (by rw [← norm_mul, e, norm_mul, hεn, one_mul])
  have hX1 : 1 ≤ B * (1 + Y) ^ m := by nlinarith
  have hinvl : ∀ i j, ‖l⁻¹ i j‖ ≤ K * (B * (1 + Y) ^ m) ^ (m - 1) := fun i j => by
    rw [hK]; exact inv_entry_le l (lt_det hl.1) _ hX1 hl_ent i j
  have hinvu : ∀ i j, ‖u'⁻¹ i j‖ ≤ K * (B * (1 + Y) ^ m) ^ (m - 1) := fun i j => by
    rw [hK]; exact inv_entry_le u' (ut_det hu) _ hX1 hu_ent i j
  have hpow : K * (B * (1 + Y) ^ m) ^ (m - 1) ≤ K * B ^ m * (1 + Y) ^ ((m - 1) * m) := by
    rw [mul_pow, ← pow_mul, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    rw [mul_comm m (m - 1)]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hB1 (Nat.sub_le m 1)) (by positivity)
  have hfirst : B * (1 + Y) ^ m ≤ K * B ^ m * (1 + Y) ^ m := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0
      rw [hB, Finset.univ_eq_empty, Finset.sum_empty, add_zero, pow_zero, mul_one]; exact hK1
    · calc B = B ^ 1 := (pow_one B).symm
        _ ≤ B ^ m := pow_le_pow_right₀ hB1 hpos
        _ ≤ K * B ^ m := le_mul_of_one_le_left (by positivity) hK1
  have hI0 : 0 ≤ K * (B * (1 + Y) ^ m) ^ (m - 1) := by positivity
  exact ⟨(mx_le l _ hEB hl_ent).trans hfirst, (mx_le u' _ hEB hu_ent).trans hfirst,
    (mx_le _ _ hI0 hinvl).trans hpow, (mx_le _ _ hI0 hinvu).trans hpow⟩

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftTypeAction
section
open Matrix Finset Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace QrD

section Left

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq]
  [NormedSpace ℂ Wq] [FiniteDimensional ℂ Wp] {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
  {π' : Mx k r → (Wq →L[ℂ] Wq)} {D : Set (Mx k r)} {J : Mx k r → (Wq →L[ℂ] Wp)}

theorem mem_left (hD : IsDom k r z z' (Fin.last r) D) {g h : Mx k r} (hg : g ∈ Glev k r (Fin.last r) ∩ D)
    (hh : h ∈ UWset k r z) : h * g ∈ Glev k r (Fin.last r) ∩ D := by
  obtain ⟨hgG, hgD⟩ := hg
  refine ⟨?_, ?_⟩
  · simp only [Glev, UH, UWset, Set.mem_setOf_eq] at hgG hh ⊢
    refine ⟨?_, fun a ha => ?_⟩
    · rw [conjTranspose_mul]
      calc gᴴ * hᴴ * Hpk k r * (h * g) = gᴴ * (hᴴ * Hpk k r * h) * g := by simp only [Matrix.mul_assoc]
        _ = Hpk k r := by rw [hh.1, hgG.1]
    · rw [← mulVec_mulVec, ← mulVec_mulVec, (hgG.2 a ha).1, (hgG.2 a ha).2]
      exact hh.2.1 a
  · have h1z' : (1 : Mx k r) ∈ UWset k r z' := by simp [UWset, UH]
    have h1N : (1 : Mx k r) ∈ Nlev k r (Fin.last r) := by simp [Nlev, QuantumDeterminants.Nset, Glev, UH, Matrix.one_apply]
    have hS := hD.2 g ⟨hgG, hgD⟩ h ⟨h, hh, 1, h1N, by simp⟩ 1 ⟨1, h1z', 1, h1N, by simp⟩
    simpa using hS

theorem J_left (hπ : IsCRepOn (UWset k r z) π) (hJ : J ∈ FFl k r z z' π π' (Fin.last r) D) {g h : Mx k r}
    (hg : g ∈ Glev k r (Fin.last r) ∩ D) (hh : h ∈ UWset k r z) : J (h * g) = (π h).comp (J g) := by
  have h1z : (1 : Mx k r) ∈ UWset k r z := by simp [UWset, UH]
  have h1z' : (1 : Mx k r) ∈ UWset k r z' := by simp [UWset, UH]
  simp only [FFl, Set.mem_setOf_eq] at hJ
  have e1 := hJ.2.2.2 g hg 1 h1z 1 h1z'
  have e2 := hJ.2.2.2 g hg h hh 1 h1z'
  rw [one_mul, mul_one, hπ.1] at e1
  have e1' : J g ∘SL π' 1 = J g := by
    ext x
    exact (congrArg (fun T => T x) e1).symm
  rw [mul_one] at e2
  rw [e2, e1']

theorem ld_left (hD : IsDom k r z z' (Fin.last r) D) (hπ : IsCRepOn (UWset k r z) π)
    (hc : ContinuousOn π (UWset k r z)) (hJ : J ∈ FFl k r z z' π π' (Fin.last r) D)
    {F : Mx k r → (Wq →L[ℂ] Wp)} {B : Wp →L[ℂ] Wp}
    (hF : ∀ g ∈ Glev k r (Fin.last r) ∩ D, F g = B.comp (J g)) {X : Mx k r} (hX : InLieW k r z X)
    {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r) ∩ D) : LdV X F g = (B.comp (dOp π X)).comp (J g) := by
  have hfun : (fun t : ℝ => F (NormedSpace.exp ((t : ℂ) • X) * g)) =
      fun t : ℝ => (B.comp (π (NormedSpace.exp ((t : ℂ) • X)))).comp (J g) := by
    funext t
    have hu := exp_uw hX t
    rw [hF _ (mem_left hD hg hu), J_left hπ hJ hg hu, ContinuousLinearMap.comp_assoc]
  unfold LdV
  rw [hfun]
  have hd := dOp_hasDeriv hπ hc hX
  let L : (Wp →L[ℂ] Wp) →L[ℝ] (Wq →L[ℂ] Wp) :=
    (((ContinuousLinearMap.compL ℂ Wq Wp Wp).flip (J g)).comp
      ((ContinuousLinearMap.compL ℂ Wp Wp Wp) B)).restrictScalars ℝ
  have key : HasDerivAt (fun t : ℝ => (B.comp (π (NormedSpace.exp ((t : ℂ) • X)))).comp (J g))
      ((B.comp (dOp π X)).comp (J g)) 0 := by
    have h2 := L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
    convert h2 using 1
    all_goals first | rfl | (ext; rfl)
  exact key.deriv

theorem lz_left (hD : IsDom k r z z' (Fin.last r) D) (hπ : IsCRepOn (UWset k r z) π)
    (hc : ContinuousOn π (UWset k r z)) (hJ : J ∈ FFl k r z z' π π' (Fin.last r) D)
    {F : Mx k r → (Wq →L[ℂ] Wp)} {B : Wp →L[ℂ] Wp}
    (hF : ∀ g ∈ Glev k r (Fin.last r) ∩ D, F g = B.comp (J g)) {Z : Mx k r}
    (h1 : InLieW k r z (hpart1 (Hpk k r) Z)) (h2 : InLieW k r z (hpart2 (Hpk k r) Z))
    {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r) ∩ D) :
    LZ (Hpk k r) Z F g = (B.comp (ecOp π Z)).comp (J g) := by
  unfold LZ
  rw [ld_left hD hπ hc hJ hF h1 hg, ld_left hD hπ hc hJ hF h2 hg]
  ext v
  simp [ecOp]

theorem fold_left (hD : IsDom k r z z' (Fin.last r) D) (hπ : IsCRepOn (UWset k r z) π)
    (hc : ContinuousOn π (UWset k r z)) (hJ : J ∈ FFl k r z z' π π' (Fin.last r) D)
    (L : List (ℂ × Mx k r))
    (hL : ∀ p ∈ L, InLieW k r z (hpart1 (Hpk k r) p.2) ∧ InLieW k r z (hpart2 (Hpk k r) p.2)) :
    ∀ (F : Mx k r → (Wq →L[ℂ] Wp)) (B : Wp →L[ℂ] Wp), (∀ g ∈ Glev k r (Fin.last r) ∩ D, F g = B.comp (J g)) →
      ∀ g ∈ Glev k r (Fin.last r) ∩ D, ∀ v,
        (L.map fun p => fun y : Mx k r → (Wq →L[ℂ] Wp) => p.1 • y + LZ (Hpk k r) p.2 y).foldl (fun h T => T h) F g v =
          B ((L.map fun p => fun y : Wp => p.1 • y + EcRep (Hpk k r) π p.2 y).foldr (fun T h => T h) (J g v)) := by
  induction L with
  | nil => intro F B hF g hg v; simp [hF g hg]
  | cons p L ih =>
    intro F B hF g hg v
    obtain ⟨h1, h2⟩ := hL p (by simp)
    have hF' : ∀ g ∈ Glev k r (Fin.last r) ∩ D,
        (p.1 • F + LZ (Hpk k r) p.2 F) g = (p.1 • B + B.comp (ecOp π p.2)).comp (J g) := by
      intro g hg
      rw [Pi.add_apply, Pi.smul_apply, lz_left hD hπ hc hJ hF h1 h2 hg, hF g hg]
      ext x
      simp
    have := ih (fun q hq => hL q (by simp [hq])) _ _ hF' g hg v
    simp only [List.map_cons, List.foldl_cons, List.foldr_cons]
    rw [this]
    simp [ecRep_eq hπ hc h1 h2]

end Left

end QrD

theorem left_type_action : Formalism.FourierDecayAlt.Q.LeftTypeAction := by
  intro Wp Wq _ _ _ _ _ k r m z z' π π' D hz hz' hD hπ hc J hJ g hg Bs hB w v
  unfold capLft capRep qmFrev qmF
  have key : ∀ σ : Equiv.Perm (Fin m), ∀ g ∈ Glev k r (Fin.last r) ∩ D, ∀ v,
      ((List.ofFn fun j => ((if σ j = j then w - ((j : ℕ) : ℂ) else 0), unitB (Hpk k r) Bs (σ j) j)).map
          fun p => fun y : Mx k r → (Wq →L[ℂ] Wp) => p.1 • y + LZ (Hpk k r) p.2 y).foldl (fun h T => T h) J g v =
        (ContinuousLinearMap.id ℂ Wp)
          (((List.ofFn fun j => ((if σ j = j then w - ((j : ℕ) : ℂ) else 0), unitB (Hpk k r) Bs (σ j) j)).map
            fun p => fun y : Wp => p.1 • y + EcRep (Hpk k r) π p.2 y).foldr (fun T h => T h) (J g v)) :=
    fun σ => QrD.fold_left hD hπ hc hJ _ (by
      intro p hp
      simp only [List.mem_ofFn] at hp
      obtain ⟨j, rfl⟩ := hp
      exact QrD.frame_lie hB (σ j) j) J (ContinuousLinearMap.id ℂ Wp) (fun g _ => by simp)
  simp only [List.map_ofFn, Function.comp_def, ite_smul, zero_smul, ContinuousLinearMap.id_apply] at key
  simp only [id, Finset.sum_apply, Pi.smul_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [key σ g hg v]

end Formalism.FourierDecayAlt.P
end
end

