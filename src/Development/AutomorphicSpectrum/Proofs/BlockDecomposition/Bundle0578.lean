import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc
import Formalism.RealPlaceAnalysis.Bundle0004
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0011
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AutomorphicSpectrum.PublishedTheorems.PublishedGlobalResults.HasInfCharOfIsRegAlg
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteSpectrumGLTwoOfCuspidalSpectrum
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.EopV
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParthasarathyRaoVaradarajan
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0400
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0548
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0549
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0524

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedPolarizationIdentity
section
set_option autoImplicit false

noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.ArInt

namespace GlobalTheory.CompanionTheory.MixZ.PolarProof

theorem multilinear_eq_zero {V : Type} [AddCommGroup V] {N : ℕ}
    (M : MultilinearMap ℤ (fun _ : Fin N => V) ℝ)
    (hs : ∀ (a : Fin N → V) (σ : Equiv.Perm (Fin N)), M (a ∘ σ) = M a)
    (hd : ∀ x : V, M (fun _ => x) = 0) (a : Fin N → V) : M a = 0 := by
  classical
  have hsurj : ∀ f : Fin N → Fin N, Function.Surjective f → M (a ∘ f) = M a := fun f hf =>
    hs a (Equiv.ofBijective f ⟨Finite.injective_iff_surjective.2 hf, hf⟩)
  have expand : ∀ T : Finset (Fin N), M (fun _ => ∑ i, if i ∈ T then 0 else a i) =
      ∑ f : Fin N → Fin N, if T ⊆ (Finset.univ.image f)ᶜ then M (a ∘ f) else 0 := by
    intro T
    rw [M.map_sum (fun _ i => if i ∈ T then 0 else a i)]
    refine Finset.sum_congr rfl fun f _ => ?_
    split_ifs with h
    · congr 1
      funext j
      have : f j ∉ T := fun hj => Finset.mem_compl.1 (h hj) (Finset.mem_image_of_mem f (Finset.mem_univ j))
      simp [this]
    · obtain ⟨t, ht, hc⟩ := Finset.not_subset.1 h
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 (Finset.notMem_compl.1 hc)
      exact M.map_coord_zero j (if_pos ht)
  have hinner : ∀ f : Fin N → Fin N, ∑ T : Finset (Fin N), (-1 : ℝ) ^ T.card *
      (if T ⊆ (Finset.univ.image f)ᶜ then M (a ∘ f) else 0) =
      if Function.Surjective f then M a else 0 := by
    intro f
    have h1 : ∑ T : Finset (Fin N), (-1 : ℝ) ^ T.card *
        (if T ⊆ (Finset.univ.image f)ᶜ then M (a ∘ f) else 0) =
        (∑ T ∈ ((Finset.univ.image f)ᶜ).powerset, (-1 : ℝ) ^ T.card) * M (a ∘ f) := by
      rw [Finset.sum_mul, ← Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun T : Finset (Fin N) => T ⊆ (Finset.univ.image f)ᶜ)]
      have h2 : Finset.univ.filter (fun T : Finset (Fin N) => T ⊆ (Finset.univ.image f)ᶜ) =
          ((Finset.univ.image f)ᶜ).powerset := by
        ext T; simp
      rw [h2, Finset.sum_eq_zero (s := Finset.univ.filter _) (fun T hT => by
        rw [if_neg (Finset.mem_filter.1 hT).2, mul_zero]), add_zero]
      refine Finset.sum_congr rfl fun T hT => ?_
      rw [if_pos (Finset.mem_powerset.1 hT)]
    have h3 : (∑ T ∈ ((Finset.univ.image f)ᶜ).powerset, (-1 : ℝ) ^ T.card) =
        if (Finset.univ.image f)ᶜ = ∅ then 1 else 0 := by
      have := congrArg (Int.cast : ℤ → ℝ)
        (Finset.sum_powerset_neg_one_pow_card (x := (Finset.univ.image f)ᶜ))
      push_cast at this
      exact this
    have h4 : (Finset.univ.image f)ᶜ = ∅ ↔ Function.Surjective f := by
      rw [Finset.compl_eq_empty_iff, Finset.eq_univ_iff_forall]
      simp [Function.Surjective]
    rw [h1, h3]
    by_cases h : Function.Surjective f
    · rw [if_pos (h4.2 h), if_pos h, one_mul, hsurj f h]
    · rw [if_neg (fun e => h (h4.1 e)), if_neg h, zero_mul]
  have htot : ∑ f : Fin N → Fin N, (if Function.Surjective f then M a else 0) = 0 := by
    simp only [← hinner]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun T _ => ?_
    rw [← Finset.mul_sum, ← expand, hd, mul_zero]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul] at htot
  rcases mul_eq_zero.1 htot with h | h
  · have hc : (Finset.univ.filter fun f : Fin N → Fin N => Function.Surjective f).card ≠ 0 :=
      Finset.card_ne_zero.2 ⟨id, by simp [Function.surjective_id]⟩
    exact absurd (by exact_mod_cast h) hc
  · exact h

theorem eq_of_diag {V : Type} [AddCommGroup V] {N : ℕ} (S T : (Fin N → V) → ℝ)
    (hS : ∀ (a : Fin N → V) (σ : Equiv.Perm (Fin N)), S (a ∘ σ) = S a)
    (hT : ∀ (a : Fin N → V) (σ : Equiv.Perm (Fin N)), T (a ∘ σ) = T a)
    (aS : ∀ (a : Fin N → V) (j : Fin N) (b c : V), S (Function.update a j (b + c)) =
      S (Function.update a j b) + S (Function.update a j c))
    (aT : ∀ (a : Fin N → V) (j : Fin N) (b c : V), T (Function.update a j (b + c)) =
      T (Function.update a j b) + T (Function.update a j c))
    (hd : ∀ x : V, S (fun _ => x) = T (fun _ => x)) (a : Fin N → V) : S a = T a := by
  have aG : ∀ (a : Fin N → V) (j : Fin N) (b c : V),
      (S - T) (Function.update a j (b + c)) =
        (S - T) (Function.update a j b) + (S - T) (Function.update a j c) := by
    intro a j b c
    simp only [Pi.sub_apply, aS, aT]
    ring
  let M : MultilinearMap ℤ (fun _ : Fin N => V) ℝ :=
    { toFun := S - T
      map_update_add' := by
        intro inst m j b c
        rw [Subsingleton.elim inst (fun a b => instDecidableEqFin N a b)]
        exact aG m j b c
      map_update_smul' := by
        intro inst m j c x
        obtain rfl : inst = (fun a b => instDecidableEqFin N a b) := Subsingleton.elim _ _
        exact map_zsmul (AddMonoidHom.mk' (fun y => (S - T) (Function.update m j y)) (aG m j)) c x }
  have h := multilinear_eq_zero M
    (fun a σ => by
      change (S - T) (a ∘ σ) = (S - T) a
      simp only [Pi.sub_apply, hS, hT])
    (fun x => by
      change (S - T) (fun _ => x) = 0
      simp only [Pi.sub_apply, hd, sub_self]) a
  have h' : (S - T) a = 0 := h
  exact sub_eq_zero.1 h'

section Line

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem hermLine_ext {A B : HermLine ι} (h₁ : A.a = B.a) (h₂ : A.h = B.h) : A = B := by
  cases A
  cases B
  simp_all

theorem combLine_add {κ : Type} [Fintype κ] (A : κ → HermLine ι) (a b : κ → ℤ) :
    combLine A (a + b) = (combLine A a).tensor (combLine A b) := by
  refine hermLine_ext ?_ ?_
  · simp only [combLine, HermLine.tensor, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  · funext z
    simp only [combLine, HermLine.tensor]
    by_cases hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0
    · rw [if_pos hz, if_pos hz, if_pos hz, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun o _ => zpow_add₀ ((A o).pos z hz).ne' _ _
    · rw [if_neg hz, if_neg hz, if_neg hz, mul_zero]

theorem combLine_elim_zero {κ : Type} [Fintype κ] (A₀ : HermLine ι) (A : κ → HermLine ι) (n : κ → ℤ) :
    combLine (fun o : Option κ => o.elim A₀ A) (fun o => o.elim 0 n) = combLine A n := by
  refine hermLine_ext ?_ ?_
  · simp [combLine, Fintype.sum_option]
  · funext z
    simp [combLine, Fintype.prod_option]

theorem combLine_elim_one {κ : Type} [Fintype κ] (A₀ : HermLine ι) (A : κ → HermLine ι)
    (c₀ : ∀ z, (¬ ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → A₀.h z = 0) :
    combLine (fun o : Option κ => o.elim A₀ A) (fun o => o.elim 1 fun _ => 0) = A₀ := by
  refine hermLine_ext ?_ ?_
  · simp [combLine, Fintype.sum_option]
  · funext z
    by_cases hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0
    · simp only [combLine]
      rw [if_pos hz]
      simp [Fintype.prod_option]
    · simp only [combLine]
      rw [if_neg hz, c₀ z hz]

end Line

section Lin

variable {κ : Type} [Fintype κ]

theorem lin_add (a b : κ → ℤ) : lin (fun o => ((a + b) o : ℝ)) = lin (fun o => (a o : ℝ)) + lin (fun o => (b o : ℝ)) := by
  simp only [lin, Pi.add_apply, Int.cast_add, map_add, add_mul, Finset.sum_add_distrib]

theorem lin_elim_zero (n : κ → ℤ) :
    lin (fun o : Option κ => (((o.elim 0 n : ℤ)) : ℝ)) = rename some (lin fun i => (n i : ℝ)) := by
  simp [lin, Fintype.sum_option, map_sum, rename_X]

theorem lin_elim_one :
    lin (fun o : Option κ => (((o.elim 1 fun _ => 0 : ℤ)) : ℝ)) = MvPolynomial.X none := by
  simp [lin, Fintype.sum_option]

end Lin

theorem polar : Polar := by
  classical
  intro K _ ι _ F D κ _ A₀ A s₀ sA c₀ cA hsym hadd Φ hΦ n
  let A' : Option κ → HermLine ι := fun o => o.elim A₀ A
  have sA' : ∀ o, IsSmoothHerm (A' o) := by
    rintro (_ | j)
    exacts [s₀, sA j]
  have sC : ∀ a, IsSmoothHerm (combLine A' a) := isSmoothHerm_combLine sA'
  let l : (Option κ → ℤ) → MvPolynomial (Option κ) ℝ := fun a => lin fun o => (a o : ℝ)
  let S : (Fin (D + 1) → Option κ → ℤ) → ℝ := fun a => Φ (∏ j, l (a j))
  let T : (Fin (D + 1) → Option κ → ℤ) → ℝ := fun a => F (D + 1) fun j => combLine A' (a j)
  have hST : ∀ a, S a = T a := by
    refine eq_of_diag S T ?_ ?_ ?_ ?_ ?_
    · intro a σ
      change Φ (∏ j, l (a (σ j))) = Φ (∏ j, l (a j))
      rw [Equiv.prod_comp σ fun j => l (a j)]
    · intro a σ
      exact hsym (fun j => combLine A' (a j)) σ fun j => sC _
    · intro a j b c
      change Φ (∏ i, l (Function.update a j (b + c) i)) =
        Φ (∏ i, l (Function.update a j b i)) + Φ (∏ i, l (Function.update a j c i))
      have e : ∀ x : Option κ → ℤ, ∏ i, l (Function.update a j x i) =
          l x * ∏ i ∈ Finset.univ \ {j}, l (a i) := by
        intro x
        have := Finset.prod_update_of_mem (Finset.mem_univ j) (fun i => l (a i)) (l x)
        rw [← this]
        refine Finset.prod_congr rfl fun i _ => ?_
        by_cases h : i = j
        · subst h; simp
        · simp [Function.update_of_ne h]
      rw [e, e, e, ← map_add, ← add_mul]
      congr 2
      exact lin_add b c
    · intro a j b c
      have e : ∀ x : Option κ → ℤ, T (Function.update a j x) =
          F (D + 1) (Function.update (fun i => combLine A' (a i)) j (combLine A' x)) := by
        intro x
        change F (D + 1) (fun i => combLine A' (Function.update a j x i)) = _
        congr 1
        funext i
        by_cases h : i = j
        · subst h; simp
        · simp [Function.update_of_ne h]
      rw [e, e, e, combLine_add]
      exact hadd _ j _ _ (fun _ => sC _) (sC _) (sC _)
    · intro x
      change Φ (∏ _j : Fin (D + 1), l x) = F (D + 1) fun _ => combLine A' x
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact hΦ x
  have key := hST (Fin.snoc (fun _ : Fin D => fun o : Option κ => o.elim 0 n) fun o => o.elim 1 fun _ => 0)
  have eS : S (Fin.snoc (fun _ : Fin D => fun o : Option κ => o.elim 0 n) fun o => o.elim 1 fun _ => 0) =
      Φ (MvPolynomial.X none * rename some (lin fun i => (n i : ℝ)) ^ D) := by
    change Φ _ = _
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have h₁ := lin_elim_zero n
    have h₂ := lin_elim_one (κ := κ)
    simp only [l]
    rw [h₁, h₂, mul_comm]
  have eT : T (Fin.snoc (fun _ : Fin D => fun o : Option κ => o.elim 0 n) fun o => o.elim 1 fun _ => 0) =
      F (D + 1) (Fin.snoc (fun _ : Fin D => combLine A n) A₀) := by
    change F (D + 1) _ = _
    congr 1
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · rw [Fin.snoc_last, Fin.snoc_last]
      exact combLine_elim_one A₀ A c₀
    · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact combLine_elim_zero A₀ A n
  rw [← eS, key, eT]

end GlobalTheory.CompanionTheory.MixZ.PolarProof
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormZInvLe
section
open Ad3 Ad3.S

noncomputable section

namespace GlobalTheory.CompanionTheory.HalfIntPR

open Complex
open UpperHalfPlane hiding I

lemma cpow_ne' {x : ℂ} (hx : x ≠ 0) (w : ℂ) : x ^ w ≠ 0 := by
  rw [Complex.cpow_def_of_ne_zero hx]; exact Complex.exp_ne_zero _

lemma normSq_pos' (z : ℍ) : 0 < ‖(z : ℂ)‖ ^ 2 := by
  have : (z : ℂ) ≠ 0 := z.ne_zero
  positivity

lemma im_le_norm (z : ℍ) : z.im ≤ ‖(z : ℂ)‖ := by
  exact (le_abs_self _).trans (Complex.abs_im_le_norm (z : ℂ))

lemma w_im (z : ℍ) : (-1 / (z : ℂ)).im = z.im / ‖(z : ℂ)‖ ^ 2 := by
  have hz : (z : ℂ) ≠ 0 := z.ne_zero
  rw [neg_div, one_div, Complex.neg_im, Complex.inv_im, Complex.normSq_eq_norm_sq]
  simp [neg_div]

lemma w_im_pos (z : ℍ) : 0 < (-1 / (z : ℂ)).im := by
  rw [w_im]; exact div_pos z.im_pos (normSq_pos' z)

lemma u_eq (w : ℂ) : ((w.im : ℂ) - I * (w.re : ℂ)) = -I * w := by
  apply Complex.ext <;> simp

lemma norm_u (w : ℂ) : ‖((w.im : ℂ) - I * (w.re : ℂ))‖ = ‖w‖ := by
  rw [u_eq]; simp

lemma norm_w (z : ℍ) : ‖(-1 / (z : ℂ))‖ = ‖(z : ℂ)‖⁻¹ := by
  simp

lemma re_u (Y T : ℝ) : ((Y : ℂ) - I * (T : ℂ)).re = Y := by simp

lemma u_ne {Y : ℝ} (hY : 0 < Y) (T : ℝ) : ((Y : ℂ) - I * (T : ℂ)) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  rw [re_u] at this
  simp at this
  exact hY.ne' this

lemma v_eq (Y T : ℝ) : ((Y : ℂ) + I * (T : ℂ)) = (starRingEnd ℂ) ((Y : ℂ) - I * (T : ℂ)) := by
  apply Complex.ext <;> simp

lemma v_ne {Y : ℝ} (hY : 0 < Y) (T : ℝ) : ((Y : ℂ) + I * (T : ℂ)) ≠ 0 := by
  rw [v_eq]; exact (map_ne_zero _).2 (u_ne hY T)

lemma arg_u_ne {Y : ℝ} (hY : 0 < Y) (T : ℝ) : Complex.arg ((Y : ℂ) - I * (T : ℂ)) ≠ Real.pi := by
  intro h
  have := Complex.arg_eq_pi_iff.1 h
  rw [re_u] at this
  linarith [this.1]

lemma norm_KK (α β : ℂ) {Y : ℝ} (hY : 0 < Y) (T : ℝ) (h : α.im = β.im) :
    ‖KK α β Y T‖ = ‖((Y : ℂ) - I * (T : ℂ))‖ ^ (-(α + β).re) := by
  have hr : 0 < ‖((Y : ℂ) - I * (T : ℂ))‖ := norm_pos_iff.2 (u_ne hY T)
  unfold KK
  rw [norm_mul, Complex.norm_cpow_of_ne_zero (u_ne hY T), Complex.norm_cpow_of_ne_zero (v_ne hY T),
    v_eq, Complex.arg_conj, if_neg (arg_u_ne hY T), Complex.norm_conj, Complex.add_re, neg_add,
    Real.rpow_add hr]
  simp only [Complex.neg_re, Complex.neg_im, h]
  rw [div_mul_div_comm, ← Real.exp_add]
  have : Complex.arg ((Y : ℂ) - I * (T : ℂ)) * -β.im + -Complex.arg ((Y : ℂ) - I * (T : ℂ)) * -β.im = 0 := by ring
  rw [this]; simp

lemma one_le_Ht (z : ℍ) : z.im ≤ Ht z ∧ z.im⁻¹ ≤ Ht z ∧ 1 ≤ Ht z := by
  have hy := z.im_pos
  have hn := im_le_norm z
  have hsq : z.im ^ 2 ≤ ‖(z : ℂ)‖ ^ 2 := by gcongr
  have h1 : z.im ≤ Ht z := by
    unfold Ht
    rw [le_div_iff₀ hy]; nlinarith
  have h2 : z.im⁻¹ ≤ Ht z := by
    unfold Ht
    rw [inv_eq_one_div]
    gcongr
    nlinarith [sq_nonneg ‖(z : ℂ)‖]
  refine ⟨h1, h2, ?_⟩
  rcases le_total 1 z.im with h | h
  · exact h.trans h1
  · exact (one_le_inv₀ hy |>.2 h).trans h2

lemma w_im_le (z : ℍ) : (-1 / (z : ℂ)).im ≤ z.im⁻¹ := by
  have hy := z.im_pos
  have hn := im_le_norm z
  have hsq : z.im ^ 2 ≤ ‖(z : ℂ)‖ ^ 2 := by gcongr
  rw [w_im, inv_eq_one_div, div_le_div_iff₀ (normSq_pos' z) hy]
  nlinarith

lemma w_im_inv_le (z : ℍ) : (-1 / (z : ℂ)).im⁻¹ ≤ Ht z := by
  have hy := z.im_pos
  rw [w_im, inv_div]
  unfold Ht
  gcongr
  linarith

lemma div_L_im (z : ℍ) (L : ℕ) : (-1 / (z : ℂ) / (L : ℂ)).im = (-1 / (z : ℂ)).im / L := by
  simpa using Complex.div_natCast_im (-1 / (z : ℂ)) L

lemma norm_z_inv_le (z : ℍ) : ‖(z : ℂ)‖⁻¹ ≤ Ht z :=
  (inv_anti₀ z.im_pos (im_le_norm z)).trans (one_le_Ht z).2.1

lemma norm_pref (L k ν : ℕ) (hL : 0 < L) (s : ℂ) (z : ℍ) :
    ‖pref L k ν s z‖ = z.im ^ (om k ν s).re * (L : ℝ) ^ (-(s.re + 1 / 2)) * ‖(z : ℂ)‖⁻¹ ^ (s.re + 1 / 2) := by
  have hα : (al k ν s).im = (be k ν s).im := by simp [al, be]
  have hsum : (al k ν s + be k ν s).re = s.re + 1 / 2 := by
    simp [al, be]; ring
  unfold pref
  rw [norm_div, norm_mul, norm_KK _ _ (w_im_pos z) _ hα, norm_u, norm_w, hsum,
    Complex.norm_cpow_eq_rpow_re_of_pos z.im_pos, Complex.norm_natCast_cpow_of_pos hL,
    Real.rpow_neg (by positivity) (s.re + 1 / 2), div_inv_eq_mul]
  simp

lemma pref_diff (L k ν : ℕ) (hL : 0 < L) (z : ℍ) : Differentiable ℂ fun s => pref L k ν s z := by
  have hy : (z.im : ℂ) ≠ 0 := by exact_mod_cast z.im_pos.ne'
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hu := u_ne (w_im_pos z) (-1 / (z : ℂ)).re
  have hv := v_ne (w_im_pos z) (-1 / (z : ℂ)).re
  intro s
  unfold pref KK al be om
  refine DifferentiableAt.div (DifferentiableAt.mul ?_ ?_) (DifferentiableAt.mul ?_ ?_) ?_
  · exact DifferentiableAt.const_cpow (by fun_prop) (Or.inl hy)
  · exact DifferentiableAt.const_cpow (by fun_prop) (Or.inl hLc)
  · exact DifferentiableAt.const_cpow (by fun_prop) (Or.inl hu)
  · exact DifferentiableAt.const_cpow (by fun_prop) (Or.inl hv)
  · exact mul_ne_zero (cpow_ne' hu _) (cpow_ne' hv _)

lemma pref_meas (L k ν : ℕ) (s : ℂ) : Measurable (pref L k ν s) := by
  have hc : Measurable (fun z : ℍ => (z : ℂ)) := UpperHalfPlane.continuous_coe.measurable
  have hw : Measurable (fun z : ℍ => -1 / (z : ℂ)) := measurable_const.div hc
  have him : Measurable (fun z : ℍ => (((-1 / (z : ℂ)).im : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp (Complex.measurable_im.comp hw)
  have hre : Measurable (fun z : ℍ => (((-1 / (z : ℂ)).re : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp (Complex.measurable_re.comp hw)
  have hy : Measurable (fun z : ℍ => ((z.im : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp (Complex.measurable_im.comp hc)
  unfold pref KK
  exact ((hy.pow_const _).mul_const _).div
    (((him.sub (measurable_const.mul hre)).pow_const _).mul
      ((him.add (measurable_const.mul hre)).pow_const _))

lemma pref_bound (L k ν : ℕ) (hL : 0 < L) (b : ℝ) :
    ∃ (C : ℝ) (A : ℕ), ∀ (s : ℂ) (z : ℍ), 0 ≤ s.re → s.re ≤ b →
      ‖pref L k ν s z‖ ≤ C * Real.exp (C * s.im ^ 2) * Ht z ^ A := by
  refine ⟨1, ⌈(b + k + ν + 1) / 2⌉₊ + ⌈b + 1 / 2⌉₊, fun s z h0 hb => ?_⟩
  obtain ⟨h1, -, hH⟩ := one_le_Ht z
  have hH0 : 0 ≤ Ht z := zero_le_one.trans hH
  have hom : (om k ν s).re = (s.re + k + ν + 1) / 2 := by simp [om]
  have e1 : 0 ≤ (om k ν s).re := by rw [hom]; positivity
  have e2 : 0 ≤ s.re + 1 / 2 := by linarith
  have b1 : z.im ^ (om k ν s).re ≤ Ht z ^ (⌈(b + k + ν + 1) / 2⌉₊ : ℕ) := by
    rw [← Real.rpow_natCast]
    refine (Real.rpow_le_rpow z.im_pos.le h1 e1).trans (Real.rpow_le_rpow_of_exponent_le hH ?_)
    rw [hom]
    exact le_trans (by linarith) (Nat.le_ceil _)
  have b2 : (L : ℝ) ^ (-(s.re + 1 / 2)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hL) (by linarith)
  have b3 : ‖(z : ℂ)‖⁻¹ ^ (s.re + 1 / 2) ≤ Ht z ^ (⌈b + 1 / 2⌉₊ : ℕ) := by
    rw [← Real.rpow_natCast]
    refine (Real.rpow_le_rpow (by positivity) (norm_z_inv_le z) e2).trans
      (Real.rpow_le_rpow_of_exponent_le hH ?_)
    exact le_trans (by linarith) (Nat.le_ceil _)
  have n1 : 0 ≤ z.im ^ (om k ν s).re := Real.rpow_nonneg z.im_pos.le _
  have n2 : 0 ≤ (L : ℝ) ^ (-(s.re + 1 / 2)) := by positivity
  have n3 : 0 ≤ ‖(z : ℂ)‖⁻¹ ^ (s.re + 1 / 2) := by positivity
  have hexp : 1 ≤ Real.exp (1 * s.im ^ 2) := Real.one_le_exp (by positivity)
  have hP : 0 ≤ Ht z ^ (⌈(b + k + ν + 1) / 2⌉₊ + ⌈b + 1 / 2⌉₊) := pow_nonneg hH0 _
  rw [norm_pref L k ν hL]
  calc z.im ^ (om k ν s).re * (L : ℝ) ^ (-(s.re + 1 / 2)) * ‖(z : ℂ)‖⁻¹ ^ (s.re + 1 / 2)
      ≤ Ht z ^ (⌈(b + k + ν + 1) / 2⌉₊ : ℕ) * 1 * Ht z ^ (⌈b + 1 / 2⌉₊ : ℕ) := by
        gcongr
    _ = Ht z ^ (⌈(b + k + ν + 1) / 2⌉₊ + ⌈b + 1 / 2⌉₊) := by rw [mul_one, pow_add]
    _ ≤ 1 * Real.exp (1 * s.im ^ 2) * Ht z ^ (⌈(b + k + ν + 1) / 2⌉₊ + ⌈b + 1 / 2⌉₊) := by
        rw [one_mul]
        exact le_mul_of_one_le_left hP hexp

theorem pr : PR := by
  intro L k ν hL
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  refine ⟨pref_diff L k ν hL, pref_meas L k ν, pref_bound L k ν hL, fun z => ?_⟩
  obtain ⟨-, h2, h3⟩ := one_le_Ht z
  have hY := w_im_pos z
  refine ⟨h3, h2, ?_, ?_, ?_⟩
  · rw [div_L_im]; exact div_pos hY hL0
  · rw [div_L_im]
    exact (div_le_self hY.le hLr).trans ((w_im_le z).trans h2)
  · rw [div_L_im, inv_div, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (w_im_inv_le z) hL0.le

end GlobalTheory.CompanionTheory.HalfIntPR

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormalisedCuspFormL2Bounded
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel

namespace GlobalTheory.CompanionTheory.CuspForms

theorem memL2_and_bounded_of_normalised : GlobalTheory.Published.CuspFormsBoundedGL → ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (π : CuspSub E a), GlobalTheory.DiscSpec.IsNormalised π → ∀ φ ∈ π.V, GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ φ.1 ∧ ∃ C : ℝ, ∀ g, ‖φ.1 g‖ ≤ C := by
  intro hB E _ _ _ a μ _ _ π hπ φ hφ
  have hc := π.cusp φ hφ
  obtain ⟨C, hC⟩ := hB.of_invariant hc (hπ φ hφ)
  exact ⟨memL2_of_isAutForm hc.1 (GlobalTheory.DiscChar.isSqInt_of_bounded (hπ φ hφ) hC), C, hC⟩

end GlobalTheory.CompanionTheory.CuspForms
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParthasarathyRaoVaradarajanStatement
section
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parthasarathy_rao_varadarajan : ∀ n : ℕ, ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (c : Fin n → Fin n → Matrix ι ι ℂ), IsCliff c ∧
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (Kf : Fin n → Fin n → Module.End ℂ V)
      (S : Submodule ℂ V) (ν : Fin n → ℤ) (v : V), Formalism.REAL.GlRel Kf →
      (∀ a b (x y : V), ⟪Kf a b x, y⟫_ℂ = ⟪x, Kf b a y⟫_ℂ) → FiniteDimensional ℂ S → (∀ a b, ∀ w ∈ S, Kf a b w ∈ S) →
      v ∈ S → v ≠ 0 → Formalism.REAL.KHighest (fun _ => true) Kf (wtR ν) v →
      ∃ w : Equiv.Perm (Fin n), Antitone (fun a => wtR ν (w a) - rhoV n (w a)) ∧ ∃ x : ι → V, x ≠ 0 ∧
        Formalism.REAL.KHighest (fun _ => true) (yF Kf c) (fun a => wtR ν (w a) - rhoV n (w a)) x := by
  first | exact @GlobalTheory.CompanionTheory.SpinPRV.spin_parthasarathy_rao_varadarajan | exact GlobalTheory.CompanionTheory.SpinPRV.spin_parthasarathy_rao_varadarajan | (intros; apply GlobalTheory.CompanionTheory.SpinPRV.spin_parthasarathy_rao_varadarajan <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductLanglandsSubquotientSegmentsStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_langlands_subquotient_segments : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL), ∀ (𝔪 𝔫 : Multiset (Segment k)) (a b : IrrGL k), IsL 𝔪 a.rep → IsL 𝔫 b.rep → ∃ (h : ℕ) (z : Fin h → IrrGL k) (Δ : Fin h → Segment k) (hd : ∑ i, (z i).1 = a.1 + b.1), (∀ i, IsLSeg (Δ i) (z i).rep) ∧ Finset.univ.val.map Δ = 𝔪 + 𝔫 ∧ IsSubquotient (prod₂ a.rep b.rep) (prodIrr z hd) := by
  first | exact @GlobalTheory.CompanionTheory.LProd.prod₂_isSubquotient_prodIrr_lseg | exact GlobalTheory.CompanionTheory.LProd.prod₂_isSubquotient_prodIrr_lseg | (intros; apply GlobalTheory.CompanionTheory.LProd.prod₂_isSubquotient_prodIrr_lseg <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightTranslationLieConjugateStatement
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.right_translation_lie_conjugate : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (g : GL (Fin a) (Cinf E)) (X : Lie E a), rt E a (infGL E a g) * lie E a X = lie E a (toL (g.val * Matrix.of X * (g⁻¹).val)) * rt E a (infGL E a g) := by
  first | exact @GlobalTheory.CompanionTheory.SmoothRep.rt_infGL_mul_lie | exact GlobalTheory.CompanionTheory.SmoothRep.rt_infGL_mul_lie | (intros; apply GlobalTheory.CompanionTheory.SmoothRep.rt_infGL_mul_lie <;> assumption)
end

