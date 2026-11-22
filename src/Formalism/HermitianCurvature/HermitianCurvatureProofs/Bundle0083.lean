import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0077
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0075
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0079
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0060
import Formalism.HermitianCurvature.HermitianCurvatureProofs.InverseSplitting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0051
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0076

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutoffIteratedFDerivBounded
section
open Matrix Set
open scoped ComplexConjugate ContDiff Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.AdmissibleLieWords

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

lemma ckOn_of_lss {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : Mat k r → E} {S : Set (Mat k r)}
    (h : LSS f S) (m : ℕ∞) : CkOn m S f := by
  intro g hg
  obtain ⟨f', hf', V, hV, hgV, hfe⟩ := h g hg
  refine ⟨V, f', hV, hgV, (hf'.of_le ?_).contDiffOn, fun g' hg' hG => hfe g' hG hg'⟩
  exact WithTop.coe_le_coe.mpr le_top

section fac

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

lemma ubl_epart (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (hfib : ∀ j, C6.FibBound D (fib j)) {ε : ℝ} (hε : 0 < ε) {S : Set (Mat k r)}
    (hS : ∀ g ∈ S, g ∈ GV k r ∧ ε ≤ Gf k r D.z D.z' g) (n : ℕ) :
    ∀ es : List (Fin nf × List (Mat k r)), (∀ e ∈ es, ∀ X ∈ e.2, inLie k r X) →
      UBL (C6.Epart fib es) S n (3 * (r + 1) * (es.map fun e => e.2.length).sum) (3 * (r + 1)) := by
  have hSG : S ⊆ GV k r := fun g hg => (hS g hg).1
  intro es
  induction es with
  | nil =>
    intro _
    have e0 : C6.Epart fib ([] : List (Fin nf × List (Mat k r))) = fun _ => 1 := by
      funext g
      simp [C6.Epart]
    rw [e0]
    simpa using ubl_const (1 : C6.EndH Wp Wq) hSG n (3 * (r + 1))
  | cons e es ih =>
    intro hes
    have hA := ubl_fib D (fib e.1) (hfib e.1) hε hS e.2 (hes e (by simp)) n
    have hB := ih (fun e' he' => hes e' (List.mem_cons_of_mem _ he'))
    have hL := ubl_clm ((ContinuousLinearMap.mul ℂ (C6.EndH Wp Wq)).restrictScalars ℝ) hSG hA
    have hAB := ubl_app hSG hL hB
    have e1 : C6.Epart fib (e :: es) =
        fun g => ((ContinuousLinearMap.mul ℂ (C6.EndH Wp Wq)).restrictScalars ℝ
          (Rw e.2 (fib e.1) g)) (C6.Epart fib es g) := by
      funext g
      simp [C6.Epart]
    rw [e1]
    convert hAB using 2
    simp only [List.map_cons, List.sum_cons]
    ring

lemma ubl_coefP (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (hfib : ∀ j, C6.FibBound D (fib j)) (L : Finset (Fin (r + 2))) {κ : ℕ} (P : Mat k r → ℂ)
    (a b : Fin (r + 2) → ℕ) (c : ℕ) (es : List (Fin nf × List (Mat k r))) (hP : U.IsPolyDeg κ P)
    (hab : ∀ l, l ∉ L → l ≠ Fin.last (r + 1) → a l = 0 ∧ b l = 0) (hes : ∀ e ∈ es, ∀ X ∈ e.2, inLie k r X)
    {ε : ℝ} (hε : 0 < ε) {S : Set (Mat k r)} (hS : ∀ g ∈ S, g ∈ GV k r ∧ ε ≤ Gf k r D.z D.z' g)
    {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hSD : ∀ g ∈ S, ∀ l, (l ∈ L ∨ l = Fin.last (r + 1)) → c₀ ≤ Complex.normSq (Dmin k r D.z D.z' g l))
    (hSGf : ∀ g ∈ S, c₀ ≤ Complex.normSq ((Gf k r D.z D.z' g : ℝ) : ℂ)) (n : ℕ) :
    UBL (fun g => (P g * C6.monoM D a b c g) • C6.Epart fib es g) S n
      (κ + 3 * (r + 1) * (es.map fun e => e.2.length).sum) (3 * (r + 1)) := by
  have hSG : S ⊆ GV k r := fun g hg => (hS g hg).1
  have hP' := ubl_poly hP S hSG n (3 * (r + 1))
  have hM := ubl_mono hSG (ubl_monoM D L a b c hab hSG hc₀ hSD hSGf n) le_rfl
    (show 2 * r + 2 ≤ 3 * (r + 1) by omega)
  have hPM := ubl_mul hSG hP' hM
  have hE := ubl_epart D fib hfib hε hS n es hes
  let Lm : ℂ →L[ℝ] (C6.EndH Wp Wq →L[ℂ] C6.EndH Wp Wq) :=
    (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ)
      (ContinuousLinearMap.id ℂ (C6.EndH Wp Wq))).restrictScalars ℝ
  have hA := ubl_clm Lm hSG hPM
  have hAE := ubl_app hSG hA hE
  have e1 : (fun g => (P g * C6.monoM D a b c g) • C6.Epart fib es g) =
      fun g => Lm (P g * C6.monoM D a b c g) (C6.Epart fib es g) := by
    funext g
    simp [Lm]
  rw [e1]
  simpa using hAE

end fac

section cut

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

private lemma contDiff_of_isPolyDeg {N κ : ℕ} {P : Matrix (Fin N) (Fin N) ℂ → ℂ} (hP : U.IsPolyDeg κ P) :
    ContDiff ℝ ∞ P := by
  obtain ⟨q, -, hq⟩ := hP
  rw [show P = fun g => MvPolynomial.eval (Sum.elim (fun x => g x.1 x.2)
    (fun x => star (g x.1 x.2))) q from funext hq]
  clear hq
  induction q using MvPolynomial.induction_on with
  | C a => simpa using contDiff_const
  | add p q hp hq => simpa only [map_add] using hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.eval_X]
    refine hp.mul ?_
    rcases i with x | x
    · exact contDiff_apply_apply ℝ ℂ x.1 x.2
    · exact Complex.conjCLE.contDiff.comp (contDiff_apply_apply ℝ ℂ x.1 x.2)

private lemma exists_bound_iteratedFDeriv_cutoff_normSq {χ₀ : ℝ → ℝ} (hχ : C6.IsCut0 χ₀) (de : ℝ) (j : ℕ) :
    ∃ B : ℝ, ∀ y : ℂ,
      ‖iteratedFDeriv ℝ j (fun y : ℂ => ((χ₀ (Complex.normSq y / de) : ℝ) : ℂ)) y‖ ≤ B := by
  obtain ⟨hs, ⟨δ, hδ, h0⟩, h1⟩ := hχ
  set Φ : ℂ → ℂ := fun y => ((χ₀ (Complex.normSq y / de) : ℝ) : ℂ) with hΦdef
  have hns : ContDiff ℝ ∞ (fun y : ℂ => Complex.normSq y) := by
    simp only [Complex.normSq_apply]
    exact (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
      (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)
  have hΦ : ContDiff ℝ ∞ Φ := Complex.ofRealCLM.contDiff.comp (hs.comp (hns.div_const de))
  have hc : Continuous (iteratedFDeriv ℝ j Φ) :=
    hΦ.continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr (by exact_mod_cast le_top))
  have hconst : ∀ (c x y : ℂ), iteratedFDeriv ℝ j (fun _ : ℂ => c) x =
      iteratedFDeriv ℝ j (fun _ : ℂ => c) y := by
    intro c x y
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp [iteratedFDeriv_zero_eq_comp]
    · rw [iteratedFDeriv_const_of_ne hj.ne']
      rfl
  obtain ⟨c, R, hR0, hloc⟩ : ∃ c : ℂ, ∃ R : ℝ, 0 ≤ R ∧
      ∀ y : ℂ, R < ‖y‖ → Φ =ᶠ[nhds y] fun _ => c := by
    rcases le_or_gt de 0 with hde | hde
    · refine ⟨0, 0, le_rfl, fun y _ => Filter.Eventually.of_forall fun z => ?_⟩
      have hz : Complex.normSq z / de ≤ 0 :=
        div_nonpos_of_nonneg_of_nonpos (Complex.normSq_nonneg z) hde
      show ((χ₀ (Complex.normSq z / de) : ℝ) : ℂ) = 0
      rw [h0 _ (by linarith)]
      simp
    · refine ⟨1, de + 1, by linarith, fun y hy => ?_⟩
      have hopen : IsOpen {z : ℂ | de + 1 < ‖z‖} := isOpen_lt continuous_const continuous_norm
      filter_upwards [hopen.mem_nhds hy] with z hz
      have hz' : de + 1 < ‖z‖ := hz
      have hn : de ≤ Complex.normSq z := by
        rw [Complex.normSq_eq_norm_sq]
        nlinarith [norm_nonneg z]
      have h1' : 1 ≤ Complex.normSq z / de := by
        rw [le_div_iff₀ hde]
        linarith
      show ((χ₀ (Complex.normSq z / de) : ℝ) : ℂ) = 1
      rw [h1 _ h1']
      simp
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) (R + 1)).exists_bound_of_continuousOn
    hc.continuousOn
  have y0n : ‖((R + 1 : ℝ) : ℂ)‖ = R + 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  refine ⟨B, fun y => ?_⟩
  rcases le_or_gt ‖y‖ (R + 1) with hy | hy
  · exact hB y (by rw [mem_closedBall_zero_iff]; exact hy)
  · have e1 := ((hloc y (by linarith)).iteratedFDeriv (𝕜 := ℝ) j).eq_of_nhds
    have e2 := ((hloc ((R + 1 : ℝ) : ℂ) (by rw [y0n]; linarith)).iteratedFDeriv
      (𝕜 := ℝ) j).eq_of_nhds
    rw [e1, hconst c y ((R + 1 : ℝ) : ℂ), ← e2]
    exact hB _ (by rw [mem_closedBall_zero_iff, y0n])

lemma ubl_chi (D : RealPlaceData k r Wp Wq) {χ₀ : ℝ → ℝ} (hχ : C6.IsCut0 χ₀) (de : ℝ) (L : Finset (Fin (r + 2)))
    (n : ℕ) : UBL (fun g => ((C6.chiAll D χ₀ de L g : ℝ) : ℂ)) (GV k r) n 0 (2 * r + 2) := by
  have hSG : GV k r ⊆ GV k r := subset_rfl
  have e0 : (fun g => ((C6.chiAll D χ₀ de L g : ℝ) : ℂ)) =
      fun g => ∏ l ∈ L, ((χ₀ (Complex.normSq (Dmin k r D.z D.z' g l) / de) : ℝ) : ℂ) := by
    funext g
    simp [C6.chiAll]
  rw [e0]
  apply ubl_prod hSG L
  intro l _
  obtain ⟨C, hC0, hC⟩ := (ubl_poly (dmin_pd k r D.z D.z' l) (GV k r) hSG n 0).1
  have hns : ContDiff ℝ ∞ (fun y : ℂ => Complex.normSq y) := by
    simp only [Complex.normSq_apply]
    exact (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
      (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)
  refine ubl_fdb (fun g => Dmin k r D.z D.z' g l) (contDiff_of_isPolyDeg (dmin_pd k r D.z D.z' l)) (GV k r) hSG
    Set.univ (fun _ _ => trivial) (2 * r + 2) n C ?_
    (fun y : ℂ => ((χ₀ (Complex.normSq y / de) : ℝ) : ℂ))
    (Complex.ofRealCLM.contDiff.comp (hχ.1.comp (hns.div_const de))) (fun j => ?_)
  · intro w hw hne g hg
    refine (hC w hw g hg).trans ?_
    apply mul_le_mul_of_nonneg_left _ hC0
    apply pow_le_pow_right₀ (gN_ge_one hg)
    have hl : 1 ≤ w.length := by
      cases w with
      | nil => exact absurd rfl hne
      | cons _ _ => simp
    simpa using Nat.le_mul_of_pos_right (2 * r + 2) hl
  · obtain ⟨B, hB⟩ := exists_bound_iteratedFDeriv_cutoff_normSq hχ de j
    exact ⟨B, fun y _ => hB y⟩

end cut

end Formalism.FourierDecayAlt.P.AdmissibleLieWords
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.FirstExpansionIdentity
section
open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants

theorem keyS_inj (k r : ℕ) : Function.Injective (keyS k r) := by
  intro p q hpq
  apply Fin.ext
  have hp := p.isLt
  have hq := q.isLt
  unfold keyS at hpq
  split_ifs at hpq <;> omega

theorem keyS_esI (k r : ℕ) (x : Fin r) : keyS k r (esI k r x) = x.val := by
  have hx := x.isLt
  have c : r + k < 2 * r + k - x.val := by omega
  simp only [keyS, Formalism.QuantumDeterminants.esI, c, if_true]
  omega

theorem star_sgnW (m : ℕ) : star (sgnW m) = sgnW m := by
  simp [sgnW]

theorem neg_one_sq' (s : ℕ) : ((-1 : ℂ) ^ s) * ((-1) ^ s) = 1 := by
  rw [← pow_add, ← two_mul, pow_mul]
  norm_num

theorem zb_col_zero (i0 s' : ℕ) (h : Matrix (Fin i0) (Fin i0) ℂ) (t : ℂ) (a : ℕ) (ha : a < i0 + s') :
    Zb i0 (s' + 1) h t a i0 = 0 := by
  unfold Zb
  split_ifs <;> first | rfl | (exfalso; omega)

private theorem sgnW_succ' (s : ℕ) : sgnW (s + 1) = (-1) ^ s * sgnW s := by
  unfold sgnW
  rw [← pow_add]
  congr 1
  cases s with
  | zero => rfl
  | succ k =>
    have e : (k + 1 + 1) * (k + 1 + 1 - 1) = (k + 1) * (k + 1 - 1) + 2 * (k + 1) := by
      simp only [Nat.add_sub_cancel]
      ring
    rw [e, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]
    ring

theorem first_expansion_identity : ExpansionOmittedColumn := by
  intro A _ _ M _ _ k r z' E La xi i0 s h t u hs hj hR hdet ht hxi
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  have hm : i0 + s' ≤ r := by omega
  rw [AAx_congr k r E xi (show i0 + (s' + 1) - 1 = i0 + s' by omega) _ hm u]
  have hhead : AAx k r E xi i0 (by omega) u =
      h.det • qminor E (xR k r i0 (by omega)) (xR k r i0 (by omega)) u := by
    apply AAx_head
    · intro a p ha hp
      rw [hxi a p (by omega)]
      split_ifs with hp'
      · unfold Zb
        rw [dif_pos ha, dif_neg (by omega)]
      · rfl
    · intro a b
      have ha := a.isLt
      have hb := b.isLt
      rw [hxi _ _ (by simp only [Fin.coe_castLE]; omega)]
      rw [if_pos (by simp only [xR, Formalism.QuantumDeterminants.eI, Fin.coe_castLE]; omega)]
      simp [Zb, xR, Formalism.QuantumDeterminants.eI, ha, hb]
  have he : StrictMono (fun l : Fin (i0 + s') =>
      xR k r (i0 + s' + 1) (by omega) ((⟨i0, by omega⟩ : Fin (i0 + s' + 1)).succAbove l)) := by
    intro a b hab
    have := (Fin.strictMono_succAbove (⟨i0, by omega⟩ : Fin (i0 + s' + 1))) hab
    rw [Fin.lt_def] at this ⊢
    simpa [xR, Formalism.QuantumDeterminants.eI] using this
  have hmain : AAx k r E xi (i0 + s') hm u = (h.det * t ^ s' * sgnW s') •
      qminor E (xR k r (i0 + s') hm)
        (fun l => xR k r (i0 + s' + 1) (by omega) ((⟨i0, by omega⟩ : Fin (i0 + s' + 1)).succAbove l)) u := by
    classical
    have hX : ∀ (a : Fin (i0 + s')) (p : Fin (2 * r + k + 1)),
        p ∉ {p : Fin (2 * r + k + 1) | p.val < i0 + s' + 1 ∧ p.val ≠ i0} → xi (Fin.castLE hm a) p = 0 := by
      intro a p hp
      simp only [Set.mem_setOf_eq, not_and, not_not] at hp
      have ha := a.isLt
      rw [hxi _ p (by simp only [Fin.coe_castLE]; omega)]
      split_ifs with hp1
      · rw [hp (by omega)]
        exact zb_col_zero i0 s' h t _ (by simp only [Fin.coe_castLE]; omega)
      · rfl
    have hu : ∀ c : Fin (i0 + s') → Fin (2 * r + k + 1), StrictMono c →
        (∀ l, c l ∈ {p : Fin (2 * r + k + 1) | p.val < i0 + s' + 1 ∧ p.val ≠ i0}) →
        c = fun l => xR k r (i0 + s' + 1) (by omega) ((⟨i0, by omega⟩ : Fin (i0 + s' + 1)).succAbove l) := by
      intro c hc hS
      apply uniq_mono _ _ he hc
      intro l
      obtain ⟨h1, h2⟩ := hS l
      have hne : (⟨(c l).val, h1⟩ : Fin (i0 + s' + 1)) ≠ ⟨i0, by omega⟩ := fun e => h2 (congrArg Fin.val e)
      obtain ⟨j, hj'⟩ := Fin.exists_succAbove_eq hne
      refine ⟨j, ?_⟩
      apply Fin.ext
      simp only [xR, Formalism.QuantumDeterminants.eI, Fin.coe_castLE, hj']
    have hs := sum_single (M := A) StrictMono (fun a p => xi (Fin.castLE hm a) p)
      {p : Fin (2 * r + k + 1) | p.val < i0 + s' + 1 ∧ p.val ≠ i0} hX _ he hu
      (fun c => qminor E (xR k r (i0 + s') hm) c u)
    have hdet' : (Matrix.of fun a l : Fin (i0 + s') => xi (Fin.castLE hm a)
        (xR k r (i0 + s' + 1) (by omega) ((⟨i0, by omega⟩ : Fin (i0 + s' + 1)).succAbove l))).det =
        h.det * t ^ s' * sgnW s' := by
      have hp := minors_first_case i0 s' h t ⟨i0, by omega⟩
      rw [if_pos rfl] at hp
      rw [← hp]
      congr 1
      ext a l
      have ha := a.isLt
      have hl := ((⟨i0, by omega⟩ : Fin (i0 + s' + 1)).succAbove l).isLt
      simp only [Matrix.of_apply]
      rw [hxi _ _ (by simp only [Fin.coe_castLE]; omega)]
      rw [if_pos (by simp only [xR, Formalism.QuantumDeterminants.eI, Fin.coe_castLE]; omega)]
      simp only [xR, Formalism.QuantumDeterminants.eI, Fin.coe_castLE]
    unfold AAx
    rw [← hdet']
    convert hs using 1
  have hpeel := first_peeling_identity A k r z' E (i0 + s') (by omega) ⟨i0, by omega⟩ u
  have hL := la_congr hR hpeel
  have hsc : (h.det * t ^ (s' + 1) * sgnW (s' + 1))⁻¹ * (h.det * t ^ s' * sgnW s') =
      (-1 : ℂ) ^ (s' + 1 - 1) * t⁻¹ * (h.det⁻¹ * h.det) := by
    rw [sgnW_succ', Nat.add_sub_cancel, scal_E _ _ _ _ s' hdet ht (sgnW_sq s') (neg_one_sq' s')]
  rw [hmain, hhead, map_smul, map_smul, hL, (derivative_leading_zb i0 (s' + 1) h t).2,
    (derivative_leading_zb i0 (s' + 1) h t).1, smul_smul, smul_smul, smul_smul]
  congr 1
  rw [hsc]
  ring

end Formalism.FourierDecayAlt.P.SignAntidiagonal
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.FlagGramRestriction
section
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P

namespace FlagGramRestriction

open C2x5 C2x6 C2x7 HermitianProjections FixedPointsGramVector UnipotentUpperFacts

variable {k r : ℕ}

lemma col_mul (M : B.Mat k r) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) (j : Fin (r + 1) ⊕ Fin (r + 1)) :
    (fun a => (M * gnB k r z z' γ) a j) = M *ᵥ gramVec k r z z' γ j := by
  funext a; simp [gnB, Matrix.mul_apply, Matrix.mulVec, dotProduct]

lemma col_V_mul (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r)
    (Φ : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ) (j : Fin (r + 1) ⊕ Fin (r + 1)) :
    (fun a => (gnB k r z z' γ * Φ) a j) = ∑ i, Φ i j • gramVec k r z z' γ i := by
  funext a; simp [gnB, Matrix.mul_apply, Finset.sum_apply, mul_comm]

lemma mat_ext_col {n : ℕ} {ι : Type*} (A B : Matrix (Fin n) ι ℂ) (h : ∀ j, (fun a => A a j) = fun a => B a j) :
    A = B := by
  ext a j; exact congrFun (h j) a

def PhiH (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ h : B.Mat k r) :
    Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ :=
  Matrix.fromBlocks (C2.uMap k r z h) 0 0 (C2.uMap k r z' (γ⁻¹ * h * γ))

lemma Hst_iff {z z' : Fin (2 * r + k + 1) → ℂ} {γ : B.Mat k r} (hγ : IsUnit γ.det) (h : B.Mat k r) :
    h ∈ C2.Hst k r z z' γ ↔ h ∈ Sset k r z ∧ γ⁻¹ * h * γ ∈ Sset k r z' := by
  constructor
  · rintro ⟨hs, s', hs', rfl⟩
    refine ⟨hs, ?_⟩
    have : γ⁻¹ * (γ * s' * γ⁻¹) * γ = s' := by
      simp only [Matrix.mul_assoc]
      rw [Matrix.nonsing_inv_mul_cancel_left _ _ hγ, Matrix.nonsing_inv_mul _ hγ, Matrix.mul_one]
    rw [this]; exact hs'
  · rintro ⟨hs, hs'⟩
    refine ⟨hs, _, hs', ?_⟩
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv _ hγ, Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_left _ _ hγ]

lemma mulV {z z' : Fin (2 * r + k + 1) → ℂ} (hstd : C2.Std k r z z') {γ : B.Mat k r} (hγ : IsUnit γ.det)
    {h : B.Mat k r} (hs : h ∈ Sset k r z) (hs' : γ⁻¹ * h * γ ∈ Sset k r z') :
    h * gnB k r z z' γ = gnB k r z z' γ * PhiH k r z z' γ h := by
  have hU := (unipotent_map_frame k r z hstd.2.1).1 h hs
  have hU' := (unipotent_map_frame k r z' hstd.2.2).1 _ hs'
  apply mat_ext_col
  intro j
  rw [col_mul, col_V_mul, Fintype.sum_sum_type]
  cases j with
  | inl b =>
    simp only [PhiH, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, zero_smul,
      Finset.sum_const_zero, add_zero]
    exact hU.1 b
  | inr b =>
    simp only [PhiH, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_smul,
      Finset.sum_const_zero, zero_add]
    show h *ᵥ (γ *ᵥ fvec k r z' b) = ∑ c, C2.uMap k r z' (γ⁻¹ * h * γ) c b • (γ *ᵥ fvec k r z' c)
    have e : h * γ = γ * (γ⁻¹ * h * γ) := by
      simp only [Matrix.mul_assoc]; rw [Matrix.mul_nonsing_inv_cancel_left _ _ hγ]
    rw [Matrix.mulVec_mulVec, e, ← Matrix.mulVec_mulVec, hU'.1 b, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul]

lemma Phi_unit {z z' : Fin (2 * r + k + 1) → ℂ} (hstd : C2.Std k r z z') {γ h : B.Mat k r}
    (hs : h ∈ Sset k r z) (hs' : γ⁻¹ * h * γ ∈ Sset k r z') : IsUnit (PhiH k r z z' γ h).det := by
  have hU := (unipotent_map_frame k r z hstd.2.1).1 h hs
  have hU' := (unipotent_map_frame k r z' hstd.2.2).1 _ hs'
  unfold PhiH
  rw [Matrix.det_fromBlocks_zero₂₁]
  exact (C2x2.ut_unit hU.2.1).mul (C2x2.ut_unit hU'.2.1)

lemma Phi_gram {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι] (H : Matrix n n ℂ)
    (V : Matrix n ι ℂ) (g : Matrix n n ℂ) (Φ : Matrix ι ι ℂ) (hg : gᴴ * H * g = H) (hgV : g * V = V * Φ) :
    Φᴴ * (Vᴴ * H * V) * Φ = Vᴴ * H * V := by
  calc Φᴴ * (Vᴴ * H * V) * Φ = (V * Φ)ᴴ * H * (V * Φ) := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = (g * V)ᴴ * H * (g * V) := by rw [hgV]
    _ = Vᴴ * (gᴴ * H * g) * V := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Vᴴ * H * V := by rw [hg]

lemma KU_V {z z' : Fin (2 * r + k + 1) → ℂ} {γ κ : B.Mat k r} (hκ : κ ∈ C2.KU k r z z' γ) :
    κ * gnB k r z z' γ = gnB k r z z' γ := by
  apply mat_ext_col; intro j
  rw [col_mul, hκ.2 j]
  funext a; simp [gnB]

lemma flag_mem (z : Fin (2 * r + k + 1) → ℂ) (u : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (hu : u ∈ C2.UTset (r + 1))
    (b : Fin (r + 1)) : (∑ c, u c b • fvec k r z c) - fvec k r z b ∈ C2.flagSpan k r z b := by
  have e : (∑ c, u c b • fvec k r z c) - fvec k r z b =
      ∑ c, (u c b - if c = b then 1 else 0) • fvec k r z c := by
    simp only [sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  rw [e]
  apply Submodule.sum_mem
  intro c _
  by_cases hcb : c < b
  · apply Submodule.smul_mem
    apply Submodule.subset_span
    exact ⟨⟨c, hcb⟩, rfl⟩
  · have h0 : u c b - (if c = b then 1 else 0) = 0 := by
      rcases lt_or_eq_of_le (not_lt.mp hcb) with h | h
      · rw [hu.1 c b h, if_neg (ne_of_gt h), sub_self]
      · subst h; rw [hu.2, if_pos rfl, sub_self]
    rw [h0, zero_smul]; exact Submodule.zero_mem _

lemma cancel_left {m : Type*} [Fintype m] [DecidableEq m] (A X Y : Matrix m m ℂ) (hA : IsUnit A.det)
    (h : A * X = A * Y) : X = Y := by
  calc X = A⁻¹ * (A * X) := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hA, Matrix.one_mul]
    _ = A⁻¹ * (A * Y) := by rw [h]
    _ = Y := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hA, Matrix.one_mul]

lemma cancel_right {m : Type*} [Fintype m] [DecidableEq m] (A X Y : Matrix m m ℂ) (hA : IsUnit A.det)
    (h : X * A = Y * A) : X = Y := by
  calc X = X * A * A⁻¹ := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hA, Matrix.mul_one]
    _ = Y * A * A⁻¹ := by rw [h]
    _ = Y := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hA, Matrix.mul_one]

lemma Rst_rho {z z' : Fin (2 * r + k + 1) → ℂ} (hstd : C2.Std k r z z') {γ : B.Mat k r}
    (hpos : C2.PosPt k r z z' γ) {ρ : B.Mat k r} (hρ : ρ ∈ C2.Rst k r z z' γ) :
    ρ = rhoOf (Hpk k r) (gnB k r z z' γ) (PhiH k r z z' γ ρ) := by
  have hγ : IsUnit γ.det := WeylGroupFacts.isUnit_of_uh hpos.1
  obtain ⟨hs, hs'⟩ := (Hst_iff hγ ρ).mp hρ.1
  apply eq_rhoOf _ _ _ (gram_det z z' γ hstd hpos) ρ (mulV hstd hγ hs hs')
  intro x hx
  exact hρ.2 x ((mem_Uperp z z' γ x).mpr hx)

lemma Rst_unip {z z' : Fin (2 * r + k + 1) → ℂ} (hstd : C2.Std k r z z') {γ : B.Mat k r}
    (hpos : C2.PosPt k r z z' γ) {ρ : B.Mat k r} (hρ : ρ ∈ C2.Rst k r z z' γ) :
    (ρ - 1) ^ (2 * r + k + 1) = 0 := by
  have hγ : IsUnit γ.det := WeylGroupFacts.isUnit_of_uh hpos.1
  obtain ⟨hs, hs'⟩ := (Hst_iff hγ ρ).mp hρ.1
  have hU := (unipotent_map_frame k r z hstd.2.1).1 ρ hs
  have hU' := (unipotent_map_frame k r z' hstd.2.2).1 _ hs'
  have e := Rst_rho hstd hpos hρ
  have hΦ : (PhiH k r z z' γ ρ - 1) ^ (r + 1) = 0 := by
    unfold PhiH
    have e1 : Matrix.fromBlocks (C2.uMap k r z ρ) 0 0 (C2.uMap k r z' (γ⁻¹ * ρ * γ)) - 1 =
        Matrix.fromBlocks (C2.uMap k r z ρ - 1) 0 0 (C2.uMap k r z' (γ⁻¹ * ρ * γ) - 1) := by
      rw [← Matrix.fromBlocks_one]
      ext (i | i) (j | j) <;> simp [Matrix.one_apply]
    rw [e1, blk_pow, ut_sub_pow hU.2.1, ut_sub_pow hU'.2.1, Matrix.fromBlocks_zero]
  rw [e, rhoOf_sub_one_pow _ _ _ (gram_det z z' γ hstd hpos),
    HermitianProjections.pow_eq_zero_of_le hΦ (by omega), Matrix.mul_zero, Matrix.zero_mul]

end FlagGramRestriction

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SectionDecomposition
section
namespace Formalism.FourierDecayAlt.P

theorem c2_section_decomp : Formalism.FourierDecayAlt.C2.SectionDecomp :=
  c2_section_decomp_of_pieces stabilizer_split stabilizer_pairs unipotent_radical_image upper_splitting standard_flag_property
    unipotent_map_frame zhat_equivalence c2_tau_mem

end Formalism.FourierDecayAlt.P
end

