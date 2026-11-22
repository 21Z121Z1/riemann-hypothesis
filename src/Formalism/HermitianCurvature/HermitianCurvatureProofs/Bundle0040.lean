import Formalism.HermitianCurvature.LetterProductDoubleDegreeCount
import Formalism.HermitianCurvature.StatementJF
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0001
import Formalism.HermitianCurvature.CompositeFormulaLevelZero
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0002

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.RhoAntitoneOfInterlacing
section
open Formalism.FourierDecayAlt Finset

namespace Formalism.FourierDecayAlt.P

theorem lambda_side_inequality : C7.LamSide := by
  unfold C7.LamSide C7.LamInterlaces
  rintro k r u u' lam l Y hl hlk ⟨hA, hL⟩ ⟨-, hL'⟩ - i
  constructor
  · intro hli
    obtain ⟨j, hj⟩ : ∃ j : Fin (k + 2 * r + 1), (j : ℕ) = l - 1 := ⟨⟨l - 1, by omega⟩, rfl⟩
    have hji : j ≤ i := Fin.le_iff_val_le_val.2 (by omega)
    have hi1 : lam i ≤ lam j := hA.antitone hji
    have h1 := (hL j).1 (by omega)
    have h2 := (hL' j).1 (by omega)
    rw [show (j : ℕ) + 1 = l by omega] at h1 h2
    exact lt_min (lt_of_le_of_lt hi1 h1) (lt_of_le_of_lt hi1 h2)
  · intro hil
    obtain ⟨j, hj⟩ : ∃ j : Fin (k + 2 * r + 1), (j : ℕ) = l - 2 := ⟨⟨l - 2, by omega⟩, rfl⟩
    have hij : i ≤ j := Fin.le_iff_val_le_val.2 (by omega)
    have hi1 : lam j ≤ lam i := hA.antitone hij
    have h1 := (hL j).2 (by omega)
    have h2 := (hL' j).2 (by omega)
    rw [show (j : ℕ) + 2 = l by omega] at h1 h2
    exact max_lt (lt_of_lt_of_le h1 hi1) (lt_of_lt_of_le h2 hi1)

theorem rho_antitone_of_interlacing {k : ℕ} {u u' ρ : ℕ → ℝ} (h : I.Interlaces k u u' ρ) :
    ∀ i j, 1 ≤ i → i ≤ j → j ≤ k - 1 → ρ j ≤ ρ i := by
  intro i j hi hij hj
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ n hin ih =>
    have h1 := h n (by simp only [Finset.mem_Icc, Set.mem_Icc]; omega)
    have h2 := h (n + 1) (by simp only [Finset.mem_Icc, Set.mem_Icc]; omega)
    have h3 := ih (by omega)
    linarith [h1.2.2.1, h2.1]

theorem rho_side_inequality : C7.RhoSide := by
  unfold C7.RhoSide C7.Between
  intro k u u' ρ l Y hl hlk hI hB i hi
  have hi' : 1 ≤ i ∧ i ≤ k - 1 := by simpa using hi
  obtain ⟨hB1, hB2⟩ := hB
  constructor
  · intro hli
    have h1 := hI l (by simp only [Finset.mem_Icc, Set.mem_Icc]; omega)
    have h2 := rho_antitone_of_interlacing hI l i hl hli hi'.2
    have h3 : ρ l + 1 / 2 ≤ min (u l) (u' l) := le_min h1.1 h1.2.1
    linarith
  · intro hil
    have h1 := hI (l - 1) (by simp only [Finset.mem_Icc, Set.mem_Icc]; omega)
    have h2 := rho_antitone_of_interlacing hI i (l - 1) hi'.1 (by omega) (by omega)
    rw [show l - 1 + 1 = l by omega] at h1
    have h3 : max (u l) (u' l) + 1 / 2 ≤ ρ (l - 1) := by
      rcases le_total (u l) (u' l) with h | h
      · rw [max_eq_right h]; exact h1.2.2.2
      · rw [max_eq_left h]; exact h1.2.2.1
    linarith

theorem sign_change_count : C7.SignCount := by
  unfold C7.SignCount
  intro ι _ f S hS hne
  classical
  rw [← Finset.prod_mul_prod_compl S f, ← mul_assoc]
  have h1 : (-1 : ℝ) ^ S.card * ∏ i ∈ S, f i = ∏ i ∈ S, (-f i) := by
    rw [Finset.prod_neg]
  rw [h1]
  apply mul_pos
  · exact Finset.prod_pos fun i hi => by linarith [(hS i).1 hi]
  · refine Finset.prod_pos fun i hi => ?_
    have h2 : ¬ f i < 0 := fun h => (Finset.mem_compl.1 hi) ((hS i).2 h)
    exact lt_of_le_of_ne (not_lt.1 h2) (hne i).symm

theorem sign_prod_of_split_at_index (s : Finset ℕ) (g : ℕ → ℝ) (m : ℕ) (hpos : ∀ j ∈ s, j < m → 0 < g j)
    (hneg : ∀ j ∈ s, m ≤ j → g j < 0) : 0 < (-1 : ℝ) ^ (s.filter (m ≤ ·)).card * ∏ j ∈ s, g j := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have ih' := ih (fun j hj => hpos j (Finset.mem_insert_of_mem hj))
      (fun j hj => hneg j (Finset.mem_insert_of_mem hj))
    rw [Finset.prod_insert ha, Finset.filter_insert]
    by_cases hma : m ≤ a
    · rw [if_pos hma, Finset.card_insert_of_notMem (fun h => ha (Finset.mem_filter.1 h).1), pow_succ]
      have := hneg a (Finset.mem_insert_self a s) hma
      nlinarith
    · rw [if_neg hma]
      have := hpos a (Finset.mem_insert_self a s) (by omega)
      nlinarith

theorem polynomial_sign : C7.PSign := by
  unfold C7.PSign
  intro k r u u' ρ lam l Y hl hlk hL hL' hI hB
  have hside := lambda_side_inequality k r u u' lam l Y hl hlk hL hL' hB
  have hrho := rho_side_inequality k u u' ρ l Y hl hlk hI hB
  have hB' := hB
  unfold C7.Between at hB'
  have hA : 0 < (-1 : ℝ) ^ (k - l) * ∏ s, (Y + lam s) := by
    have hprod : ∏ s, (Y + lam s) = ∏ j ∈ Finset.range (k + 2 * r + 1),
        (fun j => if h : j < k + 2 * r + 1 then Y + lam ⟨j, h⟩ else 1) j := by
      rw [← Fin.prod_univ_eq_prod_range]
      refine Finset.prod_congr rfl fun s _ => ?_
      simp only [dif_pos s.isLt, Fin.eta]
    have key := sign_prod_of_split_at_index (Finset.range (k + 2 * r + 1))
      (fun j => if h : j < k + 2 * r + 1 then Y + lam ⟨j, h⟩ else 1) (l - 1)
      (fun j hj hjm => by
        have hj' : j < k + 2 * r + 1 := Finset.mem_range.1 hj
        simp only [dif_pos hj']
        have := (hside ⟨j, hj'⟩).2 (show j + 1 < l by omega)
        linarith [hB'.2])
      (fun j hj hjm => by
        have hj' : j < k + 2 * r + 1 := Finset.mem_range.1 hj
        simp only [dif_pos hj']
        have := (hside ⟨j, hj'⟩).1 (show l ≤ j + 1 by omega)
        linarith [hB'.1])
    have hcard : ((Finset.range (k + 2 * r + 1)).filter (l - 1 ≤ ·)).card = (k - l) + 2 * (r + 1) := by
      rw [(show (Finset.range (k + 2 * r + 1)).filter (l - 1 ≤ ·) = Finset.Ico (l - 1) (k + 2 * r + 1) by
        ext j; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega), Nat.card_Ico]
      omega
    rw [hcard, pow_add, pow_mul, neg_one_sq, one_pow, mul_one] at key
    rw [hprod]
    exact key
  have hB2 : 0 < (-1 : ℝ) ^ (k - l) * I.xpoly k ρ Y := by
    unfold I.xpoly
    have key := sign_prod_of_split_at_index (Finset.Icc 1 (k - 1)) (fun i => Y + ρ i) l
      (fun i hi hil => show 0 < Y + ρ i by linarith [(hrho i hi).2 hil])
      (fun i hi hli => show Y + ρ i < 0 by linarith [(hrho i hi).1 hli])
    have hcard : ((Finset.Icc 1 (k - 1)).filter (l ≤ ·)).card = k - l := by
      rw [(show (Finset.Icc 1 (k - 1)).filter (l ≤ ·) = Finset.Icc l (k - 1) by
        ext j; simp only [Finset.mem_filter, Finset.mem_Icc]; omega), Nat.card_Icc]
      omega
    rw [hcard] at key
    exact key
  refine ⟨hA, hB2, ?_⟩
  have h := abs_of_pos hA
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] at h
  exact h

theorem polynomial_sign_of_parts : C7.PSignOfParts := fun _ _ _ => polynomial_sign

theorem roots_outside_jointly : C7.RootsOutJoint := by
  unfold C7.RootsOutJoint LE.Sys.RootsOut
  intro S u u' l hl hlk hI hI' hB s hs
  have hb := hB _ hs
  have key := lambda_side_inequality S.k S.r u u' S.lam l (-S.lam s) hl hlk hI hI' hb s
  unfold C7.Between at hb
  rw [neg_neg] at hb
  by_cases h : l ≤ s.val + 1
  · have := key.1 h
    linarith [hb.1]
  · have := key.2 (by omega)
    linarith [hb.2]

theorem roots_outside_of_parts : C7.RootsOutOfParts := fun _ => roots_outside_jointly

theorem interlacing_of_parts : C7.LemmaEInterlacingOfParts := by
  unfold C7.LemmaEInterlacingOfParts C7.LemmaEInterlacing LE.LemmaE
  intro hE hR CR Cd CP h1 h2 h3 C₂ hC₂ C₆ hC₆ S u u' l hl hlk hI hI' hB hN hL hβ
  exact hE CR Cd CP h1 h2 h3 C₂ hC₂ C₆ hC₆ S hN hL hβ (hR S u u' l hl hlk hI hI' hB)

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SandwichRhoAction
section
open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.SandwichRhoAction

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

lemma deriv_comp_of_leftInv {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (L : E →L[ℝ] F) (M : F →L[ℝ] E) (hML : ∀ x, M (L x) = x) (φ : ℝ → E) (t : ℝ) :
    deriv (fun s => L (φ s)) t = L (deriv φ t) := by
  by_cases h : DifferentiableAt ℝ φ t
  · exact (L.hasFDerivAt.comp_hasDerivAt t h.hasDerivAt).deriv
  · have h' : ¬ DifferentiableAt ℝ (fun s => L (φ s)) t := by
      intro hd
      apply h
      have hφ : (fun s => M (L (φ s))) = φ := funext fun s => hML (φ s)
      rw [← hφ]
      exact M.differentiableAt.comp t hd
    rw [deriv_zero_of_not_differentiableAt h, deriv_zero_of_not_differentiableAt h', map_zero]

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def sandw (P : Wp →L[ℂ] Wp) (Q : Wq →L[ℂ] Wq) : (Wq →L[ℂ] Wp) →L[ℝ] (Wq →L[ℂ] Wp) :=
  (((ContinuousLinearMap.compL ℂ Wq Wp Wp P).comp ((ContinuousLinearMap.compL ℂ Wq Wq Wp).flip Q)).restrictScalars ℝ)

lemma sandw_apply (P : Wp →L[ℂ] Wp) (Q : Wq →L[ℂ] Wq) (A : Wq →L[ℂ] Wp) : sandw P Q A = P.comp (A.comp Q) := rfl

lemma rho_eq (D : RealPlaceData k r Wp Wq) (p : SS k r) (φ : Mat k r → (Wq →L[ℂ] Wp)) (x : Mat k r) :
    rho D p φ x = sandw (D.π (Matrix.of p.1.1)) (D.π' (Matrix.of p.2.1)⁻¹) (φ (sgs p x)) := rfl

lemma sandw_leftInv (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) (A : Wq →L[ℂ] Wp) :
    sandw (D.π (Matrix.of p.1.1)⁻¹) (D.π' (Matrix.of p.2.1))
      (sandw (D.π (Matrix.of p.1.1)) (D.π' (Matrix.of p.2.1)⁻¹) A) = A := by
  have h1 := hp.1
  have h3 := hp.2.2.1
  have u1 := WeylGroupFacts.isUnit_of_uh h1.1
  have u3 := WeylGroupFacts.isUnit_of_uh h3.1
  have e1 : (D.π (Matrix.of p.1.1)⁻¹).comp (D.π (Matrix.of p.1.1)) = 1 := by
    rw [← D.π_rep.2 _ (WeylGroupFacts.uw_inv h1) _ h1, Matrix.nonsing_inv_mul _ u1, D.π_rep.1]
  have e3 : (D.π' (Matrix.of p.2.1)⁻¹).comp (D.π' (Matrix.of p.2.1)) = 1 := by
    rw [← D.π'_rep.2 _ (WeylGroupFacts.uw_inv h3) _ h3, Matrix.nonsing_inv_mul _ u3, D.π'_rep.1]
  have re : ∀ (P1 P2 : Wp →L[ℂ] Wp) (Q1 Q2 : Wq →L[ℂ] Wq) (B : Wq →L[ℂ] Wp),
      P1.comp ((P2.comp (B.comp Q2)).comp Q1) = (P1.comp P2).comp (B.comp (Q2.comp Q1)) := by
    intros; ext; rfl
  simp only [sandw_apply]
  rw [re, e1, e3]
  ext; rfl

lemma sgs_eq' (p : SS k r) (x : Mat k r) : sgs p x = (sL p)⁻¹ * x * sR p := by
  unfold sgs sL sR
  rw [Matrix.mul_inv_rev]
  simp only [Matrix.mul_assoc]

lemma isUnit_sL (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) : IsUnit (sL p).det :=
  WeylGroupFacts.isUnit_of_uh (WeylGroupFacts.uh_mul hp.2.1.1 hp.1.1)

lemma isUnit_sR (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) : IsUnit (sR p).det :=
  WeylGroupFacts.isUnit_of_uh (WeylGroupFacts.uh_mul hp.2.2.2.1 hp.2.2.1.1)

lemma sgs_curveR (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) (X g : Mat k r) (t : ℝ) :
    sgs p (g * NormedSpace.exp ((t : ℂ) • X)) = sgs p g * NormedSpace.exp ((t : ℂ) • AdR p X) := by
  have hu : IsUnit (sR p) := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_sR D hp)
  rw [sgs_eq', sgs_eq']
  unfold AdR
  have hc : ((t : ℂ) • ((sR p)⁻¹ * X * sR p)) = (sR p)⁻¹ * ((t : ℂ) • X) * sR p := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [hc]
  first
    | rw [Matrix.exp_conj' _ _ hu]
    | rw [Matrix.exp_conj' ℂ _ _ hu]
  simp only [Matrix.mul_assoc]
  rw [Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_sR D hp)]

lemma sgs_curveL (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) (X g : Mat k r) (t : ℝ) :
    sgs p (NormedSpace.exp (-((t : ℂ) • X)) * g) = NormedSpace.exp (-((t : ℂ) • AdL p X)) * sgs p g := by
  have hu : IsUnit (sL p) := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_sL D hp)
  rw [sgs_eq', sgs_eq']
  unfold AdL
  have hc : -((t : ℂ) • ((sL p)⁻¹ * X * sL p)) = (sL p)⁻¹ * (-((t : ℂ) • X)) * sL p := by
    rw [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [hc]
  first
    | rw [Matrix.exp_conj' _ _ hu]
    | rw [Matrix.exp_conj' ℂ _ _ hu]
  simp only [Matrix.mul_assoc]
  rw [Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_sL D hp)]

lemma rdV_rho (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) (X : Mat k r) (φ : Mat k r → (Wq →L[ℂ] Wp))
    (g : Mat k r) : RdV X (rho D p φ) g = rho D p (RdV (AdR p X) φ) g := by
  unfold RdV
  simp only [rho_eq, sgs_curveR D hp]
  exact deriv_comp_of_leftInv _ _ (sandw_leftInv D hp) _ 0

lemma ldV_rho (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) (X : Mat k r) (φ : Mat k r → (Wq →L[ℂ] Wp))
    (g : Mat k r) : LdV X (rho D p φ) g = rho D p (LdV (AdL p X) φ) g := by
  unfold LdV
  simp only [rho_eq, sgs_curveL D hp]
  exact deriv_comp_of_leftInv _ _ (sandw_leftInv D hp) _ 0

lemma rw_rho (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) :
    ∀ (v : List (Mat k r)) (φ : Mat k r → (Wq →L[ℂ] Wp)), Rw v (rho D p φ) = rho D p (Rw (v.map (AdR p)) φ)
  | [], _ => rfl
  | X :: v, φ => by
    funext g
    show RdV X (Rw v (rho D p φ)) g = rho D p (RdV (AdR p X) (Rw (v.map (AdR p)) φ)) g
    rw [rw_rho D hp v φ, rdV_rho D hp]

lemma lw_rho (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) :
    ∀ (u : List (Mat k r)) (φ : Mat k r → (Wq →L[ℂ] Wp)),
      u.foldr LdV (rho D p φ) = rho D p ((u.map (AdL p)).foldr LdV φ)
  | [], _ => rfl
  | X :: u, φ => by
    funext g
    show LdV X (u.foldr LdV (rho D p φ)) g = rho D p (LdV (AdL p X) ((u.map (AdL p)).foldr LdV φ)) g
    rw [lw_rho D hp u φ, ldV_rho D hp]

theorem dLR_rho (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) (u v : List (Mat k r))
    (f : Mat k r → (Wq →L[ℂ] Wp)) : dLR u v (rho D p f) = rho D p (dLR (u.map (AdL p)) (v.map (AdR p)) f) := by
  show u.foldr LdV (Rw v (rho D p f)) = rho D p ((u.map (AdL p)).foldr LdV (Rw (v.map (AdR p)) f))
  rw [rw_rho D hp v f, lw_rho D hp u]

theorem _root_.Formalism.FourierDecayAlt.P.rewrite_rho_action : RwRho := by
  intro k r Wp Wq _ _ _ _ D m f p hp _ u v _ _ _ g _
  exact congrFun (dLR_rho D hp u v f) g

end Formalism.FourierDecayAlt.P.SandwichRhoAction
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothBoundedOfFourierDecay
section
open MeasureTheory Real Complex
open scoped FourierTransform ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerC.Fou

theorem integral_fsv_eq_fourier (D : ℂ → ℂ) (s : ℂ) :
    ∫ t, Formalism.FourierDecayAlt.P5.fsv s t * D t = 𝓕 D (-(I * conj s) / (π : ℂ)) := by
  rw [Real.fourier_eq]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
  congr 1
  unfold Formalism.FourierDecayAlt.P5.fsv
  congr 1
  rw [Complex.inner]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have e1 : s * t - conj s * conj t = ((2 * (s * t).im : ℝ) : ℂ) * I := by
    rw [← map_mul, Complex.sub_conj]
  rw [e1]
  congr 1
  push_cast
  have e2 : (-(I * conj s) / (π : ℂ) * conj t).re = -((s * t).im) / π := by
    rw [div_mul_eq_mul_div, Complex.div_ofReal_re]
    simp [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  rw [e2]
  push_cast
  field_simp

theorem smooth_bounded_of_fourier_decay (D : ℂ → ℂ) (m : ℕ) (C : ℝ) (hD : Integrable D)
    (hdec : ∀ s, ‖∫ t, Formalism.FourierDecayAlt.P5.fsv s t * D t‖ ≤ C * (1 + ‖s‖) ^ (-((m : ℝ) + 3))) :
    ∃ D' : ℂ → ℂ, ContDiff ℝ m D' ∧ (∀ j ≤ m, ∃ B, ∀ t, ‖iteratedFDeriv ℝ j D' t‖ ≤ B) ∧
      ∀ t, ContinuousAt D t → D' t = D t := by
  refine fourier_smooth D m C hD fun w => ?_
  rw [Complex.finrank_real_complex]
  set s : ℂ := -(I * π * conj w) with hs
  have hw : w = -(I * conj s) / (π : ℂ) := by
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    rw [hs]
    simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_conj]
    field_simp
    ring_nf
    simp [Complex.I_sq]
  have hns : ‖s‖ = π * ‖w‖ := by
    rw [hs, norm_neg, norm_mul, norm_mul, Complex.norm_I, Complex.norm_conj, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos, one_mul]
  have h := hdec s
  rw [integral_fsv_eq_fourier, ← hw] at h
  refine h.trans ?_
  have hC : 0 ≤ C := by
    have h0 := (norm_nonneg _).trans (hdec 0)
    exact nonneg_of_mul_nonneg_left h0 (by positivity)
  have e : (-((m : ℝ) + ((2 : ℕ) : ℝ) + 1)) = -((m : ℝ) + 3) := by push_cast; ring
  rw [e]
  refine mul_le_mul_of_nonneg_left ?_ hC
  refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
  rw [hns]
  nlinarith [Real.pi_gt_three, norm_nonneg w]

end Formalism.FourierDecayAlt.P5.HerC.Fou
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ThresholdExponentEstimate
section
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P

theorem weight_determinant : C7.DetW := by
  intro s
  induction s with
  | zero => simp [G.wMat]
  | succ n ih =>
    rw [(det_weyl_matrix n).1, ih, ← pow_add]
    congr 1
    rcases n with _ | m
    · simp
    · have e : (m + 1 + 1) * (m + 1 + 1 - 1) = (m + 1) * (m + 1 - 1) + 2 * (m + 1) := by
        simp only [Nat.add_sub_cancel]; ring
      rw [e, Nat.add_mul_div_left _ _ (by norm_num)]
      ring

theorem equal_roots_determinant : C7.DEqualRoots := by
  intro s D'' c t z hs hz
  obtain ⟨m, rfl⟩ : ∃ m, s = m + 1 := ⟨s - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hz
  have e : (G.wMat (m + 1 - 1)).det = (G.wMat m).det := rfl
  rw [e, (det_weyl_matrix m).1, hz, Nat.add_sub_cancel]
  have h1 : ((-1 : ℂ)) ^ m * (-1) ^ (m + 1 + 1) = 1 := by
    rw [← pow_add]; exact Even.neg_one_pow ⟨m + 1, by ring⟩
  linear_combination (-(D'' * (G.wMat m).det * c * t ^ m)) * h1

theorem equal_roots_of_parts : C7.DEqualOfParts := fun _ => equal_roots_determinant

theorem nprime_le_bound : C7.NprimeLe := by
  intro N h; unfold C7.Nprime; omega

theorem threshold_exponent_estimate : C7.ThresholdE := by
  intro k r N AP hk hN hAP
  have h : 126 * (r + 1) ^ 3 * (C7.Nprime N * C7.nOf k r ^ 2 + C7.nOf k r ^ 3) +
      C7.B0 r * C7.mmP r (C7.Nprime N) (C7.nOf k r) + 12 * (r + 1) * C7.Nprime N * C7.nOf k r ≤
      915 * (r + 1) ^ 3 * (N * C7.nOf k r ^ 2 + C7.nOf k r ^ 3) := by
    obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hN
    obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hk
    unfold C7.Nprime C7.nOf C7.B0 C7.mmP
    refine le_trans (Nat.le_add_right _ (537*a*b^2*r^3 + 1611*a*b^2*r^2 + 1611*a*b^2*r + 537*a*b^2 + 2148*a*b*r^4 + 8592*a*b*r^3 + 12861*a*b*r^2 + 8502*a*b*r + 2085*a*b + 2148*a*r^5 + 10740*a*r^4 + 21426*a*r^3 + 21246*a*r^2 + 10434*a*r + 2022*a + 789*b^3*r^3 + 2367*b^3*r^2 + 2367*b^3*r + 789*b^3 + 5271*b^2*r^4 + 20706*b^2*r^3 + 30492*b^2*r^2 + 19950*b^2*r + 4893*b^2 + 11616*b*r^5 + 56568*b*r^4 + 110085*b*r^3 + 106926*b*r^2 + 51753*b*r + 9960*b + 8460*r^6 + 49248*r^5 + 119286*r^4 + 153702*r^3 + 110898*r^2 + 42339*r + 6645)) (le_of_eq ?_)
    ring
  have hR := (Nat.cast_le (α := ℝ)).2 h
  push_cast at hR
  linarith

theorem budget_sum_estimate : C7.BudgetSum := by
  intro r N' n d D h1 h2; unfold C7.B0; nlinarith

theorem c7_letter_product_degree_count : C7.LetterProductDegreeCount := by
  intro k r N d D hk h1 h2; unfold C7.Dstar C7.Nprime C7.nOf at *
  constructor <;> nlinarith

theorem degree_count_identity : C7.DegreeCount := by
  intro k r N M dl Dl hk hN hM h1 h2; unfold C7.Nprime C7.nOf at *
  have a2 : 1 ≤ (r + 1) * (k + 2 * r + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have a3 := Nat.mul_le_mul_left (6 * (3 * (N + 1))) a2
  have b1 : Dl ≤ (r + 1) * (k + 2 * r + 1) + 2 * (r + 1) := by nlinarith
  have b2 : 2 * M * Dl ≤ 2 * (3 * (N + 1)) * ((r + 1) * (k + 2 * r + 1) + 2 * (r + 1)) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 2 hM) b1
  have b3 : 2 * (3 * (N + 1)) * ((r + 1) * (k + 2 * r + 1) + 2 * (r + 1)) ≤
      6 * (r + 1) * (3 * (N + 1)) * (k + 2 * r + 1) := by
    have hP : (r + 1) * (N + 1) * 1 ≤ (r + 1) * (N + 1) * (k + 2 * r + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    nlinarith [hP]
  refine ⟨Nat.mul_le_mul (Nat.mul_le_mul_left 2 hM) h1, b2.trans b3, by nlinarith, by nlinarith, by nlinarith⟩

theorem eigenvalue_shift : C7.EigenShift := by
  intro k r Y a i; unfold Formalism.FourierDecayAlt.Q.uC C7.lamOf C7.nOf Formalism.FourierDecayAlt.Q.mdim; simp; ring

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.TopIdentFromParts
section
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd

theorem ofWordRR : OfWordRR := by
  intro A S _ _ _ _ _ r L st w
  induction w with
  | nil =>
    exact ⟨by simp [Fr.ofWord, RRw, Fr.Start.frame], fun Y => by simp [Fr.ofWord, TTw, Fr.Start.frame]⟩
  | cons l w ih =>
    obtain ⟨ih1, ih2⟩ := ih
    cases hl : l.plus
    · exact ⟨by simp [Fr.ofWord, RRw, hl, Fr.FrameData.minus, ih1, ih2],
        fun Y => by simp [Fr.ofWord, TTw, hl, Fr.FrameData.minus, ih2]⟩
    · exact ⟨by simp [Fr.ofWord, RRw, hl, Fr.FrameData.plus, ih1, ih2],
        fun Y => by simp [Fr.ofWord, TTw, hl, Fr.FrameData.plus, ih2]⟩

section

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem tprod_ge (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (Y : ℂ) (i : ℕ) (h : r ≤ i) :
    tprod L Y i = 1 := by
  rw [tprod, dif_neg (by omega)]

theorem QQi_last (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (st : Fr.Start (Pr (RadSp k r z z' π π')))
    (Y : ℂ) : QQi L st (Fin.last r) Y = st.QQ Y := by
  rw [QQi, Fin.val_last, tprod_ge L (star Y) r le_rfl, tprod_ge L Y r le_rfl, Matrix.conjTranspose_one,
    one_mul, mul_one]

end

theorem topIdentFromParts {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π')))
    (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')) (l0 : ℕ) :
    TopIdentFromParts (S := S) P z z' π π' X μ L st K l0 := by
  intro hD hFA hOW hAdj w hw x y hx hy c hc
  obtain ⟨hint, heq⟩ := hAdj w hw x y hx hy c hc
  refine ⟨hint, ?_⟩
  have hQ : QQi L st (Fin.last P.r) = st.QQ := funext fun Y => QQi_last L st Y
  have hfr := hFA (Pr (RadSp P.k P.r z z' π π')) S P.r L st w hD.2.2.2.2.2.2.1 hD.2.2.2.2.2.2.2 hw.1
  have hRR : RRi L st (Fin.last P.r) w =
      star (Fr.ofWord L st w).F * (Fr.ofWord L st w).d L * (Fr.ofWord L st w).F := by
    rw [RRi, hQ, ← (hOW _ S P.r L st w).1, hfr.form]
  rw [RRform, hRR, heq]

end Formalism.FourierDecayAlt.P5
end
end

