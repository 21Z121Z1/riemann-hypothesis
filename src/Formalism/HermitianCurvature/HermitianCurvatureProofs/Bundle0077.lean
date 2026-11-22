import Formalism.HermitianCurvature.HermitianCurvatureProofs.QuantumMinorExpansion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0067
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AlgebraicQuantumDeterminant
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OperatorRepresentations
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliCoordinates
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftDerivativeCurves
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0069
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0058
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameEntries
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ZinvBound
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0037
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.Bundle0003
import Formalism.HermitianCurvature.StatementTL
import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSettingBis
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0071
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0043
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0052
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliAbstractCharacter
import Formalism.HermitianCurvature.HermitianCurvatureProofs.StarSumLemmas
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BorderedDeterminants
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BranchingSystems
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ClosureOperators
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0068
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0055
import Formalism.HermitianCurvature.OperatorsCommuteTranslations
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0033
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0030

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.DeterminantGeneric
section
namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

theorem algebraic_quantum_determinant : Qr.AlgDet :=
  qr_algDet_of (qr_algDetBasis_of quantum_jacobi_identity quantum_determinant_vector quantum_minor_covariance)

theorem capelli_hat_frame : Qr.ChatFrame := qr_chatFrame_of frame_minor

theorem determinant_hat : DetHat :=
  qr_detHat_of algebraic_quantum_determinant capelli_hat_frame capelli_right_good left_right_swap

theorem determinant_hat_regular : DetHatRegular := qr_detHatRegular_of determinant_hat

theorem regular_to_smooth : RegularToSmooth := fun _ => determinant_hat

theorem determinant_generic : DetGeneric := qr_detGeneric_of determinant_hat_regular

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.DminStarPd
section
open Matrix Set
open scoped ComplexConjugate ContDiff Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.AdmissibleLieWords

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

lemma gf_pd (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) :
    U.IsPolyDeg (2 * r + 2) (fun g : Mat k r => ((Gf k r z z' g : ℝ) : ℂ)) := by
  exact gram_function_polynomial k r z z'

lemma dmin_pd (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) :
    U.IsPolyDeg (2 * r + 2) (fun g : Mat k r => Dmin k r z z' g l) := by
  obtain ⟨q, hq, he⟩ := minor_polynomial_property k r z z' l
  exact ⟨q, hq.trans (by have := l.isLt; omega), he⟩

section fac

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

lemma ubl_monoM (D : RealPlaceData k r Wp Wq) (L : Finset (Fin (r + 2))) (a b : Fin (r + 2) → ℕ) (c : ℕ)
    (hab : ∀ l, l ∉ L → l ≠ Fin.last (r + 1) → a l = 0 ∧ b l = 0) {S : Set (Mat k r)} (hSG : S ⊆ GV k r)
    {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hSD : ∀ g ∈ S, ∀ l, (l ∈ L ∨ l = Fin.last (r + 1)) → c₀ ≤ Complex.normSq (Dmin k r D.z D.z' g l))
    (hSGf : ∀ g ∈ S, c₀ ≤ Complex.normSq ((Gf k r D.z D.z' g : ℝ) : ℂ)) (n : ℕ) :
    UBL (C6.monoM D a b c) S n 0 (2 * r + 2) := by
  have hfac : ∀ l ∈ (Finset.univ : Finset (Fin (r + 2))),
      UBL (fun g => (Dmin k r D.z D.z' g l)⁻¹ ^ a l * (star (Dmin k r D.z D.z' g l))⁻¹ ^ b l)
        S n 0 (2 * r + 2) := by
    intro l _
    by_cases hl : l ∈ L ∨ l = Fin.last (r + 1)
    · have hl' : l.val ≤ 2 * r + 2 := by have := l.isLt; omega
      have h1 : UBL (fun g => (Dmin k r D.z D.z' g l)⁻¹ ^ a l) S n 0 (2 * r + 2) :=
        ubl_mono hSG (ubl_invpow (minor_polynomial_property k r D.z D.z' l) hSG hc₀
          (fun g hg => hSD g hg l hl) (a l) n) le_rfl hl'
      have h2 : UBL (fun g => (star (Dmin k r D.z D.z' g l))⁻¹ ^ b l) S n 0 (2 * r + 2) :=
        ubl_mono hSG (ubl_invpow (dmin_star_pd k r D.z D.z' l) hSG hc₀
          (fun g hg => by rw [Complex.star_def, Complex.normSq_conj]; exact hSD g hg l hl) (b l) n)
          le_rfl hl'
      exact ubl_mul hSG h1 h2
    · push_neg at hl
      obtain ⟨ha, hb⟩ := hab l hl.1 hl.2
      have e : (fun g => (Dmin k r D.z D.z' g l)⁻¹ ^ a l * (star (Dmin k r D.z D.z' g l))⁻¹ ^ b l) =
          fun _ => (1 : ℂ) := by
        funext g
        simp [ha, hb]
      rw [e]
      exact ubl_const 1 hSG n _
  have hP := ubl_prod hSG Finset.univ
    (fun l g => (Dmin k r D.z D.z' g l)⁻¹ ^ a l * (star (Dmin k r D.z D.z' g l))⁻¹ ^ b l) hfac
  have hG := ubl_invpow (gram_function_polynomial k r D.z D.z') hSG hc₀ hSGf c n
  exact ubl_mul hSG hP hG

private lemma rw_congr_on_open_of_eq_on_GV {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {V : Set (Mat k r)}
    (hV : IsOpen V) {f f' : Mat k r → F} (he : ∀ g ∈ GV k r, g ∈ V → f g = f' g) :
    ∀ (w : List (Mat k r)), (∀ X ∈ w, inLie k r X) → ∀ g ∈ GV k r, g ∈ V → Rw w f g = Rw w f' g := by
  intro w
  induction w with
  | nil => intro _ g hg hgV; exact he g hg hgV
  | cons X w ih =>
    intro hw g hg hgV
    have ih' := ih (fun Y hY => hw Y (List.mem_cons_of_mem _ hY))
    show Dx (false, X) (Rw w f) g = Dx (false, X) (Rw w f') g
    rw [Dx_eq, Dx_eq]
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [crv_ev (x := (false, X)) hV hgV] with t ht
    exact ih' _ (crv_mem (x := (false, X)) (hw X (by simp)) hg t) ht

private lemma dw_const_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] (c : ℂ) (f : Mat k r → F) :
    ∀ w : List (Bool × Mat k r), Dw w (fun g => c • f g) = fun g => c • Dw w f g := by
  intro w
  induction w with
  | nil => rfl
  | cons x w ih =>
    funext g
    show Dx x (Dw w (fun g => c • f g)) g = c • Dx x (Dw w f) g
    rw [ih, Dx_eq, Dx_eq]
    first
    | exact deriv_const_smul' c (f := fun t => Dw w f (crv x g t))
    | exact deriv_const_smul' (f := fun t => Dw w f (crv x g t)) c
    | simp [deriv_const_smul']

lemma ubl_fib (D : RealPlaceData k r Wp Wq) (E : Mat k r → C6.EndH Wp Wq) (hE : C6.FibBound D E) {ε : ℝ} (hε : 0 < ε)
    {S : Set (Mat k r)} (hS : ∀ g ∈ S, g ∈ GV k r ∧ ε ≤ Gf k r D.z D.z' g) (v : List (Mat k r))
    (hv : ∀ X ∈ v, inLie k r X) (n : ℕ) :
    UBL (Rw v E) S n (3 * (r + 1) * v.length) (3 * (r + 1)) := by
  obtain ⟨hE1, hE2⟩ := hE
  have hSsub : S ⊆ GPos D := fun g hg => ⟨(hS g hg).1, lt_of_lt_of_le hε (hS g hg).2⟩
  choose Cf hCf using fun i => hE2 ε hε i
  refine ⟨⟨|(v.map nz).prod| * ∑ j ∈ Finset.range (n + v.length + 1), |Cf j|, by positivity, ?_⟩, ?_⟩
  · intro w hw g hg
    obtain ⟨u, v', hu, hv', hlen, rfl⟩ := hw
    have hgGV := (hS g hg).1
    have hgε := (hS g hg).2
    have hX : 0 ≤ gN g := by
      first
      | positivity
      | (unfold gN; positivity)
      | (simp only [gN]; positivity)
    rw [Rw_scale v E, dw_const_smul, norm_smul]
    have hsplit : Dw (wL u ++ wR v') (Rw (v.map nrm) E) g = dLR u (v' ++ v.map nrm) E g := by
      rw [dLR_eq, Dw_append, Dw_append, Dw_wR, Dw_wR]
      rw [show Rw (v' ++ v.map nrm) E = Rw v' (Rw (v.map nrm) E) by simp only [Rw, List.foldr_append]]
    rw [hsplit]
    have hU : C6.UnitWords k r u (v' ++ v.map nrm) (u.length + (v' ++ v.map nrm).length) := by
      refine ⟨hu, fun X hX => ?_, rfl⟩
      rcases List.mem_append.1 hX with h | h
      · exact hv' X h
      · obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 h
        exact nrm_unit (hv Y hY)
    have hb := hCf (u.length + (v' ++ v.map nrm).length) u (v' ++ v.map nrm) hU g hgGV hgε
    have hlenw : (wL u ++ wR v').length = u.length + v'.length := by simp [wL, wR]
    have hexp : 3 * (r + 1) * (u.length + (v' ++ v.map nrm).length) =
        3 * (r + 1) * v.length + 3 * (r + 1) * (wL u ++ wR v').length := by
      rw [hlenw, List.length_append, List.length_map]; ring
    rw [hexp] at hb
    have hX' : 0 ≤ gN g ^ (3 * (r + 1) * v.length + 3 * (r + 1) * (wL u ++ wR v').length) :=
      pow_nonneg hX _
    have hi : u.length + (v' ++ v.map nrm).length < n + v.length + 1 := by
      rw [List.length_append, List.length_map]; omega
    have hCi : Cf (u.length + (v' ++ v.map nrm).length) ≤
        ∑ j ∈ Finset.range (n + v.length + 1), |Cf j| :=
      (le_abs_self _).trans (Finset.single_le_sum (f := fun j => |Cf j|)
        (fun j _ => abs_nonneg _) (Finset.mem_range.2 hi))
    have hnorm : ‖(((v.map nz).prod : ℝ) : ℂ)‖ = |(v.map nz).prod| := by
      first
      | simp
      | rw [Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm]
    calc |(v.map nz).prod| * ‖dLR u (v' ++ v.map nrm) E g‖
        ≤ |(v.map nz).prod| * (Cf (u.length + (v' ++ v.map nrm).length) *
            gN g ^ (3 * (r + 1) * v.length + 3 * (r + 1) * (wL u ++ wR v').length)) :=
          mul_le_mul_of_nonneg_left hb (abs_nonneg _)
      _ ≤ |(v.map nz).prod| * ((∑ j ∈ Finset.range (n + v.length + 1), |Cf j|) *
            gN g ^ (3 * (r + 1) * v.length + 3 * (r + 1) * (wL u ++ wR v').length)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hCi hX') (abs_nonneg _)
      _ = _ := by ring
  · intro g₀ hg₀
    obtain ⟨f', hf', V, hV, hgV, he⟩ := lss_of_ckOn hE1 hSsub g₀ hg₀
    refine ⟨Rw v f', ?_, V, hV, hgV, fun g' hg' hg'V => rw_congr_on_open_of_eq_on_GV hV he v hv g' hg' hg'V⟩
    rw [← Dw_wR]
    exact cdw _ hf'

end fac

end Formalism.FourierDecayAlt.P.AdmissibleLieWords
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.FnComm
section
namespace Formalism.FourierDecayAlt.TL

open Matrix Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr

section

variable {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {r : ℕ} {L : LevelData A r} {st : Start A}

theorem fn_comm (L : LevelData A r) {x y : A} (hx : x ∈ zfns L) (hy : y ∈ zfns L) : x * y = y * x :=
  L.fns_comm x (Or.inr hx) y (Or.inr hy)

theorem z10 (h : IsLevelStart L st) {Y : ℂ} (hi : Y ∈ st.inv) :
    st.QQ Y 1 0 * L.ζ = L.ζ * st.QQ Y 1 0 - st.QQ Y 1 1 ∧ Commute (st.QQ Y 1 0) L.ζb := by
  have hlow := h.low Y hi
  have htau := h.tau Y
  have mζ : L.ζ ∈ zfns L := by simp [zfns]
  have mζi : L.ζi ∈ zfns L := by simp [zfns]
  have mζb : L.ζb ∈ zfns L := by simp [zfns]
  have mGG : L.GG ∈ zfns L := by simp [zfns]
  have mGGi : L.GGi ∈ zfns L := by simp [zfns]
  have cm : ∀ {x y : A}, x ∈ zfns L → y ∈ zfns L → Commute x y := fun hx hy => fn_comm L hx hy
  have hX : ∀ g ∈ zfns L, Commute (st.x Y) g := h.x_fn Y
  have hE : ∀ g ∈ zfns L, Commute (st.ee Y) g := h.ee_fn Y
  have hc : ∀ a : A, Commute (algebraMap ℂ A (Y + 1 / 2)) a := fun a => Algebra.commutes _ a
  have hl : L.l0 Y + L.ζb * L.ζi * L.GGi * st.ee Y =
      -L.nab + (-(algebraMap ℂ A (Y + 1 / 2) * (L.ζb * L.GGi)) + L.ζb * L.ζi * L.GGi * st.ee Y) := by
    simp only [Formalism.FourierDecayAlt.R.LevelData.l0]
    abel
  rw [hl] at hlow
  have hT : ∀ g ∈ zfns L, Commute (-(algebraMap ℂ A (Y + 1 / 2) * (L.ζb * L.GGi)) +
      L.ζb * L.ζi * L.GGi * st.ee Y) g := by
    intro g hg
    apply Commute.add_left
    · exact ((hc _).mul_left ((cm mζb hg).mul_left (cm mGGi hg))).neg_left
    · exact (((cm mζb hg).mul_left (cm mζi hg)).mul_left (cm mGGi hg)).mul_left (hE _ hg)
  have hTz := hT _ mζ
  have hGXz : Commute (L.GG * st.x Y) L.ζ := (cm mGG mζ).mul_left (hX _ mζ)
  constructor
  · rw [hlow, htau]
    calc L.GG * st.x Y * (-L.nab + (-(algebraMap ℂ A (Y + 1 / 2) * (L.ζb * L.GGi)) +
          L.ζb * L.ζi * L.GGi * st.ee Y)) * L.ζ
        = L.GG * st.x Y * (-(L.nab * L.ζ) + (-(algebraMap ℂ A (Y + 1 / 2) * (L.ζb * L.GGi)) +
          L.ζb * L.ζi * L.GGi * st.ee Y) * L.ζ) := by noncomm_ring
      _ = L.GG * st.x Y * (-(L.ζ * L.nab + 1) + L.ζ * (-(algebraMap ℂ A (Y + 1 / 2) * (L.ζb * L.GGi)) +
          L.ζb * L.ζi * L.GGi * st.ee Y)) := by rw [L.nab_ζ, hTz.eq]
      _ = (L.GG * st.x Y * L.ζ) * (-L.nab + (-(algebraMap ℂ A (Y + 1 / 2) * (L.ζb * L.GGi)) +
          L.ζb * L.ζi * L.GGi * st.ee Y)) - L.GG * st.x Y := by noncomm_ring
      _ = L.ζ * (L.GG * st.x Y * (-L.nab + (-(algebraMap ℂ A (Y + 1 / 2) * (L.ζb * L.GGi)) +
          L.ζb * L.ζi * L.GGi * st.ee Y))) - L.GG * st.x Y := by
        rw [hGXz.eq]
        noncomm_ring
  · rw [hlow]
    have hnab : Commute L.nab L.ζb := L.nab_ζb
    exact ((cm mGG mζb).mul_left (hX _ mζb)).mul_left (hnab.neg_left.add_left (hT _ mζb))

theorem zetaQQ : ZetaQQ := by
  intro A _ _ _ _ r L st hS h Y hY hi
  have mζ : L.ζ ∈ zfns L := by simp [zfns]
  have mζb : L.ζb ∈ zfns L := by simp [zfns]
  have mG : L.GG ∈ zfns L := by simp [zfns]
  have sζb : star L.ζb = L.ζ := by rw [← hS.1, star_star]
  have herm : ∀ Z : ℂ, star Z = Z → ∀ i j, star (st.QQ Z i j) = st.QQ Z j i := fun Z hZ i j => by
    have := congrFun (congrFun (h.start.herm Z hZ) j) i
    rwa [Matrix.conjTranspose_apply] at this
  have base : ∀ Z : ℂ, star Z = Z → Z ∈ st.inv →
      (st.QQ Z 1 0 * L.ζ = L.ζ * st.QQ Z 1 0 - st.QQ Z 1 1 ∧ Commute (st.QQ Z 1 0) L.ζb ∧
      st.QQ Z 0 1 * L.ζb = L.ζb * st.QQ Z 0 1 + st.QQ Z 1 1 ∧ Commute (st.QQ Z 0 1) L.ζ ∧
      Commute (st.QQ Z 1 1) L.ζ ∧ Commute (st.QQ Z 1 1) L.ζb) := fun Z hZ hZi => by
    obtain ⟨a, b⟩ := z10 h hZi
    refine ⟨a, b, ?_, ?_, ?_, ?_⟩
    · have := congrArg star a
      rw [star_mul, star_sub, star_mul, herm Z hZ, herm Z hZ, hS.1] at this
      rw [this]; abel
    · have := congrArg star b.eq
      rw [star_mul, star_mul, herm Z hZ, sζb] at this
      exact this.symm
    · rw [h.tau]; exact Commute.mul_left (fn_comm L mG mζ) (h.x_fn Z _ mζ)
    · rw [h.tau]; exact Commute.mul_left (fn_comm L mG mζb) (h.x_fn Z _ mζb)
  refine ⟨base Y hY hi, fun hn => ?_⟩
  have cancel : ∀ Z ∈ st.inv, ∀ u : A, u * st.QQ Z 1 1 = 0 → u = 0 := fun Z hZ u hu => by
    rw [h.tau] at hu
    have : u * (L.GG * st.x Z) * st.xi Z * L.GGi = u := by
      rw [mul_assoc u, mul_assoc L.GG, (h.x_xi Z hZ).1, mul_one, mul_assoc, L.GG_GGi, mul_one]
    rw [← this, hu, zero_mul, zero_mul]
  have key : st.QQ Y 0 0 * L.ζb = L.ζb * st.QQ Y 0 0 + st.QQ Y 1 0 := by
    obtain ⟨-, b10, b01, -, -, -⟩ := base Y hY hi
    rcases hn with hm | hp
    · have hr : star (Y - 1) = Y - 1 := by rw [star_sub, hY, star_one]
      obtain ⟨-, -, c01, -, -, c11⟩ := base _ hr hm
      have d := congrFun (congrFun (h.start.det (Y - 1)).1 0) 1
      simp [Matrix.mul_apply, Fin.sum_univ_two, YangianSpanCharacter.T.J] at d
      have dq := Algebra.commutes (st.q (Y - 1)) L.ζb
      rw [← d] at dq
      apply eq_of_sub_eq_zero
      apply cancel _ hm
      have e1 := c11.eq
      have e2 := b10.eq
      calc _ = st.QQ Y 0 0 * (L.ζb * st.QQ (Y - 1) 1 1) - L.ζb * st.QQ Y 0 0 * st.QQ (Y - 1) 1 1
            - st.QQ Y 1 0 * st.QQ (Y - 1) 1 1 := by noncomm_ring
        _ = ((-st.QQ Y 1 0 * st.QQ (Y - 1) 0 1 + st.QQ Y 0 0 * st.QQ (Y - 1) 1 1) * L.ζb -
            L.ζb * (-st.QQ Y 1 0 * st.QQ (Y - 1) 0 1 + st.QQ Y 0 0 * st.QQ (Y - 1) 1 1)) +
            (st.QQ Y 1 0 * (st.QQ (Y - 1) 0 1 * L.ζb) - L.ζb * st.QQ Y 1 0 * st.QQ (Y - 1) 0 1
              - st.QQ Y 1 0 * st.QQ (Y - 1) 1 1) := by rw [← e1]; noncomm_ring
        _ = 0 := by
          rw [c01, ← e2]
          have : (-st.QQ Y 1 0 * st.QQ (Y - 1) 0 1 + st.QQ Y 0 0 * st.QQ (Y - 1) 1 1) * L.ζb -
            L.ζb * (-st.QQ Y 1 0 * st.QQ (Y - 1) 0 1 + st.QQ Y 0 0 * st.QQ (Y - 1) 1 1) = 0 := by
            rw [sub_eq_zero]; simpa [neg_mul] using dq
          rw [this]; noncomm_ring
    · have hr : star (Y + 1) = Y + 1 := by rw [star_add, hY, star_one]
      obtain ⟨-, c10, -, -, -, c11⟩ := base _ hr hp
      have d := congrFun (congrFun (h.start.det Y).2 0) 1
      have d' := congrFun (congrFun (h.start.det Y).2 1) 1
      simp [Matrix.mul_apply, Fin.sum_univ_two, YangianSpanCharacter.T.J] at d d'
      have dq := Algebra.commutes (st.q Y) L.ζb
      rw [← d] at dq
      apply eq_of_sub_eq_zero
      apply cancel _ hp
      have e1 := c11.eq
      have e2 := c10.eq
      have d2 : st.QQ Y 1 0 * st.QQ (Y + 1) 1 1 = st.QQ Y 1 1 * st.QQ (Y + 1) 1 0 := by
        have := d'; rw [neg_add_eq_zero] at this; exact this.symm
      calc _ = st.QQ Y 0 0 * (L.ζb * st.QQ (Y + 1) 1 1) - L.ζb * st.QQ Y 0 0 * st.QQ (Y + 1) 1 1
            - st.QQ Y 1 0 * st.QQ (Y + 1) 1 1 := by noncomm_ring
        _ = ((-st.QQ Y 0 1 * st.QQ (Y + 1) 1 0 + st.QQ Y 0 0 * st.QQ (Y + 1) 1 1) * L.ζb -
            L.ζb * (-st.QQ Y 0 1 * st.QQ (Y + 1) 1 0 + st.QQ Y 0 0 * st.QQ (Y + 1) 1 1)) +
            (st.QQ Y 0 1 * (st.QQ (Y + 1) 1 0 * L.ζb) - L.ζb * st.QQ Y 0 1 * st.QQ (Y + 1) 1 0
              - st.QQ Y 1 0 * st.QQ (Y + 1) 1 1) := by rw [← e1]; noncomm_ring
        _ = 0 := by
          rw [e2, ← mul_assoc (st.QQ Y 0 1), b01, d2]
          have : (-st.QQ Y 0 1 * st.QQ (Y + 1) 1 0 + st.QQ Y 0 0 * st.QQ (Y + 1) 1 1) * L.ζb -
            L.ζb * (-st.QQ Y 0 1 * st.QQ (Y + 1) 1 0 + st.QQ Y 0 0 * st.QQ (Y + 1) 1 1) = 0 := by
            rw [sub_eq_zero]; simpa [neg_mul] using dq
          rw [this]; noncomm_ring
  refine ⟨key, ?_⟩
  have := congrArg star key
  rw [star_mul, star_add, star_mul, herm Y hY, herm Y hY, sζb] at this
  rw [this]; abel

end

end Formalism.FourierDecayAlt.TL
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.FormPos
section
namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt NumberField MeasureTheory Formalism.QuantumDeterminants
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

section defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

def rrC (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) :
    Fin S.f → ℝ → ℕ → List C.Letter → C.LPt → C.LPt → ℂ :=
  fun v ε i w P Q =>
    ((1 / (D.bSt (D.kapG (S.g : ℝ) (S6.rd E)) P * D.bSt (D.kapG (S.g : ℝ) (S6.rd E)) Q *
      D.GamLev S.G.k S.G.r (D.kapG (S.g : ℝ) (S6.rd E)) (D.deG (S.g : ℝ) (S6.rd E)) i) : ℝ) : ℂ) *
      (p v).RR (F v ε) i w (D.toStd S.G.r (S.g : ℝ) 1 P) (D.toStd S.G.r (S.g : ℝ) 1 Q)

def setC (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) : C.HidaSetting E Wp Wq :=
  KB.withRR S (rrC S p F)

end defs

def FormPos : Prop :=
  P5.ThmPActual → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter), KB.CutWord P p.l0 w → ∀ x ε, 0 < ε →
    (∀ e, JC.NiceCoef (p.T.bs j) ε (x e)) → 0 ≤ p.form j hj w x x

end

end Formalism.FourierDecayAlt.P.PBL
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.IdentityOperator
section
namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TL Formalism.REAL Formalism.QuantumDeterminants

noncomputable section

theorem identity_operator : TL.IdOp := by
  intro k r Wp Wq _ _ _ _ _ Bs
  let T : B.DTerm k r Wp Wq :=
    { coef := fun _ => 1
      coefAdj := fun _ => 1
      word := []
      word_lie := fun X hX => by simp at hX
      adj_id := fun _ _ _ => rfl }
  have hap : ∀ F, B.opApply [T] F = F := by
    intro F
    funext g
    simp [B.opApply, B.Rw, T]
  refine ⟨[T], ⟨?_, ?_, ?_⟩, hap⟩
  · intro T' hT'
    simp only [List.mem_singleton] at hT'
    subst hT'
    refine ⟨?_, ?_⟩ <;> intro g₀ _ <;>
      refine ⟨Set.univ, fun _ => 1, ?_, Set.mem_univ _, ?_, fun _ _ _ => rfl⟩
    all_goals
      first
      | exact isOpen_univ
      | exact contDiffOn_const
      | (open scoped Formalism.FourierDecayAlt.B in exact contDiffOn_const)
      | (open scoped Matrix.Norms.Elementwise in exact contDiffOn_const)
      | (open scoped Matrix.Norms.Operator in exact contDiffOn_const)
      | exact @contDiffOn_const _ _ _ _ _ _ _ _ _ _ _ _
  · intro p _ f _ g _
    simp only [hap]
  · intro T' hT'
    simp only [List.mem_singleton] at hT'
    subst hT'
    refine ⟨fun _ => 1, 0, 0, 0, [], ⟨1, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · simp
    · intro g
      simp
    · intro l _ _
      simp
    · simp [T]
    · simp
    · intro g _
      simp [C6.monoM, C6.Epart, T]

end

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.IrreducibleCapelliModules
section
namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt

theorem capelli_singular : Qr.CapSing := qr_capSing_of singular_dominant exists_singular_maximal_vector

theorem top_weight_singular : Qr.TopWeightSing := qr_topWeightSing_of exists_singular_maximal_vector capelli_singular

theorem vector_descent : Qr.VecDown := qr_vecDown_of quantum_minor_polynomial polynomial_vanishing

theorem raising_nonzero : Qr.RaiseNZ := qr_raiseNZ_of covariant_raising

theorem lowering_nonzero : Qr.LowerNZ := qr_lowerNZ_of vector_descent

theorem branching_decomposition : Qr.Decomp :=
  qr_decomp_of exists_singular_maximal_vector capelli_singular capelli_stabilizer submodule_relations covariant_raising vector_descent
    raising_nonzero lowering_nonzero

theorem multiplicity_one : Qr.MultOne := qr_multOne_of exists_singular_maximal_vector dual_minor span_singular_vectors

theorem irreducible_capelli_modules : Qr.IrredCap :=
  qr_irredCap_of exists_singular_maximal_vector capelli_singular capelli_stabilizer submodule_relations top_weight_singular
    dual_minor span_top_vectors multiplicity_one branching_decomposition capelli_independence

theorem branching_algebraic : Qr.BranchingAlg := qr_branchingAlg_of branching_decomposition capelli_independence irreducible_capelli_modules

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.OperatorsCommuteTranslations
section
namespace Formalism.FourierDecayAlt.P

theorem operators_commute_translations' : Formalism.FourierDecayAlt.C3.OperatorsCommuteTranslations := operators_commute_translations
theorem isotropicNormalFormPartial_statement : Formalism.FourierDecayAlt.C3.IsotropicNormalFormPartial := isotropic_normal_form_partial

end Formalism.FourierDecayAlt.P
end

