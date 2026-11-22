import Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothLevOfLoc
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DegLiftOf
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0230
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0231
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0212

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.FirstDerivativeAtNormalSet
section
open Matrix Finset MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBG

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem first_derivative_at_normal_set {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (z z' : Fin (2 * r + k + 1) → ℂ)
    (hz : inWb k r z) (hz' : inWb k r z') (i0 s : ℕ) (hs : 1 ≤ s) (hj : i0 + s ≤ r)
    (hh : Matrix (Fin i0) (Fin i0) ℂ) (τ : ℂ) (hdet : hh.det ≠ 0) (hτ : τ ≠ 0) (x₁ : B.Mat k r)
    (hx₁G : x₁ ∈ B.GV k r) (hD₁ : Dmin k r z z' x₁ ⟨i0 + s, by omega⟩ ≠ 0)
    (hnf : ∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val < i0 + s →
      xi0 x₁ a p = if p.val < i0 + s then C3.Zb i0 s hh τ a.val p.val else 0)
    (hnfy : ∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val < i0 + s →
      y0 x₁ a p = if r + k < p.val ∧ 2 * r + k - p.val < i0 + s then star (C3.Zb i0 s hh τ a.val (2 * r + k - p.val))
        else 0)
    (K : B.Mat k r → E) (hK : ∀ y ∈ B.GV k r, Dmin k r z z' y ⟨i0 + s, by omega⟩ ≠ 0 → CapelliWordSumExpansion.Loc (⊤ : ℕ∞) K y)
    (hR : ∀ y (p q : Fin (2 * r + k + 1)), C3.InNp k r p q → EabH (Hpk k r) p q K y = C3.dpsiP k r z' p q • K y)
    (sx : B.Mat k r) (hsx : sx ∈ Sset k r z) (b : Bool) (Y : ℝ) :
    D.vLet k r z z' (i0 + s) hj (b, Y) 1 K (sx * x₁) =
      cLift s τ b • D.vLet k r z z' i0 (by omega) (b, Y) 0 K (sx * x₁) := by
  rw [vLet_left z z' hz hz' _ _ _ _ K sx x₁ hsx hx₁G, vLet_left z z' hz hz' _ _ _ _ K sx x₁ hsx hx₁G]
  have hsG : sx ∈ B.GV k r := Formalism.QuantumDeterminants.Sset_UH hsx
  set Dset : Set (Q.Mx k r) := {y | Dmin k r z z' y ⟨i0 + s, by omega⟩ ≠ 0} with hDset
  have hDo : IsOpen Dset := isOpen_ne_fun ((contDiff_Dmin z z' _).continuous) continuous_const
  have hx₁ : x₁ ∈ Q.Glev k r 0 ∩ Dset := ⟨Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hx₁G, hD₁⟩
  have hDinv : ∀ y, Dmin k r z z' (sx * y) ⟨i0 + s, by omega⟩ = Dmin k r z z' y ⟨i0 + s, by omega⟩ := by
    intro y
    have := Formalism.QuantumDeterminants.diagonal_inverse_holds k r z z' hz hz' sx hsx 1 (one_mem_Sset k r z') y ⟨i0 + s, by omega⟩
    rwa [Matrix.mul_one] at this
  have hK' : Q.SmoothLev k r 0 Dset (fun y => K (sx * y)) := by
    apply smoothLev_of_loc
    intro y hy
    refine loc_left hsG (hK _ (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul hsG hy.1.1) ?_)
    rw [hDinv]; exact hy.2
  have hR' : ∀ g ∈ Q.Glev k r 0 ∩ Dset, ∀ p q, C3.InNp k r p q →
      Q.EH k r p q (fun y => K (sx * y)) g = C3.dpsiP k r z' p q • (fun y => K (sx * y)) g := by
    intro g _ p q hpq
    show EabH (Hpk k r) p q (fun y => K (sx * y)) g = _
    rw [AAInvW.ly_Eab_left]
    exact hR _ p q hpq
  cases b
  · have := letter_minus_component_one_eq_smul_component_zero hDo z z' i0 s hs hj hh τ hdet hτ x₁ hx₁ hx₁G hnf hnfy _ hK' hR' Y
    simp only [cLift, Bool.false_eq_true, if_false]
    exact this
  · have := letter_plus_component_one_eq_smul_component_zero hDo z z' i0 s hs hj hh τ hdet hτ x₁ hx₁ hnf _ hK' hR' Y
    simp only [cLift, if_true]
    exact this

theorem vLet_congr_level {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (z z' : Fin (2 * r + k + 1) → ℂ) {j₁ j₂ : ℕ} (hj : j₁ = j₂) (h₁ : j₁ ≤ r) (h₂ : j₂ ≤ r) (l : C.Letter) (e : Fin 2)
    (f : B.Mat k r → E) : D.vLet k r z z' j₁ h₁ l e f = D.vLet k r z z' j₂ h₂ l e f := by subst hj; rfl

theorem dmin_congr {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) {j₁ j₂ : ℕ} (hj : j₁ = j₂)
    (h₁ : j₁ < r + 2) (h₂ : j₂ < r + 2) : Dmin k r z z' g ⟨j₁, h₁⟩ = Dmin k r z z' g ⟨j₂, h₂⟩ := by subst hj; rfl

theorem coeff_recover {V : Type} [AddCommGroup V] [Module ℂ V] (n : ℕ) (C : Fin n → V) (l : Fin n) :
    C l = ∑ i : Fin n, (Matrix.vandermonde (fun i : Fin n => (((i : ℕ) : ℝ) : ℂ)))⁻¹ l i •
      ∑ m : Fin n, ((((i : ℕ) : ℝ) : ℂ) ^ (m : ℕ)) • C m := by
  have hτ : Function.Injective (fun i : Fin n => (((i : ℕ) : ℝ) : ℂ)) := by
    intro a b hab
    simp only [Complex.ofReal_inj, Nat.cast_inj] at hab
    exact Fin.ext hab
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul]
  simp only [vand_row _ hτ l, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

section core

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem liftDeg_core {k r : ℕ} (T : D.LevTower k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (j s : ℕ) (hj : j ≤ r)
    (h : C.LPt) (τ : ℂ) (ha : D.IsLocPt (h ++ [(s, τ)]) j)
    (w' : List C.Letter) (a' : Wd.Ix (Fin w'.length)) (b : Bool) (δ : ℝ) (g : B.Mat k (r - j))
    (X : Type) [MeasurableSpace X] (μ : Measure X) (ℓ : X → ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)))
    (sx : X → B.Mat k r) (x₁ : B.Mat k r) (hsx : ∀ x, sx x ∈ Sset k r T.base.z) (hx₁G : x₁ ∈ B.GV k r)
    (hnf : ∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val < D.ptSize h + s →
      xi0 x₁ a p = if p.val < D.ptSize h + s then
        C3.Zb (D.ptSize h) s (U.hMat (D.ptPerm h) (D.ptDiag h)) τ a.val p.val else 0)
    (hnfy : ∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val < D.ptSize h + s →
      y0 x₁ a p = if r + k < p.val ∧ 2 * r + k - p.val < D.ptSize h + s then
        star (C3.Zb (D.ptSize h) s (U.hMat (D.ptPerm h) (D.ptDiag h)) τ a.val (2 * r + k - p.val)) else 0)
    (PC : (B.Mat k r → (Wq →L[ℂ] Wp)) → Prop)
    (hFub : ∀ H, PC H → Integrable (fun x => ℓ x (Kr T.base H (sx x * x₁))) μ ∧
      B.JF (T.bs j) (D.castF (by simp [ha.2]) (D.sliceAt k r T.base.z T.base.z' H (h ++ [(s, τ)]))) g =
        ∫ x, ℓ x (Kr T.base H (sx x * x₁)) ∂μ)
    (hPW : ∀ (w : List C.Letter) (e : Wd.Ix (Fin w.length)), PC (D.uwG k r T.base.z T.base.z' F j hj w e))
    (hloc : ∀ H, PC H → ∀ y ∈ B.GV k r, Dmin k r T.base.z T.base.z' y ⟨j, by omega⟩ ≠ 0 →
      CapelliWordSumExpansion.Loc (⊤ : ℕ∞) (Kr T.base H) y)
    (hvl : ∀ H, PC H → ∀ y ∈ B.GV k r, Dmin k r T.base.z T.base.z' y ⟨j, by omega⟩ ≠ 0 → ∀ (l : C.Letter) (e : Fin 2),
      Kr T.base (D.vLet k r T.base.z T.base.z' j hj l e H) y = D.vLet k r T.base.z T.base.z' j hj l e (Kr T.base H) y) :
    ∃ c : Fin (j - s + 1) → (Wq →L[ℂ] Wp),
      c (Fin.last (j - s)) = cLift s τ b • B.JF (T.bs j) (KB.slv T F j hj w' (h ++ [(s, τ)]) ha.2 a') g ∧
      ∀ y : ℝ, B.JF (T.bs j) (KB.slv T F j hj ((b, y + δ) :: w') (h ++ [(s, τ)]) ha.2 (Fin.cons 1 a')) g =
        ∑ l : Fin (j - s + 1), ((y : ℂ) ^ (l : ℕ)) • c l := by
  classical
  set z := T.base.z with hzdef
  set z' := T.base.z' with hz'def
  have hz : inWb k r z := T.base.z_mem
  have hz' : inWb k r z' := T.base.z'_mem
  have hsz : D.ptSize (h ++ [(s, τ)]) = D.ptSize h + s := Formalism.FourierDecayAlt.P.Dx2.SL.ptSize_append h s τ
  have hs1 : 1 ≤ s := (ha.1 (s, τ) (by simp)).1
  have hτ : τ ≠ 0 := (ha.1 (s, τ) (by simp)).2
  have hjeq : j = D.ptSize h + s := by rw [← ha.2, hsz]
  set i0 := D.ptSize h with hi0
  have hloc_h : D.IsLocPt h (D.ptSize h) := Formalism.FourierDecayAlt.P.Dx2.SL.isLocPt_head ⟨ha.1, rfl⟩
  set hh := U.hMat (D.ptPerm h) (D.ptDiag h) with hhdef
  have hdet : hh.det ≠ 0 := Formalism.FourierDecayAlt.P.Ux10.det_hMat_ne _ _
    (fun q => Formalism.FourierDecayAlt.P.JCTx6.Link2.ptScal_ne h hloc_h.1 q q.2)
  have hjr : i0 + s ≤ r := by omega
  have hDl : C3.Dlead i0 s hh τ (i0 + s) ≠ 0 := by
    rw [(Formalism.FourierDecayAlt.P.SignAntidiagonal.derivative_leading_zb i0 s hh τ).2]
    refine mul_ne_zero (mul_ne_zero hdet (pow_ne_zero _ hτ)) ?_
    unfold C3.sgnW; exact pow_ne_zero _ (by norm_num)
  have hD₁ : Dmin k r z z' x₁ ⟨i0 + s, by omega⟩ ≠ 0 := by
    rw [dmin_nf z z' x₁ i0 s hh τ hjr hnf (i0 + s) le_rfl]; exact hDl
  have hDinv : ∀ (y x : B.Mat k r) (hyS : y ∈ Sset k r z) (n : ℕ) (hn : n < r + 2),
      Dmin k r z z' (y * x) ⟨n, hn⟩ = Dmin k r z z' x ⟨n, hn⟩ := by
    intro y x hyS n hn
    have := Formalism.QuantumDeterminants.diagonal_inverse_holds k r z z' hz hz' y hyS 1 (one_mem_Sset k r z') x ⟨n, hn⟩
    rwa [Matrix.mul_one] at this
  have hyG : ∀ x, sx x * x₁ ∈ B.GV k r := fun x => Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.QuantumDeterminants.Sset_UH (hsx x)) hx₁G
  have hyD : ∀ x, Dmin k r z z' (sx x * x₁) ⟨j, by omega⟩ ≠ 0 := by
    intro x
    rw [hDinv _ _ (hsx x), dmin_congr z z' x₁ hjeq _ (by omega)]
    exact hD₁
  set G := D.uwG k r z z' F j hj w' a' with hGdef
  have hG := hPW w' a'
  set KG := Kr T.base G with hKG

  have key : ∀ (x : X) (Y : ℝ), Kr T.base (D.uwG k r z z' F j hj ((b, Y) :: w') (Fin.cons 1 a')) (sx x * x₁) =
      cLift s τ b • D.vLet k r z z' i0 (by omega) (b, Y) 0 KG (sx x * x₁) := by
    intro x Y
    show Kr T.base (D.vLet k r z z' j hj (b, Y) 1 G) (sx x * x₁) = _
    rw [hvl G hG _ (hyG x) (hyD x), vLet_congr_level z z' hjeq hj hjr]
    refine first_derivative_at_normal_set z z' hz hz' i0 s hs1 hjr hh τ hdet hτ x₁ hx₁G hD₁ hnf hnfy KG (fun y hy hyd => ?_)
      (fun y p q hpq => kr_rule T.base G y p q hpq) (sx x) (hsx x) b Y
    exact hloc G hG y hy (by rw [dmin_congr z z' y hjeq _ (by omega)]; exact hyd)

  have poly : ∀ x : X, ∃ c : Fin (i0 + 1) → (Wq →L[ℂ] Wp), c (Fin.last i0) = KG (sx x * x₁) ∧
      ∀ Y : ℝ, D.vLet k r z z' i0 (by omega) (b, Y + δ) 0 KG (sx x * x₁) = ∑ l : Fin (i0 + 1), ((Y : ℂ) ^ (l : ℕ)) • c l := by
    intro x
    have hDi : Dmin k r z z' (sx x * x₁) ⟨i0, by omega⟩ ≠ 0 := by
      rw [hDinv _ _ (hsx x), dmin_nf z z' x₁ i0 s hh τ hjr hnf i0 (by omega),
        (Formalism.FourierDecayAlt.P.SignAntidiagonal.derivative_leading_zb i0 s hh τ).1]
      exact hdet
    obtain ⟨c₀, hc₀l, hc₀⟩ := vLet_poly (E := Wq →L[ℂ] Wp) (j := i0) (by omega) z z' KG (sx x * x₁) (hyG x) hDi
      (hloc G hG _ (hyG x) (hyD x)) b 0
    obtain ⟨c', hc'l, hsh⟩ := poly_shift i0 c₀ (δ : ℂ)
    refine ⟨c', by rw [hc'l, hc₀l, if_pos rfl], fun Y => ?_⟩
    rw [hc₀ (Y + δ), ← hsh (Y : ℂ)]
    push_cast
    rfl
  choose cf hcfl hcfY using poly
  have hcL : cLift s τ b ≠ 0 := by
    unfold cLift
    refine mul_ne_zero (pow_ne_zero _ (by norm_num)) ?_
    cases b
    · simp only [Bool.false_eq_true, if_false]; exact inv_ne_zero ((map_ne_zero _).2 hτ)
    · simp only [if_true]; exact inv_ne_zero hτ

  have hnode : ∀ (x : X) (Y : ℝ), D.vLet k r z z' i0 (by omega) (b, Y) 0 KG (sx x * x₁) =
      (cLift s τ b)⁻¹ • Kr T.base (D.uwG k r z z' F j hj ((b, Y) :: w') (Fin.cons 1 a')) (sx x * x₁) := by
    intro x Y
    rw [key x Y, smul_smul, inv_mul_cancel₀ hcL, one_smul]
  set Vi := (Matrix.vandermonde (fun i : Fin (i0 + 1) => (((i : ℕ) : ℝ) : ℂ)))⁻¹ with hVi
  have hdl : ∀ (x : X) (l : Fin (i0 + 1)), ℓ x (cf x l) = ∑ i : Fin (i0 + 1), (Vi l i * (cLift s τ b)⁻¹) •
      ℓ x (Kr T.base (D.uwG k r z z' F j hj ((b, ((i : ℕ) : ℝ) + δ) :: w') (Fin.cons 1 a')) (sx x * x₁)) := by
    intro x l
    rw [coeff_recover (i0 + 1) (cf x) l, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← hcfY x ((i : ℕ) : ℝ), hnode x, map_smul, map_smul, smul_smul]
  have hint : ∀ l : Fin (i0 + 1), Integrable (fun x => ℓ x (cf x l)) μ := by
    intro l
    simp only [hdl]
    exact integrable_finset_sum _ (fun i _ => ((hFub (D.uwG k r z z' F j hj ((b, ((i : ℕ) : ℝ) + δ) :: w') (Fin.cons 1 a'))
      (hPW _ _)).1).smul (Vi l i * (cLift s τ b)⁻¹))
  set c' : Fin (i0 + 1) → (Wq →L[ℂ] Wp) := fun l => cLift s τ b • ∫ x, ℓ x (cf x l) ∂μ with hc'
  have hc'top : c' (Fin.last i0) = cLift s τ b • B.JF (T.bs j) (KB.slv T F j hj w' (h ++ [(s, τ)]) ha.2 a') g := by
    simp only [hc', hcfl]
    congr 1
    exact ((hFub G hG).2).symm
  have hc'exp : ∀ y : ℝ, B.JF (T.bs j) (KB.slv T F j hj ((b, y + δ) :: w') (h ++ [(s, τ)]) ha.2 (Fin.cons 1 a')) g =
      ∑ l : Fin (i0 + 1), ((y : ℂ) ^ (l : ℕ)) • c' l := by
    intro y
    have e1 := (hFub _ (hPW ((b, y + δ) :: w') (Fin.cons 1 a'))).2
    show B.JF (T.bs j) (D.castF _ (D.sliceAt k r z z' (D.uwG k r z z' F j hj ((b, y + δ) :: w') (Fin.cons 1 a'))
      (h ++ [(s, τ)]))) g = _
    rw [e1]
    have e2 : ∀ x, ℓ x (Kr T.base (D.uwG k r z z' F j hj ((b, y + δ) :: w') (Fin.cons 1 a')) (sx x * x₁)) =
        ∑ l : Fin (i0 + 1), (((y : ℂ) ^ (l : ℕ)) * cLift s τ b) • ℓ x (cf x l) := by
      intro x
      rw [key x (y + δ), hcfY x y, map_smul, map_sum, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro l _
      rw [map_smul, smul_smul, mul_comm]
    simp only [e2]
    rw [integral_finsetSum Finset.univ (f := fun (l : Fin (i0 + 1)) x => (((y : ℂ) ^ (l : ℕ)) * cLift s τ b) • ℓ x (cf x l))
      (fun l _ => (hint l).smul (((y : ℂ) ^ (l : ℕ)) * cLift s τ b))]
    apply Finset.sum_congr rfl
    intro l _
    rw [integral_smul, hc', smul_smul]
  have hcast : j - s + 1 = i0 + 1 := by omega
  refine ⟨fun l => c' (Fin.cast hcast l), ?_, fun y => ?_⟩
  · have : Fin.cast hcast (Fin.last (j - s)) = Fin.last i0 := Fin.ext (by simp <;> omega)
    simp only [this]
    exact hc'top
  · rw [hc'exp y]
    exact (Fintype.sum_equiv (finCongr hcast) _ _ (fun l => rfl)).symm

end core

end Formalism.FourierDecayAlt.P.PBG
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.FltZeroEq
section
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JfS.Sym

noncomputable section

variable {k r : ℕ}

theorem colN {ζ : B.Mat k r} (hζ : B.inLie k r ζ) (z : Fin (2 * r + k + 1) → ℂ)
    (hN : ∀ X ∈ lieOf (Sset k r z), (Matrix.trace (ζ * X)).re = 0) (a : Fin r) :
    ∀ i : Fin (2 * r + k + 1), a.val < i.val → (ζ *ᵥ bvec (eI k r a)) i = 0 := by
  have orth : ∀ v : Fin (2 * r + k + 1) → ℂ, (∀ b : Fin r, b.val ≤ a.val → v (esI k r b) = 0) →
      herm (Hpk k r) (ζ *ᵥ bvec (eI k r a)) v = 0 := by
    intro v hv
    refine herm_zero_of_trace hζ _ v (hN _ (xuv_lieN z a v hv)) (hN _ (xuv_lieN z a _ ?_))
    intro b hb; simp [hv b hb]
  intro i hi
  by_cases h1 : i.val < r
  · have e := herm_es (ζ *ᵥ bvec (eI k r a)) ⟨i.val, h1⟩
    rw [show eI k r ⟨i.val, h1⟩ = i from Fin.ext rfl] at e
    rw [← e]
    refine orth _ (fun b hb => ?_)
    have : esI k r b ≠ esI k r ⟨i.val, h1⟩ := by
      intro h; have := congrArg Fin.val h; simp [esI] at this; omega
    simp [bvec, this]
  · by_cases h2 : i.val ≤ r + k
    · have hw := herm_w (ζ *ᵥ bvec (eI k r a)) i (by omega) h2
      have h0 : herm (Hpk k r) (ζ *ᵥ bvec (eI k r a)) (bvec i) = 0 := by
        refine orth _ (fun b hb => ?_)
        have : esI k r b ≠ i := by
          intro h; have := congrArg Fin.val h; simp [esI] at this; omega
        simp [bvec, this]
      rw [hw] at h0
      split_ifs at h0 with h3
      · exact neg_eq_zero.1 h0
      · exact h0
    · have e : i = esI k r ⟨2 * r + k - i.val, by omega⟩ := by
        apply Fin.ext; simp [esI]; omega
      have e2 := herm_e (ζ *ᵥ bvec (eI k r a)) ⟨2 * r + k - i.val, by omega⟩
      rw [← e] at e2
      rw [← e2]
      refine orth _ (fun b hb => ?_)
      have : esI k r b ≠ eI k r ⟨2 * r + k - i.val, by omega⟩ := by
        intro h; have := congrArg Fin.val h; simp [esI, eI] at this; omega
      simp [bvec, this]

theorem flt_bvec (a : ℕ) (c : Fin r) (hc : c.val < a) : Flt (k := k) a (bvec (eI k r c)) := by
  intro i hi
  have : i ≠ eI k r c := by intro h; rw [h] at hi; simp [eI] at hi; omega
  simp [bvec, this]

theorem flt_zero_eq (y : Fin (2 * r + k + 1) → ℂ) (hy : Flt 0 y) : y = 0 := by
  funext i; exact hy i (Nat.zero_le _)

theorem stepNil (ζ : B.Mat k r) (N : ℕ) (hζN : ζ ^ N = 0) (a : Fin r)
    (hcol : ∀ i : Fin (2 * r + k + 1), a.val < i.val → (ζ *ᵥ bvec (eI k r a)) i = 0)
    (hkill : ∀ y, Flt a.val y → ζ *ᵥ y = 0) : Flt a.val (ζ *ᵥ bvec (eI k r a)) := by
  set ea := bvec (eI k r a) with hea
  set x := ζ *ᵥ ea with hx
  set xa := x (eI k r a)
  have hea1 : ea (eI k r a) = 1 := by simp [hea, bvec]
  have hy : Flt a.val (x - xa • ea) := by
    intro i hi
    by_cases he : i = eI k r a
    · rw [he]; simp only [Pi.sub_apply, Pi.smul_apply, hea1, smul_eq_mul, mul_one]; exact sub_self _
    · have hi' : a.val < i.val := by
        have : i.val ≠ a.val := fun h => he (Fin.ext h)
        omega
      simp [hcol i hi', hea, bvec, he]
  have hζx : ζ *ᵥ x = xa • x := by
    have e : x = xa • ea + (x - xa • ea) := by abel
    conv_lhs => rw [e]
    rw [mulVec_add, mulVec_smul, hkill _ hy, add_zero]
  have hp : ∀ m, (ζ ^ (m + 1)) *ᵥ ea = xa ^ m • x := by
    intro m
    induction m with
    | zero => simp [hx]
    | succ m ih => rw [pow_succ', ← mulVec_mulVec, ih, mulVec_smul, hζx, smul_smul, pow_succ]
  have hxa : xa = 0 := by
    cases N with
    | zero =>
      exfalso
      have := congrFun (congrArg (fun M => M *ᵥ ea) hζN) (eI k r a)
      simp [hea1] at this
    | succ m =>
      have := congrFun (hp m) (eI k r a)
      rw [hζN, zero_mulVec] at this
      simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul] at this
      have h2 : xa ^ (m + 1) = 0 := by rw [pow_succ]; exact this.symm
      exact (pow_eq_zero_iff'.1 h2).1
  have : x = x - xa • ea := by rw [hxa, zero_smul, sub_zero]
  rw [this]; exact hy

theorem killX (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r)
    (hD : ∀ a (ha : a ≤ r), Dmin k r z z' g ⟨a, by omega⟩ ≠ 0)
    (ξ η : B.Mat k r) (hξ : B.inLie k r ξ) (N : ℕ) (hξN : ξ ^ N = 0) (hηN : η ^ N = 0)
    (hgη : g * η = ξ * g)
    (colξ : ∀ a : Fin r, ∀ i : Fin (2 * r + k + 1), a.val < i.val → (ξ *ᵥ bvec (eI k r a)) i = 0)
    (colη : ∀ a : Fin r, ∀ i : Fin (2 * r + k + 1), a.val < i.val → (η *ᵥ bvec (eI k r a)) i = 0) :
    ∀ a, a ≤ r → ∀ y, Flt a y → ξ *ᵥ y = 0 ∧ η *ᵥ y = 0 := by
  have hξg : ∀ y, ξ *ᵥ (g *ᵥ y) = g *ᵥ (η *ᵥ y) := by
    intro y; rw [mulVec_mulVec, mulVec_mulVec, hgη]
  intro a
  induction a with
  | zero =>
    intro _ y hy
    rw [flt_zero_eq y hy, mulVec_zero, mulVec_zero]
    exact ⟨rfl, rfl⟩
  | succ a ih =>
    intro ha y hy
    have IH := ih (by omega)
    set a' : Fin r := ⟨a, by omega⟩
    have hxξ : Flt a (ξ *ᵥ bvec (eI k r a')) := stepNil ξ N hξN a' (colξ a') (fun y hy => (IH y hy).1)
    have hxη : Flt a (η *ᵥ bvec (eI k r a')) := stepNil η N hηN a' (colη a') (fun y hy => (IH y hy).2)
    have hξa : ξ *ᵥ bvec (eI k r a') = 0 := by
      refine dlem_ii z z' g a (by omega) (hD a (by omega)) _ hxξ (fun c hc => ?_)
      rw [herm_skew hξ, hξg, (IH _ (flt_bvec a c hc)).2, mulVec_zero, herm_zero_right, neg_zero]
    have hηa : η *ᵥ bvec (eI k r a') = 0 := by
      refine dlem_i z z' g a (by omega) (hD a (by omega)) _ hxη (fun c hc => ?_)
      rw [← hξg, herm_skew hξ, (IH _ (flt_bvec a c hc)).1, herm_zero_right, neg_zero]
    set ya := y (eI k r a')
    have hrest : Flt a (y - ya • bvec (eI k r a')) := by
      intro i hi
      by_cases he : i = eI k r a'
      · rw [he]; simp [bvec, ya]
      · have hi' : a + 1 ≤ i.val := by
          have : i.val ≠ a := fun h => he (Fin.ext h)
          omega
        simp [hy i hi', bvec, he]
    have e : y = ya • bvec (eI k r a') + (y - ya • bvec (eI k r a')) := by abel
    rw [e, mulVec_add, mulVec_smul, mulVec_add, mulVec_smul, hξa, hηa, (IH _ hrest).1, (IH _ hrest).2]
    simp

end

end Formalism.FourierDecayAlt.P.CutMP.JfS.Sym
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadPictureEmptyWord
section
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBP

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5

section read

variable {k : ℕ}

theorem pic_read {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {n ρ : ℕ} (hn : 1 + ρ = n)
    {z z' : Fin (2 * n + k + 1) → ℂ} {zs zs' : Fin (2 * ρ + k + 1) → ℂ}
    (hz : z = D.castV hn (liftVec k 1 ρ zs)) (hz' : z' = D.castV hn (liftVec k 1 ρ zs'))
    (Φ : Fn k n E) (J : Mx k n → E)
    (hΦ : ∀ x ∈ DomR k n z z', Φ x.1 x.2 = resG k n (Fin.last n) J x.1 x.2)
    {t : ℂ} (ht : t ≠ 0) (y : (Fin ρ → ℂ) × Mx k ρ) (hy : y ∈ DomR k ρ zs zs') :
    Φ (fun l => PBH.consC t y.1 (Fin.cast hn.symm l)) (D.castM hn (ιLev k 1 ρ y.2)) =
      ((‖t‖ ^ (2 * n + k) : ℝ) : ℂ) •
        resG k ρ (Fin.last ρ) (fun γ => J (D.castM hn (U.mMap k 1 ρ (Matrix.of fun _ _ => t) γ))) y.1 y.2 := by
  subst hn
  rw [Formalism.FourierDecayAlt.P.JCTx5.castV_rfl] at hz hz'
  subst hz hz'
  simp only [Fin.cast_eq_self, Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]
  rw [hΦ _ ((PBH.domR_iota ht zs zs' y.1 y.2).2 hy)]
  exact resG_consC ht J y.1 y.2

end read

def HeadPicNil : Prop :=
    ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (j : ℕ) (hj : j + 1 ≤ P.r) (h : C.LPt) (hh : D.IsLocPt h j)
    (L : R.LevelData (Pr (Q.RadSp (JC.parLev P j).k (JC.parLev P j).r (p.T.bs j).z (p.T.bs j).z' (p.T.bs j).π
      (p.T.bs j).π')) (JC.parLev P j).r)
    (Φ : Wd.Ix (Fin ([] : List C.Letter).length) →
      Q.RadSp (JC.parLev P j).k (JC.parLev P j).r (p.T.bs j).z (p.T.bs j).z' (p.T.bs j).π (p.T.bs j).π'),
    KB.CptCoef p.T.base F →
    (∀ e, Top.IsRadOf (JC.parLev P j) (p.T.bs j) (Φ e) (KB.slv p.T F j (by omega) [] h hh.2 e)) →
    ∀ (t : ℂ) (ht : D.IsLocPt (h ++ [(1, t)]) (j + 1)) (e : Wd.Ix (Fin ([] : List C.Letter).length)),
    ∀ y ∈ Q.DomR P.k (P.r - (j + 1)) (p.T.bs (j + 1)).z (p.T.bs (j + 1)).z',
      (P5.act (P5.bTl L (⟨0, by change 0 < P.r - j; omega⟩ : Fin (JC.parLev P j).r) (D.positionted [])) Φ e :
          Q.Fn (JC.parLev P j).k (JC.parLev P j).r (Wq →L[ℂ] Wp))
        (fun l => PBH.consC t y.1 (Fin.cast (by change P.r - j = 1 + (P.r - (j + 1)); omega) l))
          (D.castM (by change 1 + (P.r - (j + 1)) = P.r - j; omega) (ιLev P.k 1 (P.r - (j + 1)) y.2)) =
        ((‖t‖ ^ (2 * (P.r - j) + P.k) : ℝ) : ℂ) •
          Q.resG P.k (P.r - (j + 1)) (Fin.last _)
            (B.JF (p.T.bs (j + 1)) (KB.slv p.T F (j + 1) hj [] (h ++ [(1, t)]) ht.2 e)) y.1 y.2

theorem headPic_nil (hS : KB.SliceStep) : HeadPicNil := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj h hh L Φ hF hΦ t ht e y hy
  have ht0 : t ≠ 0 := (ht.1 (1, t) (List.mem_append_right _ (List.mem_singleton_self _))).2
  have hn : 1 + (P.r - (j + 1)) = P.r - j := by omega

  have hact : P5.act (P5.bTl L (⟨0, by change 0 < P.r - j; omega⟩ : Fin (JC.parLev P j).r) (D.positionted [])) Φ = Φ :=
    Formalism.FourierDecayAlt.P.PBF.polyAction_one₂ Φ
  rw [hact]
  have hread := pic_read (k := P.k) hn (PBH.levTower_bs_z_eq_castV_liftVec p.T j hj) (PBH.levTower_bs_z'_eq_castV_liftVec p.T j hj)
    (Subtype.val (Φ e)) (B.JF (p.T.bs j) (KB.slv p.T F j (by omega) [] h hh.2 e))
    (hΦ e) ht0 y hy
  refine hread.trans ?_
  congr 1
  unfold resG
  congr 1
  have hc : ∀ a, y.1 a ≠ 0 := hy.1
  have hγ := Formalism.FourierDecayAlt.P.PBF.wCell_mul_GV (i := Fin.last _) hc hy.2.1
  have hΩ := Formalism.FourierDecayAlt.P5.Rad.wCell_mem_omPlus (p.T.bs (j + 1)).z_mem (p.T.bs (j + 1)).z'_mem hy.1 hy.2.1 hy.2.2
  have he : e = fun a => a.elim0 := funext fun a => a.elim0
  subst he
  exact (hS Wp Wq P p F j hj h t hh ht hF _ hγ hΩ).symm

end Formalism.FourierDecayAlt.P.PBP

namespace Formalism.FourierDecayAlt.P

theorem head_picture_empty_word : PBP.HeadPicNil := PBP.headPic_nil slice_induction_level

end Formalism.FourierDecayAlt.P
end
end

