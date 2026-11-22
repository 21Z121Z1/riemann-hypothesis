import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutDec
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0037
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0295
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyContinuousOn
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormsJointContinuity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0222
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadContinuityAtZeroOfStandard

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutFpmDecay
section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.JCx2

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section poly

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def pvar (g : B.Mat k r) : (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) ⊕ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) → ℂ :=
  Sum.elim (fun x => g x.1 x.2) (fun x => star (g x.1 x.2))

def entL (a b : Fin (2 * r + k + 1)) : B.Mat k r →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun g => g a b, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

def entLc (a b : Fin (2 * r + k + 1)) : B.Mat k r →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun g => star (g a b)
      map_add' := fun g h => by simp [Matrix.add_apply]
      map_smul' := fun c g => by simp [Matrix.smul_apply] }

private theorem deriv_smul_const_at_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (φ : ℝ → ℂ) (T : E) :
    deriv (fun t => φ t • T) 0 = deriv φ 0 • T := by
  by_cases hφ : DifferentiableAt ℝ φ 0
  · exact deriv_smul_const hφ T
  by_cases hT : T = 0
  · simp [hT]
  rw [deriv_zero_of_not_differentiableAt hφ, zero_smul]
  apply deriv_zero_of_not_differentiableAt
  intro hd
  apply hφ

  obtain ⟨ℓ, -, hℓ⟩ := exists_dual_vector ℂ T (norm_ne_zero_iff.2 hT)
  have hℓT : ℓ T ≠ 0 := by
    rw [hℓ]
    exact Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hT)
  have h2 : DifferentiableAt ℝ (fun t => ℓ (φ t • T) / ℓ T) 0 :=
    ((ℓ.restrictScalars ℝ).differentiableAt.comp (0 : ℝ) hd).div_const _
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  show φ t = ℓ (φ t • T) / ℓ T
  rw [map_smul, smul_eq_mul, mul_div_cancel_right₀ _ hℓT]

private theorem dLR_smul_const_right {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (φ : B.Mat k r → ℂ) (T : E)
    (u v : List (B.Mat k r)) : B.dLR u v (fun g => φ g • T) = fun g => B.dLR u v φ g • T := by
  have hR : ∀ v : List (B.Mat k r), B.Rw v (fun g => φ g • T) = fun g => B.Rw v φ g • T := by
    intro v
    induction v with
    | nil => rfl
    | cons X v ih =>
      funext g
      show Formalism.REAL.RdV X (B.Rw v fun g => φ g • T) g = Formalism.REAL.RdV X (B.Rw v φ) g • T
      rw [ih]
      exact deriv_smul_const_at_zero _ T
  unfold B.dLR
  rw [hR v]
  induction u with
  | nil => rfl
  | cons X u ih =>
    funext g
    show B.LdV X (u.foldr B.LdV fun g => B.Rw v φ g • T) g = B.LdV X (u.foldr B.LdV (B.Rw v φ)) g • T
    rw [ih]
    exact deriv_smul_const_at_zero _ T

private theorem ckOn_of_contDiff_infty {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : B.Mat k r → E)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (m : ℕ∞) (UU : Set (B.Mat k r)) : B.CkOn m UU f :=
  fun _ _ => ⟨Set.univ, f, isOpen_univ, Set.mem_univ _,
    (hf.of_le (WithTop.coe_le_coe.2 le_top)).contDiffOn, fun _ _ _ => rfl⟩

private theorem pdGood_of_isPolyDeg {κ : ℕ} {c : B.Mat k r → ℂ} (hc : U.IsPolyDeg κ c) : pdGood Wp Wq κ c := by
  obtain ⟨hcd, hwb⟩ := PI.UnitaryCorollaryDerivatives.polynomial_bound k r κ c hc
  refine ⟨fun F hF => ?_, fun A m => ?_⟩
  · intro g₀ hg₀
    obtain ⟨U, f', hU, hgU, hf', hfe⟩ := hF g₀ hg₀
    refine ⟨U, fun g => c g • f' g, hU, hgU, hcd.contDiffOn.smul hf', fun g hg hgv => ?_⟩
    simp only [hfe g hg hgv]
  · obtain ⟨C, hC⟩ := hwb m
    refine ⟨2 ^ m * |C|, by positivity, fun F b hF => ?_⟩
    have hab : ∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ v, B.unitLie k r X) →
        u.length + v.length ≤ m → ∀ g ∈ B.GV k r, g ∉ (∅ : Set (B.Mat k r)) →
          ‖B.dLR u v (fun g => c g • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) g‖ ≤ C * B.gN g ^ (κ : ℝ) := by
      intro u v hu hv hl g hg _
      have h1 := hC u v hu hv hl g hg
      simp only [List.map_append, List.sum_append] at h1
      simp only [dLR_smul_const_right, norm_smul]
      have h1' : ‖B.dLR u v c g‖ ≤ C * B.gN g ^ (κ : ℝ) := by simpa using h1
      calc ‖B.dLR u v c g‖ * ‖ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)‖ ≤ ‖B.dLR u v c g‖ * 1 :=
            mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _)
        _ ≤ C * B.gN g ^ (κ : ℝ) := by rw [mul_one]; exact h1'
    obtain ⟨hP1, hP2⟩ := Formalism.FourierDecayAlt.P.BetaSesquilinearity.prodBound (O := ∅) (UU := B.GV k r)
      (a := fun g => c g • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) isOpen_empty (fun g hg => Or.inr hg)
      (ckOn_of_contDiff_infty _ (hcd.smul contDiff_const) _ _) hab hF (fun g _ h => by simp at h)
    have hfun : Formalism.FourierDecayAlt.P.BetaSesquilinearity.ap (fun g => c g • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) F =
        fun g => c g • F g := by
      funext g
      simp [Formalism.FourierDecayAlt.P.BetaSesquilinearity.ap]
    rw [hfun] at hP1 hP2
    refine ⟨hP1, fun u v hu hv hl g hg => ?_⟩
    have hb0 : 0 ≤ b := le_trans
      (mul_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg _) _) (norm_nonneg _))
      (hF.2 [] [] (by simp) (by simp) (by simp) g hg)
    calc _ ≤ 2 ^ m * (|C| * |b|) := hP2 u v hu hv hl g hg
      _ = 2 ^ m * |C| * b := by rw [abs_of_nonneg hb0]; ring

theorem pd_good_pow {d : ℕ} {c : B.Mat k r → ℂ} (hc : pdGood Wp Wq d c) :
    ∀ e : ℕ, pdGood Wp Wq (d * e) (fun g => c g ^ e)
  | 0 => pd_good_congr (fun g _ => by simp) (pd_good_const (Wp := Wp) (Wq := Wq) (d * 0) (1 : ℂ))
  | e + 1 => pd_good_congr (fun g _ => (pow_succ (c g) e).symm)
      (pd_good_mul (by rw [Nat.mul_succ]) (pd_good_pow hc e) hc)

theorem pd_good_of_poly {κ : ℕ} {c : B.Mat k r → ℂ} (hc : U.IsPolyDeg κ c) : pdGood Wp Wq κ c :=
  pdGood_of_isPolyDeg hc

end poly

section decay

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem pd_good_Gpow (z z' : Fin (2 * r + k + 1) → ℂ) (q : ℕ) :
    pdGood Wp Wq ((2 * r + 2) * q) (fun g : B.Mat k r => ((Gf k r z z' g ^ q : ℝ) : ℂ)) := by
  have := pd_good_pow (Wp := Wp) (Wq := Wq) (pd_good_of_poly (Formalism.FourierDecayAlt.P.gram_function_polynomial k r z z')) q
  simpa only [Complex.ofReal_pow] using this

theorem inCC_Gpow_smul (z z' : Fin (2 * r + k + 1) → ℂ) (q : ℕ) {A₀ : ℝ} {f : B.Mat k r → (Wq →L[ℂ] Wp)}
    (hf : ∀ m : ℕ, B.InCC A₀ m f) :
    ∀ m : ℕ, B.InCC (A₀ - (((2 * r + 2) * q : ℕ) : ℝ)) m (fun g => ((Gf k r z z' g ^ q : ℝ) : ℂ) • f g) := by
  intro m
  obtain ⟨c, hc⟩ := hf m
  obtain ⟨K, -, hb⟩ := (pd_good_Gpow (Wp := Wp) (Wq := Wq) z z' q).2 (A₀ - (((2 * r + 2) * q : ℕ) : ℝ)) m
  exact ⟨K * c, hb f c (by rwa [sub_add_cancel])⟩

theorem ckOn_Gpow_smul (z z' : Fin (2 * r + k + 1) → ℂ) (q : ℕ) {f : B.Mat k r → (Wq →L[ℂ] Wp)}
    (hf : B.CkOn ⊤ (B.GV k r) f) : B.CkOn ⊤ (B.GV k r) (fun g => ((Gf k r z z' g ^ q : ℝ) : ℂ) • f g) :=
  (pd_good_Gpow (Wp := Wp) (Wq := Wq) z z' q).1 f hf

end decay

section fpm

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem fpm_id (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (p₀ : ℕ) :
    TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀ =
      fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • f g := by
  funext g
  simp only [TBBx4.fpm, ContinuousLinearMap.comp_id]

theorem inCC_fpm_id (p : KB.Pl P Wp Wq) {f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (p₀ : ℕ) {A₀ : ℝ}
    (hf : ∀ m : ℕ, B.InCC A₀ m f) :
    ∀ m : ℕ, B.InCC (A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ)) m
      (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) := by
  rw [fpm_id]
  exact inCC_Gpow_smul _ _ p₀ hf

end fpm

end

end Formalism.FourierDecayAlt.P.CutBP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermLow
section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

def GLGram : Prop :=
  P5.ThmPActual → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (N : ℕ) (Cb : ℝ),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base F → (∀ y, 0 < nn y) →
    ∀ i, i ≤ P.r → ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N →
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H) (Vec : C.LPt → H),
      ∀ a b, TBB.NP p nn F i w a b = ⟪Vec a, Vec b⟫_ℂ

def GLFibre : Prop :=
  P5.ThmPActual → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (N : ℕ) (Cb : ℝ),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base F → (∀ y, 0 < nn y) →
    ∀ j, j + 1 ≤ P.r → ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → ∀ a b : C.LPt, D.IsLocPt a j → D.IsLocPt b j →
      Integrable (fun c : ℂ => TBB.NP p nn F (j + 1) w (a ++ [(1, c)]) (b ++ [(1, c)])) ∧
      ∫ c : ℂ, TBB.NP p nn F (j + 1) w (a ++ [(1, c)]) (b ++ [(1, c)]) = TBB.NP p nn F j w a b

def GLCont : Prop :=
  P5.ThmPActual → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (N : ℕ) (Cb : ℝ),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base F → (∀ y, 0 < nn y) →
    ∀ j m, 1 ≤ m → j + m ≤ P.r → ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → ∀ a : C.LPt, D.IsLocPt a j →
      ContinuousOn (fun cc : ℂ × ℂ => TBB.NP p nn F (j + m) w (a ++ [(m, cc.1)]) (a ++ [(m, cc.2)]))
        ({0}ᶜ ×ˢ {0}ᶜ)

def GLGerm : Prop :=
  P5.ThmPActual → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (N : ℕ) (Cb : ℝ),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base F → (∀ y, 0 < nn y) →
    ∀ b s : ℕ, 1 ≤ b → 2 ≤ s → b + s - 1 ≤ P.r → ∀ h : C.LPt, D.IsLocPt h (b - 1) →
    ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (Vec : C.LPt → H),
      (∀ a a', TBB.NP p nn F (b + s - 1) w a a' = ⟪Vec a, Vec a'⟫_ℂ) →
      ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K → ∃ C : ℝ, ∀ x : ℂ, x ≠ 0 → ∀ D ∈ K,
        ‖((((Real.pi ^ (s - 1))⁻¹ * ‖x‖ ^ (s - 1) : ℝ) : ℂ) • Vec (h ++ [(s - 1, x⁻¹), (1, x ^ (s - 1) * D)])) -
          ∑ z ∈ G.rootSet s ((-1) ^ (s + 1) * D),
            G.psi (-U.betaU) ((s : ℂ) * z * x) • (((((s : ℝ) * ‖z‖ ^ (s - 1))⁻¹ : ℝ) : ℂ) • Vec (h ++ [(s, z)]))‖ ≤
          C * ‖x‖⁻¹

end

end Formalism.FourierDecayAlt.P.CutBP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermTop
section
namespace Formalism.FourierDecayAlt.P.CutBP.GT

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def omT (p : KB.Pl P Wp Wq) (N : ℕ) (Q : C.LPt) : ℝ :=
  √(TBB.nPt P.k P.r (TBB.TTp p) Q) * √(Top.wPt (TBB.TTp p) P.r Q ^ N)

end place

def ptT (s : ℕ) (h : C.LPt) (x D : ℂ) : Option ℂ → C.LPt
  | none => h ++ [(s - 1, x⁻¹), (1, x ^ (s - 1) * D)]
  | some u => h ++ [(s, u)]

def coT (s : ℕ) (x : ℂ) : Option ℂ → ℂ
  | none => ((‖x‖ ^ (s - 1) : ℝ) : ℂ)
  | some u => -(G.psi U.betaU ((s : ℂ) * u * x) * ((Real.pi ^ (s - 1) * ((s : ℝ) * ‖u‖ ^ (s - 1))⁻¹ : ℝ) : ℂ))

def epsT (s : ℕ) : ℂ := (-1) ^ (s + 1)

def TopGram1 : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (Cb : ℝ),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base F → KB.CutWord P p.l0 w → (∀ y, 0 < nn y) →
    ∃ (I : Type) (_ : Fintype I) (c : I → ℝ) (Fi : I → B.Mat P.k P.r → (Wq →L[ℂ] Wp))
      (L : I → (Wq →L[ℂ] Wp) →L[ℂ] PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp)),
      (∀ i, 0 ≤ c i) ∧ (∀ i, KB.CptCoef p.T.base (Fi i)) ∧
      ∀ Q Q' : C.LPt, TBB.NP p nn F (P.r + 1) w Q Q' =
        ∑ i, (c i : ℂ) * ⟪(omT p w.length Q' : ℂ) • L i (p.V (Fi i) Q'),
          (omT p w.length Q : ℂ) • L i (p.V (Fi i) Q)⟫_ℂ

def TopCore1 : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (F' : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), KB.CptCoef p.T.base F' →
    ∀ (N b s : ℕ), 1 ≤ b → 2 ≤ s → b + s = P.r + 2 → ∀ h : C.LPt, D.IsLocPt h (b - 1) →
    ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K → ∃ C : ℝ, ∀ x : ℂ, x ≠ 0 → ∀ D ∈ K,
      ‖∑ j ∈ Finset.insertNone (G.rootSet s (epsT s * D)), (coT s x j * (omT p N (ptT s h x D j) : ℂ)) •
          p.V F' (ptT s h x D j)‖ ≤ C * ‖x‖⁻¹

def FibreTop : Prop :=
  P5.ThmPActual → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (Cb : ℝ),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base F → KB.CutWord P p.l0 w →
    ∀ a a' : C.LPt, D.IsLocPt a P.r → D.IsLocPt a' P.r →
      Integrable (fun c : ℂ => TBB.NP p nn F (P.r + 1) w (a ++ [(1, c)]) (a ++ [(1, c)])) ∧
      TBB.NP p nn F P.r w a a' = ∫ c : ℂ, TBB.NP p nn F (P.r + 1) w (a ++ [(1, c)]) (a' ++ [(1, c)])

def YCont : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (F' : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), KB.CptCoef p.T.base F' →
    ∀ (N m : ℕ) (h : C.LPt), (∀ q ∈ h, 1 ≤ q.1 ∧ q.2 ≠ 0) → 1 ≤ m → D.ptSize h + m = P.r + 1 →
      ContinuousOn (fun c : ℂ => (omT p N (h ++ [(m, c)]) : ℂ) • p.V F' (h ++ [(m, c)])) {0}ᶜ

end

end Formalism.FourierDecayAlt.P.CutBP.GT
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimTop
section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology

noncomputable section

theorem limTopN_of_decay : ∃ c₃ : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A b₀ : ℝ),
    c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤ A →
    B.CCle A 0 G b₀ → B.CkOn ⊤ (B.GV P.k P.r) G → LimTopN p nn G := by
  obtain ⟨c₃, hc₃⟩ := Formalism.FourierDecayAlt.P.PBE.vecV_cut_empty
  refine ⟨c₃, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p nn G A b₀ hA hG hGk γ hγ

  have hcut : ∀ (n : ℕ) (g : B.Mat P.k P.r),
      cutN P.k P.r n g = 1 - Formalism.FourierDecayAlt.P.JCx2.pdPsi ((n : ℝ) + 1) g := by
    intro n g
    rw [Formalism.FourierDecayAlt.P.JCx2.pdPsi, sub_sub_cancel]
    rfl
  have hv := hc₃ P.k P.r Wp Wq p.T.base p.ν' p.m₀ γ G A b₀ (fun n g => cutN P.k P.r n g) hA hG hGk hcut

  have key : ∃ K : ℂ, ∀ F : B.Mat P.k P.r → (Wq →L[ℂ] Wp), TBB.Ew p nn F (P.r + 1) [] γ =
      (K * B.hsInner (D.vecV p.T.base p.ν' p.m₀ F γ) (D.vecV p.T.base p.ν' p.m₀ F γ)).re := by
    refine ⟨?_, fun F => ?_⟩
    swap
    unfold TBB.Ew TBB.NP KB.Pl.RR D.RRplace
    rw [dif_pos ⟨hγ, hγ⟩, dif_neg (show ¬ (P.r + 1 ≤ P.r) by omega), if_pos rfl, if_pos rfl]
  obtain ⟨K, hK⟩ := key
  simp only [hK]
  have hs : Continuous (fun V : Wq →L[ℂ] Wp => B.hsVec V) := by
    unfold B.hsVec
    fun_prop
  have hcont : Continuous (fun V : Wq →L[ℂ] Wp => (K * B.hsInner V V).re) := by
    unfold B.hsInner
    exact Complex.continuous_re.comp (continuous_const.mul (hs.inner hs))
  exact (hcont.tendsto _).comp hv

theorem limTopN_cut_of_inCC : ∃ c₃ : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (p : KB.Pl P Wp Wq) (nn χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ),
    c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤ A₀ → C6.IsCut0 χ →
    (∀ m : ℕ, B.InCC A₀ m F) → B.CkOn ⊤ (B.GV P.k P.r) F →
    ∀ ε : ℝ, 0 < ε → LimTopN p nn (D.cutF p.T.base χ F ε) := by
  obtain ⟨c₃, hc₃⟩ := limTopN_of_decay
  refine ⟨c₃, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p nn χ F A₀ hA hχ hF hFk ε hε
  obtain ⟨b₀, hb₀⟩ := Formalism.FourierDecayAlt.P.PBE.cutF_inCC p.T.base hχ hF hε A₀ 0 (by simp)
  exact hc₃ Wp Wq P p nn (D.cutF p.T.base χ F ε) A₀ b₀ hA hb₀
    (Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF p.T.base hχ hFk ε)

end

end Formalism.FourierDecayAlt.P.CutBP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.GermContinuity
section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate ENNReal

noncomputable section

def RRBelowCpt : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), KB.CptCoef p.T.base F →
    ∀ (i : ℕ), i ≤ P.r → ∀ (w : List C.Letter), KB.CutWord P p.l0 w → ∀ (h h' : C.LPt) (m : ℕ), 1 ≤ m →
      D.ptSize h + m = i → D.ptSize h' + m = i →
      ContinuousOn (fun cc : ℂ × ℂ => p.RR F i w (h ++ [(m, cc.1)]) (h' ++ [(m, cc.2)]))
        (({0}ᶜ : Set ℂ) ×ˢ ({0}ᶜ : Set ℂ))

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem nPt_app_cont (TT : ℝ) (h : C.LPt) (s : ℕ) :
    ContinuousOn (fun z : ℂ => TBB.nPt P.k P.r TT (h ++ [(s, z)])) {0}ᶜ := by
  have h1 := Formalism.FourierDecayAlt.P.LastBlockContinuity.continuousOn_weight_product P.k P.r (fun _ _ => 1) (fun _ _ => one_pos) s h 1
  have hmap : Set.MapsTo (fun z : ℂ => ((Complex.normSq z - TT : ℝ), z)) {0}ᶜ (Set.univ ×ˢ {0}ᶜ) :=
    fun z hz => ⟨Set.mem_univ _, hz⟩
  have h2 := h1.comp (Continuous.continuousOn (by fun_prop)) hmap
  refine h2.congr fun z _ => ?_
  simp only [Function.comp, TBB.nPt]
  congr 1
  simp [D.ptGG, D.ptLast]

theorem diag_cont {f : ℂ × ℂ → ℂ} (hf : ContinuousOn f (({0}ᶜ : Set ℂ) ×ˢ ({0}ᶜ : Set ℂ))) :
    ContinuousOn (fun z : ℂ => f (z, z)) {0}ᶜ :=
  hf.comp (Continuous.continuousOn (by fun_prop)) fun _ hz => ⟨hz, hz⟩

theorem ew_cont_of_rr (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (i : ℕ)
    (w : List C.Letter) (h : C.LPt) (s : ℕ)
    (hRR : ContinuousOn (fun cc : ℂ × ℂ => p.RR F i w (h ++ [(s, cc.1)]) (h ++ [(s, cc.2)]))
      (({0}ᶜ : Set ℂ) ×ˢ ({0}ᶜ : Set ℂ))) :
    ContinuousOn (fun z : ℂ => TBB.Ew p nn F i w (h ++ [(s, z)])) {0}ᶜ := by
  have hn := nPt_app_cont (P := P) (TBB.TTp p) h s
  have hw : ContinuousOn (fun z : ℂ => ((Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(s, z)])) *
      Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(s, z)])) / TBB.normC nn w : ℝ) : ℂ)) {0}ᶜ :=
    Complex.continuous_ofReal.comp_continuousOn
      (((Real.continuous_sqrt.comp_continuousOn hn).mul (Real.continuous_sqrt.comp_continuousOn hn)).div_const _)
  have hr := diag_cont hRR
  exact Complex.continuous_re.comp_continuousOn (hw.mul hr)

end place

theorem germContAll_of (hR : RRBelowCpt) : GermContAll := by
  intro Wp Wq _ _ _ _ _ _ P p nn F Y K N Cb hCb hF _ b s hb hs hbs h hh w hw _
  have hsz : D.ptSize h + s = b + s - 1 := by rw [hh.2]; omega
  refine ew_cont_of_rr p nn F (b + s - 1) w h s ?_
  rcases Nat.lt_or_ge (b + s - 1) (P.r + 1) with hlt | hge
  · exact hR Wp Wq P p F hF (b + s - 1) (by omega) w hw.1 h h s (by omega) hsz hsz
  · have he : b + s - 1 = P.r + 1 := by omega
    rw [he] at hsz ⊢
    exact Formalism.FourierDecayAlt.P.LastBlockContinuity.rrTop_cont P p F hF Cb hCb w hw.1 h h s (by omega) hsz hsz

end

end Formalism.FourierDecayAlt.P.CutBP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LimZeroNPf
section
open Filter Topology

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt

noncomputable section

theorem limZeroN_of_formLimit (Cb : ℝ) : ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (ε A : ℝ) (N : ℕ) (nn : ℝ → ℝ) (Y : Finset ℝ),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → 0 < ε → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A m f) →
    Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A →
    LimZeroN p nn (D.cutF p.T.base χ f ε) Y N := by
  obtain ⟨Cc, hCc⟩ := Formalism.FourierDecayAlt.P.limit_of_module_forms Cb
  refine ⟨Cc, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f χ ε A N nn Y hDD hχ hε hf hfA hA
  have hFL := (hCc Wp Wq P p f χ ε A N (cutN P.k P.r) hDD hχ hε hf hfA hA (fun _ _ => rfl)).2
  intro w hw hN
  have hT := hFL 0 w hw.1 hN [] []
  have hre := (Complex.continuous_re.tendsto _).comp hT
  have e1 : ∀ n : ℕ, TBB.Ew p nn (apx (D.cutF p.T.base χ f ε) n) 0 w [] =
      (p.RR (fun g => cutN P.k P.r n g • D.cutF p.T.base χ f ε g) 0 w [] []).re / TBB.normC nn w :=
    fun n => Formalism.FourierDecayAlt.P.TBBx3.ew_zero_nil p nn _ w
  have e2 : TBB.Ew p nn (D.cutF p.T.base χ f ε) 0 w [] =
      (p.RR (D.cutF p.T.base χ f ε) 0 w [] []).re / TBB.normC nn w :=
    Formalism.FourierDecayAlt.P.TBBx3.ew_zero_nil p nn _ w
  simp only [e1, e2]
  exact hre.div_const _

end

end Formalism.FourierDecayAlt.P.CutBP
end

