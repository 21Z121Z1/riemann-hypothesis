import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0265
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0268
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0244
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChartCoefficientHasCompactSupport
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0264
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0267
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0246
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0090

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHLPlusZeroOfParts
section
open Matrix
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutHLPZ

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates Formalism.FourierDecayAlt.P.CutHL

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem dmin_zero (z z' : Fin (2 * r + k + 1) → ℂ) (g : Q.Mx k r) (h : 0 < r + 2) :
    Dmin k r z z' g ⟨0, h⟩ = 1 := by
  unfold Dmin
  exact Matrix.det_isEmpty

theorem qminorOp_zero (a b : Fin 0 → Fin (2 * r + k + 1)) (u : ℂ) (f : Q.Mx k r → E) (g : Q.Mx k r) :
    qminorOp (EabH (Hpk k r)) a b u f g = f g := by
  unfold qminorOp
  rw [Finset.sum_apply, Fintype.sum_unique]
  simp

theorem AAop_zero (h : 0 ≤ r) (u : ℂ) (f : Q.Mx k r → E) (g : Q.Mx k r) : C3.AAop k r 0 h u f g = f g := by
  unfold C3.AAop
  rw [Fintype.sum_unique, if_pos (Subsingleton.strictMono _), Matrix.det_isEmpty, one_smul, qminorOp_zero]

theorem qminorOp_one (a b : Fin 1 → Fin (2 * r + k + 1)) (u : ℂ) (f : Q.Mx k r → E) (g : Q.Mx k r) :
    qminorOp (EabH (Hpk k r)) a b u f g =
      (if a 0 = b 0 then u • f g else 0) + EabH (Hpk k r) (a 0) (b 0) f g := by
  unfold qminorOp
  rw [Finset.sum_apply, Fintype.sum_unique]
  simp [QuantumDeterminants.Top]

theorem AAop_one (h : 1 ≤ r) (x : Q.Mx k r) (τ : ℂ)
    (hnf : ∀ p : Fin (2 * r + k + 1), PBG.xi0 x ⟨0, by omega⟩ p = if p.val = 0 then τ else 0)
    (u : ℂ) (f : Q.Mx k r → E) :
    C3.AAop k r 1 h u f x = τ • (u • f x + Q.EH k r (eI k r ⟨0, by omega⟩) (eI k r ⟨0, by omega⟩) f x) := by
  classical
  unfold C3.AAop
  have hent : ∀ c : Fin 1 → Fin (2 * r + k + 1),
      (Matrix.of fun a l : Fin 1 =>
        herm (Hpk k r) (x *ᵥ bvec (c l)) (bvec (eI k r (Fin.castLE h a)))).det =
        if (c 0).val = 0 then τ else 0 := by
    intro c
    rw [Matrix.det_unique]
    exact hnf (c 0)
  rw [Finset.sum_eq_single (fun _ => eI k r ⟨0, by omega⟩)]
  · rw [if_pos (Subsingleton.strictMono _), hent, if_pos (by simp [eI]),
      qminorOp_one, if_pos (by simp [C3.xR, eI])]
    simp [C3.xR, eI, Q.EH]
  · intro c _ hc
    split_ifs with hm
    · rw [hent, if_neg, zero_smul]
      intro h0
      apply hc
      funext l
      rw [Subsingleton.elim l 0]
      ext
      simpa [eI] using h0
    · rfl
  · intro hc; exact absurd (Finset.mem_univ _) hc

end Formalism.FourierDecayAlt.P.CutHLPZ

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates Formalism.FourierDecayAlt.P.CutHL Formalism.FourierDecayAlt.P.CutHLPZ

theorem plus_zero_of_parts : CutHL.PlusZeroOfParts := by
  intro hNf hDm hT k r j hj z z' E _ _ Dm Φ Z γ τ hj0 hH Y
  subst hj0
  obtain ⟨_, _, hDo, _, hR, hZ, hτ, hγ, hx⟩ := hH
  have hnf := (hNf k r 0 hj Z τ γ hZ hτ hγ).1
  have hT' := hT E k r 0 hj Dm Φ Z τ γ hDo hR.1 hZ hτ hγ hx
  have hD1 := (hDm k r 0 hj z z' Z τ γ hZ hτ hγ).2
  rw [Matrix.det_isEmpty, one_mul] at hD1
  have hv0 : ∀ g, D.vLet k r z z' 0 (by omega) (true, Y) 0 Φ g = Φ g := by
    intro g
    rw [PBG.letter_plus_component_zero, dmin_zero, inv_one, one_smul, AAop_zero]
  have hv1 : ∀ g, D.vLet k r z z' 0 (by omega) (true, Y) 1 Φ g = 0 := by
    intro g
    unfold D.vLet
    simp
  have hA := AAop_one (k := k) (r := r) (E := E) hj (x0 k r 0 hj Z τ γ) τ (fun p => by
      rw [hnf ⟨0, by omega⟩ p (by simp)]
      by_cases hp : p.val = 0
      · rw [if_pos (by omega), if_pos hp, hp]; simp [C3.Zb]
      · rw [if_neg (by omega), if_neg hp])
    ((Y : ℂ) + ((2 * r + k : ℕ) : ℂ) / 2) Φ
  have hu : ((Y : ℂ) + ((2 * r + k : ℕ) : ℂ) / 2) = (Y : ℂ) + levelZeroKernel k r 0 := by
    unfold levelZeroKernel; rw [Nat.sub_zero]; push_cast; ring
  rw [hu] at hA
  unfold Eq1
  simp only [hv0, hv1]
  rw [PBG.letter_plus_component_zero, hD1, hu, hA, ← hT', smul_smul, inv_mul_cancel₀ hτ, one_smul, smul_zero, sub_zero]

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRPHRotRadSp
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q NumberField
open scoped ComplexConjugate Matrix ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.PH

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.TwoByOneBlock

variable {k r : ℕ}

theorem star_exp_mul (θ : ℝ) :
    star (Complex.exp ((θ : ℂ) * Complex.I)) * Complex.exp ((θ : ℂ) * Complex.I) = 1 := by
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
  norm_num

theorem cW_mem_UWb (θ : ℝ) : cW k r θ ∈ UWb k r := by
  refine emb_mem_UWb ?_
  show (Complex.exp ((θ : ℂ) * Complex.I) • (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ))ᴴ * Hb k *
    (Complex.exp ((θ : ℂ) * Complex.I) • (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)) = Hb k
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, smul_mul_assoc, one_mul, mul_smul_comm, mul_one, smul_smul,
    mul_comm, star_exp_mul, one_smul]

theorem cW_comm (θ : ℝ) {h : Q.Mx k r} (hh : h ∈ UWb k r) : cW k r θ * h = h * cW k r θ := by
  obtain ⟨μ, _, rfl⟩ := (UWb_iff h).1 hh
  unfold cW
  rw [← emb_mul, ← emb_mul, smul_mul_assoc, one_mul, mul_smul_comm, mul_one]

theorem cW_Glev (θ : ℝ) {g : Q.Mx k r} (hg : g ∈ Q.Glev k r (Fin.last r)) : cW k r θ * g ∈ Q.Glev k r (Fin.last r) := by
  obtain ⟨hc, hfix⟩ := cW_mem_UWb (k := k) (r := r) θ
  refine ⟨UH_mul hc hg.1, fun a ha => ⟨?_, ?_⟩⟩
  · rw [← Matrix.mulVec_mulVec, (hg.2 a ha).1, (hfix a).1]
  · rw [← Matrix.mulVec_mulVec, (hg.2 a ha).2, (hfix a).2]

theorem herm_cW (θ : ℝ) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (v : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (cW k r θ *ᵥ v) z = Complex.exp ((θ : ℂ) * Complex.I) * herm (Hpk k r) v z := by
  have h1 : cW k r θ *ᵥ (Complex.exp (-((θ : ℂ) * Complex.I)) • z) = z := by
    rw [Matrix.mulVec_smul, cW_mulVec _ hz, smul_smul, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_smul]
  have h2 : star (Complex.exp (-((θ : ℂ) * Complex.I))) = Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [Complex.star_def, ← Complex.exp_conj]
    congr 1
    simp
  calc herm (Hpk k r) (cW k r θ *ᵥ v) z
      = herm (Hpk k r) (cW k r θ *ᵥ v) (cW k r θ *ᵥ (Complex.exp (-((θ : ℂ) * Complex.I)) • z)) := by rw [h1]
    _ = _ := by rw [herm_UH (cW_mem_UWb θ).1, herm_smul_right, h2]

theorem GGl_cW (θ : ℝ) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (z' : Fin (2 * r + k + 1) → ℂ) (g : Q.Mx k r) :
    Q.GGl k r z z' (cW k r θ * g) = Q.GGl k r z z' g := by
  unfold Q.GGl Q.zetaL
  rw [fvec_last, fvec_last, ← Matrix.mulVec_mulVec, herm_cW θ hz, map_mul, Complex.normSq_eq_norm_sq,
    Complex.norm_exp_ofReal_mul_I]
  norm_num

theorem domR_cW (θ : ℝ) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (z' : Fin (2 * r + k + 1) → ℂ)
    {x : (Fin r → ℂ) × Q.Mx k r} (hx : x ∈ Q.DomR k r z z') : (x.1, cW k r θ * x.2) ∈ Q.DomR k r z z' :=
  ⟨hx.1, cW_Glev θ hx.2.1, by
    show 0 < Q.GGl k r z z' (cW k r θ * x.2)
    rw [GGl_cW θ hz]
    exact hx.2.2⟩

theorem domR_of_cW (θ : ℝ) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (z' : Fin (2 * r + k + 1) → ℂ)
    {x : (Fin r → ℂ) × Q.Mx k r} (hx : (x.1, cW k r θ * x.2) ∈ Q.DomR k r z z') : x ∈ Q.DomR k r z z' := by
  have h := domR_cW (-θ) hz z' hx
  have e : cW k r (-θ) * (cW k r θ * x.2) = x.2 := by
    rw [← Matrix.mul_assoc, cW_mul, neg_add_cancel, cW_zero, one_mul]
  change (x.1, cW k r (-θ) * (cW k r θ * x.2)) ∈ Q.DomR k r z z' at h
  rwa [e] at h

theorem rotation_radial_space_holds : RotRadSp := by
  intro Wp Wq _ _ _ _ k r z z' π π' hz hz' θ Φ hΦ
  obtain ⟨h0, hs, he⟩ := hΦ
  refine ⟨fun x hx => h0 (x.1, cW k r θ * x.2) (fun h => hx (domR_of_cW θ hz z' h)), fun x₀ hx₀ => ?_,
    fun x hx h hh h' hh' => ?_⟩
  · obtain ⟨U, F, hU, hxU, hF, hΦF⟩ := hs (x₀.1, cW k r θ * x₀.2) (domR_cW θ hz z' hx₀)
    have hL : ContDiff ℝ ∞ (fun x : (Fin r → ℂ) × Q.Mx k r => (x.1, cW k r θ * x.2)) :=
      contDiff_fst.prodMk (((LinearMap.mulLeft ℝ (cW k r θ)).toContinuousLinearMap.contDiff).comp contDiff_snd)
    exact ⟨(fun x : (Fin r → ℂ) × Q.Mx k r => (x.1, cW k r θ * x.2)) ⁻¹' U,
      F ∘ (fun x : (Fin r → ℂ) × Q.Mx k r => (x.1, cW k r θ * x.2)), hU.preimage hL.continuous, hxU,
      hF.comp hL.contDiffOn (fun x hx => hx), fun x hx hg => hΦF (x.1, cW k r θ * x.2) hx (cW_Glev θ hg)⟩
  · show Φ x.1 (cW k r θ * (h * x.2 * h')) = _
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, cW_comm θ ⟨hh.1, hh.2.1⟩, Matrix.mul_assoc h]
    exact he (x.1, cW k r θ * x.2) (domR_cW θ hz z' hx) h hh h' hh'

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.PH
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutMK2
section
noncomputable section

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMK

def HB {k p ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (b b' : U.RC k p ρ → ℝ) (β : (Fin p → Fin p → ℂ) → ℝ)
    (Φ : (Fin p → Fin p → ℂ) → Mt k ρ → (Wq →L[ℂ] Wp)) : B.Mat k (p + ρ) → (Wq →L[ℂ] Wp) :=
  PBI.chartCoefficient b b' (fun Z' y' => ((β Z' : ℝ) : ℂ) • Φ Z' y')

def kapL {k p ρ : ℕ} (z : Fin (2 * ρ + k + 1) → ℂ) (b : U.RC k p ρ → ℝ) : ℂ :=
  ∫ x, (b x : ℂ) * psi k (p + ρ) (liftVec k p ρ z) cStd (U.Rn k p ρ x) ∂(U.muRC k p ρ)

def kapR {k p ρ : ℕ} (z' : Fin (2 * ρ + k + 1) → ℂ) (b' : U.RC k p ρ → ℝ) : ℂ :=
  ∫ x, (b' x : ℂ) * star (psi k (p + ρ) (liftVec k p ρ z') cStd (U.Rn k p ρ x)) ∂(U.muRC k p ρ)

def RightAvg : Prop :=
  ∀ (k p ρ : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq], ρ = 0 →
    ∀ (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k (p + ρ) Wp Wq),
    B0.z' = liftVec k p ρ Bj.z' → (∀ y : B.Mat k ρ, Bj.π' y = B0.π' (U.embG k p ρ y)) →
    Bj.μW' Set.univ = 1 → B0.μW' = Bj.μW'.map (Formalism.FourierDecayAlt.P.PBM.levMt p ρ rfl) →
    Bj.μN = D.muN k ρ → B0.μN = D.muN k (p + ρ) →
    ∀ (b b' : U.RC k p ρ → ℝ) (β : (Fin p → Fin p → ℂ) → ℝ) (Φ : (Fin p → Fin p → ℂ) → Mt k ρ → (Wq →L[ℂ] Wp)),
    Continuous b' → HasCompactSupport b' →
    ∀ Z : Fin p → Fin p → ℂ, (Matrix.of Z).det ≠ 0 →
    Integrable (fun v : G.UT p → ℂ => β (Matrix.of.symm (Matrix.of Z * G.upper v))) →
    ∫ v : G.UT p → ℂ, β (Matrix.of.symm (Matrix.of Z * G.upper v)) = 1 →
    ∀ y : Mt k ρ, (Matrix.of y : B.Mat k ρ) ∈ B.GV k ρ →
    (∀ h1 ∈ UWset k ρ Bj.z, ∀ h2 ∈ UWset k ρ Bj.z',
      Φ Z (Matrix.of.symm (h1 * Matrix.of y * h2)) = (Bj.π h1).comp ((Φ Z y).comp (Bj.π' h2))) →
    (∀ (u : G.UT p → ℂ) (y' : Mt k ρ), (Matrix.of y' : B.Mat k ρ) ∈ B.GV k ρ →
      Φ (Matrix.of.symm (Matrix.of Z * G.upper u)) y' =
        psi k (p + ρ) (liftVec k p ρ Bj.z') cStd (U.muP k p ρ (G.upper u)) • Φ Z y') →
    ∀ h ∈ UWset k ρ Bj.z, ∀ a : U.RC k p ρ,
      PBG.Kr B0 (HB b b' β Φ) (U.Rn k p ρ (-a) * U.embG k p ρ h⁻¹ * U.mMap k p ρ (Matrix.of Z) (Matrix.of y)) =
        (((b a : ℝ) : ℂ) * kapR Bj.z' b') • (Bj.π h⁻¹).comp (Φ Z y)

def LeftAvg : Prop :=
  ∀ (k p ρ : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq], ρ = 0 →
    ∀ (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k (p + ρ) Wp Wq),
    Bj.μW Set.univ = 1 → Bj.μN = D.muN k ρ →
    ∀ (H : B.Mat k (p + ρ) → (Wq →L[ℂ] Wp)) (g : B.Mat k (p + ρ)) (b : U.RC k p ρ → ℝ) (c : ℂ)
      (A : Wq →L[ℂ] Wp), Continuous b → HasCompactSupport b →
    (∀ h ∈ UWset k ρ Bj.z, ∀ a : U.RC k p ρ,
      PBG.Kr B0 H (U.Rn k p ρ (-a) * U.embG k p ρ h⁻¹ * g) = (((b a : ℝ) : ℂ) * c) • (Bj.π h⁻¹).comp A) →
    PBQ.pbF Bj B0 rfl H g = (kapL Bj.z b * c) • A

def CoreN : Prop :=
  ∀ (k p ρ n : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (e : p + ρ = n), ρ = 0 →
    ∀ (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq),
    D.castV e (liftVec k p ρ Bj.z') = B0.z' → (∀ y : B.Mat k ρ, Bj.π' y = B0.π' (D.castM e (ιLev k p ρ y))) →
    Bj.μW Set.univ = 1 → Bj.μW' Set.univ = 1 → B0.μW' = Bj.μW'.map (Formalism.FourierDecayAlt.P.PBM.levMt p ρ e) →
    Bj.μN = D.muN k ρ → B0.μN = D.muN k n →
    ∀ (b b' : U.RC k p ρ → ℝ) (β : (Fin p → Fin p → ℂ) → ℝ) (Φ : (Fin p → Fin p → ℂ) → Mt k ρ → (Wq →L[ℂ] Wp)),
    Continuous b → HasCompactSupport b → Continuous b' → HasCompactSupport b' →
    ∀ Z : Fin p → Fin p → ℂ, (Matrix.of Z).det ≠ 0 →
    Integrable (fun v : G.UT p → ℂ => β (Matrix.of.symm (Matrix.of Z * G.upper v))) →
    ∫ v : G.UT p → ℂ, β (Matrix.of.symm (Matrix.of Z * G.upper v)) = 1 →
    ∀ y : Mt k ρ, (Matrix.of y : B.Mat k ρ) ∈ B.GV k ρ →
    (∀ h1 ∈ UWset k ρ Bj.z, ∀ h2 ∈ UWset k ρ Bj.z',
      Φ Z (Matrix.of.symm (h1 * Matrix.of y * h2)) = (Bj.π h1).comp ((Φ Z y).comp (Bj.π' h2))) →
    (∀ (u : G.UT p → ℂ) (y' : Mt k ρ), (Matrix.of y' : B.Mat k ρ) ∈ B.GV k ρ →
      Φ (Matrix.of.symm (Matrix.of Z * G.upper u)) y' =
        psi k (p + ρ) (liftVec k p ρ Bj.z') cStd (U.muP k p ρ (G.upper u)) • Φ Z y') →
    PBQ.pbF Bj B0 e (D.castF e.symm (HB b b' β Φ)) (D.castM e (U.mMap k p ρ (Matrix.of Z) (Matrix.of y))) =
      (kapL Bj.z b * kapR Bj.z' b') • Φ Z y

def TopMk : Prop := CoreN → CutEX.MkTop

section assembly

theorem coreRfl (hR : RightAvg) (hL : LeftAvg) (k p ρ : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
    [FiniteDimensional ℂ Wq] (hρ : ρ = 0) (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k (p + ρ) Wp Wq)
    (hz' : B0.z' = liftVec k p ρ Bj.z') (hπ' : ∀ y : B.Mat k ρ, Bj.π' y = B0.π' (U.embG k p ρ y))
    (hW : Bj.μW Set.univ = 1) (hW' : Bj.μW' Set.univ = 1)
    (hW0' : B0.μW' = Bj.μW'.map (Formalism.FourierDecayAlt.P.PBM.levMt p ρ rfl))
    (hNj : Bj.μN = D.muN k ρ) (hN0 : B0.μN = D.muN k (p + ρ))
    (b b' : U.RC k p ρ → ℝ) (β : (Fin p → Fin p → ℂ) → ℝ) (Φ : (Fin p → Fin p → ℂ) → Mt k ρ → (Wq →L[ℂ] Wp))
    (hb : Continuous b) (hbc : HasCompactSupport b) (hb' : Continuous b') (hbc' : HasCompactSupport b')
    (Z : Fin p → Fin p → ℂ) (hZ : (Matrix.of Z).det ≠ 0)
    (hβi : Integrable (fun v : G.UT p → ℂ => β (Matrix.of.symm (Matrix.of Z * G.upper v))))
    (hβ1 : ∫ v : G.UT p → ℂ, β (Matrix.of.symm (Matrix.of Z * G.upper v)) = 1)
    (y : Mt k ρ) (hy : (Matrix.of y : B.Mat k ρ) ∈ B.GV k ρ)
    (hΦL : ∀ h1 ∈ UWset k ρ Bj.z, ∀ h2 ∈ UWset k ρ Bj.z',
      Φ Z (Matrix.of.symm (h1 * Matrix.of y * h2)) = (Bj.π h1).comp ((Φ Z y).comp (Bj.π' h2)))
    (hΦU : ∀ (u : G.UT p → ℂ) (y' : Mt k ρ), (Matrix.of y' : B.Mat k ρ) ∈ B.GV k ρ →
      Φ (Matrix.of.symm (Matrix.of Z * G.upper u)) y' =
        psi k (p + ρ) (liftVec k p ρ Bj.z') cStd (U.muP k p ρ (G.upper u)) • Φ Z y') :
    PBQ.pbF Bj B0 rfl (HB b b' β Φ) (U.mMap k p ρ (Matrix.of Z) (Matrix.of y)) =
      (kapL Bj.z b * kapR Bj.z' b') • Φ Z y := hL k p ρ Wp Wq hρ Bj B0 hW hNj (HB b b' β Φ) (U.mMap k p ρ (Matrix.of Z) (Matrix.of y)) b
    (kapR Bj.z' b') (Φ Z y) hb hbc
    (fun h hh a => hR k p ρ Wp Wq hρ Bj B0 hz' hπ' hW' hW0' hNj hN0 b b' β Φ hb' hbc' Z hZ hβi hβ1 y hy
      hΦL hΦU h hh a)

private theorem embG_eq_ιLev (k p ρ : ℕ) (g : B.Mat k ρ) : U.embG k p ρ g = ιLev k p ρ g := by
  ext i j
  obtain ⟨x, rfl⟩ := (U.eB k p ρ).surjective i
  obtain ⟨w, rfl⟩ := (U.eB k p ρ).surjective j
  simp only [U.embG, U.blk3, ιLev, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases x with (a | a) | a <;> rcases w with (c | c) | c <;>
    simp [U.eB, Matrix.fromBlocks, Matrix.fromRows, Matrix.fromCols, Matrix.one_apply, Fin.ext_iff,
      Sum.elim] <;> split_ifs <;> (try simp_all [Fin.ext_iff]) <;> (try omega)

theorem coreN_of (hR : RightAvg) (hL : LeftAvg) : CoreN := by
  intro k p ρ n Wp Wq _ _ _ _ _ _ e hρ Bj B0 hz' hπ' hW hW' hW0' hNj hN0 b b' β Φ hb hbc hb' hbc' Z hZ hβi hβ1 y hy
    hΦL hΦU
  subst e
  rw [Formalism.FourierDecayAlt.P.Dx2.Tower.castV_rfl] at hz'
  have hπ'' : ∀ y : B.Mat k ρ, Bj.π' y = B0.π' (U.embG k p ρ y) := fun y => by
    rw [hπ' y, Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl, Formalism.FourierDecayAlt.P.Dx2.Tower.lev_eq_embG]
  have hF : D.castF (rfl : p + ρ = p + ρ).symm (HB b b' β Φ) = HB b b' β Φ := funext fun x => by
    simp only [D.castF, Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]
  rw [hF, Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]
  exact coreRfl hR hL k p ρ Wp Wq hρ Bj B0 hz'.symm hπ'' hW hW' hW0' hNj hN0 b b' β Φ hb hbc hb' hbc' Z hZ hβi hβ1
    y hy hΦL hΦU

theorem mkTop_of_leaves (hR : RightAvg) (hL : LeftAvg) (hT : TopMk) : CutEX.MkTop := hT (coreN_of hR hL)

end assembly

end Formalism.FourierDecayAlt.P.CutMK
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianPartLevi
section
open Matrix
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.WirtingerOperators.LeviExponential

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates

theorem castM_mul' {k a b : ℕ} (h : a = b) (g g' : B.Mat k a) :
    D.castM h (g * g') = D.castM h g * D.castM h g' := by
  simp only [D.castM, Matrix.reindex_apply, Matrix.submatrix_mul_equiv]

theorem exp_castM {k a b : ℕ} (h : a = b) (M : B.Mat k a) :
    NormedSpace.exp (D.castM h M) = D.castM h (NormedSpace.exp M) := by
  unfold D.castM; exact exp_reindex _ M

theorem exp_block_three_diagonal {k j ρ : ℕ} (A : Matrix (Fin j) (Fin j) ℂ) (Bm : B.Mat k ρ) (C : Matrix (Fin j) (Fin j) ℂ) :
    NormedSpace.exp (U.blk3 A 0 0 0 Bm 0 0 0 C) =
      U.blk3 (NormedSpace.exp A) 0 0 0 (NormedSpace.exp Bm) 0 0 0 (NormedSpace.exp C) := by
  unfold U.blk3
  rw [exp_reindex]
  have h1 : Matrix.fromRows (0 : Matrix (Fin j) (Fin j) ℂ) (0 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) = 0 := by
    ext i l; rcases i with i | i <;> rfl
  have h2 : Matrix.fromCols (0 : Matrix (Fin j) (Fin j) ℂ) (0 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) = 0 := by
    ext i l; rcases l with l | l <;> rfl
  rw [h1, h2, exp_fromBlocks, exp_fromBlocks]

theorem exp_block_two_diagonal {p s : ℕ} (A : Matrix (Fin p) (Fin p) ℂ) (Dd : Matrix (Fin s) (Fin s) ℂ) :
    NormedSpace.exp (U.blk2 A 0 0 Dd) = U.blk2 (NormedSpace.exp A) 0 0 (NormedSpace.exp Dd) := by
  unfold U.blk2
  rw [exp_reindex, exp_fromBlocks]

theorem symmetricScalarBlockMatrix_one_zero {p s : ℕ} : U.blk2 (1 : Matrix (Fin p) (Fin p) ℂ) 0 0 (1 : Matrix (Fin s) (Fin s) ℂ) = 1 := by
  simp [U.blk2]

theorem block_two_identity_conjTranspose {p s : ℕ} (A : Matrix (Fin p) (Fin p) ℂ) :
    (U.blk2 A 0 0 (1 : Matrix (Fin s) (Fin s) ℂ))ᴴ = U.blk2 Aᴴ 0 0 1 := by
  ext a b
  simp only [Matrix.conjTranspose_apply, block_two_apply]
  split_ifs <;> simp [Matrix.one_apply, Fin.ext_iff, eq_comm]

theorem w_inv (d : ℕ) : (G.wMat d)⁻¹ = G.wMat d :=
  Matrix.inv_eq_left_inv (Ux4.wMat_mul_self d)

theorem exp_w_conj (d : ℕ) (M : Matrix (Fin d) (Fin d) ℂ) :
    NormedSpace.exp (G.wMat d * M * G.wMat d) = G.wMat d * NormedSpace.exp M * G.wMat d := by
  have hu : IsUnit (G.wMat d) := ⟨⟨G.wMat d, G.wMat d, Ux4.wMat_mul_self d, Ux4.wMat_mul_self d⟩, rfl⟩
  have e := Matrix.exp_conj (G.wMat d) M hu
  rw [w_inv] at e
  exact e

theorem block_two_exp_conjTranspose_inv {j : ℕ} (y : MJ j) :
    (U.blk2 (NormedSpace.exp y) 0 0 (1 : Matrix (Fin 1) (Fin 1) ℂ))ᴴ⁻¹ = U.blk2 (NormedSpace.exp (-yᴴ)) 0 0 1 := by
  rw [block_two_identity_conjTranspose]
  apply Matrix.inv_eq_left_inv
  rw [Ux4.symmetricScalarBlockMatrix_mul]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one]
  have hu : IsUnit (NormedSpace.exp yᴴ).det := (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_exp _)
  rw [Matrix.exp_neg, ← Matrix.exp_conjTranspose, Matrix.nonsing_inv_mul _ hu, symmetricScalarBlockMatrix_one_zero]

theorem exp_levi {k r j : ℕ} (hj : j + 1 ≤ r) (x : MJ j) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • levi k r j x) = D.castM (by omega : j + 1 + (r - (j + 1)) = r)
      (U.muP k (j + 1) (r - (j + 1)) (U.blk2 (NormedSpace.exp ((t : ℂ) • x)) 0 0 1)) := by
  have hs : (t : ℂ) • levi k r j x = levi k r j ((t : ℂ) • x) := by
    ext p q
    simp only [levi, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    split_ifs <;> simp [Complex.conj_ofReal]
  rw [hs, levi_eq hj, exp_castM, exp_block_three_diagonal, exp_w_conj, exp_block_two_diagonal, exp_block_two_diagonal]
  simp only [NormedSpace.exp_zero]
  unfold U.muP
  rw [block_two_exp_conjTranspose_inv]

theorem zfull_mul {j : ℕ} (Z E : MJ j) (τ : ℂ) :
    zfull Z τ * U.blk2 E 0 0 (1 : Matrix (Fin 1) (Fin 1) ℂ) = zfull (Z * E) τ := by
  unfold zfull
  rw [Ux4.symmetricScalarBlockMatrix_mul]
  simp

theorem curveLevi : CurveLevi := by
  intro k r j hj Z τ γ x t
  rw [exp_levi hj]
  unfold x0
  rw [← castM_mul', Ux4.mMap_mul_muP, zfull_mul]

end Formalism.FourierDecayAlt.P.WirtingerOperators.LeviExponential

theorem Formalism.FourierDecayAlt.P.levi_curve : Formalism.FourierDecayAlt.P.WirtingerOperators.CurveLevi := Formalism.FourierDecayAlt.P.WirtingerOperators.LeviExponential.curveLevi

theorem Formalism.FourierDecayAlt.P.hermitian_part_levi : Formalism.FourierDecayAlt.P.WirtingerOperators.HpartLevi := Formalism.FourierDecayAlt.P.WirtingerOperators.LeviExponential.hpartLevi
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.IsOpenDminNe
section
open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.PartialBesselProperness

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

section auxC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k n : ℕ}

theorem isOpen_dminNe (z z' : Fin (2 * n + k + 1) → ℂ) (i : ℕ) (hi : i ≤ n) :
    IsOpen {g : Q.Mx k n | Dmin k n z z' g ⟨i, by omega⟩ ≠ 0} :=
  isOpen_ne_fun (Formalism.FourierDecayAlt.P.JCx1.contDiff_Dmin z z' ⟨i, by omega⟩).continuous continuous_const

theorem uwG_locSupp {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (z z' : Fin (2 * n + k + 1) → ℂ) (i : ℕ)
    (hi : i ≤ n) {H : B.Mat k n → E} {Cs : Set (B.Mat k n)} (hCs : IsClosed Cs)
    (hL : ∀ g ∈ B.GV k n, Dmin k n z z' g ⟨i, by omega⟩ ≠ 0 → CapelliWordSumExpansion.Loc ⊤ H g)
    (hS : ∀ g ∈ B.GV k n, g ∉ Cs → H g = 0) :
    ∀ (w : List C.Letter) (ew : Wd.Ix (Fin w.length)),
      (∀ g ∈ B.GV k n, Dmin k n z z' g ⟨i, by omega⟩ ≠ 0 → CapelliWordSumExpansion.Loc ⊤ (D.uwG k n z z' H i hi w ew) g) ∧
        ∀ g ∈ B.GV k n, g ∉ Cs → D.uwG k n z z' H i hi w ew g = 0 := by
  set Dm : Set (Q.Mx k n) := {g | Dmin k n z z' g ⟨i, by omega⟩ ≠ 0} with hDm
  have hDo : IsOpen Dm := isOpen_dminNe z z' i hi
  have hH : Q.SmoothLev k n 0 Dm H := by
    intro g₀ hg₀
    obtain ⟨U, F, hU, hgU, hF, hE⟩ := hL g₀ hg₀.1.1 hg₀.2
    exact ⟨U, F, hU, hgU, hF, fun g hg hgl => hE g hg hgl.1⟩
  have hSm : ∀ (w : List C.Letter) (ew : Wd.Ix (Fin w.length)),
      Q.SmoothLev k n 0 Dm (D.uwG k n z z' H i hi w ew) := by
    intro w
    induction w with
    | nil => intro ew; exact hH
    | cons l w ih =>
      intro ew
      exact Formalism.FourierDecayAlt.P.SingleEntryHermitianProducts.smooth_vLet z z' i hi l _ hDo (ih _) (fun g hg => hg)
  have hSu : ∀ (w : List C.Letter) (ew : Wd.Ix (Fin w.length)),
      ∀ g ∈ B.GV k n, g ∉ Cs → D.uwG k n z z' H i hi w ew g = 0 := by
    intro w
    induction w with
    | nil => intro ew; exact hS
    | cons l w ih =>
      intro ew g hg hgC
      exact Formalism.FourierDecayAlt.P.PBG.vLet_zero_near z z' i hi l _ _ hCs.isOpen_compl (fun x hx hxG => ih _ x hxG hx) g hgC hg
  intro w ew
  refine ⟨fun g hg hd => ?_, hSu w ew⟩
  obtain ⟨U, F, hU, hgU, hF, hE⟩ := hSm w ew g ⟨Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hg, hd⟩
  exact ⟨U, F, hU, hgU, hF, fun x hx hxG => hE x hx (Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hxG)⟩

end auxC

end Formalism.FourierDecayAlt.P.PartialBesselProperness
end
end

