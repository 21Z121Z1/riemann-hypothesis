import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.Bundle0001
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0014
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0076

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.BaseSub
section
namespace UpperTheory.V.Z.Sym.Glob

open Matrix Loc

private theorem base_bot {Γ G V : Type} [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V] (ι : Γ →* G) (U : Subgroup G)
    (W : Representation ℂ Γ V) : ∃ B : Base Γ G V, B.ι = ι ∧ B.U = U ∧ B.ω = 1 ∧ B.Γ₀ = ⊥ ∧ B.W = W := by
  refine ⟨⟨ι, U, 1, W, ⊥, bot_le, ?_, ?_, ?_⟩, rfl, rfl, rfl, rfl, rfl⟩
  · intro z hz
    rw [Subgroup.mem_bot.1 hz, map_one]
    exact one_mem _
  · intro z hz
    rw [Subgroup.mem_bot.1 hz, map_one]
    exact one_mem _
  · intro z hz v
    obtain rfl := Subgroup.mem_bot.1 hz
    simp

private theorem base_sub {Γ G V : Type} [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V] (ι : Γ →* G) (S : Subgroup Γ)
    (T U : Subgroup G) (h : ∀ γ ∈ S, ι γ ∈ T) (x : G) (W : Representation ℂ S V) :
    ∃ B : Base S T V, (∀ γ : S, (B.ι γ : G) = ι γ) ∧ (∀ g : T, g ∈ B.U ↔ x⁻¹ * g * x ∈ U) ∧ B.ω = 1 ∧ B.Γ₀ = ⊥ ∧ B.W = W := by
  obtain ⟨B, h1, h2, h3⟩ := base_bot ((ι.comp S.subtype).codRestrict T fun γ => h γ γ.2)
    ((U.comap (MulAut.conj x⁻¹).toMonoidHom).subgroupOf T) W
  refine ⟨B, fun γ => by rw [h1]; rfl, fun g => ?_, h3⟩
  rw [h2, Subgroup.mem_subgroupOf, Subgroup.mem_comap]
  simp

private theorem mem_SU {K : Type} [Field K] {Δ : K} (g : DX Δ) : g ∈ SU Δ ↔ (mt g).det = 1 := by
  rw [SU, MonoidHom.mem_ker, ← Units.val_eq_one]
  rfl

end UpperTheory.V.Z.Sym.Glob

open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Glob in
theorem UpperTheory.V.Z.Sym.Glob.baseS :
    UpperTheory.V.Z.Sym.Glob.BaseS := by
  intro F _ _ Δ D _ V _ _ W ch htr x
  obtain ⟨-, ⟨ι, hι⟩, -⟩ := iotaEx F Δ
  have hmem : ∀ γ ∈ SU Δ, ι γ ∈ SA Δ := by
    intro γ hγ
    refine Subgroup.mem_iInf.2 fun v => Subgroup.mem_comap.2 ((mem_SU _).2 ?_)
    have h1 : (mt ((ι γ).1 v)).det = 1 := by
      rw [hι γ v, ← RingHom.mapMatrix_apply, ← RingHom.map_det, (mem_SU γ).1 hγ, map_one]
    exact h1
  obtain ⟨B, h1, h2, h3, h4, h5⟩ := base_sub ι (SU Δ) (SA Δ) D.U2 hmem x W
  refine ⟨B, ⟨fun γ v => ?_, h2, h3, h4, fun γ τ h => ?_⟩, h5⟩
  · rw [h1]
    exact hι _ v
  · rw [h5]
    exact htr γ τ h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.CharpolyThree
section
noncomputable section

namespace UpperTheory.V.Z.Sym.Glob

open Matrix Polynomial Loc

private theorem charpoly_three {R : Type} [CommRing R] (N : Matrix (Fin 3) (Fin 3) R) :
    N.charpoly = X ^ 3 - C N.trace * X ^ 2 + C N.adjugate.trace * X - C N.det := by
  simp only [Matrix.charpoly, Matrix.det_fin_three, Matrix.charmatrix_apply, Matrix.adjugate_fin_three,
    Matrix.trace_fin_three]
  simp [Matrix.diagonal_apply, Matrix.det_fin_three]
  ring

private theorem charpoly_recip {R : Type} [CommRing R] [StarRing R] (N : Matrix (Fin 3) (Fin 3) R)
    (h : N * star N = 1) (hd : N.det = 1) (ht : star N.trace = N.trace) :
    N.charpoly = (X - 1) * (X ^ 2 - C (N.trace - 1) * X + 1) := by
  have ha : N.adjugate = star N := by
    calc N.adjugate = N.adjugate * (N * star N) := by rw [h, mul_one]
      _ = star N := by rw [← mul_assoc, Matrix.adjugate_mul, hd, one_smul, one_mul]
  have hs : N.adjugate.trace = N.trace := by
    rw [ha, Matrix.star_eq_conjTranspose, Matrix.trace_conjTranspose, ht]
  rw [charpoly_three, hs, hd]
  simp only [map_sub, map_one]
  ring

private theorem eig_sq {A : Matrix (Fin 3) (Fin 3) ℂ} (h : star A * A = 1) (r : ℝ)
    (hr : A.charpoly.eval (r : ℂ) = 0) : r ^ 2 = 1 :=
  _root_.UpperTheory.Reformulated.B.EigenvalueSquare.eig_sq h r hr

private theorem exists_complex {F : Type} [Field F] (σ : F →+* ℝ) (Δ : F) (h : σ Δ < 0) :
    ∃ φ : Lsq F Δ →+* ℂ, (∀ x, φ (star x) = star (φ x)) ∧ ∀ a, φ (algebraMap F _ a) = (σ a : ℂ) := by
  have hr : Real.sqrt (-σ Δ) ^ 2 = -σ Δ := Real.sq_sqrt (by linarith)
  set r := Real.sqrt (-σ Δ)
  have hI : ((r : ℂ) * Complex.I) ^ 2 = (σ Δ : ℂ) := by
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, hr]
    simp
  refine ⟨{ toFun := fun x => (σ x.re : ℂ) + σ x.im * (r * Complex.I)
            map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, ?_, ?_⟩
  · simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  · intro x y
    simp
    linear_combination (-(σ x.im : ℂ) * σ y.im) * hI
  · simp
  · intro x y
    simp
    ring
  · intro x
    simp
  · intro a
    simp

private theorem trace_det {K : Type} [Field K] {Δ : K} (δ : U3 Δ) :
    star ((δ * theta Δ δ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).trace =
        ((δ * theta Δ δ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).trace ∧
      ((δ * theta Δ δ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).det = 1 := by
  set A : Matrix (Fin 3) (Fin 3) (Lsq K Δ) := δ.1 with hA
  have hB : ((theta Δ δ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) = A.map star := rfl
  have hN : ((δ * theta Δ δ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) = A * A.map star := by
    rw [← hB]; rfl
  have hu : A * star A = 1 := Matrix.mem_unitaryGroup_iff.1 δ.2
  rw [hN]
  constructor
  · have e : (A * A.map star).map (starRingEnd (Lsq K Δ)) = A.map star * A := by
      have e1 := Matrix.map_mul (L := A) (M := A.map star) (f := starRingEnd (Lsq K Δ))
      have e2 : (A.map star).map (starRingEnd (Lsq K Δ)) = A := by
        ext i j <;> simp [starRingEnd_apply]
      rw [e1, e2]
      rfl
    have e3 : ∀ M : Matrix (Fin 3) (Fin 3) (Lsq K Δ), star M.trace = (M.map (starRingEnd (Lsq K Δ))).trace := fun M => by
      simp [Matrix.trace_fin_three, starRingEnd_apply]
    rw [e3, e, Matrix.trace_mul_comm]
  · have e1 : (A.map star).det = star A.det := by
      rw [← Matrix.det_conjTranspose, ← Matrix.det_transpose]
      rfl
    have e2 : A.det * star A.det = 1 := by
      rw [← Matrix.det_conjTranspose, ← Matrix.det_mul, ← Matrix.star_eq_conjTranspose, hu, Matrix.det_one]
    rw [Matrix.det_mul, e1, e2]

private theorem eq_base {K : Type} [Field K] [CharZero K] {Δ : K} (t : Lsq K Δ) (h : star t = t) :
    t = algebraMap K _ t.re := by
  have h1 : (star t).im = t.im := by rw [h]
  have h2 : t.im = 0 := by
    simp at h1
    have h3 : (2 : K) * t.im = 0 := by linear_combination -h1
    simpa using h3
  ext <;> simp [h2]

end UpperTheory.V.Z.Sym.Glob

theorem UpperTheory.V.Z.Sym.Glob.tauEx :
    UpperTheory.V.Z.Sym.Glob.TauEx :=
  _root_.UpperTheory.Reformulated.B.CubicCharpolyDiscriminant.tauEx
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.ThetaTheta
section
namespace UpperTheory.V.Z.Sym.Glob

open Loc

end UpperTheory.V.Z.Sym.Glob

private theorem theta_apply_eq_star {K : Type} [Field K] (Δ : K) (g : UpperTheory.V.Z.Sym.Loc.U3 Δ) (i j : Fin 3) :
    (UpperTheory.V.Z.Sym.Loc.theta Δ g : Matrix (Fin 3) (Fin 3) (UpperTheory.V.Z.Sym.Lsq K Δ)) i j = star ((g : Matrix (Fin 3) (Fin 3) (UpperTheory.V.Z.Sym.Lsq K Δ)) i j) := by
  simp [UpperTheory.V.Z.Sym.Loc.theta]

private theorem theta_theta' {K : Type} [Field K] (Δ : K) (g : UpperTheory.V.Z.Sym.Loc.U3 Δ) :
    UpperTheory.V.Z.Sym.Loc.theta Δ (UpperTheory.V.Z.Sym.Loc.theta Δ g) = g := by
  apply Subtype.ext
  exact Matrix.ext fun i j => by rw [theta_apply_eq_star, theta_apply_eq_star, star_star]

private theorem theta_mem_ku_of_mem_ku (O : Type) [CommRing O] {K : Type} [Field K] [Algebra O K] (Δ : K)
    (g : UpperTheory.V.Z.Sym.Loc.U3 Δ) (hg : g ∈ UpperTheory.V.Z.Sym.Loc.KU O Δ) :
    UpperTheory.V.Z.Sym.Loc.theta Δ g ∈ UpperTheory.V.Z.Sym.Loc.KU O Δ := by
  intro i j
  rw [theta_apply_eq_star, star_star]
  exact ⟨(hg i j).2, (hg i j).1⟩

private theorem lmap_star_scalar_tuples {K K' : Type} [Field K] [Field K'] (f : K →+* K') (Δ : K)
    (x : UpperTheory.V.Z.Sym.Lsq K Δ) :
    UpperTheory.V.Z.Sym.Glob.lmap f Δ (star x) = star (UpperTheory.V.Z.Sym.Glob.lmap f Δ x) := by
  ext <;> simp [UpperTheory.V.Z.Sym.Glob.lmap]

open UpperTheory.V.Z.Sym.Loc in
theorem UpperTheory.V.Z.Sym.Glob.baseG :
    UpperTheory.V.Z.Sym.Glob.BaseG := by
  intro F _ _ Δ D _ V _ _ W Θ ch hΘ htr
  obtain ⟨⟨ι, hι⟩, -, -⟩ := UpperTheory.V.Z.Sym.Glob.iotaEx F Δ
  let tΓ : UpperTheory.V.Z.Sym.Loc.U3 Δ ≃* UpperTheory.V.Z.Sym.Loc.U3 Δ :=
    MonoidHom.toMulEquiv (UpperTheory.V.Z.Sym.Loc.theta Δ) (UpperTheory.V.Z.Sym.Loc.theta Δ)
      (by ext1 g; exact theta_theta' Δ g) (by ext1 g; exact theta_theta' Δ g)
  let tG0 : UpperTheory.V.Z.Sym.Glob.GA Δ →* UpperTheory.V.Z.Sym.Glob.GA Δ :=
    { toFun := fun g => ⟨fun v => UpperTheory.V.Z.Sym.Loc.theta (UpperTheory.V.Z.Sym.Glob.cv v Δ) (g.1 v),
        Filter.Eventually.mono (show ∀ᶠ v in Filter.cofinite, g.1 v ∈ UpperTheory.V.Z.Sym.Loc.KU
          (UpperTheory.V.Z.Sym.Glob.Ov v) (UpperTheory.V.Z.Sym.Glob.cv v Δ) from g.2)
          fun v hv => theta_mem_ku_of_mem_ku _ _ _ hv⟩
      map_one' := Subtype.ext (funext fun v => map_one _)
      map_mul' := fun a b => Subtype.ext (funext fun v => map_mul _ _ _) }
  let tG : UpperTheory.V.Z.Sym.Glob.GA Δ ≃* UpperTheory.V.Z.Sym.Glob.GA Δ :=
    MonoidHom.toMulEquiv tG0 tG0
      (by ext1 g; exact Subtype.ext (funext fun v => theta_theta' _ _))
      (by ext1 g; exact Subtype.ext (funext fun v => theta_theta' _ _))
  let B : UpperTheory.V.Z.Sym.Base (UpperTheory.V.Z.Sym.Loc.U3 Δ) (UpperTheory.V.Z.Sym.Glob.GA Δ) V :=
    { ι := ι, U := D.UG, ω := 1, W := W, Γ₀ := ⊥
      cenΓ := bot_le
      cenG := by
        intro z hz
        rw [Subgroup.mem_bot.mp hz, map_one]
        exact one_mem _
      memU := by
        intro z hz
        rw [Subgroup.mem_bot.mp hz, map_one]
        exact one_mem _
      scal := by
        intro z hz v
        obtain rfl := Subgroup.mem_bot.mp hz
        rw [MonoidHom.one_apply, Units.val_one, one_smul, map_one]
        rfl }
  let s : B.Tw :=
    { θΓ := tΓ, θ := tG, Θ := Θ
      comm := by
        intro γ
        apply Subtype.ext
        funext v
        apply Subtype.ext
        show ((UpperTheory.V.Z.Sym.Loc.theta (UpperTheory.V.Z.Sym.Glob.cv v Δ) ((ι γ).1 v)).1) =
          ((ι (UpperTheory.V.Z.Sym.Loc.theta Δ γ)).1 v).1
        rw [hι (UpperTheory.V.Z.Sym.Loc.theta Δ γ) v]
        refine Matrix.ext fun i j => ?_
        rw [theta_apply_eq_star, hι γ v, Matrix.map_apply, Matrix.map_apply, theta_apply_eq_star, lmap_star_scalar_tuples]
      int := hΘ
      fix := by
        intro z hz
        rw [Subgroup.mem_bot.mp hz]
        exact map_one _ }
  exact ⟨B, s, ⟨hι, rfl, rfl, rfl, fun γ => rfl, fun g v => rfl, htr⟩, rfl, rfl⟩
end

