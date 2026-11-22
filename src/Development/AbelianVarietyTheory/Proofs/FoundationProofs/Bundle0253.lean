import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0234
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0240
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUnitaryMulTriangular
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0237
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0238
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0013
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
import Formalism.GradedWeylDivisibility.StatementE
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.Bundle0001
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0082
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0239

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNonzeroThetaOfFiniteLevelAverage
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.GalTheta.Avg

theorem sum_out_translate {A M : Type*} [AddCommGroup A] [AddCommMonoid M] (S : AddSubgroup A) [Fintype (A ⧸ S)]
    (f : A → M) (hf : ∀ a, ∀ s ∈ S, f (a + s) = f a) (x : A) :
    ∑ q : A ⧸ S, f (x + q.out) = ∑ q : A ⧸ S, f q.out := by
  rw [← Equiv.sum_comp (Equiv.addLeft (x : A ⧸ S)) (fun q : A ⧸ S => f q.out)]
  refine Finset.sum_congr rfl fun q _ => ?_
  have h : ((x + q.out : A) : A ⧸ S) = (((x : A ⧸ S) + q).out : A) := by simp
  rw [QuotientAddGroup.eq] at h
  have := hf (x + q.out) _ h
  simp only [Equiv.coe_addLeft]
  rw [← this]
  congr 1
  abel

variable (D : D7) (T : Tor D) {N N' : ℕ}

def W (x : VC D N N') (G : VC D N N' → ℂ) : VC D N N' → ℂ := fun z => al D T x * U D T x G z

theorem Wm_mul_Wm_comm {x y : VC D N N'}
    (h : al D T (x + y) = al D T x * al D T y *
      Complex.exp (-(Real.pi : ℂ) * Complex.I * ((Hf D T x y).im : ℂ))) (G : VC D N N' → ℂ) :
    W D T x (W D T y G) = W D T (x + y) G := by
  funext z
  have := U_mul D T x (al D T y) (U D T y G) z
  unfold W
  rw [this, U_U, h]
  ring

theorem U_comm (x y : VC D N N') (G : VC D N N' → ℂ) (z : VC D N N') :
    U D T x (U D T y G) z =
      Complex.exp (-(2 * Real.pi * Complex.I) * ((Hf D T x y).im : ℂ)) * U D T y (U D T x G) z := by
  rw [U_U, U_U, add_comm y x, Hf_im_swap D T x y, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem eq_zero_of_U {x : VC D N N'} {G : VC D N N' → ℂ} (h : ∀ z, U D T x G z = 0) (z : VC D N N') :
    G z = 0 := by
  have := h (z - x)
  simpa [U] using this

theorem al_two_mul {x : VC D N N'} (hx : ∃ m : ℤ, qH D T x = m) (n : ℕ) : al D T ((2 * n) • x) = 1 := by
  obtain ⟨m, hm⟩ := hx
  unfold qH at hm
  have : √↑D.host.d / 2 * (Hf D T ((2 * n) • x) ((2 * n) • x)).re = ((2 * (2 * n * n * m) : ℤ) : ℝ) := by
    rw [Hf_nsmul_left, Hf_nsmul_right, ← mul_assoc, ← Nat.cast_mul, ← Complex.ofReal_natCast,
      Complex.re_ofReal_mul, mul_left_comm, hm]
    push_cast
    ring
  unfold al
  rw [this, round_intCast, zpow_mul]
  norm_num

theorem im_smul_right (c : ℝ) (x y : VC D N N') : (Hf D T x ((c : ℂ) • y)).im = c * (Hf D T x y).im := by
  rw [Hf_smul_right, Complex.conj_ofReal, Complex.im_ofReal_mul]

theorem im_smul_left (c : ℝ) (x y : VC D N N') : (Hf D T ((c : ℂ) • x) y).im = c * (Hf D T x y).im := by
  rw [Hf_smul_left, Complex.im_ofReal_mul]

theorem im_nsmul_right (c : ℕ) (x y : VC D N N') : (Hf D T x (c • y)).im = c * (Hf D T x y).im := by
  rw [← im_smul_right, Complex.ofReal_natCast, Nat.cast_smul_eq_nsmul]

theorem im_nsmul_left (c : ℕ) (x y : VC D N N') : (Hf D T (c • x) y).im = c * (Hf D T x y).im := by
  rw [← im_smul_left, Complex.ofReal_natCast, Nat.cast_smul_eq_nsmul]

theorem exp_int (t : ℝ) (m : ℤ) (h : t = m) : Complex.exp (-(2 * Real.pi * Complex.I) * (t : ℂ)) = 1 := by
  rw [Complex.exp_eq_one_iff]
  exact ⟨-m, by rw [h]; push_cast; ring⟩

theorem int_of_exp (t : ℝ) (h : Complex.exp (-(2 * Real.pi * Complex.I) * (t : ℂ)) = 1) : ∃ m : ℤ, t = m := by
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨m, hm⟩ := h
  refine ⟨-m, ?_⟩
  have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have : (t : ℂ) = ((-m : ℤ) : ℝ) := by
    apply mul_left_cancel₀ h2
    push_cast
    linear_combination -hm
  exact_mod_cast this

end GlobalTheory.GalTheta.Avg

namespace GlobalTheory.GalTheta

open Avg

theorem exists_theta_of_level : ∀ (D : D7) (T : Tor D) (N N' : ℕ) (A : AddSubgroup (VC D N N')), A.FG → (∀ x ∈ A, ∀ y ∈ A, ∃ m : ℤ, (Hf D T x y).im = m) → (∀ x, (∀ y ∈ A, ∃ m : ℤ, (Hf D T x y).im = m) → x ∈ A) → (∀ x ∈ A, ∃ m : ℤ, qH D T x = m) → (∀ x ∈ A, ∀ y ∈ A, al D T (x + y) = al D T x * al D T y * Complex.exp (-(Real.pi : ℂ) * Complex.I * ((Hf D T x y).im : ℂ))) → ∀ F : VC D N N' → ℂ, Differentiable ℂ F → F ≠ 0 → ∀ n : ℕ, 0 < n → (∀ x ∈ A, U D T (n • x) F = F) → ∃ P, IsTr D T A F P ∧ P ∈ ThSp D T A ∧ P ≠ 0 := by
  intro D T N N' A hfg hint hdual hq hal F hF hF0 n hn hlev
  have hn2 : 0 < 2 * n := by omega
  haveI : AddGroup.FG A := (AddGroup.fg_iff_addSubgroup_fg A).2 hfg
  set S : AddSubgroup A := (nsmulAddMonoidHom (α := A) (2 * n)).range with hS
  haveI : S.FiniteIndex := AddSubgroup.finiteIndex_range_nsmulAddMonoidHom_of_fg A hn2.ne'
  letI : Fintype (A ⧸ S) := Fintype.ofFinite _
  set c : ℝ := ((2 * n : ℕ) : ℝ)⁻¹ with hc
  have hcn : ((2 * n : ℕ) : ℝ) * c = 1 := mul_inv_cancel₀ (by exact_mod_cast hn2.ne')
  have hcs : ∀ y : VC D N N', (2 * n) • ((c : ℂ) • y) = y := by
    intro y
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, ← Complex.ofReal_natCast, ← Complex.ofReal_mul, hcn]
    simp
  have hUF : ∀ x ∈ A, U D T ((2 * n) • x) F = F := by
    intro x hx
    rw [mul_comm, mul_smul]
    exact hlev _ (A.nsmul_mem hx 2)

  have hfix : ∀ y ∈ A, ∀ x ∈ A, W D T ((2 * n) • x) (U D T ((c : ℂ) • y) F) = U D T ((c : ℂ) • y) F := by
    intro y hy x hx
    funext z
    obtain ⟨m, hm⟩ := hint x hx y hy
    unfold W
    rw [al_two_mul D T (hq x hx), one_mul, U_comm, hUF x hx, exp_int _ m, one_mul]
    rw [im_nsmul_left, im_smul_right, ← mul_assoc, hcn, one_mul, hm]
  have hcls : ∀ y ∈ A, ∀ a : A, ∀ s ∈ S,
      W D T ((a + s : A) : VC D N N') (U D T ((c : ℂ) • y) F) = W D T a (U D T ((c : ℂ) • y) F) := by
    rintro y hy a s ⟨b, rfl⟩
    have e : ((a + nsmulAddMonoidHom (2 * n) b : A) : VC D N N') = (a : VC D N N') + (2 * n) • (b : VC D N N') := by
      simp
    rw [e, ← Wm_mul_Wm_comm D T (hal _ a.2 _ (A.nsmul_mem b.2 _)), hfix y hy b b.2]

  set P : VC D N N' → VC D N N' → ℂ :=
    fun y z => ∑ q : A ⧸ S, W D T (q.out : A) (U D T ((c : ℂ) • y) F) z with hP
  have hTr : ∀ y ∈ A, IsTr D T A F (P y) := by
    intro y hy
    refine IsTr.trans D T (IsTr.single D T F 1 ((c : ℂ) • y) (2 * n) hn2 (by rw [hcs]; exact hy)) ?_
    let e := Fintype.equivFin (A ⧸ S)
    refine ⟨_, fun i => al D T (((e.symm i).out : A) : VC D N N'), fun i => (((e.symm i).out : A) : VC D N N'), 1, one_pos,
      fun i => by simp, ?_⟩
    funext z
    simp only [hP, comb, one_mul, W]
    exact (Equiv.sum_comp e.symm _).symm
  have hTh : ∀ y ∈ A, P y ∈ ThSp D T A := by
    intro y hy
    refine ⟨?_, fun x hx z => ?_⟩
    · exact Differentiable.fun_sum fun q _ =>
        (differentiable_U D T _ (differentiable_U D T ((c : ℂ) • y) hF)).const_mul _
    · have h1 := sum_out_translate S (fun a : A => W D T (a : VC D N N') (U D T ((c : ℂ) • y) F) z)
        (fun a s hs => by simp only [hcls y hy a s hs]) ⟨x, hx⟩
      simp only [hP]
      rw [← h1, U_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      exact congrFun (Wm_mul_Wm_comm D T (hal x hx _ (q.out).2) _) z
  by_contra hcon
  push Not at hcon
  have hP0 : ∀ y ∈ A, P y = 0 := fun y hy => hcon _ (hTr y hy) (hTh y hy)

  set χ : A → A → ℂ := fun a y =>
    Complex.exp (-(2 * Real.pi * Complex.I) * ((c * (Hf D T (a : VC D N N') y).im : ℝ) : ℂ)) with hχ
  have hsum : ∀ y : A, ∀ z, ∑ q : A ⧸ S, χ q.out y * W D T (q.out : A) F z = 0 := by
    intro y
    apply eq_zero_of_U D T (x := (c : ℂ) • (y : VC D N N'))
    intro z
    have h0 := congrFun (hP0 y y.2) z
    simp only [hP, Pi.zero_apply] at h0
    rw [U_sum, ← h0]
    refine Finset.sum_congr rfl fun q _ => ?_
    have h2 := U_mul D T ((c : ℂ) • (y : VC D N N')) (al D T ((q.out : A) : VC D N N')) (U D T (q.out : A) F) z
    rw [U_mul]
    unfold W
    rw [h2, U_comm D T ((q.out : A) : VC D N N'), im_smul_right]
    simp only [hχ]
    ring
  have hadd : ∀ a x y : A, χ a (x + y) = χ a x * χ a y := by
    intro a x y
    simp only [hχ]
    rw [← Complex.exp_add, AddSubgroup.coe_add, Hf_add_right, Complex.add_im]
    congr 1
    push_cast
    ring
  have hS1 : ∀ a : A, ∀ s ∈ S, χ a s = 1 := by
    rintro a s ⟨b, rfl⟩
    obtain ⟨m, hm⟩ := hint a a.2 b b.2
    have e : ((nsmulAddMonoidHom (2 * n) b : A) : VC D N N') = (2 * n) • (b : VC D N N') := by simp
    refine exp_int _ m ?_
    rw [e, im_nsmul_right, ← mul_assoc, mul_comm c, hcn, one_mul, hm]
  have hS2 : ∀ s ∈ S, ∀ a : A, χ s a = 1 := by
    rintro s ⟨b, rfl⟩ a
    obtain ⟨m, hm⟩ := hint b b.2 a a.2
    have e : ((nsmulAddMonoidHom (2 * n) b : A) : VC D N N') = (2 * n) • (b : VC D N N') := by simp
    refine exp_int _ m ?_
    rw [e, im_nsmul_left, ← mul_assoc, mul_comm c, hcn, one_mul, hm]
  have hvan : ∀ q : A ⧸ S, q ≠ 0 → ∑ r : A ⧸ S, χ q.out r.out = 0 := by
    intro q hq0
    by_contra hne
    apply hq0
    have hall : ∀ y : A, χ q.out y = 1 := by
      intro y
      have h1 := sum_out_translate S (χ q.out) (fun a s hs => by rw [hadd, hS1 _ s hs, mul_one]) y
      simp only [hadd, ← Finset.mul_sum] at h1
      exact mul_right_cancel₀ hne (by rw [h1, one_mul])
    have hmem : (c : ℂ) • ((q.out : A) : VC D N N') ∈ A := by
      refine hdual _ fun y hy => ?_
      rw [im_smul_left]
      exact int_of_exp _ (hall ⟨y, hy⟩)
    rw [← QuotientAddGroup.out_eq' q, QuotientAddGroup.eq_zero_iff]
    exact ⟨⟨_, hmem⟩, Subtype.ext (by simpa using hcs _)⟩
  have h0S : (0 : A ⧸ S).out ∈ S := by
    rw [← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.out_eq']
  have hW0 : W D T ((0 : A ⧸ S).out : A) F = F := by
    obtain ⟨b, hb⟩ := h0S
    have := hfix 0 A.zero_mem b b.2
    rw [smul_zero, U_zero] at this
    rw [← hb]
    simpa using this
  apply hF0
  funext z
  have h3 : ∑ r : A ⧸ S, ∑ q : A ⧸ S, χ q.out r.out * W D T (q.out : A) F z = 0 :=
    Finset.sum_eq_zero fun r _ => hsum _ z
  rw [Finset.sum_comm, Finset.sum_eq_single 0 (fun q _ hq0 => by rw [← Finset.sum_mul, hvan q hq0, zero_mul])
    (by simp)] at h3
  simp only [hS2 _ h0S, hW0, one_mul, Finset.sum_const, nsmul_eq_mul, mul_eq_zero, Nat.cast_eq_zero,
    Finset.card_univ, Fintype.card_ne_zero, false_or] at h3
  exact h3

end GlobalTheory.GalTheta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsOrthonormalEigenbasis
section
open Module.End

namespace GlobalTheory.OrthonormalEigenbasis

theorem exists_eigenbasis_of_isometry {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (a : E →ₗ[ℂ] E) (ha : ∀ x y, inner ℂ (a x) (a y) = inner ℂ x y) :
    ∃ (b : OrthonormalBasis (Fin (Module.finrank ℂ E)) ℂ E) (l : Fin (Module.finrank ℂ E) → ℂ),
      ∀ i, a (b i) = l i • b i := by
  set a' := LinearMap.adjoint a with ha'

  have h1 : a' * a = 1 := by
    ext x
    apply ext_inner_right ℂ
    intro y
    rw [Module.End.mul_apply, ha', LinearMap.adjoint_inner_left, ha, Module.End.one_apply]
  have h2 : a * a' = 1 := mul_eq_one_comm.mp h1

  set A : E →ₗ[ℂ] E := a + a' with hAdef
  set B : E →ₗ[ℂ] E := Complex.I • (a' - a) with hBdef
  have hA : A.IsSymmetric := by
    intro x y
    simp only [hAdef, LinearMap.add_apply, inner_add_left, inner_add_right, ha',
      LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_right]
    ring
  have hB : B.IsSymmetric := by
    intro x y
    simp only [hBdef, LinearMap.smul_apply, LinearMap.sub_apply, inner_smul_left, inner_smul_right,
      inner_sub_left, inner_sub_right, ha', LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_right,
      Complex.conj_I]
    ring
  have hAB : Commute A B := by
    have hc : Commute (a + a') (a' - a) := by
      show (a + a') * (a' - a) = (a' - a) * (a + a')
      simp only [add_mul, mul_add, sub_mul, mul_sub, h1, h2]
      abel
    exact hc.smul_right Complex.I
  have hV := LinearMap.IsSymmetric.directSum_isInternal_of_commute hA hB hAB
  have hV' := LinearMap.IsSymmetric.orthogonalFamily_eigenspace_inf_eigenspace hA hB

  have hT : Set.Finite {i : ℂ × ℂ | eigenspace A i.2 ⊓ eigenspace B i.1 ≠ ⊥} := by
    refine ((Module.End.finite_hasEigenvalue (f := B)).prod
      (Module.End.finite_hasEigenvalue (f := A))).subset fun i hi => ⟨?_, ?_⟩
    · exact Module.End.hasEigenvalue_iff.mpr (ne_bot_of_le_ne_bot hi inf_le_right)
    · exact Module.End.hasEigenvalue_iff.mpr (ne_bot_of_le_ne_bot hi inf_le_left)
  have : Finite {i : ℂ × ℂ // eigenspace A i.2 ⊓ eigenspace B i.1 ≠ ⊥} := hT.to_subtype
  have := Fintype.ofFinite {i : ℂ × ℂ // eigenspace A i.2 ⊓ eigenspace B i.1 ≠ ⊥}
  classical
  have hW := DirectSum.isInternal_ne_bot_iff.mpr hV
  have hW' := hV'.comp (Subtype.val_injective (p := fun i : ℂ × ℂ => eigenspace A i.2 ⊓ eigenspace B i.1 ≠ ⊥))

  refine ⟨hW.subordinateOrthonormalBasis rfl hW', fun i =>
    ((hW.subordinateOrthonormalBasisIndex rfl i hW').1.2 +
      Complex.I * (hW.subordinateOrthonormalBasisIndex rfl i hW').1.1) / 2, fun i => ?_⟩
  have hmem := hW.subordinateOrthonormalBasis_subordinate rfl i hW'
  rw [Submodule.mem_inf, Module.End.mem_eigenspace_iff, Module.End.mem_eigenspace_iff] at hmem
  have hsum : ∀ v, A v + Complex.I • B v = (2 : ℂ) • a v := by
    intro v
    simp only [hAdef, hBdef, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply, smul_smul,
      Complex.I_mul_I, neg_one_smul, smul_sub, two_smul]
    abel
  calc a (hW.subordinateOrthonormalBasis rfl hW' i)
      = (2 : ℂ)⁻¹ • (A (hW.subordinateOrthonormalBasis rfl hW' i) +
          Complex.I • B (hW.subordinateOrthonormalBasis rfl hW' i)) := by
        rw [hsum, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
    _ = _ := by
        rw [hmem.1, hmem.2, smul_smul, ← add_smul, smul_smul]
        congr 1
        ring

open GlobalTheory.UnitaryTheta in

theorem exists_orthonormal_eigenbasis {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (H : Sesq V) (hH : IsPosHerm H) (a : V →ₗ[ℂ] V) (ha : ∀ z w, H (a z) (a w) = H z w) :
    ∃ (n : ℕ) (e : Module.Basis (Fin n) ℂ V) (l : Fin n → ℂ),
      (∀ i j, H (e i) (e j) = if i = j then (1 : ℂ) else 0) ∧ ∀ i, ‖l i‖ = 1 ∧ a (e i) = l i • e i := by

  let cd : InnerProductSpace.Core ℂ V :=
    { inner := fun x y => H y x
      conj_inner_symm := fun x y => (hH.1 y x).symm
      re_inner_nonneg := fun x => by
        by_cases hx : x = 0
        · simp [hx]
        · exact (hH.2 x hx).le
      add_left := fun x y z => by
        show H z (x + y) = H z x + H z y
        exact map_add _ _ _
      smul_left := fun x y r => by
        show H y (r • x) = (starRingEnd ℂ) r * H y x
        rw [LinearMap.map_smulₛₗ, smul_eq_mul]
      definite := fun x hx => by
        by_contra h
        have := hH.2 x h
        simp [hx] at this }
  let _ : NormedAddCommGroup V := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  let _ : InnerProductSpace ℂ V := InnerProductSpace.ofCore cd.toCore
  have hinner : ∀ x y : V, inner ℂ x y = H y x := fun _ _ => rfl
  obtain ⟨b, l, hb⟩ := exists_eigenbasis_of_isometry a (fun x y => by rw [hinner, hinner]; exact ha y x)
  refine ⟨Module.finrank ℂ V, b.toBasis, l, fun i j => ?_, fun i => ⟨?_, ?_⟩⟩
  · rw [OrthonormalBasis.coe_toBasis, ← hinner, orthonormal_iff_ite.mp b.orthonormal j i]
    exact if_congr eq_comm rfl rfl
  ·
    have h1 : ‖a (b i)‖ = ‖b i‖ := by
      rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ), hinner, hinner, ha]
    rw [hb i, norm_smul, b.orthonormal.1 i, mul_one] at h1
    exact h1
  · rw [OrthonormalBasis.coe_toBasis]
    exact hb i

end GlobalTheory.OrthonormalEigenbasis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSmulMemOfLeLocP
section
open GlobalTheory.DualWeyl MvPolynomial NumberField IsDedekindDomain
open Formalism.L2.DIV (colLat IsBasisAt dualFr)
open Formalism.HermitianLatticesTheory (localization₂)
open scoped Matrix

namespace GlobalTheory.DualWeylDual

variable {K : Type} [Field K] {N : ℕ}

theorem exists_smul_mem_of_le_locP (w : HeightOneSpectrum (𝓞 K)) {M M' : Submodule (𝓞 K) (Fin N → K)}
    (hM : M.FG) (h : M ≤ localization₂ w.asIdeal M') : ∃ t ∈ w.asIdeal.primeCompl, ∀ x ∈ M, t • x ∈ M' := by
  classical
  obtain ⟨s, rfl⟩ := hM
  have h1 : ∀ y : s, ∃ a ∈ w.asIdeal.primeCompl, a • (y : Fin N → K) ∈ M' := fun y =>
    h (Submodule.subset_span y.2)
  choose a ha0 ha using h1
  refine ⟨∏ y, a y, Submonoid.prod_mem _ fun y _ => ha0 y, fun x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem y hy =>
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (⟨y, hy⟩ : s)), mul_smul]
    exact M'.smul_mem _ (ha ⟨y, hy⟩)
  | zero => simp
  | add y z _ _ hy hz => rw [smul_add]; exact M'.add_mem hy hz
  | smul c y _ hy => rw [smul_comm]; exact M'.smul_mem _ hy

theorem localization_dualFr_le (w : HeightOneSpectrum (𝓞 K)) {M M' : Submodule (𝓞 K) (Fin N → K)}
    (hM : M.FG) (h : localization₂ w.asIdeal M ≤ localization₂ w.asIdeal M') :
    localization₂ w.asIdeal (dualFr M') ≤ localization₂ w.asIdeal (dualFr M) := by
  obtain ⟨t, ht, htM⟩ := exists_smul_mem_of_le_locP w hM
    (fun x hx => h ⟨1, Submonoid.one_mem _, by rwa [one_smul]⟩)
  rintro φ ⟨s, hs, hφ⟩
  refine ⟨t * s, Submonoid.mul_mem _ ht hs, fun x hx => ?_⟩
  have h1 : (s • φ) ⬝ᵥ (t • x) ∈ (1 : Submodule (𝓞 K) K) := hφ _ (htM x hx)
  rwa [dotProduct_smul, ← smul_dotProduct, smul_smul] at h1

theorem dualFr_colLat (B : GL (Fin N) K) : dualFr (colLat B) = colLat (Formalism.BasicNotions.inside₂ K N B) := by
  ext φ
  rw [mem_colLat_iff]
  constructor
  · intro h
    have h1 : ∀ j, ∃ c : 𝓞 K, algebraMap (𝓞 K) K c = φ ⬝ᵥ fun a => (B : Matrix (Fin N) (Fin N) K) a j := fun j =>
      Submodule.mem_one.mp (h _ (Submodule.subset_span ⟨j, rfl⟩))
    choose c hc using h1
    refine ⟨c, ?_⟩
    have h2 : (fun j => (c j : K)) = (B : Matrix (Fin N) (Fin N) K)ᵀ *ᵥ φ := by
      funext j
      rw [Matrix.mulVec_transpose]
      exact hc j
    rw [h2, Matrix.mulVec_mulVec]
    change (((B⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)ᵀ * _) *ᵥ φ = φ
    rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one, Matrix.one_mulVec]
  · rintro ⟨c, rfl⟩ x hx
    obtain ⟨d, rfl⟩ := (mem_colLat_iff _ _).mp hx
    change (((B⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)ᵀ *ᵥ _) ⬝ᵥ _ ∈ _
    rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    refine Submodule.mem_one.mpr ⟨c ⬝ᵥ d, ?_⟩
    simp [dotProduct]

theorem isBasisAt_dualFr (w : HeightOneSpectrum (𝓞 K)) {L : Submodule (𝓞 K) (Fin N → K)} (hL : L.FG)
    {B : GL (Fin N) K} (hB : IsBasisAt w L B) : IsBasisAt w (dualFr L) (Formalism.BasicNotions.inside₂ K N B) := by
  unfold IsBasisAt at hB ⊢
  rw [← dualFr_colLat]
  exact le_antisymm (localization_dualFr_le w (Submodule.fg_span (Set.finite_range _)) hB.ge) (localization_dualFr_le w hL hB.le)

end GlobalTheory.DualWeylDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTraceDualFamilyHomLatticeStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_traceDual_family_homLattice : ∀ (D : D7), (∃ (r : ℕ) (a a' : Fin r → D.host.E), (∀ k, a k ∈ D.host.AA0) ∧ (∀ k, a' k ∈ D.host.AA0) ∧ ∀ t : D.host.E, t = ∑ k, (Algebra.trace D.host.K D.host.E (t * D.host.conj (a' k))) • a k) → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), SD D L → SD D L' → ∃ (r : ℕ) (y y' : Fin r → Matrix (Fin N') (Fin N) D.host.E), (∀ i, y i ∈ YYl D L L') ∧ (∀ i, y' i ∈ YYl D L L') ∧ ∀ x : Matrix (Fin N') (Fin N) D.host.E, x = ∑ i, hYY D x (y' i) • y i := by
  first | exact @GlobalTheory.HomDual.exists_dual_family_hom | exact GlobalTheory.HomDual.exists_dual_family_hom | (intros; apply GlobalTheory.HomDual.exists_dual_family_hom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTraceDualFamilyInverseHalfDifferentStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_traceDual_family_inverseHalfDifferent : ∀ (D : D7), ∃ (r : ℕ) (a a' : Fin r → D.host.E), (∀ k, a k ∈ D.host.AA0) ∧ (∀ k, a' k ∈ D.host.AA0) ∧ ∀ t : D.host.E, t = ∑ k, (Algebra.trace D.host.K D.host.E (t * D.host.conj (a' k))) • a k := by
  first | exact @GlobalTheory.exists_trace_dual_family_halfDifferent | exact GlobalTheory.exists_trace_dual_family_halfDifferent | (intros; apply GlobalTheory.exists_trace_dual_family_halfDifferent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExtNormMulWeylPairingIntegralSelfDualStatement
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extNorm_mul_weylPairing_integral_selfDual : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (G : ι → Matrix (Fin n) (Fin n) K) (M : ι → Submodule (𝓞 K) (Fin n → K)), (∀ τ, (G τ)ᴴ = G τ) → (∀ τ, IsUnit (G τ).det) → (∀ τ, IsSelfDualK (G τ) (M τ)) → ∀ x ∈ nabK lam M, ∀ y ∈ nabK lam M, extNorm K lam * pairK lam G x y ∈ (algebraMap (𝓞 K) K).range := by
  first | exact @GlobalTheory.PairInt.extNorm_mul_pairK_integral | exact GlobalTheory.PairInt.extNorm_mul_pairK_integral | (intros; apply GlobalTheory.PairInt.extNorm_mul_pairK_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FockNormExtremalVectorEqBoundedNatStatement
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockNorm_extremal_vector_eq_bounded_nat : ∀ (n : ℕ) (lam : DomWeight n) (R : ℕ), (∀ i, lam.natW i ≤ R) → ∃ s : ℕ, 0 < s ∧ s ≤ (n.factorial) ^ (2 * R) * (R.factorial) ^ n ∧ ∀ (K : Type) [Field K] [StarRing K] [CharZero K], fockS (extremal K n lam) (extremal K n lam) = (s : K) := by
  first | exact @GlobalTheory.ExtremalNorm.fockS_extremal_eq_nat | exact GlobalTheory.ExtremalNorm.fockS_extremal_eq_nat | (intros; apply GlobalTheory.ExtremalNorm.fockS_extremal_eq_nat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HarmonicHighestWeightEqLowestKTypeHighestWeightStatement
section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harmonic_highestWeight_eq_lowestKTypeHighestWeight : ∀ (p q n : ℕ) (hn : p + q < n) (ap : Fin p → ℕ) (am : Fin q → ℕ) (μ : Ix p q → ℚ) (P : Pol p q n 0), IsHW (fockAct1 p q n 0) μ P → P ∈ hwSub (fockAct2 p q n 0) (wtH n ap am) → KilledByLower (fockAct1 p q n 0) P → μ = wtK n ap am := by
  first | exact @GlobalTheory.HarmonicShape.weight_eq_wtK | exact GlobalTheory.HarmonicShape.weight_eq_wtK | (intros; apply GlobalTheory.HarmonicShape.weight_eq_wtK <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HermitianPairingRationalValuesStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_pairing_integral_values : ∀ (D : D7) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), SD D L → SD D L' → ∀ x ∈ YYl D L L', ∀ y ∈ YYl D L L', hYY D x y ∈ (algebraMap (𝓞 D.host.K) D.host.K).range := by
  first | exact @GlobalTheory.NormSum.TraceInt.hYY_integral | exact GlobalTheory.NormSum.TraceInt.hYY_integral | (intros; apply GlobalTheory.NormSum.TraceInt.hYY_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealPeriodLatticeOfCurveDatumStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idealPeriodLattice_of_curveDatum : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → (∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ (lamOf D cc δ) = AddSubgroup.closure {w₁, w₂}) ∧ δ ≠ 0 ∧ TaylorLogMetric.discr (lamOf D cc δ) = 1 ∧ area (lamOf D cc δ) = ‖δ‖ ^ 2 * (Ideal.absNorm cc : ℝ) * Real.sqrt D.host.d / 2 ∧ (∀ a : 𝓞 D.host.K, ∀ w ∈ (lamOf D cc δ), D.host.φ₀ (((a : D.host.K) : D.host.E)) * w ∈ (lamOf D cc δ)) := by
  first | exact @GlobalTheory.CurveLattice.lattice_of_curve | exact GlobalTheory.CurveLattice.lattice_of_curve | (intros; apply GlobalTheory.CurveLattice.lattice_of_curve <;> assumption)
end

