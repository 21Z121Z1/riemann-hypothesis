import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0017
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0083
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0087
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0095
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0052
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0077
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LocDerRegularCoeff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0117
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0085
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0004
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0005
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0098
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0121
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0120

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HolomorphicLiftRegularOfPeriodsZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

noncomputable section
namespace GlobalTheory.KS.ZeroClass
open VertReg

section
variable {R : Type} [CommRing R] {Y X : Scheme.{0}} {q : Y ⟶ Sp ℂ} {p : X ⟶ Sp R} {m : Y ⟶ X} {D : R → ℂ}

theorem locDer_sub {V V' : X.Opens} {d d' : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)} (h : LocDer q p m D V d)
    (h' : LocDer q p m D V' d') : LocDer q p m (fun _ => 0) (V ⊓ V') (fun W f => d W f - d' W f) where
  add W hW f f' := by
    rw [h.add W (hW.trans inf_le_left), h'.add W (hW.trans inf_le_right)]
    abel
  mul W hW f f' := by
    rw [h.mul W (hW.trans inf_le_left), h'.mul W (hW.trans inf_le_right)]
    ring
  res W W' hle hW f := by
    rw [h.res W W' hle (hW.trans inf_le_left), h'.res W W' hle (hW.trans inf_le_right), map_sub]
  base W hW r := by
    rw [h.base W (hW.trans inf_le_left), h'.base W (hW.trans inf_le_right), sub_self,
      ← liftConstHom_apply, map_zero]

theorem ptOf_of_le {V : X.Opens} {d : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)} (h : LocDer q p m D V d)
    (y : Sp ℂ ⟶ Y) {W : X.Opens} (hW : W ≤ V) (hy : ⊤ ≤ (y ≫ m) ⁻¹ᵁ W) (f : Γ(X, W)) :
    ptOf V d y W f = valAt' y (m ⁻¹ᵁ W) (d W f) := by
  have hy' : ⊤ ≤ (y ≫ m) ⁻¹ᵁ (W ⊓ V) := (inf_eq_left.mpr hW).symm ▸ hy
  exact val_res h y inf_le_left hW hy' f

theorem ptDer_sub {y : Sp ℂ ⟶ X} {δ δ' : ∀ W : X.Opens, Γ(X, W) → ℂ} (h : PtDer y δ) (h' : PtDer y δ') :
    PtDer y (fun W f => δ W f - δ' W f) := by
  constructor
  · intro W hW f f'
    simp only [h.add W hW, h'.add W hW]
    ring
  · intro W hW f f'
    simp only [h.mul W hW, h'.mul W hW]
    ring
  · intro W W' hle hW f
    simp only [h.res W W' hle hW, h'.res W W' hle hW]

end

theorem ex_add_lattice {g : ℕ} {A₀ : Over (Sp ℂ)} [GrpObj A₀] {L₀ : LB A₀.left} (u : HolUnif A₀ L₀ g)
    (z : Fin g → ℂ) (l : u.Λ) : u.ex (z + l) = u.ex z := by
  rw [u.ex_add, (u.ker l).mpr l.2, ← (u.ker 0).mpr (zero_mem _), ← u.ex_add, add_zero]

variable {P₀ : Out.PolAV (Sp ℂ)} {u : HolUnif P₀.A P₀.L P₀.g} {Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ} {χ : u.Λ → ℂ}
  {R : Type} [CommRing R] {x₀ : R →+* ℂ} {X : Scheme.{0}} {p : X ⟶ Sp R} {m : P₀.A.left ⟶ X}

theorem vector_ext (hu : GoodU u Hm χ) (hp : Smooth p) (hm : IsPullback m P₀.A.hom p (spMap x₀)) {V : X.Opens}
    {z : Fin P₀.g → ℂ} (hz : z ∈ dom u m V) {v v' : Fin P₀.g → ℂ}
    (h : ∀ W, W ≤ V → z ∈ dom u m W → ∀ f, fderiv ℂ (fn u m W f) z v = fderiv ℂ (fn u m W f) z v') : v = v' := by
  obtain ⟨W, t, hzW, hdet⟩ := exists_fibre_coords P₀ u Hm χ hu R x₀ X p m hp hm z
  have hzWV : z ∈ dom u m (W ⊓ V) := fun a ha => ⟨hzW ha, hz ha⟩
  have hlin : ∀ (w : Fin P₀.g → ℂ) b, fderiv ℂ (fn u m W (t b)) z w =
      Matrix.vecMul w (Matrix.of fun a b => fderiv ℂ (fn u m W (t b)) z (Pi.single a 1)) b := by
    intro w b
    conv_lhs => rw [← Finset.univ_sum_single w]
    rw [map_sum]
    simp only [Matrix.vecMul, dotProduct, Matrix.of_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [show Pi.single a (w a) = w a • (Pi.single a 1 : Fin P₀.g → ℂ) by
      ext j; by_cases hj : j = a <;> simp [hj], map_smul, smul_eq_mul]
  have hk : Matrix.vecMul (v - v') (Matrix.of fun a b => fderiv ℂ (fn u m W (t b)) z (Pi.single a 1)) = 0 := by
    ext b
    rw [← hlin, map_sub, Pi.zero_apply, sub_eq_zero]
    have e := h (W ⊓ V) inf_le_right hzWV (resG X inf_le_left (t b))
    rwa [fderiv_fn_resG u m inf_le_left (t b) hzWV] at e
  exact sub_eq_zero.mp (Matrix.eq_zero_of_vecMul_eq_zero hdet hk)

theorem exists_periodic_vector (hu : GoodU u Hm χ) (hp : Smooth p) (hm : IsPullback m P₀.A.hom p (spMap x₀))
    {D : R → ℂ} {s} (hs : KSRel u p m D 0 s) {V : X.Opens} {d} (hd : LocDer P₀.A.hom p m D V d) :
    ∃ w : (Fin P₀.g → ℂ) → (Fin P₀.g → ℂ), DifferentiableOn ℂ w (dom u m V) ∧
      (∀ (l : u.Λ), ∀ z ∈ dom u m V, w (z + l) = w z) ∧
      ∀ W, W ≤ V → ∀ f, ∀ z ∈ dom u m W,
        s z W f = valAt' (u.ex z).left (m ⁻¹ᵁ W) (d W f) + fderiv ℂ (fn u m W f) z (w z) := by
  have hq : ∀ z, (u.ex z).left ≫ P₀.A.hom = 𝟙 _ := fun z => by simp
  have hex : ∀ (l : u.Λ) z, u.ex (z + l) = u.ex z := fun l z => ex_add_lattice u z l
  have hdomV : IsOpen (dom u m V) := (u.hol (m ⁻¹ᵁ V) 0).1
  have hpt : ∀ z ∈ dom u m V, PtDer ((u.ex z).left ≫ m)
      (fun W f => s z W f - ptOf V d (u.ex z).left W f) ∧
      ∀ r, s z ⊤ (constFn p ⊤ r) - ptOf V d (u.ex z).left ⊤ (constFn p ⊤ r) = 0 := fun z hz =>
    ⟨ptDer_sub (hs.der z) (ptDer_ptOf hd (u.ex z).left hz), fun r => by
      rw [hs.base z r, ptOf_const hd (u.ex z).left (hq z) hz r, sub_self]⟩
  obtain ⟨w, hw, hrep⟩ := GlobalTheory.T.exists_differentiableOn_verticalVectorField P₀ u Hm χ hu R x₀ X p m hp hm P₀.g (dom u m V) id
    (fun z W f => s z W f - ptOf V d (u.ex z).left W f) hdomV differentiable_id hpt
    (fun W f => ((hs.hol W f).mono fun z hz => hz.2).sub
      (((u.hol (m ⁻¹ᵁ (W ⊓ V)) (d (W ⊓ V) (resG X inf_le_left f))).2).mono fun z hz a ha => ⟨hz.2 ha, hz.1 ha⟩))
  refine ⟨w, hw, fun l z hz => ?_, fun W hWV f z hz => ?_⟩
  · have hzl : z + l ∈ dom u m V := by
      show ⊤ ≤ ((u.ex (z + l)).left ≫ m) ⁻¹ᵁ V
      rw [hex]; exact hz
    have hfn : ∀ W (f : Γ(X, W)), fderiv ℂ (fn u m W f) (z + l) = fderiv ℂ (fn u m W f) z := by
      intro W f
      have e : (fun x => fn u m W f (x + l)) = fn u m W f := by
        funext x; simp only [fn, hex]
      rw [← fderiv_comp_add_right, e]
    refine ((GlobalTheory.T.existsUnique_uniformising_vector_vertical_tangent P₀ u Hm χ hu R x₀ X p m hp hm z _ (hpt z hz).1 (hpt z hz).2).unique
      (fun W f hzW => ?_) (fun W f hzW => ?_))
    · have hzlW : z + l ∈ dom u m W := by
        show ⊤ ≤ ((u.ex (z + l)).left ≫ m) ⁻¹ᵁ W
        rw [hex]; exact hzW
      have e := hrep (z + l) hzl W f hzlW
      simp only [id, hex, hfn] at e
      rw [← e, hs.per l W f z hzW, Matrix.zero_mulVec, map_zero, add_zero]
    · exact hrep z hz W f hzW
  · have e := hrep z (fun a ha => hWV (hz ha)) W f hz
    rw [ptOf_of_le hd (u.ex z).left hWV hz f] at e
    simp only [id] at e
    rw [← e]; ring

private theorem valAt'_sub' {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (U : X.Opens) (hx : ⊤ ≤ x ⁻¹ᵁ U)
    (a b : Γ(X, U)) : valAt' x U (a - b) = valAt' x U a - valAt' x U b := by
  simp only [valAt', dif_pos hx, valAt, map_sub]

private theorem valAt'_add_of_top_le {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (U : X.Opens) (hx : ⊤ ≤ x ⁻¹ᵁ U)
    (a b : Γ(X, U)) : valAt' x U (a + b) = valAt' x U a + valAt' x U b := by
  simp only [valAt', dif_pos hx, valAt, map_add]

private theorem valAt'_mul_of_top_le {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (U : X.Opens) (hx : ⊤ ≤ x ⁻¹ᵁ U)
    (a b : Γ(X, U)) : valAt' x U (a * b) = valAt' x U a * valAt' x U b := by
  simp only [valAt', dif_pos hx, valAt, map_mul]

private theorem valAt'_finset_sum {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (U : X.Opens) (hx : ⊤ ≤ x ⁻¹ᵁ U)
    {κ : Type} (s : Finset κ) (F : κ → Γ(X, U)) : valAt' x U (∑ i ∈ s, F i) = ∑ i ∈ s, valAt' x U (F i) := by
  simp only [valAt', dif_pos hx, valAt, map_sum]

private theorem valAt'_comp' {Y X : Scheme.{0}} (y : Sp ℂ ⟶ Y) (m : Y ⟶ X) (W : X.Opens) (f : Γ(X, W)) :
    valAt' (y ≫ m) W f = valAt' y (m ⁻¹ᵁ W) ((m.app W).hom f) := by
  by_cases hy : ⊤ ≤ (y ≫ m) ⁻¹ᵁ W
  · have hy' : ⊤ ≤ y ⁻¹ᵁ (m ⁻¹ᵁ W) := hy
    rw [valAt', dif_pos hy, valAt', dif_pos hy', valAt, valAt]
    first
      | (rw [Scheme.comp_appLE]; rfl)
      | simp [Scheme.comp_appLE]
      | simp [Scheme.Hom.comp_appLE]
  · have hy' : ¬ ⊤ ≤ y ⁻¹ᵁ (m ⁻¹ᵁ W) := hy
    rw [valAt', dif_neg hy, valAt', dif_neg hy']

private theorem valAt'_resG_of_top_le {X : Scheme.{0}} (x : Sp ℂ ⟶ X) {U V : X.Opens} (h : V ≤ U) (hx : ⊤ ≤ x ⁻¹ᵁ V)
    (a : Γ(X, U)) : valAt' x V (resG X h a) = valAt' x U a := by
  have hx' : ⊤ ≤ x ⁻¹ᵁ U := fun p hp => h (hx hp)
  rw [valAt', dif_pos hx, valAt', dif_pos hx', valAt, valAt, resG]
  congr 1
  exact congrArg (fun φ => φ.hom a) (x.map_appLE hx (homOfLE h).op)

private theorem continuousLinearMap_apply_eq_sum_single {n : ℕ} (φ : (Fin n → ℂ) →L[ℂ] ℂ) (w : Fin n → ℂ) :
    φ w = ∑ b, w b * φ (Pi.single b 1) := by
  conv_lhs => rw [← Finset.univ_sum_single w]
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [show Pi.single a (w a) = w a • (Pi.single a 1 : Fin n → ℂ) by
    ext j; by_cases hj : j = a <;> simp [hj], map_smul, smul_eq_mul]

end GlobalTheory.KS.ZeroClass

namespace GlobalTheory.KS
open ZeroClass

theorem regular_of_periods_zero : Out.Laws → ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ D s, IsDer x₀ D → KSRel u p m D 0 s → ∀ W₀, IsAffineOpen W₀ → ∀ W, W ≤ W₀ → ∀ f : Γ(X, W), ∃ a : Γ(P₀.A.left, m ⁻¹ᵁ W), ∀ z ∈ dom u m W, valAt' (u.ex z).left (m ⁻¹ᵁ W) a = s z W f := by
  intro hL P₀ u Hm χ hu R _ x₀ X p m hp hm D s hD hs W₀ hW₀ W hWW₀ f
  choose dd hdd using fun i : X.affineOpens =>
    exists_locDer_of_smooth R x₀ P₀.A.left X P₀.A.hom p m D i.1 hp hm.w hD i.2
  choose ww hww hper hrep using fun i : X.affineOpens => exists_periodic_vector hu hp hm hs (hdd i)
  choose cc hcc using fun i j : X.affineOpens =>
    locDer_regular_coeff P₀ u Hm χ hu R x₀ X p m hp hm _ _ (locDer_sub (hdd i) (hdd j))
  have hrel : ∀ (i j : X.affineOpens) z, z ∈ dom u m (i.1 ⊓ j.1) →
      ww j z - ww i z = fun a => valAt' (u.ex z).left (m ⁻¹ᵁ (i.1 ⊓ j.1)) (cc i j a) := by
    intro i j z hz
    refine vector_ext hu hp hm hz fun W' hW' hzW' f' => ?_
    have e1 := hrep i W' (hW'.trans inf_le_left) f' z hzW'
    have e2 := hrep j W' (hW'.trans inf_le_right) f' z hzW'
    have e3 := hcc i j W' hW' f' z hzW'
    rw [valAt'_sub' (u.ex z).left (m ⁻¹ᵁ W') hzW'] at e3
    rw [map_sub, ← e3]
    linear_combination e1 - e2
  have hcov : ⨆ i : X.affineOpens, m ⁻¹ᵁ i.1 = ⊤ := by
    refine eq_top_iff.mpr fun y _ => ?_
    have hy : m.base y ∈ (⨆ i : X.affineOpens, (i.1 : X.Opens)) := by
      rw [iSup_affineOpens_eq_top X]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  let i₀ : X.affineOpens := ⟨W₀, hW₀⟩
  have hcob : ∀ a : Fin P₀.g, ∃ e : Γ(P₀.A.left, m ⁻¹ᵁ W₀), ∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (m ⁻¹ᵁ W₀) →
      valAt' (u.ex z).left (m ⁻¹ᵁ W₀) e = ww i₀ z a := fun a =>
    algebraic_coboundary_of_holomorphic_coboundary hL P₀ u Hm χ hu X.affineOpens (fun i => m ⁻¹ᵁ i.1)
      (fun i j => cc i j a) (fun i z => ww i z a) hcov
      (fun i => ⟨(differentiableOn_pi.mp (hww i)) a, fun l z hz => congrFun (hper i l z hz) a⟩)
      (fun i j z hz => (congrFun (hrel i j z hz) a).symm) i₀
  choose ee hee using hcob
  choose δ hδ hδv using fun b : Fin P₀.g => invariant_field_algebraic P₀ u Hm χ hu (Pi.single b 1)
  have hW' : m ⁻¹ᵁ W ≤ m ⁻¹ᵁ W₀ := fun y hy => hWW₀ hy
  refine ⟨dd i₀ W f + ∑ b, resG P₀.A.left hW' (ee b) *
    (show Γ(P₀.A.left, m ⁻¹ᵁ W) from δ b (m ⁻¹ᵁ W) ((m.app W).hom f)), fun z hz => ?_⟩
  have hz0 : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (m ⁻¹ᵁ W₀) := fun y hy => hWW₀ (hz hy)
  have hzW : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (m ⁻¹ᵁ W) := hz
  rw [hrep i₀ W hWW₀ f z hz, valAt'_add_of_top_le _ _ hzW, valAt'_finset_sum _ _ hzW]
  congr 1
  rw [continuousLinearMap_apply_eq_sum_single (fderiv ℂ (fn u m W f) z) (ww i₀ z)]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hv : valAt' (u.ex z).left (m ⁻¹ᵁ W) (show Γ(P₀.A.left, m ⁻¹ᵁ W) from δ b (m ⁻¹ᵁ W) ((m.app W).hom f)) =
      fderiv ℂ (fun z' => valAt' (u.ex z').left (m ⁻¹ᵁ W) ((m.app W).hom f)) z (Pi.single b 1) :=
    hδv b (m ⁻¹ᵁ W) ((m.app W).hom f) z hzW
  have efn : (fun z' => valAt' (u.ex z').left (m ⁻¹ᵁ W) ((m.app W).hom f)) = fn u m W f :=
    funext fun z' => (valAt'_comp' _ _ _ _).symm
  rw [valAt'_mul_of_top_le _ _ hzW, valAt'_resG_of_top_le _ hW' hzW, hee b z hz0, hv, efn]

end GlobalTheory.KS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HomExtOfLin
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.SharpObj

section Unif

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem ex_zero : u.ex 0 = 1 := (u.ker 0).mpr u.Λ.zero_mem

def exHom : Multiplicative (Fin g → ℂ) →* (𝟙_ (Over (Sp ℂ)) ⟶ A) :=
  MonoidHom.mk' (fun z => u.ex z.toAdd) fun z w => u.ex_add _ _

theorem ex_zsmul (n : ℤ) (z : Fin g → ℂ) : u.ex (n • z) = u.ex z ^ n := by
  have h := map_zpow (exHom u) (Multiplicative.ofAdd z) n
  rw [← ofAdd_zsmul] at h
  simpa [exHom] using h

theorem ex_nsmul (n : ℕ) (z : Fin g → ℂ) : u.ex (n • z) = u.ex z ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero]; exact ex_zero u
  | succ n ih => rw [succ_nsmul, u.ex_add, ih, pow_succ]

theorem ex_sum [IsCommMonObj A] {I : Type} [Fintype I] (z : I → Fin g → ℂ) : u.ex (∑ i, z i) = ∏ i, u.ex (z i) := by
  classical
  have key : ∀ s : Finset I, u.ex (∑ i ∈ s, z i) = ∏ i ∈ s, u.ex (z i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty, Finset.prod_empty]; exact ex_zero u
    | @insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, u.ex_add, ih]
  exact key Finset.univ

end Unif

variable (laws : Out.Laws) (laws2 : Out.Laws2)
  (hc : ∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen)
  (hT : ThetaUnifAV)
include laws laws2 hc hT

theorem hom_ext_of_lin (P P' : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (u' : HolUnif P'.A P'.L P'.g)
    (F : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P'.g → ℂ)) (f f' : P.A ⟶ P'.A) (hf : ∀ z, u'.ex (F z) = u.ex z ≫ f)
    (hf' : ∀ z, u'.ex (F z) = u.ex z ≫ f') (h1 : IsMonHom f) : f = f' := by
  have e : ∀ B : Over (Sp ℂ), ∀ [GrpObj B], (η[B] : 𝟙_ _ ⟶ B) = 1 := fun B _ => by rw [Hom.one_def]; simp
  have h2 : IsMonHom f' := laws.rigidity _ _ _ P.isAb P'.isAb f' (by
    rw [e, e, ← ex_zero u, ← hf', map_zero, ex_zero])
  refine (GlobalTheory.T.existsUnique_isMonHom_of_linearMap_lattice_anyDim laws laws2 hc hT P P' _ _ u u' F fun z hz => ?_).unique ⟨h1, hf⟩ ⟨h2, hf'⟩
  rw [← u'.ker, hf, (u.ker z).2 hz, MonObj.one_comp]

theorem exists_proj (P P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (u₀ : HolUnif P₀.A P₀.L P₀.g)
    {I : Type} [Fintype I] (σ : I × Fin P₀.g ≃ Fin P.g)
    (hΛ : ∀ z, z ∈ u.Λ ↔ ∀ i, (fun j => z (σ (i, j))) ∈ u₀.Λ) :
    ∃ pr : I → (P.A ⟶ P₀.A), (∀ i, IsMonHom (pr i)) ∧ (∀ i z, u₀.ex (fun j => z (σ (i, j))) = u.ex z ≫ pr i) ∧
      ∀ (T : Over (Sp ℂ)) (y : I → (T ⟶ P₀.A)), ∃! x : T ⟶ P.A, ∀ i, x ≫ pr i = y i := by
  classical
  letI := P.isAb.comm
  letI := P₀.isAb.comm
  let R : I → (Fin P.g → ℂ) →ₗ[ℂ] (Fin P₀.g → ℂ) := fun i => LinearMap.funLeft ℂ ℂ fun j => σ (i, j)
  let S : I → (Fin P₀.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ) := fun i =>
    LinearMap.pi fun a => if (σ.symm a).1 = i then LinearMap.proj (σ.symm a).2 else 0
  have hRS : ∀ i i' z, R i (S i' z) = if i = i' then z else 0 := fun i i' z => by
    ext j
    by_cases e : i = i' <;> simp [R, S, LinearMap.funLeft_apply, e]
  have hSR : ∀ z, ∑ i, S i (R i z) = z := fun z => by
    ext a
    obtain ⟨⟨i, j⟩, rfl⟩ := σ.surjective a
    rw [Finset.sum_apply, Finset.sum_eq_single i]
    · simp [R, S, LinearMap.funLeft_apply]
    · intro b _ hb
      simp [S, hb.symm]
    · simp
  choose pr hpr using fun i => (GlobalTheory.T.existsUnique_isMonHom_of_linearMap_lattice_anyDim laws laws2 hc hT P P₀ _ _ u u₀ (R i) fun z hz => (hΛ z).1 hz i).exists
  choose inc hinc using fun i => (GlobalTheory.T.existsUnique_isMonHom_of_linearMap_lattice_anyDim laws laws2 hc hT P₀ P _ _ u₀ u (S i) fun z hz => (hΛ _).2 fun i' => by
    change R i' (S i z) ∈ _
    rw [hRS]
    split_ifs
    exacts [hz, u₀.Λ.zero_mem]).exists
  haveI := fun i => (hpr i).1
  haveI := fun i => (hinc i).1
  have e1 : ∀ i, inc i ≫ pr i = 𝟙 _ := fun i =>
    hom_ext_of_lin laws laws2 hc hT P₀ P₀ u₀ u₀ LinearMap.id _ _ (fun z => by
      rw [← Category.assoc, ← (hinc i).2, ← (hpr i).2, hRS]; simp) (fun z => by simp) inferInstance
  have e2 : ∀ i i', i ≠ i' → inc i ≫ pr i' = 1 := fun i i' hi =>
    hom_ext_of_lin laws laws2 hc hT P₀ P₀ u₀ u₀ 0 _ _ (fun z => by
      rw [← Category.assoc, ← (hinc i).2, ← (hpr i').2, hRS]; simp [hi.symm])
      (fun z => by simp [ex_zero]) inferInstance
  have e3 : 𝟙 P.A = ∏ i, pr i ≫ inc i :=
    hom_ext_of_lin laws laws2 hc hT P P u u LinearMap.id _ _ (fun z => by simp) (fun z => by
      rw [PowMatrixLinear.comp_prod]
      simp only [← Category.assoc, ← (hpr _).2, ← (hinc _).2]
      rw [← ex_sum, hSR]; rfl) inferInstance
  refine ⟨pr, fun i => (hpr i).1, fun i => (hpr i).2, fun T y => ⟨∏ i, y i ≫ inc i, fun i => ?_, fun x hx => ?_⟩⟩
  · rw [PowMatrixLinear.prod_comp, Finset.prod_eq_single i]
    · rw [Category.assoc, e1, Category.comp_id]
    · intro b _ hb
      rw [Category.assoc, e2 _ _ hb, MonObj.comp_one]
    · simp
  · rw [← Category.comp_id x, e3, PowMatrixLinear.comp_prod]
    simp only [← Category.assoc, hx]

end GlobalTheory.SharpObj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsFiniteAndSurjectiveOfFormIs
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

namespace GlobalTheory.FormFinite

open GlobalTheory.CechPic GlobalTheory.AmpleStabFinite

theorem lam_inv_eq {S : Scheme.{0}} {A T : Over S} [GrpObj A] [IsCommMonObj A] (m l : CechPic.Pic A.left) (s : A ⟶ A)
    [IsMonHom s] (h : ∀ u v : T ⟶ A, lam m u v = lam l u (v ≫ s)) {x y : T ⟶ A} (e : x ≫ s = y ≫ s) :
    lam m x⁻¹ x = lam m y y⁻¹ := by
  rw [h, e, ← h, lam_comm, h, GrpObj.inv_comp, e, ← GrpObj.inv_comp, ← h]

theorem isFinite_of_lam_eq {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A] [IsProper A.hom]
    {M : LB A.left} (hM : IsAmpleLB M) (l : CechPic.Pic A.left) (s : A ⟶ A) [IsMonHom s]
    (h : ∀ (T : Over (Sp K)) (u v : T ⟶ A), lam (cls M hM.isLB) u v = lam l u (v ≫ s)) : IsFinite s.left := by
  obtain ⟨n, -, N, t, hc, ha⟩ := hM.exists_cover
  have : IsProper (s.left ≫ A.hom) := by rw [Over.w s]; infer_instance
  have : IsProper s.left := .of_comp _ A.hom
  suffices LocallyQuasiFinite s.left from .of_isProper_of_locallyQuasiFinite _
  refine LocallyQuasiFinite.of_finite_preimage_singleton _ fun z => ?_
  rcases Set.eq_empty_or_nonempty (s.left ⁻¹' {z}) with h0 | ⟨a, hz⟩
  · rw [h0]; exact Set.finite_empty
  let k : Type := A.left.residueField a
  let y₀ : Spec (CommRingCat.of k) ⟶ A.left := A.left.fromSpecResidueField a
  let P : Over (Sp K) := Over.mk (y₀ ≫ A.hom)
  let y : P ⟶ A := Over.homMk y₀ rfl
  let π : pullback s.left (y₀ ≫ s.left) ⟶ A.left := pullback.fst _ _
  let q : pullback s.left (y₀ ≫ s.left) ⟶ Spec (CommRingCat.of k) := pullback.snd _ _
  have w : π ≫ s.left = q ≫ y₀ ≫ s.left := pullback.condition
  let F : Over (Sp K) := Over.mk (π ≫ A.hom)
  let x : F ⟶ A := Over.homMk π rfl
  let r : F ⟶ P := Over.homMk q (by
    change q ≫ y₀ ≫ A.hom = π ≫ A.hom
    rw [← Over.w s, reassoc_of% w])
  have : IsAffineHom (y₀ ≫ s.left) := .of_comp _ A.hom
  have : IsAffineHom π := MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom.{0})
    (IsPullback.of_hasPullback s.left (y₀ ≫ s.left)).flip this
  have key := lam_inv_eq _ l s (h F) (x := x) (y := r ≫ y) (Over.OverMorphism.ext w)
  have triv : ∀ (b : P ⟶ A) (c : CechPic.Pic A.left), CechPic.pull (r ≫ b).left c = 0 := fun b c => by
    rw [Over.comp_left, pull_comp, pull_spec_local (K := k) b.left, map_zero]
  have one : ∀ c : CechPic.Pic A.left, CechPic.pull (1 : F ⟶ A).left c = 0 := fun c => by
    rw [← MonObj.comp_one r, triv]
  simp only [lam, inv_mul_cancel, ← GrpObj.comp_inv, ← MonObj.comp_mul, one, triv] at key
  have : CompactSpace ↥(pullback s.left (y₀ ≫ s.left)) := QuasiCompact.compactSpace_of_compactSpace q
  have : (pullback s.left (y₀ ≫ s.left)).IsQuasiAffine := quasiAffine_of_pull_add π (x⁻¹).left
    (isLB_lbPow hM.isLB n) t hc ha (by
      have e : CechPic.pull x.left (cls M hM.isLB) + CechPic.pull (x⁻¹).left (cls M hM.isLB) = 0 := by
        linear_combination (norm := abel) - key
      change CechPic.pull x.left _ + CechPic.pull (x⁻¹).left _ = 0
      rw [cls_lbPow hM.isLB, map_nsmul, map_nsmul, ← nsmul_add, e, nsmul_zero])
  have : IsAffine (pullback s.left (y₀ ≫ s.left)) := isAffine_of_quasiAffine q
  have : IsFinite q := IsFinite.iff_isProper_and_isAffineHom.2 ⟨inferInstance, inferInstance⟩
  have hfin : (Set.univ : Set ↥(pullback s.left (y₀ ≫ s.left))).Finite :=
    (q.finite_preimage_singleton (IsLocalRing.closedPoint k)).subset fun t _ => Subsingleton.elim _ _
  refine (hfin.image π).subset fun b hb => ?_
  have e : s.left b = (y₀ ≫ s.left) (IsLocalRing.closedPoint k) := by
    have e₀ : y₀ (IsLocalRing.closedPoint k) = a := Scheme.fromSpecResidueField_apply a _
    exact (show s.left b = z from hb).trans ((show s.left a = z from hz).symm.trans (congrArg s.left e₀).symm)
  obtain ⟨c, hc, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := s.left) (g := y₀ ≫ s.left) b _ e
  exact ⟨c, trivial, hc⟩

theorem isFinite_and_surjective_of_formIs : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M : LB P.A.left) (s : P.A ⟶ P.A), M.IsLB → Out.RelAmple P.A M → FormIs P M s → IsFinite s.left ∧ Surjective s.left := by
  intro _ _ K _ _ P M s hM hA ⟨hs, H⟩
  have := P.isAb.proper
  have := P.isAb.comm
  have e := (cls_eq_iff (LB.isLB_linComb hM _ _) (LB.isLB_linComb P.isLB _ _)).2 H
  have e' := (cls_cube_two hM _ _ _).symm.trans (e.trans (cls_cube_two P.isLB _ _ _))
  have hf : IsFinite s.left :=
    isFinite_of_lam_eq (isAmpleLB_of_relAmple_of_isAffine P.A hM hA) (cls P.L P.isLB) s fun T u v => by
      simpa only [pull_lam, lift_fst, lift_snd, lift_snd_assoc] using congrArg (CechPic.pull (lift u v).left) e'
  exact ⟨hf, (flat_and_surjective_of_isFinite_abelianEnd
    forall_geometricallyIntegral_of_smooth_of_geometricallyConnected K P.A P.isAb s hs hf).2⟩

end GlobalTheory.FormFinite
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionEqOneOfTranslDiffTrivialModelStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_eq_one_of_translDiff_trivial_model : Laws → Laws2 → ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (P : PolAV (Sp K)) (B : Over (Sp V)) [GrpObj B] [IsCommMonObj B] (M : GlobalTheory.UU.CP B) (φ : P.A.left ⟶ B.left), IsAbelianScheme B → IsGrpPullback P.A B (spMap (algebraMap V K)) φ → LBIso P.L (M.L.L.pull φ) → IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (f : V →+* Ω), IsLocalHom f → ∀ n : ℕ, (n : Ω) ≠ 0 → ∀ x : Over.mk (spMap f) ⟶ B, x ^ n = 1 → GlobalTheory.AbLaw.Triv (translDiff B M.L.L x) → x = 1 := by
  first | exact @GlobalTheory.PrincipalModel.torsion_eq_one_of_triv | exact GlobalTheory.PrincipalModel.torsion_eq_one_of_triv | (intros; apply GlobalTheory.PrincipalModel.torsion_eq_one_of_triv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionSectionConstantFamilyDualNumbers
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS

theorem torsion_section_const : Out.Laws → ∀ (P₀ : Out.PolAV (Sp ℂ)), ∀ (A' : Over (Sp (DualNumber ℂ))) [GrpObj A'] (ρ : A'.left ⟶ P₀.A.left) (j : P₀.A.left ⟶ A'.left), IsConst A' P₀.A ρ j → ∀ (k : ℕ) (y : Out.baseOver (Sp (DualNumber ℂ)) ⟶ A') (y₀ : Out.baseOver (Sp ℂ) ⟶ P₀.A), k ≠ 0 → y ^ k = 1 → y₀ ^ k = 1 → (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ≫ y.left = y₀.left ≫ j → y.left ≫ ρ = (spMap (algebraMap ℂ (DualNumber ℂ))) ≫ y₀.left := by
  intro _ P₀ A' _ ρ j hc k y y₀ hk hy hy₀ hyj
  letI := P₀.isAb.comm
  have hu : IsUnit ((k : ℕ) : Γ(Sp ℂ, ⊤)) := by
    let e : Γ(Sp ℂ, ⊤) ≃+* ℂ := (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv
    refine (MulEquiv.isUnit_map e.toMulEquiv).mp ?_
    have he : e.toMulEquiv (k : Γ(Sp ℂ, ⊤)) = (k : ℂ) := map_natCast e k
    rw [he]
    exact (Nat.cast_ne_zero.mpr hk).isUnit
  exact GlobalTheory.ConstTheta.torsion_const hc.1 hc.2.2 hu y y₀ hy hy₀ hyj.symm

end GlobalTheory.KS
end

