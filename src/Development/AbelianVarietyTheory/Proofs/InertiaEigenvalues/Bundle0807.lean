import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CmHostRootComplexEqPmSqrt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0019
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsLocExtFinrankEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecTransportFieldIso
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0786
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NatCastMemPlaceAt
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0029
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtensionUnramifiedAtOnePlace
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0802
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0021
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0803
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsGrpPullbackOfLattice
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompRat.Inertia

open GlobalTheory.WeierstrassCurve GlobalTheory.UnifCoord GlobalTheory.PeriodicWeierstrass PeriodPair GlobalTheory.CompRat.Weber

theorem fibre_coord (W : WeierstrassCurve ℂ) (hb : W.b₂ = 0) {P₀ : Out.PolAV (Sp ℂ)} {ψ₀ : P₀.A.left ⟶ scheme W}
    [IsIso ψ₀] (hψ₀ : ψ₀ ≫ toSpec W = P₀.A.hom) (he : eSec P₀.A ≫ ψ₀ = zero W) {v : epsR ℂ ⟶ P₀.A}
    (hvt : IsTangent v) {h : IsUnimodularSol (W.map (algebraMap ℂ (DualNumber ℂ))) ![DualNumber.eps, -1, 0]}
    (hv : v.left ≫ ψ₀ = ptHom W (algebraMap ℂ (DualNumber ℂ)) ![DualNumber.eps, -1, 0] h) (f : ℂ →+* ℂ)
    (PC : Out.PolAV (Sp ℂ)) (hg1 : PC.g = 1) (u : HolUnif PC.A PC.L PC.g) (hu : IsThetaUnif u)
    {ψ : PC.A.left ⟶ P₀.A.left} (hψ : IsGrpPullback PC.A P₀.A (spMap f) ψ) :
    ∃ (w : Fin PC.g → ℂ) (L' : PeriodPair), w ≠ 0 ∧ (∀ z, z ∈ L'.lattice ↔ z • w ∈ u.Λ) ∧
      f W.c₄ = 12 * L'.g₂ ∧ f W.c₆ = 216 * L'.g₃ ∧
      ∀ z : ℂ, ∃ (P : Fin 3 → ℂ) (hP : IsUnimodularSol (W.map f) P),
        (u.ex (z • w)).left ≫ ψ ≫ ψ₀ = ptHom W f P hP ∧ (P 2 = 0 ↔ z ∈ L'.lattice) ∧
          (P 2 ≠ 0 → ℘[L'] z * P 2 = P 0) := by
  obtain ⟨v', hv't, hv'⟩ := exists_tangent_over f hψ hvt
  obtain ⟨w, hd, -⟩ := hu.choose_spec.choose_spec.choose_spec.2.1 v' hv't
  obtain ⟨h', h1, h2, h3⟩ := fibre_over_scheme W f hψ₀ he hv hψ hv'
  obtain ⟨hw, x, y, t, hP, hx, hy, hper, heq, ht, ht0, ht1, hty, hlim⟩ :=
    exists_coord_eq ℂ W f PC.A (ψ ≫ ψ₀) v' h' h1 h2 h3 PC.L PC.g u w hd
  obtain ⟨L', hL'⟩ := exists_periodPair_of_lattice_in_line PC.g u.Λ w hg1 hw u.discrete u.full
  have hset : (L'.lattice : Set ℂ) = {z | z • w ∈ u.Λ} := Set.ext hL'
  have key := invariants_eq_of_periodic_solution L' (W.map f) x y t 1 one_ne_zero (hset ▸ hx) (hset ▸ hy)
    (fun l hl => hper l ((hL' l).1 hl)) (fun z hz => heq z fun e => hz ((hL' z).2 e)) ht ht0 ht1 hty hlim
  have kx := x_eq_of_periodic_solution L' (W.map f) x y t 1 one_ne_zero (hset ▸ hx) (hset ▸ hy)
    (fun l hl => hper l ((hL' l).1 hl)) (fun z hz => heq z fun e => hz ((hL' z).2 e)) ht ht0 ht1 hty hlim
  simp only [one_pow, _root_.one_mul, WeierstrassCurve.map_c₄, WeierstrassCurve.map_c₆, WeierstrassCurve.map_b₂,
    hb, map_zero, zero_div, sub_zero] at key kx
  refine ⟨w, L', hw, hL', key.1, key.2.1, fun z => ?_⟩
  obtain ⟨P, hP, e1, e2, e3⟩ := hP z
  refine ⟨P, hP, e1, by rw [e2, hL'], fun h2 => ?_⟩
  rw [← e3 h2, kx _ fun hz => h2 (e2.2 ((hL' _).1 hz))]

theorem exists_hom_of_lattice (P Q : Out.PolAV (Sp ℂ)) (g1 : P.g = 1) (g2 : Q.g = 1) (u : HolUnif P.A P.L P.g)
    (u' : HolUnif Q.A Q.L Q.g) (hu : IsThetaUnif u) (hu' : IsThetaUnif u') (L : PeriodPair) (w : Fin P.g → ℂ)
    (w' : Fin Q.g → ℂ) (w0 : w ≠ 0) (w0' : w' ≠ 0) (hΛ : ∀ z, z ∈ L.lattice ↔ z • w ∈ u.Λ)
    (hΛ' : ∀ z, z ∈ L.lattice ↔ z • w' ∈ u'.Λ) :
    ∃ f : P.A ⟶ Q.A, IsMonHom f ∧ ∀ z : ℂ, u'.ex (z • w') = u.ex (z • w) ≫ f := by
  obtain ⟨Hm, χ, Ef, hA, -, -, hθ, hE, hEb⟩ := hu
  obtain ⟨Hm', χ', Ef', hA', -, -, hθ', hE', hEb'⟩ := hu'
  have hH := hermForm_principal_dim_one _ u.Λ w L Hm Ef g1 w0 hΛ hA.1 (hA.2.1 w w0) hE hEb
  have hH' := hermForm_principal_dim_one _ u'.Λ w' L Hm' Ef' g2 w0' hΛ' hA'.1 (hA'.2.1 w' w0') hE' hEb'
  obtain ⟨c, hc, hc1⟩ := EllipticHom.exists_coord g1 w0
  let F : (Fin P.g → ℂ) →ₗ[ℂ] (Fin Q.g → ℂ) := c.smulRight w'
  have hF : ∀ x, F x = c x • w' := fun x => rfl
  obtain ⟨f, hf, hFf⟩ := exists_hom_of_linear_scaling_hermForm P Q u u' Hm χ Hm' χ' hA hA'
    (fun k => (hθ k).2) (fun k => (hθ' k).1) F 1
    (fun l hl => by
      rw [hF, ← hΛ']
      exact (hΛ _).2 (by rwa [hc]))
    (fun x y => by
      have e := hH (c x) (c y)
      rw [hc, hc] at e
      rw [hF, hF, hH', e, Nat.cast_one, _root_.one_mul])
  refine ⟨f, hf, fun z => ?_⟩
  rw [← hFf, hF, map_smul, hc1, smul_eq_mul, _root_.mul_one]

theorem exists_isGrpPullback_of_lattice (P Q : Out.PolAV (Sp ℂ)) (g1 : P.g = 1) (g2 : Q.g = 1)
    (u : HolUnif P.A P.L P.g)
    (u' : HolUnif Q.A Q.L Q.g) (hu : IsThetaUnif u) (hu' : IsThetaUnif u') (L : PeriodPair) (w : Fin P.g → ℂ)
    (w' : Fin Q.g → ℂ) (w0 : w ≠ 0) (w0' : w' ≠ 0) (hΛ : ∀ z, z ∈ L.lattice ↔ z • w ∈ u.Λ)
    (hΛ' : ∀ z, z ∈ L.lattice ↔ z • w' ∈ u'.Λ) :
    ∃ φ : P.A.left ⟶ Q.A.left, IsGrpPullback P.A Q.A (𝟙 _) φ := by
  obtain ⟨f, hf, e⟩ := exists_hom_of_lattice P Q g1 g2 u u' hu hu' L w w' w0 w0' hΛ hΛ'
  obtain ⟨f', hf', e'⟩ := exists_hom_of_lattice Q P g2 g1 u' u hu' hu L w' w w0' w0 hΛ' hΛ
  obtain ⟨c, hc, -⟩ := EllipticHom.exists_coord g1 w0
  obtain ⟨c', hc', -⟩ := EllipticHom.exists_coord g2 w0'
  have := P.isAb.smooth
  have := Q.isAb.smooth
  have := P.isAb.proper
  have := Q.isAb.proper
  have : IsReduced P.A.left := isReduced_of_smooth_complex _ P.A.hom inferInstance
  have : IsReduced Q.A.left := isReduced_of_smooth_complex _ Q.A.hom inferInstance
  let i : P.A ≅ Q.A :=
    { hom := f
      inv := f'
      hom_inv_id := ComplexPoints.over_hom_ext_of_complexPoints fun x => by
        obtain ⟨z, rfl⟩ := u.ex_onto x
        rw [← hc z, ← Category.assoc, ← e, ← e', Category.comp_id]
      inv_hom_id := ComplexPoints.over_hom_ext_of_complexPoints fun x => by
        obtain ⟨z, rfl⟩ := u'.ex_onto x
        rw [← hc' z, ← Category.assoc, ← e', ← e, Category.comp_id] }
  have : IsMonHom i.hom := hf
  exact ⟨_, isGrpPullback_of_iso i⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem mem_iff (C : Curve H) {L : PeriodPair} (hL : ∀ x, x ∈ L.lattice ↔ ∃ s, x = wC H s) (z : ℂ) :
    z ∈ L.lattice ↔ (fun _ => C.c * z : Fin C.P.g → ℂ) ∈ C.u.Λ := by
  have i : Fin C.P.g := ⟨0, by rw [C.g_eq]; omega⟩
  rw [hL, exists_wC_iff, C.lat]
  exact ⟨fun ⟨m, n, h⟩ => ⟨m, n, by rw [h]⟩, fun ⟨m, n, h⟩ => ⟨m, n, mul_left_cancel₀ C.c_ne (congrFun h i)⟩⟩

theorem curve_coord (C : Curve H) {L : PeriodPair} (hL : ∀ x, x ∈ L.lattice ↔ ∃ s, x = wC H s)
    (W : WeierstrassCurve ℂ) (hb : W.b₂ = 0) {P₀ : Out.PolAV (Sp ℂ)} {ψ₀ : P₀.A.left ⟶ scheme W}
    [IsIso ψ₀] (hψ₀ : ψ₀ ≫ toSpec W = P₀.A.hom) (he : eSec P₀.A ≫ ψ₀ = zero W) {v : epsR ℂ ⟶ P₀.A}
    (hvt : IsTangent v) {h : IsUnimodularSol (W.map (algebraMap ℂ (DualNumber ℂ))) ![DualNumber.eps, -1, 0]}
    (hv : v.left ≫ ψ₀ = ptHom W (algebraMap ℂ (DualNumber ℂ)) ![DualNumber.eps, -1, 0] h) (f : ℂ →+* ℂ)
    {ψ : C.P.A.left ⟶ P₀.A.left} (hψ : IsGrpPullback C.P.A P₀.A (spMap f) ψ) :
    ∃ lam : ℂ, lam ≠ 0 ∧ ∀ z : ℂ, ∃ (P : Fin 3 → ℂ) (hP : IsUnimodularSol (W.map f) P),
        C.pt z ≫ ψ ≫ ψ₀ = ptHom W f P hP ∧ (P 2 = 0 ↔ z ∈ L.lattice) ∧
          (P 2 ≠ 0 → lam * ℘[L] z * P 2 = P 0) := by
  obtain ⟨w, L', hw, hL', -, -, hP⟩ := fibre_coord W hb hψ₀ he hvt hv f C.P C.g_eq C.u C.theta hψ
  obtain ⟨c, hc, -⟩ := EllipticHom.exists_coord C.g_eq hw
  set m := c fun _ => C.c with hm
  have e : ∀ z : ℂ, (fun _ => C.c * z : Fin C.P.g → ℂ) = (m * z) • w := fun z => by
    rw [_root_.mul_comm m, ← smul_smul, hm, hc]
    funext _
    simp [_root_.mul_comm]
  have hh : IsHomothetic m L L' := fun x => by rw [hL', ← e, ← mem_iff C hL]
  refine ⟨(m ^ 2)⁻¹, inv_ne_zero (pow_ne_zero _ hh.ne_zero), fun z => ?_⟩
  obtain ⟨P, hP, e1, e2, e3⟩ := hP (m * z)
  refine ⟨P, hP, by unfold Curve.pt; rw [e]; exact e1, by rw [e2, hh], fun h2 => ?_⟩
  rw [← e3 h2, hh.weierstrassP_mul]

theorem exists_multiplier (C : Curve H) {L : PeriodPair} (hL : ∀ x, x ∈ L.lattice ↔ ∃ s, x = wC H s)
    {τ : ℂ ≃+* ℂ} {io : C.P.A.left ⟶ C.P.A.left} (h : IsGrpPullback C.P.A C.P.A (spMap (τ : ℂ →+* ℂ)) io) :
    ∃ a : ℂ, ∀ z z', C.pt z ≫ io = spMap (τ : ℂ →+* ℂ) ≫ C.pt z' → z' ∉ L.lattice →
      z ∉ L.lattice ∧ τ (℘[L] z') = a * ℘[L] z := by
  let W := latticeCurve L
  have hb : W.b₂ = 0 := by simp [W, latticeCurve, WeierstrassCurve.b₂]
  have h4 : W.c₄ = 12 * L.g₂ := latticeCurve_c₄ L
  have h6 : W.c₆ = 216 * L.g₃ := by
    simp only [W, latticeCurve, WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
    ring
  have hid : spMap (RingHom.id ℂ) = 𝟙 (Sp ℂ) := Spec.map_id (CommRingCat.of ℂ)
  obtain ⟨P₀, ψ₀, v, hg, hiso, hψ₀, he, ⟨hs, hv⟩, hlie⟩ := exists_polAV ℂ W (latticeCurve_Δ_ne_zero L).isUnit
  obtain ⟨u, hu⟩ := exists_isThetaUnif thetaUnifAV_all P₀
  have : IsMonHom (Iso.refl P₀.A).hom := inferInstanceAs (IsMonHom (𝟙 _))
  obtain ⟨w, L', hw, hL', e4, e6, -⟩ := fibre_coord W hb hψ₀ he (hlie.1 0) hv (RingHom.id ℂ) P₀ hg u hu
    ((isGrpPullback_of_iso (Iso.refl P₀.A)).congr hid.symm rfl)
  have eL : L'.lattice = L.lattice :=
    lattice_eq_of_g₂_eq_of_g₃_eq (by rw [RingHom.id_apply, h4] at e4; linear_combination -e4 / 12)
      (by rw [RingHom.id_apply, h6] at e6; linear_combination -e6 / 216)
  obtain ⟨φ, hφ⟩ := exists_isGrpPullback_of_lattice C.P P₀ C.g_eq hg C.u u C.theta hu L (fun _ => C.c) w
    (fun e => C.c_ne (congrFun e ⟨0, by rw [C.g_eq]; omega⟩)) hw
    (fun z => by
      rw [mem_iff C hL]
      congr! 2
      simp [_root_.mul_comm])
    (fun z => by rw [← eL, hL'])
  obtain ⟨l₁, hl₁, hQ⟩ := curve_coord C hL W hb hψ₀ he (hlie.1 0) hv (RingHom.id ℂ) (hφ.congr hid.symm rfl)
  obtain ⟨l₂, -, hP⟩ := curve_coord C hL W hb hψ₀ he (hlie.1 0) hv (τ : ℂ →+* ℂ)
    ((h.comp hφ).congr (Category.comp_id _) rfl)
  have ht : τ l₁ ≠ 0 := by simpa using hl₁
  refine ⟨l₂ / τ l₁, fun z z' e hz' => ?_⟩
  obtain ⟨P, hP1, a1, a2, a3⟩ := hP z
  obtain ⟨Q, hQ1, b1, b2, b3⟩ := hQ z'
  have e2 : C.pt z ≫ (io ≫ φ) ≫ ψ₀ = spMap (τ : ℂ →+* ℂ) ≫ C.pt z' ≫ φ ≫ ψ₀ := by
    simp only [← Category.assoc, e]
  have hτ : (τ : ℂ →+* ℂ).comp (RingHom.id ℂ) = (τ : ℂ →+* ℂ) := rfl
  have hQ2 := hQ1.map_comp (τ : ℂ →+* ℂ)
  rw [hτ] at hQ2
  rw [a1, b1, SpecMap_ptHom, ptHom_congr W _ _ _ hτ rfl hQ2, ptHom_eq_ptHom_iff] at e2
  obtain ⟨v, hv⟩ := e2
  have v0 : τ (Q 0) = v * P 0 := congrFun hv 0
  have v2 : τ (Q 2) = v * P 2 := congrFun hv 2
  have hQ0 : Q 2 ≠ 0 := fun h => hz' (b2.1 h)
  have hQ0' : τ (Q 2) ≠ 0 := by simpa using hQ0
  have hP0 : P 2 ≠ 0 := right_ne_zero_of_mul (v2 ▸ hQ0')
  refine ⟨fun h => hP0 (a2.2 h), ?_⟩
  have e3 : τ l₁ * τ (℘[L] z') * τ (Q 2) = l₂ * ℘[L] z * τ (Q 2) := by
    rw [← map_mul, ← map_mul, b3 hQ0, v0, v2, ← a3 hP0]
    ring
  have e4 := mul_right_cancel₀ hQ0' e3
  field_simp
  linear_combination e4

end GlobalTheory.CompRat.Inertia
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocExtProper
section
noncomputable section
open NumberField IsDedekindDomain ValuativeRel
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.DelEps
variable {Ω : Type} [Field Ω] {A : ValuationSubring Ω}
variable {K : Type} [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] {v : HeightOneSpectrum (𝓞 K)}

theorem trW_mk {h : IsPlaceOver A v} {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (a : WDRep h V) (σ : Weil h) :
    trW (WD.mk a) σ = LinearMap.trace ℂ V (a.ρ σ) := by
  obtain ⟨e, he, -⟩ := WD.mk_eq_mk.1 (Classical.choose_spec (Classical.choose_spec (WD.mk a).exists_rep))
  unfold trW
  rw [← LinearMap.trace_conj' _ e]
  congr 1
  ext x
  simp [LinearEquiv.conj_apply, he]

def LocExt.self (h : IsPlaceOver A v) : LocExt h := ⟨K, v, h, isLocalExt_self h⟩

theorem trW_of_induces_self {h : IsPlaceOver A v} {x y : WD h} (H : Induces x y) (σ : Weil h) : trW y σ = trW x σ := by
  obtain ⟨m, n, a, b, j, rfl, rfl, hn, hj, hs⟩ := H
  have hj' : ∀ σ u, j (a.ρ σ u) = b.ρ σ (j u) := fun σ => hj σ σ fun _ => rfl
  have hsurj : Function.Surjective j := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hs, Submodule.span_le]
    rintro _ ⟨⟨τ, u⟩, rfl⟩
    exact ⟨_, hj' τ u⟩
  have hmn : n = m := by simpa using hn
  subst hmn
  have hb : Function.Bijective j := ⟨LinearMap.injective_iff_surjective.2 hsurj, hsurj⟩
  rw [trW_mk, trW_mk, ← LinearMap.trace_conj' (a.ρ σ) (LinearEquiv.ofBijective j hb)]
  congr 1
  refine LinearMap.ext fun x => ?_
  obtain ⟨u, rfl⟩ := (LinearEquiv.ofBijective j hb).surjective x
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  exact (hj' σ u).symm

theorem trW_indOf_self {h : IsPlaceOver A v} (ξ : Weil h →* ℂˣ) (hξ : GlobalTheory.WeilDeligne.IsSmooth ξ) (σ : Weil h) :
    trW (indOf (LocExt.self h) ξ hξ) σ = trW (WD.lpOfChar h ξ hξ) σ := by
  have hy : ∃ y : WD h, Induces (WD.lpOfChar (LocExt.self h).h' ξ hξ) y := ⟨_, induces_self _⟩
  have e : indOf (LocExt.self h) ξ hξ = hy.choose := dif_pos hy
  exact (congrArg (trW · σ) e).trans (trW_of_induces_self (h := h) hy.choose_spec σ)

end GlobalTheory.DelEps
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNormEqOfMemClosure
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KurValue

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GeoTie Polynomial

theorem exists_norm_eq_of_mem_closure {K : Type*} [NormedField K] [IsUltrametricDist K] {S : Set K} {x : K}
    (hx : x ∈ closure S) (h0 : x ≠ 0) : ∃ y ∈ S, ‖x‖ = ‖y‖ := by
  obtain ⟨y, hy, hd⟩ := Metric.mem_closure_iff.1 hx ‖x‖ (norm_pos_iff.2 h0)
  refine ⟨y, hy, ?_⟩
  rw [dist_comm, dist_eq_norm] at hd
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := y - x) (y := x) hd.ne
  rw [sub_add_cancel, max_eq_right hd.le] at this
  exact this.symm

variable {p : ℕ} [Fact p.Prime]

theorem mem_range_of_isIntegral {x : ℂ_[p]} (hx : IsIntegral (PadicAlgCl p) x) :
    x ∈ (algebraMap (PadicAlgCl p) ℂ_[p]).range :=
  minpoly.mem_range_of_degree_eq_one _ x (IsAlgClosed.degree_eq_one_of_irreducible _ (minpoly.irreducible hx))

theorem exists_lift {F : Type} [Field F] [NumberField F] (φ : F →+* ℂ_[p]) :
    ∃ ψ : F →+* PadicAlgCl p, ∀ a, algebraMap (PadicAlgCl p) ℂ_[p] (ψ a) = φ a := by
  have h : ∀ a : F, φ a ∈ (algebraMap (PadicAlgCl p) ℂ_[p]).range := fun a => by
    have h1 : IsIntegral ℚ (φ a) := (Algebra.IsIntegral.isIntegral (R := ℚ) a).map φ.toRatAlgHom
    exact mem_range_of_isIntegral h1.tower_top
  choose f hf using h
  have hi := (algebraMap (PadicAlgCl p) ℂ_[p]).injective
  refine ⟨⟨⟨⟨f, hi ?_⟩, fun a b => hi ?_⟩, hi ?_, fun a b => hi ?_⟩, hf⟩
  · rw [hf, map_one, map_one]
  · simp only [map_mul, hf]
  · simp only [map_zero, hf]
  · simp only [map_add, hf]

theorem exists_finite {F : Type} [Field F] [NumberField F] (ψ : F →+* PadicAlgCl p) :
    ∃ K : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] K ∧ (∀ a, ψ a ∈ K) ∧
      ∀ x ∈ K, ∃ a, ‖x‖ = ‖ψ a‖ := by
  let b := Module.finBasis ℚ F
  refine ⟨IntermediateField.adjoin ℚ_[p] (Set.range fun i => ψ (b i)), ?_, fun a => ?_, fun x hx => ?_⟩
  · exact IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  · rw [← b.sum_repr a, map_sum]
    refine sum_mem fun i _ => ?_
    rw [Rat.smul_def, map_mul, map_ratCast]
    exact mul_mem (SubfieldClass.ratCast_mem _ _) (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
  · let M : IntermediateField ℚ_[p] (PadicAlgCl p) :=
      ψ.fieldRange.topologicalClosure.toIntermediateField fun r => by
        have hc : IsClosed {r : ℚ_[p] | algebraMap ℚ_[p] (PadicAlgCl p) r ∈ ψ.fieldRange.topologicalClosure} :=
          (Subfield.isClosed_topologicalClosure _).preimage (continuous_algebraMap _ _)
        refine (Padic.denseRange_ratCast p).induction_on r hc fun q => ?_
        rw [map_ratCast]
        exact SubfieldClass.ratCast_mem _ _
    have hM : IntermediateField.adjoin ℚ_[p] (Set.range fun i => ψ (b i)) ≤ M := by
      refine IntermediateField.adjoin_le_iff.2 ?_
      rintro _ ⟨i, rfl⟩
      exact Subfield.le_topologicalClosure ψ.fieldRange ⟨b i, rfl⟩
    by_cases h0 : x = 0
    · exact ⟨0, by simp [h0]⟩
    obtain ⟨_, ⟨a, rfl⟩, h⟩ := exists_norm_eq_of_mem_closure (S := (ψ.fieldRange : Set (PadicAlgCl p))) (hM hx) h0
    exact ⟨a, h⟩

theorem exists_norm_eq {F : Type} [Field F] [NumberField F] (φ : F →+* ℂ_[p]) {x : ℂ_[p]} (hx : x ∈ kurC φ) :
    ∃ a : F, ‖x‖ = ‖φ a‖ := by
  obtain ⟨ψ, hψ⟩ := exists_lift φ
  obtain ⟨K, hK, hmem, hnorm⟩ := exists_finite ψ
  let M : Subfield ℂ_[p] := (ReciprocityTheory.DiscreteGroups.LocalClassField.MaximalUnramifiedExtension p K).toSubfield.map (algebraMap (PadicAlgCl p) ℂ_[p])
  have hle : kurC φ ≤ M.topologicalClosure := by
    refine Subfield.topologicalClosure_minimal _ (sup_le ?_ ?_) (Subfield.isClosed_topologicalClosure _)
    · rintro _ ⟨a, rfl⟩
      exact M.le_topologicalClosure ⟨ψ a, ReciprocityTheory.DiscreteGroups.LocalClassField.le_Kur (hmem a), hψ a⟩
    · refine Subfield.topologicalClosure_minimal _ (Subfield.closure_le.2 ?_) (Subfield.isClosed_topologicalClosure _)
      rintro ζ ⟨n, hn, hpn, hζ⟩
      obtain ⟨ξ, rfl⟩ := mem_range_of_isIntegral (IsIntegral.of_pow hn (by rw [hζ]; exact isIntegral_one))
      refine M.le_topologicalClosure ⟨ξ, ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Kur_of_pow hK hpn ?_, rfl⟩
      apply (algebraMap (PadicAlgCl p) ℂ_[p]).injective
      rw [map_pow, hζ, map_one]
  by_cases h0 : x = 0
  · exact ⟨0, by simp [h0]⟩
  obtain ⟨_, ⟨y, hy, rfl⟩, h⟩ := exists_norm_eq_of_mem_closure (S := (M : Set ℂ_[p])) (hle hx) h0
  obtain ⟨n, hn, hyn⟩ := (ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Kur_iff hK y).1 hy
  obtain ⟨z, hz, hyz⟩ := ReciprocityTheory.DiscreteGroups.LocalClassField.norm_Kn p K hK hn hyn
  obtain ⟨a, ha⟩ := hnorm z hz
  refine ⟨a, ?_⟩
  rw [h, ← hψ, norm_algebraMap', norm_algebraMap', ← ha, hyz]

theorem exists_near {F : Type} [Field F] (φ : F →+* ℂ_[p]) {x : ℂ_[p]} (hx : ‖x‖ ≤ 1) :
    ∃ y ∈ kurC φ, ‖x - y‖ < 1 := by
  rcases hx.lt_or_eq with hlt | heq
  · exact ⟨0, zero_mem _, by rwa [sub_zero]⟩
  obtain ⟨z, hz⟩ := (UniformSpace.Completion.denseRange_coe (α := PadicAlgCl p)).exists_dist_lt x one_pos
  rw [dist_eq_norm, PadicComplex.coe_eq] at hz
  have hz1 : ‖z‖ = 1 := by
    have h1 : ‖algebraMap (PadicAlgCl p) ℂ_[p] z - x‖ < ‖x‖ := by rwa [norm_sub_rev, heq]
    have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h1.ne
    rwa [sub_add_cancel, max_eq_right h1.le, heq, norm_algebraMap'] at this
  obtain ⟨ζ, m, hm, hζ, h⟩ := ReciprocityTheory.DiscreteGroups.LocalClassField.exists_teichmuller_bar z hz1
  refine ⟨algebraMap (PadicAlgCl p) ℂ_[p] ζ, root_mem_kurC φ hm (by rw [← map_pow, hζ, map_one]), ?_⟩
  have e : x - algebraMap (PadicAlgCl p) ℂ_[p] ζ =
      (x - algebraMap (PadicAlgCl p) ℂ_[p] z) + algebraMap (PadicAlgCl p) ℂ_[p] (z - ζ) := by
    rw [map_sub]; ring
  rw [e]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hz (by rwa [norm_algebraMap']))

theorem kurC_value_residue : ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F] (φ : F →+* ℂ_[p]),
    (∀ x ∈ kurC φ, ∃ a : F, ‖x‖ = ‖φ a‖) ∧ ∀ x : ℂ_[p], ‖x‖ ≤ 1 → ∃ y ∈ kurC φ, ‖x - y‖ < 1 :=
  fun _ _ _ _ _ φ => ⟨fun _ hx => exists_norm_eq φ hx, fun _ hx => exists_near φ hx⟩

end GlobalTheory.KurValue

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRamificationOverPlaceOfCdvrReadingInCp
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GeoTie

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ReadingOver

open GlobalTheory.GoodPts

variable {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [NumberField F] (φ : F →+* ℂ_[p])

theorem norm_le_one_of_valuation_le_one {x : F} (hx : (placeAt φ).valuation F x ≤ 1) : ‖φ x‖ ≤ 1 := by
  obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer (placeAt φ) x hx
  have hd : ‖φ ((d : 𝓞 F) : F)‖ = 1 := le_antisymm (norm_int_le_one φ _) (not_lt.1 d.2)
  have h2 := congrArg (fun t => ‖φ t‖) hnd
  simp only [map_mul, norm_mul] at h2
  have h3 : ‖φ x‖ * ‖φ ((d : 𝓞 F) : F)‖ = ‖φ (n : F)‖ := h2
  rw [hd, mul_one] at h3
  rw [h3]; exact norm_int_le_one φ n

variable (T : CDVR)

theorem valV_le_one_of_inV {x : T.Fr} (hx : InV T x) : valV T.V x ≤ 1 := by
  obtain ⟨v, rfl⟩ := hx
  rw [valV, HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_le_one _ _

theorem inV_of_valV_le_one {x : T.Fr} (hx : valV T.V x ≤ 1) : InV T x := by
  obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer
    (IsDiscreteValuationRing.maximalIdeal T.V) x hx
  have hu : IsUnit (d : T.V) := by
    by_contra h
    exact d.2 ((IsLocalRing.mem_maximalIdeal _).2 h)
  refine ⟨n * ↑hu.unit⁻¹, ?_⟩
  rw [map_mul, ← hnd, mul_assoc, ← map_mul, hu.mul_val_inv, map_one, mul_one]

theorem vV_zpow {x : T.Fr} (n : ℤ) : vV T.V (x ^ n) = n * vV T.V x := by
  simp only [vV, map_zpow₀, WithZero.log_zpow, smul_eq_mul]
  ring

variable {T}

theorem overLa_placeAt_of_isReading {io : F →+* T.Fr} {k : T.Fr →+* ℂ_[p]} (hR : IsReading φ T io k) :
    ∃ e : ℕ, OverLa (placeAt φ) T.V io e := by
  set P := placeAt φ with hP
  have key : ∀ y : T.Fr, valV T.V y ≤ 1 ↔ ‖k y‖ ≤ 1 := fun y =>
    ⟨fun h => (hR.int y).2 (inV_of_valV_le_one T h), fun h => valV_le_one_of_inV T ((hR.int y).1 h)⟩
  obtain ⟨π, hπ⟩ := P.intValuation_exists_uniformizer
  have hπ1 : P.intValuation π < 1 := by
    rw [hπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have hπn : ‖φ (π : F)‖ < 1 := (mem_placeAt φ π).1 ((P.intValuation_lt_one_iff_mem π).1 hπ1)
  have hπ0 : (π : F) ≠ 0 := by
    intro h
    have h' : π = 0 := by exact_mod_cast h
    rw [h', map_zero] at hπ
    exact WithZero.exp_ne_zero.symm hπ
  have hνπ : P.valuation F (π : F) = WithZero.exp (-1) := by
    rw [← hπ]; exact HeightOneSpectrum.valuation_of_algebraMap P π
  set x := io (π : F) with hx
  have hx0 : x ≠ 0 := (map_ne_zero io).2 hπ0
  have hkx : ‖k x‖ < 1 := by rw [hx, hR.comp]; exact hπn
  have hvx1 : valV T.V x < 1 := by
    refine lt_of_le_of_ne ((key x).2 hkx.le) fun h1 => ?_
    have h2 : valV T.V x⁻¹ ≤ 1 := by rw [map_inv₀, h1, inv_one]
    have h3 := (key _).1 h2
    rw [map_inv₀, norm_inv] at h3
    have h4 : 0 < ‖k x‖ := norm_pos_iff.2 ((map_ne_zero k).2 hx0)
    exact absurd h3 (not_le.2 ((one_lt_inv₀ h4).2 hkx))
  have hvx : 0 < vV T.V x := by
    have h := (WithZero.log_lt_log (valV_ne_zero hx0) one_ne_zero).2 hvx1
    rw [WithZero.log_one] at h
    simp only [vV]; omega
  refine ⟨(vV T.V x).toNat, by omega, fun a => ?_⟩
  by_cases ha : a = 0
  · subst ha; simp [vV, vLa]
  set n := vLa P a with hn
  set b := a * (π : F) ^ (-n) with hb
  have hb0 : b ≠ 0 := mul_ne_zero ha (zpow_ne_zero _ hπ0)
  have hνa : P.valuation F a = WithZero.exp (-n) := by
    rw [hn, vLa, neg_neg, WithZero.exp_log ((P.valuation F).ne_zero_iff.2 ha)]
  have hνb : P.valuation F b = 1 := by
    rw [hb, map_mul, map_zpow₀, hνa, hνπ, ← WithZero.exp_zsmul, ← WithZero.exp_add]
    simp
  have hkb : ‖k (io b)‖ ≤ 1 := by rw [hR.comp]; exact norm_le_one_of_valuation_le_one φ hνb.le
  have hkb' : ‖k (io b)⁻¹‖ ≤ 1 := by
    rw [← map_inv₀, hR.comp]
    exact norm_le_one_of_valuation_le_one φ (by rw [map_inv₀, hνb, inv_one])
  have hvb1 : valV T.V (io b) = 1 := by
    have h1 := (key _).2 hkb
    have h2 := (key _).2 hkb'
    rw [map_inv₀] at h2
    have hv0 : valV T.V (io b) ≠ 0 := valV_ne_zero ((map_ne_zero io).2 hb0)
    have h3 : valV T.V (io b) * (valV T.V (io b))⁻¹ ≤ valV T.V (io b) * 1 := mul_le_mul_right h2 _
    rw [mul_inv_cancel₀ hv0, mul_one] at h3
    exact le_antisymm h1 h3
  have hvb : vV T.V (io b) = 0 := by simp [vV, hvb1]
  have hab : io a = io b * x ^ n := by
    rw [hx, ← map_zpow₀, ← map_mul, hb, mul_assoc, ← zpow_add₀ hπ0, neg_add_cancel, zpow_zero, mul_one]
  rw [hab, vV_mul ((map_ne_zero io).2 hb0) (zpow_ne_zero _ hx0), hvb, vV_zpow, Int.toNat_of_nonneg hvx.le]
  ring

theorem overLa_placeAt : ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F] (φ : F →+* ℂ_[p]) (T : CDVR)
    (io : F →+* T.Fr) (k : T.Fr →+* ℂ_[p]), IsReading φ T io k → ∃ e : ℕ, OverLa (placeAt φ) T.V io e :=
  fun _ _ _ _ _ φ _ _ _ hR => overLa_placeAt_of_isReading φ hR

end GlobalTheory.ReadingOver

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtensionUnramifiedAtOnePlaceStatement
section
open NumberField IsDedekindDomain Polynomial Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq GlobalTheory.SmGL Formalism.L2.NT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unramified_totallyComplex_ext_with_unity_roots : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (g : ℕ)
    [Fact g.Prime] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i) (n : ℕ) (hn : 0 < n),
    ∃ (E' : Type) (_ : Field E') (_ : NumberField E') (_ : IsTotallyComplex E') (_ : Algebra E E')
      (_ : Algebra E' Ω) (_ : IsScalarTower E E' Ω) (_ : IsAlgClosure E' Ω) (w' : HeightOneSpectrum (𝓞 E'))
      (_ : IsPlaceOver A w'), ((g : ℕ) : 𝓞 E') ∈ w'.asIdeal ∧ ((g : ℕ) : 𝓞 E') ∉ w'.asIdeal ^ 2 ∧
      normV w' = g ^ n ∧ (∃ ζ : E', IsPrimitiveRoot ζ (g ^ n - 1)) ∧
      ∀ t ∈ Ine (F := E) A, ∀ e : E', t (algebraMap E' Ω e) = algebraMap E' Ω e := by
  first | exact @GlobalTheory.UnrCycExt.exists_unramified_ext | exact GlobalTheory.UnrCycExt.exists_unramified_ext | (intros; apply GlobalTheory.UnrCycExt.exists_unramified_ext <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GammaSubOneDivUniformiserAtLetterOfConclusionsStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gamma_sub_one_div_uniformiser_at_letter_of_conclusions : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), Formalism.MainNotions.DeltaInvariantLattices.DeltaInvariantNormBound D HW F Cm → Formalism.MainNotions.RamifiedCoefficientChains.adm18 D HW F := by
  first | exact @GlobalTheory.adm18_of_N1used | exact GlobalTheory.adm18_of_N1used | (intros; apply GlobalTheory.adm18_of_N1used <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralCombIdempotentSectionsNonnegOverPlaceStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralComb_idempotentSections_nonneg_over_place : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (la : HeightOneSpectrum (𝓞 c.F)) (m : ℕ) (χ : Fin m → Rul Xo c) (v : Fin m → c.F), (∀ i, χ i ∈ sec Xo c 0 0 ∧ χ i * χ i = χ i) → (∀ i, la.valuation c.F (v i) ≤ 1) → ∀ f : Rul Xo c, (∀ u ∈ valSet Xo c (algCls Xo c) la, 0 ≤ u f) → ∀ u ∈ valSet Xo c (algCls Xo c) la, 0 ≤ u ((∑ i, v i • χ i) * f) := by
  first | exact @GlobalTheory.IdemInt.idem_comb_mul_nonneg | exact GlobalTheory.IdemInt.idem_comb_mul_nonneg | (intros; apply GlobalTheory.IdemInt.idem_comb_mul_nonneg <;> assumption)
end

