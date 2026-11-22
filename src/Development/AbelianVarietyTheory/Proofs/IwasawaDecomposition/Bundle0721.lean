import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0699
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0703
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0687
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0623
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0021
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0404
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0497
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0709
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0704
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0033
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotMemSqOfRamificationIdx
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistDataAgreeAcrossCoefficients
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0684
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPosRatMultipleOfPosRealMultipleIntForm
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory

theorem posReal_multiple_rat {X : Type} [AddCommGroup X] (x y : LinearMap.BilinForm ℤ X) (d : ℝ)
    (hd : 0 < d) (hy : y ≠ 0) (h : toReal x = d • toReal y) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ (a : ℤ) • x = (b : ℤ) • y := by
  have hpt : ∀ u v, (x u v : ℝ) = d * (y u v : ℝ) := by
    intro u v
    have := congrArg (fun f => f u v) h
    simpa [toReal] using this
  obtain ⟨u, v, huv⟩ : ∃ u v, y u v ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hy (LinearMap.ext₂ hc)
  set r : ℚ := (x u v : ℚ) / (y u v : ℚ) with hr_def
  have hy' : (y u v : ℝ) ≠ 0 := by exact_mod_cast huv
  have hdr : d = (r : ℝ) := by
    rw [hr_def]; push_cast; rw [hpt u v]; field_simp
  have hr : 0 < r := by exact_mod_cast (hdr ▸ hd)
  have hnum : 0 < r.num := Rat.num_pos.mpr hr
  have hcast : ((r.num.toNat : ℕ) : ℤ) = r.num := Int.toNat_of_nonneg hnum.le
  refine ⟨r.den, r.num.toNat, r.den_pos, by omega, ?_⟩
  apply LinearMap.ext₂
  intro p q
  simp only [LinearMap.smul_apply, smul_eq_mul]
  rw [hcast]
  apply Int.cast_injective (α := ℝ)
  push_cast
  rw [hpt p q, hdr]
  have hrr : (r : ℝ) = (r.num : ℝ) / (r.den : ℝ) := by
    rw [← Rat.cast_intCast, ← Rat.cast_natCast, ← Rat.cast_div, Rat.num_div_den]
  have hden : (r.den : ℝ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  rw [hrr]; field_simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrimitiveBalancedFormFracCoordsOfCellMult
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

noncomputable section

namespace GlobalTheory.PolFan

namespace CentreChoice

variable {O : Type} [CommRing O] {bar : O → O} {X : Type} [AddCommGroup X] [Module O X]

theorem exists_isPrim_smul {x : balForms bar X} (hx : x ≠ 0) :
    ∃ (g : ℕ) (v : balForms bar X), 0 < g ∧ x = g • v ∧ IsPrim bar v := by
  classical
  obtain ⟨a, b, hab⟩ : ∃ a b, (x : LinearMap.BilinForm ℤ X) a b ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (Subtype.ext (LinearMap.ext₂ h))
  let S : Set ℕ := {g | 0 < g ∧ ∃ v : balForms bar X, x = g • v}
  have hS1 : 1 ∈ S := ⟨one_pos, x, (one_smul _ _).symm⟩
  have hbd : ∀ g ∈ S, g ≤ ((x : LinearMap.BilinForm ℤ X) a b).natAbs := by
    rintro g ⟨hg, v, hv⟩
    have e : (x : LinearMap.BilinForm ℤ X) a b = (g : ℤ) * (v : LinearMap.BilinForm ℤ X) a b := by
      rw [hv]
      simp
    rw [e] at hab ⊢
    rw [Int.natAbs_mul, Int.natAbs_natCast]
    exact Nat.le_mul_of_pos_right _ (Int.natAbs_pos.2 (right_ne_zero_of_mul hab))
  have hB : BddAbove S := ⟨_, hbd⟩
  obtain ⟨hg, v, hv⟩ := Nat.sSup_mem ⟨1, hS1⟩ hB
  refine ⟨sSup S, v, hg, hv, fun j v' hj => ?_⟩
  have hj0 : j ≠ 0 := by
    rintro rfl
    apply hx
    rw [hv, hj, zero_smul, smul_zero]
  have hmem : sSup S * j ∈ S := ⟨Nat.mul_pos hg (Nat.pos_of_ne_zero hj0), v', by rw [hv, hj, mul_smul]⟩
  have h1 : sSup S * j ≤ sSup S * 1 := by simpa using le_csSup hB hmem
  have h2 := Nat.le_of_mul_le_mul_left h1 hg
  omega

theorem exists_isPrim_frac : ∀ {O : Type} [CommRing O] (bar : O → O) (φ : InvFun O) (M : ℕ) {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] {m : ℕ} (δ : Fin m → LinearMap.BilinForm ℤ X), IsMultCell bar φ M δ → 2 ≤ M →
  ∃ (v : LinearMap.BilinForm ℤ X) (hv : v ∈ balForms bar X), IsPrim bar (⟨v, hv⟩ : balForms bar X) ∧ (∀ y, 0 ≤ v y y) ∧
    ∃ t : Fin m → ℝ, (∀ i, 0 ≤ t i ∧ t i < 1) ∧ toReal v = ∑ i, t i • toReal (δ i) := by
  intro O _ bar φ M X _ _ _ m δ hδ h2
  classical
  obtain ⟨hc, -, -, hM⟩ := hδ
  let δ' : Fin m → balForms bar X := fun i => ⟨δ i, hc.mem i⟩
  let P := Submodule.span ℤ (Set.range δ')
  have hcard : 1 < Nat.card (Submodule.torsion ℤ (balForms bar X ⧸ P)) := by
    have : Nat.card (Submodule.torsion ℤ (balForms bar X ⧸ P)) = M := hM
    omega
  have hfin : Finite (Submodule.torsion ℤ (balForms bar X ⧸ P)) := Nat.finite_of_card_ne_zero (by omega)
  haveI := Finite.one_lt_card_iff_nontrivial.1 hcard
  obtain ⟨t, ht⟩ := exists_ne (0 : Submodule.torsion ℤ (balForms bar X ⧸ P))
  obtain ⟨⟨a, ha⟩, hat⟩ := (Submodule.mem_torsion_iff _).1 t.2
  obtain ⟨x, hx⟩ := Submodule.mkQ_surjective P t.1
  have hxP : x ∉ P := fun h => ht (Subtype.ext (by rw [← hx]; exact (Submodule.Quotient.mk_eq_zero P).2 h))
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  have h1 : a • x ∈ P := (Submodule.Quotient.mk_eq_zero P).1 (by
    rw [Submodule.Quotient.mk_smul, ← Submodule.mkQ_apply, hx]; exact hat)
  have hk : 0 < a.natAbs := Int.natAbs_pos.2 ha0
  have hkx : (a.natAbs : ℤ) • x ∈ P := by
    rcases Int.natAbs_eq a with h | h
    · rwa [h] at h1
    · rw [h, neg_smul] at h1
      exact P.neg_mem_iff.1 h1
  obtain ⟨c, hc'⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hkx
  set k : ℕ := a.natAbs with hkdef
  have hkZ : (0 : ℤ) < k := by exact_mod_cast hk
  let x' : balForms bar X := x - ∑ i, (c i / k) • δ' i
  have hsP : ∑ i, (c i / k) • δ' i ∈ P :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hx'0 : x' ≠ 0 := fun h => hxP (by
    have : x = x' + ∑ i, (c i / k) • δ' i := by simp [x']
    rw [this, h, zero_add]; exact hsP)
  have hkx' : (k : ℤ) • x' = ∑ i, (c i % k) • δ' i := by
    simp only [x', smul_sub, Finset.smul_sum, smul_smul, ← hc']
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← sub_smul]
    congr 1
    have := Int.mul_ediv_add_emod (c i) k
    linarith
  obtain ⟨g, v, hg, hxv, hprim⟩ := exists_isPrim_smul hx'0
  have hr0 : ∀ i, 0 ≤ c i % k := fun i => Int.emod_nonneg _ hkZ.ne'
  have hr1 : ∀ i, c i % k < k := fun i => Int.emod_lt_of_pos _ hkZ
  have key : ∀ a b, ((k : ℤ) * g) * (v : LinearMap.BilinForm ℤ X) a b = ∑ i, (c i % k) * δ i a b := by
    intro a b
    have e := congrArg (fun z : balForms bar X => (z : LinearMap.BilinForm ℤ X) a b) hkx'
    simp only [hxv] at e
    simpa [Submodule.coe_sum, LinearMap.sum_apply, δ', mul_assoc] using e
  have hkg : (0 : ℤ) < (k : ℤ) * g := mul_pos hkZ (by exact_mod_cast hg)
  refine ⟨v, v.2, hprim, fun y => ?_, fun i => ((c i % k : ℤ) : ℝ) / ((k : ℝ) * g), fun i => ⟨?_, ?_⟩, ?_⟩
  · have hs : 0 ≤ ∑ i, (c i % k) * δ i y y :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hr0 i) (hc.nonneg i y)
    rw [← key] at hs
    exact nonneg_of_mul_nonneg_right hs hkg
  · have : (0 : ℝ) < (k : ℝ) * g := by exact_mod_cast hkg
    exact div_nonneg (by exact_mod_cast hr0 i) this.le
  · have : (0 : ℝ) < (k : ℝ) * g := by exact_mod_cast hkg
    rw [div_lt_one this]
    have : c i % k < (k : ℤ) * g := lt_of_lt_of_le (hr1 i) (le_mul_of_one_le_right hkZ.le (by exact_mod_cast hg))
    exact_mod_cast this
  · have hpos : (0 : ℝ) < (k : ℝ) * g := by exact_mod_cast hkg
    refine LinearMap.ext₂ fun a b => ?_
    have e : ((k : ℝ) * g) * ((v : LinearMap.BilinForm ℤ X) a b : ℝ) = ∑ i, ((c i % k : ℤ) : ℝ) * (δ i a b : ℝ) := by
      exact_mod_cast key a b
    simp only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [← mul_right_inj' hpos.ne', e, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp

end CentreChoice

end GlobalTheory.PolFan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSemilinearPullbackOfMarkedOrbitIndicator
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

noncomputable section

namespace GlobalTheory.PolFan.OrbMark

theorem exists_semilinear_pull_of_evalZ_eq_one : ∀ {O : Type} [CommRing O] (w0 : O) {X₀ : Type} [AddCommGroup X₀] [Module O X₀] (v : LinearMap.BilinForm ℤ X₀)
  {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] (β : LinearMap.BilinForm ℤ X), (OrbMark.orbFun O w0 v).evalZ β = 1 →
  ∃ (τ : O ≃+* O) (f : X →+ X₀ ⧸ (CarDim.orad v : Submodule O X₀)), τ w0 = w0 ∧ Function.Surjective f ∧
    (∀ (a : O) (x : X), f (a • x) = τ a • f x) ∧
    ∀ (x y : X) (x₀ y₀ : X₀), Submodule.Quotient.mk x₀ = f x → Submodule.Quotient.mk y₀ = f y → β x y = v x₀ y₀ := by
  intro O _ w0 X₀ _ _ v X _ _ _ β h1
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' O X
  rw [InvFun.evalZ, (orbFun O w0 v).eval_eq hr, orbFun_toFun] at h1
  split_ifs at h1 with hc
  swap
  · exact absurd h1 zero_ne_one
  obtain ⟨-, σ, hσ, s, hs, H⟩ := hc

  let g : (Fin n → O) →+ X :=
    { toFun := fun a => r (twv σ a)
      map_zero' := by rw [twv_zero, map_zero]
      map_add' := fun a b => by
        have e : twv σ (a + b) = twv σ a + twv σ b := funext fun _ => map_add σ _ _
        rw [e, map_add] }
  have hg : ∀ a, g a = r (twv σ a) := fun _ => rfl
  have hgs : ∀ (c : O) a, g (c • a) = σ c • g a := fun c a => by
    rw [hg, hg, twv_smul, map_smul]
  have hgsurj : Function.Surjective g := fun x => by
    obtain ⟨a, ha⟩ := hr x
    exact ⟨twv σ.symm a, by rw [hg, twv_twv_symm, ha]⟩
  have hker : ∀ z, g z = 0 → s z = 0 := by
    intro z hz
    obtain ⟨x, hx⟩ := Submodule.mkQ_surjective _ (s z)
    rw [← hx]
    refine (Submodule.Quotient.mk_eq_zero _).2 fun c y => ?_
    obtain ⟨b, hb⟩ := hs (Submodule.Quotient.mk y)
    have h1 := H (c • z) b (c • x) y
      (by rw [Submodule.Quotient.mk_smul, map_smul]; exact congrArg _ hx) hb.symm
    have e : r (twv σ (c • z)) = 0 := by rw [← hg, hgs, hz, smul_zero]
    dsimp only at h1
    rw [e, map_zero, LinearMap.zero_apply] at h1
    exact_mod_cast h1.symm
  have hwd : ∀ a a', g a = g a' → s a = s a' := fun a a' h => by
    have := hker (a - a') (by rw [map_sub, h, sub_self])
    rwa [map_sub, sub_eq_zero] at this
  let pre : X → (Fin n → O) := fun x => (hgsurj x).choose
  have hpre : ∀ x, g (pre x) = x := fun x => (hgsurj x).choose_spec
  have hf : ∀ a, s (pre (g a)) = s a := fun a => hwd _ _ (hpre _)
  let f : X →+ X₀ ⧸ (CarDim.orad v : Submodule O X₀) :=
    { toFun := fun x => s (pre x)
      map_zero' := by
        have := hf 0
        rw [map_zero] at this
        rw [this, map_zero]
      map_add' := fun x y => by
        have := hf (pre x + pre y)
        rw [map_add, hpre, hpre] at this
        rw [this, map_add] }
  have hfg : ∀ a, f (g a) = s a := hf
  refine ⟨σ.symm, f, by rw [RingEquiv.symm_apply_eq, hσ], fun q => ?_, fun c x => ?_, fun x y x₀ y₀ hx hy => ?_⟩
  · obtain ⟨a, rfl⟩ := hs q
    exact ⟨g a, hfg a⟩
  · obtain ⟨a, rfl⟩ := hgsurj x
    have e : c • g a = g (σ.symm c • a) := by rw [hgs, σ.apply_symm_apply]
    rw [e, hfg, hfg, map_smul]
  · obtain ⟨a, rfl⟩ := hgsurj x
    obtain ⟨b, rfl⟩ := hgsurj y
    rw [hfg] at hx hy
    have h := H a b x₀ y₀ hx hy
    dsimp only at h
    rw [← hg, ← hg] at h
    exact_mod_cast h

end GlobalTheory.PolFan.OrbMark
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSpecTensorToPullbackSectionsCompatStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_specTensor_to_pullback_sections_compat : ∀ {X Y' : Scheme.{0}} (ρ : Y' ⟶ X) {R : Type} [CommRing R] (ξ : Sp R ⟶ X) (U : X.affineOpens) (hle : ⊤ ≤ ξ ⁻¹ᵁ (U : X.Opens)) (W : Y'.affineOpens) (hW : (W : Y'.Opens) ≤ ρ ⁻¹ᵁ (U : X.Opens)), letI := (ρ.appLE U W hW).hom.toAlgebra; letI := (ξ.appLE U ⊤ hle ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom.toAlgebra; ∃ (κ : Spec (CommRingCat.of (Γ(Y', W) ⊗[Γ(X, U)] R)) ⟶ pullback ξ ρ) (hκ : ⊤ ≤ (κ ≫ pullback.snd ξ ρ) ⁻¹ᵁ (W : Y'.Opens)), (∀ c : Γ(Y', W), (Scheme.ΓSpecIso _).hom.hom (((κ ≫ pullback.snd ξ ρ).appLE W ⊤ hκ).hom c) = c ⊗ₜ[Γ(X, U)] (1 : R)) ∧ ∀ r : R, (Scheme.ΓSpecIso _).hom.hom (κ.appTop.hom ((pullback.fst ξ ρ).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))) = (1 : Γ(Y', W)) ⊗ₜ[Γ(X, U)] r := by
  first | exact @GlobalTheory.specTensor_to_pullback | exact GlobalTheory.specTensor_to_pullback | (intros; apply GlobalTheory.specTensor_to_pullback <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStdWtCast
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3.RowStd

set_option maxHeartbeats 4000000 in

theorem exists_std_wtCast : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cX : CoefA X.toD7.sp.X') (gramR : Matrix (Fin X.toD7.sp.X'.rank) (Fin X.toD7.sp.X'.rank) X.toD7.host.E)
    (c0R : VV X.toD7.what₂.LL (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) →ₛₗ[X.toD7.what₂.embLL] cX.W),
    cX.Is → (gramR = X.toD7.sp.X'.gram ∨ gramR = -X.toD7.sp.X'.gram) →
    Bridge.CoefMapTie X.toD7.sp.X' cX.coef c0R (rhoV (labLL X.toD7) _) →
    (∀ x y, inner ℂ (c0R x) (c0R y) = X.toD7.what₂.embLL (pairV (labLL X.toD7) _ gramR x y)) →
    L.βX = 1 → ∃ c : VV X.B.fields.K X.B.wts.sgTrue →ₛₗ[X.B.embLL] cX.W,
      (∀ v, c v = c0R (wtCast X v)) ∧
      LinearIndependent ℂ (fun i => c (bVV X.B.fields.K X.B.wts.sgTrue i)) ∧
      Submodule.span ℂ (Set.range fun i => c (bVV X.B.fields.K X.B.wts.sgTrue i)) = ⊤ ∧
      (∀ x y, inner ℂ (c x) (c y) = X.B.embLL (pairV X.B.fields.emb X.B.wts.sgTrue 1 x y)) ∧
      (∀ (γ : GQ X.toD7.sp.X') (γE : GL (Fin X.toD7.sp.X'.rank) X.toD7.host.E) (g : GL (Fin (X.B.R.N X.B.R.m - 1)) X.B.fields.E),
        Bridge.IsRatMat X.toD7.sp.X' γ γE → MatEq γE g → ∀ v, c (rhoV X.B.fields.emb X.B.wts.sgTrue g v) = cX.coef.ρ γ (c v)) ∧
      ∀ t, ∃ P : Bridge.ClassPres (Bridge.ratF X.toD7.sp.X') ((famR X I hX U Xg tr).A.MtildeCSD t) X.toD7.what₂.embLL cX.coef.ρ (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J (levEnv X.toD7.sp.X' L.βX (L.datXt t)).χ,
        (∀ (f : ((famR X I hX U Xg tr).A.MtildeCSD t).Forms) (h : Bridge.Gf X.toD7.sp.X'),
          P.ext (f : _ → _) h = c ((((Formalism.L2.Col.mtildeKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1).res (Formalism.L2.Col.mtildeKOk _ _ _ _ hX)).symm f).1 (GlobalTheory.Mem.R3.RowAd.decoAd X I t h))) ∧
        Bridge.CoefTie X.toD7.sp.X' cX.coef P (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) c0R (pairV (labLL X.toD7) _ gramR)
          (nabAt (labLL X.toD7) _) (delAt (labLL X.toD7) _) := by
  intro X px I hX U Xg tr L eG hI hV hL hG cX gramR c0R hc hgr hM hin hb
  obtain ⟨c, hc0, hInter, hli, hsp, hinn, hT⟩ := exists_coef X px I hX U Xg tr L hI cX gramR c0R hc hgr hM hin
  refine ⟨c, hc0, hli, hsp, hinn, hInter, fun t => ?_⟩
  obtain ⟨P, hPc, hPy, hPe⟩ := GlobalTheory.T.rowsClassSet_presentation_coefficientMap X px I hX U Xg tr L eG hI hV hL hG hb cX c hInter hli hsp hinn t
  exact ⟨P, hPe, hT t P hPc hPy⟩

set_option maxHeartbeats 4000000 in

theorem exists_std : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cX : CoefA X.toD7.sp.X') (gramR : Matrix (Fin X.toD7.sp.X'.rank) (Fin X.toD7.sp.X'.rank) X.toD7.host.E)
    (c0R : VV X.toD7.what₂.LL (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) →ₛₗ[X.toD7.what₂.embLL] cX.W),
    cX.Is → (gramR = X.toD7.sp.X'.gram ∨ gramR = -X.toD7.sp.X'.gram) →
    Bridge.CoefMapTie X.toD7.sp.X' cX.coef c0R (rhoV (labLL X.toD7) _) →
    (∀ x y, inner ℂ (c0R x) (c0R y) = X.toD7.what₂.embLL (pairV (labLL X.toD7) _ gramR x y)) →
    L.βX = 1 → ∃ c : VV X.B.fields.K X.B.wts.sgTrue →ₛₗ[X.B.embLL] cX.W,
      (∀ (γ : GQ X.toD7.sp.X') (γE : GL (Fin X.toD7.sp.X'.rank) X.toD7.host.E) (g : GL (Fin (X.B.R.N X.B.R.m - 1)) X.B.fields.E),
        Bridge.IsRatMat X.toD7.sp.X' γ γE → MatEq γE g → ∀ v, c (rhoV X.B.fields.emb X.B.wts.sgTrue g v) = cX.coef.ρ γ (c v)) ∧
      ∀ t, ∃ P : Bridge.ClassPres (Bridge.ratF X.toD7.sp.X') ((famR X I hX U Xg tr).A.MtildeCSD t) X.toD7.what₂.embLL cX.coef.ρ (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J (levEnv X.toD7.sp.X' L.βX (L.datXt t)).χ,
        (∀ (f : ((famR X I hX U Xg tr).A.MtildeCSD t).Forms) (h : Bridge.Gf X.toD7.sp.X'),
          P.ext (f : _ → _) h = c ((((Formalism.L2.Col.mtildeKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1).res (Formalism.L2.Col.mtildeKOk _ _ _ _ hX)).symm f).1 (GlobalTheory.Mem.R3.RowAd.decoAd X I t h))) ∧
        Bridge.CoefTie X.toD7.sp.X' cX.coef P (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) c0R (pairV (labLL X.toD7) _ gramR)
          (nabAt (labLL X.toD7) _) (delAt (labLL X.toD7) _) := by
  intro X px I hX U Xg tr L eG hI hV hL hG cX gramR c0R hc hgr hM hin hb
  obtain ⟨c, -, -, -, -, h⟩ := exists_std_wtCast X px I hX U Xg tr L eG hI hV hL hG cX gramR c0R hc hgr hM hin hb
  exact ⟨c, h⟩

end GlobalTheory.Mem.R3.RowStd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitTauCoordinateAddNsmulFirstVariableStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_tauCoordinate_add_nsmul_first_variable : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R), D.TauBimult →
    ∀ (a z b : D.X) (k : ℕ) (x x' x'' : (FractionRing R)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D a b x →
      GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D z b x' → GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D (a + k • z) b x'' →
      ∃ u : Rˣ, x'' = Units.map (algebraMap R (FractionRing R)).toMonoidHom u * (x * x' ^ k) := by
  first | exact @GlobalTheory.TauShift.main | exact GlobalTheory.TauShift.main | (intros; apply GlobalTheory.TauShift.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnlocalizedSaturatedState
section
noncomputable section

namespace GlobalTheory.HeightCounting.Up

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
open GlobalTheory.Mem.Top.TwChar (plUnder RootIso FrobPick)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option genInjectivity false
set_option genSizeOfSpec false
set_option maxHeartbeats 2000000

def SatU {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} (P : Pre2 K w) : Prop :=
  T = TwDat.untw B T.pl → ∀ v v', OverOne (w.D P.Z₀) v v' → v ∈ P.Wt → v' ∈ P.Wt

section Slot

variable (hL : GlobalTheory.Published.LocalLanglandsGL) (cDep : ℝ)

def Org (K : Ctx) {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) {D : D7} (Wt : Set B.places.Pl) (nch : NChoice D) : Prop :=
  ∃ (P : Pre2 K w) (x : St P) (l : LC hL x), (ListSt cDep x ∧ SatU P) ∧ Wt = P.Wt ∧ Kept l.c.ch nch

def NEo : NExt hL := fun K B f T w Z Wt p0 t nch n xd c => NEl hL cDep K B f T w Z Wt p0 t nch n xd c ×
  PLift (Org hL cDep K w Wt nch)

def NEog : NExt hL := fun K B f T w Z Wt p0 t nch n xd c => NEo hL cDep K B f T w Z Wt p0 t nch n xd c × PLift (GoodO (w.D Z) nch xd)

def SFino : Prop := AllSt fun K _ _ _ w P x => ∀ (l : LC hL x) (S : SExt) (Γ : GeoP), (ListSt cDep x ∧ SatU P) →
  ∃ (Z : w.Lt) (v : Lv3 (prmR (NEo hL cDep) S Γ).s K w Z), v.Wt = P.Wt ∧ Kept l.c.ch v.nch

def SecondNo : Prop := ∀ (S : SExt) (Γ : GeoP), Pass KPx (IsBuiltE (prmR (NEo hL cDep) S Γ).s) fun K B f T =>
  ∃ w : ColW B f T, Start K B f T w ∧ Has3 (prmR (NEog hL cDep) S Γ).s K B f T w

end Slot

def ExistsUnlocalizedSaturatedState : Prop := StepW Start fun K _ _ _ w => ∃ (P : Pre2 K w) (x : St P), SatU P ∧ IsEmpty x.o.N.nd.Loc ∧ ∀ j v, x.o.η j v = 0

structure SameGal (D D' : D7) : Prop where
  gal : SameGalois D.nd D'.nd
  pl : HEq D.naut.plGw D'.naut.plGw

structure Carried (D D' : D7) : Prop where
  exp : SameExport D D'
  emb : ∀ (i : D.ntw.Tw) (i' : D'.ntw.Tw), HEq i i' → ∀ (x : D.LL0) (x' : D'.LL0),
    D.what₂.embLL (x : D.what₂.LL) = D'.what₂.embLL (x' : D'.what₂.LL) →
      HEq (D.ntw.emb0 i x) (D'.ntw.emb0 i' x') ∧ HEq (D.ntw.emb0b i x) (D'.ntw.emb0b i' x')

theorem SameGal.refl (D : D7) : SameGal D D := ⟨(SameExport.refl D).gal, HEq.rfl⟩

theorem Carried.refl (D : D7) : Carried D D := ⟨SameExport.refl D, fun i i' h x x' e => by
  obtain rfl := eq_of_heq h
  obtain rfl : x = x' := Subtype.ext (D.what₂.embLL.injective e)
  exact ⟨HEq.rfl, HEq.rfl⟩⟩

structure Seed (D : D7) (A : D.ntw.Tw → Finset (PlE D.host)) where
  s : D.what₂.places.Pl → D.ntw.Tw
  reads : ∀ v, ∃ b, ReadsAt (s v) b v
  conj : ∀ v, s (D.what₂.places.conj v) = s v
  same : ∀ v v', TwistedAt D v → TwistedAt D v' → OverOne D v v' → s v' = s v
  xd : ThData D
  all : XdAll xd
  N0 : D.ntw.Tw → ℕ
  S : ∀ (i : D.ntw.Tw) (j : ℕ) (b : Bool), Finset (D.nexp.Dat i j b)
  Q : D.ntw.Tw → Finset (PlE D.host)
  k : D.ntw.Tw → ℕ
  ψ : ∀ i, D.ntw.RCG i (Q i) →* (D.ntw.Ok i (k i))ˣ
  good : ∀ v, TwistedAt D v → TwIn.Ok (⟨twEOf xd, N0, S⟩ : TwIn D) (s v) ∧
    ∀ a : ℤ, Nat.Coprime a.natAbs (D.ntw.l (s v)) →
      IntegralHeckeForms.GoodTw D.nexp (BlochKatoReduction.bk0 D) (twEOf xd) N0 (s v) (twEps D (s v)) (S (s v)) (A (s v)) (Q (s v)) (k (s v)) (ψ (s v) ^ a)
  sep : ∀ v v', TwistedAt D v → TwistedAt D v' → s v ≠ s v' → Disjoint (Q (s v)) (Q (s v'))

def Seed.pack {D : D7} {A : D.ntw.Tw → Finset (PlE D.host)} (σ : Seed D A) (v : D.what₂.places.Pl) : TwPack D :=
  ⟨σ.s v, σ.Q (σ.s v), σ.k (σ.s v), σ.ψ (σ.s v)⟩

def Seed.ofUntw {D : D7} (A : D.ntw.Tw → Finset (PlE D.host)) (s : D.what₂.places.Pl → D.ntw.Tw) (h1 : ∀ v, ∃ b, ReadsAt (s v) b v)
    (h2 : ∀ v, s (D.what₂.places.conj v) = s v) (xd : ThData D) (h3 : XdAll xd) (h : ∀ v, ¬ TwistedAt D v) : Seed D A :=
  ⟨s, h1, h2, fun v _ hv => absurd hv (h v), xd, h3, fun _ => 0, fun _ _ _ => ∅, fun _ => ∅, fun _ => 0, fun _ => 1,
    fun v hv => absurd hv (h v), fun v _ hv => absurd hv (h v)⟩

def TwFrom (X : Stages) {A : X.toD7.ntw.Tw → Finset (PlE X.toD7.host)} (σ : Seed X.toD7 A) {B' : Base} (h : Enl X.B B')
    (T' : TwDat B') : Prop :=
  (∀ (v' : B'.places.Pl) (z : ℂ), z ^ B'.places.resChar v' ^ T'.k v' = 1 → ∃ x : B'.LL, B'.embLL x = z) ∧
  ∀ v' : B'.places.Pl,
    (TwistedAt X.toD7 (plUnder h v') →
      HEq (T'.Q v') (σ.Q (σ.s (plUnder h v'))) ∧ T'.k v' = σ.k (σ.s (plUnder h v')) ∧
      ∃ (ι : RootIso X.toD7 (σ.s (plUnder h v')) (σ.k (σ.s (plUnder h v')))) (χ : HChar X.toD7.host.E),
        FrobPick (σ.s (plUnder h v')) _ _ (σ.ψ (σ.s (plUnder h v'))) ι χ ∧ HEq (T'.psi v') χ) ∧
    (¬ TwistedAt X.toD7 (plUnder h v') → T'.psi v' = 1)

def BareK : Prop := StepW Start fun K B' f' _ w' => ∀ (P' : Pre2 K w') (X : Stages) (f : Fr X.B.toPre), B'.toPre = X.B.toPre →
  HEq f' f → GrpTrue X.N f → ∃ x' : St P', IsEmpty x'.o.N.nd.Loc ∧ SameGal X.toD7 (Dof x')

variable (hL : GlobalTheory.Published.LocalLanglandsGL)

def SAk : Prop := AllSt fun _ _ _ _ _ P x => IsEmpty x.o.N.nd.Loc →
  ∃ x' : St P, Nonempty (LA hL x') ∧ SameGal (Dof x) (Dof x')

def SCk : Prop := AllSt fun _ B _ T _ _ x => ∀ (l : StrictHenselianAcyclic hL x) (s : B.places.Pl → (Dof x).ntw.Tw),
  (∀ v, ∃ b, ReadsAt (D := Dof x) (s v) b v) → (∀ v, s (B.places.conj v) = s v) →
  ∃ c : StC l.mt l.b T.k T.psi, c.ch.twI = s

def MvB : Prop := StepW Start fun K B' f' _ w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl B B' →
  HEq f' f → Start K B f T w → HEq w'.px w.px → HEq w'.I.sel w.I.sel → HEq w'.I.J w.I.J → HEq w'.δ w.δ →
  ∀ (P : Pre2 K w) (x : St P), StrictHenselianAcyclic hL x → ∀ (P' : Pre2 K w'), Ext P.z P'.z → ∀ x' : St P', LI hL x' → SameGal (Dof x) (Dof x') →
    ∃ x'' : St P', Nonempty (StrictHenselianAcyclic hL x'') ∧ Carried (Dof x) (Dof x'') ∧ ∀ cDep : ℝ, ListSt cDep x → ListSt cDep x''

end GlobalTheory.HeightCounting.Up

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsVarietyConnectedComponentGenericFibreStatement
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_variety_connectedComponent_genericFibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F), SmoothOfRelativeDimension Dw.dim (genStr Z) → ∀ (Y : Var F) (π : Y.X ⟶ gen Z), π ≫ genStr Z ≫ spMap e.toRingHom = Y.str → ∃ (X : Var F) (j : X.X ⟶ gen Z), IsOpenImmersion j ∧ j ≫ genStr Z ≫ spMap e.toRingHom = X.str ∧ Set.range π ⊆ Set.range j := by
  first | exact @GlobalTheory.CompOfVar.exists_var_comp | exact GlobalTheory.CompOfVar.exists_var_comp | (intros; apply GlobalTheory.CompOfVar.exists_var_comp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentIntegralAll
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

namespace GlobalTheory.HeightCounting.Up

theorem eExp_int_of_third : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AllSt fun _ _ _ _ _ _ x => ∀ _ : LC hL x, ∀ j g, ∃ z : ℤ, eExp (Dof x) j g = z := by
  intro _ _
  refine StepW.of_all fun K B f T w _ _ _ P x _ j g => ?_
  exact ((Dof x).hc ((Dof x).eTau.symm g)).e_int j

end GlobalTheory.HeightCounting.Up
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentIntegralValued
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

namespace GlobalTheory.HeightCounting.Up

theorem eExp_int_allSt : PrN → AllSt fun _ _ _ _ _ _ x => ∀ (j : Fin (Dof x).R.m) (g : ↥((Dof x).R.Psi)), ∃ z : ℤ, eExp (Dof x) j g = (z : ℚ) := by
  intro _
  refine StepW.of_all fun K B f T w _ _ _ P x j g => ?_
  exact ((Dof x).hc ((Dof x).eTau.symm g)).e_int j

end GlobalTheory.HeightCounting.Up
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagCellsGlueLocallyClosedPluckerProductStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagCells_glue_locallyClosed_pluckerProduct : ∀ (O K : Type) [CommRing O] [IsNoetherianRing O] [Field K] (β : O →+* K) (X : Scheme.{0}) (s : X ⟶ Sp O) (T : Type) [Finite T] (m : T → ℕ) (M : ℕ) (B : Type) [Finite B] (V : B → X.affineOpens) (α : ∀ b, K →+* Γ(X, (V b).1)) (c D : ∀ b, Let m → Fin (M + 1) → Γ(X, (V b).1)) (P : Scheme.{0}) (p0 : P ⟶ X) (p : ∀ en : En m, P ⟶ PSpace O (plN M en.1)) (h : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ P)), IsProjOver s → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsCover β s V α c D → IsPlk β s V α c p0 p h → ∃ (F : Scheme.{0}) (f : F ⟶ P) (i : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ F)), IsImmersion f ∧ (∀ b w, IsOpenImmersion (i b w)) ∧ (∀ b w, i b w ≫ f = h b w) ∧ ∀ x : F, ∃ b w, x ∈ Set.range (i b w) := by
  first | exact @GlobalTheory.FlagEmb.cells_glue | exact GlobalTheory.FlagEmb.cells_glue | (intros; apply GlobalTheory.FlagEmb.cells_glue <;> assumption)
end

