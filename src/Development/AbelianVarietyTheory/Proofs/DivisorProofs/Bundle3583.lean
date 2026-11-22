import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3429
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3378
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3391
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3401
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3451
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3581
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2534
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureStalkFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2481
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3499
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3360
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3576
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3214
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2811
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2956
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2969
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3580
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3354
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3398
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3492
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3460
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2623
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2761
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3452
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3577
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreLiftCommTranslationSectionRatios
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

theorem GlobalTheory.HeatRatioW.exists_acts {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) {O : Type} [CommRing O]
    [StarRing O] [Module O Dd.toPre.X] {oa : Dd.toPre.OAct O} (Y : Ray oa) {n : ℕ}
    (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left) (hv : ∀ a, IsInv Y.H (v a) (dd a))
    (inst : Algebra ℤ R) (D : @Derivation ℤ R R _ _ _ inst _ _) (h : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D)
    (hb : IsBasic Y h) (k : ℕ) (α : Dd.toPre.X) (σ : Dd.toPre.SecB k α) : ∃ σ', TActs Y h k α σ σ' := by
  obtain rfl : inst = Ring.toIntAlgebra R := Subsingleton.elim _ _
  exact heat_acts_on_terms R Dd O oa Y n v dd hv D h hb k α σ

set_option maxHeartbeats 1600000 in

theorem GlobalTheory.HeatRatioW.dl_comm_transl_ratio : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r)))  → ∀ (A₀ : Over (Sp k)) (_ : GrpObj A₀) (m₀ : A₀.left ⟶ P.D.toPre.P.A.left), IsGrpPullback A₀ P.D.toPre.P.A (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)) m₀ → ∀ dl : ∀ W : P.D.toPre.P.A.left.Opens, Γ(P.D.toPre.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W), GlobalTheory.KS.LocDerK A₀.hom P.D.toPre.P.A.hom m₀ (fun r => (ρ r).snd) ⊤ dl → (∀ (Z' : Scheme.{0}) (a : Z' ⟶ Y.H.left) (b : Z' ⟶ A₀.left), a ≫ Y.q.left = b ≫ m₀ → ∀ (i : h.J) (W : P.D.toPre.P.A.left.Opens), Y.q.left ⁻¹ᵁ W ≤ h.W i → ∀ f, pbT b (dl W f) (b ⁻¹ᵁ (m₀ ⁻¹ᵁ W)) = pbT a (h.d i _ ((Y.q.left.app W).hom f)) (b ⁻¹ᵁ (m₀ ⁻¹ᵁ W))) → ∀ (y : P.D.toPre.X) (T₀ : A₀.left ⟶ A₀.left), T₀ ≫ m₀ = m₀ ≫ (lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A]).left → T₀ ≫ A₀.hom = A₀.hom → ∀ (N : ℕ), 1 ≤ N → ∀ (σ σ' : P.D.toPre.SecB N 0) (U : P.D.toPre.P.A.left.Opens) (f : Γ(P.D.toPre.P.A.left, U)), (∀ z ∈ U, ∀ J, Good P.D.toPre.P.L z J → IsUnit (sval σ' (𝟙 _) z J) ∧ sval σ (𝟙 _) z J = gs (𝟙 _) z U f * sval σ' (𝟙 _) z J) → dl ((lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A]).left ⁻¹ᵁ U) (((lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A]).left.app U).hom f) = pbT T₀ (dl U f) (m₀ ⁻¹ᵁ ((lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A]).left ⁻¹ᵁ U)) := by
  intro E _ _ _ H k _ _ m d t P gam hmon hli hab Y n' v' dd hdd D q hq h hb hdef hΘ ρ hρ A₀ grp m₀ hpb dl hdl
    hdesc y T₀ hT₀ hT₀' N hN σ σ' U f hf
  letI := H.starRing
  haveI : IsAdicComplete (maximalIdeal k) k := by rw [maximalIdeal_eq_bot]; infer_instance
  haveI : IsAdicComplete (maximalIdeal (ChartRing k m d)) (ChartRing k m d) :=
    GlobalTheory.PlaceInt.isAdicComplete_mvPowerSeries_finite (V := k) _
  have hr : GlobalTheory.HeatRatio.IsRatio P.D.toPre σ σ' U f := hf
  have hN2 : 1 ≤ 2 * N := by omega
  obtain ⟨ρ₁, ρ₁', hr2⟩ := GlobalTheory.HeatRatio.isRatio_square _ P.D.toPre N σ σ' U f hN hr
  have HA := fun (k' : ℕ) (α : P.D.toPre.X) (s : P.D.toPre.SecB k' α) =>
    GlobalTheory.HeatRatioW.exists_acts P.D Y v' dd hdd _ D h hb k' α s
  obtain ⟨σp, a1⟩ := HA N 0 σ
  obtain ⟨σp', a2⟩ := HA N 0 σ'
  obtain ⟨ρp, a3⟩ := HA (2 * N) 0 ρ₁
  obtain ⟨ρp', a4⟩ := HA (2 * N) 0 ρ₁'
  obtain ⟨g₁, hg₁⟩ := GlobalTheory.HeatRatio.exists_isRem _ P.D.toPre N 0 σ σ' σp σp' U f hr
  obtain ⟨g₂, hg₂⟩ := GlobalTheory.HeatRatio.exists_isRem _ P.D.toPre (2 * N) 0 ρ₁ ρ₁' ρp ρp' U f hr2
  have e1 := GlobalTheory.HeatRatio.Closed.closed_fibre_rem_indep E H k m d t P gam hmon hli hab Y n' v' dd hdd D q hq h hb hΘ ρ hρ A₀ grp m₀ hpb dl hdl
    hdesc N (2 * N) hN hN2 0 0 σ σ' σp σp' ρ₁ ρ₁' ρp ρp' U f g₁ g₂ hr hr2 a1 a2 a3 a4 hg₁ hg₂
  obtain ⟨β₁, s, s', sp, sp', b1, b2, b3, b4⟩ := GlobalTheory.T.translation_carries_ratioDatum_remainder E H k m d t P gam hmon hli hab Y n' v' dd hdd D q hq
    h hb hdef y N hN σ σ' σp σp' U f g₁ hr a1 a2 hg₁
  obtain ⟨β₂, r, r', rp, rp', c1, c2, c3, c4⟩ := GlobalTheory.T.translation_carries_ratioDatum_remainder E H k m d t P gam hmon hli hab Y n' v' dd hdd D q hq
    h hb hdef y (2 * N) hN2 ρ₁ ρ₁' ρp ρp' U f g₂ hr2 a3 a4 hg₂
  have e2 := GlobalTheory.HeatRatio.Closed.closed_fibre_rem_indep E H k m d t P gam hmon hli hab Y n' v' dd hdd D q hq h hb hΘ ρ hρ A₀ grp m₀ hpb dl hdl
    hdesc N (2 * N) hN hN2 β₁ β₂ s s' sp sp' r r' rp rp' _ _ _ _ b1 c1 b2 b3 c2 c3 b4 c4

  set T := (lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A]).left with hTdef
  have hle : m₀ ⁻¹ᵁ (T ⁻¹ᵁ U) ≤ T₀ ⁻¹ᵁ (m₀ ⁻¹ᵁ U) := by
    intro x hx
    have e : (T₀ ≫ m₀) x = (m₀ ≫ T) x := by rw [hT₀]
    show m₀ (T₀ x) ∈ U
    have e' : m₀ (T₀ x) = T (m₀ x) := by simpa using e
    rw [e']; exact hx
  have key : ∀ (φ ψ : A₀.left ⟶ P.D.toPre.P.A.left), φ = ψ → ∀ (h1 : m₀ ⁻¹ᵁ (T ⁻¹ᵁ U) ≤ φ ⁻¹ᵁ U)
      (h2 : m₀ ⁻¹ᵁ (T ⁻¹ᵁ U) ≤ ψ ⁻¹ᵁ U), φ.appLE U _ h1 = ψ.appLE U _ h2 := by
    rintro φ _ rfl _ _; rfl
  have L5 : ∀ g : Γ(P.D.toPre.P.A.left, U), (m₀.app (T ⁻¹ᵁ U)).hom ((T.app U).hom g) =
      (T₀.appLE (m₀ ⁻¹ᵁ U) (m₀ ⁻¹ᵁ (T ⁻¹ᵁ U)) hle).hom ((m₀.app U).hom g) := by
    intro g
    have c1 := Scheme.Hom.comp_appLE m₀ T U (m₀ ⁻¹ᵁ (T ⁻¹ᵁ U)) le_rfl
    have c2 := Scheme.Hom.comp_appLE T₀ m₀ U (m₀ ⁻¹ᵁ (T ⁻¹ᵁ U)) (le_trans hle le_rfl)
    have c3 := key _ _ hT₀ (le_trans hle le_rfl) le_rfl
    have := congrArg (fun φ => φ.hom g) (c2.symm.trans (c3.trans c1))
    simpa [Scheme.Hom.app_eq_appLE] using this.symm
  rw [pbT, dif_pos hle]
  set φ := (T₀.appLE (m₀ ⁻¹ᵁ U) (m₀ ⁻¹ᵁ (T ⁻¹ᵁ U)) hle).hom
  rw [L5, L5] at e2
  have h1 : (2 * N : Γ(A₀.left, m₀ ⁻¹ᵁ U)) * dl U f = (m₀.app U).hom g₂ - (m₀.app U).hom g₁ := by
    push_cast at e1; linear_combination e1
  have h2 : (2 * N : Γ(A₀.left, m₀ ⁻¹ᵁ (T ⁻¹ᵁ U))) * dl _ ((T.app U).hom f) =
      φ ((m₀.app U).hom g₂) - φ ((m₀.app U).hom g₁) := by
    push_cast at e2; linear_combination e2
  rw [← map_sub, ← h1, map_mul, map_mul, map_ofNat, map_natCast] at h2
  have hu : IsUnit (2 * N : Γ(A₀.left, m₀ ⁻¹ᵁ (T ⁻¹ᵁ U))) := by
    let ψ : k →+* Γ(A₀.left, m₀ ⁻¹ᵁ (T ⁻¹ᵁ U)) :=
      (A₀.hom.appLE ⊤ (m₀ ⁻¹ᵁ (T ⁻¹ᵁ U)) le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
    have hk : IsUnit (2 * N : k) := by
      refine IsUnit.mk0 _ ?_
      exact_mod_cast (by omega : 2 * N ≠ 0)
    have := hk.map ψ
    rwa [map_mul, map_ofNat, map_natCast] at this
  exact hu.mul_left_cancel h2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeepEqOfCongMod
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc.DeepSame

theorem deep_eq_of_congMod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X₁ : USetup C) (D : UDeep X₁) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (z₂ : D.X.M.Z), D.q z₂ = z₁ → ∀ (f : D.X.S.Gam → X₁.S.HH X₁.M z₁ → D.X.Ω₁) (t : ∀ (ct : UCTrait X₁ p z₁) (_ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) ct.T.P.D.toPre.X), ct.T.P.D.toPre.X → X₁.S.HH X₁.M z₁ → PadicAlgCl p), (∀ a κ (z' : D.X.M.Z), D.q z' = z₁ → f a κ ∈ D.X.M.O z') → (∀ (ct : UCTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) ct.T.P.D.toPre.X), UIsLab X₁ ct yy₁ → ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = ct.y), y (cPt p) = z₂ → ∀ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) ct.T.P.D.toPre.X, UIsLab D.X (D.lift ct y h) yy → D.Compat yy₁ yy → ∀ a ν κ, yy a = QuotientAddGroup.mk ν → ∀ δ : ℝ, 0 < δ → ∃ S₀ : Finset ct.T.P.D.toPre.X, ∀ S : Finset ct.T.P.D.toPre.X, (∀ μ ∈ S, CongMod D.m μ ν) → (∀ μ ∈ S₀, CongMod D.m μ ν → μ ∈ S) → ‖D.X.M.val (gPt p ≫ y) (f a κ) - ∑ μ ∈ S, t ct yy₁ μ κ‖ ≤ δ) → ∀ (w₁ : UWit X₁) (w₂ : UWit D.X), D.Comparison₂ w₁ w₂ → IsProjOver D.X.M.s → ∀ (ct₀ : UCTrait D.X p z₂) (yy₀ : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) ct₀.T.P.D.toPre.X), UIsLabW D.X w₂ ct₀ yy₀ → ∀ (a a' : D.X.S.Gam) (ν ν' : ct₀.T.P.D.toPre.X), yy₀ a = QuotientAddGroup.mk ν → yy₀ a' = QuotientAddGroup.mk ν' → CongMod D.m ν ν' → ∀ κ, f a κ = f a' κ := by
  intro E _ _ _ H Dw hpq l Xo cf C X₁ D p _ z₁ z₂ hz f t hf hsum w₁ w₂ htie hproj ct₀ yy₀ hyy₀ a a' ν ν' ha ha' hcong κ
  obtain ⟨U₁, hU₁, hct⟩ := GlobalTheory.UPoinc.UCTraitEx.exists_uCTrait_of_open E H Dw hpq l Xo cf C X₁ p
  have hU : ((D.q ⁻¹ᵁ U₁ : D.X.M.Z.Opens) : Set D.X.M.Z).Nonempty :=
    GlobalTheory.Poinc.FinPts.preimage_nonempty D.gen hU₁
  have hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme D.X.M.Z := by
    have := D.X.normal
    intro x
    exact ⟨inferInstance, inferInstance⟩
  have hfa : f a κ ∈ D.X.M.O z₂ := hf a κ z₂ hz
  have hfa' : f a' κ ∈ D.X.M.O z₂ := hf a' κ z₂ hz
  have hb : f a κ - f a' κ ∈ D.X.M.O (ct₀.y (cPt p)) := by
    rw [ct₀.cen]; exact sub_mem hfa hfa'
  have key := GlobalTheory.Poinc.eq_zero_of_val_cen_eq_zero D.X.o₁ D.X.Ω₁ D.X.M hN (D.q ⁻¹ᵁ U₁) hU p ct₀.y
    (f a κ - f a' κ) hb ?_
  · exact sub_eq_zero.1 key
  intro y' hy'
  obtain ⟨hcen, hrange⟩ := hy'
  rw [ct₀.cen] at hcen
  have hr₁ : Set.range (gPt p ≫ (y' ≫ D.q)) ⊆ (U₁ : Set X₁.M.Z) := by
    rintro _ ⟨w, rfl⟩
    exact hrange ⟨w, rfl⟩
  obtain ⟨ct', hct'⟩ := hct (y' ≫ D.q) hr₁
  have hz₁ : (y' ≫ D.q) (cPt p) = z₁ := by rw [← hz, ← hcen]; rfl
  let ct₁ : UCTrait X₁ p z₁ :=
    { y := y' ≫ D.q, cen := hz₁, T := ct'.T, ι := ct'.ι, int := ct'.int,
      comm := by have hc := ct'.comm; rw [hct'] at hc; exact hc }
  obtain ⟨yy₁, hyy₁⟩ := GlobalTheory.T.exists_labels_unitaryClassicalTrait E H Dw hpq l Xo cf C X₁ w₁ p z₁ ct₁
  obtain ⟨yy, hyy, hcomp⟩ := GlobalTheory.T.unitary_trait_labels_extend_to_deeper_level E H Dw hpq l Xo cf C X₁ D w₁ w₂ htie p z₁ ct₁ yy₁ hyy₁ y' rfl
  let ct₂ : UCTrait D.X p z₂ := { D.lift ct₁ y' rfl with cen := hcen }
  have hyy₂ : UIsLabW D.X w₂ ct₂ yy := hyy
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_linearEquiv_labelledLattices_unitaryTraits E H Dw hpq l Xo cf C D.X w₂ hproj p z₂ ct₀ ct₂ yy₀ yy hyy₀ hyy₂
  have h1 := he a ν ha
  have h2 := he a' ν' ha'
  obtain ⟨w, hw⟩ := hcong
  have hc : CongMod D.m (e ν) (e ν') := ⟨e w, by rw [hw, map_add, map_nsmul]⟩
  have hfin : ∀ δ : ℝ, 0 < δ → ‖D.X.M.val (gPt p ≫ y') (f a κ) - D.X.M.val (gPt p ≫ y') (f a' κ)‖ ≤ 2 * δ := by
    intro δ hδ
    obtain ⟨S₀, hS₀⟩ := hsum ct₁ yy₁ hyy₁.uIsLab y' rfl hcen yy hyy.uIsLab hcomp a (e ν) κ h1 δ hδ
    obtain ⟨S₀', hS₀'⟩ := hsum ct₁ yy₁ hyy₁.uIsLab y' rfl hcen yy hyy.uIsLab hcomp a' (e ν') κ h2 δ hδ
    let S := (S₀ ∪ S₀').filter (fun μ => CongMod D.m μ (e ν))
    have A := hS₀ S (fun μ hμ => (Finset.mem_filter.1 hμ).2)
      (fun μ hμ hc' => Finset.mem_filter.2 ⟨Finset.mem_union_left _ hμ, hc'⟩)
    have B := hS₀' S
      (fun μ hμ => by
        obtain ⟨w₁', hw₁'⟩ := (Finset.mem_filter.1 hμ).2
        obtain ⟨w₂', hw₂'⟩ := hc
        exact ⟨w₁' + w₂', by rw [hw₁', hw₂', smul_add]; abel⟩)
      (fun μ hμ hc' => by
        refine Finset.mem_filter.2 ⟨Finset.mem_union_right _ hμ, ?_⟩
        obtain ⟨w₁', hw₁'⟩ := hc'
        obtain ⟨w₂', hw₂'⟩ := hc
        exact ⟨w₁' - w₂', by rw [hw₁', hw₂', smul_sub]; abel⟩)
    calc ‖D.X.M.val (gPt p ≫ y') (f a κ) - D.X.M.val (gPt p ≫ y') (f a' κ)‖
        = ‖(D.X.M.val (gPt p ≫ y') (f a κ) - ∑ μ ∈ S, t ct₁ yy₁ μ κ) -
            (D.X.M.val (gPt p ≫ y') (f a' κ) - ∑ μ ∈ S, t ct₁ yy₁ μ κ)‖ := by congr 1; abel
      _ ≤ ‖D.X.M.val (gPt p ≫ y') (f a κ) - ∑ μ ∈ S, t ct₁ yy₁ μ κ‖ +
            ‖D.X.M.val (gPt p ≫ y') (f a' κ) - ∑ μ ∈ S, t ct₁ yy₁ μ κ‖ := norm_sub_le _ _
      _ ≤ δ + δ := add_le_add A B
      _ = 2 * δ := by ring
  have hxx : D.X.M.val (gPt p ≫ y') (f a κ) = D.X.M.val (gPt p ≫ y') (f a' κ) := by
    by_contra hne
    have hpos : 0 < ‖D.X.M.val (gPt p ≫ y') (f a κ) - D.X.M.val (gPt p ≫ y') (f a' κ)‖ :=
      norm_pos_iff.2 (sub_ne_zero.2 hne)
    have := hfin (‖D.X.M.val (gPt p ≫ y') (f a κ) - D.X.M.val (gPt p ≫ y') (f a' κ)‖ / 4) (by positivity)
    linarith
  have hsp : ∀ w, (gPt p ≫ y') w ⤳ z₂ := GlobalTheory.ZH.RatModel.gPt_specializes hcen
  have hadd := GlobalTheory.ZH.RatModel.val_add hsp (sub_mem hfa hfa') hfa'
  rw [sub_add_cancel] at hadd
  rw [hadd] at hxx
  simpa using hxx

end GlobalTheory.UPoinc.DeepSame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorStalkEvaluationLinearMapFamily
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

namespace GlobalTheory.Poinc.Sep

theorem sub_mem_of_sumI {V Ix : Type} [CommRing V] {I : Ideal V} {y : Ix → V} {v : V} (h : SumI I y v) (i₀ : Ix)
    (hy : ∀ j, j ≠ i₀ → y j ∈ I) : v - y i₀ ∈ I := by
  classical
  obtain ⟨N, -, -, -, hS⟩ := h
  obtain ⟨S, hS⟩ := hS 1
  have h1 := Submodule.smul_mono (le_refl (I ^ 1)) (le_top : N ≤ ⊤) (hS (insert i₀ S) (Finset.subset_insert _ _))
  rw [pow_one, smul_eq_mul, Ideal.mul_top, ← Finset.add_sum_erase _ _ (Finset.mem_insert_self i₀ S)] at h1
  have h2 : ∑ j ∈ (insert i₀ S).erase i₀, y j ∈ I :=
    Submodule.sum_mem _ fun j hj => hy j (Finset.ne_of_mem_erase hj)
  have := add_mem h1 h2
  convert this using 1
  ring

private theorem sum_terms_universal_member {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
    {X₁ : Setup F W i} {z₁ : X₁.M.Z} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V} {X : Type} [AddCommGroup X]
    {m : ℕ} {t : Fin m → V} {δ : Fin m → LinearMap.BilinForm ℤ X} (𝔪 : UMem X₁ z₁ act V ev X t δ)
    {x₀ : X₁.S.Gam} {C : Type} {lab : C → X₁.S.Gam} {T : (Fin 8 → X) → C → V} (h : 𝔪.Terms x₀ lab T) (c : C) :
    SumF (maximalIdeal V) (FractionRing V)
      (fun χ => algebraMap V (FractionRing V) (T (𝔪.e₈.symm χ) c) * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩)
      (𝔪.yK ⟨X₁.S.th (lab c), X₁.S.th_mem _⟩) := by
  obtain ⟨x, fr, th, w₀, s, g', w, -, -, hth, -, hs, hc, hT⟩ := h
  have := (hc c).2.2 1 le_rfl (w c) (fun z J _ => (pow_one _).symm) (hc c).2.1 th s _ hs (hth (lab c))
  convert this using 2 with χ
  rw [hT, AddEquiv.apply_symm_apply]

theorem UMem.const_term_sub_mem : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (m1 : ℕ) (t1 : Fin m1 → V1) (δ1 : Fin m1 → LinearMap.BilinForm ℤ Y1) (𝔪1 : UMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : (Fin 8 → Y1) → C → V1, 𝔪1.Terms x₀ lab T → ∀ (c : C) (r : X₁.M.Z.presheaf.stalk z₁), X₁.M.stalkHom z₁ r = X₁.S.th (lab c) / X₁.S.th x₀ → ev1 r - T 0 c ∈ maximalIdeal V1 := by
  intro g n F W Z i X₁ z₁ act x₀ hd V _ _ _ ev X _ m t δ 𝔪 C lab hlab T hT c r hr
  haveI : IsNoetherianRing V := 𝔪.cn.1
  haveI : IsLocalHom ev := 𝔪.loc
  have hθ := UMem.yK_th_ne_zero g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 x₀ hd
  have sp : ∀ w, X₁.M.Z.fromSpecStalk z₁ w ⤳ z₁ := fun w => by
    have : X₁.M.Z.fromSpecStalk z₁ w ∈ Set.range (X₁.M.Z.fromSpecStalk z₁) := ⟨w, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  have hd' := hd.of_specializes
    (ξ := (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint (FractionRing V))) (sp _)
  have hs : ∀ w, (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) w ⤳
      (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint (FractionRing V)) :=
    RatModel.specializes_of_range_eq (RatModel.range_eq_singleton _ _)
  have e := RatModel.val_mul hs (hd'.2 (lab c)) (𝔪.reg _ (X₁.S.th_mem x₀))
  rw [div_mul_cancel₀ _ hd.1, ← hr, TwistSum₂.val_stalkHom] at e
  have e' : 𝔪.yK ⟨X₁.S.th (lab c), X₁.S.th_mem _⟩ =
      algebraMap V (FractionRing V) (ev r) * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ := by
    rw [𝔪.yK_eq, 𝔪.yK_eq]
    exact e
  have hS := sum_terms_universal_member 𝔪 hT c
  rw [e'] at hS
  have hI := TwistSum₂.sumI_of_sumF_mul (fun χ => T (𝔪.e₈.symm χ) c) (ev r) _ hθ hS
  have := sub_mem_of_sumI hI 0 fun j hj =>
    GlobalTheory.T.thetaModelMember_term_mem_maximalIdeal g n F W Z i X₁ z₁ act x₀ hd V ev X m t δ 𝔪 C lab hlab T hT c _ (𝔪.e₈.symm.map_ne_zero_iff.2 hj)
  simpa only [map_zero] using this

end GlobalTheory.Poinc.Sep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndCharpolyTateDetDegreeTraceStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.endCharpoly_tate_det_degree_trace : ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ (A : AbVar K) (f : End A), (∀ [Module.Finite ℚ_[l] (Vl l A)], (charpoly f).map (algebraMap ℤ ℚ_[l]) = (vmap l (A := A) (B := A) f).charpoly) ∧ (∀ [Module.Free ℤ_[l] (Tl l A)] [Module.Finite ℤ_[l] (Tl l A)], (charpoly f).map (algebraMap ℤ ℤ_[l]) = (tend l A f).charpoly) ∧ LinearMap.det (vmap l (A := A) (B := A) f) = (deg (A := A) (B := A) f : ℚ_[l]) ∧ LinearMap.trace ℚ_[l] _ (vmap l (A := A) (B := A) f) = (trace f : ℚ_[l]) := by
  first | (exact @GlobalTheory.AV.AbVar.charpoly_tate_det_trace) | (exact GlobalTheory.AV.AbVar.charpoly_tate_det_trace) | (intros; apply GlobalTheory.AV.AbVar.charpoly_tate_det_trace  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfClassSumApprox
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc.GalLab

theorem eq_of_classSum_approx {X K : Type} [AddCommGroup X] [NormedAddCommGroup K] (m : ℕ) (τ : X → K) (ν ν' : X)
    (h : CongMod m ν ν') (u v : K)
    (hu : ∀ δ : ℝ, 0 < δ → ∃ S₀ : Finset X, ∀ S : Finset X, (∀ μ ∈ S, CongMod m μ ν) →
      (∀ μ ∈ S₀, CongMod m μ ν → μ ∈ S) → ‖u - ∑ μ ∈ S, τ μ‖ ≤ δ)
    (hv : ∀ δ : ℝ, 0 < δ → ∃ S₀ : Finset X, ∀ S : Finset X, (∀ μ ∈ S, CongMod m μ ν') →
      (∀ μ ∈ S₀, CongMod m μ ν' → μ ∈ S) → ‖v - ∑ μ ∈ S, τ μ‖ ≤ δ) : u = v := by
  obtain ⟨w, hw⟩ := h
  have key : ∀ μ, CongMod m μ ν ↔ CongMod m μ ν' := fun μ =>
    ⟨fun ⟨x, hx⟩ => ⟨w + x, by rw [hx, hw, smul_add, add_assoc]⟩,
      fun ⟨x, hx⟩ => ⟨x - w, by rw [hx, hw, smul_sub]; abel⟩⟩
  rw [← sub_eq_zero, ← norm_le_zero_iff]
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  obtain ⟨S₀, h₀⟩ := hu (δ / 2) (half_pos hδ)
  obtain ⟨S₁, h₁⟩ := hv (δ / 2) (half_pos hδ)
  have a := h₀ ((S₀ ∪ S₁).filter fun μ => CongMod m μ ν) (fun μ hμ => (Finset.mem_filter.1 hμ).2)
    fun μ hμ hc => Finset.mem_filter.2 ⟨Finset.mem_union_left _ hμ, hc⟩
  have b := h₁ ((S₀ ∪ S₁).filter fun μ => CongMod m μ ν) (fun μ hμ => (key μ).1 (Finset.mem_filter.1 hμ).2)
    fun μ hμ hc => Finset.mem_filter.2 ⟨Finset.mem_union_right _ hμ, (key μ).2 hc⟩
  have c := norm_sub_le_norm_sub_add_norm_sub u (∑ μ ∈ (S₀ ∪ S₁).filter fun μ => CongMod m μ ν, τ μ) v
  rw [norm_sub_rev] at b
  linarith

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X₁ : USetup C) (D : UDeep X₁) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (z₂ : D.X.M.Z), D.q z₂ = z₁ → ∀ (f : D.X.S.Gam → X₁.S.HH X₁.M z₁ → D.X.Ω₁) (t : ∀ (ct : UCTrait X₁ p z₁) (_ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) ct.T.P.D.toPre.X), ct.T.P.D.toPre.X → X₁.S.HH X₁.M z₁ → PadicAlgCl p), (∀ a κ (z' : D.X.M.Z), D.q z' = z₁ → f a κ ∈ D.X.M.O z') → (∀ (ct : UCTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) ct.T.P.D.toPre.X), UIsLab X₁ ct yy₁ → ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = ct.y), y (cPt p) = z₂ → ∀ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) ct.T.P.D.toPre.X, UIsLab D.X (D.lift ct y h) yy → D.Compat yy₁ yy → ∀ a ν κ, yy a = QuotientAddGroup.mk ν → ∀ δ : ℝ, 0 < δ → ∃ S₀ : Finset ct.T.P.D.toPre.X, ∀ S : Finset ct.T.P.D.toPre.X, (∀ μ ∈ S, CongMod D.m μ ν) → (∀ μ ∈ S₀, CongMod D.m μ ν → μ ∈ S) → ‖D.X.M.val (gPt p ≫ y) (f a κ) - ∑ μ ∈ S, t ct yy₁ μ κ‖ ≤ δ) → ∀ (w₁ : UWit X₁) (w₂ : UWit D.X), D.Comparison₂ w₁ w₂ → IsProjOver D.X.M.s → ∀ (σ' : D.X.Ω₁ ≃ₐ[X₁.Ω₁] D.X.Ω₁) (s : D.X.M.Z ⟶ D.X.M.Z), s ≫ D.q = D.q → (∀ (K : Type) [Field K] (y : Sp K ⟶ D.X.M.Z) (b : D.X.Ω₁), D.X.M.val (y ≫ s) b = D.X.M.val y (σ' b)) → s z₂ = z₂ → ∀ aσ : D.X.S.Gam ≃+ D.X.S.Gam, (∀ (ct : UCTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) ct.T.P.D.toPre.X), UIsLab X₁ ct yy₁ → ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = ct.y) (h' : (y ≫ s) ≫ D.q = ct.y) (yy yy' : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) ct.T.P.D.toPre.X), UIsLab D.X (D.lift ct y h) yy → D.Compat yy₁ yy → UIsLab D.X (D.lift ct (y ≫ s) h') yy' → D.Compat yy₁ yy' → ∀ x, yy' x = yy (aσ x)) → ∀ (ct₀ : UCTrait D.X p z₂) (yy₀ : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) ct₀.T.P.D.toPre.X), UIsLabW D.X w₂ ct₀ yy₀ → ∀ (a a' : D.X.S.Gam) (ν ν' : ct₀.T.P.D.toPre.X), yy₀ (aσ a) = QuotientAddGroup.mk ν → yy₀ a' = QuotientAddGroup.mk ν' → CongMod D.m ν ν' → ∀ κ, σ' (f a κ) = f a' κ := by
  intro E _ _ _ H Dw hpq l Xo cf C X₁ D p _ z₁ z₂ hz f t hf hsum w₁ w₂ htie hproj σ' s hs hval hsz aσ haσ ct₀ yy₀ hl₀
    a a' ν ν' ha ha' hνν' κ
  have hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme D.X.M.Z :=
    fun x => ⟨D.X.normal.isDomain_stalk x, D.X.normal.isIntegrallyClosed_stalk x⟩
  have hσ : σ' (f a κ) ∈ D.X.M.O z₂ := by
    letI : Algebra (X₁.M.Z.presheaf.stalk z₁) D.X.Ω₁ :=
      ((algebraMap X₁.Ω₁ D.X.Ω₁).comp (X₁.M.stalkHom z₁)).toAlgebra
    have halg : ∀ x, algebraMap (X₁.M.Z.presheaf.stalk z₁) D.X.Ω₁ x =
      algebraMap X₁.Ω₁ D.X.Ω₁ (X₁.M.stalkHom z₁ x) := fun _ => rfl
    let φ : D.X.Ω₁ →ₐ[X₁.M.Z.presheaf.stalk z₁] D.X.Ω₁ :=
      { (σ' : D.X.Ω₁ →+* D.X.Ω₁) with commutes' := fun x => σ'.commutes (X₁.M.stalkHom z₁ x) }
    exact FinPts.mem_O_of_isIntegral hN D.gen halg
      ((FinPts.isIntegral_of_mem_O D.fin D.gen halg (hf a κ)).map φ) hz
  have hf' : f a' κ ∈ D.X.M.O z₂ := hf a' κ z₂ hz
  obtain ⟨U₁, hU₁, hct⟩ := GlobalTheory.UPoinc.UCTraitEx.exists_uCTrait_of_open E H Dw hpq l Xo cf C X₁ p
  have hc₀ := ct₀.cen
  rw [← sub_eq_zero]
  refine eq_zero_of_val_cen_eq_zero _ _ D.X.M hN (D.q ⁻¹ᵁ U₁) (FinPts.preimage_nonempty D.gen hU₁) p ct₀.y _
    (by rw [hc₀]; exact sub_mem hσ hf') fun y hy => ?_
  obtain ⟨hy, hyU⟩ := hy
  rw [hc₀] at hy
  obtain ⟨ct₁, hct₁⟩ := hct (y ≫ D.q) (by
    rintro _ ⟨w, rfl⟩
    exact hyU ⟨w, rfl⟩)
  have hz₁ : (y ≫ D.q) (cPt p) = z₁ := by rw [← hz, ← hy]; rfl
  let ct : UCTrait X₁ p z₁ := { ct₁ with cen := ct₁.cen.trans hz₁ }
  have h : y ≫ D.q = ct.y := hct₁.symm
  have h' : (y ≫ s) ≫ D.q = ct.y := by rw [Category.assoc, hs, h]
  have hys : (y ≫ s) (cPt p) = z₂ := by
    show s (y (cPt p)) = z₂
    rw [hy, hsz]
  obtain ⟨yy₁, hl₁⟩ := GlobalTheory.T.exists_labels_unitaryClassicalTrait E H Dw hpq l Xo cf C X₁ w₁ p z₁ ct
  obtain ⟨yy, hl, hco⟩ := GlobalTheory.T.unitary_trait_labels_extend_to_deeper_level E H Dw hpq l Xo cf C X₁ D w₁ w₂ htie p z₁ ct yy₁ hl₁ y h
  obtain ⟨yy', hl', hco'⟩ := GlobalTheory.T.unitary_trait_labels_extend_to_deeper_level E H Dw hpq l Xo cf C X₁ D w₁ w₂ htie p z₁ ct yy₁ hl₁ (y ≫ s) h'
  have hyy := haσ ct yy₁ hl₁.uIsLab y h h' yy yy' hl.uIsLab hco hl'.uIsLab hco'
  let ct₂ : UCTrait D.X p z₂ := { D.lift ct y h with cen := hy }
  obtain ⟨d, hd⟩ := exists_linearEquiv_labelled_of_uIsLabW E H Dw hpq l Xo cf C D.X w₂ hproj p z₂ ct₀ ct₂ yy₀ yy
    hl₀ hl
  have hdν : CongMod D.m (d ν) (d ν') := by
    obtain ⟨w, hw⟩ := hνν'
    exact ⟨d w, by rw [hw, map_add, map_nsmul]⟩
  have e := eq_of_classSum_approx D.m (fun μ => t ct yy₁ μ κ) _ _ hdν _ _
    (hsum ct yy₁ hl₁.uIsLab (y ≫ s) h' hys yy' hl'.uIsLab hco' a (d ν) κ ((hyy a).trans (hd _ _ ha)))
    (hsum ct yy₁ hl₁.uIsLab y h hy yy hl.uIsLab hco a' (d ν') κ (hd _ _ ha'))
  rw [← Category.assoc, hval] at e
  have hsp : ∀ w, (gPt p ≫ y) w ⤳ z₂ := RatModel.gPt_specializes hy
  have e' := map_sub (RatModel.valHomOf _ z₂ hsp) ⟨_, hσ⟩ ⟨_, hf'⟩
  exact e'.trans (sub_eq_zero.2 e)

end GlobalTheory.UPoinc.GalLab
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineScalarTorusInvariantHeatOperators
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatUniq

theorem exists_affine_scalar : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [Algebra ℚ R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (h h' : Heat Y.H Y.q.left Q.P.L dd ⇑D), IsBasic Y h → IsBasic Y h' → h.Θ = h'.Θ → h.u = h'.u → ∃ (ℓ : Q.X →+ R) (π π' : R), ∀ (k : ℕ) (α : Q.X) (σ σ' σ'' : Q.SecB k α), TActs Y h k α σ σ' → TActs Y h' k α σ σ'' → ∀ (T : Over (Sp R)) (x : T ⟶ Q.P.A) z J, Good Q.P.L z J → sval σ'' x.left z J = sval σ' x.left z J + gs (𝟙 _) z ⊤ (scal T.hom (2 * (k : R) * ℓ α + 2 * (k : R) ^ 2 * π + 2 * (k : R) * π')) * sval σ x.left z J := by
  intro R _ _ _ _ _ Q O _ _ _ oa Y n v dd hdd D h' h hb' hb hΘ' hu'
  have hΘ : h.Θ = h'.Θ := hΘ'.symm
  have hu : h.u = h'.u := hu'.symm
  obtain ⟨e, π, π', hT, hG⟩ := GlobalTheory.T.torusInvariant_heatOperators_difference_global R Q O oa Y n v dd hdd D h h' hb hb' hΘ hu
  obtain ⟨ℓ, hℓ⟩ := GlobalTheory.T.exists_addHom_invariantField_kills_weightZero R Q O oa Y n v dd hdd e hT
  refine ⟨ℓ, π, π', ?_⟩
  intro k α σ σ'' σ' h1' h1 T x z J hJ
  refine GlobalTheory.T.heat_operator_fourier_term_values_eq_of_local_identity R Q O oa Y n v dd hdd D h h' hb hb'
    (fun k α => 2 * (k : R) * ℓ α + 2 * (k : R) ^ 2 * π + 2 * (k : R) * π') ?_ k α σ σ' σ'' h1 h1' T x z J hJ
  intro i i' k α V hV f hf
  obtain ⟨h2d, h3, h4⟩ := hG i i' _ hV
  simp only [dlg] at h2d h3 h4
  have hle : Y.q.left ⁻¹ᵁ V ≤ Y.q.left ⁻¹ᵁ (Q.P.L.U (h.j i) ⊓ Q.P.L.U (h'.j i')) := fun pt hpt =>
    ⟨h.le i (hV hpt).1, h'.le i' (hV hpt).2⟩
  have hg : pbT Y.q.left (Q.P.L.g (h.j i) (h'.j i')).val (Y.q.left ⁻¹ᵁ V) *
      pbT Y.q.left (Q.P.L.g (h.j i) (h'.j i'))⁻¹.val (Y.q.left ⁻¹ᵁ V) = 1 := by
    unfold pbT
    rw [dif_pos hle, dif_pos hle, ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  have mono : ∀ (δ : Fld Y.H.left) {W₁ W₂ : Y.H.left.Opens}, W₁ ≤ W₂ → IsField W₂ δ → IsField W₁ δ :=
    fun δ W₁ W₂ hle H => ⟨fun W hW => H.1 W (hW.trans hle), fun W hW => H.2.1 W (hW.trans hle),
      fun W W' hh hW => H.2.2 W W' hh (hW.trans hle)⟩
  rw [GlobalTheory.T.heatOperator_conj_unitPow_corrections R Y.H n dd h.Θ h.symm h.u (h.d i) (h.W i) (h.W i) _ (h.p i) (h.p' i) k _ _ hg (hV.trans inf_le_left)
    (h.lift i).1 (fun a => mono _ le_top (hdd a).1) f]
  congr 1
  have hc : constFn Y.H.hom (Y.q.left ⁻¹ᵁ V) (2 * (k : R) * ℓ α + 2 * (k : R) ^ 2 * π + 2 * (k : R) * π') =
      2 * (k : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V)) * constFn Y.H.hom _ (ℓ α) +
        2 * (k : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V)) ^ 2 * constFn Y.H.hom _ π +
        2 * (k : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V)) * constFn Y.H.hom _ π' := by
    simp only [constFn, map_add, map_mul, map_pow, map_natCast, map_ofNat]
  simp only [hc]
  have hl := hℓ α V f hf
  unfold op
  rw [← hΘ, ← hu]
  linear_combination (2 * (k : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V))) * h2d f + (k : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V)) ^ 2 * f * h3 +
    (k : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V)) * f * h4 + 2 * (k : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V)) * hl

end GlobalTheory.HeatUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCarriedFrameNearClosedFibreStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_carried_frame_near_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hB : Base R) (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R') (hF : FinExt ρ) (hG : IsGal ρ) (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (hS' : IsSemiAbelian G') (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left) (hS : IsSemiAbelian G) (hβ : IsGrpPullback G' G (spMap ρ) β) (hact : ∀ σ, a.act σ ≫ β = β), ∀ y : G.left, G.hom y = closedPoint R → ∃ V : G.left.Opens, y ∈ V ∧ ∃ T : ∀ k : U'.LG.L.ι, Γ(G'.left, β ⁻¹ᵁ V ⊓ U'.LG.L.U k)ˣ, IsFrameOver U'.LG.L (β ⁻¹ᵁ V) T ∧ ∀ (σ : Gal ρ) (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'), bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ → ∀ hP : IsPullUnif (Gal.hom σ) h bc U' U', PullOver hD h → FrameCarried U'.LG.L (β ⁻¹ᵁ V) T _ (Classical.choose hP.lg) := by
  first | exact @GlobalTheory.Mum.FrameCarried.exists_near_closed_fibre | exact GlobalTheory.Mum.FrameCarried.exists_near_closed_fibre | (intros; apply GlobalTheory.Mum.FrameCarried.exists_near_closed_fibre <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCarriedSectionOffClosedFibreStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_carried_section_off_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hB : Base R) (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R') (hF : FinExt ρ) (hG : IsGal ρ) (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (hS' : IsSemiAbelian G') (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left) (hS : IsSemiAbelian G) (hβ : IsGrpPullback G' G (spMap ρ) β) (hact : ∀ σ, a.act σ ≫ β = β), ∀ y : G.left, G.hom y ≠ closedPoint R → ∃ V : G.left.Opens, y ∈ V ∧ ∃ s : ∀ k : U'.LG.L.ι, Γ(G'.left, β ⁻¹ᵁ V ⊓ U'.LG.L.U k), IsSecOver U'.LG.L (β ⁻¹ᵁ V) s ∧ (∀ (z : G'.left) (k : U'.LG.L.ι), β z = y → z ∈ U'.LG.L.U k → IsUnit (gs (𝟙 G'.left) z (β ⁻¹ᵁ V ⊓ U'.LG.L.U k) (s k))) ∧ ∀ σ : Gal ρ, ∃ (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'), bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ ∧ ∃ hP : IsPullUnif (Gal.hom σ) h bc U' U', PullOver hD h ∧ SecCarriedOver U'.LG.L (β ⁻¹ᵁ V) s _ (Classical.choose hP.lg) := by
  first | exact @GlobalTheory.Mum.exists_carried_sec_off_closed | exact GlobalTheory.Mum.exists_carried_sec_off_closed | (intros; apply GlobalTheory.Mum.exists_carried_sec_off_closed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompatibleIsometriesCoisotropicKernelsStatement
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compatible_isometries_coisotropic_kernels : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (y : ℕ → D.La →ₗ[𝓞 E] X), (∀ n, 0 < n → Cois D (y n) n) →
    (∀ n m, 0 < n → 0 < m → ∀ a, ∃ e, y (n * m) a = y n a + n • e) →
    Module.finrank (𝓞 E) X ≤ min D.p D.q → ∀ N, 0 < N →
    ∃ Z : Submodule (𝓞 E) D.La, IsIsoSat D Z ∧ Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X ∧
      ∃ g : ℕ → D.La ≃ₗ[𝓞 E] D.La, (∀ n a b, D.EF (g n a) (g n b) = D.EF a b) ∧
        (∀ n m, 0 < n → 0 < m → ∀ a, ∃ e, g (n * m) a = g n a + n • e) ∧ (∀ n a, ∃ e, g n a = a + N • e) ∧
        ∀ n, 0 < n → ∀ a, (∃ e, y n (g n a) = n • e) ↔ ∃ b ∈ perp D Z, ∃ e, a = b + n • e := by
  first | exact @GlobalTheory.LowFilt.exists_compatible_isometries | exact GlobalTheory.LowFilt.exists_compatible_isometries | (intros; apply GlobalTheory.LowFilt.exists_compatible_isometries <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDivisorNonKltAtPointsNotContainingCentreStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_divisor_nonKlt_at_points_not_containing_centre : GlobalTheory.Published.Principalisation → GlobalTheory.Published.NadelVanishingPair → GlobalTheory.Published.NefNumerics → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → letI := algebraΓOfHom p; ∀ (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) (N : LB X) (D : X → ℚ) (P : Finset X) (z : X) (k : ℕ) (h : ℚ), IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < m → IsLogCanonicalMultiple p n Δ m G → IsAmpleLB N → IsQCart D → (∀ x ∈ P, IsClosed ({x} : Set X) ∧ z ⤳ x) → 1 ≤ k → topologicalKrullDim (closure ({z} : Set X)) = k → (z = genericPoint X ∨ IsNkltCentre p n (Δ + D) z) → 0 < h → (P.card : ℚ) * (k : ℚ) ^ k < h ^ k * (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin k => N : ℤ) → ∃ (B : X → ℚ) (δ₀ : ℚ), 0 < δ₀ ∧ δ₀ ≤ 1 ∧ QNum p N h B ∧ Off B z ∧ (∀ δ : ℚ, 0 ≤ δ → δ ≤ δ₀ → ∀ x ∈ P, ¬ KltAt p n (Δ + (1 - δ) • D + B) x) ∧ (∀ y, ¬ z ⤳ y → ∀ a : ℚ, 0 ≤ a → KltAt p n (Δ + a • D) y → KltAt p n (Δ + a • D + B) y) := by
  first | exact @GlobalTheory.PairStep.exists_step_divisor | exact GlobalTheory.PairStep.exists_step_divisor | (intros; apply GlobalTheory.PairStep.exists_step_divisor <;> assumption)
end

