import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0677
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3369
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0704
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0701
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3276
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2250
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2354
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2343
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2928
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3376
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3374
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0786
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3375
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0037
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0035
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3373
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2819
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2760
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupCocycleCoboundaryModPrime
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.CobModP

theorem constantCoeff_subst_of_zero' {σ τ R : Type} [CommRing R] [Finite σ]
    {a : σ → MvPowerSeries τ R} (ha0 : ∀ s, constantCoeff (a s) = 0) (f : MvPowerSeries σ R) :
    constantCoeff (subst a f) = constantCoeff f := by
  have ha : HasSubst a := hasSubst_of_constantCoeff_zero ha0
  have h := constantCoeff_subst_eq_zero ha ha0 (f := f - C (constantCoeff f)) (by simp)
  rw [subst_sub ha, subst_C, map_sub, constantCoeff_C, sub_eq_zero] at h
  exact h

theorem constantCoeff_formalGroupLawCoboundaryOne_eq_zero {R : Type} [CommRing R] {d : ℕ}
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R} (h : ∀ i, constantCoeff (μ i) = 0)
    (f : MvPowerSeries (Fin d) R) : constantCoeff (cob1 μ f) = -constantCoeff f := by
  unfold cob1 inL inR
  rw [map_sub, map_sub, constantCoeff_subst_of_zero' h,
    constantCoeff_subst_of_zero' (fun _ => constantCoeff_X _),
    constantCoeff_subst_of_zero' (fun _ => constantCoeff_X _)]
  ring

theorem coboundary_mod_p : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (κ : MvPowerSeries (Fin d ⊕ Fin d) O) (B : MvPowerSeries (Fin d) O) (y : G.A 1), constantCoeff κ = 0 → IsCoc c.μ κ → (∀ α, (p : O) ∣ coeff α (cob1 c.μ B - pull2 (nmul c.μ p) κ)) → c.ev 1 B = (p : O) • y → ∃ t : MvPowerSeries (Fin d) O, constantCoeff t = 0 ∧ ∀ α, (p : O) ∣ coeff α (κ - cob1 c.μ t) := by
  intro p _ O _ G d c κ B y hκ0 hcoc hdiv hB
  set I : Ideal O := Ideal.span {(p : O)} with hI
  set r : O →+* O ⧸ I := Ideal.Quotient.mk I with hr
  obtain ⟨c', hlaw, hev, -⟩ := GlobalTheory.T.exists_formalChart_quotient_by_ideal_with_primePow p O G d c I 1 (by
    rw [pow_one]; exact Ideal.mem_span_singleton_self _)
  have hconst := c.isLaw.const
  obtain ⟨hm1, hm2, hm3, -, hm5⟩ := GlobalTheory.T.map_coboundary_swap_pullback_commute O d c.μ hconst (O ⧸ I) r
  obtain ⟨-, hn⟩ := GlobalTheory.T.isCommFormalGroupLaw_map_natMultiple O d c.μ c.isLaw (O ⧸ I) r
  have hnc : ∀ i, constantCoeff (nmul c.μ p i) = 0 := fun i => (hn p i).1
  have hcoc' : IsCoc (fun i => map r (c.μ i)) (map r κ) :=
    ⟨by rw [← hm2, hcoc.1, map_zero], by rw [← hm3, hcoc.2]⟩
  have heq : cob1 (fun i => map r (c.μ i)) (map r B) =
      pull2 (nmul (fun i => map r (c.μ i)) p) (map r κ) := by
    have h0 : map r (cob1 c.μ B - pull2 (nmul c.μ p) κ) = 0 :=
      ((GlobalTheory.mvPowerSeries_lift_quotient O (Fin d ⊕ Fin d) I).2.1 _).2
        (fun α => Ideal.mem_span_singleton.2 (hdiv α))
    rw [map_sub, hm1, (hm5 _ hnc).1, sub_eq_zero] at h0
    rw [h0]
    congr 1
    funext i
    exact (hn p i).2
  have hp1 : (p : O) • (1 : O ⧸ I) = 0 := by
    rw [Algebra.smul_def, mul_one]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
  have hev0 : c'.ev 1 (map r B) = 0 := by
    rw [hev, hB, toBase_app, ← TensorProduct.smul_tmul, hp1, TensorProduct.zero_tmul]
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_coboundary_of_pullback_nmul_coboundary p (O ⧸ I) d (G.baseChange (O ⧸ I)) c' _ hlaw (map r κ) (map r B)
    hcoc' heq hev0
  have hs0 : constantCoeff s = 0 := by
    have h1 : constantCoeff (map r κ) = 0 := by
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hκ0,
        map_zero]
    have hc' : ∀ i, constantCoeff (map r (c.μ i)) = 0 := fun i => by
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
        hconst i, map_zero]
    rw [hs, constantCoeff_formalGroupLawCoboundaryOne_eq_zero hc'] at h1
    exact neg_eq_zero.1 h1
  obtain ⟨t, ht, ht0⟩ := (GlobalTheory.mvPowerSeries_lift_quotient O (Fin d) I).1 s
  refine ⟨t, ht0 hs0, fun α => ?_⟩
  have h2 : map r (κ - cob1 c.μ t) = 0 := by rw [map_sub, hm1, ht, hs, sub_self]
  exact Ideal.mem_span_singleton.1 (((GlobalTheory.mvPowerSeries_lift_quotient O (Fin d ⊕ Fin d) I).2.1 _).1 h2 α)

end GlobalTheory.CobModP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericStatementOfCanonicalExtension
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FlatModel

theorem genSt_of_hypotheses : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.CanonicalExtensionRankOne → GlobalTheory.Published.DeRhamCanonicalExtension →
    GenSt := by
  intro h1 h2 h3 E _ _ _ H Dw l l' Xo Xo' c c' W Y r ν hle r₀ U x hL Z τ s la p Xw hp hC A _ _ _ ξ β hξ hβ hpu hgen
    g e U₁ h₁ U₂ h₂ hT hE hd₁ hd₂
  haveI := GlobalTheory.T.integral_model_open_noetherian E H Dw l' Xo' c' W Y A ξ hξ
  obtain ⟨f, hf⟩ := GlobalTheory.T.property_of_codim_one_local_units A (SecValAt Y r ν τ.1 s.sig ξ e U₁ U₂) {𝔭 | ξ 𝔭 ∈ Set.range Y.j} (hC.2.2.2.2.1 hgen)
    (fun 𝔭 h𝔭 => by
      by_cases hg : ξ 𝔭 ∈ Set.range Y.j
      · exact GlobalTheory.T.integral_model_map_extension h1 h2 h3 E H Dw l l' Xo Xo' c c' W Y r ν hle r₀ U x hL Z τ s la p Xw hp hC A ξ β hξ hβ hpu hgen
          g e U₁ h₁ U₂ h₂ hT hE hd₁ hd₂ 𝔭 hg
      · exact GlobalTheory.T.integral_model_map_uniqueness h1 h2 h3 E H Dw l l' Xo Xo' c c' W Y r ν hle r₀ U x hL Z τ s la p Xw hp hC A ξ β hξ hβ hpu hgen
          g e U₁ h₁ U₂ h₂ hT hE hd₁ hd₂ 𝔭 (h𝔭.resolve_left hg) hg)
    (GlobalTheory.T.integral_model_map_compatibility h1 h2 h3 E H Dw l l' Xo Xo' c c' W Y r ν hle r₀ U x hL Z τ s la p Xw hp hC A ξ β hξ hβ hpu hgen
                   g e U₁ h₁ U₂ h₂ hT hE hd₁ hd₂)
    (fun k _ φ v hv inst yy hyy => by
      exfalso
      apply hv
      refine ⟨yy (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k), ?_⟩
      have e1 : (yy ≫ Y.j) (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k) =
          (spMap φ ≫ ξ) (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k) := by rw [hyy]
      exact (Scheme.Hom.comp_apply _ _ _).symm.trans
        (e1.trans ((Scheme.Hom.comp_apply _ _ _).trans (congrArg ξ (PrimeSpectrum.ext rfl)))))
  exact ⟨f, fun k _ _ φ yy hyy => hf k φ _ yy hyy⟩
end GlobalTheory.FlatModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupPullbackAbelianSchemeDualNumberEqStatement
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

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.groupPullback_abelianScheme_dualNumber_eq : ∀ {R : Type} [CommRing R] (k : Type) [Field k] (A : Over (Sp R)) [GrpObj A] (g : ℕ) (B' : Over (Sp (DualNumber k))) [GrpObj B'] (f : R →+* DualNumber k) (π₁ π₂ : B'.left ⟶ A.left), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → IsGrpPullback B' A (spMap f) π₁ → IsGrpPullback B' A (spMap f) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → π₁ = π₂ := by
  first | exact @GlobalTheory.DualRigidityField.pullback_eq | exact GlobalTheory.DualRigidityField.pullback_eq | (intros; apply GlobalTheory.DualRigidityField.pullback_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupPullbackTranslationCompEqStatement
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.groupPullback_translation_comp_eq : ∀ {S S' : Scheme.{0}} (G' : Over S') [GrpObj G'] (G : Over S) [GrpObj G] (f : S' ⟶ S) (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → ∀ (x : 𝟙_ (Over S') ⟶ G') (s : 𝟙_ (Over S) ⟶ G), x.left ≫ φ = f ≫ s.left → (lift (toUnit G' ≫ x) (𝟙 G') ≫ μ[G']).left ≫ φ = φ ≫ (lift (toUnit G ≫ s) (𝟙 G) ≫ μ[G]).left := by
  first | exact @GlobalTheory.TranslPull.transl_comp_of_isGrpPullback | exact GlobalTheory.TranslPull.transl_comp_of_isGrpPullback | (intros; apply GlobalTheory.TranslPull.transl_comp_of_isGrpPullback <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpMulTransport
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

namespace GlobalTheory.PolAVPull

theorem grp_mul_transport {Y X : Scheme.{0}} (G : Over X) [GrpObj G] {a b : Y ⟶ X} (h : a = b)
    (u v : Over.mk a ⟶ G) (u' v' : Over.mk b ⟶ G) (hu : u'.left = u.left) (hv : v'.left = v.left) :
    (u' * v').left = (u * v).left := by
  subst h
  have e1 : u' = u := Over.OverMorphism.ext hu
  have e2 : v' = v := Over.OverMorphism.ext hv
  rw [e1, e2]

theorem polAV_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (T : SAB H X) (t : SAB H X') (g : X' ⟶ X) (φ : SABMap t T g) (K : Type) [Field K] (z : Sp K ⟶ X') (P₀ : PolAV (Sp K)) (θ : P₀.A.left ⟶ T.G.left), IsGrpPullback P₀.A T.G (z ≫ g) θ → LBIso P₀.L (T.PP.L.pull θ) → ∃ m : P₀.A.left ⟶ t.G.left, IsGrpPullback P₀.A t.G z m ∧ LBIso P₀.L (t.PP.L.pull m) := by
  intro E _ _ _ H X X' T t g φ K _ z P₀ θ hθ hL
  have hw : θ ≫ T.G.hom = (P₀.A.hom ≫ z) ≫ g := by rw [Category.assoc]; exact hθ.1.w
  let m : P₀.A.left ⟶ t.G.left := φ.cart.1.lift θ (P₀.A.hom ≫ z) hw
  have hm1 : m ≫ φ.φ = θ := φ.cart.1.lift_fst _ _ _
  have hm2 : m ≫ t.G.hom = P₀.A.hom ≫ z := φ.cart.1.lift_snd _ _ _
  refine ⟨m, ⟨?_, ?_⟩, ?_⟩
  · have s : IsPullback (m ≫ φ.φ) P₀.A.hom T.G.hom (z ≫ g) := by rw [hm1]; exact hθ.1
    exact IsPullback.of_right s hm2 φ.cart.1
  · intro T' x y x₀ y₀ hx hy
    apply φ.cart.1.hom_ext
    · let x₁ : Over.mk ((Over.mk (T'.hom ≫ z)).hom ≫ g) ⟶ T.G :=
        Over.homMk (x₀.left ≫ φ.φ) (by
          show x₀.left ≫ φ.φ ≫ T.G.hom = _; rw [φ.cart.1.w, ← Category.assoc, Over.w x₀]; rfl)
      let y₁ : Over.mk ((Over.mk (T'.hom ≫ z)).hom ≫ g) ⟶ T.G :=
        Over.homMk (y₀.left ≫ φ.φ) (by
          show y₀.left ≫ φ.φ ≫ T.G.hom = _; rw [φ.cart.1.w, ← Category.assoc, Over.w y₀]; rfl)
      have e1 := φ.cart.2 (Over.mk (T'.hom ≫ z)) x₀ y₀ x₁ y₁ rfl rfl
      let x₂ : Over.mk (T'.hom ≫ z ≫ g) ⟶ T.G := Over.homMk (x.left ≫ θ) (by
        show x.left ≫ θ ≫ T.G.hom = _; rw [hθ.1.w, ← Category.assoc, Over.w x]; rfl)
      let y₂ : Over.mk (T'.hom ≫ z ≫ g) ⟶ T.G := Over.homMk (y.left ≫ θ) (by
        show y.left ≫ θ ≫ T.G.hom = _; rw [hθ.1.w, ← Category.assoc, Over.w y]; rfl)
      have e2 := hθ.2 T' x y x₂ y₂ rfl rfl
      have e3 : (x₁ * y₁).left = (x₂ * y₂).left :=
        grp_mul_transport T.G (by simp [Category.assoc]) x₂ y₂ x₁ y₁
          (by simp [x₁, x₂, hx, Category.assoc, hm1]) (by simp [y₁, y₂, hy, Category.assoc, hm1])
      rw [← e1, e3, e2, Category.assoc, hm1]
    · rw [Category.assoc, hm2, Over.w]
      simp only [Over.mk_hom, ← Category.assoc, Over.w]
  · have h1 : LBIso (t.PP.L.pull m) (T.PP.L.pull θ) :=
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull t.PP.L m m rfl)
        (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullSame T.PP.L (fun _ : PUnit => θ) (fun _ => φ.φ) (fun _ => 1) m (fun _ => hm1.symm))
        (by obtain ⟨w, hw, -⟩ := φ.lin; exact ⟨w, hw⟩)
    exact ReciprocityTheory.ChartRestriction.G.Geo.Tor.LBIso.trans P₀.isLB (pull_isLB T.PP.isLB θ) (pull_isLB t.PP.isLB m) hL (ReciprocityTheory.ChartRestriction.G.Geo.Tor.LBIso.symm h1)

end GlobalTheory.PolAVPull
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLatticesComplete
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.VB GlobalTheory.TwoSeq GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PDivGroup

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BadPt

section Linear

variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {H : Type*} [AddCommGroup H] [Module K H] [Module R H]
  [IsScalarTower R K H]

def IsAdapted (β : LinearMap.BilinForm K H) (F : Submodule K H) (N Λ : Submodule R H) : Prop :=
  Λ ⊓ F.restrictScalars R = N ∧ Λ ⊔ F.restrictScalars R = β.dualSubmodule N

def IsLagr (β : LinearMap.BilinForm K H) (F : Submodule K H) : Prop := ∀ s, s ∈ F ↔ ∀ w ∈ F, β s w = 0

end Linear

section Sheaf

variable {O : Type} [CommRing O] {X T : Scheme.{0}} {R K : Type} [CommRing R] [Field K] [Algebra R K]
  {f : Sp R ⟶ X} {f₀ : T ⟶ X} {ξ : Sp K ⟶ T}

def toFn (r : K) : Γ(Sp K, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of K)).inv r

def resSec (w : spMap (algebraMap R K) ≫ f = ξ ≫ f₀) (A : X.Modules) (t : Γ((Scheme.Modules.pullback f).obj A, ⊤)) :
    Γ((Scheme.Modules.pullback ξ).obj ((Scheme.Modules.pullback f₀).obj A), ⊤) :=
  ((sqIso w).hom.app A).app ⊤ (QCoh.pullbackSections (spMap (algebraMap R K)) _ (V := ⊤) le_top t)

variable (R) in

def InLat {M : (Sp K).Modules} {n : ℕ} (e : Fin n → Γ(M, ⊤)) (s : Γ(M, ⊤)) : Prop :=
  ∃ r : Fin n → R, s = ∑ i, toFn (algebraMap R K (r i)) • e i

variable (w : spMap (algebraMap R K) ≫ f = ξ ≫ f₀) {A B A' B' : X.Modules} {D : T.Modules}
  (a : (Scheme.Modules.pullback f₀).obj A ⟶ D) (b : D ⟶ (Scheme.Modules.pullback f₀).obj B)

def LatSeq (L : Γ((Scheme.Modules.pullback ξ).obj D, ⊤) → Prop) : Prop :=
  (∀ s, (L s ∧ ((Scheme.Modules.pullback ξ).map b).app ⊤ s = 0) ↔
      ∃ t, s = ((Scheme.Modules.pullback ξ).map a).app ⊤ (resSec w A t)) ∧
    ∀ t', (∃ s, L s ∧ ((Scheme.Modules.pullback ξ).map b).app ⊤ s = t') ↔ ∃ t, t' = resSec w B t

def Reads {H : Type*} [AddCommGroup H] [Module K H] [Module R H] [IsScalarTower R K H]
    (E : Γ((Scheme.Modules.pullback ξ).obj D, ⊤) ≃+ H) (β : LinearMap.BilinForm K H) (F : Submodule K H)
    (N : Submodule R H) : Prop :=
  (∀ s, ((Scheme.Modules.pullback ξ).map b).app ⊤ s = 0 ↔ E s ∈ F) ∧
    (∀ s, E s ∈ N ↔ ∃ t, s = ((Scheme.Modules.pullback ξ).map a).app ⊤ (resSec w A t)) ∧
    (∀ s, E s ∈ β.dualSubmodule N ↔ ∃ t, ((Scheme.Modules.pullback ξ).map b).app ⊤ s = resSec w B t) ∧
    Function.Surjective (((Scheme.Modules.pullback ξ).map b).app ⊤)

variable {w a b} in

theorem Reads.latSeq {H : Type*} [AddCommGroup H] [Module K H] [Module R H] [IsScalarTower R K H]
    {E : Γ((Scheme.Modules.pullback ξ).obj D, ⊤) ≃+ H} {β : LinearMap.BilinForm K H} {F : Submodule K H}
    {N Λ : Submodule R H} (h : Reads w a b E β F N) (h' : IsAdapted β F N Λ) : LatSeq w a b fun s => E s ∈ Λ := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h
  refine ⟨fun s => ?_, fun t' => ⟨?_, ?_⟩⟩
  · rw [← h₂, h₁, ← h'.1]; rfl
  · rintro ⟨s, hs, rfl⟩
    exact (h₃ s).1 (h'.2 ▸ Submodule.mem_sup_left hs)
  · rintro ⟨t, rfl⟩
    obtain ⟨s, hs⟩ := h₄ (resSec w B t)
    obtain ⟨x, hx, y, hy, e⟩ := Submodule.mem_sup.1 (h'.2.ge ((h₃ s).2 ⟨t, hs⟩))
    refine ⟨E.symm x, by simpa using hx, ?_⟩
    have e' : s = E.symm x + E.symm y := by rw [← map_add, e, E.symm_apply_apply]
    rw [← hs, e', map_add, (h₁ (E.symm y)).2 (by simpa using hy), add_zero]

variable {α : O →+* End A} {β : O →+* End B} {α' : O →+* End A'} {β' : O →+* End B'} {r : ℕ}

def HasLattice (d : DatumOn α β α' β' r f₀) : Prop :=
  ∃ (n : ℕ) (e : Fin n → Γ((Scheme.Modules.pullback ξ).obj d.D, ⊤)),
    (∀ x s, InLat R e s → InLat R e ((act (pullAct d.ρ ξ) x).app ⊤ s)) ∧
      LatSeq w d.a d.b (InLat R e) ∧ LatSeq w d.u d.v (InLat R e)

def HasLatticesDvr (d : DatumOn α β α' β' r f₀) : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [IsAlgClosed (IsLocalRing.ResidueField R)]
    (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] (f : Sp R ⟶ X) (ξ : Sp K ⟶ T)
    (w : spMap (algebraMap R K) ≫ f = ξ ≫ f₀), HasLattice w d

def HasLatticesComplete (d : DatumOn α β α' β' r f₀) : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [IsAlgClosed (IsLocalRing.ResidueField R)]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] (f : Sp R ⟶ X) (ξ : Sp K ⟶ T)
    (w : spMap (algebraMap R K) ≫ f = ξ ≫ f₀), HasLattice w d

end Sheaf

section Forms

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]

def intForms (G : Over (Sp R)) [GrpObj G] (A : Over (Sp K)) [GrpObj A] (φ : A.left ⟶ G.left)
    [Module R (primDR A)] [IsScalarTower R K (primDR A)] : Submodule R (primDR A) where
  carrier := {c | c ∈ PrimitiveSubmodule A ∧ ∀ (v : epsR R ⟶ G) (v' : epsR K ⟶ A) (h : HdR A), IsTangent v →
    v'.left ≫ φ = spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR (algebraMap R K)) ≫ v.left → IsLieImage h v' →
    h c ∈ (1 : Submodule R K)}
  zero_mem' := ⟨zero_mem _, fun _ _ h _ _ _ => by rw [map_zero]; exact zero_mem _⟩
  add_mem' {x y} hx hy := ⟨add_mem hx.1 hy.1, fun v v' h a b c => by
    rw [map_add]; exact add_mem (hx.2 v v' h a b c) (hy.2 v v' h a b c)⟩
  smul_mem' r x hx := by
    rw [← algebraMap_smul K r x]
    refine ⟨Submodule.smul_mem _ _ hx.1, fun v v' h a b c => ?_⟩
    rw [map_smul, algebraMap_smul]
    exact Submodule.smul_mem _ _ (hx.2 v v' h a b c)

end Forms

section Tower

variable {p : ℕ} {R K : Type} [CommRing R] [CommRing K] [Algebra R K]

structure FinTower (Γ : PDivGroup p R) (G : Over (Sp R)) [GrpObj G] : Type where

  y : ∀ n, SpAlg R (Γ.A n) ⟶ G

  mul : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra R B] (φ ψ : WithConv (Γ.A n →ₐ[R] B)),
    spOver (φ * ψ).ofConv ≫ y n = (spOver φ.ofConv ≫ y n) * (spOver ψ.ofConv ≫ y n)

  inj : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra R B] (φ ψ : Γ.A n →ₐ[R] B),
    spOver φ ≫ y n = spOver ψ ≫ y n → φ = ψ

  surj : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra R B] [Module.Finite R B] (z : SpAlg R B ⟶ G),
    z ^ p ^ n = 1 → ∃ φ : Γ.A n →ₐ[R] B, spOver φ ≫ y n = z

  res : ∀ n, spOver (Γ.res n : Γ.A (n + 1) →ₐ[R] Γ.A n) ≫ y (n + 1) = y n

def FinTower.ofTower {Γ : PDivGroup p R} {G : Over (Sp R)} [GrpObj G] (t : Γ.TorsionTower G) : FinTower Γ G :=
  ⟨t.y, t.mul, t.inj, fun n B _ _ _ => t.surj n B, t.res⟩

example [Fact p.Prime] : FinTower (mu p R) (Gm (Sp R)) := .ofTower (muTower p R)

def FinTower.IsIncl {Γ : PDivGroup p R} {G : Over (Sp R)} [GrpObj G] (s : FinTower Γ G) {𝒜 : PDivGroup p K}
    {A : Over (Sp K)} [GrpObj A] (t : 𝒜.TorsionTower A) (φ : A.left ⟶ G.left) (κ : Γ.baseChange K ⟶ 𝒜) : Prop :=
  ∀ n, spMap (κ.app n : 𝒜.A n →+* (Γ.baseChange K).A n) ≫ (t.y n).left ≫ φ =
    spMap ((Γ.toBase K).app n).toRingHom ≫ (s.y n).left

def IsWeilHom {𝒜 ℬ : PDivGroup p R} {A B : Over (Sp R)} [GrpObj A] [GrpObj B] (t : 𝒜.TorsionTower A)
    (u : ℬ.TorsionTower B) (P : LB (A ⊗ B).left) (w : 𝒜 ⟶ ℬ.dual) : Prop :=
  ∀ n, ∃ U : (𝒜.A n ⊗[R] ℬ.A n)ˣ,
    Out.WeilIs (A ⊗ B) P ((p ^ n : ℕ) : ℤ) (T := SpAlg R (𝒜.A n ⊗[R] ℬ.A n))
      (CartesianMonoidalCategory.lift (spOver Algebra.TensorProduct.includeLeft ≫ t.y n) 1)
      (CartesianMonoidalCategory.lift 1 (spOver Algebra.TensorProduct.includeRight ≫ u.y n)) (unitOn U) ∧
    ∀ χ : CartierDual R (ℬ.A n), w.app n χ = TensorProduct.rid R _ (χ.ofConv.lTensor _ U.val)

variable [Fact p.Prime] {Γ : PDivGroup p R} {𝒜 : PDivGroup p K}

def weilProj (κ : Γ.baseChange K ⟶ 𝒜) (w : 𝒜 ⟶ 𝒜.dual) : 𝒜 ⟶ Γ.dual.baseChange K :=
  w ≫ dualHom _ _ κ ≫ (PerfdLat.dualBaseChange K Γ).hom

variable [Module R 𝒜.RigExt] [IsScalarTower R K 𝒜.RigExt]

def latOmega (κ : Γ.baseChange K ⟶ 𝒜) : Submodule R 𝒜.RigExt where
  carrier := {x | ∃ (w : 𝒜.omega) (w₀ : Γ.omega), x = 𝒜.rigOfOmega w ∧ omegaMap _ _ κ w = (Γ.toBase K).omega w₀}
  zero_mem' := ⟨0, 0, (map_zero _).symm, by rw [map_zero, map_zero]⟩
  add_mem' := by
    rintro _ _ ⟨w, w₀, rfl, h⟩ ⟨w', w₀', rfl, h'⟩
    exact ⟨w + w', w₀ + w₀', (map_add _ _ _).symm, by rw [map_add, map_add, h, h']⟩
  smul_mem' := by
    rintro r _ ⟨w, w₀, rfl, h⟩
    exact ⟨algebraMap R K r • w, r • w₀, by rw [map_smul, algebraMap_smul], by rw [map_smul, map_smulₛₗ, h]⟩

def latExt {Δ : PDivGroup p R} (π : 𝒜 ⟶ Δ.baseChange K) : Submodule R 𝒜.RigExt where
  carrier := {x | ∃ y : Δ.RigExt, x = rigExtMap π ((Δ.toBase K).rig y)}
  zero_mem' := ⟨0, by rw [map_zero, map_zero]⟩
  add_mem' := by
    rintro _ _ ⟨y, rfl⟩ ⟨y', rfl⟩
    exact ⟨y + y', by rw [map_add, map_add]⟩
  smul_mem' := by
    rintro r _ ⟨y, rfl⟩
    exact ⟨r • y, by rw [map_smulₛₗ, map_smul, algebraMap_smul]⟩

def lattice (κ : Γ.baseChange K ⟶ 𝒜) (w : 𝒜 ⟶ 𝒜.dual) : Submodule R 𝒜.RigExt :=
  latOmega κ ⊔ latExt (weilProj κ w)

end Tower

end GlobalTheory.BadPt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorConjUnitPowCorrectionsStatement
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heatOperator_conj_unitPow_corrections : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (n : ℕ) (dd : Fin n → Fld G.left) (Θ : Matrix (Fin n) (Fin n) R), Θᵀ = Θ → ∀ (u : Fin n → R) (d : Fld G.left) (W₀ Wp Wo : G.left.Opens) (p p' : Γ(G.left, Wp)) (k : ℕ) (g g' : Γ(G.left, Wo)), g * g' = 1 → Wo ≤ W₀ → IsField W₀ d → (∀ a, IsField W₀ (dd a)) → ∀ f, op G dd Θ u d p p' k Wo (g ^ k * f) = g ^ k * (op G dd Θ u d p p' k Wo f - 2 * (k : Γ(G.left, Wo)) * ∑ a, ∑ b, constFn G.hom Wo (Θ a b) * (dd b Wo g * g') * dd a Wo f + ((k : Γ(G.left, Wo)) ^ 2 * (2 * (d Wo g * g') - ∑ a, ∑ b, constFn G.hom Wo (Θ a b) * (dd a Wo g * g') * (dd b Wo g * g')) + (k : Γ(G.left, Wo)) * (2 * ∑ a, constFn G.hom Wo (u a) * (dd a Wo g * g') - ∑ a, ∑ b, constFn G.hom Wo (Θ a b) * dd a Wo (dd b Wo g * g'))) * f) := by
  first | exact @GlobalTheory.HeatConj.op_pow_mul | exact GlobalTheory.HeatConj.op_pow_mul | (intros; apply GlobalTheory.HeatConj.op_pow_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorOnRingConjPowFractionFieldStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heatOperatorOnRing_conj_pow_fractionField : ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] (n : ℕ) (d : Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (δ : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (Θ : Matrix (Fin n) (Fin n) (FractionRing Ω)), Θᵀ = Θ → (2 : FractionRing Ω) ≠ 0 → ∀ (u : Fin n → FractionRing Ω) (p p' c : FractionRing Ω), c ≠ 0 → ∃ (d' : Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (u'' : Fin n → FractionRing Ω) (q q' : FractionRing Ω), (∀ y, (∀ a, δ a y = 0) → d' y = d y) ∧ ∀ (k : ℕ) (f : FractionRing Ω), ringOp ⇑d (fun a => ⇑(δ a)) Θ u p p' k (c ^ k * f) = c ^ k * ringOp ⇑d' (fun a => ⇑(δ a)) Θ u'' q q' k f := by
  first | exact @GlobalTheory.Heat.ringOp_conj_pow | exact GlobalTheory.Heat.ringOp_conj_pow | (intros; apply GlobalTheory.Heat.ringOp_conj_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorValueAtPointEqRingOperatorStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heatOperator_value_at_point_eq_ringOperator : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (X : Scheme.{0}) (m : G.left ⟶ X) (L : LB X) (n : ℕ) (dd : Fin n → Fld G.left) (D : R → R) (h : Heat G m L dd D) (i0 : h.J) (Ω : Type) [CommRing Ω] (φ : R →+* Ω) (x : Sp Ω ⟶ G.left), x ≫ G.hom = spMap φ → ∀ (δ : Fin n → Derivation ℤ Ω Ω), (∀ a O f, ⊤ ≤ x ⁻¹ᵁ O → valR x O (dd a O f) = δ a (valR x O f)) → ∀ (dΩ : Derivation ℤ Ω Ω), ⊤ ≤ x ⁻¹ᵁ h.W i0 → (∀ O f, O ≤ h.W i0 → ⊤ ≤ x ⁻¹ᵁ O → valR x O (h.d i0 O f) = dΩ (valR x O f)) → (∀ r, dΩ (φ r) = φ (D r)) ∧ ∀ (k : ℕ) (τ τ' : SecM m L k), h.Acts k τ τ' → valR x (h.W i0) (rsT (τ'.f fun _ => h.j i0) (h.W i0)) = ringOp ⇑dΩ (fun a => ⇑(δ a)) (φ.mapMatrix h.Θ) (fun a => φ (h.u a)) (valR x _ (h.p i0)) (valR x _ (h.p' i0)) k (valR x (h.W i0) (rsT (τ.f fun _ => h.j i0) (h.W i0))) := by
  first | exact @GlobalTheory.HeatPointValue.value_acts | exact GlobalTheory.HeatPointValue.value_acts | (intros; apply GlobalTheory.HeatPointValue.value_acts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantVectorFieldConstFnEqZeroStatement
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariantVectorField_constFn_eq_zero : ∀ {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (v : TanM (𝟙 (Sp R)) G) (dd : Fld G.left), IsInv G v dd → ∀ (O : G.left.Opens) (r : R), dd O (constFn G.hom O r) = 0 := by
  first | exact @GlobalTheory.Heat.IsInv.apply_constFn | exact GlobalTheory.Heat.IsInv.apply_constFn | (intros; apply GlobalTheory.Heat.IsInv.apply_constFn <;> assumption)
end

