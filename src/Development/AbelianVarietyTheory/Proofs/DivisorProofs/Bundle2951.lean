import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2505
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0114
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2779
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0102
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2851
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2411
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2852
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2514
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2248
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarIndependentOfOrthonormalFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1951
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2818
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2785
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2764
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2843

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleDiagonalPullbackBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot

noncomputable section
namespace GlobalTheory.DiagAmpleBC

theorem diag_comp {S T : Scheme.{0}} (A : Over S) (B : Over T) (β : B.left ⟶ A.left)
    (β₂ : (G2 B).left ⟶ (G2 A).left) (hs : IsSquare β β₂) :
    (lift (𝟙 B) (𝟙 B)).left ≫ β₂ = β ≫ (lift (𝟙 A) (𝟙 A)).left := by
  have h1 : (lift (𝟙 B) (𝟙 B)).left ≫ (fst B B).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_fst]; rfl
  have h2 : (lift (𝟙 A) (𝟙 A)).left ≫ (fst A A).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_fst]; rfl
  have h3 : (lift (𝟙 B) (𝟙 B)).left ≫ (snd B B).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_snd]; rfl
  have h4 : (lift (𝟙 A) (𝟙 A)).left ≫ (snd A A).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_snd]; rfl
  apply pullback.hom_ext
  · show _ ≫ (fst A A).left = _ ≫ (fst A A).left
    rw [Category.assoc, hs.1, ← Category.assoc, h1, Category.assoc, h2, Category.id_comp, Category.comp_id]
  · show _ ≫ (snd A A).left = _ ≫ (snd A A).left
    rw [Category.assoc, hs.2, ← Category.assoc, h3, Category.assoc, h4, Category.id_comp, Category.comp_id]

theorem relAmple_diag_pull : ∀ (S T : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left), P.IsLB → RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (t : T ⟶ S) (B : Over T) (β : B.left ⟶ A.left) (β₂ : (G2 B).left ⟶ (G2 A).left), IsPullback β B.hom A.hom t → IsSquare β β₂ → RelAmple B ((P.pull β₂).pull (lift (𝟙 B) (𝟙 B)).left) := by
  intro S T A _ hA P hP hD t B β β₂ hpb hs
  haveI := hA.proper
  have e₁ : LBIso ((P.pull β₂).pull (lift (𝟙 B) (𝟙 B)).left) (P.pull ((lift (𝟙 B) (𝟙 B)).left ≫ β₂)) :=
    GlobalTheory.ZM.SiegPull.lbIso_pull_comp (GlobalTheory.lbIso_refl (pull_isLB hP β₂)) _
  have e₂ : LBIso ((P.pull (lift (𝟙 A) (𝟙 A)).left).pull β) (P.pull (β ≫ (lift (𝟙 A) (𝟙 A)).left)) :=
    GlobalTheory.ZM.SiegPull.lbIso_pull_comp (GlobalTheory.lbIso_refl (pull_isLB hP _)) _
  rw [diag_comp A B β β₂ hs] at e₁
  have e := LBIso.trans (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) e₁ e₂.symm
  exact GlobalTheory.ModelAbLocus.relAmple_of_lbIso_pull hpb (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) e hD

end GlobalTheory.DiagAmpleBC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleOfAppellHumbertStatement
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rel_ample_of_appell_humbert : ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A →
    ∀ (M : LB A.left) (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ),
    M.IsLB → u.IsAH Hm χ → Out.RelAmple A M := by
  first | exact @GlobalTheory.LefschetzAmple.relAmple_of_isAH | exact GlobalTheory.LefschetzAmple.relAmple_of_isAH | (intros; apply GlobalTheory.LefschetzAmple.relAmple_of_isAH <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReprEqZeroOfCardNe
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.LineForm

namespace GlobalTheory.PullTop

theorem repr_eq_zero_of_card_ne {R M I : Type*} [CommRing R] [AddCommGroup M] [Module R M] [LinearOrder I]
    (b : Module.Basis I R M) {k : ℕ} (x : ⋀[R]^k M) {S : Finset I} (hS : S.card ≠ k) :
    b.ExteriorAlgebra.repr (x : ExteriorAlgebra R M) S = 0 := by
  have h : (Finsupp.lapply S ∘ₗ b.ExteriorAlgebra.repr.toLinearMap ∘ₗ (⋀[R]^k M).subtype) = 0 := by
    refine (b.exteriorPower k).ext fun s => ?_
    have hs : (s : Finset I) ≠ S := fun e => hS (e ▸ s.2)
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, ← ExteriorAlgebra.basis_eq_coe_basis,
      LinearEquiv.coe_coe, Module.Basis.repr_self, Finsupp.lapply_apply, LinearMap.zero_apply]
    exact Finsupp.single_eq_of_ne' hs
  exact LinearMap.congr_fun h x

theorem repr_map_eq_zero {R M N I J : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [LinearOrder I] [LinearOrder J] [Fintype I] (b : Module.Basis I R M) (c : Module.Basis J R N) (f : M →ₗ[R] N)
    {S : Finset J} (hS : Fintype.card I < S.card) (β : ExteriorAlgebra R M) :
    c.ExteriorAlgebra.repr (ExteriorAlgebra.map f β) S = 0 := by
  have h : (Finsupp.lapply S ∘ₗ c.ExteriorAlgebra.repr.toLinearMap ∘ₗ (ExteriorAlgebra.map f).toLinearMap) = 0 := by
    refine b.ExteriorAlgebra.ext fun T => ?_
    have hT : S.card ≠ T.card := ((Finset.card_le_univ T).trans_lt hS).ne'
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearEquiv.coe_coe, Finsupp.lapply_apply,
      LinearMap.zero_apply]
    rw [ExteriorAlgebra.basis_apply b T, ExteriorAlgebra.map_apply_ιMulti,
      ← exteriorPower.ιMulti_apply_coe]
    exact repr_eq_zero_of_card_ne c _ hT
  exact LinearMap.congr_fun h β

theorem repr_pull_univ {n : ℕ} (L : ReciprocityTheory.L2DbarEstimates.V (n + 1) →L[ℂ] ReciprocityTheory.L2DbarEstimates.V n) (β : Alt n) :
    (bas (n + 1)).repr (pull L β) Finset.univ = 0 :=
  repr_map_eq_zero ((Pi.basisFun ℂ (Fin n ⊕ Fin n)).reindex finSumFinEquiv) _ _ (by simp; omega) β

end GlobalTheory.PullTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictSurjectiveAlt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.TorusOntoSpread

theorem restrict_surjective : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G') (g : R →+* V) (β : G'.left ⟶ G.left), IsGrpPullback G' G (spMap g) β → ∀ ρ, Spread U U' g β ρ → Function.Surjective ρ := by
  intro R _ _ _ _ G _ _ hG D A U V _ _ _ _ G' _ _ _ D' A' U' g β _ ρ hsp
  obtain ⟨V₁, _, _, _, ψ, G₁, _, _, m₁, Ω, _, α, b, hb, GΩ, _, n, hn, n', hn', j, G₀, _, m₀, hm₀, h₀, hm₀',
    hψl, hm₁, hj, _, _, _, hΩ, h₀j⟩ := hsp
  haveI := hψl; haveI := hj
  have hG₁ : IsSemiAbelian G₁ := GlobalTheory.Mum.isSemiAbelian_of_isGrpPullback_square _ _ _ G G₁ m₁ hm₁ hG
  classical
  by_contra hρ
  have hM : ρ.range ≠ ⊤ := fun h => hρ (AddMonoidHom.range_eq_top.1 h)
  obtain ⟨F, _, _, l, hl0, hl⟩ := GlobalTheory.TorusOnto.exists_finite_quotient_ne_zero ρ.range hM
  have hlρ : l.comp ρ = 0 := AddMonoidHom.ext fun x => hl _ ⟨x, rfl⟩
  have key : GlobalTheory.SplitTorus.torusMap (Sp V₁) l ≫ j = GlobalTheory.SplitTorus.torusMap (Sp V₁) 0 ≫ j := by
    haveI : IsSeparated G₁.hom := hG₁.separated
    have hjac : maximalIdeal V₁ ≤ Ideal.jacobson ⊥ := (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
    refine GlobalTheory.hom_eq_of_thickenings_of_isProper V₁ (maximalIdeal V₁) hjac (splitTorus (Sp V₁) F) G₁ _ _ fun e => ?_
    have hψ : ∀ x ∈ maximalIdeal R, ψ x ∈ maximalIdeal V₁ := fun x hx =>
      (mem_maximalIdeal _).2 fun hu => (mem_maximalIdeal _).1 hx (isUnit_of_map_unit ψ x hu)
    have hI : maximalIdeal V₁ ^ (e + 1) ≠ ⊤ := fun h =>
      (maximalIdeal.isMaximal V₁).ne_top (top_le_iff.1 (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero e)))
    haveI : Nontrivial (V₁ ⧸ maximalIdeal V₁ ^ (e + 1)) := Ideal.Quotient.nontrivial_iff.2 hI
    haveI : IsLocalRing (V₁ ⧸ maximalIdeal V₁ ^ (e + 1)) := .of_surjective' _ Ideal.Quotient.mk_surjective
    let q : V₁ →+* V₁ ⧸ maximalIdeal V₁ ^ (e + 1) := Ideal.Quotient.mk _
    have he := isGrpPullback_pullback G₁ (thick V₁ (maximalIdeal V₁) e)
    have ha : ∀ x ∈ maximalIdeal R ^ (e + 1), (q.comp ψ) x = 0 := by
      intro x hx
      refine Ideal.Quotient.eq_zero_iff_mem.2 ?_
      have hle : Ideal.map ψ (maximalIdeal R ^ (e + 1)) ≤ maximalIdeal V₁ ^ (e + 1) := by
        rw [Ideal.map_pow]
        exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 hψ) _
      exact hle (Ideal.mem_map_of_mem ψ hx)
    have hR : IsGrpPullback (thickObj V₁ (maximalIdeal V₁) e G₁) G (spMap (q.comp ψ))
        (pullback.fst G₁.hom (thick V₁ (maximalIdeal V₁) e) ≫ m₁) :=
      (he.comp hm₁).congr (by rw [spMap, spMap, ← Spec.map_comp]; rfl) rfl
    obtain ⟨-, hfac⟩ := GlobalTheory.TorusPart.mono_gtTorus_and_factor (U.gt e) ha hR
    obtain ⟨ρe, hρe⟩ := hfac D'.toPre.X (GlobalTheory.TorusPart.pullTorus he j) inferInstance
    have hres : ∀ x ∈ maximalIdeal V₁ ^ (e + 1), residue V₁ x = 0 := fun x hx =>
      (residue_eq_zero_iff x).2 (Ideal.pow_le_self (Nat.succ_ne_zero e) hx)
    have ke := GlobalTheory.TorusPart.isGrpPullback_thickLift hres hm₀
    have ha' : ∀ x ∈ maximalIdeal R ^ (e + 1), ((residue V₁).comp ψ) x = 0 := fun x hx =>
      h₀ x (by rw [zero_add, pow_one]; exact Ideal.pow_le_self (Nat.succ_ne_zero e) hx)
    have e1 : GlobalTheory.TorusPart.pullTorus ke (GlobalTheory.TorusPart.pullTorus he j) = GlobalTheory.TorusPart.pullTorus hm₀ j :=
      GlobalTheory.TorusPart.pullTorus_pullTorus ke he hm₀ (GlobalTheory.TorusPart.thickPt_thick hres).symm
        (GlobalTheory.TorusPart.thickLift_fst hres hm₀).symm j
    have e2 : GlobalTheory.TorusPart.pullTorus ke (GlobalTheory.TorusPart.gtTorus (U.gt e) ha hR) =
        GlobalTheory.TorusPart.gtTorus (U.gt e) ha' hm₀' :=
      GlobalTheory.TorusPart.pullTorus_gtTorus (σ := Ideal.Quotient.lift _ (residue V₁) hres) (U.gt e) ha ha' hR hm₀' ke
        (RingHom.ext fun x => rfl)
        (by rw [← Category.assoc, GlobalTheory.TorusPart.thickLift_fst])
    obtain ⟨hmono, hfac'⟩ := GlobalTheory.TorusPart.mono_gtTorus_and_factor (U.gt e) ha' hm₀'
    obtain ⟨u, hu⟩ := hfac' D.toPre.X (GlobalTheory.TorusPart.gtTorus (U.gt 0) h₀ hm₀') inferInstance
    have e3 := congrArg (GlobalTheory.TorusPart.pullTorus ke) hρe
    rw [e1, GlobalTheory.TorusPart.pullTorus_torusMap_comp, e2, h₀j, hu, ← Category.assoc,
      ← GlobalTheory.SplitTorus.torusMap_comp, cancel_mono] at e3
    have e4 : ρe = ρ.comp u := (GlobalTheory.SplitTorus.torusMap_injective e3).symm
    have hstep : GlobalTheory.TorusPart.pullTorus he (GlobalTheory.SplitTorus.torusMap _ l ≫ j) =
        GlobalTheory.TorusPart.pullTorus he (GlobalTheory.SplitTorus.torusMap _ (0 : D'.toPre.X →+ F) ≫ j) := by
      rw [GlobalTheory.TorusPart.pullTorus_torusMap_comp, GlobalTheory.TorusPart.pullTorus_torusMap_comp, hρe, ← Category.assoc,
        ← Category.assoc, ← GlobalTheory.SplitTorus.torusMap_comp, ← GlobalTheory.SplitTorus.torusMap_comp, e4,
        ← AddMonoidHom.comp_assoc, hlρ, AddMonoidHom.zero_comp, AddMonoidHom.zero_comp]
    have k1 := GlobalTheory.TorusPart.pullTorus_left he (GlobalTheory.SplitTorus.torusMap _ l ≫ j)
    have k2 := GlobalTheory.TorusPart.pullTorus_left he (GlobalTheory.SplitTorus.torusMap _ (0 : D'.toPre.X →+ F) ≫ j)
    rw [hstep] at k1
    have k3 := k1.symm.trans k2
    show pullback.fst (splitTorus (Sp V₁) F).hom (thick V₁ (maximalIdeal V₁) e) ≫ _ =
      pullback.fst (splitTorus (Sp V₁) F).hom (thick V₁ (maximalIdeal V₁) e) ≫ _
    rw [← GlobalTheory.SplitTorus.bcIso_inv_bcMap, Category.assoc, Category.assoc, k3]
  haveI : Mono (GlobalTheory.TorusPart.gtTorus (U'.gt 0) hb hn') :=
    (GlobalTheory.TorusPart.mono_gtTorus_and_factor (U'.gt 0) hb hn').1
  have e2 := congrArg (GlobalTheory.TorusPart.pullTorus hn) key
  rw [GlobalTheory.TorusPart.pullTorus_torusMap_comp, GlobalTheory.TorusPart.pullTorus_torusMap_comp, hΩ] at e2
  have e3 : GlobalTheory.SplitTorus.torusMap (Sp Ω) l = GlobalTheory.SplitTorus.torusMap (Sp Ω) 0 := (cancel_mono _).1 e2
  exact hl0 (GlobalTheory.SplitTorus.torusMap_injective e3)

end GlobalTheory.TorusOntoSpread
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RetractionLiftObstructionZeroOfLiftedSectionStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.retractionLiftObstruction_zero_of_liftedSection : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ Z₀ X Z : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (t₀ : Z₀ ⟶ Sp R₀) (s : X ⟶ Sp R) (t : Z ⟶ Sp R) (i : X₀ ⟶ X) (k : Z₀ ⟶ Z) (hi : IsPullback i s₀ s (spMap π)) (hkk : IsPullback k t₀ t (spMap π)) (S : Sys I π s₀) (S' : Sys I π t₀) (P : S.Presents s i) (P' : S'.Presents t k) (f₀ : Z₀ ⟶ X₀) (h : f₀ ≫ s₀ = t₀ ≫ spMap (RingHom.id R₀)) (j₀ : X₀ ⟶ Z₀) (hj : j₀ ≫ t₀ = s₀ ≫ spMap (RingHom.id R₀)) (j : X ⟶ Z), j₀ ≫ f₀ = 𝟙 X₀ → j ≫ t = s → i ≫ j = j₀ ≫ k → ∀ (l : ∀ T : (Pair f₀)ᵒᵖ, (ofSys S).B ((pairPull h).G.obj T) →ₐ[R] (pairPre S' f₀).B T), (ofSys S).IsLift (pairPre S' f₀) (pairPull h) l → ∀ (w : GlobForm s₀) (c : GlobalTheory.CatCoh.H1 (ext R₁ (OAff t₀))), (ofSys S).IsOb1 (pairPre S' f₀) (pairPull h) l α w ((extMap R₁ (pairRes f₀ t₀)).pull1 c) → IsExtendedPullbackDegOne R₁ hj c 0 := by
  first | exact @GlobalTheory.Obs.retractionLiftObstruction_zero_of_liftedSection_alt | exact GlobalTheory.Obs.retractionLiftObstruction_zero_of_liftedSection_alt | (intros; apply GlobalTheory.Obs.retractionLiftObstruction_zero_of_liftedSection_alt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarFrameBallLeStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.riemannianHaar_frameBall_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (κ : Type) (p q : κ → ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (σ : κ ≃ Ψ) (A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ) (e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r), 1 ≤ r → IsIdent p q Ψ G x σ A e → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → riemHaar Ψ G x (frBall Ψ G x ε) ≤ ENNReal.ofReal ((8 * ε) ^ (Ψ.card * (r ^ 2 - 1))) := by
  first | exact @GlobalTheory.CovTop.VolUp.UpBall.riemHaar_frBall_le | exact GlobalTheory.CovTop.VolUp.UpBall.riemHaar_frBall_le | (intros; apply GlobalTheory.CovTop.VolUp.UpBall.riemHaar_frBall_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedGaloisLinearisationCarriesRigidificati
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.RigCubCarry

theorem pmaps_of_pullGen {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]
    {w : LB.Iso L' (L.pull F)} {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {a : LB.Gen (LB.LinComb L' φ' ε)}
    {t : LB.Gen (LB.LinComb L φ ε)} {h : Y' ⟶ Y} (hc : ∀ k, φ' k ≫ F = h ≫ φ k)
    (H : PMaps w φ' (fun k => h ≫ φ k) ε a (LB.pullGen L φ ε t h) (𝟙 Y')) : PMaps w φ' φ ε a t h := by
  intro Z r z p q hp hq
  have e := H Z r z p q hp hq
  rw [Category.comp_id] at e
  have hm' : ∀ k, (h ≫ φ k) (r z) ∈ L.U (p k) := fun k => by
    rw [← hc k]; exact hp k
  have hm : r z ∈ LB.wchart L (fun k => h ≫ φ k) p := Set.mem_iInter.2 hm'
  have hm2 : h (r z) ∈ LB.wchart L φ p := Set.mem_iInter.2 hm'
  refine Eq.trans ?_ e
  exact ((gm_res r z _ hm _).trans (gm_pull r h z _ hm2 _)).symm

open RigidIsoCube in

theorem surjective_appTop_tripleProduct_uniformisedGroup (R : Type) [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
    [IsCommMonObj G] (U : UnifPre I D A G) :
    Function.Surjective ((snd G (G ⊗ G)).left ≫ (snd G G).left ≫ G.hom).appTop.hom := by
  have hG : GlobalFnsSt := GlobalTheory.globalFns_holds
  have := U.smooth
  have : IsDominant (jK R) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))).le.trans bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (jK R)
  have hg : IsPullback (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) A.A.hom G.hom (jK R) := by
    have : IsIso U.gen.inv.left := inferInstanceAs (IsIso ((Over.forget _).map U.gen.inv))
    have s : IsPullback U.gen.inv.left A.A.hom (pullback.snd G.hom (jK R)) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨(Over.w U.gen.inv).trans (Category.comp_id _).symm⟩
    simpa using s.paste_horiz (IsPullback.of_hasPullback G.hom (jK R))
  have s₁ : Function.Surjective G.hom.appTop.hom :=
    surjective_appTop_of_baseChange hg (eSec G) (Over.w η[G]) (hG _ _ A.isAb).2
  have : Flat (G ⊗ G).hom := by rw [Over.tensorObj_hom]; infer_instance
  exact surj_comp (surjective_snd_of_generic hG (jK R) G A.isAb hg _)
      (surj_comp (surjective_snd_of_generic hG (jK R) G A.isAb hg _) s₁)

theorem cubeMap_tripleProduct_unit_eq {S : Scheme.{0}} {G' : Over S} [GrpObj G'] [IsCommMonObj G'] (m : CubeMap G' G') :
    (lift (1 : 𝟙_ (Over S) ⟶ G') (lift 1 1)).left ≫ m.F3 =
      (lift (1 : Over.mk (m.e ≫ (𝟙_ (Over S)).hom) ⟶ G') (lift 1 1)).left := by
  have ht : (toUnit (Over.mk (m.e ≫ (𝟙_ (Over S)).hom))).left = m.e := by
    have w := Over.w (toUnit (Over.mk (m.e ≫ (𝟙_ (Over S)).hom)))
    simpa using w
  apply hom_ext_triple
  intro i
  rw [Category.assoc, cubeMap_comp_proj_three m i, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
  have h1 : ∀ {T : Over S}, lift (1 : T ⟶ G') (lift 1 1) ≫ x3 G' i = 1 := by
    intro T; fin_cases i <;> simp [x3]
  rw [h1, h1, Hom.one_def, Hom.one_def, Over.comp_left, Over.comp_left, ht]
  have e₁ : (toUnit (𝟙_ (Over S))).left = 𝟙 _ := by simp
  rw [e₁, Category.id_comp]
  exact m.e_comm

end GlobalTheory.Mum.RigCubCarry

namespace GlobalTheory.Mum

set_option maxHeartbeats 2000000 in
open RigidIsoCube RigCubCarry in

theorem rigidified_galois_lin_carries_rig_and_cube : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hB : Base R) (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R') (hF : FinExt ρ) (hG : IsGal ρ) (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (hS' : IsSemiAbelian G') (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left) (hS : IsSemiAbelian G) (hβ : IsGrpPullback G' G (spMap ρ) β) (hact : ∀ σ, a.act σ ≫ β = β) (σ : Gal ρ) (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'), bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ → ∀ hP : IsPullUnif (Gal.hom σ) h bc U' U', PMaps (Classical.choose hP.lg) (K := PUnit) (fun _ => eSec G') (fun _ => eSec G') (fun _ => 1) U'.LG.rig U'.LG.rig (specOf (Gal.hom σ)) ∧ ∀ hc : IsGrpPullback G' G' (specOf (Gal.hom σ)) (bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ))), PMaps (Classical.choose hP.lg) (thφ G' (x3 G')) (thφ G' (x3 G')) thε U'.cubG.t U'.cubG.t (cubeMapOf hc).F3 := by
  intro R _ _ _ hB R' _ _ _ ρ hF hGal D D' hD A' G' _ _ hS' U' a G _ _ β hS hβ hact σ h bc hbc hP
  obtain ⟨hw, he, hrig, -⟩ := Classical.choose_spec hP.lg
  refine ⟨(maps_iff _ _ (fun _ => eSec G') _ U'.LG.rig U'.LG.rig (specOf (Gal.hom σ)) _
    (rigPull_le _ _ he U'.LG.L) (fun _ => rfl)).1 hrig, fun hc => ?_⟩
  have sj := surjective_appTop_tripleProduct_uniformisedGroup R' G' U'.toUnifPre
  let e : 𝟙_ (Over (Sp R')) ⟶ G3 G' := lift 1 (lift 1 1)
  have he3 : e.left ≫ (snd G' (G' ⊗ G')).left ≫ (snd G' G').left ≫ G'.hom = 𝟙 _ := by
    rw [Over.w, Over.w]; exact Over.w e
  have pg := (isGen_iff _).1 hw
  have hψ : ∀ k : thK.{0}, thφ G' (x3 G') k ≫ (bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ))) =
      (cubeMapOf hc).F3 ≫ thφ G' (x3 G') k := fun k => (cubeMapOf hc).psum_comm k.down
  have eF := cubeMap_tripleProduct_unit_eq (cubeMapOf hc)
  refine pmaps_of_pullGen hψ (pmaps_of_section pg U'.LG.isLB U'.LG.isLB U'.cubG.t U'.cubG.isGen
    (LB.pullGen _ _ _ U'.cubG.t (cubeMapOf hc).F3) (DVR.pullGen_isGen _ _ _ _ U'.cubG.isGen _) hψ _ e.left he3 sj
    fun y J J' hJ hJ' => ?_)
  refine ((val_pull hJ _ _ _).trans (congrArg (fun r => val U'.cubG.t r y J) eF)).trans ?_
  have f1 := (isCub_cubV U'.cubG (T := Over.mk ((cubeMapOf hc).e ≫ (𝟙_ (Over (Sp R'))).hom)) hJ).face 1 1
  have p := prod_cub (1 : 𝟙_ (Over (Sp R')) ⟶ G') 1 1
    (fun q => gw (Classical.choose hP.lg) q y (J (q ≫ bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)))) (J' q))
  rw [_root_.mul_one, _root_.mul_one] at p
  refine f1.trans (Eq.trans ?_ (congrArg₂ (· * ·) p ((isCub_cubV U'.cubG hJ').face 1 1)).symm)
  simp

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedPresentationCocycleMemBialgebraSymmetr
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

open Algebra.TensorProduct in

theorem coc_mem_symCocycles (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R)
    (t : G.TorsionTower A) (c : primDR A) (d : Dat t c) (hg : IsSymCoc d.g) (n : ℕ) :
    d.coc n ∈ symCocycles R (G.A n) := by
  set H := G.A n

  have V : ∀ (D : Type) [CommRing D] [Algebra R D] (φ ψ : H →ₐ[R] D),
      lift φ ψ (fun _ _ ↦ Commute.all _ _) (d.coc n) = d.g D (spOver φ ≫ t.y n) (spOver ψ ≫ t.y n) -
        ((fv d.f H D (toConv φ * toConv ψ).ofConv (t.y n) + (toConv φ * toConv ψ).ofConv (d.h n)) -
          (fv d.f H D φ (t.y n) + φ (d.h n)) - (fv d.f H D ψ (t.y n) + ψ (d.h n))) :=
    fun D _ _ φ ψ ↦ GlobalTheory.T.cocycle_tensorLift_apply_eq_twoPointValue R A p G t c d n D φ ψ
  have M : ∀ (D : Type) [CommRing D] [Algebra R D] (φ ψ : H →ₐ[R] D),
      spOver (toConv φ * toConv ψ).ofConv ≫ t.y n = (spOver φ ≫ t.y n) * (spOver ψ ≫ t.y n) :=
    fun D _ _ φ ψ ↦ t.mul n D (toConv φ) (toConv ψ)
  rw [mem_symCocycles]
  constructor
  · let T := H ⊗[R] (H ⊗[R] H)
    let i1 : H →ₐ[R] H ⊗[R] (H ⊗[R] H) := includeLeft
    let i2 : H →ₐ[R] H ⊗[R] (H ⊗[R] H) := (includeRight : H ⊗[R] H →ₐ[R] H ⊗[R] (H ⊗[R] H)).comp includeLeft
    let i3 : H →ₐ[R] H ⊗[R] (H ⊗[R] H) := (includeRight : H ⊗[R] H →ₐ[R] H ⊗[R] (H ⊗[R] H)).comp includeRight
    let i12 := (toConv i1 * toConv i2).ofConv
    let i23 := (toConv i2 * toConv i3).ofConv
    have e1 : ∀ x : H ⊗[R] H, (1 : H) ⊗ₜ[R] x = lift i2 i3 (fun _ _ ↦ Commute.all _ _) x := by
      intro x
      induction x with
      | zero => simp
      | add x y hx hy => rw [tmul_add, map_add, hx, hy]
      | tmul a b => simp [i2, i3, Algebra.TensorProduct.tmul_mul_tmul, includeLeft_apply, includeRight_apply]
    have e2 : ∀ x : H ⊗[R] H, TensorProduct.assoc R H H H ((Coalgebra.comul (R := R) (A := H)).rTensor H x) =
        lift i12 i3 (fun _ _ ↦ Commute.all _ _) x := by
      intro x
      induction x with
      | zero => simp
      | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
      | tmul a b =>
        rw [LinearMap.rTensor_tmul, lift_tmul]
        simp only [i12, AlgHom.convMul_apply, ofConv_toConv]
        induction (Coalgebra.comul (R := R) a : H ⊗[R] H) with
        | zero => simp
        | add x y hx hy => simp only [add_tmul, map_add, hx, hy, add_mul]
        | tmul a1 a2 => simp [i1, i2, i3, Algebra.TensorProduct.tmul_mul_tmul, includeLeft_apply, includeRight_apply]
    have e3 : ∀ x : H ⊗[R] H, (Coalgebra.comul (R := R) (A := H)).lTensor H x = lift i1 i23 (fun _ _ ↦ Commute.all _ _) x := by
      intro x
      induction x with
      | zero => simp
      | add x y hx hy => rw [map_add, map_add, hx, hy]
      | tmul a b =>
        rw [LinearMap.lTensor_tmul, lift_tmul]
        simp only [i23, AlgHom.convMul_apply, ofConv_toConv]
        induction (Coalgebra.comul (R := R) b : H ⊗[R] H) with
        | zero => simp
        | add x y hx hy => simp only [tmul_add, map_add, hx, hy, mul_add]
        | tmul b1 b2 => simp [i1, i2, i3, Algebra.TensorProduct.tmul_mul_tmul, includeLeft_apply, includeRight_apply]
    have e4 : ∀ x : H ⊗[R] H, ((TensorProduct.mk R H H).flip 1).lTensor H x =
        lift i1 i2 (fun _ _ ↦ Commute.all _ _) x := by
      intro x
      induction x with
      | zero => simp
      | add x y hx hy => rw [map_add, map_add, hx, hy]
      | tmul a b => simp [i1, i2, Algebra.TensorProduct.tmul_mul_tmul, includeLeft_apply, includeRight_apply]
    rw [cobTwo_apply, e1, e2, e3, e4, V, V, V, V]
    simp only [i12, i23, toConv_ofConv, M, mul_assoc]
    have hc := (hg (H ⊗[R] (H ⊗[R] H))).2 (spOver i1 ≫ t.y n) (spOver i2 ≫ t.y n) (spOver i3 ≫ t.y n)
    rw [mul_assoc (toConv i1)]
    linear_combination hc
  · have e : ∀ x : H ⊗[R] H, TensorProduct.comm R H H x =
        lift (includeRight : H →ₐ[R] H ⊗[R] H) (includeLeft : H →ₐ[R] H ⊗[R] H) (fun _ _ ↦ Commute.all _ _) x := by
      intro x
      induction x with
      | zero => simp
      | add x y hx hy => rw [map_add, map_add, hx, hy]
      | tmul a b => simp [Algebra.TensorProduct.tmul_mul_tmul, includeLeft_apply, includeRight_apply]
    have e' : d.coc n = lift (includeLeft : H →ₐ[R] H ⊗[R] H) includeRight (fun _ _ ↦ Commute.all _ _) (d.coc n) := by
      exact (DFunLike.congr_fun (lift_includeLeft_includeRight (R := R) (S := R) (A := H) (B := H)) (d.coc n)).symm
    rw [e, V]
    conv_rhs => rw [e', V]
    rw [mul_comm (toConv (includeRight : H →ₐ[R] H ⊗[R] H)), (hg _).1]
    ring

end GlobalTheory.PtExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedValueAtOriginMemIdealPowOfVanishes
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.OrigVan

theorem stalkMap_gs {X Y Z : Scheme.{0}} (t : Z ⟶ Y) (r : Y ⟶ X) (z : Z) (U : X.Opens) (h : r (t z) ∈ U)
    (a : Γ(X, U)) : (t.stalkMap z).hom (gs r (t z) U a) = gs (t ≫ r) z U a := by
  rw [gs_eq r (t z) U h, gs_eq (t ≫ r) z U h]
  exact Scheme.Hom.germ_stalkMap_apply t (r ⁻¹ᵁ U) z h _

theorem stalkMap_stalkOf {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (z : Sp S) (v : R) :
    ((Spec.map (CommRingCat.ofHom φ)).stalkMap z).hom (stalkOf ((Spec.map (CommRingCat.ofHom φ)) z) v) =
      stalkOf z (φ v) := by
  have e := congrArg (fun q => q.hom v) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  refine (Scheme.Hom.germ_stalkMap_apply (Spec.map (CommRingCat.ofHom φ)) ⊤ z trivial _).trans ?_
  exact congrArg ((Sp S).presheaf.germ ⊤ z trivial).hom e.symm

theorem eq_zero_of_stalkOf {S : Type} [CommRing S] (w : S) (h : ∀ z : Sp S, stalkOf z w = 0) : w = 0 := by
  have h1 : (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom w = 0 := by
    apply TopCat.Presheaf.section_ext (Sp S).sheaf ⊤
    intro x hx
    exact (h x).trans (map_zero _).symm
  have h2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom h1
  simpa using h2

end GlobalTheory.Mum.OrigVan

namespace GlobalTheory.Mum
open OrigVan

theorem origVal_mem_of_vanMod : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (k : ℕ) (α : D.X)
    (b : D.SecB k α) (v : R) (e : ℕ), OrigVal D b v → VanMod I b e → v ∈ I ^ (e + 1) := by
  intro R _ _ I D k α b v e hO hV
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  refine eq_zero_of_stalkOf _ fun z => ?_
  choose J hJ using fun χ : Sp R ⟶ D.P.A.left => exists_chart D.P.isLB (χ (thick R I e z))
  have hG : Good D.P.L (thick R I e z) J := hJ
  have h1 := congrArg ((thick R I e).stalkMap z).hom (hO (thick R I e z) J hG)
  have hm := hG.mem (D.famφB α) (unitW D.P.A)
  have hu : unitW D.P.A ≫ D.P.A.hom = 𝟙 _ := Over.w (η[D.P.A])
  let s : Sp (R ⧸ I ^ (e + 1)) ⟶ pullback D.P.A.hom (thick R I e) :=
    pullback.lift (thick R I e ≫ unitW D.P.A) (𝟙 _) (by rw [Category.assoc, hu, Category.comp_id, Category.id_comp])
  have hs : s ≫ pullback.fst D.P.A.hom (thick R I e) = thick R I e ≫ unitW D.P.A := pullback.lift_fst _ _ _
  have hm' : (s ≫ pullback.fst D.P.A.hom (thick R I e)) z ∈
      LB.wchart D.P.L (D.famφB α) (fun k => J (unitW D.P.A ≫ D.famφB α k)) := by
    rw [hs]; exact hm
  have h0 : ((thick R I e).stalkMap z).hom (sval b (unitW D.P.A) (thick R I e z) J) = 0 := by
    refine (stalkMap_gs (thick R I e) (unitW D.P.A) z _ hm _).trans ?_
    rw [← hs]
    refine (gs_pull s _ z _ hm' _).symm.trans ?_
    refine (congrArg (gs s z _) (hV _)).trans ?_
    refine (gs_eq s z _ hm' _).trans ?_
    rw [map_zero, map_zero]
  rw [h0, map_mul, map_pow, stalkMap_stalkOf] at h1
  exact (((Units.isUnit _).map _).pow k).mul_left_eq_zero.1 h1.symm

end GlobalTheory.Mum
end
end

