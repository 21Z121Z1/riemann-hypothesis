import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2314
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsFiniteEtaleCoverConstantTorsion
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0085
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemeGlueAffineCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0152
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2821
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2812
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2870
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2828
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2684
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2829
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0678
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesExist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2696
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2694
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2446
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2479
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2813
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2830
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2726
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2739

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackSelf
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LevSpread

theorem eq_of_comp_eq {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A) {n : ℕ}
    (hn : IsUnit (n : Γ(S, ⊤))) (Z : Over S) [PreconnectedSpace Z.left] (x y : Z ⟶ A) (hx : x ^ n = 1)
    (hy : y ^ n = 1) (T : Over S) (z : T ⟶ Z) [Nonempty T.left] (h : z ≫ x = z ≫ y) : x = y := by
  have hw : (x * y⁻¹) ^ n = 1 := by rw [mul_pow, inv_pow, hx, hy, inv_one, _root_.mul_one]
  obtain ⟨C, hC, hz⟩ := GlobalTheory.TorsionCover.exists_clopen_eq_one A hA hn (x * y⁻¹) hw
  have h1 : z ≫ (x * y⁻¹) = 1 := by
    show (preHom z) (x * y⁻¹) = 1
    rw [map_mul, map_inv]
    show (z ≫ x) * (z ≫ y)⁻¹ = 1
    rw [h, mul_inv_cancel]
  have hsub := (hz T z).1 h1
  obtain ⟨p⟩ := ‹Nonempty T.left›
  have hne : C.Nonempty := ⟨_, hsub ⟨p, rfl⟩⟩
  have huniv : C = Set.univ := hC.eq_univ hne
  have h2 : 𝟙 Z ≫ (x * y⁻¹) = 1 := (hz Z (𝟙 Z)).2 (by rw [huniv]; exact Set.subset_univ _)
  rw [Category.id_comp] at h2
  exact mul_inv_eq_one.1 h2

theorem isGrpPullback_self {S : Scheme.{0}} (G : Over S) [GrpObj G] : IsGrpPullback G G (𝟙 S) (𝟙 G.left) := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let ρ : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have ex : x₀ = ρ ≫ x := Over.OverMorphism.ext (hx.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  have ey : y₀ = ρ ≫ y := Over.OverMorphism.ext (hy.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  rw [ex, ey, ← MonObj.comp_mul]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

end GlobalTheory.LevSpread

namespace GlobalTheory.LevSpread

theorem l1 : ∀ (S T : Scheme.{0}) (A₀ : Over T) [GrpObj A₀] [IsCommMonObj A₀] (P₀ : LB (G2 A₀).left) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left) (f : T ⟶ S), P₀.IsLB → P.IsLB → SameFib A₀ P₀ (𝟙 _) A P f → ∃ (φ : A₀.left ⟶ A.left) (φ₂ : (G2 A₀).left ⟶ (G2 A).left), IsGrpPullback A₀ A f φ ∧ IsSquare φ φ₂ ∧ LBIso P₀ (P.pull φ₂) ∧ LBIso (P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left) ((P.pull (lift (𝟙 A) (𝟙 A)).left).pull φ) := GlobalTheory.T.grpPullback_of_sameFibreWithSquareBundle

theorem l2a : ∀ (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsNoetherianRing R₀] [IsIntegrallyClosed R₀] (A : Over (Sp R₀)) [GrpObj A] [IsCommMonObj A] (n : ℕ), IsAbelianScheme A → IsUnit (n : R₀) → TorsRat A n → ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ Sp R₀) (x : Over.mk t ⟶ A), x ^ n = 1 → ∃ σ : 𝟙_ (Over (Sp R₀)) ⟶ A, σ ^ n = 1 ∧ toUnit (Over.mk t) ≫ σ = x := GlobalTheory.T.exists_torsionSection_of_torsionRationalOverFraction

theorem l2 : ∀ (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsNoetherianRing R₀] [IsIntegrallyClosed R₀] (A : Over (Sp R₀)) [GrpObj A] [IsCommMonObj A] (n : ℕ), IsAbelianScheme A → IsUnit (n : R₀) → TorsRat A n → ∀ (K : Type) [Field K] (t : Sp K ⟶ Sp R₀) (x : Over.mk t ⟶ A), x ^ n = 1 → ∃ σ : 𝟙_ (Over (Sp R₀)) ⟶ A, σ ^ n = 1 ∧ toUnit (Over.mk t) ≫ σ = x := by
  intro R₀ _ _ _ _ A _ _ n hA hnR hT K _ t x hx
  have hnΓ : IsUnit (n : Γ(Sp R₀, ⊤)) := by
    have := hnR.map (Scheme.ΓSpecIso (CommRingCat.of R₀)).inv.hom
    rwa [map_natCast] at this
  let t' : Sp (AlgebraicClosure K) ⟶ Sp R₀ := spMap (algebraMap K (AlgebraicClosure K)) ≫ t
  let z : Over.mk t' ⟶ Over.mk t := Over.homMk (spMap (algebraMap K (AlgebraicClosure K))) rfl
  obtain ⟨σ, hσ, hσx⟩ := l2a R₀ A n hA hnR hT (AlgebraicClosure K) t' (z ≫ x)
    (by rw [← MonObj.comp_pow, hx, MonObj.comp_one])
  refine ⟨σ, hσ, ?_⟩
  haveI : PreconnectedSpace (Over.mk t).left := inferInstanceAs (PreconnectedSpace (Sp K))
  haveI : Nonempty (Over.mk t').left := inferInstanceAs (Nonempty (Sp (AlgebraicClosure K)))
  refine eq_of_comp_eq A hA hnΓ (Over.mk t) _ x (by rw [← MonObj.comp_pow, hσ, MonObj.comp_one]) hx (Over.mk t') z ?_
  rw [← Category.assoc, show z ≫ toUnit (Over.mk t) = toUnit (Over.mk t') from toUnit_unique _ _, hσx]

theorem l3 : ∀ (O : Type) [CommRing O] [IsDomain O] (A : Over (Sp O)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left), IsPPol A P → ∀ (N : ℕ), 0 < N → IsUnit (N : O) → ∀ (u v : 𝟙_ (Over (Sp O)) ⟶ A), u ^ N = 1 → v ^ N = 1 → ∀ (ζ : Oˣ), IsPrimitiveRoot ζ N → ∀ (m : ℤ) (K : Type) [Field K] (κ : O →+* K), Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) N (toUnit (Over.mk (spMap κ)) ≫ u) (toUnit (Over.mk (spMap κ)) ≫ v) (unitOn (Units.map κ.toMonoidHom (ζ ^ m))) → ∀ (k : Type) [Field k] (ρ : O →+* k), Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) N (toUnit (Over.mk (spMap ρ)) ≫ u) (toUnit (Over.mk (spMap ρ)) ≫ v) (unitOn (Units.map ρ.toMonoidHom (ζ ^ m))) := GlobalTheory.T.weilPairing_eq_zpow_of_fieldPoint_domain

theorem prim_map {n : ℕ} (hn : n ≠ 0) {R : Type} [CommRing R] [IsDomain R] (β : cycAway n →+* R) :
    IsPrimitiveRoot (β (zetaAway n)) n := by
  have h₁ : IsPrimitiveRoot (zetaAway n) n :=
    IsPrimitiveRoot.of_map_of_injective (f := (cycAway n).subtype) (Complex.isPrimitiveRoot_exp n hn) Subtype.val_injective
  have : NeZero (n : R) := ⟨by simpa using ((isUnit_natCast hn).map β).ne_zero⟩
  have h₂ := (h₁.isRoot_cyclotomic (Nat.pos_of_ne_zero hn)).map (f := β)
  rwa [Polynomial.map_cyclotomic, Polynomial.isRoot_cyclotomic_iff] at h₂

theorem level_spreads : ∀ (n : ℕ), 3 ≤ n → Odd n → ∀ (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsNoetherianRing R₀] [IsIntegrallyClosed R₀] (b : cycAway n →+* R₀) (A : Over (Sp R₀)) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left), IsAbelianScheme A → IsPPol A P → TorsRat A n → ∀ (g : ℕ) (K : Type) [Field K] (κ : R₀ →+* K) (c₀ : SiegPre g n (zetaAway n) (spMap (κ.comp b))), c₀.Principal → SameFib c₀.A c₀.P (𝟙 _) A P (spMap κ) → ∃ c : SiegPre g n (zetaAway n) (spMap b), c.Principal ∧ SiegPB c₀ c (spMap κ) ∧ ∃ (a : c.A.left ⟶ A.left) (a₂ : (G2 c.A).left ⟶ (G2 A).left), IsGrpPullback c.A A (𝟙 _) a ∧ IsSquare a a₂ ∧ LBIso c.P (P.pull a₂) := by
  intro n hn3 hnodd R₀ _ _ _ _ b A _ _ P hA hP hT g K _ κ c₀ hc₀ hsf
  have hn0 : n ≠ 0 := by omega
  have hnR : IsUnit (n : R₀) := by simpa using (isUnit_natCast hn0).map b
  have hnΓ : IsUnit (n : Γ(Sp R₀, ⊤)) := by
    have := hnR.map (Scheme.ΓSpecIso (CommRingCat.of R₀)).inv.hom
    rwa [map_natCast] at this

  have hζc : IsPrimitiveRoot (zetaAway n) n :=
    IsPrimitiveRoot.of_map_of_injective (f := (cycAway n).subtype) (Complex.isPrimitiveRoot_exp n hn0) Subtype.val_injective
  let ζU : (cycAway n)ˣ := (hζc.isUnit hn0).unit
  have hζU : (ζU : cycAway n) = zetaAway n := rfl
  let ζR : R₀ˣ := Units.map b.toMonoidHom ζU
  have hζR : IsPrimitiveRoot ζR n := IsPrimitiveRoot.coe_units_iff.1 (prim_map hn0 b)

  obtain ⟨φ, φ₂, hφ, hsq, hiso, hdiag⟩ := l1 _ _ c₀.A c₀.P A P (spMap κ) c₀.isLB hP.1.1 hsf
  let E := GlobalTheory.ObjPull.pushEquiv hφ (𝟙_ (Over (Sp K)))
  have hxa : ∀ a, (E (c₀.lev a)) ^ n = 1 := fun a => by rw [← map_pow, c₀.lev_tors, map_one]
  choose σ hσn hσx using fun a => l2 R₀ A n hA hnR hT K _ (E (c₀.lev a)) (hxa a)
  have hcomp : ∀ a, (c₀.lev a).left ≫ φ = spMap κ ≫ (σ a).left := fun a => by
    have e := congrArg (fun w => w.left) (hσx a)
    simp only [Over.comp_left, GlobalTheory.ObjPull.toUnit_left'] at e
    rw [← GlobalTheory.ObjPull.pushEquiv_left hφ, ← e]
    exact congrArg (· ≫ (σ a).left) (Category.id_comp _)
  haveI : PreconnectedSpace (𝟙_ (Over (Sp R₀))).left := inferInstanceAs (PreconnectedSpace (Sp R₀))
  have inj : ∀ (T : Over (Sp R₀)) [Nonempty T.left] (s s' : 𝟙_ (Over (Sp R₀)) ⟶ A), s ^ n = 1 → s' ^ n = 1 →
      toUnit T ≫ s = toUnit T ≫ s' → s = s' := fun T _ s s' hs hs' h =>
    eq_of_comp_eq A hA hnΓ (𝟙_ _) s s' hs hs' T (toUnit T) h
  haveI : Nonempty (Over.mk ((𝟙_ (Over (Sp K))).hom ≫ spMap κ)).left := inferInstanceAs (Nonempty (Sp K))
  have hadd : ∀ a a', σ (a + a') = σ a * σ a' := fun a a' =>
    inj _ _ _ (hσn _) (by rw [mul_pow, hσn, hσn, _root_.mul_one])
      (by rw [MonObj.comp_mul, hσx, hσx, hσx, c₀.lev_add, map_mul])
  have one_iff : ∀ (T : Over (Sp R₀)) [Nonempty T.left] a, toUnit T ≫ σ a = 1 ↔ σ a = 1 := fun T _ a =>
    ⟨fun h => inj T (σ a) 1 (hσn a) (one_pow n) (h.trans (MonObj.comp_one _).symm),
      fun h => by rw [h, MonObj.comp_one]⟩
  let c : SiegPre g n (zetaAway n) (spMap b) :=
    { A := A
      ab := hA
      P := P
      isLB := hP.1.1
      rig₁ := hP.1.2.1
      rig₂ := hP.1.2.2.1
      symm := hP.1.2.2.2
      lev := σ
      lev_add := hadd
      lev_tors := hσn
      geom := ?_ }
  refine ⟨c, ⟨hP.2.1, hP.2.2⟩, ⟨φ, φ₂, hφ, hsq, hiso, hcomp⟩,
    ⟨𝟙 _, 𝟙 _, isGrpPullback_self A, ⟨(Category.id_comp _).trans (Category.comp_id _).symm,
      (Category.id_comp _).trans (Category.comp_id _).symm⟩, GlobalTheory.ThetaAffineGlue.lbIso_pull_id hP.1.1⟩⟩
  intro k _ _ x β z hxβ hz
  obtain ⟨ρ, rfl⟩ : ∃ ρ : R₀ →+* k, spMap ρ = x := ⟨(Spec.preimage x).hom, by simp [spMap]⟩
  have hβ : β = ρ.comp b := by
    have e : spMap (ρ.comp b) = spMap β := by rw [← hxβ]; exact Spec.map_comp _ _
    exact (congrArg CommRingCat.Hom.hom (Spec.map_injective e)).symm
  have hzU : z = Units.map ρ.toMonoidHom ζR := Units.ext (by rw [hz, hβ]; rfl)
  subst hzU
  let iK : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  let x₀ : Sp (AlgebraicClosure K) ⟶ Sp K := spMap iK
  obtain ⟨g1, g2, g3⟩ := c₀.geom (AlgebraicClosure K) x₀ ((iK.comp κ).comp b)
    (Units.map ((iK.comp κ).comp b).toMonoidHom ζU) (by rw [← Spec.map_comp]; rfl) rfl
  let T₀ : Over (Sp R₀) := Over.mk ((Over.mk x₀).hom ≫ spMap κ)
  haveI : Nonempty T₀.left := inferInstanceAs (Nonempty (Sp (AlgebraicClosure K)))
  haveI : Nonempty (Over.mk (spMap ρ)).left := inferInstanceAs (Nonempty (Sp k))
  have push : ∀ a, GlobalTheory.ObjPull.pushEquiv hφ (Over.mk x₀) (toUnit _ ≫ c₀.lev a) = toUnit T₀ ≫ σ a := fun a => by
    apply Over.OverMorphism.ext
    rw [GlobalTheory.ObjPull.pushEquiv_left, Over.comp_left, Over.comp_left, Category.assoc, hcomp,
      GlobalTheory.ObjPull.toUnit_left', GlobalTheory.ObjPull.toUnit_left']
    exact (Category.assoc _ _ _).symm
  refine ⟨fun a => ?_, fun gg hg => ?_, fun a a' => ?_⟩
  · rw [one_iff, ← one_iff T₀, ← push, map_eq_one_iff _ (GlobalTheory.ObjPull.pushEquiv hφ _).injective]
    exact g1 a
  · obtain ⟨τ, hτn, hτ⟩ := l2 R₀ A n hA hnR hT k (spMap ρ) gg hg
    obtain ⟨a, ha⟩ := g2 ((GlobalTheory.ObjPull.pushEquiv hφ (Over.mk x₀)).symm (toUnit T₀ ≫ τ))
      (by rw [← map_pow, ← MonObj.comp_pow, hτn, MonObj.comp_one, map_one])
    refine ⟨a, ?_⟩
    have e : σ a = τ := inj T₀ _ _ (hσn a) hτn (by rw [← push, ha, MulEquiv.apply_symm_apply])
    rw [e, hτ]
  · have H' := (GlobalTheory.weilIs_iff_of_isGrpPullback_comm (Sp R₀) (Sp K) A c₀.A (spMap κ) φ
      (P.pull (lift (𝟙 A) (𝟙 A)).left) (c₀.P.pull (lift (𝟙 c₀.A) (𝟙 c₀.A)).left) (pull_isLB hP.1.1 _)
      (pull_isLB c₀.isLB _) hφ hdiag (Over.mk x₀) (n : ℤ) _ _ (toUnit T₀ ≫ σ a) (toUnit T₀ ≫ σ a') _
      (by rw [← push]; rfl) (by rw [← push]; rfl)).1 (g3 a a')
    have ht : (Over.mk x₀).hom ≫ spMap κ = spMap (iK.comp κ) := by
      show x₀ ≫ spMap κ = _
      rw [← Spec.map_comp]; rfl
    have hu : (Units.map ((iK.comp κ).comp b).toMonoidHom ζU) ^ (2 * omegaStd a a') =
        Units.map (iK.comp κ).toMonoidHom (ζR ^ (2 * omegaStd a a')) := by
      rw [map_zpow]; rfl
    rw [hu] at H'
    simp only [T₀] at H'
    rw [ht] at H'
    have H'' := l3 R₀ A hA P hP n (by omega) hnR (σ a) (σ a') (hσn a) (hσn a') ζR hζR (2 * omegaStd a a')
      (AlgebraicClosure K) (iK.comp κ) H' k ρ
    rw [← map_zpow]
    exact H''

end GlobalTheory.LevSpread
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGtPointInvolutionActionSubOfIdempotent
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TorusExt

noncomputable section

namespace GlobalTheory.Mum.IdemDiff

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
variable {O : Type} [Ring O] [StarRing O] [Module O D.X]

theorem val_act (oa : D.OAct O) (a : O)
    (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A (oa.onB.act (star a)) (oa.onB.act a)) rosatiε))
    (g : GtPtF D F) (χ : D.X) {y J} (hJ : Good D.P.L y J) :
    val (LB.mulGen D.P.L _ _ _ _ (g.s (star a • χ))
        (LB.pullGen D.P.L _ _ u (lift (cP D _ χ) g.b).left)) (𝟙 (TF (R := R) F).left) y J =
        charVal g (star a • χ) y J * val₂ u y J (cP D _ χ) g.b :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl ((val_pull hJ _ _ _).trans (by rw [Category.id_comp]; rfl)))

theorem gtPtAct_of_isAdd : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F] {O : Type} [Ring O] [StarRing O] [Module O D.X] (oa : D.OAct O) (a : O), a * a = a → ∀ g₀ g h t : GtPtF D F, GtPtAct oa a g₀ g → GtPtAct oa a h h → GtPtF.IsAdd t h g → GtPtAct oa a t t := by
  intro R _ _ D F _ _ O _ _ _ oa a ha g₀ g h t hg hh hadd
  have hG : GlobalFnsSt := GlobalTheory.globalFns_holds
  have := oa.onB.hom a
  have := oa.onB.hom (star a)
  have hs : star a * star a = star a := by rw [← star_mul, ha]
  have cf : ∀ (T) (x : O) χ, cP D T (x • χ) = cP D T χ ≫ oa.onB.act x := fun T x χ => by
    rw [cP, oa.c_lin, ← Category.assoc]; rfl
  have aa : oa.onB.act a = oa.onB.act a ≫ oa.onB.act a := by rw [← oa.onB.map_mul, ha]
  have ss : oa.onB.act (star a) = oa.onB.act (star a) ≫ oa.onB.act (star a) := by rw [← oa.onB.map_mul, hs]
  obtain ⟨b₁, v₁⟩ := (isAdd_iff_val _ _ _).1 hadd
  have gb : g.b = g.b ≫ oa.onB.act a := by rw [hg.1, Category.assoc, ← aa]
  have tb : t.b = t.b ≫ oa.onB.act a := by
    have e := gb
    rw [b₁, MonObj.mul_comp, ← hh.1] at e
    exact mul_right_cancel e
  refine ⟨tb, fun u hu u₀ χ => corr_of_val D.P.isLB fun y J hJ => (val_act oa a u t χ hJ).trans ?_⟩
  have vg : ∀ χ, charVal g χ y J = charVal g₀ (star a • χ) y J * val₂ u y J (cP D _ χ) g₀.b := fun χ =>
    (val_corr hJ (hg.2 u hu u₀ χ) _).symm.trans (val_act oa a u g₀ χ hJ)
  have vh : charVal h χ y J = charVal h (star a • χ) y J * val₂ u y J (cP D _ χ) h.b :=
    (val_corr hJ (hh.2 u hu u₀ χ) _).symm.trans (val_act oa a u h χ hJ)
  have vc := IsRos.val_comp hG D.P.isAb D.P.isLB ss aa ⟨hu, u₀⟩ ⟨hu, u₀⟩ ⟨hu, u₀⟩ hJ (cP D _ χ) g₀.b
  have vg' : charVal g χ y J = charVal g (star a • χ) y J * val₂ u y J (cP D _ χ) g.b := by
    rw [vg χ, vg (star a • χ), ← mul_smul, hs, vc, cf, hg.1, _root_.mul_assoc]
  have ra := (ros_add D.cub hG D.P.isAb _ _ u hu u₀ (T := TF (R := R) F) hJ t.b h.b (cP D _ χ)).2
  rw [← tb, ← hh.1, ← b₁] at ra
  have e₂ := v₁ (star a • χ) y J hJ
  rw [cf] at e₂
  have a₁ := congrArg Additive.ofMul ra
  have a₂ := congrArg Additive.ofMul e₂
  have a₃ := congrArg Additive.ofMul (v₁ χ y J hJ)
  have a₄ := congrArg Additive.ofMul vg'
  have a₅ := congrArg Additive.ofMul vh
  show _ = charVal t χ y J
  apply Additive.ofMul.injective
  simp only [ofMul_mul, th] at a₁ a₂ a₃ a₄ a₅ ⊢
  linear_combination (norm := abel) a₃ - a₄ + a₅ - a₁ - a₂

end GlobalTheory.Mum.IdemDiff
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfSmoothGeomIrreducibleOverModificatioStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_of_smooth_geomIrreducible_over_modification : ∀ (R : Type) [CommRing R] [IsDomain R] (M : Modif R) (G : Over M.S), Smooth G.hom → GeometricallyIrreducible G.hom → Nonempty G.left → IsIntegral G.left := by
  first | exact @GlobalTheory.MumInt.isIntegral_of_smooth | exact GlobalTheory.MumInt.isIntegral_of_smooth | (intros; apply GlobalTheory.MumInt.isIntegral_of_smooth <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIrreducibleFibreFstStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIrreducible_preimage_fst_of_isSemiAbelian : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → ∀ x : G.left, IsIrreducible ((fst G G).left ⁻¹' {x}) := by
  first | exact @GlobalTheory.MoverFibre.isIrreducible_fibre_fst | exact GlobalTheory.MoverFibre.isIrreducible_fibre_fst | (intros; apply GlobalTheory.MoverFibre.isIrreducible_fibre_fst <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoFlagModelFlagBundleOverModuliStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIso_flagModel_flagBundle_over_moduli : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)}, ∀ (X : GlobalTheory.FlagMod.FlagCover Y) (Z : Formalism.L2.Pj.Comp Xo c), GlobalTheory.VarFlag.FramesExist X → ∀ (C : GlobalTheory.ShFam.FlagCpt Y (RingEquiv.refl c.F)), GlobalTheory.VarFlag.CarriesTri C → ∀ (B : GlobalTheory.ProjVar.Var c.F) (j : B.X ⟶ GlobalTheory.Toroidal.gen Y) [IsOpenImmersion j] (f : C.Y.X ⟶ B.X), C.π = f ≫ j → (∀ w : GlobalTheory.Toroidal.gen Y, GlobalTheory.Toroidal.genι Y w ∈ GlobalTheory.CompHS.barComp Y Z ↔ w ∈ Set.range j) → ∀ (h : GlobalTheory.CompHS.Y₀ X Z ⟶ C.Y.X) [IsProper h], (∀ (K : Type) [Field K] (z : Sp K ⟶ GlobalTheory.CompHS.Y₀ X Z), ∃! p : Sp K ⟶ C.Y.X, GlobalTheory.VarFlag.Rel X.F C (z ≫ GlobalTheory.CompHS.inc₀ X Z) p) → (∀ (K : Type) [Field K] (z : Sp K ⟶ GlobalTheory.CompHS.Y₀ X Z), GlobalTheory.VarFlag.Rel X.F C (z ≫ GlobalTheory.CompHS.inc₀ X Z) (z ≫ h)) → IsIso (h ∣_ GlobalTheory.VarFlag.Vo C) := by
  first | exact @GlobalTheory.VarFlag.isIso_restrict_Vo | exact GlobalTheory.VarFlag.isIso_restrict_Vo | (intros; apply GlobalTheory.VarFlag.isIso_restrict_Vo <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalHomCompletedStalkToDvrOverTraitStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocalHom_completedStalk_to_dvr_over_trait : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (M : RatModel o' Ω) (x : M.Z) (R : Type) [CommRing R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), IsCpl j → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V) (V' : Type) [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'] (h : V →+* V') (g' : R →+* V') (ξ : Sp V ⟶ M.Z), Irreducible (h ϖ) → ξ (IsLocalRing.closedPoint V) = x → spMap g' ≫ (spMap j ≫ M.Z.fromSpecStalk x) = spMap h ≫ ξ → IsLocalHom g' := by
  first | exact @GlobalTheory.Poinc.TraitLocal.isLocalHom_of_square | exact GlobalTheory.Poinc.TraitLocal.isLocalHom_of_square | (intros; apply GlobalTheory.Poinc.TraitLocal.isLocalHom_of_square <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyNoetherianOfSmoothOverModificationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocallyNoetherian_of_smooth_over_modification : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (M : Modif R) (G : Over M.S), Smooth G.hom → IsLocallyNoetherian G.left := by
  first | exact @GlobalTheory.Mum.isLocallyNoetherian_of_smooth_over_modif | exact GlobalTheory.Mum.isLocallyNoetherian_of_smooth_over_modif | (intros; apply GlobalTheory.Mum.isLocallyNoetherian_of_smooth_over_modif <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsModelValBaseChange
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult.ModelValBaseChange

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}

theorem spMap_comp_ringHom {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map (CommRingCat.ofHom (g.comp f)) = Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f)
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

theorem dualMapR_comp_ringHom {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    Chart.dualMapR (g.comp f) = (Chart.dualMapR g).comp (Chart.dualMapR f) :=
  RingHom.ext fun x ↦ TrivSqZeroExt.ext (by simp [Chart.dualMapR]) (by simp [Chart.dualMapR])

variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R'']

theorem lieCorr_comp {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')} {X'' : Obj F 𝔠 (Sp R'')} {σ : R →+* R'}
    {τ : R' →+* R''} {φ : X'.A.left ⟶ X.A.left} {φ' : X''.A.left ⟶ X'.A.left} {v : X.Lie} {v' : X'.Lie}
    {v'' : X''.Lie} (h : Obj.LieCorr σ φ v v') (h' : Obj.LieCorr τ φ' v' v'') :
    Obj.LieCorr (τ.comp σ) (φ' ≫ φ) v v'' := by
  unfold Obj.LieCorr at *
  rw [← Category.assoc, h', Category.assoc, h, ← Category.assoc, ← spMap_comp_ringHom, ← dualMapR_comp_ringHom]

theorem exists_lieCorr {σ : R →+* R'} {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')} {φ : X'.A.left ⟶ X.A.left}
    (hp : X'.IsPullBy X (spMap σ) φ) (v : X.Lie) : ∃ w : X'.Lie, Obj.LieCorr σ φ v w := by
  letI := σ.toAlgebra
  obtain ⟨e, he, -⟩ := Obj.exists_lieEquiv (R' := R') hp
  exact ⟨e (1 ⊗ₜ v), (he _ _).2 rfl⟩

theorem lieCorr_unique {σ : R →+* R'} {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')} {φ : X'.A.left ⟶ X.A.left}
    (hp : X'.IsPullBy X (spMap σ) φ) {v : X.Lie} {w₁ w₂ : X'.Lie} (h₁ : Obj.LieCorr σ φ v w₁)
    (h₂ : Obj.LieCorr σ φ v w₂) : w₁ = w₂ := by
  letI := σ.toAlgebra
  obtain ⟨e, he, -⟩ := Obj.exists_lieEquiv (R' := R') hp
  exact ((he _ _).1 h₁).trans ((he _ _).1 h₂).symm

theorem isPullBy_comp {σ : R →+* R'} {τ : R' →+* R''} {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')}
    {X'' : Obj F 𝔠 (Sp R'')} {φ : X'.A.left ⟶ X.A.left} {φ' : X''.A.left ⟶ X'.A.left}
    (hp : X'.IsPullBy X (spMap σ) φ) (hp' : X''.IsPullBy X' (spMap τ) φ') :
    X''.IsPullBy X (spMap (τ.comp σ)) (φ' ≫ φ) := by
  rw [spMap_comp_ringHom]
  exact hp'.comp hp

theorem detCorr_comp {σ : R →+* R'} {τ : R' →+* R''} {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')}
    {X'' : Obj F 𝔠 (Sp R'')} {φ : X'.A.left ⟶ X.A.left} {φ' : X''.A.left ⟶ X'.A.left}
    (hp : X'.IsPullBy X (spMap σ) φ) (hp' : X''.IsPullBy X' (spMap τ) φ') {δ : X.DetOmega} {δ' : X'.DetOmega}
    {δ'' : X''.DetOmega} (hd : Obj.DetCorr σ φ δ δ') (hd' : Obj.DetCorr τ φ' δ' δ'') :
    Obj.DetCorr (τ.comp σ) (φ' ≫ φ) δ δ'' := by
  intro v v'' hv
  choose v' hv' using fun i ↦ exists_lieCorr hp (v i)
  choose w hw using fun i ↦ exists_lieCorr hp' (v' i)
  have hwv : w = v'' := funext fun i ↦
    lieCorr_unique (isPullBy_comp hp hp') (lieCorr_comp (hv' i) (hw i)) (hv i)
  subst hwv
  rw [hd' v' w hw, hd v v' hv', RingHom.comp_apply]

end GlobalTheory.RealMult.ModelValBaseChange

namespace GlobalTheory.RealMult

open ModelValBaseChange in

theorem isModelVal_baseChange : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (R₀ : Type) [CommRing R₀] (k : ℕ)
  (r₀ : Rule (rapObj 𝔠) R₀ k) (M : Scheme.{0}) (U : Obj F 𝔠 M) (R R' : Type) [CommRing R] [Algebra R₀ R]
  [CommRing R'] [Algebra R₀ R'] (σ : R →ₐ[R₀] R') (X : Obj F 𝔠 (Sp R)) (X' : Obj F 𝔠 (Sp R'))
  (φ : X'.A.left ⟶ X.A.left) (δ : X.DetGen) (δ' : X'.DetGen) (v : R), X'.IsPullBy X (spMap (σ : R →+* R')) φ →
  Obj.DetCorr (σ : R →+* R') φ δ.1 δ'.1 → IsModelVal r₀ U X δ v → IsModelVal r₀ U X' δ' (σ v) := by
  intro F _ _ 𝔠 R₀ _ k r₀ M U R R' _ _ _ _ σ X X' φ δ δ' v hp hd hv
  intro R'' _ _ τ X'' φ'' δ'' hp'' hd'' W hW Y φY hY δY h hh ψ χ hχ
  have hc : ((τ.comp σ : R →ₐ[R₀] R'') : R →+* R'') = (τ : R' →+* R'').comp (σ : R →+* R') := rfl
  have := hv R'' (τ.comp σ) X'' (φ'' ≫ φ) δ'' (by rw [hc]; exact isPullBy_comp hp hp'')
    (by rw [hc]; exact detCorr_comp hp hp'' hd hd'') W hW Y φY hY δY h hh ψ χ hχ
  exact this

end GlobalTheory.RealMult
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsModelValHomog
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult

theorem DetGen.smul_cancel {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R : Type} [CommRing R]
    (X : Obj F 𝔠 (Sp R)) (δ : X.DetGen) {r s : R} (h : r • δ.1 = s • δ.1) : r = s := by
  haveI := Obj.invertible_detOmega X
  refine FaithfulSMul.eq_of_smul_eq_smul (α := X.DetOmega) fun m ↦ ?_
  have hm : m ∈ Submodule.span R {δ.1} := by rw [δ.2]; exact Submodule.mem_top
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hm
  rw [smul_comm r t, smul_comm s t, h]

theorem isModelVal_homog : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (R₀ : Type) [CommRing R₀] (k : ℕ)
  (r₀ : Rule (rapObj 𝔠) R₀ k) (M : Scheme.{0}) (U : Obj F 𝔠 M) (R : Type) [CommRing R] [Algebra R₀ R]
  (X : Obj F 𝔠 (Sp R)) (δ δ' : X.DetGen) (c v : R), δ'.1 = c • δ.1 → IsModelVal r₀ U X δ' v →
    IsModelVal r₀ U X δ (c ^ k * v) := by
  intro F _ _ 𝔠 R₀ _ k r₀ M U R _ _ X δ δ' c v hδ hv
  intro R' _ _ σ X' φ' δ'' hX' hδ'' W hW Y φY hY δY h hh ψ χ hχ δY' u hY' hu

  have hδm : δ.1 ∈ Submodule.span R {δ'.1} := by rw [δ'.2]; exact Submodule.mem_top
  obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.1 hδm
  have hdc : d * c = 1 := DetGen.smul_cancel X δ (by rw [mul_smul, ← hδ, hd, one_smul])

  have hgen : Submodule.span R' {((σ : R →+* R') c) • δ''.1} = ⊤ := by
    refine eq_top_iff.2 fun m _ ↦ ?_
    have hm : m ∈ Submodule.span R' {δ''.1} := by rw [δ''.2]; exact Submodule.mem_top
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hm
    refine Submodule.mem_span_singleton.2 ⟨t * (σ : R →+* R') d, ?_⟩
    rw [smul_smul, _root_.mul_assoc, ← map_mul, hdc, map_one, _root_.mul_one]

  have hcorr : Obj.DetCorr (σ : R →+* R') φ' δ'.1 (((σ : R →+* R') c) • δ''.1) := by
    intro w w' hw
    rw [hδ, AlternatingMap.smul_apply, AlternatingMap.smul_apply, smul_eq_mul, smul_eq_mul, hδ'' w w' hw,
      map_mul]
  obtain ⟨δ''', hδ''', huniq⟩ := hX'.existsUnique_detGen (σ : R →+* R') δ'
  have heq : δ'''.1 = ((σ : R →+* R') c) • δ''.1 :=
    (congrArg Subtype.val (huniq ⟨_, hgen⟩ hcorr)).symm
  have hYm : δY'.1 ∈ Submodule.span R' {δ'''.1} := by rw [δ'''.2]; exact Submodule.mem_top
  obtain ⟨u', hu'⟩ := Submodule.mem_span_singleton.1 hYm
  have hval := hv R' σ X' φ' δ''' hX' hδ''' W hW Y φY hY δY h hh ψ χ hχ δY' u' hY' hu'.symm
  have huu : u = u' * (σ : R →+* R') c := DetGen.smul_cancel X' δ'' (by rw [← hu, ← hu', heq, smul_smul])
  rw [huu, mul_pow, map_mul, map_pow, hval]
  simp only [RingHom.coe_coe]
  ring

end GlobalTheory.RealMult
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomOfBaseChangesArtinFibreProductStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isGrpPullback_id_of_baseChanges_artinFibreProduct : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (A' A : Over (Spec P)) [GrpObj A'] [GrpObj A] (A₁ : Over (Spec R₁)) (A₂ : Over (Spec R₂)) (A₀ : Over (Spec R₀)) [GrpObj A₁] [GrpObj A₂] [GrpObj A₀] (j₁ : A₁.left ⟶ A'.left) (j₂ : A₂.left ⟶ A'.left) (k₁ : A₁.left ⟶ A.left) (k₂ : A₂.left ⟶ A.left) (i₁ : A₀.left ⟶ A₁.left) (i₂ : A₀.left ⟶ A₂.left) (φ : A'.left ⟶ A.left), Flat A'.hom → IsGrpPullback A₁ A' (Spec.map f₁) j₁ → IsGrpPullback A₂ A' (Spec.map f₂) j₂ → IsGrpPullback A₁ A (Spec.map f₁) k₁ → IsGrpPullback A₂ A (Spec.map f₂) k₂ → IsGrpPullback A₀ A₁ (Spec.map g₁) i₁ → IsGrpPullback A₀ A₂ (Spec.map g₂) i₂ → i₁ ≫ j₁ = i₂ ≫ j₂ → IsPullback φ A'.hom A.hom (𝟙 _) → j₁ ≫ φ = k₁ → j₂ ≫ φ = k₂ → IsGrpPullback A' A (𝟙 _) φ := by
  first | exact @GlobalTheory.PinchHom.main | exact GlobalTheory.PinchHom.main | (intros; apply GlobalTheory.PinchHom.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomSectionOfProdTrivialStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isMonHom_of_section_of_isIso_lift : ∀ (S : Scheme.{0}) (B B₁ B₂ : Over S) [GrpObj B] [GrpObj B₁] [GrpObj B₂] (p₁ : B ⟶ B₁) (p₂ : B ⟶ B₂) (i₁ : B₁ ⟶ B), IsMonHom p₁ → IsMonHom p₂ → IsIso (lift p₁ p₂) → i₁ ≫ p₁ = 𝟙 _ → i₁ ≫ p₂ = toUnit _ ≫ η[B₂] → IsMonHom i₁ := by
  first | exact @GlobalTheory.isMonHom_section_of_prod_trivial | exact GlobalTheory.isMonHom_section_of_prod_trivial | (intros; apply GlobalTheory.isMonHom_section_of_prod_trivial <;> assumption)
end

