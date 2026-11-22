import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2418
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2364
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2447
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0090
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0130
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0085
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2387
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2290
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitMkOfFormallyUnramified
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2388
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2377
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2345
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1523
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralNthRootTestModelPoint
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0177
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2420
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0469
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStandardSmoothLocalizationAwayJacobianDvdStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isStandardSmooth_localizationAway_jacobian_dvd : ∀ (R ν σ : Type) [CommRing R] [Finite ν] [Fintype σ] [DecidableEq σ] (m : σ → ν), Function.Injective m → ∀ (F : σ → MvPolynomial ν R) (h : MvPolynomial ν R), (Matrix.of fun s t : σ ↦ MvPolynomial.pderiv (m s) (F t)).det ∣ h → Algebra.IsStandardSmoothOfRelativeDimension (Nat.card ν - Nat.card σ) R (Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range F)) h)) := by
  first | exact @GlobalTheory.Pinch.isStandardSmoothOfRelativeDimension_localizationAway_of_det_dvd | exact GlobalTheory.Pinch.isStandardSmoothOfRelativeDimension_localizationAway_of_det_dvd | (intros; apply GlobalTheory.Pinch.isStandardSmoothOfRelativeDimension_localizationAway_of_det_dvd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymplecticLevelOfPulledBackObject
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover

namespace GlobalTheory.HTSympCover

theorem isSympLev_of_sympCond_pull : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ)
  (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (T : Over S) (t₁ : T.left ⟶ Sp (cycAway M))
  (o' : Obj b N (T.hom ≫ t)) (m : ObjMap o' o T.hom)
  (lv' : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over T.left) ⟶ o'.A)) (lv : (Fin h ⊕ Fin h → ℤ) → (T ⟶ o.A)),
    (∀ a, (lv' a).left ≫ m.φ = (lv a).left) → SympCond o h M T t₁ lv →
      IsSympLev o'.P h M (zetaAway M) t₁ lv' := by
  intro p _ D R _ b N h M S t o T t₁ o' m lv' lv hα hlv
  obtain ⟨hadd, hkill, hgeo⟩ := hlv
  obtain ⟨ρ, eρ⟩ := GlobalTheory.HkSetPull.exists_equiv m.cart (𝟙_ (Over T.left))
  let j : Over.mk ((𝟙_ (Over T.left)).hom ≫ T.hom) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have key : ∀ a, ρ (lv' a) = j ≫ lv a := fun a => Over.OverMorphism.ext (by simp [eρ, hα, j])
  have dg := GlobalTheory.SiegelPull.diag_iso m.sq m.pol
  refine ⟨fun a c => ρ.injective ?_, fun a => ρ.injective ?_, fun k _ _ x β z hx hz => ?_⟩
  · rw [map_mul, key, key, key, hadd, MonObj.comp_mul]
  · rw [map_pow, key, ← MonObj.comp_pow, hkill, MonObj.comp_one, map_one]
  obtain ⟨hker, honto, hw⟩ := hgeo k x β z hx hz
  obtain ⟨σ, eσ⟩ := GlobalTheory.HkSetPull.exists_equiv m.cart (Over.mk x)
  have key' : ∀ a, σ (toUnit (Over.mk x) ≫ lv' a) = (Over.homMk x rfl : Over.mk (x ≫ T.hom) ⟶ T) ≫ lv a :=
    fun a => Over.OverMorphism.ext (by
      rw [eσ, Over.comp_left, Category.assoc, hα, Over.comp_left]
      congr 1)
  refine ⟨fun a => ?_, fun g hg => ?_, fun a c => ?_⟩
  · rw [← hker a, ← key', map_eq_one_iff _ σ.injective]
  · obtain ⟨a, ha⟩ := honto (σ g) (by rw [← map_pow, hg, map_one])
    exact ⟨a, σ.injective (by rw [key', ha])⟩
  · exact (GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ o.A o'.A T.hom m.φ _ _ (pull_isLB o.isLB _)
      (pull_isLB o'.isLB _) m.cart dg (Over.mk x) M _ _ _ _ _ (eσ _) (eσ _)).2 (by rw [key', key']; exact hw a c)

end GlobalTheory.HTSympCover
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymplecticOfSubring
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings

open GlobalTheory.EighthPower GlobalTheory.CechPic GlobalTheory.MatrixBundle GlobalTheory.ZM

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SympDescent

theorem translFixed_of_pair {S : Scheme.{0}} {h M : ℕ} (A : Over S) [GrpObj A] (P : LB (A ⊗ A).left)
    (H : IsSymmetricPair h A P) (ha : Out.RelAmple A (diagPull A P)) (x : 𝟙_ (Over S) ⟶ A) (hx : x ^ M = 1) :
    (M : ℤ) • cls (diagPull A P) (pull_isLB H.2.2.1 _) =
      (M : ℤ) • pull ((toUnit A ≫ x) * 𝟙 A).left (cls (diagPull A P) (pull_isLB H.2.2.1 _)) := by
  haveI := H.1.comm
  have hP := H.2.2.1
  have hb : IsSymBilin (cls P hP) := isSymBilin_of_gen hP (fun T x x' y =>
    (Biadditive.biadditive_of_triv_axes globalFns_holds S A (diagPull A P) H.1 (pull_isLB hP _) ha P hP
      H.2.2.2.1 H.2.2.2.2.1 T x x' y).1) H.2.2.2.2.2
  have d : ∀ f : A ⟶ A, pull f.left (cls (diagPull A P) (pull_isLB hP _)) = pairCls (cls P hP) f f := fun f =>
    (pull_pairCls (cls P hP) f (𝟙 _) (𝟙 _)).trans (by rw [Category.comp_id])
  have z : ∀ y : A ⟶ A, (M : ℤ) • pairCls (cls P hP) (toUnit A ≫ x) y = 0 := fun y => by
    have e := BilinCalc.map_prod_zpow (fun z => pairCls (cls P hP) z y) (fun a b => hb.mul _ a b y)
      (fun _ : Fin 1 => toUnit A ≫ x) fun _ => (M : ℤ)
    simp only [Finset.univ_unique, Finset.prod_const, Finset.card_singleton, pow_one, Finset.sum_const, one_smul,
      zpow_natCast] at e
    rw [← e, ← MonObj.comp_pow, hx, MonObj.comp_one]
    exact one_left (hb.mul _) y
  rw [d, hb.mul, hb.symm _ (𝟙 A) (_ * _), hb.mul, smul_add, smul_add, z, z, zero_add, zero_add]
  rfl

theorem units_map_comp_appTop {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (u : Γ(Z, ⊤)ˣ) :
    Units.map (f ≫ g).appTop.hom.toMonoidHom u =
      Units.map f.appTop.hom.toMonoidHom (Units.map g.appTop.hom.toMonoidHom u) :=
  Units.ext (by simp [Scheme.Hom.comp_appTop]; rfl)

theorem isSymplectic_of_subring : ∀ (h M : ℕ) (B R : Type) [CommRing B] [CommRing R] (ζ : Bˣ) (R₁ : Subring R) (s₁ : Sp R₁ ⟶ Sp B) (A : Over (Sp R)) [GrpObj A] (P : LB (A ⊗ A).left) (lv : Std h M → (𝟙_ (Over (Sp R)) ⟶ A)) (A₁ : Over (Sp R₁)) [GrpObj A₁] (P₁ : LB (A₁ ⊗ A₁).left) (lv₁ : Std h M → (𝟙_ (Over (Sp R₁)) ⟶ A₁)), 0 < M → ζ ^ M = 1 → IsUnit (M : R₁) → IsSymmetricPair h A₁ P₁ → IsPrincipal A₁ P₁ → IsLevel A₁ lv₁ → P.IsLB → IsPullbackTriple A P lv A₁ P₁ lv₁ (spMap R₁.subtype) → IsSymplectic ζ (spMap R₁.subtype ≫ s₁) A P lv → IsSymplectic ζ s₁ A₁ P₁ lv₁ := by
  intro h M B R _ _ ζ R₁ s₁ A _ P lv A₁ _ P₁ lv₁ hM hζ hu H₁ H₂ H₃ hPR Hpb Hs
  haveI := H₁.1.comm
  have hP := H₁.2.2.1
  have hD : (diagPull A₁ P₁).IsLB := pull_isLB hP _
  have z₀ : lv₁ 0 = 1 := by
    have e := H₃.1 0 0
    rw [add_zero] at e
    exact left_eq_mul.1 e
  have tors : ∀ a, lv₁ a ^ M = 1 := fun a => by
    have e : ∀ n : ℕ, lv₁ (n • a) = lv₁ a ^ n := fun n => by
      induction n with
      | zero => rw [zero_smul, pow_zero, z₀]
      | succ n ih => rw [succ_nsmul, H₃.1, ih, pow_succ]
    rw [← e, show M • a = 0 by ext i <;> simp, z₀]
  have th : ∀ a (p : (𝟙_ (Over (Sp R₁))).left), ∃ V : (𝟙_ (Over (Sp R₁))).left.Opens, p ∈ V ∧
      ∃ θ : Out.ThetaGrp A₁ (diagPull A₁ P₁) M (Out.overRes V), θ.pt = Out.overResι V ≫ lv₁ a := fun a p => by
    let T := Out.overRes (T := 𝟙_ (Over (Sp R₁))) ⊤
    have hT : (Out.thetaLB A₁ (diagPull A₁ P₁) M (Out.overResι ⊤ ≫ lv₁ a)).IsLB := LB.isLB_linComb hD _ _
    obtain ⟨t, ht⟩ := (cls_eq_zero_iff hT).1 (by
      unfold Out.thetaLB at hT ⊢
      rw [cls_linComb hD, Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, neg_smul]
      have e : Out.translPt A₁ (Out.overResι ⊤ ≫ lv₁ a) = snd T A₁ ≫ ((toUnit A₁ ≫ lv₁ a) * 𝟙 A₁) := by
        rw [MonObj.comp_mul, Category.comp_id, comp_toUnit_assoc, Out.translPt, ← Hom.mul_def, ← Category.assoc,
          toUnit_unique (fst _ _ ≫ _) (toUnit _)]
      rw [e, Over.comp_left, pull_comp, ← map_zsmul, ← map_zsmul,
        ← GlobalTheory.SympDescent.translFixed_of_pair A₁ P₁ H₁ H₂.1 (lv₁ a) (tors a), add_neg_cancel])
    exact ⟨⊤, trivial, ⟨_, t, ht⟩, rfl⟩
  obtain ⟨φ, φ₂, pb, s₁', s₂', iso, hl⟩ := Hpb
  have hdi : LBIso (diagPull A P) ((diagPull A₁ P₁).pull φ) := GlobalTheory.SiegelPull.diag_iso ⟨s₁', s₂'⟩ iso
  have hL : (diagPull A P).IsLB := pull_isLB hPR _

  have inj : Function.Injective ((𝟙_ (Over (Sp R))).hom ≫ spMap R₁.subtype).appTop.hom := by
    have u₁ : (𝟙_ (Over (Sp R))).hom = 𝟙 _ := rfl
    rw [u₁, Category.id_comp]
    have k : ∀ z, (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((spMap R₁.subtype).appTop.hom z) =
        ((Scheme.ΓSpecIso (CommRingCat.of R₁)).hom.hom z : R) := fun z => by
      have e := congrArg (fun q => q.hom z) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom R₁.subtype))
      first
        | exact e
        | (simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom, Subring.subtype_apply] at e; exact e)
    intro x y hxy
    have h2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom hxy
    rw [k, k] at h2
    have h3 := congrArg (Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (Subtype.val_injective h2)
    simpa using h3
  intro a b
  obtain ⟨c, hc⟩ := CommutatorPairing.exists_weilIs globalFns_holds H₁.1 hD (th a) (th b)
  let X' : Over (Sp R₁) := Over.mk ((𝟙_ (Over (Sp R))).hom ≫ spMap R₁.subtype)
  have ex : ∀ a, (toUnit X' ≫ lv₁ a).left = (lv a).left ≫ φ := fun a => by
    rw [Over.comp_left, Over.toUnit_left, hl a]
    exact Category.assoc _ _ _
  have w := (weilIs_grpPullback_of_comm (Sp R₁) (Sp R) A₁ A (spMap R₁.subtype) φ (diagPull A₁ P₁) (diagPull A P)
    hD hL pb hdi (𝟙_ (Over (Sp R))) M (lv a) (lv b) (toUnit X' ≫ lv₁ a) (toUnit X' ≫ lv₁ b) _ (ex a) (ex b)).1 (Hs a b)
  have w' := CommPairing.weilIs_pull globalFns_holds H₁.1 hD (toUnit X') hc
  have q := CommutatorPairing.weilIs_unique globalFns_holds H₁.1 hD w' w
  have u₂ : (𝟙_ (Over (Sp R₁))).hom = 𝟙 _ := rfl
  have hinj : Function.Injective (Units.map (toUnit X').left.appTop.hom.toMonoidHom) := fun u v huv =>
    Units.ext (inj (by
      have := congrArg Units.val huv
      simp only [Units.coe_map, MonoidHom.coe_coe, Over.toUnit_left] at this
      exact this))
  have q₂ : Units.map (toUnit X').left.appTop.hom.toMonoidHom
      (Units.map ((𝟙_ (Over (Sp R₁))).hom ≫ s₁).appTop.hom.toMonoidHom (unitOn (ζ ^ (2 * stdForm a b).val))) =
      Units.map ((𝟙_ (Over (Sp R))).hom ≫ spMap R₁.subtype ≫ s₁).appTop.hom.toMonoidHom
        (unitOn (ζ ^ (2 * stdForm a b).val)) := by
    rw [← GlobalTheory.SympDescent.units_map_comp_appTop, Over.toUnit_left, u₂, Category.id_comp]
    rfl
  rw [← hinj (q.trans q₂.symm)]
  exact hc

end GlobalTheory.SympDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopFormFrameBaseCoordinatesAddVariablesEtale
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TopFrameEt

open GlobalTheory.TopForm

theorem appLE_comp_algX' {k : Type} [CommRing k] {X Y : Scheme.{0}} (p : X ⟶ Sp k) (q : Y ⟶ X)
    {U : X.Opens} {W : Y.Opens} (h : W ≤ q ⁻¹ᵁ U) :
    (q.appLE U W h).hom.comp (algX p U) = algX (q ≫ p) W := by
  have e := Scheme.Hom.appLE_comp_appLE q p ⊤ U W le_top h
  exact congrArg (fun f ↦ (CommRingCat.Hom.hom f).comp
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom) e

theorem exists_basis_of_exact {R M₁ M₂ M₃ ι ι' : Type} [CommRing R] [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃]
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) (hf : Function.Injective f) (hex : Function.Exact f g)
    (v : Module.Basis ι R M₁) (w : Module.Basis ι' R M₃) (u : ι' → M₂) (hu : ∀ a, g (u a) = w a) :
    ∃ b : Module.Basis (ι ⊕ ι') R M₂, ∀ j, b j = Sum.elim (fun i ↦ f (v i)) u j := by
  let S : ShortComplex (ModuleCat R) := ShortComplex.mk (ModuleCat.ofHom f) (ModuleCat.ofHom g)
    (by ext x; exact hex.apply_apply_eq_zero x)
  have hS : S.Exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).2 hex
  have hm : Mono S.f := (ModuleCat.mono_iff_injective _).2 hf
  let u' : ι ⊕ ι' → M₂ := Sum.elim (fun i ↦ f (v i)) u
  have hw : (S.g ∘ u' ∘ Sum.inr) = w := funext fun a ↦ hu a
  have hli : LinearIndependent R u' := by
    refine ModuleCat.linearIndependent_leftExact (S := S) (v := v) hS v.linearIndependent ?_ hm ?_
    · rw [hw]; exact w.linearIndependent
    · rfl
  have hsp : ⊤ ≤ Submodule.span R (Set.range u') := by
    refine ModuleCat.span_exact (S := S) (v := v) hS rfl (by rw [v.span_eq]) ?_
    rw [hw, w.span_eq]
  exact ⟨Module.Basis.mk hli hsp, fun j ↦ by simp [u']⟩

theorem isFrame_etale : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ X) (p' : Y ⟶ Sp k), q ≫ p = p' → ∀ (m D : ℕ), SmoothOfRelativeDimension m p → ∀ (ι : Type) (o : Fin D ≃ Fin m ⊕ ι) (U U' : X.Opens) (hU' : U' ≤ U), IsAffineOpen U → ∀ (W W' : Y.Opens) (hW' : W' ≤ W), IsAffineOpen W → IsAffineOpen W' → ∀ (hWU : W ≤ q ⁻¹ᵁ U), W' ≤ q ⁻¹ᵁ U' → ∀ (N : ι → Γ(Y, W)), (MvPolynomial.eval₂Hom (q.appLE U W hWU).hom N).Etale → ∀ (x : Fin m → Γ(X, U)), TopForm.IsFrame (TopForm.dOn p fun i => resG X hU' (x i)) → TopForm.IsFrame (TopForm.dOn p' fun a => resG Y hW' (Sum.elim (fun i => (q.appLE U W hWU).hom (x i)) N (o a))) := by
  intro k _ X Y p q p' hp m D _ ι o U U' hU' hU W W' hW' hW hW'a hWU hW'U' N hN x hx
  subst hp
  have hU'a : IsAffineOpen U' := hx.affine
  have hC := GlobalTheory.T.etale_mvPolynomial_eval2Hom_restrict_smaller_affines X Y q ι U U' hU' hU hU'a W W' hW' hW hW'a hWU hW'U' N hN
  obtain ⟨bR, hbR⟩ := GlobalTheory.T.exists_kaehlerBasis_differentials_of_topFormFrame k X p m ‹_› U' _ hx
  haveI : Finite ι := Finite.of_injective (fun a ↦ o.symm (Sum.inr a))
    (fun a b h ↦ Sum.inr_injective (o.symm.injective h))
  letI : Algebra k Γ(X, U') := (algX p U').toAlgebra
  letI : Algebra k Γ(Y, W') := (algX (q ≫ p) W').toAlgebra
  letI : Algebra Γ(X, U') Γ(Y, W') := (q.appLE U' W' hW'U').hom.toAlgebra
  haveI : IsScalarTower k Γ(X, U') Γ(Y, W') :=
    IsScalarTower.of_algebraMap_eq' (appLE_comp_algX' p q hW'U').symm
  let φ := MvPolynomial.eval₂Hom (q.appLE U' W' hW'U').hom (fun a ↦ resG Y hW' (N a))
  letI : Algebra (MvPolynomial ι Γ(X, U')) Γ(Y, W') := φ.toAlgebra
  haveI : IsScalarTower Γ(X, U') (MvPolynomial ι Γ(X, U')) Γ(Y, W') :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      change _ = φ (MvPolynomial.C r)
      simp [φ]; rfl
  haveI : Algebra.Etale (MvPolynomial ι Γ(X, U')) Γ(Y, W') := hC
  obtain ⟨⟨bT, hbT⟩, hsm⟩ := GlobalTheory.EtaleCoordJacobian.exists_basis_of_etale Γ(X, U') Γ(Y, W') ι
  haveI := hsm
  haveI : Subsingleton (Algebra.H1Cotangent Γ(X, U') Γ(Y, W')) :=
    Algebra.FormallySmooth.subsingleton_h1Cotangent
  have hinj : Function.Injective (KaehlerDifferential.mapBaseChange k Γ(X, U') Γ(Y, W')) := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨z, rfl⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange k Γ(X, U') Γ(Y, W') y).1 hy
    rw [Subsingleton.elim z 0, map_zero]
  obtain ⟨b, hb⟩ := exists_basis_of_exact
    (KaehlerDifferential.mapBaseChange k Γ(X, U') Γ(Y, W'))
    (KaehlerDifferential.map k Γ(X, U') Γ(Y, W') Γ(Y, W')) hinj
    (KaehlerDifferential.exact_mapBaseChange_map k Γ(X, U') Γ(Y, W'))
    (bR.baseChange Γ(Y, W')) bT (fun a ↦ KaehlerDifferential.D k Γ(Y, W') (resG Y hW' (N a)))
    (fun a ↦ by rw [hbT, KaehlerDifferential.map_D]; simp [φ, RingHom.algebraMap_toAlgebra])
  refine ⟨hW'a, isFreeGen_dForm _ (b.reindex o.symm) fun a ↦ ?_⟩
  rw [Module.Basis.reindex_apply, Equiv.symm_symm, hb]
  rcases o a with i | i
  · simp only [Sum.elim_inl, Module.Basis.baseChange_apply, KaehlerDifferential.mapBaseChange_tmul,
      one_smul, hbR, dFun, KaehlerDifferential.map_D]
    refine congrArg (KaehlerDifferential.D k Γ(Y, W')) ?_
    rw [RingHom.algebraMap_toAlgebra, GlobalTheory.LB.appLE_resG, GlobalTheory.LB.resG_appLE]
  · rfl

end GlobalTheory.TopFrameEt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetFrameEigenbasisBlockAtPointStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_det_frame_eigenbasis_block_at_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (k : TF.X.F.J) (S : Type) [CommRing S] (z : Sp S ⟶ Y₀ TF.X Z) (hU : ⊤ ≤ (z ≫ toBase TF Z) ⁻¹ᵁ U.1) (hk : ⊤ ≤ (z ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k) (hx : (z ≫ inc₀ TF.X Z) ≫ TF.X.π = z ≫ toBase TF Z) (σ : E →+* ℂ) (C : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S), (∀ i : Fin (Dw.mult σ), IsCombAtG TF.Y.t (z ≫ toBase TF Z) (fun j => spMap (dualMap (ev (z ≫ toBase TF Z) U.1 hU)) ≫ v (e ⟨σ, j⟩)) (C i) (tv (TF.X.F.vecAt k (z ≫ inc₀ TF.X Z) hk hx σ i)).left) → IsUnit C.det := by
  first | exact @GlobalTheory.LogPole.isUnit_det_of_isCombAtG_vecAt | exact GlobalTheory.LogPole.isUnit_det_of_isCombAtG_vecAt | (intros; apply GlobalTheory.LogPole.isUnit_det_of_isCombAtG_vecAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsoPreservesRigidificationAtOrigin
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem GlobalTheory.normW_origin : ∀ (V : Type) [CommRing V] [IsDomain V] (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G]
    (A : Over (Sp (FractionRing V))) [GrpObj A] [IsCommMonObj A] (θ : (Over.pullback (jK V)).obj G ⟶ A) [IsMonHom θ]
    (φ : A.left ⟶ G.left), θ.left ≫ φ = pullback.fst G.hom (jK V) →
    ∀ (he : eSec A ≫ φ = spMap (algebraMap V (FractionRing V)) ≫ eSec G)
    (LP : LB A.left) (LL LM : LB G.left), LP.IsLB → LL.IsLB → LM.IsLB →
    ∀ (rA : LB.Gen (LP.pull (eSec A))) (rL : LB.Gen (LL.pull (eSec G))) (rM : LB.Gen (LM.pull (eSec G)))
      (ψ : LB.Iso LP (LL.pull φ)) (e : LB.Iso LM LL) (w₀ : LB.Iso (LP.pull θ.left) (LM.pull (pullback.fst G.hom (jK V)))),
      (∀ (Z : Scheme.{0}) (r : Z ⟶ ((Over.pullback (jK V)).obj G).left) (z : Z) (i : LL.ι) (j : LM.ι) (k : LP.ι),
        pullback.fst G.hom (jK V) (r z) ∈ LL.U i → pullback.fst G.hom (jK V) (r z) ∈ LM.U j → θ.left (r z) ∈ LP.U k →
        gw w₀ r z j (fun _ => k) =
          (gm (r ≫ pullback.fst G.hom (jK V)) z (LL.U i ⊓ LM.U j) (e.s (i, j)))⁻¹ * gw ψ (r ≫ θ.left) z i k) →
      LB.Gen.Maps (LB.linCombIso ψ (K := PUnit) (fun _ => eSec A) (fun _ => 1)) rA
        (rigPullOf φ (spMap (algebraMap V (FractionRing V))) he LL rL) →
      LB.Gen.Maps (LB.linCombIso e (K := PUnit) (fun _ => eSec G) (fun _ => 1)) rM rL →
      ∀ (z : Sp (FractionRing V)) (JA : (Sp (FractionRing V) ⟶ A.left) → LP.ι) (JG : (Sp (FractionRing V) ⟶ G.left) → LM.ι),
        Good LP z JA → Good LM z JG →
        gw w₀ (eSec ((Over.pullback (jK V)).obj G)) z (JG (jK V ≫ eSec G)) (fun _ => JA (eSec A)) *
            val (L := LP) (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) rA (𝟙 _) z JA =
          val (L := LM) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) rM (jK V) z JG := by
  intro V _ _ G _ _ A _ _ θ _ φ hφ he LP LL LM hP hL hM rA rL rM ψ e w₀ hpt hψ hε z JA JG gA gG
  have h1 : eSec ((Over.pullback (jK V)).obj G) ≫ θ.left = eSec A := by
    show η[(Over.pullback (jK V)).obj G].left ≫ θ.left = η[A].left
    rw [← Over.comp_left, IsMonHom.one_hom]
  have h2 : eSec ((Over.pullback (jK V)).obj G) ≫ pullback.fst G.hom (jK V) = jK V ≫ eSec G := by
    rw [← hφ, ← Category.assoc, h1, he]
  have p1 : θ.left (eSec ((Over.pullback (jK V)).obj G) z) = eSec A z := congrArg (fun f => f z) h1
  have p2 : pullback.fst G.hom (jK V) (eSec ((Over.pullback (jK V)).obj G) z) = eSec G (jK V z) :=
    congrArg (fun f => f z) h2
  have p3 : φ (eSec A z) = eSec G (jK V z) := congrArg (fun f => f z) he
  have hA : eSec A z ∈ LP.U (JA (eSec A)) := gA (eSec A)
  have hG : eSec G (jK V z) ∈ LM.U (JG (jK V ≫ eSec G)) := gG (jK V ≫ eSec G)
  obtain ⟨i, hi⟩ := exists_chart hL (eSec G (jK V z))

  have s2 := hpt _ (eSec ((Over.pullback (jK V)).obj G)) z i (JG (jK V ≫ eSec G)) (JA (eSec A))
    (by rw [p2]; exact hi) (by rw [p2]; exact hG) (by rw [p1]; exact hA)
  rw [h2, h1] at s2

  have s3 := (maps_iff ψ (fun _ : PUnit => eSec A) (fun _ => eSec G) (fun _ => 1) rA rL
    (spMap (algebraMap V (FractionRing V))) _ (rigPull_le φ _ he LL) (fun _ => rfl)).1 hψ
    _ (𝟙 _) z (fun _ => i) (fun _ => JA (eSec A))
    (fun _ => by show φ (eSec A z) ∈ _; rw [p3]; exact hi) (fun _ => hA)
  simp only [Category.id_comp, Fintype.prod_unique, zpow_one] at s3

  have hm : jK V z ∈ (LB.wchart LL (fun _ : PUnit => eSec G) (fun _ => i) ⊓
      LB.wchart LM (fun _ : PUnit => eSec G) (fun _ => JG (jK V ≫ eSec G)) : (Sp V).Opens) := by
    exact ⟨Set.mem_iInter.2 fun _ => hi, Set.mem_iInter.2 fun _ => hG⟩
  have s4 := congrArg (gm (jK V) z _) (hε (fun _ => i, fun _ => JG (jK V ≫ eSec G)))
  have eU : gm (jK V) z _ ((LB.linCombIso e (K := PUnit) (fun _ => eSec G) (fun _ => 1)).s
      (fun _ => i, fun _ => JG (jK V ≫ eSec G))) =
      gm (jK V ≫ eSec G) z (LL.U i ⊓ LM.U (JG (jK V ≫ eSec G))) (e.s (i, JG (jK V ≫ eSec G))) := by
    show gm _ z _ (∏ _k : PUnit, (res _ (pullU (eSec G) _ (e.s (i, JG (jK V ≫ eSec G))))) ^ (1 : ℤ)) = _
    rw [Fintype.prod_unique, zpow_one]
    exact (gm_res _ z _ hm _).trans (gm_pull _ _ z _ (show eSec G (jK V z) ∈ LL.U i ⊓ LM.U (JG (jK V ≫ eSec G)) from ⟨hi, hG⟩) _)
  have s4' := (gm_res _ z _ hm _).symm.trans (s4.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) eU (gm_res _ z _ hm _))))
  rw [val_of rA (𝟙 _) z JA (fun _ => JA (eSec A)) (fun _ => by rw [Category.id_comp]),
    val_of rM (jK V) z JG (fun _ => JG (jK V ≫ eSec G)) (fun _ => rfl), s2, _root_.mul_assoc, ← s3]
  exact inv_mul_eq_of_eq_mul s4'
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyFiniteFlat
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SurjHomFlat

open GlobalTheory GlobalTheory.SurjIsogeny GlobalTheory.IsogenyModel

theorem finite_flat :
    ∀ (A X : Over (Sp ℂ)) [GrpObj A] [GrpObj X] (g : ℕ), IsAbelianScheme A → IsAbelianScheme X →
    SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g X.hom →
    ∀ (ψ : A ⟶ X) [IsMonHom ψ] [Surjective ψ.left], IsFinite ψ.left ∧ Flat ψ.left := by
  intro A X _ _ g hA hX hgA hgX ψ _ _
  have := hX.proper
  have := hA.proper
  have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ X.hom hX.smooth
    hX.geomConnected
  have : IsIntegral X.left := GeometricallyIntegral.isIntegral_of_subsingleton X.hom
  have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ A.hom
    hA.smooth hA.geomConnected
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  have : IsProper (ψ.left ≫ X.hom) := by rw [Over.w]; infer_instance
  have : IsProper ψ.left := IsProper.of_comp ψ.left X.hom
  have hA' : SmoothOfRelativeDimension g (ψ.left ≫ X.hom) := by rw [Over.w]; exact hgA
  obtain ⟨a, ha⟩ := ψ.left.surjective (genericPoint X.left)
  have : LocallyQuasiFinite ψ.left := by
    refine locallyQuasiFinite_of_finite_fibre ψ a ((Set.finite_singleton (genericPoint _)).subset ?_)
    intro x hx
    exact eq_genericPoint_of_apply_eq ψ.left X.hom hgX hA' (ha ▸ hx)
  have hf : IsFinite ψ.left := .of_isProper_of_locallyQuasiFinite _
  refine ⟨hf, ?_⟩
  exact GlobalTheory.SS.flat_of_isDominant_grpHom ℂ A X ψ

end GlobalTheory.SurjHomFlat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetGroupMorphismBaseChange
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatJet

theorem JetRing.π_algebraMap {R : Type} [CommRing R] {I : Type} [Fintype I] {n : ℕ} (J : JetRing R I n) (r : R) :
    J.π (algebraMap R J.B r) = r := by
  rw [J.π_eq, Algebra.algebraMap_eq_smul_one, ← J.one, map_smul, J.b.repr_self]
  simp

theorem isBC_jetRing : GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (R : Type) [CommRing R] [IsDomain R] [CharZero R]
    [IsLocalRing R] (I : Type) [Fintype I] (n : ℕ) (J : JetRing R I n) (X : Obj F 𝔠 (Sp R))
    (m : GrpMor (dp0 R) (𝟙 _) X.A J.κ (spMap J.π) X.A (algebraMap R J.B) (𝟙 _) (Over.Hom.left (𝟙 X.A))), m.IsBC := by
  intro _ H _ F _ _ _ 𝔠 R _ _ _ _ I _ n J X m
  have e : (𝟙 _ : Sp R ⟶ Sp R) = spMap (RingHom.id R) := (Cris.spMap_id R).symm
  have h := (GlobalTheory.CrysConn.isGrpPullback_refl X.A).congr e rfl
  have key : ∀ (t : Sp R ⟶ Sp R), t = spMap (RingHom.id R) →
      ∀ m : GrpMor (dp0 R) t X.A J.κ (spMap J.π) X.A (algebraMap R J.B) (𝟙 _) (Over.Hom.left (𝟙 X.A)), m.IsBC := by
    rintro _ rfl m
    exact GlobalTheory.CrysConn.isBC_of_lift H X.ab X.dim (isDPNilpotent_bot R) Function.surjective_id
      ((RingHom.injective_iff_ker_eq_bot _).1 Function.injective_id) h J.nil
      (fun r ↦ ⟨_, J.π_algebraMap r⟩) rfl m (GlobalTheory.CrysConn.isGrpPullback_refl X.A)
  exact key _ e m

end GlobalTheory.LatJet
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetRingProdEqFactorialSmul
section
open GlobalTheory.LatJet
open scoped Classical

namespace GlobalTheory.LatJet

theorem count_cons_eq_single_add {I : Type} [DecidableEq I] (a : I) (l : List I) (i : I) :
    (a :: l).count i = (Pi.single a 1 : I → ℕ) i + l.count i := by
  rw [List.count_cons]
  by_cases h : i = a
  · subst h; simp [add_comm]
  · have h' : ¬ a = i := fun e => h e.symm
    simp [h, h', Pi.single_apply]

theorem prod_map_t_eq_smul_b : ∀ {R : Type} [CommRing R] {I : Type} [Fintype I] {n : ℕ} (J : JetRing R I n) (l : List I)
    (hc : ∑ i, l.count i ≤ n + 1),
    (l.map J.t).prod = ((∏ i, (l.count i).factorial : ℕ) : R) • J.b ⟨fun i => l.count i, hc⟩ := by
  intro R _ I _ n J l
  induction l with
  | nil =>
    intro hc
    have : (⟨fun i => List.count i ([] : List I), hc⟩ : Idx I n) = ⟨0, by simp⟩ := by
      apply Subtype.ext; funext i; simp
    rw [this, J.one]; simp
  | cons a l ih =>
    intro hc
    have hc' : ∑ i, l.count i ≤ n + 1 :=
      le_trans (Finset.sum_le_sum fun i _ => List.count_le_count_cons ..) hc
    have hsum : ∑ i, ((Pi.single a 1 : I → ℕ) + fun i => l.count i) i ≤ n + 1 := by
      refine le_of_eq_of_le ?_ hc
      exact Finset.sum_congr rfl fun i _ => (count_cons_eq_single_add a l i).symm
    rw [List.map_cons, List.prod_cons, ih hc', mul_smul_comm, JetRing.t, J.mul, dif_pos hsum,
      ← Nat.cast_smul_eq_nsmul R, smul_smul, ← Nat.cast_mul]
    have hidx : (⟨(Pi.single a 1 : I → ℕ) + fun i => l.count i, hsum⟩ : Idx I n) = ⟨fun i => (a :: l).count i, hc⟩ := by
      apply Subtype.ext; funext i; exact (count_cons_eq_single_add a l i).symm
    have hprod : (∏ i, ((a :: l).count i).factorial) =
        (∏ i, ((Pi.single a 1 : I → ℕ) i + l.count i).choose ((Pi.single a 1 : I → ℕ) i)) * ∏ i, (l.count i).factorial := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [count_cons_eq_single_add]
      by_cases h : i = a
      · subst h; simp [Nat.factorial_succ, add_comm]
      · simp [Pi.single_apply, h]
    rw [hidx, hprod, mul_comm]

end GlobalTheory.LatJet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftBaseChangeBijectiveLinearEquivSquareUnivStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftBaseChange_bijective_linearEquiv_square_univ : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (M : Type 1) [AddCommGroup M] [Module R M] (N : Type) [AddCommGroup N] [Module R N] (M' : Type 1) [AddCommGroup M'] [Module R' M'] (N' : Type) [AddCommGroup N'] [Module R' N'] (e : M →ₗ[R] N) (e' : M' →ₗ[R'] N') (f : M →ₛₗ[algebraMap R R'] M') (g : N →ₛₗ[algebraMap R R'] N'), Function.Bijective e → Function.Bijective e' → (∀ x, e' (f x) = g (e x)) → (Function.Bijective (liftSemi f) ↔ Function.Bijective (liftSemi g)) := by
  first | exact @GlobalTheory.BaseChangeIso.main | exact GlobalTheory.BaseChangeIso.main | (intros; apply GlobalTheory.BaseChangeIso.main <;> assumption)
end

