import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2687
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionToG
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUOfIntegralTorsionPoint
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0081
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2572
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2669
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1207
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1186
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1117
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1260
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionCellFlAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2782
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2817
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2790
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2779
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2736
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2826
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2250
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExtensionSecPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0061
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2684
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2827
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2842
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsLastTail
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusModel GlobalTheory.ConstLin GlobalTheory.FinitePartGeneric

noncomputable section
namespace GlobalTheory.ToricTorsionSpec

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (k : ℕ), 1 ≤ k → ∀ τ : Multiplicative D.toPre.X →* Rˣ, τ ^ k = 1 → ∃ s : 𝟙_ (Over (Sp R)) ⟶ G, s ^ k = 1 ∧ ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ (ev₀ : R →+* V), IsLocalHom ev₀ → ∀ (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'] (bc : G' ≅ (Over.pullback (specOf ev₀)).obj G), IsMonHom bc.hom → ∀ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (hD : IsPullDeg ev₀ D.toPre D'.toPre) (U' : Unif (maximalIdeal V) D' A' G'), IsPullUnif ev₀ hD bc U U' → ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing V) K] (τ' : Multiplicative D'.toPre.X →* Kˣ), (∀ χ', ((τ' χ' : Kˣ) : K) = algebraMap (FractionRing V) K (algebraMap V (FractionRing V) (ev₀ ((τ (Multiplicative.ofAdd (hD.xe (Multiplicative.toAdd χ'))) : Rˣ) : R)))) → ∀ (q : QkPt D'.toPre K k) (x' : TFK (R := V) K ⟶ A'.A), q.y = 0 → GlobalTheory.UT.IsTor τ' q.g → QkToAkU U'.toUnifPre K k q x' → x'.left ≫ genMap U' ≫ bc.hom.left ≫ pullback.fst G.hom (specOf ev₀) = spMap ((algebraMap (FractionRing V) K).comp ((algebraMap V (FractionRing V)).comp ev₀)) ≫ s.left := by
  intro R _ _ _ hB G _ _ hG D A U k hk τ hτ
  obtain ⟨hR, hC⟩ := hB
  haveI := hC
  obtain ⟨N, g₀, x₀, hfin, -, -, hU, htors, hform⟩ := GlobalTheory.ToricTorsionSecUnif.exists_torsion_toG R hR G D A U k hk
  let u : D.toPre.X →+ Additive Γ((𝟙_ (Over (Sp R))).left, ⊤)ˣ :=
    AddMonoidHom.mk' (fun χ => Additive.ofMul (unitOn (τ (Multiplicative.ofAdd χ)))) (fun χ χ' => by
      simp only [ofAdd_add, map_mul, unitOn, ofMul_mul])
  have hu : k • u = 0 := by
    refine AddMonoidHom.ext fun χ => Additive.toMul.injective ?_
    have e : (τ (Multiplicative.ofAdd χ)) ^ k = 1 := by rw [← MonoidHom.pow_apply, hτ, MonoidHom.one_apply]
    simp only [u, AddMonoidHom.nsmul_apply, AddMonoidHom.mk'_apply, toMul_nsmul, toMul_ofMul, unitOn, ← map_pow, e,
      map_one, AddMonoidHom.zero_apply, toMul_zero]
  obtain ⟨gT, hgT⟩ := GlobalTheory.TorusTorsion.exists_torusPt (D := D.toPre) (T := 𝟙_ (Over (Sp R))) u
  obtain ⟨g', h₁, h₂⟩ := GlobalTheory.TorusTorsion.exists_nsmul_zero k u hu hgT
  obtain ⟨h, hh, -⟩ := hU _ _ ⟨g', h₁, h₂⟩
  refine ⟨h ≫ x₀, by rw [← MonObj.comp_pow, htors, MonObj.comp_one], ?_⟩
  intro V _ _ _ _ hVc ev₀ hev G' _ _ bc hbc D' A' hD U' hUU' K _ _ _ τ' hτ' q x' hq htor hqx'
  have hV : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hVc⟩
  have hG' : IsSemiAbelian G' := GlobalTheory.isSemiAbelian_of_grpIso bc (IsSemiAbelian.pullback (specOf ev₀) G hG)
  have hL := firstFiveLaws
  have hL2 := abelianSchemeLaws_all
  let ξ : Sp V ⟶ N.left := spMap ev₀ ≫ h.left
  have hh' : ξ ≫ N.hom = (𝟙_ (Over (Sp V))).hom ≫ spMap ev₀ := by
    simp only [ξ, Category.assoc, Over.w h]
    rfl
  obtain ⟨gp, hgp⟩ : ∃ gp : GtPt D'.toPre (𝟙_ (Over (Sp V))), ConstLin.Thru hD.w hD.xe (T' := 𝟙_ _) ξ g₀ gp :=
    ConstPoint.exists_gtPt_through hL.1.globalFns (pull_grp hD) hD.w_gen hD.xe.toAddMonoidHom hD.c_pr
      (T' := 𝟙_ _) ξ hh' g₀
  let x₁' : 𝟙_ (Over (Sp V)) ⟶ (Over.pullback (specOf ev₀)).obj G :=
    Over.homMk (pullback.lift (ξ ≫ x₀.left) (𝟙_ (Over (Sp V))).hom (by rw [Category.assoc, Over.w]; exact hh'))
      (pullback.lift_snd _ _ _)
  let x₁ : 𝟙_ (Over (Sp V)) ⟶ G' := x₁' ≫ bc.inv
  have e₁ : x₁'.left ≫ pullback.fst G.hom (specOf ev₀) = ξ ≫ x₀.left := pullback.lift_fst _ _ _
  have e₂ : x₁.left ≫ bc.hom.left ≫ pullback.fst G.hom (specOf ev₀) = ξ ≫ x₀.left := by
    rw [Over.comp_left, Category.assoc, ← Category.assoc bc.inv.left, ← Over.comp_left, Iso.inv_hom_id, Over.id_left,
      Category.id_comp, e₁]
  have gG := isGrpPullback_pullback G (spMap ev₀)
  have hk₁' : x₁' ^ k = 1 := ConstGrp.push_injective gG _ (by
    let ρ : Over.mk ((𝟙_ (Over (Sp V))).hom ≫ spMap ev₀) ⟶ N := Over.homMk ξ hh'
    have e : pushHom gG _ x₁' = ρ ≫ x₀ := Over.OverMorphism.ext e₁
    rw [map_pow, map_one, e, ← MonObj.comp_pow, htors, MonObj.comp_one])
  haveI : IsMonHom bc.inv := inferInstance
  have hk₁ : x₁ ^ k = 1 := by
    show (x₁' ≫ bc.inv) ^ k = 1
    rw [← MonObj.pow_comp, hk₁', MonObj.one_comp]
  have hp := isPointOf_thru hUU' hgp e₂ ((TorsionFormCompare.formalEq_iff _ _ _).1 hform)
  have gpg := pull_grp hD
  have hb : gp.b = 1 := Over.OverMorphism.ext (gpg.1.hom_ext (((hgp 0).1 2).trans (Eq.trans ?_ ((hgp 0).1 3).symm))
    ((Over.w _).trans (Over.w _).symm))
  swap
  · show ξ ≫ g₀.b.left = ξ ≫ (1 : N ⟶ D.toPre.P.A).left
    have e1 : h.left ≫ g₀.b.left = h.left ≫ (1 : N ⟶ D.toPre.P.A).left := by
      have t1 : gT.b.left = h.left ≫ g₀.b.left := hh.1
      have t2 : gT.b = 1 := (hgT 0).1
      have t3 : h ≫ (1 : N ⟶ D.toPre.P.A) = 1 := MonObj.comp_one h
      rw [← t1, t2, ← t3]
      rfl
    simp only [ξ, Category.assoc, e1]
  let uV : D'.toPre.X → Γ((𝟙_ (Over (Sp V))).left, ⊤)ˣ := fun y =>
    unitOn (Units.map ev₀.toMonoidHom (τ (Multiplicative.ofAdd (hD.xe y))))
  have hgpT : ∀ y, TorusVal gp y (uV y) := by
    intro y
    refine ⟨hb, corr_of_val D'.toPre.P.isLB fun z J' hJ' => ?_⟩
    obtain ⟨J, hJ⟩ := ConstFam.exists_good' D.toPre.P.isLB z
    have v := hgp.val_id y z hJ hJ'
    rw [GlobalTheory.TorusTorsion.val_unitGen _ _ hJ']
    generalize Geo.Tor.val (gp.s y) (𝟙 _) z J' = s at v ⊢
    rw [hb, _root_.mul_one, inv_mul_cancel, _root_.one_mul, mul_inv_cancel, _root_.one_mul] at v
    rw [← v]
    have c := val_corr hJ (hh.2 (hD.xe y)) (spMap ev₀)
    have c2 := GlobalTheory.TorusTorsion.TorusVal.val_eq (hgT (hD.xe y)) (spMap ev₀) hJ
    have c3 : Geo.Tor.val (g₀.s (hD.xe y)) ξ z J = gm (spMap ev₀) z ⊤ (Additive.toMul (u (hD.xe y))) := by
      first
      | exact ((val_pull hJ _ _ _).symm.trans (c.symm.trans c2))
      | exact ((val_pull hJ _ _ _).symm.trans (c.trans c2))
      | exact (c.symm.trans c2)
      | exact (c.trans c2)
    rw [c3]
    refine Units.ext ?_
    rw [gm_val _ z ⊤ trivial, gm_val _ z ⊤ trivial]
    have e := GlobalTheory.ToricTorsionSec.appTop_unitOn ev₀ (τ (Multiplicative.ofAdd (hD.xe y)))
    first
    | (simp only [uV]; rw [← e]; rfl)
    | (rw [show (uV y).val = _ from e.symm]; rfl)
    | (erw [← e]; rfl)
  let fK : V →+* K := (algebraMap (FractionRing V) K).comp (algebraMap V (FractionRing V))
  let uK : D'.toPre.X →+ Additive Γ((Over.mk (spMap fK)).left, ⊤)ˣ :=
    AddMonoidHom.mk' (fun χ => Additive.ofMul (unitOn (τ' (Multiplicative.ofAdd χ)))) (fun χ χ' => by
      simp only [ofAdd_add, map_mul, unitOn, ofMul_mul])
  obtain ⟨gK, hgK⟩ := GlobalTheory.TorusTorsion.exists_torusPt (D := D'.toPre) (T := Over.mk (spMap fK)) uK
  have hpK := GlobalTheory.ToricTorsionSec.isPullF_torusPt τ' gK hgK q.g htor
  let ρ : Over.mk (spMap fK) ⟶ 𝟙_ (Over (Sp V)) := toUnit _
  have hρ : GtPt.IsPull ρ.left gp gK := GlobalTheory.TorusTorsion.isPull_of_units ρ hgpT hgK fun χ => by
    refine (GlobalTheory.ToricTorsionSec.appTop_unitOn fK _).trans ?_
    congr 2
    refine Units.ext ?_
    have := hτ' (Multiplicative.ofAdd χ)
    simp only [toAdd_ofAdd] at this
    exact this.symm
  have hpF := GlobalTheory.ToricTorsionSec.isPullF_trans hρ hpK
  have hTF : (toUnit (TF (R := V) K)).left = 𝟙 _ ≫ ρ.left := by
    rw [Category.id_comp]
    have e₁ := Over.w (toUnit (TF (R := V) K))
    have e₂ := Over.w ρ
    simp only [Over.mk_hom] at e₁ e₂
    rw [← Category.comp_id (toUnit (TF (R := V) K)).left, ← Category.comp_id ρ.left]
    exact e₁.trans ((GlobalTheory.ToricTorsionSec.spMap_comp _ _).symm.trans e₂.symm)
  have hpF' : GtPt.IsPullF K (toUnit (TF (R := V) K)).left gp q.g := by
    rw [hTF]; exact hpF
  let yK : TFK (R := V) K ⟶ (Over.pullback (jK V)).obj G' :=
    Over.homMk (pullback.lift ((toUnit (TF (R := V) K)).left ≫ x₁.left) (jFK (R := V) K)
      (by rw [Category.assoc, Over.w x₁]; exact Over.w (toUnit (TF (R := V) K)))) (pullback.lift_snd _ _ _)
  let xF : TFK (R := V) K ⟶ A'.A := yK ≫ U'.gen.hom
  have hxF : xF.left ≫ U'.gen.inv.left ≫ pullback.fst G'.hom (jK V) = (toUnit (TF (R := V) K) ≫ x₁).left := by
    rw [← Category.assoc, ← Over.comp_left, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact pullback.lift_fst _ _ _
  have hQ := qkToAkU_of_integral_torsion hL.1 V (maximalIdeal V) hV (maximalIdeal.isMaximal V).ne_top D' A' G' U' k hk
    x₁ gp hk₁ (fun e => ?_) K q xF hq hpF' hxF
  · have hEq := GlobalTheory.TorsionImage.qkToAkU_unique hL2.1 hL2.2 V (maximalIdeal V) hV D' A' G' hG' U' K k hk q x' xF hqx' hQ
    subst hEq
    have hρl : ρ.left = spMap fK := by
      have e₂ := Over.w ρ
      rw [← Category.comp_id ρ.left]
      exact e₂
    show xF.left ≫ (U'.gen.inv.left ≫ pullback.fst G'.hom (jK V)) ≫ bc.hom.left ≫ pullback.fst G.hom (specOf ev₀) = _
    rw [← Category.assoc, hxF, Over.comp_left, Category.assoc, e₂, hTF, Category.id_comp, hρl, Over.comp_left]
    simp only [ξ, ← Category.assoc]
    congr 1
    rw [← GlobalTheory.ToricTorsionSec.spMap_comp]
  · let xe : Over.mk (thick V (maximalIdeal V) e) ⟶ (Over.map (thick V (maximalIdeal V) e)).obj
        (thickObj V (maximalIdeal V) e G') :=
      Over.homMk (pullback.lift (toUnit (Over.mk (thick V (maximalIdeal V) e)) ≫ x₁).left (𝟙 _)
        ((Over.w _).trans (Category.id_comp _).symm))
        (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (pullback.lift_snd _ _ _))).trans (Category.id_comp _))
    have hxe : xe ≫ fstG _ e _ = toUnit _ ≫ x₁ := Over.OverMorphism.ext (pullback.lift_fst _ _ _)
    have c := hp e _ (toUnit (Over.mk (thick V (maximalIdeal V) e))).left xe.left (congrArg (·.left) hxe)
    exact ⟨xe, hxe, Over.OverMorphism.ext c.1, c.2⟩

end GlobalTheory.ToricTorsionSpec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveAndExistsFrameMulUpper
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.FlagZ

set_option autoImplicit false
noncomputable section

open GlobalTheory.Twist (resM app_resM)
open GlobalTheory.QCoh (appLinear appLinear_apply)

namespace GlobalTheory.FlagZ.Loc

theorem isUnit_submatrix_castLE_of_upper {R : Type*} [CommRing R] {N l : ℕ} (hl : l ≤ N)
    (b : Matrix (Fin N) (Fin N) R) (hb : ∀ i j : Fin N, j < i → b i j = 0) (hu : IsUnit b) :
    IsUnit (b.submatrix (Fin.castLE hl) (Fin.castLE hl)) := by
  have h1 : b.BlockTriangular id := fun i j h => hb i j h
  have h2 : (b.submatrix (Fin.castLE hl) (Fin.castLE hl)).BlockTriangular id :=
    fun i j h => hb _ _ h
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_of_isUpperTriangular h1,
    IsUnit.prod_univ_iff] at hu
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_of_isUpperTriangular h2, IsUnit.prod_univ_iff]
  exact fun i => hu _

theorem injective_app_of_frame {X : Scheme.{0}} {F G : X.Modules} (φ : F ⟶ G) {V : X.Opens}
    {m n : Type} [Fintype m] [Fintype n] {e : m → Γ(F, V)} {c : n → Γ(G, V)} (σ : m → n)
    (hσ : Function.Injective σ) (he : VB.IsFrame e) (hc : VB.IsFrame c)
    (h : ∀ k, φ.app V (e k) = c (σ k)) (W : X.Opens) (hW : W ≤ V) :
    Function.Injective (φ.app W) := by
  have hli : LinearIndependent Γ(X, W) fun k => resM G hW (c (σ k)) :=
    (Fintype.linearIndependent_iff.2 fun a ha =>
      congrFun ((injective_iff_map_eq_zero _).1 (hc W hW).1 a
        ((Fintype.linearCombination_apply _ _ _).trans ha))).comp σ hσ
  change Function.Injective (appLinear φ W)
  refine (injective_iff_map_eq_zero _).2 fun t ht => ?_
  obtain ⟨a, rfl⟩ := (he W hW).2 t
  simp only [Fintype.linearCombination_apply, map_sum, map_smul, appLinear_apply, app_resM,
    h] at ht
  have ha : a = 0 := funext (Fintype.linearIndependent_iff.1 hli a ht)
  rw [ha, map_zero]

theorem colSecOn_mul {N : ℕ} {T : Scheme.{0}} (x : T ⟶ Sp ℤ) (V : T.Opens)
    (C b : Matrix (Fin N) (Fin N) Γ(T, V)) (j : Fin N) :
    colSecOn x V (C * b) j = ∑ k, b k j • colSecOn x V C k := by
  simp only [colSecOn, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

theorem injective_and_exists_frame_mul_upper : ∀ {T : Scheme.{0}} (x : T ⟶ Sp ℤ) {N : ℕ} {F' : T.Modules}
    (φ : F' ⟶ (Scheme.Modules.pullback x).obj (GlobalTheory.FlagZ.Taut.stdE N)) (V : T.Opens) (l : Fin (N + 1))
    (e : Fin l → Γ(F', V)) (C : GL (Fin N) Γ(T, V)) (b : Matrix (Fin N) (Fin N) Γ(T, V)),
    GlobalTheory.VB.IsFrame e → (∀ k, φ.app V (e k) = GlobalTheory.FlagZ.Loc.colSecOn x V C.1 (Fin.castLE l.is_le k)) →
    (∀ i j : Fin N, j < i → b i j = 0) → IsUnit b →
    (∀ W : T.Opens, W ≤ V → Function.Injective (φ.app W)) ∧
      ∃ s : Fin l → Γ(F', V), GlobalTheory.VB.IsFrame s ∧
        ∀ j, φ.app V (s j) = GlobalTheory.FlagZ.Loc.colSecOn x V (C.1 * b) (Fin.castLE l.is_le j) := by
  intro T x N F' φ V l e C b he hφ hb hu
  have hc : VB.IsFrame (colSecOn x V C.1) :=
    Univ.isFrame_sum_smul_of_isUnit (isFrame_stdSec x V) C.1 C.isUnit
  refine ⟨injective_app_of_frame φ _ (Fin.castLE_injective l.is_le) he hc hφ,
    _, Univ.isFrame_sum_smul_of_isUnit he _ (isUnit_submatrix_castLE_of_upper l.is_le b hb hu),
    fun j => ?_⟩
  rw [colSecOn_mul, ← appLinear_apply]
  simp only [map_sum, map_smul, appLinear_apply, hφ, Matrix.submatrix_apply]
  refine Finset.sum_of_injOn (Fin.castLE l.is_le) (Fin.castLE_injective _).injOn
    (fun _ _ => Finset.mem_univ _) (fun k _ hk => ?_) (fun _ _ => rfl)
  rw [hb, zero_smul]
  by_contra hlt
  have hk' : (k : ℕ) < l := lt_of_le_of_lt (Fin.le_def.1 (not_lt.1 hlt)) j.2
  exact hk ⟨⟨k, hk'⟩, Finset.mem_coe.2 (Finset.mem_univ _), rfl⟩

end GlobalTheory.FlagZ.Loc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegerActionExtendsSemiAbelianThetaModel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

theorem GlobalTheory.UPoinc.exists_endo_of_generic {Z W : Scheme.{0}} [IsIntegral W] {G : Over Z} [GrpObj G] {G₀ : Over W}
    [GrpObj G₀] (hab : IsAbelianScheme G₀) {q : W ⟶ Z} {Φ : G₀.left ⟶ G.left} (hΦ : IsGrpPullback G₀ G q Φ)
    {Ω : Type} [Field Ω] (pt : Sp Ω ⟶ W) (hd : Dense (Set.range pt)) (m : Sp Ω ⟶ Z) (hm : pt ≫ q = m)
    (hendo : ∀ f : (Over.pullback m).obj G ⟶ (Over.pullback m).obj G, IsMonHom f →
      ∃! F : G ⟶ G, IsMonHom F ∧ (Over.pullback m).map F = f)
    (f₀ : G₀ ⟶ G₀) (hf₀ : IsMonHom f₀) : ∃ F : G ⟶ G, IsMonHom F ∧ Φ ≫ F.left = f₀.left ≫ Φ := by
  have hgen := isGrpPullback_pullback G m
  have wk : pullback.fst G.hom m ≫ G.hom = (pullback.snd G.hom m ≫ pt) ≫ q := by
    rw [Category.assoc, hm, pullback.condition]
  let k : pullback G.hom m ⟶ G₀.left := hΦ.1.lift (pullback.fst _ _) (pullback.snd _ _ ≫ pt) wk
  have hk : IsGrpPullback ((Over.pullback m).obj G) G₀ pt k :=
    hΦ.cancel (hgen.congr hm.symm (hΦ.1.lift_fst _ _ _).symm) (hΦ.1.lift_snd _ _ _)
  obtain ⟨e, he, hek⟩ := GlobalTheory.Ex.Arch.exists_pull_endo hk f₀ hf₀
  obtain ⟨F, ⟨hF, hFe⟩, -⟩ := hendo e he
  obtain ⟨F₀, hF₀, hF₀e⟩ := GlobalTheory.Ex.Arch.exists_pull_endo hΦ F hF
  have wθ : (pullback.fst G₀.hom pt ≫ Φ) ≫ G.hom = pullback.snd G₀.hom pt ≫ m := by
    rw [Category.assoc, hΦ.1.w, ← Category.assoc, pullback.condition, Category.assoc, hm]
  let θ : pullback G₀.hom pt ⟶ pullback G.hom m := pullback.lift _ _ wθ
  have hθk : θ ≫ k = pullback.fst _ _ := by
    apply hΦ.1.hom_ext
    · rw [Category.assoc, hΦ.1.lift_fst, pullback.lift_fst]
    · rw [Category.assoc, hΦ.1.lift_snd, ← Category.assoc, pullback.lift_snd, pullback.condition]
  have hFm : ((Over.pullback m).map F).left ≫ pullback.fst G.hom m = pullback.fst G.hom m ≫ F.left := by
    first | exact pullback.lift_fst _ _ _ | (simp [Over.pullback, pullback.map]) | (erw [pullback.lift_fst])
  have key : F₀ = f₀ := by
    apply GlobalTheory.T.abelianScheme_endomorphism_ext_of_dense_point W G₀ hab Ω pt hd
    apply hΦ.1.hom_ext
    · calc (pullback.fst G₀.hom pt ≫ F₀.left) ≫ Φ = pullback.fst G₀.hom pt ≫ Φ ≫ F.left := by
            rw [Category.assoc, hF₀e]
        _ = θ ≫ pullback.fst G.hom m ≫ F.left := by rw [← Category.assoc θ, pullback.lift_fst, Category.assoc]
        _ = θ ≫ e.left ≫ pullback.fst G.hom m := by rw [← hFm, hFe]
        _ = θ ≫ e.left ≫ k ≫ Φ := by rw [hΦ.1.lift_fst]
        _ = θ ≫ k ≫ f₀.left ≫ Φ := by rw [← Category.assoc e.left, hek, Category.assoc]
        _ = (pullback.fst G₀.hom pt ≫ f₀.left) ≫ Φ := by rw [← Category.assoc θ, hθk, Category.assoc]
    · rw [Category.assoc, Category.assoc, Over.w F₀, Over.w f₀]
  exact ⟨F, hF, by rw [← hF₀e, key]⟩

theorem GlobalTheory.UPoinc.act_extends_ratModel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (M : RatModel X₁.o₁ X₁.Ω₁) (U₀ : M.Z.Opens) (EE : M.Lat X₁.S.J) (out : ZHOut X₁.ρ M U₀ EE), X₁.S.admitted M U₀ → ∃ f : 𝓞 E → (out.G ⟶ out.G), (∀ a, IsMonHom (f a)) ∧ ∀ (K : Type) [Field K] (ξ₀ : Sp K ⟶ U₀.toScheme) (y : Sp K ⟶ Xo.XF c), X₁.Lies (ξ₀ ≫ out.u₀) y → ∀ (tK : SAB H (Sp K)), Nonempty (SABMap tK Xo.univ.t (y ≫ pullback.fst _ _)) → ∃ γ : tK.G.left ⟶ out.G.left, IsGrpPullback tK.G out.G (ξ₀ ≫ U₀.ι) γ ∧ LBIso tK.PP.L (out.L.L.pull γ) ∧ ∀ a, (tK.act.act a).left ≫ γ = γ ≫ (f a).left := by
  intro E _ _ _ H Dw l Xo c C X₁ M U₀ EE out hAdm
  haveI := X₁.ar.char
  obtain ⟨hW, pt, hpt, hd⟩ := GlobalTheory.T.isIntegral_pullback_rationalSaturation_model_open X₁.o₁ X₁.Ω₁ M U₀ X₁.S.R out.u₀ hAdm.1.ne out.u₀_gen
  haveI := hW
  obtain ⟨G₁, _, α, β, hα, hβ, hL⟩ := X₁.pulled
  let s : pullback out.u₀ (spMap (toRat X₁.S.R)) ⟶ Sp (ratHull X₁.S.R) := pullback.snd _ _
  let G₀ : Over (pullback out.u₀ (spMap (toRat X₁.S.R))) := (Over.pullback s).obj G₁
  have h₀ : IsGrpPullback G₀ G₁ s (pullback.fst G₁.hom s) := isGrpPullback_pullback G₁ s
  let w : pullback out.u₀ (spMap (toRat X₁.S.R)) ⟶ Xo.XF c := s ≫ X₁.u
  have hβ₀ : IsGrpPullback G₀ Xo.univ.t.G (w ≫ pullback.fst _ _) (pullback.fst G₁.hom s ≫ β) :=
    (h₀.comp hβ).congr (Category.assoc _ _ _).symm rfl
  obtain ⟨f₀, hf₀, hT⟩ := GlobalTheory.T.exists_action_pullback_universalUnitary E H Dw l Xo c _ w G₀ _ hβ₀
  have hα₀ := h₀.comp hα
  have wψ : (pullback.fst G₁.hom s ≫ α) ≫ X₁.ρ.P.A.hom = (G₀.hom ≫ pullback.fst out.u₀ (spMap (toRat X₁.S.R))) ≫ out.u₀ := by
    rw [hα₀.1.w, Category.assoc, pullback.condition]
  let ψ : G₀.left ⟶ pullback X₁.ρ.P.A.hom out.u₀ := pullback.lift _ _ wψ
  have hψ : IsGrpPullback G₀ ((Over.pullback out.u₀).obj X₁.ρ.P.A) (pullback.fst out.u₀ (spMap (toRat X₁.S.R))) ψ :=
    (isGrpPullback_pullback X₁.ρ.P.A out.u₀).cancel (hα₀.congr pullback.condition.symm (pullback.lift_fst _ _ _).symm)
      (pullback.lift_snd _ _ _)
  have hΦ := hψ.comp out.cart
  have hm : pt ≫ pullback.fst out.u₀ (spMap (toRat X₁.S.R)) ≫ U₀.ι = M.pt := hpt
  have hab : IsAbelianScheme G₀ := PolPull.isAbelianScheme_of_isGrpPullback X₁.ρ.P.isAb hα₀
  choose F hF hFe using fun a => exists_endo_of_generic hab hΦ pt hd M.pt hm out.endo (f₀ a) (hf₀ a).1
  refine ⟨F, hF, ?_⟩
  intro K _ ξ₀ y hLies tK ⟨mm⟩
  obtain ⟨x', hx', hxy⟩ := hLies
  let x : Sp K ⟶ pullback out.u₀ (spMap (toRat X₁.S.R)) := pullback.lift ξ₀ x' hx'.symm
  have hxw : x ≫ w = y := by
    show x ≫ pullback.snd _ _ ≫ X₁.u = y
    rw [← Category.assoc, pullback.lift_snd, hxy]
  have mm' : SABMap tK Xo.univ.t ((x ≫ w) ≫ pullback.fst _ _) := by rw [hxw]; exact mm
  obtain ⟨γ₀, hγ₀, -, hLγ, hact⟩ := hT (Sp K) x tK mm'
  refine ⟨γ₀ ≫ ψ ≫ out.φ, (hγ₀.comp hΦ).congr (by rw [← Category.assoc, pullback.lift_fst]) rfl, ?_, fun a => ?_⟩
  · have hU := Xo.univ.t.PP.isLB
    have hP := X₁.ρ.P.isLB
    have hO := out.L.isLB
    have i1 : LBIso (out.L.L.pull out.φ) (X₁.ρ.P.L.pull (pullback.fst X₁.ρ.P.A.hom out.u₀)) := ⟨out.w, out.w_gen⟩
    have i2 : LBIso (out.L.L.pull (ψ ≫ out.φ)) (X₁.ρ.P.L.pull (pullback.fst G₁.hom s ≫ α)) :=
      GenSpread.lbIso_pull_comp ψ rfl (pullback.lift_fst _ _ _).symm i1
    have i3 : LBIso (X₁.ρ.P.L.pull (pullback.fst G₁.hom s ≫ α)) (Xo.univ.t.PP.L.pull (pullback.fst G₁.hom s ≫ β)) :=
      GenSpread.lbIso_pull_comp (pullback.fst G₁.hom s) rfl rfl hL
    have i4 := LBIso.trans (pull_isLB hO _) (pull_isLB hP _) (pull_isLB hU _) i2 i3
    have i5 : LBIso (out.L.L.pull (γ₀ ≫ ψ ≫ out.φ)) (Xo.univ.t.PP.L.pull (γ₀ ≫ pullback.fst G₁.hom s ≫ β)) :=
      GenSpread.lbIso_pull_comp γ₀ rfl rfl i4
    have i6 : LBIso (Xo.univ.t.PP.L.pull (γ₀ ≫ pullback.fst G₁.hom s ≫ β))
        ((Xo.univ.t.PP.L.pull (pullback.fst G₁.hom s ≫ β)).pull γ₀) := GenSpread.lbIso_pull_pull hU γ₀ rfl
    exact LBIso.trans tK.PP.isLB (pull_isLB (pull_isLB hU _) _) (pull_isLB hO _) hLγ
      (LBIso.trans (pull_isLB (pull_isLB hU _) _) (pull_isLB hU _) (pull_isLB hO _) i6.symm i5.symm)
  · rw [← Category.assoc, hact a, Category.assoc, Category.assoc, ← hFe a, Category.assoc]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelLevelPPowerTangentStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_model_level_p_power_tangent : GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.HodgeTateKernelAtPoint → TateSt → ValueSt → BoundSt →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (τ : Psi H) (p : ℕ) [Fact p.Prime]
    [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ n : ℕ,
    ∀ (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F), OverIncl r hle → l'.A = p ^ n →
    ∀ (N : ℕ) (a : Fin N → Dw.La) (T S : Ind Dw τ.1 → Fin N → c'.V W), LatData Dw (embV c' W (conjEmb τ.1)) a T S →
    ∀ [Algebra c.F ℂ_[p]] (f : Rul Xo c) (yb : Sp 𝓞_ℂ_[p] ⟶ Y.X) (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p)
      (π : P.G.left ⟶ Y.t.G.left) (ψ : P.A.A.left ⟶ Y.oF.t.G.left) (y : FrPt Xo c ℂ_[p]), HTAt Y r ν yb yy P π ψ y →
      evR Xo c f y ≠ 0 → ∃ κ : ℂ_[p], ‖κ‖ = ‖evR Xo c f y‖ ∧
      ∀ (β : c'.V W →+* 𝓞_ℂ_[p]), yb ≫ Y.s = spMap β →
      ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber 𝓞_ℂ_[p]) ⟶ Y.t.G.left)) (U₁ U₂ : Fin g → Fin g → 𝓞_ℂ_[p])
        (h : Fin N → Fin g → 𝓞_ℂ_[p]), IsTanBasis Y.t yb e → EigAt Y.t yb (β.comp (embV c' W τ.1)) e U₁ →
        EigAt Y.t yb (β.comp (embV c' W (conjEmb τ.1))) e U₂ → HTApprox Y n yy P π ψ a e h →
        ∀ (σ : Equiv.Perm (Ind Dw τ.1)) (K₁ : Fin (Dw.mult τ.1) → Fin g) (K₂ : Fin (Dw.mult (conjEmb τ.1)) → Fin g),
          ((p : ℝ)⁻¹ ^ n < ‖((pairDet (covec β T h (σ ∘ Sum.inl)) (U₁ ∘ K₁) *
        pairDet (covec β S h (σ ∘ Sum.inr)) (U₂ ∘ K₂) : 𝓞_ℂ_[p]) : ℂ_[p])‖) →
          ∀ fv : ℂ_[p], GVal Y r ν τ.1 f yy (bcV Y.t (algebraMap 𝓞_ℂ_[p] ℂ_[p]) e) (fun k b => (U₁ (K₁ k) b : ℂ_[p]))
            (fun k b => (U₂ (K₂ k) b : ℂ_[p])) fv →
          ‖fv * ((Equiv.Perm.sign σ : ℤ) : ℂ_[p]) * (pairDet (covec β T h (σ ∘ Sum.inl)) (U₁ ∘ K₁) : 𝓞_ℂ_[p]) /
            (pairDet (covec β S h (σ ∘ Sum.inr)) (U₂ ∘ K₂) : 𝓞_ℂ_[p]) - κ‖ < ‖κ‖ := by
  first | exact @GlobalTheory.FlatModel.kap_close | exact GlobalTheory.FlatModel.kap_close | (intros; apply GlobalTheory.FlatModel.kap_close <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelMapExtensionStatement
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_model_map_extension : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.CanonicalExtensionRankOne → GlobalTheory.Published.DeRhamCanonicalExtension →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F)
    (r₀ : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r₀) (x : ℝ), Laws U x →
    ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ)
      (Xw : Y.X.Opens), p.Prime → IsCover Y r hle Z la p Xw →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] (ξ : Sp A ⟶ Y.X) (β : c'.V W →+* A),
      IsOpenImmersion ξ → ξ ≫ Y.s = spMap β → IsUnit (p : A) → ξ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ∈ Xw →
    ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber A) ⟶ Y.t.G.left)) (U₁ h₁ : Fin (Dw.mult τ.1) → Fin g → A)
      (U₂ h₂ : Fin (Dw.mult (conjEmb τ.1)) → Fin g → A), IsTanBasis Y.t ξ e →
      (∀ (S : Type) [CommRing S] (φ : A →+* S),
        EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W τ.1))) (bcV Y.t φ e) (fun k b => φ (U₁ k b)) ∧
        EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W (conjEmb τ.1)))) (bcV Y.t φ e) fun k b => φ (U₂ k b)) →
      IsUnit (pairDet h₁ U₁) → IsUnit (pairDet h₂ U₂) →
    ∀ 𝔭 : PrimeSpectrum A, ξ 𝔭 ∈ Set.range Y.j → ∃ u : (Localization.AtPrime 𝔭.asIdeal)ˣ,
      ∀ (k : Type) [Field k] (φ : Localization.AtPrime 𝔭.asIdeal →+* k), SecValAt Y r ν τ.1 s.sig ξ e U₁ U₂ k (φ.comp (algebraMap A _)) (φ u) := by
  first | exact @GlobalTheory.FlatModelOpen.unit_loc | exact GlobalTheory.FlatModelOpen.unit_loc | (intros; apply GlobalTheory.FlatModelOpen.unit_loc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralThetaFamilyOverDegenerationFamilyPullbac
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.UpExt GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Mum.UpExt

theorem over_famPull : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (k : ℕ) (F₀ : IntFam I D k) (E F : Type) [Field E] [Field F] [Algebra (FractionRing R) E] [Algebra (FractionRing R) F] [Algebra E F] [IsScalarTower (FractionRing R) E F] (s : Fam D E k), F₀.Over s → F₀.Over (famPull D E F GlobalTheory.globalFns_holds k s) := by
  intro R _ _ I D k F₀ E F _ _ _ _ _ _ s h α
  have hL := D.P.isLB
  have g1 : ∀ {W : Scheme.{0}} (w : W), gs (𝟙 W) w ⊤ (1 : Γ(W, ⊤)) = 1 := fun w => by
    rw [gs_eq _ w ⊤ trivial, map_one, map_one]
  have h1 := (secScal_iff_val hL _ _ _ _).1 (h α)
  refine (secScal_iff_val hL _ _ _ _).2 fun y J hJ => ?_
  have e1 : (𝟙 _ ≫ (DegPre.prB D F).left) = (famMap D E F).left ≫ (𝟙 _ ≫ (DegPre.prB D E).left) := by
    rw [Category.id_comp, Category.id_comp, ← Over.comp_left, famMap_snd]
  have e2 : (𝟙 _ ≫ (famMap D E F).left) = (famMap D E F).left ≫ 𝟙 _ := by
    rw [Category.id_comp, Category.comp_id]
  change _ = _ * sval (termPull D E F k α (s.s α)) _ y J
  rw [g1, _root_.one_mul, show sval (termPull D E F k α (s.s α)) (𝟙 _) y J =
      sval (s.s α) (𝟙 _ ≫ (famMap D E F).left) y J from sval_pullOver _ _ _ _ hJ, e1, e2, GlobalTheory.UU.IntExp.sval_comp _ _ _ _ _ hJ,
    GlobalTheory.UU.IntExp.sval_comp _ _ _ _ _ hJ, h1 _ _ (fun ψ => hJ _), g1, _root_.one_mul]

end GlobalTheory.Mum.UpExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageGenericBaseChangeModificatioStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAffineOpen_preimage_genericBaseChange_modification : ∀ (R : Type) [CommRing R] [IsDomain R] (M : Modif R) (G : Over M.S) (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)), IsPullback α t G.hom M.gp → ∀ W : G.left.Opens, IsAffineOpen W → IsAffineOpen (α ⁻¹ᵁ W) := by
  first | exact @GlobalTheory.Mum.isAffineOpen_preimage_genericBaseChange | exact GlobalTheory.Mum.isAffineOpen_preimage_genericBaseChange | (intros; apply GlobalTheory.Mum.isAffineOpen_preimage_genericBaseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleLineBundlePullbackOfTranslatesStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAmple_lineBundle_pullback_of_translates : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left) (hL : L.IsLB) (c : Pic A.left) (V : A.left.Opens), cls L hL = c → IsAffineOpen V → IsLocus c V → ∀ (T : Over (Sp R)) [IsAffine T.left] (n : ℕ) (a : Fin n → (T ⟶ A)), ⨆ i, ((fst A T * (snd A T ≫ a i)).left ⁻¹ᵁ V ⊓ (fst A T * (snd A T ≫ a i)⁻¹).left ⁻¹ᵁ V) = ⊤ → (∀ i, GlobalTheory.CechPic.pull (a i).left c + GlobalTheory.CechPic.pull ((a i)⁻¹).left c - 2 • GlobalTheory.CechPic.pull (1 : T ⟶ A).left c = 0) → GlobalTheory.IsAmpleLB (L.pull (fst A T).left) := by
  first | exact @GlobalTheory.isAmpleLB_pull_fst_of_translates | exact GlobalTheory.isAmpleLB_pull_fst_of_translates | (intros; apply GlobalTheory.isAmpleLB_pull_fst_of_translates <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyKodairaSpencerIdentificationOffBoundaryStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_kodairaSpencer_identification_offBoundary : GlobalTheory.Published.AbelianDeRham → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (X : GlobalTheory.FlagMod.FlagCover Y) (Z : Comp Xo c) (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)), (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y) → Nonempty (CanId M) := by
  first | exact @GlobalTheory.CompHS.canId_nonempty | exact GlobalTheory.CompHS.canId_nonempty | (intros; apply GlobalTheory.CompHS.canId_nonempty <;> assumption)
end

