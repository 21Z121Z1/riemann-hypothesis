import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2347
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2511
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2451
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqBasicOpen
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2411
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2551
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0019
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2492
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingHomAddEpsMul
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
open GlobalTheory.CechKS
noncomputable section
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.CechKS

theorem exists_ringHom_add_eps_mul {R B : Type} [CommRing R] [CommRing B] {n : ℕ} (e : R →+* B)
    (e' : Fin n → (R →+* DualNumber B)) (he : ∀ a f, (e' a f).fst = e f) (δ : R → R)
    (hδa : ∀ f f', δ (f + f') = δ f + δ f') (hδm : ∀ f f', δ (f * f') = f * δ f' + f' * δ f)
    (c : Fin n → B) (ε : B) (hε : ε * ε = 0) :
    ∃ ψ : R →+* B, ∀ f, ψ f = e f + ε * (e (δ f) + ∑ a, c a * (e' a f).snd) := by
  have h1 : δ 1 = 0 := by
    have := hδm 1 1
    simp only [_root_.one_mul, _root_.mul_one] at this
    linear_combination -this
  have h0 : δ 0 = 0 := by
    have := hδa 0 0
    rw [add_zero] at this
    linear_combination -this
  refine ⟨{ toFun := fun f => e f + ε * (e (δ f) + ∑ a, c a * (e' a f).snd),
            map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, fun f => rfl⟩
  · simp [h1]
  · intro f f'
    simp only [hδm, map_add, map_mul, TrivSqZeroExt.snd_mul, he, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op]
    have hs : ∑ x, c x * (e f * TrivSqZeroExt.snd ((e' x) f') + TrivSqZeroExt.snd ((e' x) f) * e f') =
        e f * ∑ a, c a * TrivSqZeroExt.snd ((e' a) f') + e f' * ∑ a, c a * TrivSqZeroExt.snd ((e' a) f) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun a _ => by ring
    rw [hs]
    linear_combination (-(e (δ f) + ∑ a, c a * (e' a f).snd) * (e (δ f') + ∑ a, c a * (e' a f').snd)) * hε
  · simp [h0]
  · intro f f'
    simp only [hδa, map_add, TrivSqZeroExt.snd_add, mul_add, Finset.sum_add_distrib]
    ring

theorem fst_comp_tangent_eq_one : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)
    (U : X.affineOpens) (v : Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left) (hv : IsTanAtG t (LogKS.chart U) v)
    {K : Type} [Field K] (x0 : Sp K ⟶ X) (hU : ⊤ ≤ x0 ⁻¹ᵁ U.1) (A : Over (Sp K)) [GrpObj A]
    (m : A.left ⟶ t.G.left) (hm : IsGrpPullback A t.G x0 m) (u : epsR K ⟶ A)
    (hu : u.left ≫ m = spMap (dualMap (ev x0 U.1 hU)) ≫ v),
    spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ u.left = (1 : Over.mk (𝟙 (Sp K)) ⟶ A).left := by
  intro E _ _ _ H X t U v hv K _ x0 hU A _ m hm u hu
  have hv2 : spMap (TrivSqZeroExt.fstHom Γ(X, U.1) Γ(X, U.1) Γ(X, U.1)).toRingHom ≫ v =
      (1 : Over.mk (LogKS.chart U) ⟶ t.G).left := hv.2
  have hux : spMap (ev x0 U.1 hU) ≫ LogKS.chart U = x0 := GlobalTheory.FlagMod.spMap_ev x0 U.2 hU
  let κ : Over.mk x0 ⟶ Over.mk (LogKS.chart U) := Over.homMk (spMap (ev x0 U.1 hU)) hux

  have hG1 : (spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ u.left) ≫ m = (1 : Over.mk x0 ⟶ t.G).left := by
    rw [Category.assoc, hu, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have e : (TrivSqZeroExt.fstHom K K K).toRingHom.comp (dualMap (ev x0 U.1 hU)) =
        (ev x0 U.1 hU).comp ((TrivSqZeroExt.fstHom Γ(X, U.1) Γ(X, U.1) Γ(X, U.1)).toRingHom) := by
      ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
    rw [e, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hv2]
    have := congrArg Over.Hom.left (comp_one (M := t.G) κ)
    exact this.symm ▸ rfl
  have hA1 : (1 : Over.mk (𝟙 (Sp K)) ⟶ A).left ≫ m = (1 : Over.mk x0 ⟶ t.G).left := by
    have hw : ((1 : Over.mk (𝟙 (Sp K)) ⟶ A).left ≫ m) ≫ t.G.hom = (Over.mk ((Over.mk (𝟙 (Sp K))).hom ≫ x0)).hom := by
      rw [Category.assoc, hm.1.w, ← Category.assoc, Over.w (1 : Over.mk (𝟙 (Sp K)) ⟶ A)]
      rfl
    let z : Over.mk ((Over.mk (𝟙 (Sp K))).hom ≫ x0) ⟶ t.G := Over.homMk ((1 : Over.mk (𝟙 (Sp K)) ⟶ A).left ≫ m) hw
    have hz : (z * z).left = z.left := by
      have := hm.2 (Over.mk (𝟙 (Sp K))) 1 1 z z rfl rfl
      rw [this, _root_.mul_one]
      rfl
    have hz1 : z = 1 := by
      have : z * z = z := Over.OverMorphism.ext hz
      simpa using this
    let κ' : Over.mk x0 ⟶ Over.mk ((Over.mk (𝟙 (Sp K))).hom ≫ x0) := Over.homMk (𝟙 _) (by simp)
    have := congrArg Over.Hom.left (comp_one (M := t.G) κ')
    calc _ = (κ' ≫ z).left := by simp [κ', z]
      _ = _ := by rw [hz1]; exact this
  have hA2 : (spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ u.left) ≫ A.hom = 𝟙 (Sp K) := by
    rw [Category.assoc, Over.w u]; show spMap _ ≫ spMap (algebraMap K (DualNumber K)) = 𝟙 _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have e3 : (TrivSqZeroExt.fstHom K K K).toRingHom.comp (algebraMap K (DualNumber K)) = RingHom.id K := by
      ext a; simp [TrivSqZeroExt.algebraMap_eq_inl]
    rw [e3, CommRingCat.ofHom_id, Spec.map_id]
  refine hm.1.hom_ext (hG1.trans hA1.symm) (hA2.trans ?_)
  exact (Over.w (1 : Over.mk (𝟙 (Sp K)) ⟶ A)).symm

theorem fst_comp_transl_eq : ∀ {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {B : Type} [CommRing B] (φ : K →+* B)
    (x : Sp B ⟶ A.left) (v : epsR K ⟶ A)
    (hv : spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ v.left = (1 : Over.mk (𝟙 (Sp K)) ⟶ A).left)
    (w : Sp (DualNumber B) ⟶ A.left), IsTransl φ x v w → spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ w = x := by
  intro K _ A _ B _ φ x v hv w ⟨x', v', hx', hv', hw⟩
  have hio : spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ spMap ((algebraMap B (DualNumber B)).comp φ) = spMap φ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
  let io : Over.mk (spMap φ) ⟶ Over.mk (spMap ((algebraMap B (DualNumber B)).comp φ)) :=
    Over.homMk (spMap (TrivSqZeroExt.fstHom B B B).toRingHom) hio
  have hνw : (spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ v.left) ≫ A.hom = (Over.mk (𝟙 (Sp K))).hom := by
    rw [Category.assoc, Over.w v]; show spMap _ ≫ spMap (algebraMap K (DualNumber K)) = 𝟙 _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have e3 : (TrivSqZeroExt.fstHom K K K).toRingHom.comp (algebraMap K (DualNumber K)) = RingHom.id K := by
      ext a; simp [TrivSqZeroExt.algebraMap_eq_inl]
    rw [e3, CommRingCat.ofHom_id, Spec.map_id]
  let ν : Over.mk (𝟙 (Sp K)) ⟶ A := Over.homMk (spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ v.left) hνw
  have hν : ν = 1 := Over.OverMorphism.ext hv
  let κ : Over.mk (spMap φ) ⟶ Over.mk (𝟙 (Sp K)) := Over.homMk (spMap φ) (Category.comp_id _)
  have h1 : io ≫ v' = 1 := by
    have : io ≫ v' = κ ≫ ν := by
      apply Over.OverMorphism.ext
      simp only [io, κ, ν, Over.comp_left, Over.homMk_left, hv']
      rw [← Category.assoc, ← Category.assoc]
      congr 1
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
    rw [this, hν, comp_one]
  have h2 : (io ≫ (x' * v')).left = x := by
    rw [comp_mul, h1, _root_.mul_one]
    simp only [io, Over.comp_left, Over.homMk_left, hx']
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (TrivSqZeroExt.fstHom B B B).toRingHom.comp (algebraMap B (DualNumber B)) = RingHom.id B := by
      ext a; simp [TrivSqZeroExt.algebraMap_eq_inl]
    rw [this, CommRingCat.ofHom_id, Spec.map_id]
    exact Category.id_comp x
  rw [← hw]
  exact h2

theorem top_le_preimage_of_fst : ∀ {B : Type} [CommRing B] {Z : Scheme.{0}} (z : Sp (DualNumber B) ⟶ Z) (V : Z.Opens),
    ⊤ ≤ (spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ z) ⁻¹ᵁ V → ⊤ ≤ z ⁻¹ᵁ V := by
  intro B _ Z z V h p _
  have hp : (spMap (TrivSqZeroExt.fstHom B B B).toRingHom) ((spMap (algebraMap B (DualNumber B))) p) = p := by
    show PrimeSpectrum.comap _ (PrimeSpectrum.comap _ p) = p
    ext y
    show (algebraMap B (DualNumber B)) (TrivSqZeroExt.fst y) ∈ p.asIdeal ↔ y ∈ p.asIdeal
    rw [TrivSqZeroExt.algebraMap_eq_inl]
    have hy : y = TrivSqZeroExt.inl y.fst + TrivSqZeroExt.inr y.snd := (TrivSqZeroExt.inl_fst_add_inr_snd_eq y).symm
    have hn : TrivSqZeroExt.inr y.snd ∈ p.asIdeal := by
      apply p.isPrime.mem_of_pow_mem 2
      rw [pow_two, TrivSqZeroExt.inr_mul_inr]
      exact p.asIdeal.zero_mem
    constructor
    · intro h1
      rw [hy]
      exact p.asIdeal.add_mem h1 hn
    · intro h1
      have : TrivSqZeroExt.inl y.fst = y - TrivSqZeroExt.inr y.snd :=
        eq_sub_of_add_eq (TrivSqZeroExt.inl_fst_add_inr_snd_eq y)
      rw [this]
      exact p.asIdeal.sub_mem h1 hn
  have := h (Set.mem_univ ((spMap (algebraMap B (DualNumber B))) p))
  show z p ∈ V
  rw [← hp]
  exact this

theorem comp_hom_of_isTransl {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {B : Type} [CommRing B] (φ : K →+* B)
    (x : Sp B ⟶ A.left) (v : epsR K ⟶ A) (w : Sp (DualNumber B) ⟶ A.left) (hw : IsTransl φ x v w) :
    w ≫ A.hom = spMap ((algebraMap B (DualNumber B)).comp φ) := by
  obtain ⟨x', v', -, -, rfl⟩ := hw
  exact Over.w (x' * v')

theorem exists_isChartPt : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X) (U : X.affineOpens) {n : ℕ} (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)) (D : Γ(X, U.1) → Γ(X, U.1)) (hv : ∀ a, IsTanAtG t (LogKS.chart U) (v a)) (W₀ : t.G.left.Opens) (hW₀ : W₀ ≤ t.G.hom ⁻¹ᵁ U.1) (d : ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)) (hd : LogKS.IsField W₀ d) (hlift : ∀ r, d W₀ ((t.G.hom.appLE U.1 W₀ hW₀).hom r) = (t.G.hom.appLE U.1 W₀ hW₀).hom (D r)) {K : Type} [Field K] (x0 : Sp K ⟶ X) (hU : ⊤ ≤ x0 ⁻¹ᵁ U.1) (y1 : Sp (DualNumber K) ⟶ X) (hU' : ⊤ ≤ y1 ⁻¹ᵁ U.1) (hy1 : ∀ r, ev y1 U.1 hU' r = TrivSqZeroExt.inl (ev x0 U.1 hU r) + TrivSqZeroExt.inr (ev x0 U.1 hU (D r))) (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (m : A.left ⟶ t.G.left) (m' : A'.left ⟶ t.G.left) (u : Fin n → (epsR K ⟶ A)) (hm : IsGrpPullback A t.G x0 m) (hm' : IsGrpPullback A' t.G y1 m') (hu : ∀ a, (u a).left ≫ m = spMap (dualMap (ev x0 U.1 hU)) ≫ v a) (Ω : t.G.left.affineOpens) (hΩ : Ω.1 ≤ W₀) (θ : Matrix (Fin n) (Fin n) K) (Wo : A.left.Opens) (g : Γ(A.left, Wo)ˣ) (B : Type) [CommRing B] [Algebra (DualNumber K) B] (x : Sp B ⟶ A.left) (hx : x ≫ A.hom = spMap (baseMap K B)) (hxΩ : ⊤ ≤ x ⁻¹ᵁ (m ⁻¹ᵁ Ω.1)), ∃ l, IsChartPt A' m m' Ω.1 (d Ω.1) u θ Wo g x l := by
  intro E _ _ _ H X t U n v D hv W₀ hW₀ d hd hlift K _ x0 hU y1 hU' hy1 A _ A' _ m m' u hm hm' hu Ω hΩ θ Wo g B _ _ x hx hxΩ
  have hwT : ∀ a, IsTransl (baseMap K B) x (u a) (transl (baseMap K B) x (u a)) :=
    fun a => isTransl_transl (baseMap K B) x hx (u a)
  have hred : ∀ a, spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ transl (baseMap K B) x (u a) = x := fun a =>
    fst_comp_transl_eq (baseMap K B) x (u a) (fst_comp_tangent_eq_one t U (v a) (hv a) x0 hU A m hm (u a) (hu a)) _ (hwT a)
  have hxm : ⊤ ≤ (x ≫ m) ⁻¹ᵁ Ω.1 := GlobalTheory.FlagMod.le_preimage_map m le_rfl hxΩ
  have hwm : ∀ a, ⊤ ≤ (transl (baseMap K B) x (u a) ≫ m) ⁻¹ᵁ Ω.1 := fun a =>
    top_le_preimage_of_fst _ Ω.1 (by rw [← Category.assoc, hred a]; exact hxm)
  have he : ∀ a f, (ev (transl (baseMap K B) x (u a) ≫ m) Ω.1 (hwm a) f).fst = ev (x ≫ m) Ω.1 hxm f := by
    intro a f
    have := GlobalTheory.FlagMod.ev_spMap (TrivSqZeroExt.fstHom B B B).toRingHom (transl (baseMap K B) x (u a) ≫ m) Ω.1 (hwm a)
      (by rw [← Category.assoc, hred a]; exact hxm)
    have e1 := GlobalTheory.FlagMod.ev_congr (show spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫
      (transl (baseMap K B) x (u a) ≫ m) = x ≫ m by rw [← Category.assoc, hred a]) Ω.1
      (by rw [← Category.assoc, hred a]; exact hxm) hxm
    rw [e1] at this
    rw [this]
    rfl
  have hdΩ := hd.2.1 Ω.1 hΩ
  obtain ⟨ψ, hψ⟩ := exists_ringHom_add_eps_mul (ev (x ≫ m) Ω.1 hxm) (fun a => ev (transl (baseMap K B) x (u a) ≫ m) Ω.1 (hwm a)) he
    (d Ω.1) (hd.1 Ω.1 hΩ) (hd.2.1 Ω.1 hΩ) (fun a => ∑ b, baseMap K B (θ a b) * dlogAt (baseMap K B) x (u b) Wo g)
    (algebraMap (DualNumber K) B DualNumber.eps) (by rw [← map_mul, DualNumber.eps_mul_eps, map_zero])
  have hψ' : ∀ f, ψ f = chartVal m Ω.1 (d Ω.1) u θ Wo g x f := by
    intro f
    rw [hψ f, chartVal, valR_eq_ev _ _ hxm, valR_eq_ev _ _ hxm]
    simp only [valR_eq_ev _ _ (hwm _)]
  set q : Sp B ⟶ t.G.left := spMap ψ ≫ Ω.2.fromSpec with hq_def
  have hqΩ : ⊤ ≤ q ⁻¹ᵁ Ω.1 := GlobalTheory.FlagMod.le_preimage_comp _ (GlobalTheory.FlagMod.tau_le Ω.2 le_rfl)
  have hevq : ev q Ω.1 hqΩ = ψ := GlobalTheory.FlagMod.ev_spMap_tau Ω.2 ψ hqΩ
  have hΩU : Ω.1 ≤ t.G.hom ⁻¹ᵁ U.1 := hΩ.trans hW₀
  have key : ∀ {S : Type} [CommRing S] (ρ : K →+* S) (z : Sp S ⟶ A.left) (hz : z ≫ A.hom = spMap ρ)
      (hzΩ : ⊤ ≤ (z ≫ m) ⁻¹ᵁ Ω.1) (r : Γ(X, U.1)),
      ev (z ≫ m) Ω.1 hzΩ ((t.G.hom.appLE U.1 Ω.1 hΩU).hom r) = ρ (ev x0 U.1 hU r) := by
    intro S _ ρ z hz hzΩ r
    have h1 : (z ≫ m) ≫ t.G.hom = spMap ρ ≫ x0 := by
      rw [Category.assoc, hm.1.w, ← Category.assoc, hz]
    rw [GlobalTheory.FlagMod.ev_appLE (z ≫ m) t.G.hom hΩU hzΩ (GlobalTheory.FlagMod.le_preimage_map t.G.hom hΩU hzΩ) r,
      GlobalTheory.FlagMod.ev_congr h1 U.1 _ (GlobalTheory.FlagMod.le_preimage_comp _ hU), GlobalTheory.FlagMod.ev_spMap ρ x0 U.1 hU]
    rfl
  have hres : ∀ r, resG t.G.left hΩ ((t.G.hom.appLE U.1 W₀ hW₀).hom r) = (t.G.hom.appLE U.1 Ω.1 hΩU).hom r := by
    intro r
    rw [resG, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
  have hdr : ∀ r, d Ω.1 ((t.G.hom.appLE U.1 Ω.1 hΩU).hom r) = (t.G.hom.appLE U.1 Ω.1 hΩU).hom (D r) := by
    intro r
    rw [← hres, hd.2.2 W₀ Ω.1 hΩ le_rfl, hlift, hres]
  have hU1 : ⊤ ≤ (q ≫ t.G.hom) ⁻¹ᵁ U.1 := GlobalTheory.FlagMod.le_preimage_map t.G.hom hΩU hqΩ
  have hU2 : ⊤ ≤ (spMap (algebraMap (DualNumber K) B) ≫ y1) ⁻¹ᵁ U.1 := GlobalTheory.FlagMod.le_preimage_comp _ hU'
  have hq : q ≫ t.G.hom = spMap (algebraMap (DualNumber K) B) ≫ y1 := by
    rw [← GlobalTheory.FlagMod.spMap_ev (q ≫ t.G.hom) U.2 hU1, ← GlobalTheory.FlagMod.spMap_ev (spMap (algebraMap (DualNumber K) B) ≫ y1) U.2 hU2]
    suffices e : ev (q ≫ t.G.hom) U.1 hU1 = ev (spMap (algebraMap (DualNumber K) B) ≫ y1) U.1 hU2 by rw [e]
    ext r
    rw [← GlobalTheory.FlagMod.ev_appLE q t.G.hom hΩU hqΩ hU1 r, hevq, hψ, GlobalTheory.FlagMod.ev_spMap _ y1 U.1 hU' hU2,
      RingHom.comp_apply, hy1 r, hdr, key (baseMap K B) x hx hxm, key (baseMap K B) x hx hxm]
    have hw0 : ∀ a, (ev (transl (baseMap K B) x (u a) ≫ m) Ω.1 (hwm a) ((t.G.hom.appLE U.1 Ω.1 hΩU).hom r)).snd = 0 := by
      intro a
      rw [key _ _ (comp_hom_of_isTransl _ x (u a) _ (hwT a)) (hwm a) r]
      simp [TrivSqZeroExt.algebraMap_eq_inl]
    simp only [hw0, mul_zero, Finset.sum_const_zero, add_zero]
    rw [map_add, DualNumber.inr_eq_smul_eps, Algebra.smul_def, map_mul, baseMap, RingHom.comp_apply,
      RingHom.comp_apply, mul_comm, TrivSqZeroExt.algebraMap_eq_inl]
  obtain ⟨l, hl1, hl2⟩ := hm'.1.exists_lift q (spMap (algebraMap (DualNumber K) B)) hq
  refine ⟨l, hl2, ?_, ?_⟩
  · rw [hl1]; exact hqΩ
  · intro f
    rw [← hψ' f, valR_eq_ev _ _ (by rw [hl1]; exact hqΩ)]
    rw [GlobalTheory.FlagMod.ev_congr hl1 Ω.1 _ hqΩ, hevq]

end GlobalTheory.CechKS

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionNonvanishingBasicOpenOfNearGenerato
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LBGerm GlobalTheory.AmpleOverBase

namespace GlobalTheory.GenNearExtend

theorem exists_sec_of_gen_near : ∀ (Z X : Scheme.{0}) (e : X ⟶ Z), IsOpenImmersion e → CompactSpace X →
    QuasiSeparatedSpace X → ∀ (M : LB Z), M.IsLB → ∀ (r : Γ(X, ⊤)) (O : Z.Opens),
    (∀ x ∈ X.basicOpen r, e x ∈ O) → ∀ t : LB.Gen (M.pull O.ι), t.IsGen →
    ∃ σ : LB.Sec (M.pull e), X.basicOpen r ≤ nonzeroLocus σ := by
  intro Z X e _ _ _ M hM r O hO t ht
  have hL : (M.pull e).IsLB := LB.isLB_pull hM e
  let f : (X.basicOpen r).toScheme ⟶ X := (X.basicOpen r).ι
  have hrange : Set.range (f ≫ e).base ⊆ Set.range O.ι.base := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hO _ y.2
  let ψ : (X.basicOpen r).toScheme ⟶ O.toScheme := IsOpenImmersion.lift O.ι (f ≫ e) hrange
  have hψ : ψ ≫ O.ι = f ≫ e := IsOpenImmersion.lift_fac _ _ _
  have hpt : ∀ y, O.ι (ψ y) = e (f y) := fun y => by
    rw [← Scheme.Hom.comp_apply, hψ, Scheme.Hom.comp_apply]
  let a : ChartPull (lbPow ((M.pull e).pull f) 1) (M.pull O.ι) ψ :=
    { idx := fun J _ => J PUnit.unit PUnit.unit PUnit.unit
      le := fun J y hy => by
        have h1 := mem_pull.1 (mem_pull.1 (mem_powChart.1 hy))
        show ψ y ∈ (M.pull O.ι).U _
        rw [mem_pull, hpt]
        exact h1
      g := fun y J J' hJ hJ' => by
        have h1 := mem_powChart.1 hJ
        have h2 := mem_powChart.1 hJ'
        have h1' : (𝟙 _ ≫ f) y ∈ (M.pull e).U (J PUnit.unit PUnit.unit) := mem_pull.1 h1
        have h2' : (𝟙 _ ≫ f) y ∈ (M.pull e).U (J' PUnit.unit PUnit.unit) := mem_pull.1 h2
        have h3 : ψ y ∈ (M.pull O.ι).U (fun _ => J PUnit.unit PUnit.unit PUnit.unit) := by
          rw [mem_pull, hpt]; exact mem_pull.1 (mem_pull.1 h1)
        have h4 : ψ y ∈ (M.pull O.ι).U (fun _ => J' PUnit.unit PUnit.unit PUnit.unit) := by
          rw [mem_pull, hpt]; exact mem_pull.1 (mem_pull.1 h2)
        refine (gm_lbPow_g 1 (𝟙 _) y J J' hJ hJ').trans ?_
        rw [pow_one, gm_pull_g ((M.pull e)) f (𝟙 _) y _ _ h1 h2, gm_pull_g M e (𝟙 _ ≫ f) y _ _ h1' h2',
          gm_pull_g M O.ι ψ y _ _ h3 h4, hψ, Category.id_comp] }
  let s0 : (M.pull O.ι).Sec := ⟨fun i => (t.s i).val, fun i j => congrArg Units.val (ht i j)⟩
  let t' := chartSec a s0
  have ht' : ∀ y, y ∈ nonzeroLocus t' := fun y => by
    obtain ⟨i, hi⟩ := exists_chart hM (e (f y))
    have hJ : y ∈ (lbPow ((M.pull e).pull f) 1).U (fun _ _ _ => i) :=
      mem_powChart.2 (mem_pull.2 (mem_pull.2 hi))
    rw [mem_nonzeroLocus_iff_isUnit t' hJ, gs_chartSec a s0 (𝟙 _) y _ hJ]
    have hm : (𝟙 _ ≫ ψ) y ∈ (M.pull O.ι).U (a.idx (fun _ _ _ => i)) := a.le _ hJ
    rw [gs_unit _ y _ hm]
    exact Units.isUnit _
  have hr : X.basicOpen r = f.opensRange := (Scheme.Opens.opensRange_ι _).symm
  have hs₀ : nonzeroLocus (secOfFn (M.pull e) r) = f.opensRange := (nonzeroLocus_secOfFn hL r).trans hr
  obtain ⟨T, hT, hTu⟩ := exists_push f (nonzeroLocus (secOfFn (M.pull e) r)) hs₀ t'
  obtain ⟨N, hN⟩ := exists_sec_eq_pow_mul hL (secOfFn (M.pull e) r) T hT
  obtain ⟨u, hu⟩ := hN N le_rfl
  have key : ∀ (y' : (X.basicOpen r).toScheme) (J : PUnit → (M.pull e).ι), f y' ∈ powChart (M.pull e) J →
      (f y' ∈ nonzeroLocus u ↔ y' ∈ nonzeroLocus t') := fun y' J hJ => by
    have hs : f y' ∈ nonzeroLocus (secOfFn (M.pull e) r) := hs₀ ▸ ⟨y', rfl⟩
    have hy : f y' ∈ nonzeroLocus (secOfFn (M.pull e) r) ⊓ powChart (M.pull e) J := ⟨hs, hJ⟩
    have e' := congrArg (gs (𝟙 X) (f y') _) (hu J)
    rw [gs_res (𝟙 X) (f y') _ hy, gs_mul (𝟙 X) (f y') _ hy, gs_pow (𝟙 X) (f y') _ hy,
      gs_res (𝟙 X) (f y') _ hy] at e'
    rw [mem_nonzeroLocus_iff_powFn u hJ, e', IsUnit.mul_iff, hTu y' J hJ]
    exact and_iff_right (((mem_nonzeroLocus_iff_powFn _ hJ).1 hs).pow N)
  refine ⟨secOfPowOne (secCast (by omega) u), ?_⟩
  rw [nonzeroLocus_secOfPowOne, nonzeroLocus_secCast]
  intro x hx
  obtain ⟨y, rfl⟩ : ∃ y, f y = x := ⟨⟨x, hx⟩, rfl⟩
  obtain ⟨i, hi⟩ := exists_chart hL (f y)
  exact (key y (fun _ => i) (mem_powChart.2 hi)).2 (ht' y)

end GlobalTheory.GenNearExtend
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionNonvanishingWhereSingleCoefficient
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory

theorem exists_sec_sum_nonzero :
    ∀ (X : Scheme.{0}) (L : LB X) (κ : Type) [Fintype κ] (r : κ → Γ(X, ⊤)) (σ : κ → LB.Sec L),
      ∃ s : LB.Sec L, ∀ (z : X) (i : κ), z ∈ X.basicOpen (r i) → z ∈ nonzeroLocus (σ i) →
        (∀ j, j ≠ i → z ∉ X.basicOpen (r j)) → z ∈ nonzeroLocus s := by
  intro X L κ _ r σ
  classical
  have hres : ∀ {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (a : Γ(X, U)),
      (X.presheaf.map (homOfLE h2).op).hom ((X.presheaf.map (homOfLE h1).op).hom a) =
        (X.presheaf.map (homOfLE (h2.trans h1)).op).hom a := by
    intro U V W h1 h2 a
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl
  let s : LB.Sec L :=
    { f := fun m => ∑ j, (X.presheaf.map (homOfLE (le_top : L.U m ≤ ⊤)).op).hom (r j) * (σ j).f m
      compat := fun m n => by
        simp only [map_sum, map_mul, Finset.mul_sum, hres]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [(σ j).compat m n]
        ring }
  refine ⟨s, fun z i hri hσi hrj => ?_⟩
  obtain ⟨m, hm⟩ := TopologicalSpace.Opens.mem_iSup.1 hσi
  have hzm : z ∈ L.U m := X.basicOpen_le _ hm
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨m, ?_⟩
  rw [Scheme.mem_basicOpen X _ z hzm] at hm ⊢
  have hgerm : ∀ j, (X.presheaf.germ (L.U m) z hzm).hom
      ((X.presheaf.map (homOfLE (le_top : L.U m ≤ ⊤)).op).hom (r j)) =
        (X.presheaf.germ ⊤ z trivial).hom (r j) := fun j =>
    TopCat.Presheaf.germ_res_apply _ _ _ _ _
  simp only [s, map_sum, map_mul, hgerm]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have hu : IsUnit ((X.presheaf.germ ⊤ z trivial).hom (r i) * (X.presheaf.germ (L.U m) z hzm).hom ((σ i).f m)) :=
    ((Scheme.mem_basicOpen_top X _ z).1 hri).mul hm
  have hmax : ∑ j ∈ Finset.univ.erase i, (X.presheaf.germ ⊤ z trivial).hom (r j) *
      (X.presheaf.germ (L.U m) z hzm).hom ((σ j).f m) ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk z) := by
    refine Ideal.sum_mem _ fun j hj => Ideal.mul_mem_right _ _ ?_
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← Scheme.mem_basicOpen_top]
    exact hrj j (Finset.ne_of_mem_erase hj)
  by_contra hn
  have : (X.presheaf.germ ⊤ z trivial).hom (r i) * (X.presheaf.germ (L.U m) z hzm).hom ((σ i).f m) ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk z) := by
    have h2 : _ ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk z) := (IsLocalRing.mem_maximalIdeal _).2 hn
    simpa using Ideal.sub_mem _ h2 hmax
  exact (IsLocalRing.mem_maximalIdeal _).1 this hu

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionOfAppellHumbertThetaFunction
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaGAGA

variable {A : Over (Sp ℂ)} [GrpObj A] {M : LB A.left} {g : ℕ}

theorem top_le_of_lbPow (u : HolUnif A M g) (k : ℕ) (j : (lbPow M k).ι) {z : Fin g → ℂ}
    (hz : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow M k).U j) : ⊤ ≤ (u.ex z).left ⁻¹ᵁ M.U (j PUnit.unit) :=
  GlobalTheory.top_le_preimage_mono _ (GlobalTheory.Cartier.lbPow_U M k j).le hz

def powFrame (u : HolUnif A M g) (k : ℕ) : HolUnif A (lbPow M k) g where
  ex := u.ex
  ex_add := u.ex_add
  ex_onto := u.ex_onto
  Λ := u.Λ
  ker := u.ker
  discrete := u.discrete
  full := u.full
  hol := u.hol
  fr j z := u.fr (j PUnit.unit) z ^ k
  fr_hol j := ((u.fr_hol (j PUnit.unit)).mono fun _ hz => top_le_of_lbPow u k j hz).pow k
  fr_ne j z hz := pow_ne_zero _ (u.fr_ne _ z (top_le_of_lbPow u k j hz))
  fr_compat i j z hz := GlobalTheory.ThetaBundleSec.fr_pow_compat u z k i j
    ((GlobalTheory.top_le_preimage_inf _ _ _).1 hz).1 ((GlobalTheory.top_le_preimage_inf _ _ _).1 hz).2

theorem exists_isFnPow : ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A →
    ∀ (M : LB A.left) (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ),
    M.IsLB → u.IsAH Hm χ → ∀ (k : ℕ) (θ : (Fin g → ℂ) → ℂ), u.IsThetaFn Hm χ k θ → ∃ s, u.IsFnPow k s θ := by
  intro g A _ hA M u Hm χ hM hAH k θ hθ
  have := hA.comm
  have hp : IsProjOver A.hom := (GlobalTheory.ProjSpace.isProjBy_iff_isProjOver A.hom).1
    (GlobalTheory.AbelianProjective.isProjBy_of_isAbelianScheme ℂ A hA)
  obtain ⟨s, hs⟩ := GlobalTheory.HolUnifSec.exists_isFn (powFrame u k) hA hp (GlobalTheory.isLB_lbPow hM k) hθ.1 (by
    intro l hl j z hz
    have hz' : ⊤ ≤ (u.ex z).left ⁻¹ᵁ M.U (j PUnit.unit) := top_le_of_lbPow u k j hz
    have h1 := hθ.2 ⟨l, hl⟩ z
    have h2 := hAH.2.2.2 ⟨l, hl⟩ _ z hz'
    change θ (z + l) * u.fr (j PUnit.unit) (z + l) ^ k = θ z * u.fr (j PUnit.unit) z ^ k
    simp only [hermForm] at h1
    change θ (z + l) = _ at h1
    change u.fr (j PUnit.unit) z = _ * u.fr (j PUnit.unit) (z + l) at h2
    rw [h1, h2, mul_pow]
    ring)
  exact ⟨s, hs⟩

end GlobalTheory.ThetaGAGA
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionTranslateTensorFibreNonvanishingStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_translateTensor_fibre_nonvanishing : ∀ (S : Scheme.{0}) (P : PolAV S) (k : Type) [Field k] (t : Spec (CommRingCat.of k) ⟶ S) (c : Over.mk t ⟶ P.A) (y : (Over.mk t ⊗ P.A).left), ∃ s : LB.Sec (twistLB P.A P.L 2 c), y ∈ nonzeroLocus s := by
  first | exact @GlobalTheory.TwistFibreGen.exists_sec_mem_nonzeroLocus | exact GlobalTheory.TwistFibreGen.exists_sec_mem_nonzeroLocus | (intros; apply GlobalTheory.TwistFibreGen.exists_sec_mem_nonzeroLocus <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionTransportAlongGeneratingIsoStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_transport_along_generating_iso : ∀ {X : Scheme.{0}} {M L : LB X} (e : LB.Iso M L), e.IsGen → M.IsLB → L.IsLB →
    ∀ σ : L.Sec, ∃ σ' : M.Sec, GlobalTheory.Cartier.SecMaps e σ' σ ∧ Out.nonzeroLocus σ ≤ Out.nonzeroLocus σ' := by
  first | exact @GlobalTheory.SecTransport.main | exact GlobalTheory.SecTransport.main | (intros; apply GlobalTheory.SecTransport.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionWithRangeInOpenStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_residueFieldPoint_smooth_completeLocal : ∀ (R R' : Type) [CommRing R] [CommRing R'] [IsLocalRing R'] [IsNoetherianRing R'], IsAdicComplete (maximalIdeal R') R' → ∀ (ρ : R →+* R') (U : Over (Sp R)), Smooth U.hom → ∀ (x₀ : Sp (ResidueField R') ⟶ U.left), x₀ ≫ U.hom = spMap ((residue R').comp ρ) → ∀ O : U.left.Opens, Set.range x₀ ⊆ O → ∃ a : Sp R' ⟶ U.left, a ≫ U.hom = spMap ρ ∧ Set.range a ⊆ O := by
  first | exact @GlobalTheory.HenselLift.exists_lift_mem_open | exact GlobalTheory.HenselLift.exists_lift_mem_open | (intros; apply GlobalTheory.HenselLift.exists_lift_mem_open <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeparablePointSmoothLocalRingOpenStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_separable_point_smooth_localRing_open : ∀ (R : Type) [CommRing R] [IsLocalRing R] (U : Over (Sp R)), Smooth U.hom → ∀ O : U.left.Opens, (∃ u ∈ O, U.hom u = closedPoint R) → ∃ (k' : Type) (_ : Field k') (_ : Algebra (ResidueField R) k') (_ : Module.Finite (ResidueField R) k') (_ : Algebra.IsSeparable (ResidueField R) k') (x : Sp k' ⟶ U.left), x ≫ U.hom = spMap ((algebraMap (ResidueField R) k').comp (residue R)) ∧ Set.range x ⊆ O := by
  first | exact @GlobalTheory.Mum.exists_separable_point_of_smooth | exact GlobalTheory.Mum.exists_separable_point_of_smooth | (intros; apply GlobalTheory.Mum.exists_separable_point_of_smooth <;> assumption)
end

