import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.ExistsUniqueEqConstMulEllTheta
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsVariableChangeEisensteinCurve
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HypSEisensteinCurve
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ZH.CubeRootAut

open GlobalTheory.CechPic GlobalTheory.TripleProd GlobalTheory.WeierstrassCurve GlobalTheory.CMCurve GlobalTheory.AddLaw

section General

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

theorem cubeCls_pair {T : Over S} (x y : T ⟶ G) (c : CechPic.Pic G.left) :
    cubeCls ![x, y] c = pull (x * y).left c - pull x.left c - pull y.left c + pull (1 : T ⟶ G).left c := by
  refine (Fintype.sum_equiv (Equiv.ulift : ULift.{0} (Finset (Fin 2)) ≃ Finset (Fin 2)) _
    (fun I => ((-1 : ℤ) ^ (2 - I.card)) • pull (psum G ![x, y] I).left c) fun _ => rfl).trans ?_
  have u : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide
  have p₀ : psum G ![x, y] ∅ = 1 := rfl
  have p₁ : psum G ![x, y] {0} = x := _root_.mul_one x
  have p₂ : psum G ![x, y] {1} = y := _root_.mul_one y
  have p₄ : psum G ![x, y] {0, 1} = x * y := congrArg (x * ·) (_root_.mul_one y)
  rw [u, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, p₀, p₁, p₂, p₄]
  have c₁ : ({0, 1} : Finset (Fin 2)).card = 2 := by decide
  simp only [c₁, Finset.card_singleton, Finset.card_empty]
  norm_num
  abel

theorem cubeCls_triple {T : Over S} (x y z : T ⟶ G) (c : CechPic.Pic G.left) :
    cubeCls ![x, y, z] c = pull (x * y * z).left c - pull (x * y).left c - pull (x * z).left c -
      pull (y * z).left c + pull x.left c + pull y.left c + pull z.left c - pull (1 : T ⟶ G).left c := by
  refine (Fintype.sum_equiv (Equiv.ulift : ULift.{0} (Finset (Fin 3)) ≃ Finset (Fin 3)) _
    (fun I => ((-1 : ℤ) ^ (3 - I.card)) • pull (psum G ![x, y, z] I).left c) fun _ => rfl).trans ?_
  have u : (Finset.univ : Finset (Finset (Fin 3))) = {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} := by decide
  have p₀ : psum G ![x, y, z] ∅ = 1 := rfl
  have p₁ : psum G ![x, y, z] {0} = x := _root_.mul_one x
  have p₂ : psum G ![x, y, z] {1} = y := _root_.mul_one y
  have p₃ : psum G ![x, y, z] {2} = z := _root_.mul_one z
  have p₄ : psum G ![x, y, z] {0, 1} = x * y := congrArg (x * ·) (_root_.mul_one y)
  have p₅ : psum G ![x, y, z] {0, 2} = x * z := congrArg (x * ·) (_root_.mul_one z)
  have p₆ : psum G ![x, y, z] {1, 2} = y * z := congrArg (y * ·) (_root_.mul_one z)
  have p₇ : psum G ![x, y, z] {0, 1, 2} = x * y * z :=
    (congrArg (fun w => x * (y * w)) (_root_.mul_one z)).trans (_root_.mul_assoc x y z).symm
  rw [u, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton, p₀, p₁, p₂, p₃, p₄, p₅, p₆, p₇]
  have c₁ : ({0, 1} : Finset (Fin 3)).card = 2 := by decide
  have c₂ : ({0, 2} : Finset (Fin 3)).card = 2 := by decide
  have c₃ : ({1, 2} : Finset (Fin 3)).card = 2 := by decide
  have c₄ : ({0, 1, 2} : Finset (Fin 3)).card = 3 := by decide
  simp only [c₁, c₂, c₃, c₄, Finset.card_singleton, Finset.card_empty]
  norm_num
  abel

theorem hypS_of_invariant {L : LB G.left} (hL : L.IsLB) (h0 : Rigidified G L)
    (hΘ : ∃ t : LB.Gen (Theta G L), t.IsGen) (w wd : G ⟶ G) [IsMonHom w] [IsMonHom wd]
    (hsum : w * wd = 𝟙 G) (hcomp : wd ≫ w = 𝟙 G) (hw : pull w.left (cls L hL) = cls L hL)
    (hι : pull (ι[G]).left (cls L hL) = cls L hL) : HypS G L := by
  have qw : ∀ {T : Over S} (x : T ⟶ G), pull (x ≫ w).left (cls L hL) = pull x.left (cls L hL) := fun x => by
    rw [Over.comp_left, pull_comp, hw]
  have qwd : ∀ {T : Over S} (x : T ⟶ G), pull (x ≫ wd).left (cls L hL) = pull x.left (cls L hL) := fun x => by
    rw [← qw, Category.assoc, hcomp, Category.comp_id]
  have qι : ∀ {T : Over S} (x : T ⟶ G), pull (x⁻¹).left (cls L hL) = pull x.left (cls L hL) := fun x => by
    rw [Hom.inv_def, Over.comp_left, pull_comp, hι]
  have q1 : ∀ T : Over S, pull (1 : T ⟶ G).left (cls L hL) = 0 := fun T => by
    have e : pull (η[G]).left (cls L hL) = 0 := (cls_eq_zero_iff (pull_isLB hL _)).2 h0
    rw [Hom.one_def, Over.comp_left, pull_comp, e, map_zero]
  have qid : pull (𝟙 G : G ⟶ G).left (cls L hL) = cls L hL := pull_id _
  have hwd : pull wd.left (cls L hL) = cls L hL := by
    have := qwd (𝟙 G)
    rwa [Category.id_comp, qid] at this
  have cube : cubeCls ![𝟙 G, w, w⁻¹] (cls L hL) = 0 := by
    have h : cubeCls (x3 G) (cls L hL) = 0 := (cls_cubeLB _ hL).symm.trans ((cls_eq_zero_iff _).2 hΘ)
    rw [pull_cubeCls (lift (𝟙 G) (lift w w⁻¹)) (x3 G) _ _ (fun i => by fin_cases i <;> simp [x3]), h, map_zero]
  have e₁ : 𝟙 G * w⁻¹ = wd := by rw [← hsum, _root_.mul_comm w wd, mul_inv_cancel_right]
  rw [cubeCls_triple, mul_inv_cancel_right, e₁, mul_inv_cancel, q1, qι, qid, hw, hwd] at cube
  refine ⟨w, wd, inferInstance, inferInstance, hsum, (cls_eq_iff hL (LB.isLB_linComb hL _ _)).1 ?_,
    (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL _ _)).1 ?_⟩
  · refine Eq.trans ?_ (cls_cubeLB _ hL).symm
    rw [cubeCls_pair, q1, qid, hw]
    refine sub_eq_zero.1 (Eq.trans ?_ cube)
    abel
  · refine (cls_cubeLB _ hL).trans (Eq.trans ?_ (cls_cubeLB _ hL).symm)
    have e₂ : (fst G G * (snd G G ≫ wd)) ≫ w = (fst G G ≫ w) * snd G G := by
      rw [MonObj.mul_comp, Category.assoc, hcomp, Category.comp_id]
    rw [cubeCls_pair, cubeCls_pair, ← e₂, qw, qw, qwd]

end General

theorem pull_cls_originLB {R : Type} [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic]
    (u : schemeOver W ⟶ schemeOver W) [IsIso u] (hu : η[schemeOver W] ≫ u = η[schemeOver W]) :
    pull u.left (cls (originLB W) (originLB_isLB W)) = cls (originLB W) (originLB_isLB W) := by
  have : IsIso u.left := inferInstanceAs (IsIso ((Over.forget _).map u))
  have hreg := fun i V h => ((isRegularSec_originSec W i).resG (V := V) h).mem
  have key := SameZeroScheme.exists_isGen_linComb (schemeOver W).left _ (originLB W) (originSec W) u.left (𝟙 _)
    (originLB_isLB W)
    (fun i V h => SymOfZeroDivisor.appLE_mem_nonZeroDivisors _ _ _ (hreg i) V h)
    (fun i V h => SymOfZeroDivisor.appLE_mem_nonZeroDivisors _ _ _ (hreg i) V h) (by
      intro T t i j h h'
      rw [appLE_originSec_eq_zero_iff_eSec, appLE_originSec_eq_zero_iff_eSec, Category.comp_id]
      have h1 : u.left ≫ (schemeOver W).hom = (schemeOver W).hom := Over.w _
      have h2 : eSec (schemeOver W) ≫ u.left = eSec (schemeOver W) := congrArg (·.left) hu
      have h3 : (t ≫ u.left) ≫ (schemeOver W).hom ≫ eSec (schemeOver W) =
          (t ≫ (schemeOver W).hom ≫ eSec (schemeOver W)) ≫ u.left := by
        rw [Category.assoc, reassoc_of% h1]
        simp only [Category.assoc]
        exact congrArg (fun v => t ≫ (schemeOver W).hom ≫ v) h2.symm
      rw [h3]
      exact cancel_mono _)
  have e := (cls_linComb (originLB_isLB W) _ _ _).symm.trans
    ((cls_eq_zero_iff (LB.isLB_linComb (originLB_isLB W) _ _)).2 key)
  rw [Fin.sum_univ_two] at e
  have e' : (1 : ℤ) • pull u.left (cls (originLB W) (originLB_isLB W)) +
      (-1 : ℤ) • pull (𝟙 (schemeOver W).left) (cls (originLB W) (originLB_isLB W)) = 0 := e
  rwa [pull_id, one_zsmul, neg_one_zsmul, ← sub_eq_add_neg, sub_eq_zero] at e'

theorem hypS_eisensteinCurve (hC : CubeSt) {R : Type} [CommRing R] [IsNoetherianRing R] {ω : R}
    (hω : ω ^ 2 + ω + 1 = 0) [(eisensteinCurve R).IsElliptic] :
    HypS (ellPolAV (eisensteinCurve R)).A (ellPolAV (eisensteinCurve R)).L := by
  let P := ellPolAV (eisensteinCurve R)
  obtain ⟨r, hr⟩ := P.rigid
  obtain ⟨⟨cub⟩, -⟩ := hC _ P ⟨P.L, r, P.isLB, hr⟩ rfl
  let φ : P.A ⟶ P.A := eisensteinAut hω
  have : IsMonHom φ := isMonHom_eisensteinAut hω
  have h₂ : (φ ≫ φ) * φ * 𝟙 _ = 1 := eisensteinAut_sq hω
  have h₃ : φ ≫ φ ≫ φ = 𝟙 _ := by
    have h := congrArg (φ ≫ ·) h₂
    simp only [MonObj.comp_mul, MonObj.comp_one, Category.comp_id] at h
    rw [_root_.mul_comm] at h₂
    rw [_root_.mul_assoc] at h
    exact mul_right_cancel (h.trans h₂.symm)
  have : IsIso φ := ⟨φ ≫ φ, h₃, (Category.assoc _ _ _).trans h₃⟩
  have hφ : pull φ.left (cls P.L P.isLB) = cls P.L P.isLB :=
    @pull_cls_originLB _ _ (eisensteinCurve R) _ φ ‹IsIso φ› (IsMonHom.one_hom φ)
  have hι : pull (ι[P.A]).left (cls P.L P.isLB) = cls P.L P.isLB :=
    pull_cls_originLB (eisensteinCurve R) ι[schemeOver _] GrpObj.one_inv
  refine hypS_of_invariant P.isLB P.rigid ⟨cub.t, cub.isGen⟩ (φ ≫ ι[P.A]) ((φ ≫ φ) ≫ ι[P.A]) ?_ ?_ ?_ hι
  · rw [← Hom.inv_def, ← Hom.inv_def, ← mul_inv_rev, inv_eq_iff_mul_eq_one, h₂]
  · rw [← Hom.inv_def, ← Hom.inv_def, GrpObj.comp_inv, GrpObj.inv_comp, inv_inv, Category.assoc, h₃]
  · rw [Over.comp_left, pull_comp, hι, hφ]

theorem exists_hypS : Laws → ∀ (K : Type) [Field K] [CharZero K] (ω : K), ω ^ 2 + ω + 1 = 0 →
    ∃ P : PolAV (Sp K), P.g = 1 ∧ HypS P.A P.L := by
  intro hL K _ _ ω hω
  have := isElliptic_eisensteinCurve (R := K) (Ne.isUnit three_ne_zero)
  exact ⟨ellPolAV (eisensteinCurve K), rfl, hypS_eisensteinCurve hL.cube hω⟩

end GlobalTheory.ZH.CubeRootAut
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IntegralGaugeValuesAreValuationUnits
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
noncomputable section
namespace GlobalTheory.Ex.UnitVal

section Values
variable {C : Type} [Field C] {X Y : Scheme.{0}}

theorem valF_appLE' {F : Type} [Field F] {x : Sp F ⟶ X} {U : X.Opens} (f : X ⟶ Y) (W : Y.Opens) (e : U ≤ f ⁻¹ᵁ W)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(Y, W)) : valF x U ((f.appLE W U e).hom a) = valF (x ≫ f) W a := by
  have h' : ⊤ ≤ (x ≫ f) ⁻¹ᵁ W := fun q hq => e (h hq)
  rw [valF, valF, dif_pos h, dif_pos h', ← Scheme.Hom.appLE_comp_appLE x f W U ⊤ e h]
  rfl

theorem valF_res' {F : Type} [Field F] {x : Sp F ⟶ X} {U V : X.Opens} (e : V ≤ U)
    (h : ⊤ ≤ x ⁻¹ᵁ V) (a : Γ(X, U)) : valF x V ((X.presheaf.map (homOfLE e).op).hom a) = valF x U a := by
  have h' : ⊤ ≤ x ⁻¹ᵁ U := fun q hq => e (h hq)
  rw [valF, valF, dif_pos h, dif_pos h', ← Scheme.Hom.map_appLE x h (homOfLE e).op]
  rfl

theorem exists_valHom (S : ValuationSubring C) (t : Sp S ⟶ X) (U : X.Opens) (ht : ⊤ ≤ t ⁻¹ᵁ U) :
    ∃ g : Γ(X, U) →+* S, ∀ a, valF (spMap S.subtype ≫ t) U a = g a := by
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom.comp (t.appLE U ⊤ ht).hom, fun a => ?_⟩
  have h' : ⊤ ≤ (spMap S.subtype ≫ t) ⁻¹ᵁ U := fun q _ => ht (Set.mem_univ (spMap S.subtype q))
  rw [valF, dif_pos h']
  have e : (spMap S.subtype ≫ t).appLE U ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom =
      t.appLE U ⊤ ht ≫ (Scheme.ΓSpecIso (CommRingCat.of S)).hom ≫ CommRingCat.ofHom S.subtype := by
    rw [← Scheme.ΓSpecIso_naturality, ← Scheme.Hom.appLE_comp_appLE (spMap S.subtype) t U ⊤ ⊤ ht le_rfl,
      Category.assoc]
    rfl
  exact congrArg (fun g => g.hom a) e

theorem val_valF_le {S : ValuationSubring C} (t : Sp S ⟶ X) (U : X.Opens)
    (ht : ⊤ ≤ t ⁻¹ᵁ U) (a : Γ(X, U)) : valF (spMap S.subtype ≫ t) U a ∈ S := by
  obtain ⟨g, hg⟩ := exists_valHom S t U ht
  rw [hg]
  exact (g a).2

theorem val_valF_unit {S : ValuationSubring C} (t : Sp S ⟶ X) (U : X.Opens)
    (ht : ⊤ ≤ t ⁻¹ᵁ U) (a : Γ(X, U)) (ha : IsUnit a) : S.valuation (valF (spMap S.subtype ≫ t) U a) = 1 := by
  obtain ⟨g, hg⟩ := exists_valHom S t U ht
  rw [hg]
  exact (S.valuation_eq_one_iff (g a)).1 (ha.map g)
end Values

section Geo
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {C : Type} [Field C] [Algebra (FractionRing R) C]
  {N : NumD C} {ν : NumOf D C N} {S : ValuationSubring C} {s : Sp S ⟶ Sp R}

theorem exists_base (h : ∀ r : R, algebraMap (FractionRing R) C (algebraMap R _ r) ∈ S) :
    ∃ s : Sp S ⟶ Sp R, spMap S.subtype ≫ s = (TF (R := R) C).hom := by
  refine ⟨spMap (((algebraMap (FractionRing R) C).comp (algebraMap R _)).codRestrict S.toSubring h), ?_⟩
  change _ = jFK (R := R) C ≫ jK R
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

theorem base_ext {a b : Sp S ⟶ Sp R} (h : spMap S.subtype ≫ a = spMap S.subtype ≫ b) : a = b := by
  obtain ⟨a, rfl⟩ := Spec.map_surjective a
  obtain ⟨b, rfl⟩ := Spec.map_surjective b
  rw [← Spec.map_comp, ← Spec.map_comp] at h
  have := Spec.map_injective h
  congr 1
  ext r
  exact congrArg (fun g => g.hom r) this

theorem isDominant_sub : IsDominant (spMap S.subtype) :=
  ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical S.subtype).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 S.subtype_injective]; exact bot_le)⟩

theorem chart_int (hν : ν.Integral S) (hs : spMap S.subtype ≫ s = (TF (R := R) C).hom) (y : Sp S ⟶ D.P.A.left)
    (hy : y ≫ D.P.A.hom = s) : ⊤ ≤ y ⁻¹ᵁ D.P.L.U (ν.J (spMap S.subtype ≫ y)) := by
  obtain ⟨x₀, e, h⟩ := hν (Over.homMk (spMap S.subtype ≫ y) (by rw [Category.assoc, hy, hs]))
  have := D.P.isAb.proper
  have := isDominant_sub (S := S)
  have e' : spMap S.subtype ≫ x₀ = spMap S.subtype ≫ y := e
  obtain rfl : x₀ = y := ext_of_isDominant_of_isSeparated D.P.A.hom
    (base_ext (by rw [← Category.assoc, e', Category.assoc])) _ e'
  exact h

theorem wchart_int (hν : ν.Integral S) (hs : spMap S.subtype ≫ s = (TF (R := R) C).hom) {Y : Scheme.{0}} {K : Type}
    [Fintype K] (φ : K → (Y ⟶ D.P.A.left)) (r : Sp S ⟶ Y) (h : ∀ k, r ≫ φ k ≫ D.P.A.hom = s) :
    ⊤ ≤ r ⁻¹ᵁ LB.wchart D.P.L φ fun k => ν.J ((spMap S.subtype ≫ r) ≫ φ k) := fun q hq =>
  Set.mem_iInter.2 fun k => by
    beta_reduce
    rw [Category.assoc]
    exact chart_int hν hs (r ≫ φ k) (by rw [Category.assoc, h]) hq

theorem val_vF (hν : ν.Integral S) (hs : spMap S.subtype ≫ s = (TF (R := R) C).hom)
    {Y : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ D.P.A.left)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb D.P.L φ ε))
    (r : Sp S ⟶ Y) (h : ∀ k, r ≫ φ k ≫ D.P.A.hom = s) {r' : Sp C ⟶ Y} (e : spMap S.subtype ≫ r = r') :
    S.valuation (vF t r' ν.J) = 1 := by
  subst e
  exact val_valF_unit r _ (wchart_int hν hs φ r h) _ (Units.isUnit _)

theorem val_sF (hν : ν.Integral S) (hs : spMap S.subtype ≫ s = (TF (R := R) C).hom)
    {Y : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ D.P.A.left)} {ε : K → ℤ} (t : LB.Sec (LB.LinComb D.P.L φ ε))
    (r : Sp S ⟶ Y) (h : ∀ k, r ≫ φ k ≫ D.P.A.hom = s) {r' : Sp C ⟶ Y} (e : spMap S.subtype ≫ r = r') :
    sF t r' ν.J ∈ S := by
  subst e
  exact val_valF_le r _ (wchart_int hν hs φ r h) _

theorem exists_ext (hν : ν.Integral S) (hs : spMap S.subtype ≫ s = (TF (R := R) C).hom) (x : TF (R := R) C ⟶ D.P.A) :
    ∃ x₀ : Over.mk s ⟶ D.P.A, (Over.homMk (spMap S.subtype) hs : TF (R := R) C ⟶ Over.mk s) ≫ x₀ = x := by
  obtain ⟨x₀, e, -⟩ := hν x
  refine ⟨Over.homMk x₀ (base_ext ?_), Over.OverMorphism.ext e⟩
  rw [← Category.assoc, e, Over.w x]
  exact hs.symm

theorem val_rig (hν : ν.Integral S) (hs : spMap S.subtype ≫ s = (TF (R := R) C).hom) :
    S.valuation (vF (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig (TF (R := R) C).hom ν.J) = 1 :=
  val_vF hν hs _ s (fun _ => by
    have : eSec D.P.A ≫ D.P.A.hom = 𝟙 _ := Over.w η[D.P.A]
    exact (congrArg (s ≫ ·) this).trans (Category.comp_id _)) hs

theorem val_θ (hν : ν.Integral S) (hs : spMap S.subtype ≫ s = (TF (R := R) C).hom)
    (x y u : N.A) : S.valuation ((N.θ x y u : C)) = 1 := by
  obtain ⟨x₀, hx⟩ := exists_ext hν hs (ν.eA x)
  obtain ⟨y₀, hy⟩ := exists_ext hν hs (ν.eA y)
  obtain ⟨u₀, hu⟩ := exists_ext hν hs (ν.eA u)
  rw [ν.θ_eq]
  refine val_vF hν hs _ (lift x₀ (lift y₀ u₀)).left (fun k => ?_) ?_
  · exact (congrArg (_ ≫ ·) (Over.w (psum D.P.A (x3 D.P.A) k.down))).trans (Over.w (lift x₀ (lift y₀ u₀)))
  · rw [← hx, ← hy, ← hu, ← comp_lift, ← comp_lift]
    rfl

theorem val_σ (hν : ν.Integral S) (hs : spMap S.subtype ≫ s = (TF (R := R) C).hom)
    (x : N.A) : S.valuation ((N.σ x : C)) = 1 := by
  obtain ⟨x₀, hx⟩ := exists_ext hν hs (ν.eA x)
  rw [ν.σ_eq]
  refine val_vF hν hs _ x₀.left (fun k => ?_) (congrArg (·.left) hx)
  fin_cases k
  · exact (congrArg (_ ≫ ·) (Over.w ι[D.P.A])).trans (Over.w x₀)
  · exact (congrArg (_ ≫ ·) (Category.id_comp _)).trans (Over.w x₀)

theorem val_th (hν : ν.Integral S) (hs : spMap S.subtype ≫ s = (TF (R := R) C).hom)
    (x : N.A) : N.th x ∈ S := by
  obtain ⟨x₀, hx⟩ := exists_ext hν hs (ν.eA x)
  have h := congrArg S.valuation (ν.th_eq x)
  rw [map_mul, val_rig hν hs, _root_.mul_one] at h
  rw [← S.valuation_le_one_iff, h, S.valuation_le_one_iff]
  exact val_sF hν hs _ x₀.left (fun _ => (congrArg (_ ≫ ·) (Category.id_comp _)).trans (Over.w x₀))
    (congrArg (·.left) hx)

theorem val_psi (hν : ν.Integral S) (hs : spMap S.subtype ≫ s = (TF (R := R) C).hom)
    (χ : D.X) (hχ : PsiUnitOn D χ Set.univ) : S.valuation (vF (D.psi χ) (jFK (R := R) C) ν.J) = 1 := by
  have e : jFK (R := R) C ≫ D.xK χ = spMap S.subtype ≫ s ≫ (D.c χ).left := by
    rw [← Category.assoc, hs]
    exact (Category.assoc _ _ _).symm
  have h1 := chart_int hν hs (s ≫ (D.c χ).left)
    ((Category.assoc _ _ _).trans ((congrArg (s ≫ ·) (Over.w (D.c χ))).trans (Category.comp_id _)))
  rw [← e] at h1
  have h2 : s (IsLocalRing.closedPoint S) ∈ ((D.c χ).left ⁻¹ᵁ D.P.L.U (ν.J (jFK (R := R) C ≫ D.xK χ)) : (Sp R).Opens) :=
    h1 (Set.mem_univ _)
  obtain ⟨_, ⟨V, hV, rfl⟩, hy, hle⟩ := (Sp R).isBasis_affineOpens.exists_subset_of_mem_open h2 (TopologicalSpace.Opens.isOpen _)
  have h3 : ⊤ ≤ s ⁻¹ᵁ V := ((IsLocalRing.closedPoint_mem_iff (s ⁻¹ᵁ V)).1 hy).ge
  have h : jK R ⁻¹ᵁ V ≤ (LB.LinComb D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => -1)).U
      (fun _ => ν.J (jFK (R := R) C ≫ D.xK χ)) := fun y hy => Set.mem_iInter.2 fun _ => hle hy
  obtain ⟨r, hr, er⟩ := hχ (fun _ => ν.J (jFK (R := R) C ≫ D.xK χ)) V hV (Set.subset_univ _) hle h
  have hs' : jFK (R := R) C ≫ jK R = spMap S.subtype ≫ s := hs.symm
  have h4 : ⊤ ≤ jFK (R := R) C ⁻¹ᵁ (jK R ⁻¹ᵁ V) := by
    change ⊤ ≤ (jFK (R := R) C ≫ jK R) ⁻¹ᵁ V
    rw [hs']
    exact fun q _ => h3 (Set.mem_univ (spMap S.subtype q))
  have a := valF_res' h h4 ((D.psi χ).s _).val
  rw [Scheme.Hom.app_eq_appLE] at er
  refine (congrArg S.valuation (a.symm.trans ((congrArg (valF _ _) er.symm).trans
    (valF_appLE' (jK R) V le_rfl h4 r)))).trans ?_
  exact (congrArg (fun q => S.valuation (valF q V r)) hs').trans (val_valF_unit s V h3 r hr)

theorem val_ψ (hν : ν.Integral S) (hs : spMap S.subtype ≫ s = (TF (R := R) C).hom)
    (χ : N.X) (hχ : PsiUnitOn D (ν.eX χ) Set.univ) : S.valuation ((N.ψ χ : C)) = 1 := by
  rw [ν.ψ_eq, map_mul, val_rig hν hs, val_psi hν hs _ hχ, _root_.mul_one]
end Geo

theorem integral_values : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (S : ValuationSubring F), (∀ r : R, algebraMap (FractionRing R) F (algebraMap R _ r) ∈ S) → ∀ (N : NumD F) (ν : NumOf D F N), ν.Integral S → (∀ x y u, S.valuation (N.θ x y u : F) = 1) ∧ (∀ x, S.valuation (N.σ x : F) = 1) ∧ (∀ x, N.th x ∈ S) ∧ ((∀ y, PsiUnitOn D y Set.univ) → ∀ χ, S.valuation (N.ψ χ : F) = 1) := by
  intro R _ _ D F _ _ S hR N ν hν
  obtain ⟨s, hs⟩ := exists_base (R := R) (S := S) hR
  exact ⟨val_θ hν hs, val_σ hν hs, val_th hν hs, fun h χ => val_ψ hν hs χ (h _)⟩

end GlobalTheory.Ex.UnitVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsThetaPtDown
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.ThetaNest
open ThetaCoord CommPairing GlobalLift

variable {S : Scheme.{0}} {T : Over S}

theorem isThetaPt_of_over (P : PolAV S) [Subsingleton T.left] {k : ℕ} {I : Type} {x : I → (T ⟶ P.A)}
    {v : I → Γ(T.left, ⊤)} (ho : Odd k) (hu : IsUnit (k : Γ(T.left, ⊤))) (H : IsThetaPtOver P k x v) :
    IsThetaPt P k x v := by
  refine ⟨ho, hu, fun p => ⟨⊤, trivial, ?_⟩⟩
  obtain ⟨h, hh⟩ := exists_section (T := T) (V := ⊤) (p := p) trivial
  have hi : overResι (T := T) ⊤ ≫ h = 𝟙 _ := by
    haveI : Mono (overResι (T := T) ⊤) := Over.mono_of_mono_left _ (hk := inferInstanceAs (Mono (⊤ : T.left.Opens).ι))
    rw [← cancel_mono (overResι (T := T) ⊤), Category.assoc, hh, Category.comp_id, Category.id_comp]
  exact isThetaPtOver_pull P H _ h hi

theorem weilIs_one_left (hG : GlobalFnsSt) (P : PolAV S) {k : ℤ} {ν : LB.Gen (negLB P.A P.L k T)} (hν : ν.IsGen)
    (θ : ThetaGrp P.A P.L k T) : WeilIs P.A P.L k 1 θ.pt 1 := by
  obtain ⟨o, ho, hv⟩ := exists_symLift_one P.isLB hν 1
  rw [← ho.pt_eq]
  refine weilIs_of_commIsOf hG P.isAb P.isLB ((commIsOf_iff P.isLB _ _ _).2 fun Z r z J hJ => ?_)
  have e : translT P.A (1 : T ⟶ P.A) = 𝟙 _ := by
    rw [translT, ThetaAct.translPt_one, lift_fst_snd]
  rw [hv _ _ z J hJ, hv _ _ z J hJ, ho.pt_eq, e, map_one]
  simp

theorem isThetaPtOver_down (hG : GlobalFnsSt) (P : PolAV S) [Subsingleton T.left] {n m : ℕ} (ho : Odd (n * m))
    {I : Type} {x : I → (T ⟶ P.A)} {v v' : I → Γ(T.left, ⊤)} (hx : ∀ i, (x i ^ n) ^ m ^ 2 = 1)
    (H : IsThetaPtOver P (n * m) x v) (H' : IsThetaPtOver P m (fun i => x i ^ n) v') :
    IsThetaPtOver P m (fun i => x i ^ n) v := by
  rcases isEmpty_or_nonempty I with hI | ⟨⟨i₀⟩⟩
  · rwa [Subsingleton.elim v v']
  obtain ⟨th', s', α', τ', W, t', w', u', hth', hα', hτ', hs', hW, ht', hw', hv⟩ := H
  obtain ⟨th, s, α, τ, U, t, -, -, hth, hα, hτ, hs, hU, ht, -, -⟩ := H'
  obtain ⟨ρ, hρ⟩ := exists_unit_of_isGenSec hth hth'
  obtain ⟨ν, hν, -⟩ := (hW i₀).sym
  obtain ⟨o, hoo, -⟩ := exists_symLift_one P.isLB hν ((n * m) ^ 2)
  obtain ⟨u, hu⟩ := exists_unit_isValueAt hG P.isAb P.isLB (r := n) (q := m ^ 2) rfl
    (pow_dvd_pow_of_dvd (Dvd.intro_left n rfl) 2) ho.pow hρ hα hα' hs hs' hτ' (one_pow n) hoo hτ
  refine ⟨th, s, α, τ, U, t, fun i => ρ * u * w' i, u' * (ρ * u)⁻¹, hth, hα, hτ, hs, hU, ht, fun i => ?_, fun i => ?_⟩
  · have := hu (x i) (U i) (t i) (W i) (t' i) (w' i) 1
      (by rw [show (n * m) ^ 2 = n * m ^ 2 * n by ring, pow_mul, pow_mul, hx, one_pow]) (hU i) (ht i)
      (by rw [_root_.mul_one]; exact hW i) (ht' i) (hw' i)
      (by rw [← (hW i).pt_eq]; exact weilIs_one_left hG P hν _)
    rwa [one_pow, Units.val_one, _root_.mul_one] at this
  · rw [hv, ← Units.val_mul, ← _root_.mul_assoc, ← Units.val_mul, inv_mul_cancel_right]

theorem isThetaPt_down : Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Sp K)) (n m : ℕ) (Ix : Type)
    (x : Ix → (baseOver (Sp K) ⟶ P.A)) (v : Ix → Γ((baseOver (Sp K)).left, ⊤)),
    (∀ i, (x i ^ n) ^ m ^ 2 = 1) → IsThetaPt P (n * m) x v → IsThetaPt P m (fun i => x i ^ n) v := by
  intro hL K _ _ P n m Ix x v hx H
  haveI : Subsingleton (baseOver (Sp K)).left := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  haveI : Nonempty (baseOver (Sp K)).left := inferInstanceAs (Nonempty (PrimeSpectrum K))
  have ho : Odd m := (Nat.odd_mul.1 H.1).2
  have hu : IsUnit (m : Γ((baseOver (Sp K)).left, ⊤)) :=
    isUnit_of_mul_isUnit_right (by rw [← Nat.cast_mul]; exact H.2.1)
  have hK : (m : K) ≠ 0 := by
    have := IsUnit.map (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom hu
    rw [map_natCast] at this
    exact this.ne_zero
  obtain ⟨v', H'⟩ := ThetaPtExist.exists_isThetaPt hL K P m ho hK (fun i => x i ^ n) hx
  exact isThetaPt_of_over P ho hu (isThetaPtOver_down hL.globalFns P H.1 hx (isThetaPtOver_of_subsingleton P H)
    (isThetaPtOver_of_subsingleton P H'))

end GlobalTheory.ThetaNest
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.QvalAddTower
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.NestQVal

attribute [local instance] GlobalTheory.TorusExt.gtGroup

theorem pt_nsmul {R : Type} [CommRing R] [IsDomain R] {D₀ : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
    {N : NumD F} (ν : NumOf D₀ F N) (h1 : ∀ g, ∃! c, ν.Pt g c)
    (h2 : ∀ g g' g'' c c' c'', ν.Pt g c → ν.Pt g' c' → ν.Pt g'' c'' → (GtPtF.IsAdd g g' g'' ↔ c'' = c * c'))
    {g : GtPtF D₀ F} {c : N.Gt} (hc : ν.Pt g c) (m : ℕ) : ν.Pt (m • g) (c ^ m) := by
  induction m with
  | zero =>
    obtain ⟨z, hz, -⟩ := h1 0
    have e : z = z * z := (h2 0 0 0 z z z hz hz hz).1 ((GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).2 (add_zero _).symm)
    have e' : z = 1 := left_eq_mul.1 e
    rw [zero_nsmul, pow_zero, ← e']
    exact hz
  | succ m ih =>
    obtain ⟨z, hz, -⟩ := h1 ((m + 1) • g)
    have e : z = c ^ m * c :=
      (h2 _ _ _ _ _ _ ih hc hz).1 ((GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).2 (succ_nsmul g m))
    rw [pow_succ, ← e]
    exact hz

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField in
open scoped CategoryTheory.Obj BigOperators in
attribute [local instance] Over.cartesianMonoidalCategory in
attribute [local instance] _root_.GlobalTheory.TorusExt.gtGroup in

theorem _root_.GlobalTheory.NestQVal.qval_add_tower : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H), ∀ (R : Type) [CommRing R] [IsDomain R] (D₀ : _root_.ReciprocityTheory.ChartRestriction.G.Out.DegPre R) [Module (𝓞 E) D₀.X] (oa : letI := H.starRing; D₀.OAct (𝓞 E)), D₀.PsiEven → D₀.TauBimult → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (I : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.TateIsoQ D D₀ oa F) (N : _root_.GlobalTheory.Ex.NumD F) (ν : _root_.GlobalTheory.Ex.NumOf D₀ F N) (q : ∀ n : ℕ, D.La → N.QT n), (∀ g, ∃! c, ν.Pt g c) → (∀ g g' g'' c c' c'', ν.Pt g c → ν.Pt g' c' → ν.Pt g'' c'' → (_root_.ReciprocityTheory.ChartRestriction.G.Out.GtPtF.IsAdd g g' g'' ↔ c'' = c * c')) → (∀ k, (∀ p : _root_.ReciprocityTheory.ChartRestriction.G.Out.QkPt D₀ F k, ∃! q, ν.QPt p q) ∧ ∀ (p p' : _root_.ReciprocityTheory.ChartRestriction.G.Out.QkPt D₀ F k) q q', ν.QPt p q → ν.QPt p' q' → (_root_.ReciprocityTheory.ChartRestriction.G.Out.QkPt.Equiv D₀ F p p' ↔ N.QEq q q')) → (∀ n a, ν.QPt (I.ev n a) (q n a)) → (∀ n, 0 < n → ∀ a b, N.QEq (q n a * q n b) (q n (a + b))) ∧ ∀ n m, 0 < n → 0 < m → ∀ a (p : N.QT n), p.1.1 = (q (n * m) a).1.1 → p.1.2 = (q (n * m) a).1.2 ^ m → N.QEq p (q n a) := by
  intro E _ _ _ H D R _ _ D₀ _ oa _ _ F _ _ _ I N ν q hPt hAdd hQ hev

  have hzero : ν.Pt 0 1 := by
    obtain ⟨c, hc, -⟩ := hPt 0
    have h := (hAdd 0 0 0 c c c hc hc hc).1 ((_root_.GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).2 (add_zero 0).symm)
    have : c = 1 := by simpa using (mul_eq_left.1 h.symm)
    simpa [this] using hc
  have hsmul : ∀ (m : ℕ) g c, ν.Pt g c → ν.Pt (m • g) (c ^ m) := by
    intro m g c hc
    induction m with
    | zero => simpa using hzero
    | succ k ih =>
      obtain ⟨c', hc', -⟩ := hPt ((k + 1) • g)
      have h := (hAdd _ _ _ _ _ _ ih hc hc').1 ((_root_.GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).2 (succ_nsmul g k))
      simpa [h, pow_succ] using hc'
  refine ⟨fun n hn a b => ?_, fun n m hn hm a p hp1 hp2 => ?_⟩
  · obtain ⟨r, hry, hrg, hr⟩ := I.add n hn a b
    obtain ⟨hya, hga⟩ := hev n a
    obtain ⟨hyb, hgb⟩ := hev n b
    obtain ⟨c'', hc'', -⟩ := hPt r.g
    have hc := (hAdd _ _ _ _ _ _ hga hgb hc'').1 hrg
    have hrs : ν.QPt r (q n a * q n b) := by
      refine ⟨?_, ?_⟩
      · simp [hry, ← hya, ← hyb]
      · simpa [hc] using hc''
    exact ((hQ n).2 _ _ _ _ hrs (hev n (a + b))).1 hr
  · obtain ⟨Q, hQy, hQg, hQe⟩ := I.tower n m hn hm a
    obtain ⟨hy, hg⟩ := hev (n * m) a
    have hQp : ν.QPt Q p := by
      refine ⟨?_, ?_⟩
      · rw [hQy, ← hy, hp1]
      · rw [(_root_.GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).1 hQg, hp2]
        exact hsmul m _ _ hg
    exact ((hQ n).2 _ _ _ _ hQp (hev n a)).1 hQe

end GlobalTheory.NestQVal
end

