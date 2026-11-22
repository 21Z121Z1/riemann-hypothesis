import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0092
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0177
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0010
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0173
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0131
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0021
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0001
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0015
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0178
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0003
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsGeometricPoint
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverOfIsIso
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0179
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLevelIsometryOfDenseGeometricPoints
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.LevelSpread

theorem exists_closed_eq {S : Scheme.{0}} {Z A : Over S} [IsSeparated A.hom] (u u' : Z ⟶ A) :
    ∃ C : Set Z.left, IsClosed C ∧ ∀ (K : Type) [Field K] (x : Sp K ⟶ S) (h : Over.mk x ⟶ Z),
      h ≫ u = h ≫ u' ↔ Set.range h.left ⊆ C := by
  have : IsClosedImmersion (equalizer.ι u u').left := inferInstance
  refine ⟨Set.range (equalizer.ι u u').left, (Scheme.Hom.isClosedEmbedding _).isClosed_range,
    fun K _ x h => ⟨fun e => ?_, fun e => ?_⟩⟩
  · rintro _ ⟨p, rfl⟩
    refine ⟨(equalizer.lift h e).left p, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, equalizer.lift_ι]
  · have : IsReduced (Over.mk x).left := inferInstanceAs (IsReduced (Sp K))
    obtain ⟨f, hf⟩ := exists_lift_closedImmersion_of_dense (equalizer.ι u u').left h.left Set.univ dense_univ
      fun p _ => e ⟨p, rfl⟩
    apply Over.OverMorphism.ext
    rw [Over.comp_left, Over.comp_left, ← hf, Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left,
      equalizer.condition]

theorem appTop_eq_zero_iff {Z : Scheme.{0}} (f : Γ(Z, ⊤)) {K : Type} [Field K] (h : Sp K ⟶ Z) :
    h.appTop.hom f = 0 ↔ Set.range h ⊆ (Z.basicOpen f : Set Z)ᶜ := by
  rw [← basicOpen_eq_bot_iff, ← Scheme.preimage_basicOpen_top, eq_bot_iff]
  constructor
  · rintro e _ ⟨p, rfl⟩ hp
    exact e hp
  · intro e p hp
    exact e ⟨p, rfl⟩ hp

theorem map_fnOn_apply {L k : Type} [CommRing L] [CommRing k] {T : Scheme.{0}} (g : T ⟶ Sp L) (h : Sp k ⟶ T)
    (β : L →+* k) (e : h ≫ g = spMap β) (c : L) :
    h.appTop.hom (LevCover.fnOn g c) = (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom (β c) := by
  have h1 : (h ≫ g).appTop = g.appTop ≫ h.appTop := Scheme.Hom.comp_appTop _ _
  have h2 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β)
  have h3 := congrArg (fun φ => φ.hom c) h2
  rw [e] at h1
  have h4 := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of L)).inv.hom c)) h1
  exact h4.symm.trans h3.symm

theorem exists_unitOn {K : Type} [CommRing K] (c : Γ(Sp K, ⊤)ˣ) : ∃ ζ : Kˣ, c = unitOn ζ := by
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.toMonoidHom c, Units.ext ?_⟩
  exact ((Scheme.ΓSpecIso (CommRingCat.of K)).hom_inv_id_apply c).symm

theorem pow_eq_iff {L K : Type} [CommRing L] [Field K] {T : Scheme.{0}} (g : T ⟶ Sp L) (h : Sp K ⟶ T)
    (β : L →+* K) (e : h ≫ g = spMap β) (z : L) (c : Γ(T, ⊤)ˣ) (ζ : Kˣ) (m : ℕ)
    (hc : Units.map h.appTop.hom.toMonoidHom c = unitOn ζ) :
    (ζ : K) ^ m = β z ↔ Set.range h ⊆ (T.basicOpen ((c : Γ(T, ⊤)) ^ m - LevCover.fnOn g z) : Set T)ᶜ := by
  have h1 : h.appTop.hom c = (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom ζ := congrArg Units.val hc
  rw [← appTop_eq_zero_iff, map_sub, map_pow, h1, map_fnOn_apply g h β e, ← map_pow, sub_eq_zero]
  exact ((Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.injective.eq_iff).symm

end GlobalTheory.LevelSpread

namespace GlobalTheory

open LevelSpread

theorem exists_levelIsometry_of_dense : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (S : Scheme.{0}) (P : Out.PolAV S) (act : 𝓞 E → (P.A ⟶ P.A)) (o : Type) [CommRing o] (s : S ⟶ Sp o) (z : o) (κ : Type) (lam : κ → D.La) (pt : κ → (Out.baseOver S ⟶ P.A)) (n m : ℕ), 0 < n → Dense {p : S | ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ S) (β : o →+* K) (ζ : Kˣ) (ev : D.La → (Over.mk x ⟶ P.A)), (n : K) ≠ 0 ∧ p ∈ Set.range x ∧ x ≫ s = spMap β ∧ IsPrimitiveRoot ζ n ∧ (∀ a c, ev (a + c) = ev a * ev c) ∧ (∀ a, ev a ^ n = 1) ∧ (∀ (c : 𝓞 E) a, ev (c • a) = ev a ≫ act c) ∧ (∀ a c, Out.WeilIs P.A P.L n (ev a) (ev c) (unitOn (ζ ^ D.EF a c))) ∧ (ζ : K) ^ m = β z ∧ ∀ i, ev (lam i) ^ m = (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) ≫ pt i} → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (β : o →+* K), (n : K) ≠ 0 → x ≫ s = spMap β → ∃ (ζ : Kˣ) (ev : D.La → (Over.mk x ⟶ P.A)), IsPrimitiveRoot ζ n ∧ (∀ a c, ev (a + c) = ev a * ev c) ∧ (∀ a, ev a ^ n = 1) ∧ (∀ (c : 𝓞 E) a, ev (c • a) = ev a ≫ act c) ∧ (∀ a c, Out.WeilIs P.A P.L n (ev a) (ev c) (unitOn (ζ ^ D.EF a c))) ∧ (ζ : K) ^ m = β z ∧ ∀ i, ev (lam i) ^ m = (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) ≫ pt i := by
  intro hL E _ _ _ H D S P act o _ s z κ lam pt n m hn hD K _ _ x β hK hx
  obtain ⟨hfree, hfin⟩ := LevCover.datum_free D
  have := P.isAb.comm
  have := P.isAb.proper
  obtain ⟨Z, et, c, hu, hadd, hpow, hc, hprim, hrep, hlast⟩ := GlobalTheory.T.exists_finite_scheme_latticeTorsionHom_primitiveRoot S P.A n D.La P.isAb hn
  choose C1 hC1 HC1 using fun (b : 𝓞 E) (a : D.La) => exists_closed_eq (et (b • a)) (et a ≫ act b)
  choose C2 hC2 HC2 using fun (a a' : D.La) => GlobalTheory.exists_clopen_weilIs_iff hL S P n Z (et a) (et a')
    (c ^ D.EF a a') hn hu (hpow _) (hpow _)
    (by rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc, one_zpow])
  let q : Z ⟶ Out.baseOver S := Over.homMk Z.hom (by simp)
  choose C4 hC4 HC4 using fun i : κ => exists_closed_eq (et (lam i) ^ m) (q ≫ pt i)
  let C3 : Set Z.left := (Z.left.basicOpen ((c : Γ(Z.left, ⊤)) ^ m - LevCover.fnOn (Z.hom ≫ s) z) : Set Z.left)ᶜ
  let C : Set Z.left := (⋂ b, ⋂ a, C1 b a) ∩ (⋂ a, ⋂ a', (C2 a a' : Set Z.left)) ∩ C3 ∩ ⋂ i, C4 i
  have hC : IsClosed C :=
    (((isClosed_iInter fun b => isClosed_iInter fun a => hC1 b a).inter
      (isClosed_iInter fun a => isClosed_iInter fun a' => hC2 a a')).inter
      (Z.left.basicOpen _).isOpen.isClosed_compl).inter (isClosed_iInter hC4)
  have key : ∀ (K : Type) [Field K] (x : Sp K ⟶ S) (β : o →+* K) (ζ : Kˣ) (h : Over.mk x ⟶ Z), x ≫ s = spMap β →
      Units.map h.left.appTop.hom.toMonoidHom c = unitOn ζ →
      (((∀ (b : 𝓞 E) a, h ≫ et (b • a) = (h ≫ et a) ≫ act b) ∧
        (∀ a a', Out.WeilIs P.A P.L n (h ≫ et a) (h ≫ et a') (unitOn (ζ ^ D.EF a a'))) ∧ (ζ : K) ^ m = β z ∧
        ∀ i, (h ≫ et (lam i)) ^ m = (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) ≫ pt i) ↔
        Set.range h.left ⊆ C) := by
    intro K _ x β ζ h hx hζ
    have hw : h.left ≫ Z.hom = x := Over.w h
    have hq : h ≫ q = (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) := Over.OverMorphism.ext hw
    have h3 := pow_eq_iff (Z.hom ≫ s) h.left β (by rw [← Category.assoc, hw, hx]) z c ζ m hζ
    have hz : ∀ k : ℤ, unitOn (ζ ^ k) = Units.map h.left.appTop.hom.toMonoidHom (c ^ k) := fun k => by
      rw [map_zpow, hζ, unitOn, unitOn, map_zpow]
    simp only [C, Set.subset_inter_iff, Set.subset_iInter_iff, and_assoc]
    refine and_congr (forall₂_congr fun b a => ?_) (and_congr (forall₂_congr fun a a' => ?_)
      (and_congr h3 (forall_congr' fun i => ?_)))
    · rw [← HC1 b a K x h, Category.assoc]
    · rw [← HC2 a a' _ h, hz]
    · rw [← HC4 i K x h, ← hq, Category.assoc, MonObj.comp_pow]
  have hdense : Dense (Z.hom '' C) := by
    refine hD.mono ?_
    rintro _ ⟨K, _, x, β, ζ, ev, hK, ⟨p, rfl⟩, hx, h1, h2, h3, h4⟩
    obtain ⟨h, hh, hζ⟩ := hrep K x ev ζ hK h2 h3 h1
    obtain rfl : (fun a => h ≫ et a) = ev := funext hh
    have hw : h.left ≫ Z.hom = x := Over.w h
    exact ⟨h.left p, (key K x β ζ h hx hζ).1 h4 ⟨p, rfl⟩, by rw [← Scheme.Hom.comp_apply, hw]⟩
  obtain ⟨h, hh⟩ := hlast C hC K x hK (by rw [hdense.closure_eq]; exact Set.subset_univ _)
  obtain ⟨ζ, hζ⟩ := exists_unitOn (K := K) (Units.map h.left.appTop.hom.toMonoidHom c)
  exact ⟨ζ, fun a => h ≫ et a, hprim K h.left ζ hζ, fun a a' => by beta_reduce; rw [hadd, MonObj.comp_mul],
    fun a => by beta_reduce; rw [← MonObj.comp_pow, hpow, MonObj.comp_one], (key K x β ζ h hx hζ).2 hh⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPolarisationFormOfLineBundle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

noncomputable section
namespace GlobalTheory.BundleForm

section
variable {Pic : Scheme.{0} → Type 1} [∀ X, CommGroup (Pic X)]
  (pl : ∀ {X Y : Scheme.{0}}, (Y ⟶ X) → (Pic X →* Pic Y))
  {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

def lam (c : Pic A.left) {T : Over S} (a b : T ⟶ A) : Pic T.left :=
  pl (a * b).left c * pl (1 : T ⟶ A).left c / (pl a.left c * pl b.left c)

theorem lam_one_left (c : Pic A.left) {T : Over S} (b : T ⟶ A) : lam @pl c 1 b = 1 := by
  simp [lam, _root_.mul_comm]

theorem lam_one_right (c : Pic A.left) {T : Over S} (a : T ⟶ A) : lam @pl c a 1 = 1 := by
  simp [lam]

theorem lam_comm (c : Pic A.left) {T : Over S} (a b : T ⟶ A) : lam @pl c a b = lam @pl c b a := by
  unfold lam
  rw [_root_.mul_comm a b, _root_.mul_comm (pl a.left c)]

theorem pl_lam (hc : ∀ (X Y Z : Scheme.{0}) (f : Y ⟶ X) (g : Z ⟶ Y) (c : Pic X), pl (g ≫ f) c = pl g (pl f c))
    (c : Pic A.left) {T T' : Over S} (u : T' ⟶ T) (a b : T ⟶ A) :
    pl u.left (lam @pl c a b) = lam @pl c (u ≫ a) (u ≫ b) := by
  unfold lam
  rw [map_div, map_mul, map_mul, ← hc, ← hc, ← hc, ← hc, ← MonObj.comp_mul, ← MonObj.comp_one u]
  rfl

theorem cl_cube (cl : ∀ {X : Scheme.{0}}, LB X → Pic X)
    (hl : ∀ (X Y : Scheme.{0}) (L : LB X), L.IsLB → ∀ (I : Type) [Fintype I] (φ : I → (Y ⟶ X)) (ε : I → ℤ),
      (LB.LinComb L φ ε).IsLB ∧ cl (LB.LinComb L φ ε) = ∏ k, pl (φ k) (cl L) ^ ε k)
    {L : LB A.left} (hL : L.IsLB) {T : Over S} (a b : T ⟶ A) :
    cl (cubeLB A ![a, b] L) = lam @pl (cl L) a b := by
  unfold cubeLB
  rw [(hl _ _ L hL _ _ _).2, ← Equiv.ulift.symm.prod_comp]
  have e : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide
  rw [e, Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  have e0 : psum A ![a, b] ∅ = 1 := rfl
  have e1 : psum A ![a, b] {0} = a := _root_.mul_one a
  have e2 : psum A ![a, b] {1} = b := _root_.mul_one b
  have e3 : psum A ![a, b] {0, 1} = a * b := congrArg (a * ·) (_root_.mul_one b)
  simp only [Equiv.ulift_symm_down, e0, e1, e2, e3, lam]
  simp [div_eq_mul_inv, _root_.mul_comm, _root_.mul_left_comm, _root_.mul_assoc]

theorem eq_of_lam_eq (cl : ∀ {X : Scheme.{0}}, LB X → Pic X)
    (h1 : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → (cl L = 1 ↔ ∃ t : LB.Gen L, t.IsGen))
    (hc : ∀ (X Y Z : Scheme.{0}) (f : Y ⟶ X) (g : Z ⟶ Y) (c : Pic X), pl (g ≫ f) c = pl g (pl f c))
    (hl : ∀ (X Y : Scheme.{0}) (L : LB X), L.IsLB → ∀ (I : Type) [Fintype I] (φ : I → (Y ⟶ X)) (ε : I → ℤ),
      (LB.LinComb L φ ε).IsLB ∧ cl (LB.LinComb L φ ε) = ∏ k, pl (φ k) (cl L) ^ ε k)
    {L : LB A.left} (hL : L.IsLB) (hK : Out.KTriv A L) {T : Over S} (y y' : T ⟶ A)
    (h : lam @pl (cl L) (fst T A ≫ y) (snd T A) = lam @pl (cl L) (fst T A ≫ y') (snd T A)) : y = y' := by
  let τ : T ⊗ A ⟶ T ⊗ A := lift (fst T A) ((fst T A ≫ y')⁻¹ * snd T A)
  have h' := congrArg (pl τ.left) h
  rw [pl_lam @pl hc, pl_lam @pl hc, ← Category.assoc, ← Category.assoc, lift_fst, lift_snd] at h'
  have et : Out.translPt A (y * y'⁻¹) = (fst T A ≫ y) * ((fst T A ≫ y')⁻¹ * snd T A) := by
    change (fst T A ≫ (y * y'⁻¹)) * snd T A = _
    rw [MonObj.comp_mul, GrpObj.comp_inv, _root_.mul_assoc]
  unfold lam at h'
  rw [← et, mul_inv_cancel_left] at h'
  have H : KerPow.HasGen L (K := Fin 4) ![(Out.translPt A (y * y'⁻¹)).left, (snd T A).left,
      (fst T A).left ≫ y.left, (fst T A).left ≫ y'.left] ![1, -1, -1, 1] := by
    refine (h1 _ _ (hl _ _ L hL _ _ _).1).1 ?_
    rw [(hl _ _ L hL _ _ _).2, Fin.prod_univ_four]
    have aux : ∀ a b c d e f : Pic (T ⊗ A).left, a * e / (c * f) = b * e / (d * f) →
        a ^ (1 : ℤ) * b ^ (-1 : ℤ) * c ^ (-1 : ℤ) * d ^ (1 : ℤ) = 1 := fun a b c d e f k => by
      have k' := congrArg Additive.ofMul k
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_div, ofMul_zpow, ofMul_one] at k' ⊢
      linear_combination (norm := module) k'
    exact aux _ _ _ _ _ _ h'
  have H' : KerPow.LocGen L (K := Fin 4) (fst T A).left ![(Out.translPt A (y * y'⁻¹)).left, (snd T A).left,
      (fst T A).left ≫ y.left, (fst T A).left ≫ y'.left] ![1, -1, -1, 1] :=
    fun _ => ⟨⊤, trivial, H.pull _ fun _ => rfl⟩
  have B := BoxKernel.locGen_base hL (fst T A).left (K := Fin 2) ![y.left, y'.left] ![-1, 1]
  refine mul_inv_eq_one.1 (KerPow.eq_one_of_locGen hK _ (H'.comb hL B fun U _ g => ?_))
  simp [Fin.prod_univ_four, Fin.prod_univ_two]

end

theorem exists_formIs : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M : LB P.A.left), M.IsLB → ∃ s : P.A ⟶ P.A, FormIs P M s := by
  intro hA hB K _ _ P M hM
  obtain ⟨Pic, _, cl, pl, hiso, h1, -, hc, hl, hd⟩ := GlobalTheory.CechPicMul.exists_picardGroup
  have cc := fun {L : LB P.A.left} (hL : L.IsLB) {T : Over (Sp K)} (a b : T ⟶ P.A) => cl_cube @pl @cl hl hL a b
  have ci : ∀ {L : LB P.A.left} (_ : L.IsLB) {T : Over (Sp K)} (a b : T ⟶ P.A), (cubeLB P.A ![a, b] L).IsLB :=
    fun hL _ a b => (hl _ _ _ hL _ _ _).1
  have cp : ∀ {X Y : Scheme.{0}} {L : LB X} (_ : L.IsLB) (f : Y ⟶ X),
      (∃ t : (L.pull f).Gen, t.IsGen) ↔ pl f (cl L) = 1 := fun hL f => by
    rw [← h1 _ _ (hl _ _ _ hL _ _ _).1, (hl _ _ _ hL _ _ _).2, Fintype.prod_unique, zpow_one]
  obtain ⟨hN, eN⟩ := hd _ _ _ (ci P.isLB (fst (P.A ⊗ P.A) P.A ≫ snd _ _) (snd _ _))
    (ci hM (fst (P.A ⊗ P.A) P.A ≫ fst _ _) (snd _ _))
  rw [cc hM, cc P.isLB] at eN
  obtain ⟨Z, i, hi, hZ⟩ := GlobalTheory.SeesawGlobal.exists_closed_triv hA hB K P (P.A ⊗ P.A) _ hN (by
    rw [cp hN, eN, map_div, pl_lam @pl hc, pl_lam @pl hc, lift_snd, lam_one_right, lam_one_right, div_one])

  have hR : ∀ (T : Over (Sp K)) (h : T ⟶ P.A ⊗ P.A),
      lam @pl (cl M) (fst T P.A ≫ h ≫ fst _ _) (snd T P.A) = lam @pl (cl P.L) (fst T P.A ≫ h ≫ snd _ _) (snd T P.A) ↔
        ∃ u : T.left ⟶ Z, u ≫ i = h.left := fun T h => by
    rw [← hZ, cp hN, eN, map_div, pl_lam @pl hc, pl_lam @pl hc, div_eq_one, whiskerRight_snd,
      whiskerRight_fst_assoc, whiskerRight_fst_assoc]
  have uniq := fun {T : Over (Sp K)} (y y' : T ⟶ P.A) => eq_of_lam_eq @pl @cl h1 hc hl P.isLB P.ktriv y y'
  let q : Z ⟶ P.A.left := i ≫ (fst P.A P.A).left
  have w1 : (fst P.A P.A).left ≫ P.A.hom = (P.A ⊗ P.A).hom := Over.w _
  have hmono : Mono q := ⟨fun {W} u v e => by
    let T : Over (Sp K) := Over.mk (u ≫ i ≫ (P.A ⊗ P.A).hom)
    let a : T ⟶ P.A ⊗ P.A := Over.homMk (u ≫ i) (Category.assoc _ _ _)
    let b : T ⟶ P.A ⊗ P.A := Over.homMk (v ≫ i) (by
      have := congrArg (· ≫ P.A.hom) e
      simp only [q, Category.assoc, w1] at this
      exact (Category.assoc _ _ _).trans this.symm)
    have e1 : a ≫ fst _ _ = b ≫ fst _ _ := Over.OverMorphism.ext (by
      simpa only [q, a, b, Over.comp_left, Over.homMk_left, Category.assoc] using e)
    have e2 : a ≫ snd _ _ = b ≫ snd _ _ := uniq _ _ (by
      rw [← (hR T a).2 ⟨u, rfl⟩, ← (hR T b).2 ⟨v, rfl⟩, e1])
    have e3 : a = b := CartesianMonoidalCategory.hom_ext _ _ e1 e2
    exact (cancel_mono i).1 (congrArg (fun z => z.left) e3)⟩
  have := P.isAb.proper
  have : IsProper (fst P.A P.A).left := inferInstanceAs (IsProper (pullback.fst P.A.hom P.A.hom))
  have hq : IsClosedImmersion q := (IsClosedImmersion.iff_isProper_and_mono q).2 ⟨inferInstance, hmono⟩
  obtain ⟨l, hl1, hl2⟩ : ∃ l : ℕ, l.Prime ∧ (l : K) ≠ 0 := by
    by_cases h2 : ((2 : ℕ) : K) = 0
    · refine ⟨3, Nat.prime_three, fun h3 => one_ne_zero (α := K) ?_⟩
      push_cast at h2 h3
      linear_combination h3 - h2
    · exact ⟨2, Nat.prime_two, h2⟩
  have hsurj : Surjective q := ⟨by
    rw [← Set.range_eq_univ, ← q.isClosedEmbedding.isClosed_range.closure_eq]
    refine ((GlobalTheory.PrimePowerTorsion.dense_torsion_and_eq_one hA hB K P l hl1 hl2).1.mono ?_).closure_eq
    refine Set.iUnion₂_subset fun x ⟨j, hj⟩ => ?_
    obtain ⟨y, -, hy⟩ := GlobalTheory.T.exists_torsion_cubeLB_iso_polarisation_translate hA hB K P M (l ^ j) x hM (by push_cast; exact pow_ne_zero _ hl2) hj
    rw [← hiso _ _ _ (ci hM _ _) (ci P.isLB _ _), cc hM, cc P.isLB] at hy
    have hy' := congrArg (pl (snd (𝟙_ (Over (Sp K))) P.A).left) hy
    rw [pl_lam @pl hc, pl_lam @pl hc, Category.comp_id, ← Category.assoc, ← Category.assoc,
      toUnit_unique (_ ≫ _) (fst _ _)] at hy'
    obtain ⟨u, hu⟩ := (hR _ (lift x y)).1 (by rw [lift_fst, lift_snd]; exact hy')
    have e : u ≫ q = x.left := by
      rw [← Category.assoc, hu, ← Over.comp_left, lift_fst]
    rintro _ ⟨z, rfl⟩
    exact ⟨u z, by rw [← e]; rfl⟩⟩
  have := polAV_isIntegral_of_isAlgClosed K P
  have : IsIso q := isIso_of_isClosedImmersion_of_surjective q
  let h : P.A ⟶ P.A ⊗ P.A := Over.homMk (inv q ≫ i) (by
    rw [← w1, Category.assoc, ← Category.assoc i, IsIso.inv_hom_id_assoc])
  have h₁ : h ≫ fst _ _ = 𝟙 _ := Over.OverMorphism.ext (by
    change (inv q ≫ i) ≫ _ = 𝟙 _
    rw [Category.assoc, IsIso.inv_hom_id])
  have key := (hR _ h).2 ⟨inv q, rfl⟩
  rw [h₁, Category.comp_id] at key
  refine ⟨h ≫ snd _ _, hA.rigidity _ _ _ P.isAb P.isAb _ ?_, ?_⟩
  · have e1 : (1 : 𝟙_ (Over (Sp K)) ⟶ P.A) = η[P.A] := by rw [Hom.one_def]; simp
    rw [← e1]
    refine uniq _ _ ?_
    have k := congrArg (pl ((1 : 𝟙_ (Over (Sp K)) ⟶ P.A) ▷ P.A).left) key
    rw [pl_lam @pl hc, pl_lam @pl hc, whiskerRight_snd, whiskerRight_fst_assoc, whiskerRight_fst,
      MonObj.comp_one, lam_one_left] at k
    rw [← k, MonObj.comp_one, lam_one_left]
  · change LBIso (cubeLB P.A ![fst _ _, snd _ _] M) _
    rw [← hiso _ _ _ (ci hM _ _) (ci P.isLB _ _), cc hM, cc P.isLB]
    have k := congrArg (pl (lift (snd P.A P.A) (fst P.A P.A)).left) key
    rw [pl_lam @pl hc, pl_lam @pl hc, lift_fst_assoc, lift_fst, lift_snd] at k
    rw [lam_comm, k, lam_comm]

end GlobalTheory.BundleForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinrankTangentPELFamilyLeSymmetricDomainStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_tangent_PEL_family_le_symmetricDomain : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La), 1 ≤ D.p + D.q → IsSympBasis D bas → a w = H.w0 → a w' = H.bar H.w0 → Subring.closure (Set.range a) = ⊤ → ∀ (N' : ℕ) (o : Type) [CommRing o] (b : TBase o (N' ^ 2)) (ρ : o) (R : Type) [CommRing R] [Algebra o R] [Algebra o ℂ] [Algebra R ℂ] [IsScalarTower o R ℂ] (t : TObj g (N' ^ 2) J b (spMap (algebraMap o R))) (τ : SAB H (Sp R)), ρ ^ 2 = -(H.d : o) → IsPEL D a bas ρ t τ → Algebra.FiniteType o R → (∀ (x : Sp (DualNumber ℂ) ⟶ Sp R) (t' : TObj g (N' ^ 2) J b (x ≫ spMap (algebraMap o R))), x ≫ spMap (algebraMap o R) = constPt x ≫ spMap (algebraMap o R) → TMap t' t x → TMap t' t (constPt x) → x = constPt x) → Module.finrank ℂ (Derivation o R ℂ) ≤ D.dim := by
  first | exact @GlobalTheory.PelTan.finrank_derivation_le | exact GlobalTheory.PelTan.finrank_derivation_le | (intros; apply GlobalTheory.PelTan.finrank_derivation_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThEqClassicalThetaFunctionValuesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasTh_eq_classicalThetaFunction_values : Out.Laws → Out.Laws2 → ThetaUnifAV → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (t : TObj g (N' ^ 2) J b (spMap em)) (u : HolUnif t.A t.L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (θ : (Fin g → ℂ) → ℂ) (lam : Fin (2 * g) → u.Λ), Odd N' → u.IsAH Hm χ → u.IsThetaFn Hm χ 1 θ → θ ≠ 0 → (∀ i, (t.pt i).left = (u.ex (((N' : ℂ) ^ 2)⁻¹ • (lam i : Fin g → ℂ))).left) → t.HasTh (𝟙 _) (fun a => χ (∑ i, ((a i).val : ℤ) • lam i) * Complex.exp (-(Real.pi / 2 / (N' : ℂ) ^ 2) * hermForm Hm (∑ i, ((a i).val : ℂ) • (lam i : Fin g → ℂ)) (∑ i, ((a i).val : ℂ) • (lam i : Fin g → ℂ))) * θ ((N' : ℂ)⁻¹ • ∑ i, ((a i).val : ℂ) • (lam i : Fin g → ℂ))) := by
  first | exact @GlobalTheory.ThetaClassical.hasTh_classical | exact GlobalTheory.ThetaClassical.hasTh_classical | (intros; apply GlobalTheory.ThetaClassical.hasTh_classical <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HomExtensionSemiAbelianDiscreteValuationRingStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homExtension_semiAbelian_discreteValuationRing : GlobalTheory.LN.HomExtSt := by
  first | exact @GlobalTheory.homExtension_semiAbelian_dvr | exact GlobalTheory.homExtension_semiAbelian_dvr | (intros; apply GlobalTheory.homExtension_semiAbelian_dvr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoOfNoTwoTorsion
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.Models.RankZeroFamily

open RankZero

theorem isIso_of_no_two_torsion {R : Type} [CommRing R] [IsDomain R] [CharZero R] {S : Scheme.{0}} [IsReduced S]
    (s : S ⟶ Sp R) [Flat s] (G : Over S) [GrpObj G] (hG : IsAbelianScheme G)
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ S) (g : Over.mk x ⟶ G), g ^ 2 = 1 → g = 1) :
    IsIso G.hom := by
  have := hG.proper
  have := hG.smooth
  have := hG.comm
  have : IsReduced G.left := isReduced_of_smooth_of_isReduced G.hom
  have hcl := isClosedImmersion_of_section_of_isSeparated G.hom (eSec G) (section_w η[G])
  have hs : Surjective (eSec G) := by
    refine ⟨fun y => ?_⟩
    obtain ⟨k, _, _, _, u, q, hu⟩ := FamTest.exists_geom_specializes (G.hom ≫ s) y
    refine (eSec G).isClosedEmbedding.isClosed_range.stableUnderSpecialization hu ?_
    let x := u ≫ G.hom
    have hp := isGrpPullback_pullback G x
    have hB := isAbelianScheme_pullback_obj x G hG
    have := hB.comm
    have ht := h k ((𝟙_ (Over (Sp k))).hom ≫ x)
    have hsB := surjective_unit GlobalTheory.card_torsion_abelianVariety _ hB one_lt_two (by simp) fun g hg => by
      have e := ht (pushHom hp _ g) (by rw [← map_pow, hg, map_one])
      rw [← map_one (pushHom hp (𝟙_ _))] at e
      exact Over.OverMorphism.ext (hp.1.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w]))
    obtain ⟨p, hp'⟩ := hsB (hp.1.lift u (𝟙 _) (Category.id_comp _).symm q)
    refine ⟨x p, ?_⟩
    have e₁ := congrArg (fun q => q p) (cubeMapOf hp).e_comm
    have e₂ := congrArg (fun r => r q) (hp.1.lift_fst u (𝟙 _) (Category.id_comp _).symm)
    exact e₁.symm.trans ((congrArg (pullback.fst G.hom x) hp').trans e₂)
  have : IsIso (eSec G) := isIso_of_isClosedImmersion_of_surjective _
  have : IsIso (eSec G ≫ G.hom) := by
    rw [show eSec G ≫ G.hom = 𝟙 S from section_w η[G]]
    exact inferInstanceAs (IsIso (𝟙 S))
  exact IsIso.of_isIso_comp_left (eSec G) G.hom

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {n N : ℕ}

theorem fullObj_zero (hD : D.p + D.q = 0) {S : Scheme.{0}} (s : S ⟶ Sp (RZ H n N)) :
    FullObj D s (Inhab.zeroTriple H S) (fun _ => 1) := by
  have hz := isIso_zeroTriple (H := H) S
  have := subsingleton_La hD
  refine ⟨Inhab.isProper_zeroTriple S, (Out.Inh.zeroPolAV S).ample, fun _ _ _ _ _ => hom_unique hz _ _,
    fun _ _ => (_root_.mul_one _).symm, fun _ => rfl, fun k _ _ _ x β _ => ?_⟩
  obtain ⟨ζ, h₁, h₂, h₃⟩ := FamTest.exists_roots β
  refine ⟨fun τ => ⟨fun _ => lieMult_zero hz _ _ _ (by omega), fun _ => lieMult_zero hz _ _ _ (by omega)⟩,
    ⟨ζ, h₁, h₂, fun _ _ => 1, fun _ _ _ => hom_unique hz _ _, fun _ _ _ => hom_unique hz _ _,
      fun _ _ _ => ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => rfl⟩,
      fun _ _ _ => ⟨fun _ => ⟨0, hom_unique hz _ _⟩, fun _ => hom_unique hz _ _⟩,
      fun _ _ _ _ _ => hom_unique hz _ _, fun m _ a b => ?_⟩, h₃, fun _ => hom_unique hz _ _⟩
  have e : unitOn (ζ m ^ D.EF a b) = 1 := by
    rw [Subsingleton.elim b 0, map_zero, zpow_zero, unitOn, map_one]
  rw [e]
  exact weilIs_zero hz (Inhab.zeroTriple H S).PP.isLB (triv_rig hz _) _ _ _

theorem isIso_fullObj (hD : D.p + D.q = 0) {S : Scheme.{0}} [IsReduced S] {s : S ⟶ Sp (RZ H n N)} [Flat s]
    {t : SAB H S} {lv : D.La → (𝟙_ (Over S) ⟶ t.G)} (o : FullObj D s t lv) : IsIso t.G.hom := by
  refine isIso_of_no_two_torsion s _ ⟨t.semi.comm, t.semi.smooth, o.proper, t.semi.geomConnected⟩
    fun k _ _ _ x g hg => ?_
  obtain ⟨β, hβ⟩ := exists_spMap (x ≫ s)
  obtain ⟨-, I, -⟩ := o.geom k x β hβ
  have := subsingleton_La hD
  obtain ⟨a, rfl⟩ := (I.onto 2 two_pos g).1 hg
  exact (I.ker 2 two_pos a).2 ⟨0, Subsingleton.elim _ _⟩

theorem famCore (hD : D.p + D.q = 0) (n N : ℕ) :
    FamCore D (𝟙 (Sp (RZ H n N))) (Inhab.zeroTriple H _) (fun _ => 1) := by
  refine ⟨inferInstance, inferInstance, isQProjOver_of_isIso _ inferInstance, inferInstance, fullObj_zero hD _,
    fun S s t lv hr _ hf o => ?_, fun k _ x _ _ _ _ e _ _ => by simpa using e⟩
  have hz := isIso_zeroTriple (H := H) (Sp (RZ H n N))
  obtain ⟨ν⟩ := nonempty_sabMap (isIso_fullObj hD o) hz s
  exact ⟨s, ⟨Category.comp_id _, ν, fun _ => sec_comm hz ν.cart.1.w _ _⟩,
    fun f hf => (Category.comp_id f).symm.trans hf.1⟩

theorem siegClause (hD : D.p + D.q = 0) (hn : n.Prime) {J : ℕ} (hJ : 1 ≤ J) :
    SiegClause D (𝟙 (Sp (RZ H n (n ^ J)))) (Inhab.zeroTriple H _) (fun _ => 1) := by
  intro p hp hpn
  have hz := isIso_zeroTriple (H := H) (Sp (RZ H n (n ^ J)))
  obtain ⟨Ag, bas, e₁, e₂⟩ := siegel_zero (H := H) GlobalTheory.card_torsion_abelianVariety hD
    (g := Module.finrank ℚ E / 2 * (D.p + D.q)) (by rw [hD, mul_zero]) hp (Nat.one_lt_pow (by omega) hn.one_lt)
    (((Nat.coprime_primes hn hp).2 hpn.symm).pow_left J)
  exact ⟨Ag, bas, e₁, fun O _ _ z b _ _ _ T sT f tT ν levT hpb _ => e₂ O z T sT tT levT
    (MorphismProperty.of_isPullback (P := MorphismProperty.isomorphisms _) hpb (inferInstanceAs (IsIso (𝟙 _))))
    (MorphismProperty.of_isPullback (P := MorphismProperty.isomorphisms _) ν.cart.1 hz)⟩

theorem siegRep {p : ℕ} (hp : p.Prime) (h₁ : 1 < N) (hN : N.Coprime p) :
    SiegRep (zeroFamily GlobalTheory.card_torsion_abelianVariety hp h₁ hN) :=
  ⟨isQProjOver_of_isIso _ (inferInstanceAs (IsIso (𝟙 _))), fun _ s o _ _ _ _ =>
    ⟨s, ⟨Category.comp_id _, siegPB_zero (isIso_sieg GlobalTheory.card_torsion_abelianVariety hp h₁ hN o) (isIso_unit _) _⟩,
      fun f hf => (Category.comp_id f).symm.trans hf.1⟩⟩

theorem main : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n J : ℕ), D.p + D.q = 0 → AuxiliaryInertOddPrime H n → 1 ≤ J → FamCore D (𝟙 (Sp (RZ H n (n ^ J)))) (Inhab.zeroTriple H _) (fun _ => 1) ∧ SiegClause D (𝟙 (Sp (RZ H n (n ^ J)))) (Inhab.zeroTriple H _) (fun _ => 1) ∧ ∀ p : ℕ, p.Prime → p ≠ n → ∃ Ag : SiegelFamily 0 p (n ^ J), SiegRep Ag :=
  fun _ _ _ _ _ _ _ _ _ J hD hn hJ => ⟨famCore hD _ _, siegClause hD hn.1 hJ, fun _ hp hpn =>
    ⟨_, siegRep hp (Nat.one_lt_pow (by omega) hn.1.one_lt) (((Nat.coprime_primes hn.1 hp).2 hpn.symm).pow_left J)⟩⟩

end GlobalTheory.Models.RankZeroFamily

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleExtendedPrincipalPolarisationDvrStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relAmple_extended_principalPolarisation_dvr : Laws → Laws2 → ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (P : PolAV (Sp K)) (B : Over (Sp V)) [GrpObj B] [IsCommMonObj B] (M : GlobalTheory.UU.CP B) (φ : P.A.left ⟶ B.left), IsAbelianScheme B → IsGrpPullback P.A B (spMap (algebraMap V K)) φ → LBIso P.L (M.L.L.pull φ) → IsAdicComplete (IsLocalRing.maximalIdeal V) V → RelAmple B M.L.L := by
  first | exact @GlobalTheory.ExtAmple.relAmple_extension | exact GlobalTheory.ExtAmple.relAmple_extension | (intros; apply GlobalTheory.ExtAmple.relAmple_extension <;> assumption)
end

