import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAbelianSchemeAway
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2354
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0564
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.InjectiveOfFlatLocal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0037
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1839
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0143
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0086
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0007
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0005
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0620
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0112
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0668
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProperSemiAbelianFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2341
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2342

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjOfLawUnitInverseAgreeAway
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc.SpreadGrp

theorem grpObj_of_agree : ∀ (R : Type) [CommRing R] [IsDomain R] (f g : R), f ≠ 0 → ∀ (X : Scheme.{0}) (q : X ⟶ Sp R), Flat q → IsSeparated q → ∀ (A : Over (Sp (Localization.Away f))) [GrpObj A], IsCommMonObj A → ∀ i : A.left ⟶ X, IsPullback i A.hom q (awayMap f) → ∀ (H : Over (Sp (Localization.Away g))) (h : H.left ⟶ X), IsPullback h H.hom q (awayMap g) → ∀ (m : H ⊗ H ⟶ H) (n : H ⟶ H) (o : 𝟙_ (Over (Sp (Localization.Away g))) ⟶ H), (∀ (T : Scheme.{0}) (t₁ : T ⟶ Sp (Localization.Away g)) (t₀ : T ⟶ Sp (Localization.Away f)) (a b : Over.mk t₁ ⟶ H) (a' b' : Over.mk t₀ ⟶ A), a.left ≫ h = a'.left ≫ i → b.left ≫ h = b'.left ≫ i → (lift a b ≫ m).left ≫ h = (a' * b').left ≫ i) → (∀ (T : Scheme.{0}) (t₁ : T ⟶ Sp (Localization.Away g)) (t₀ : T ⟶ Sp (Localization.Away f)) (a : Over.mk t₁ ⟶ H) (a' : Over.mk t₀ ⟶ A), a.left ≫ h = a'.left ≫ i → (a ≫ n).left ≫ h = (a'⁻¹).left ≫ i) → (∀ (T : Scheme.{0}) (t₁ : T ⟶ Sp (Localization.Away g)) (t₀ : T ⟶ Sp (Localization.Away f)), t₁ ≫ awayMap g = t₀ ≫ awayMap f → t₁ ≫ o.left ≫ h = (1 : Over.mk t₀ ⟶ A).left ≫ i) → ∃ _ : GrpObj H, MulAgree H A h i := by
  intro R _ _ f g hf X q hq hs A _ _ i hA H h hH m n o hm hn ho
  have hinj : Function.Injective (algebraMap R (Localization.Away f)) :=
    IsLocalization.injective (Localization.Away f) (powers_le_nonZeroDivisors_of_noZeroDivisors hf)
  have : IsSchemeTheoreticallyDominant (awayMap f) :=
    ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective
      (CommRingCat.ofHom (algebraMap R (Localization.Away f))) hinj
  have : Flat (awayMap g) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ (Submonoid.powers g))
  have : Flat H.hom := MorphismProperty.of_isPullback hH hq
  have : IsSeparated H.hom := MorphismProperty.of_isPullback hH hs
  have := ExtUnique.flat_tensorUnit (S := Sp (Localization.Away g))
  have := ExtUnique.flat_tensorObj H H
  have := ExtUnique.flat_tensorObj (𝟙_ _) H
  have := ExtUnique.flat_tensorObj H (𝟙_ _)
  have := ExtUnique.flat_tensorObj (H ⊗ H) H
  let j := pullback.fst (awayMap g) (awayMap f)
  let k := pullback.snd (awayMap g) (awayMap f)
  have w : ∀ T : Over (pullback (awayMap g) (awayMap f)), (T.hom ≫ j) ≫ awayMap g = (T.hom ≫ k) ≫ awayMap f := by
    intro T; simp only [Category.assoc, j, k, pullback.condition]

  have key : ∀ {T : Scheme.{0}} {t₁ : T ⟶ Sp (Localization.Away g)} {t₀ : T ⟶ Sp (Localization.Away f)},
      t₁ ≫ awayMap g = t₀ ≫ awayMap f → ∀ a : Over.mk t₁ ⟶ H, ∃ a' : Over.mk t₀ ⟶ A, a.left ≫ h = a'.left ≫ i := by
    intro T t₁ t₀ e a
    have e' : (a.left ≫ h) ≫ q = t₀ ≫ awayMap f := by
      rw [Category.assoc, hH.w, ← Category.assoc, Over.w a]; exact e
    exact ⟨Over.homMk (hA.lift (a.left ≫ h) t₀ e') (hA.lift_snd _ _ _), (hA.lift_fst _ _ _).symm⟩

  have inj : ∀ {T : Scheme.{0}} {t₁ : T ⟶ Sp (Localization.Away g)} (a b : Over.mk t₁ ⟶ H),
      a.left ≫ h = b.left ≫ h → a = b := by
    intro T t₁ a b e
    exact Over.OverMorphism.ext (hH.hom_ext e (by rw [Over.w a, Over.w b]))
  have hone : ∀ {T : Scheme.{0}} {t₁ : T ⟶ Sp (Localization.Away g)} {t₀ : T ⟶ Sp (Localization.Away f)},
      t₁ ≫ awayMap g = t₀ ≫ awayMap f → (toUnit (Over.mk t₁) ≫ o).left ≫ h = (1 : Over.mk t₀ ⟶ A).left ≫ i := by
    intro T t₁ t₀ e
    simpa using ho T t₁ t₀ e
  letI : MonObj H :=
    { one := o
      mul := m
      one_mul := SpreadAb.hom_ext_of_points j fun T t => by
        obtain ⟨x, hx⟩ : ∃ x, t ≫ snd _ _ = x := ⟨_, rfl⟩
        have ht : t = lift (toUnit _) x :=
          CartesianMonoidalCategory.hom_ext _ _ (toUnit_unique _ _) (by rw [lift_snd, hx])
        subst ht
        obtain ⟨x', hx'⟩ := key (w T) x
        rw [lift_whiskerRight_assoc, lift_leftUnitor_hom]
        apply inj
        rw [hm _ _ _ _ _ _ _ (hone (w T)) hx', _root_.one_mul, hx']
      mul_one := SpreadAb.hom_ext_of_points j fun T t => by
        obtain ⟨x, hx⟩ : ∃ x, t ≫ fst _ _ = x := ⟨_, rfl⟩
        have ht : t = lift x (toUnit _) :=
          CartesianMonoidalCategory.hom_ext _ _ (by rw [lift_fst, hx]) (toUnit_unique _ _)
        subst ht
        obtain ⟨x', hx'⟩ := key (w T) x
        rw [lift_whiskerLeft_assoc, lift_rightUnitor_hom]
        apply inj
        rw [hm _ _ _ _ _ _ _ hx' (hone (w T)), _root_.mul_one, hx']
      mul_assoc := SpreadAb.hom_ext_of_points j fun T t => by
        obtain ⟨x, hx⟩ : ∃ x, t ≫ fst _ _ ≫ fst _ _ = x := ⟨_, rfl⟩
        obtain ⟨y, hy⟩ : ∃ y, t ≫ fst _ _ ≫ snd _ _ = y := ⟨_, rfl⟩
        obtain ⟨z, hz⟩ : ∃ z, t ≫ snd _ _ = z := ⟨_, rfl⟩
        have ht : t = lift (lift x y) z := by
          ext <;> simp [← hx, ← hy, ← hz]
        subst ht
        obtain ⟨x', hx'⟩ := key (w T) x
        obtain ⟨y', hy'⟩ := key (w T) y
        obtain ⟨z', hz'⟩ := key (w T) z
        rw [lift_whiskerRight_assoc, lift_lift_associator_hom_assoc, lift_whiskerLeft_assoc]
        apply inj
        rw [hm _ _ _ _ _ _ _ (hm _ _ _ _ _ _ _ hx' hy') hz', hm _ _ _ _ _ _ _ hx' (hm _ _ _ _ _ _ _ hy' hz'),
          _root_.mul_assoc] }
  letI : GrpObj H :=
    { inv := n
      left_inv := SpreadAb.hom_ext_of_points j fun T t => by
        obtain ⟨x', hx'⟩ := key (w T) t
        change _ ≫ lift n (𝟙 H) ≫ m = _ ≫ toUnit H ≫ o
        rw [comp_lift_assoc, Category.comp_id, comp_toUnit_assoc]
        apply inj
        rw [hm _ _ _ _ _ _ _ (hn _ _ _ _ _ hx') hx', inv_mul_cancel, hone (w T)]
      right_inv := SpreadAb.hom_ext_of_points j fun T t => by
        obtain ⟨x', hx'⟩ := key (w T) t
        change _ ≫ lift (𝟙 H) n ≫ m = _ ≫ toUnit H ≫ o
        rw [comp_lift_assoc, Category.comp_id, comp_toUnit_assoc]
        apply inj
        rw [hm _ _ _ _ _ _ _ hx' (hn _ _ _ _ _ hx'), mul_inv_cancel, hone (w T)] }
  exact ⟨inferInstance, fun T t₁ t₂ a b a' b' ha hb => hm T t₁ t₂ a b a' b' ha hb⟩

end GlobalTheory.Desc.SpreadGrp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpUnitsAndInversesAgreeOfLawsAgree
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem hom_ext_of_cartesian {S S₀ X : Scheme.{0}} {q : X ⟶ S} {s₀ : S₀ ⟶ S} {A : Over S₀}
    {i : A.left ⟶ X} (h : IsPullback i A.hom q s₀) {T : Scheme.{0}} {t₀ : T ⟶ S₀}
    (c c' : Over.mk t₀ ⟶ A) (hc : c.left ≫ i = c'.left ≫ i) : c = c' := by
  apply Over.OverMorphism.ext
  apply h.hom_ext hc
  rw [Over.w c, Over.w c']

theorem oneAgree_invAgree_of_mulAgree : ∀ (S S₀ S₁ X : Scheme.{0}) (q : X ⟶ S) (s₀ : S₀ ⟶ S) (s₁ : S₁ ⟶ S) (A : Over S₀) [GrpObj A] (G : Over S₁) [GrpObj G] (i : A.left ⟶ X) (e : G.left ⟶ X), IsPullback i A.hom q s₀ → e ≫ q = G.hom ≫ s₁ → MulAgree G A e i → OneAgree s₁ s₀ G A e i ∧ ∀ (T : Scheme.{0}) (t₁ : T ⟶ S₁) (t₀ : T ⟶ S₀) (a : Over.mk t₁ ⟶ G) (a' : Over.mk t₀ ⟶ A), a.left ≫ e = a'.left ≫ i → (a⁻¹).left ≫ e = (a'⁻¹).left ≫ i := by
  intro S S₀ S₁ X q s₀ s₁ A _ G _ i e h he hm
  have one : OneAgree s₁ s₀ G A e i := by
    intro T t₁ t₀ ht
    have hw : ((1 : Over.mk t₁ ⟶ G).left ≫ e) ≫ q = t₀ ≫ s₀ := by
      rw [Category.assoc, he, ← Category.assoc, Over.w]; exact ht
    let a' : Over.mk t₀ ⟶ A := Over.homMk (h.lift _ t₀ hw) (by simp)
    have ha' : a'.left ≫ i = (1 : Over.mk t₁ ⟶ G).left ≫ e := h.lift_fst _ _ _
    have hmm := hm T t₁ t₀ 1 1 a' a' ha'.symm ha'.symm
    rw [_root_.mul_one] at hmm
    have h2 : a' * a' = a' := hom_ext_of_cartesian h _ _ (by rw [← hmm, ha'])
    have h3 : a' = 1 := by simpa using h2
    rw [← ha', h3]
  refine ⟨one, ?_⟩
  intro T t₁ t₀ a a' haa
  have ht : t₁ ≫ s₁ = t₀ ≫ s₀ := by
    have w1 : a.left ≫ G.hom = t₁ := Over.w a
    have w0 : a'.left ≫ A.hom = t₀ := Over.w a'
    calc t₁ ≫ s₁ = (a.left ≫ G.hom) ≫ s₁ := by rw [w1]
      _ = (a.left ≫ e) ≫ q := by rw [Category.assoc, Category.assoc, he]
      _ = (a'.left ≫ i) ≫ q := by rw [haa]
      _ = (a'.left ≫ A.hom) ≫ s₀ := by rw [Category.assoc, Category.assoc, h.w]
      _ = t₀ ≫ s₀ := by rw [w0]
  have hw : ((a⁻¹).left ≫ e) ≫ q = t₀ ≫ s₀ := by
    rw [Category.assoc, he, ← Category.assoc, Over.w]; exact ht
  let b' : Over.mk t₀ ⟶ A := Over.homMk (h.lift _ t₀ hw) (by simp)
  have hb' : b'.left ≫ i = (a⁻¹).left ≫ e := h.lift_fst _ _ _
  have hmm := hm T t₁ t₀ a a⁻¹ a' b' haa hb'.symm
  rw [_root_.mul_inv_cancel] at hmm
  have h2 : a' * b' = 1 := hom_ext_of_cartesian h _ _ (by rw [← hmm, one T t₁ t₀ ht])
  have h3 : b' = a'⁻¹ := eq_inv_of_mul_eq_one_right h2
  rw [← h3, hb']

end GlobalTheory.Desc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalfMetWeightEqPotentialHolo
section
namespace HalfMetricWeight
section

open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CxPts GlobalTheory.Mean4O.CombForm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.Dblock.HalfWeight

theorem half_metWeight_eq : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (σ : F →+* ℂ) (D : ℕ) (A : FinHolAtlas D (Pts Y σ)), IsAlgAtlas A → ∀ (Δ : Y.Dv) (m : C.Met Y σ Δ) (hm : ∀ y, PosAt m y) (Q : LocPot (Pts Y σ)), IsPot id m Q → ∀ (x : Pts Y σ) (c : (toLB Δ).ι), x ∈ ptsIn Y.str σ ((toLB Δ).U c) → ∃ W : Set (Pts Y σ), IsOpen W ∧ x ∈ W ∧ ∃ G : Pts Y σ → ℂ, A.HoloOn W G ∧ ∀ z ∈ W, (metWeight Δ m hm).φ c z / 2 = Q.φ x z + (G z).re := by
  intro F _ _ C Y σ D A hA Δ m hm Q hQ x c hx
  obtain ⟨f, hf⟩ := hQ x
  have hxc : under x ∈ c.1.1 := mem_ptsIn.1 hx
  have hu : UnitAt (under x) (f * (c.1.2 : Y.Fn)) :=
    (c.2.2 _ hxc).generatesAt_iff.1 (hf x (Q.mem_U x)).1
  obtain ⟨U, hU, a, ea⟩ := hu.regAt.exists_fnOf
  have hxU : x ∈ ptsIn Y.str σ U := mem_ptsIn.2 hU
  have hv : ∀ z ∈ ptsIn Y.str σ U, ev Y.str σ U a z = ratVal (f * (c.1.2 : Y.Fn)) z := fun z hz => by
    rw [← ea, ratVal_fnOf hz]
  have hS : IsOpen (ptsIn Y.str σ U ∩ (Q.U x ∩ ptsIn Y.str σ ((toLB Δ).U c))) :=
    (isOpen_ptsIn _).inter ((Q.isOpen_U x).inter (isOpen_ptsIn _))
  have hH : hA.anRead.HoloOn (ptsIn Y.str σ U ∩ (Q.U x ∩ ptsIn Y.str σ ((toLB Δ).U c))) (ev Y.str σ U a) :=
    fun j => (hA.anRead.holoOn_ev U a j).mono fun v hv => ⟨hv.1, hv.2.1⟩
  obtain ⟨W, hW, hxW, hs, G, hG, e⟩ := AnRead.HoloOn.exists_log hH hS ⟨hxU, Q.mem_U x, hx⟩
    (by rw [hv x hxU]; exact ratVal_ne_zero hu)
  refine ⟨W, hW, hxW, G, (hA.holoOn_iff hA.anRead hW).2 hG, fun z hz => ?_⟩
  obtain ⟨hzU, hzQ, hzc⟩ := hs hz
  have hzc' : under z ∈ c.1.1 := mem_ptsIn.1 hzc
  have he := c.2.2 _ hzc'
  obtain ⟨hgen, -, hφ⟩ := hf z hzQ
  have hgen' : Δ.GeneratesAt (under z) f := hgen
  have huz : UnitAt (under z) (f * (c.1.2 : Y.Fn)) := he.generatesAt_iff.1 hgen'
  have hgi := CartierDiv.isEqn_iff_generatesAt_inv.1 he
  have hp := pn_pos_of_generatesAt (C := C) hgi (hm z)
  have hr : 0 < ‖ratVal (f * (c.1.2 : Y.Fn)) z‖ := norm_pos_iff.2 (ratVal_ne_zero huz)
  have e1 : f = (f * (c.1.2 : Y.Fn)) * ((c.1.2 : Y.Fn))⁻¹ := by
    rw [mul_assoc, mul_inv_cancel₀ (Units.ne_zero _), mul_one]
  have e2 : C.pn Y σ Δ m (C.cx Y σ f) z =
      ‖ratVal (f * (c.1.2 : Y.Fn)) z‖ ^ 2 * C.pn Y σ Δ m (C.cx Y σ ((c.1.2 : Y.Fn))⁻¹) z := by
    rw [← C.pn_mul Y σ Δ m _ _ z huz.regAt hgi.regularAt, ← e1]
  have e3 : Q.φ x z = -(Real.log (C.pn Y σ Δ m (C.cx Y σ f) z) / 2) := hφ
  have e4 : (G z).re = Real.log ‖ratVal (f * (c.1.2 : Y.Fn)) z‖ := by rw [e z hz, hv z hzU]
  rw [metWeight_φ, e4, e3, e2, Real.log_mul (pow_pos hr 2).ne' hp.ne', Real.log_pow]
  push_cast
  ring

end GlobalTheory.CompanionTheory.Dblock.HalfWeight

end
end

end HalfMetricWeight
section
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CxPts GlobalTheory.Mean4O.CombForm
theorem _root_.GlobalTheory.Adopt.half_metWeight_eq_potential_holo : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (σ : F →+* ℂ) (D : ℕ) (A : FinHolAtlas D (Pts Y σ)), IsAlgAtlas A → ∀ (Δ : Y.Dv) (m : C.Met Y σ Δ) (hm : ∀ y, PosAt m y) (Q : LocPot (Pts Y σ)), IsPot id m Q → ∀ (x : Pts Y σ) (c : (toLB Δ).ι), x ∈ ptsIn Y.str σ ((toLB Δ).U c) → ∃ W : Set (Pts Y σ), IsOpen W ∧ x ∈ W ∧ ∃ G : Pts Y σ → ℂ, A.HoloOn W G ∧ ∀ z ∈ W, (metWeight Δ m hm).φ c z / 2 = Q.φ x z + (G z).re := by
  first | exact @HalfMetricWeight.GlobalTheory.CompanionTheory.Dblock.HalfWeight.half_metWeight_eq | exact HalfMetricWeight.GlobalTheory.CompanionTheory.Dblock.HalfWeight.half_metWeight_eq | (intros; apply HalfMetricWeight.GlobalTheory.CompanionTheory.Dblock.HalfWeight.half_metWeight_eq <;> assumption)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasApproxPoincareSeriesNatMultiple
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem approxAt_mul_of_one_le (g n : ℕ) (F : SFam g n (zetaAway n)) (W8 : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0})
    (i : F.X ⟶ Z) (X₁ : Setup F W8 i) (φ : InvFun ℤ) (d m : ℕ) (hm : 1 ≤ m) (hd : ApproxAt X₁ φ d) :
    ApproxAt X₁ φ (d * m) := by
  intro p _ z₁ c₀ e
  obtain ⟨f, hf0, hf⟩ := hd p z₁ c₀ e
  have hpow : ∀ c : CTrait X₁ p z₁, ‖c.val (f ^ m)‖ = ‖c.val f‖ ^ m := fun c => by
    rw [CTrait.val_eq_valInt, CTrait.val_eq_valInt, map_pow]
    push_cast
    exact norm_pow _ _
  have hexp : ∀ c : CTrait X₁ p z₁, Real.exp (-(c.sc * (((d * m : ℕ) : ℝ) * φ.evalZ c.T.β))) =
      Real.exp (-(c.sc * (d * φ.evalZ c.T.β))) ^ m := fun c => by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  refine ⟨f ^ m, ?_, fun c => ?_⟩
  · rw [hpow, hf0, hexp]
  · rcases hf c with h1 | ⟨h, hh, h2⟩
    · left
      rw [hpow, hexp]
      exact pow_le_pow_left₀ (norm_nonneg _) h1 m
    · right
      refine ⟨h, hh, ?_⟩
      rw [hpow]
      exact (pow_le_of_le_one (norm_nonneg _) (c.norm_val_le f) (by omega)).trans h2

theorem approxAt_mul : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W8 : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W8 i) (φ : InvFun ℤ) (d m : ℕ), 1 ≤ m → ApproxAt X₁ φ d → ApproxAt X₁ φ (d * m) := approxAt_mul_of_one_le

end GlobalTheory.Poinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasFibrewiseNonvanishingThetaSectionOfSmoothMode
section
open AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open CategoryTheory Limits IsLocalRing

namespace GlobalTheory.ThetaNormal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.Models
open scoped CategoryTheory.Obj

theorem exists_theta_of_flat {X : Scheme.{0}} {G : Over X} [GrpObj G] (hG : IsSemiAbelian G) {L : LB G.left}
    (hL : L.IsLB) (x : X) {R : Type} [CommRing R] [IsLocalRing R] (ψ : X.presheaf.stalk x →+* R) (hψ : ψ.Flat)
    [IsLocalHom ψ] {G' : Over (Sp R)} {φ : G'.left ⟶ G.left}
    (hφ : IsPullback φ G'.hom G.hom (spMap ψ ≫ X.fromSpecStalk x)) {L' : LB G'.left} (hL' : L'.IsLB)
    (hw : LBIso L' (L.pull φ)) (hθ : LN.ThetaNZ G' L') :
    ∃ V : X.Opens, x ∈ V ∧ ∃ θ ∈ secOn L (G.hom ⁻¹ᵁ V),
      ∀ y ∈ V, ∃ (g : G.left) (i : L.ι), G.hom g = y ∧ g ∈ G.left.basicOpen (θ i) := by
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := x) trivial
  let ι := pullback.fst G.hom hU.fromSpec
  let f := pullback.snd G.hom hU.fromSpec
  let gm : Γ(X, U) →+* R := ψ.comp (X.presheaf.germ U x hx).hom
  have hξ : spMap gm ≫ hU.fromSpec = spMap ψ ≫ X.fromSpecStalk x := by
    rw [← hU.fromSpecStalk_eq_fromSpecStalk hx]
    show Spec.map (CommRingCat.ofHom (X.presheaf.germ U x hx).hom ≫ CommRingCat.ofHom ψ) ≫ _ = _
    rw [Spec.map_comp, Category.assoc]
    rfl
  let π : G'.left ⟶ pullback G.hom hU.fromSpec := pullback.lift φ (G'.hom ≫ spMap gm)
    (by rw [Category.assoc, hξ, hφ.w])
  have hπ : π ≫ ι = φ := pullback.lift_fst _ _ _
  have hP : IsPullback π G'.hom f (spMap gm) :=
    IsPullback.of_right (by rw [hπ, hξ]; exact hφ) (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
  have : CompactSpace (pullback G.hom hU.fromSpec : Scheme.{0}) := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace (pullback G.hom hU.fromSpec : Scheme.{0}) := quasiSeparatedSpace_of_quasiSeparated f
  have hflat : gm.Flat := by
    have h₀ : (X.presheaf.germ U x hx).hom.Flat := by
      letI := X.presheaf.algebra_section_stalk (⟨x, hx⟩ : U)
      have := hU.isLocalization_stalk ⟨x, hx⟩
      exact RingHom.flat_algebraMap_iff.2
        (IsLocalization.flat (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl)
    exact RingHom.Flat.comp h₀ hψ
  have hM := pull_isLB hL ι
  obtain ⟨w, hw'⟩ : LBIso ((L.pull ι).pull π) (L'.pull (𝟙 _)) :=
    LBIso.chartPull (chartPullLinComb L ι (fun _ : PUnit => π) (fun _ => φ) (fun _ => 1) (𝟙 _)
      fun _ => hπ.trans (Category.id_comp _).symm) (Geo.Tor.chartPullPull L' _ _ rfl) hw.symm
  obtain ⟨θ', hθ'⟩ := hθ
  obtain ⟨σ, hσ⟩ := ThetaLocal.exists_sec_pull hL' (pull_isLB hM π) (𝟙 _) w hw' (O := ⊤) le_top _
    (SecSpread.res_mem_secOn θ' ⊤)
  obtain ⟨z, i, hz, hi⟩ := hθ' (IsLocalRing.closedPoint _)
  obtain ⟨k, hk⟩ := hσ z i ((ThetaLocal.mem_basicOpen_resG _ _ _).2 ⟨⟨trivial, G'.left.basicOpen_le _ hi⟩, hi⟩)
  obtain ⟨k, rfl⟩ : ∃ j, k = fun _ => j := ⟨k PUnit.unit, rfl⟩
  have hk₁ := G'.left.basicOpen_le _ hk
  have hk₂ : π z ∈ (L.pull ι).U k := mem_pull.1 hk₁
  obtain ⟨n, a, u, hu⟩ := FlatSec.exists_comb_of_flat _ _ gm hflat _ f _ π G'.hom hP _ hM σ
  obtain ⟨j, hj⟩ : ∃ j, π z ∈ Scheme.basicOpen _ ((u j).f k) := by
    by_contra hn
    have h₁ := (AbLocusPull.isUnit_gs_iff (𝟙 _) z _ hk₁ _).2 hk
    rw [hu z k hk₂] at h₁
    refine (IsLocalRing.mem_maximalIdeal _).1 (Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ ?_) h₁
    exact fun h₂ => hn ⟨j, (AbLocusPull.isUnit_gs_iff π z _ hk₂ _).1 h₂⟩
  let V : X.Opens := ⟨(ι ≫ G.hom) '' Scheme.basicOpen _ ((u j).f k),
    (ι ≫ G.hom).isOpenMap _ (Scheme.basicOpen _ ((u j).f k)).isOpen⟩
  have hr : G.hom ⁻¹ᵁ V ≤ ι.opensRange := by
    rintro g ⟨y, -, e⟩
    obtain ⟨q, hq, -⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback G.hom hU.fromSpec) g (f y)
      (e.symm.trans (congrArg (fun r : pullback G.hom hU.fromSpec ⟶ X => r y) pullback.condition))
    exact ⟨q, hq⟩
  obtain ⟨θ, hθ, hb⟩ := ThetaLocal.exists_secOn_push hL hM (lbIso_refl hM) hr le_top
    (SecSpread.res_mem_secOn (u j) ⊤)
  refine ⟨V, ⟨π z, hj, ?_⟩, θ, hθ, ?_⟩
  · rw [← Scheme.Hom.comp_apply, ← Category.assoc, hπ, hφ.w, Scheme.Hom.comp_apply, hz]
    show X.fromSpecStalk x (spMap ψ (IsLocalRing.closedPoint R)) = x
    have hc : spMap ψ (IsLocalRing.closedPoint R) = IsLocalRing.closedPoint _ := IsLocalRing.comap_closedPoint ψ
    rw [hc]
    exact Scheme.fromSpecStalk_closedPoint
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨i', hi'⟩ := exists_chart hL (ι y)
    exact ⟨ι y, i', rfl, hb y ⟨y, hy, rfl⟩ i' k hi'
      ((ThetaLocal.mem_basicOpen_resG _ _ _).2 ⟨⟨trivial, Scheme.basicOpen_le _ _ hy⟩, hy⟩)⟩

theorem hasTheta_of_smooth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), SmoothOfRelativeDimension Dw.dim Y.s → GlobalTheory.Models.HasTheta Y.t.G Y.t.PP.L := by
  intro E _ _ _ H Dw _ l Xo c Y hsm x
  have : Smooth Y.s := SmoothOfRelativeDimension.smooth Dw.dim _
  haveI hAr : IsRegularRing (Y.X.presheaf.stalk x) :=
    ExtendRig.isRegularRing_stalk isRegularRing_of_smooth c.F Y.s x
  haveI : IsRegularLocalRing (Y.X.presheaf.stalk x) :=
    IsRegularLocalRing.of_isRegularRing_of_isLocalRing _
  haveI : IsRegularLocalRing (AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x)) (Y.X.presheaf.stalk x)) :=
    RegularCompletion.isRegularLocalRing_adicCompletion _
  obtain ⟨hdC, hnC⟩ := isDomain_and_isIntegrallyClosed_of_isRegularLocalRing
    (AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x)) (Y.X.presheaf.stalk x))

  haveI hκ : CharZero (Y.X.residueField x) := by
    let φ : c.F →+* Y.X.residueField x := (Y.X.evaluation ⊤ x trivial).hom.comp (GlobalTheory.QCoh.structureRingHom Y.s)
    exact charZero_of_injective_ringHom φ.injective
  obtain ⟨k, _, _, hk, S', hS'⟩ := CoveringCompare.exists_finite_splitOver Y.t.G Y.t.semi x

  haveI : Algebra.IsSeparable (Y.X.residueField x) k := inferInstance
  obtain ⟨R, _, _, _, _, j, _, _, hj⟩ := LocM.Bdy.exists_etale_local
    (AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x)) (Y.X.presheaf.stalk x)) (Y.X.residueField x) k
    (ResidueField.map (algebraMap (Y.X.presheaf.stalk x)
      (AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x)) (Y.X.presheaf.stalk x))))
  have : IsLocalization.AtPrime R (maximalIdeal R) :=
    IsLocalization.self fun a ha => by_contra fun h => ha h
  obtain ⟨hd, hn⟩ := isDomain_and_isIntegrallyClosed_atPrime_of_etale
    (AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x)) (Y.X.presheaf.stalk x)) (maximalIdeal R) R
  have hNR : IsNoetherianRing R :=
    IsNoetherianRing.of_finite (AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x)) (Y.X.presheaf.stalk x)) R
  have hc := CompleteFiniteExtension.isAdicComplete_of_finite_local
    (AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x)) (Y.X.presheaf.stalk x)) R
  have f₁ := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := Y.X.presheaf.stalk x)
    (B := AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x)) (Y.X.presheaf.stalk x))
  have f₂ := Module.FaithfullyFlat.of_flat_of_isLocalHom
    (A := AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x)) (Y.X.presheaf.stalk x)) (B := R)
  let ψ : Y.X.presheaf.stalk x →+* R := (algebraMap (AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x))
    (Y.X.presheaf.stalk x)) R).comp (algebraMap (Y.X.presheaf.stalk x) (AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x)) (Y.X.presheaf.stalk x)))
  have hinj : Function.Injective ψ :=
    (FaithfulSMul.algebraMap_injective _ _).comp (FaithfulSMul.algebraMap_injective _ _)
  haveI : CharZero (ResidueField (Y.X.presheaf.stalk x)) := hκ
  haveI : CharZero (Y.X.presheaf.stalk x) := RingHom.charZero (residue (Y.X.presheaf.stalk x))
  haveI : CharZero R := charZero_of_injective_ringHom hinj
  have hadm := isAdmissibleCompleteLocalDomainPrime_maximalIdeal R hNR hn hc
  have hψf : ψ.Flat := RingHom.Flat.comp (RingHom.flat_algebraMap_iff.2 inferInstance)
    (RingHom.flat_algebraMap_iff.2 inferInstance)
  haveI : IsLocalHom ψ := inferInstance

  obtain ⟨t, ⟨m⟩⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_sab (spMap ψ ≫ Y.X.fromSpecStalk x) Y.t
  haveI : IsProper Y.s := ProperFamily.isProper_of_isProjOver Y.proj
  haveI : IsLocallyNoetherian Y.X := LocallyOfFiniteType.isLocallyNoetherian Y.s
  haveI : CompactSpace Y.X := QuasiCompact.compactSpace_of_compactSpace Y.s
  haveI : IsNoetherian Y.X := {}
  have hjo := GenFan.Tri.isOpenImmersion_j_id Y
  have hopen : IsOpen (Set.range Y.j) := Y.j.isOpenEmbedding.isOpen_range
  have hdense : Dense (Set.range Y.j) := by
    have : IsIso (pullback.fst Y.s (spMap (RingHom.id c.F))) := by
      have : IsIso (spMap (RingHom.id c.F)) := by
        show IsIso (Spec.map (CommRingCat.ofHom (RingHom.id c.F)))
        rw [show CommRingCat.ofHom (RingHom.id c.F) = 𝟙 (CommRingCat.of c.F) from rfl, Spec.map_id]
        infer_instance
      infer_instance
    have e : Set.range Y.j = (pullback.fst Y.s (spMap (RingHom.id c.F))) '' Set.range Y.jQ := by
      ext z
      constructor
      · rintro ⟨w, rfl⟩
        exact ⟨Y.jQ w, ⟨w, rfl⟩, (Scheme.Hom.comp_apply _ _ _).symm⟩
      · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
        exact ⟨w, Scheme.Hom.comp_apply _ _ _⟩
    rw [e]
    exact ((pullback.fst Y.s (spMap (RingHom.id c.F))).surjective.denseRange).dense_image
      (pullback.fst Y.s (spMap (RingHom.id c.F))).continuous Y.jQ_dense
  let ξ : Sp R := (⊥ : PrimeSpectrum R)
  have hgen : (spMap ψ ≫ Y.X.fromSpecStalk x) ξ ∈ Set.range Y.j :=
    LocM.SharedLaws.mem_of_maximal (fun y hy => LocM.Bdy.generic_image x ψ hinj ξ rfl y hy) hopen hdense
  have hr : Set.range (jK R ≫ spMap ψ ≫ Y.X.fromSpecStalk x) ⊆ Set.range Y.j := by
    rintro _ ⟨q, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact LN.GenericPoint.jK_mem (U := (spMap ψ ≫ Y.X.fromSpecStalk x) ⁻¹' Set.range Y.j)
      (hopen.preimage (Scheme.Hom.continuous _)) ⟨ξ, hgen⟩ q
  have hpol : LN.PolAt t (jK R) :=
    GoodTrait.polAt_of_point Y m (jK R) (IsOpenImmersion.lift Y.j _ hr) (IsOpenImmersion.lift_fac _ _ _)
  have h₁ := LocM.Bdy.residue_comp (R := R) x
  have e : spMap (algebraMap (AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x)) (Y.X.presheaf.stalk x)) R) ≫
      fromSpecCompletedStalk Y.X x = spMap ψ ≫ Y.X.fromSpecStalk x := by
    rw [spMap_comp, Category.assoc]; rfl
  have h₂ : spMap j ≫ spMap (algebraMap (Y.X.residueField x) k) =
      spMap ((ResidueField.map (algebraMap (AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x))
        (Y.X.presheaf.stalk x)) R)).comp (ResidueField.map (algebraMap (Y.X.presheaf.stalk x)
          (AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x)) (Y.X.presheaf.stalk x))))) :=
    (spMap_comp _ _).symm.trans (congrArg spMap hj)
  obtain ⟨S₁, hS₁⟩ := LocM.Bdy.split_pull _ hS' j (ι := spMap ψ ≫ Y.X.fromSpecStalk x) (by
    rw [← Category.assoc]
    refine (congrArg (· ≫ Y.X.fromSpecResidueField x) h₂).trans ?_
    exact h₁.trans (congrArg (spMap (residue R) ≫ ·) e)) m
  have hsplit : LN.SplitOver t.G (maximalIdeal R) := ⟨S₁, hS₁⟩
  have hθ := thetaNZ_of_polAt E H R hadm t hpol hsplit
  exact exists_theta_of_flat Y.t.semi Y.t.PP.isLB x ψ hψf m.cart.1 t.PP.isLB (m.lin.imp fun _ h => h.1) hθ

end GlobalTheory.ThetaNormal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasProperSmoothDualRepresentativeFinAffineOfIsEmStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasProperSmoothDualRepresentativeFinAffine_of_isEmpty : ∀ (S : Scheme.{0}) (A S' : Over S) [GrpObj A] (g : ℕ), IsEmpty S'.left → HasRepAF A g S' := by
  first | exact @GlobalTheory.DualCon.hasRepAF_of_isEmpty | exact GlobalTheory.DualCon.hasRepAF_of_isEmpty | (intros; apply GlobalTheory.DualCon.hasRepAF_of_isEmpty <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasProperSmoothDualRepresentativeFinAffineOfIsoStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasProperSmoothDualRepresentativeFinAffine_of_iso : ∀ {S : Scheme.{0}} (A : Over S) [GrpObj A] (g : ℕ) {Y Y' : Over S}, (Y ≅ Y') → HasRepAF A g Y → HasRepAF A g Y' := by
  first | exact @GlobalTheory.hasRepAF_of_iso | exact GlobalTheory.hasRepAF_of_iso | (intros; apply GlobalTheory.hasRepAF_of_iso <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasProperSmoothDualRepresentativeGrpPullbackIffStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasProperSmoothDualRepresentative_grpPullback_iff : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (A : Over S) [GrpObj A] (A' : Over S') [GrpObj A'] (φ : A'.left ⟶ A.left), IsGrpPullback A' A f φ → ∀ (g : ℕ) (T : Over S'), (HasRep A' g T ↔ HasRep A g (Over.mk (T.hom ≫ f))) ∧ (HasRepAF A' g T ↔ HasRepAF A g (Over.mk (T.hom ≫ f))) := by
  first | exact @GlobalTheory.DualCon.hasRep_baseChange_iff | exact GlobalTheory.DualCon.hasRep_baseChange_iff | (intros; apply GlobalTheory.DualCon.hasRep_baseChange_iff <;> assumption)
end

