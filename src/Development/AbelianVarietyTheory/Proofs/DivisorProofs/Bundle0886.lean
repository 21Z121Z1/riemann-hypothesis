import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0843
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0865
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThickId
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0011
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0857
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecMatEqAdd
section
open MeasureTheory GlobalTheory.JSW
open scoped FourierTransform ContDiff

noncomputable section

namespace GlobalTheory.JSW

variable {n : ℕ}

open scoped Matrix

theorem secMat_of_ne (ρ j : Fin n) (v : Fin n → ℂ) {i : Fin n} (hi : i ≠ ρ) (l : Fin n) :
    secMat ρ j v i l = if l = Equiv.swap j ρ i then 1 else 0 := by
  simp [secMat, hi]

theorem secMat_self (ρ j : Fin n) (v : Fin n → ℂ) (l : Fin n) :
    secMat ρ j v ρ l = if l ≤ ρ then v l else 0 := by
  simp [secMat]

theorem swap_of_lt' {ρ j i : Fin n} (hj : j ≤ ρ) (hi : ρ < i) : Equiv.swap j ρ i = i :=
  Equiv.swap_apply_of_ne_of_ne (lt_of_le_of_lt hj hi).ne' hi.ne'

theorem isUnit_secMat (ρ j : Fin n) (hj : j ≤ ρ) (v : Fin n → ℂ) (hv : v j ≠ 0) :
    IsUnit (Matrix.of (secMat ρ j v)) := by
  rw [← Matrix.vecMul_injective_iff_isUnit]
  have key : ∀ e : Fin n → ℂ, e ᵥ* Matrix.of (secMat ρ j v) = 0 → e = 0 := by
    intro e he
    have hcol : ∀ l, ∑ i, e i * secMat ρ j v i l = 0 := fun l => by
      have := congrFun he l
      simpa [Matrix.vecMul, dotProduct] using this
    have hρ : e ρ = 0 := by
      have h := hcol j
      rw [Finset.sum_eq_single ρ] at h
      · rw [secMat_self, if_pos hj] at h
        exact (mul_eq_zero.1 h).resolve_right hv
      · intro i _ hi
        rw [secMat_of_ne _ _ _ hi, if_neg, mul_zero]
        intro h'
        apply hi
        calc i = Equiv.swap j ρ (Equiv.swap j ρ i) := (Equiv.swap_apply_self _ _ _).symm
          _ = Equiv.swap j ρ j := by rw [← h']
          _ = ρ := Equiv.swap_apply_left _ _
      · simp
    funext i
    by_cases hi : i = ρ
    · rw [hi]; exact hρ
    · have h := hcol (Equiv.swap j ρ i)
      rw [Finset.sum_eq_single i] at h
      · rw [secMat_of_ne _ _ _ hi, if_pos rfl, mul_one] at h
        exact h
      · intro i' _ hi'
        by_cases h'' : i' = ρ
        · rw [h'', hρ, zero_mul]
        · rw [secMat_of_ne _ _ _ h'', if_neg, mul_zero]
          intro h3
          exact hi' ((Equiv.swap j ρ).injective h3).symm
      · simp
  intro c d hcd
  have := key (c - d) (by
    change (c - d) ᵥ* _ = 0
    rw [Matrix.sub_vecMul]
    exact sub_eq_zero.2 hcd)
  exact sub_eq_zero.1 this

def secLin (ρ : Fin n) : (Fin n → ℂ) →L[ℝ] (Fin n → Fin n → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v i l => if i = ρ ∧ l ≤ ρ then v l else 0
      map_add' := fun v w => by
        funext i l
        by_cases h : i = ρ ∧ l ≤ ρ <;> simp [h]
      map_smul' := fun c v => by
        funext i l
        by_cases h : i = ρ ∧ l ≤ ρ <;> simp [h] }

theorem secMat_eq_add (ρ j : Fin n) (v : Fin n → ℂ) : secMat ρ j v = secMat ρ j 0 + secLin ρ v := by
  funext i l
  by_cases hi : i = ρ
  · subst hi
    by_cases hl : l ≤ i <;> simp [secMat, secLin, hl]
  · simp [secMat, secLin, hi]

theorem secMat_main : ∀ (n : ℕ) (ρ j : Fin n), j ≤ ρ → (∀ v : Fin n → ℂ, v j ≠ 0 → IsUnit (Matrix.of (secMat ρ j v))) ∧ (∀ g ∈ levSet n (ρ + 1), rowCut ρ (g : Matrix (Fin n) (Fin n) ℂ) j ≠ 0 → g * (toGL (Matrix.of (secMat ρ j (rowCut ρ (g : Matrix (Fin n) (Fin n) ℂ)))))⁻¹ ∈ levSet n ρ) ∧ ∃ L : (Fin n → ℂ) →L[ℝ] (Fin n → Fin n → ℂ), ∀ v, secMat ρ j v = secMat ρ j 0 + L v := by
  intro n ρ j hj
  refine ⟨fun v hv => isUnit_secMat ρ j hj v hv, ?_, secLin ρ, secMat_eq_add ρ j⟩
  intro g hg hgj
  set v := rowCut ρ (g : Matrix (Fin n) (Fin n) ℂ) with hv
  have hS := isUnit_secMat ρ j hj v hgj
  set S := toGL (Matrix.of (secMat ρ j v)) with hSdef
  have hSv : (S : Matrix (Fin n) (Fin n) ℂ) = Matrix.of (secMat ρ j v) := val_toGL hS
  have hSlev : S ∈ levSet n (ρ + 1) := by
    intro i hi
    have hiρ : ρ < i := by rw [Fin.lt_def]; omega
    refine ⟨fun l hl => ?_, ?_⟩
    · rw [hSv, Matrix.of_apply, secMat_of_ne _ _ _ hiρ.ne', swap_of_lt' hj hiρ, if_neg hl.ne]
    · rw [hSv, Matrix.of_apply, secMat_of_ne _ _ _ hiρ.ne', swap_of_lt' hj hiρ, if_pos rfl]
  have hp : g * S⁻¹ ∈ levSet n (ρ + 1) :=
    (GlobalTheory.T.unipotentLowerRowsLeviSet_closed_subgroup n (ρ + 1)).1 g hg _ ((GlobalTheory.T.unipotentLowerRowsLeviSet_closed_subgroup n (ρ + 1)).2.1 S hSlev)
  set P := ((g * S⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) with hPdef
  have hPS : P * Matrix.of (secMat ρ j v) = (g : Matrix (Fin n) (Fin n) ℂ) := by
    rw [← hSv, hPdef, ← Units.val_mul, inv_mul_cancel_right]
  let w : Fin n → ℂ := fun i => if i = ρ then 1 else if i < ρ then 0 else (g : Matrix (Fin n) (Fin n) ℂ) ρ i
  have hw : w ᵥ* Matrix.of (secMat ρ j v) = (g : Matrix (Fin n) (Fin n) ℂ) ρ := by
    funext l
    simp only [Matrix.vecMul, dotProduct, Matrix.of_apply]
    by_cases hl : l ≤ ρ
    · rw [Finset.sum_eq_single ρ]
      · simp [w, secMat_self, hl, hv, rowCut]
      · intro i _ hi
        rcases lt_or_gt_of_ne hi with h | h
        · simp [w, hi, h]
        · rw [secMat_of_ne _ _ _ hi, swap_of_lt' hj h, if_neg (lt_of_le_of_lt hl h).ne, mul_zero]
      · simp
    · have hlρ : ρ < l := lt_of_not_ge hl
      rw [Finset.sum_eq_single l]
      · simp [w, secMat_of_ne _ _ _ hlρ.ne', swap_of_lt' hj hlρ, hlρ.ne', not_lt.2 hlρ.le]
      · intro i _ hi
        by_cases h1 : i = ρ
        · rw [h1, secMat_self, if_neg hl, mul_zero]
        · rcases lt_or_gt_of_ne h1 with h | h
          · simp [w, h1, h]
          · rw [secMat_of_ne _ _ _ h1, swap_of_lt' hj h, if_neg (Ne.symm hi), mul_zero]
      · simp
  have hPw : P ρ ᵥ* Matrix.of (secMat ρ j v) = (g : Matrix (Fin n) (Fin n) ℂ) ρ := by
    rw [← hPS]
    funext l
    simp [Matrix.vecMul, dotProduct, Matrix.mul_apply]
  have hrow : P ρ = w := (Matrix.vecMul_injective_iff_isUnit.2 hS) (hPw.trans hw.symm)
  intro i hi
  by_cases hiρ : (i : ℕ) = ρ
  · have hie : i = ρ := Fin.ext hiρ
    subst hie
    refine ⟨fun l hl => ?_, ?_⟩
    · change P i l = 0
      rw [hrow]
      simp [w, hl, hl.ne]
    · change P i i = 1
      rw [hrow]
      simp [w]
  · exact hp i (by omega)

end GlobalTheory.JSW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallAffineBasisAndTransitionUnitsLift
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Obs GlobalTheory.LBLift
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LBLift

theorem app_presheaf_map {X Y : Scheme.{0}} (f : Y ⟶ X) {V W : X.Opens} (h : W ≤ V) (x : Γ(X, V)) :
    (f.app W).hom ((X.presheaf.map (homOfLE h).op).hom x) =
      (Y.presheaf.map (homOfLE (f.preimage_mono h)).op).hom ((f.app V).hom x) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality]
  rfl

theorem presheaf_map_map {Y : Scheme.{0}} {U V W : Y.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (y : Γ(Y, U)) :
    (Y.presheaf.map (homOfLE h₂).op).hom ((Y.presheaf.map (homOfLE h₁).op).hom y) =
      (Y.presheaf.map (homOfLE (h₂.trans h₁)).op).hom y := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

variable {R : Type} [CommRing R] {I : Ideal R} {X X₀ : Scheme.{0}} {s : X ⟶ Sp R} {i : X₀ ⟶ X} {L : LB X₀}

theorem isBasis_smallG (hi : IsThick I s i) (hL : L.IsLB) : IsBasis (smallG i L) := by
  haveI := hi.closed
  have hind : Topology.IsInducing i.base := i.isClosedEmbedding.isInducing
  have cov : ∀ (x : X) (U : X.Opens), x ∈ U → ∃ t : (Small i L)ᵒᵖ,
      x ∈ ((smallG i L).obj t).unop.1 ∧ ((smallG i L).obj t).unop.1 ≤ U := by
    intro x U hx
    obtain ⟨x₀, rfl⟩ := hi.surj.surj x
    have hx₀ : x₀ ∈ ⨆ j, L.U j := by rw [hL.cover]; trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hx₀
    obtain ⟨V, hV, hVe⟩ := hind.isOpen_iff.1 (L.U j).isOpen
    have hxV : i.base x₀ ∈ (⟨V, hV⟩ : X.Opens) ⊓ U := ⟨show x₀ ∈ i.base ⁻¹' V from hVe ▸ hj, hx⟩
    obtain ⟨W, hW, hxW, hWle⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens) hxV
    have hsm : i ⁻¹ᵁ W ≤ L.U j := fun y hy ↦ by
      show y ∈ (L.U j : Set X₀)
      rw [← hVe]
      exact (hWle hy).1
    exact ⟨Opposite.op ⟨(⟨W, hW⟩, j), hsm⟩, hxW, fun y hy ↦ (hWle hy).2⟩
  refine ⟨cov, fun t₁ t₂ x U hx h₁ h₂ ↦ ?_⟩
  obtain ⟨t₃, hx₃, hle⟩ := cov x (U ⊓ ((smallG i L).obj t₁).unop.1 ⊓ ((smallG i L).obj t₂).unop.1)
    ⟨⟨hx, h₁⟩, h₂⟩
  exact ⟨t₃, ⟨(homOfLE (show t₃.unop ≤ t₁.unop from fun y hy ↦ (hle hy).1.2)).op⟩,
    ⟨(homOfLE (show t₃.unop ≤ t₂.unop from fun y hy ↦ (hle hy).2)).op⟩, hx₃, fun y hy ↦ (hle hy).1.1⟩

theorem exists_isLift (hi : IsThick I s i) : ∃ u, IsLift s i L u :=
  ⟨fun p q a ↦ (hi.app_surj q.unop.1.1 (res (Small.le_inf a) (L.g p.unop.1.2 q.unop.1.2)).val).choose,
    fun p q a ↦ (hi.app_surj q.unop.1.1 _).choose_spec⟩

end GlobalTheory.LBLift

namespace GlobalTheory.LBLift
variable {R : Type} [CommRing R] {I : Ideal R} {X X₀ : Scheme.{0}} {s : X ⟶ Sp R} {i : X₀ ⟶ X} {L : LB X₀}

theorem isUnit_of_sqZero {A A₀ : Type} [CommRing A] [CommRing A₀] (p : A →+* A₀)
    (hp : Function.Surjective p) (K : Ideal A) (hK : K ^ 2 = ⊥) (hker : ∀ a, p a = 0 → a ∈ K)
    (x : A) (hx : IsUnit (p x)) : IsUnit x := by
  obtain ⟨v, hv⟩ := hx.exists_right_inv
  obtain ⟨y, rfl⟩ := hp v
  have hn : x * y - 1 ∈ K := hker _ (by simp [hv])
  have hsq : (x * y - 1) * (x * y - 1) = 0 := by
    have : (x * y - 1) * (x * y - 1) ∈ K ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul hn hn
    rw [hK] at this; simpa using this
  have hnil : IsNilpotent (x * y - 1) := ⟨2, by rw [pow_two, hsq]⟩
  have : IsUnit (x * y) := by simpa using hnil.isUnit_one_add
  exact isUnit_of_mul_isUnit_left this

theorem lift_isUnit (hI : I ^ 2 = ⊥) (hi : IsThick I s i) {u : C1 (smallG i L ⋙ OAff s)} (hu : IsLift s i L u)
    (p q : (Small i L)ᵒᵖ) (a : p ⟶ q) : IsUnit (u p q a) := by
  have hK : ∀ (A : Type) [CommRing A] [Algebra R A], (I.map (algebraMap R A)) ^ 2 = ⊥ := fun A _ _ ↦ by
    rw [← Ideal.map_pow, hI, Ideal.map_bot]
  exact isUnit_of_sqZero (A := Γ(X, q.unop.1.1.1)) (i.app q.unop.1.1.1).hom (hi.app_surj q.unop.1.1)
    (I.map (algebraMap R (Sec s q.unop.1.1.1))) (hK (Sec s q.unop.1.1.1)) (fun b hb ↦ (hi.ker q.unop.1.1 b).1 hb) (u p q a)
    ((hu p q a).symm ▸ Units.isUnit _)

theorem lift_mdef (hi : IsThick I s i) (hL : L.IsLB) {u : C1 (smallG i L ⋙ OAff s)} (hu : IsLift s i L u) :
    In2 I _ (mdef _ u) := by
  intro t t' t'' a b
  refine (hi.ker t''.unop.1.1 _).1 ?_
  have hb : t''.unop.1.1.1 ≤ t'.unop.1.1.1 := leOfHom b.unop
  have h2 : i ⁻¹ᵁ t''.unop.1.1.1 ≤ L.U t.unop.1.2 ⊓ L.U t'.unop.1.2 ⊓ L.U t''.unop.1.2 :=
    le_inf ((i.preimage_mono hb).trans (Small.le_inf a)) t''.unop.2
  have hc := congrArg (fun w ↦ (X₀.presheaf.map (homOfLE h2).op).hom w.val)
    (hL.cocycle t.unop.1.2 t'.unop.1.2 t''.unop.1.2)
  simp only [Units.val_mul, map_mul, res, Units.coe_map, MonoidHom.coe_coe,
    presheaf_map_map] at hc
  have k : ∀ (x : Γ(X, t'.unop.1.1.1)) (y z : Γ(X, t''.unop.1.1.1)),
      (i.app t'.unop.1.1.1).hom x = (res (Small.le_inf a) (L.g t.unop.1.2 t'.unop.1.2)).val →
      (i.app t''.unop.1.1.1).hom y = (res (Small.le_inf b) (L.g t'.unop.1.2 t''.unop.1.2)).val →
      (i.app t''.unop.1.1.1).hom z = (res (Small.le_inf (a ≫ b)) (L.g t.unop.1.2 t''.unop.1.2)).val →
      (i.app t''.unop.1.1.1).hom ((X.presheaf.map (homOfLE hb).op).hom x * y - z) = 0 := by
    intro x y z hx hy hz
    rw [map_sub, map_mul, app_presheaf_map, hx, hy, hz, sub_eq_zero]
    simp only [res, Units.coe_map, MonoidHom.coe_coe, presheaf_map_map]
    exact hc
  exact k _ _ _ (hu t t' a) (hu t' t'' b) (hu t t'' (a ≫ b))

theorem isLiftOfTransitionUnits_of_ideal_cochain_change (hi : IsThick I s i) {u : C1 (smallG i L ⋙ OAff s)} (hu : IsLift s i L u)
    (u' : C1 (smallG i L ⋙ OAff s)) (h : In1 I _ (u' - u)) : IsLift s i L u' := by
  intro p q a
  have h0 := (hi.ker q.unop.1.1 _).2 (h p q a)
  have e : u' p q a = u p q a + (u' - u) p q a := by simp
  rw [e]
  exact (map_add (i.app q.unop.1.1.1).hom (u p q a) ((u' - u) p q a)).trans
    ((congrArg₂ (· + ·) (hu p q a) h0).trans (add_zero _))

end GlobalTheory.LBLift

namespace GlobalTheory.LBLift

theorem small_basis_lift : ∀ (R : Type) [CommRing R] (I : Ideal R), I ^ 2 = ⊥ → ∀ (X X₀ : Scheme.{0}) (s : X ⟶ Sp R) (i : X₀ ⟶ X) (L : LB X₀), IsThick I s i → L.IsLB → IsBasis (smallG i L) ∧ (∃ u, IsLift s i L u) ∧ ∀ u, IsLift s i L u → (∀ t t' a, IsUnit (u t t' a)) ∧ In2 I _ (mdef _ u) ∧ ∀ u', In1 I _ (u' - u) → IsLift s i L u' := by
  intro R _ I hI X X₀ s i L hi hL
  exact ⟨isBasis_smallG hi hL, exists_isLift hi, fun u hu ↦
    ⟨lift_isUnit hI hi hu, lift_mdef hi hL hu, fun u' h ↦ isLiftOfTransitionUnits_of_ideal_cochain_change hi hu u' h⟩⟩

end GlobalTheory.LBLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusMapOfCharHom
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory
namespace TorusOfCharMap

variable {S : Scheme.{0}} {X X' : Type} [AddCommGroup X] [AddCommGroup X']

theorem ext_chV {Z : Over S} {a b : Z ⟶ splitTorus S X} (h : ∀ χ, chV a χ = chV b χ) : a = b :=
  (splitTorusPointsEquiv S X Z).injective (MonoidHom.ext fun χ => h χ.toAdd)

theorem chV_torusMap (ρ : X' →+ X) (χ : X') :
    chV (SplitTorusPow.torusMap S ρ) χ = charUnit S X (ρ χ) := by
  ext1
  rw [chV_val]
  exact SplitTorusPow.torusMap_char ρ χ

theorem chV_comp_torusMap (ρ : X' →+ X) {Z : Over S} (s : Z ⟶ splitTorus S X) (χ : X') :
    chV (s ≫ SplitTorusPow.torusMap S ρ) χ = chV s (ρ χ) := by
  unfold chV
  rw [SplitTorusPow.points_comp_torusMap]
  rfl

theorem torusMap_comp {X'' : Type} [AddCommGroup X''] (ρ : X' →+ X) (σ : X'' →+ X') :
    SplitTorusPow.torusMap S ρ ≫ SplitTorusPow.torusMap S σ = SplitTorusPow.torusMap S (ρ.comp σ) := by
  refine ext_chV fun χ => ?_
  rw [← Category.id_comp (SplitTorusPow.torusMap S ρ ≫ _), ← Category.assoc, chV_comp_torusMap,
    chV_comp_torusMap, ← Category.id_comp (SplitTorusPow.torusMap S (ρ.comp σ)), chV_comp_torusMap]
  rfl

theorem torusMap_id : SplitTorusPow.torusMap S (AddMonoidHom.id X) = 𝟙 _ := by
  refine ext_chV fun χ => ?_
  rw [← Category.id_comp (SplitTorusPow.torusMap S _), chV_comp_torusMap]
  rfl

end TorusOfCharMap

theorem splitTorus_map_of_charHom : ∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] (X' : Type) [AddCommGroup X'] (ρ : X' →+ X), (∃ (τ : splitTorus S X ⟶ splitTorus S X'), (∀ χ, chV τ χ = charUnit S X (ρ χ))) ∧ ∀ (τ : splitTorus S X ⟶ splitTorus S X'), (∀ χ, chV τ χ = charUnit S X (ρ χ)) → IsMonHom τ ∧ (Function.Bijective ρ → IsIso τ) ∧ ∀ (Z : Over S) (s : Z ⟶ splitTorus S X) (χ : X'), chV (s ≫ τ) χ = chV s (ρ χ) := by
  intro S X _ X' _ ρ
  have key : ∀ τ : splitTorus S X ⟶ splitTorus S X', (∀ χ, chV τ χ = charUnit S X (ρ χ)) →
      τ = SplitTorusPow.torusMap S ρ := fun τ h =>
    TorusOfCharMap.ext_chV fun χ => (h χ).trans (TorusOfCharMap.chV_torusMap ρ χ).symm
  refine ⟨⟨_, TorusOfCharMap.chV_torusMap ρ⟩, fun τ h => ?_⟩
  obtain rfl := key τ h
  refine ⟨SplitTorusPow.isMonHom_torusMap ρ, fun hb => ?_, fun Z s χ => TorusOfCharMap.chV_comp_torusMap ρ s χ⟩
  let e : X' ≃+ X := AddEquiv.ofBijective ρ hb
  refine ⟨⟨SplitTorusPow.torusMap S e.symm.toAddMonoidHom, ?_, ?_⟩⟩
  · rw [TorusOfCharMap.torusMap_comp]
    convert TorusOfCharMap.torusMap_id (S := S) (X := X)
    ext x
    exact e.apply_symm_apply x
  · rw [TorusOfCharMap.torusMap_comp]
    convert TorusOfCharMap.torusMap_id (S := S) (X := X')
    ext x
    exact e.symm_apply_apply x

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubMemSmulTopOfNeatLevel
section
open NumberField

namespace GlobalTheory.NeatLevel

variable {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]

lemma val_pow_apply (W : Submodule R M) (S : Module.End R W) (T : Module.End R M)
    (hST : ∀ y : W, ((S y : W) : M) = T y) (k : ℕ) (y : W) :
    (((S ^ k) y : W) : M) = (T ^ k) y := by
  induction k generalizing y with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hST]

end GlobalTheory.NeatLevel

theorem GlobalTheory.sub_mem_smul_top_of_neat_level : ∀ (E : Type) [Field E] [NumberField E] (La Λ Q : Type) [AddCommGroup La] [Module (𝓞 E) La] [AddCommGroup Λ] [Module (𝓞 E) Λ] [AddCommGroup Q] [Module (𝓞 E) Q] (J : Ideal (𝓞 E)) (n N m g₁ g₂ : ℕ) (I₁ I₂ : Ideal (𝓞 E)) (ev : La →ₗ[𝓞 E] Q) (ψ : Λ →ₗ[𝓞 E] Q) (θ : Q →ₗ[𝓞 E] Q) (F : Λ →ₗ[𝓞 E] Λ) (gM : La →ₗ[𝓞 E] La), Module.Finite (𝓞 E) Λ → Module.IsTorsionFree (𝓞 E) Λ → 0 < n → (n : 𝓞 E) ∈ J → (∀ a, ev a = 0 ↔ a ∈ J • (⊤ : Submodule (𝓞 E) La)) → (∀ q : Q, (∀ c ∈ J, c • q = 0) → ∃ a, ev a = q) → (∀ b, ψ b = 0 ↔ ∃ b', b = n • b') → (∀ q : Q, n • q = 0 → ∃ b, ψ b = q) → (∀ b, ψ (F b) = θ (ψ b)) → (∀ a, θ (ev (gM a)) = ev a) → 0 < N → F ^ N = 1 → g₁.Prime → g₂.Prime → g₁ ≠ g₂ → I₁ ≠ ⊤ → I₂ ≠ ⊤ → (g₁ : 𝓞 E) ∈ I₁ → (g₂ : 𝓞 E) ∈ I₂ → J ≤ I₁ → J ≤ I₂ → (∀ x, ((gM - 1) ^ m) x ∈ I₁ • (⊤ : Submodule (𝓞 E) La)) → (∀ x, ((gM - 1) ^ m) x ∈ I₂ • (⊤ : Submodule (𝓞 E) La)) → ∀ a, gM a - a ∈ J • (⊤ : Submodule (𝓞 E) La) := by

  intro E _ _ La Λ Q _ _ _ _ _ _ J n N m g₁ g₂ I₁ I₂ ev ψ θ F gM hfin htf hn hnJ hev hevs hψ hψs hFθ hθ hN hFN hg₁ hg₂ hg hI₁ hI₂ hgI₁ hgI₂ hJI₁ hJI₂ hu₁ hu₂
  have hevJ : ∀ c : 𝓞 E, c ∈ J → ∀ a, c • ev a = 0 := by
    intro c hc a
    rw [← map_smul, hev]
    exact Submodule.smul_mem_smul hc trivial
  have hevψ : ∀ a, ∃ μ, ψ μ = ev a := by
    intro a; apply hψs
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]; exact hevJ _ hnJ a
  set G := F ^ (N - 1) with hGdef
  have hGF : G * F = 1 := by
    rw [hGdef, ← pow_succ, Nat.sub_add_cancel hN, hFN]
  have hFG : F * G = 1 := by
    rw [hGdef, ← pow_succ', Nat.sub_add_cancel hN, hFN]
  have hFGl : ∀ l, F (G l) = l := fun l => by
    rw [← Module.End.mul_apply, hFG, Module.End.one_apply]
  have hGFl : ∀ l, G (F l) = l := fun l => by
    rw [← Module.End.mul_apply, hGF, Module.End.one_apply]
  have hkey : ∀ (l : Λ) (a : La), ψ l = ev a → ψ (G l) = ev (gM a) := by
    intro l a hla
    obtain ⟨μ, hμ⟩ := hevψ (gM a)
    have h1 : ψ (F (μ - G l)) = 0 := by
      rw [map_sub, map_sub, hFθ, hμ, hθ, hFGl, hla, sub_self]
    obtain ⟨b', hb'⟩ := (hψ _).1 h1
    have h2 : μ - G l = n • G b' := by
      rw [← map_nsmul, ← hb', hGFl]
    have h3 : ψ (μ - G l) = 0 := (hψ _).2 ⟨G b', h2⟩
    rw [map_sub, sub_eq_zero] at h3
    rw [← h3, hμ]
  let W : Submodule (𝓞 E) Λ := (LinearMap.range ev).comap ψ
  have hGW : ∀ l ∈ W, G l ∈ W := by
    rintro l ⟨a, ha⟩; exact ⟨gM a, (hkey l a ha.symm).symm⟩
  obtain ⟨J', hJ'⟩ : J ∣ Ideal.span {(n : 𝓞 E)} :=
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hnJ)
  have hJ'W : ∀ c' : 𝓞 E, c' ∈ J' → ∀ l, c' • l ∈ W := by
    intro c' hc' l
    obtain ⟨a, ha⟩ := hevs (ψ (c' • l)) (by
      intro c hc
      have hcc : c * c' ∈ Ideal.span {(n : 𝓞 E)} := by rw [hJ']; exact Ideal.mul_mem_mul hc hc'
      obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hcc
      rw [← map_smul, smul_smul, ← hr, mul_comm, mul_smul, Nat.cast_smul_eq_nsmul]
      exact (hψ _).2 ⟨_, rfl⟩)
    exact ⟨a, ha⟩
  have hnW : ∀ I : Ideal (𝓞 E), J ≤ I → ∀ l : Λ, n • l ∈ I • W := by
    intro I hJI l
    have h1 : (n : 𝓞 E) • l ∈ (J * J') • (⊤ : Submodule (𝓞 E) Λ) :=
      Submodule.smul_mem_smul (by rw [← hJ']; exact Ideal.mem_span_singleton_self _) trivial
    rw [Submodule.mul_smul, Nat.cast_smul_eq_nsmul] at h1
    exact Submodule.smul_mono hJI (Submodule.smul_le.2 fun c' hc' l _ => hJ'W c' hc' l) h1
  have hpow : ∀ k (l : Λ) (a : La), ψ l = ev a → ψ (((G - 1 : Module.End (𝓞 E) Λ) ^ k) l) = ev (((gM - 1 : Module.End (𝓞 E) La) ^ k) a) := by
    intro k
    induction k with
    | zero => intro l a h; simpa using h
    | succ k ih =>
      intro l a h
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply]
      apply ih
      simp [map_sub, hkey l a h, h]
  have hunipW : ∀ I : Ideal (𝓞 E), J ≤ I → (∀ x, ((gM - 1) ^ m) x ∈ I • (⊤ : Submodule (𝓞 E) La)) →
      ∀ l ∈ W, ((G - 1) ^ m) l ∈ I • W := by
    rintro I hJI hu l ⟨a, ha⟩
    have hx := hpow m l a ha.symm
    have hmem : ev (((gM - 1) ^ m) a) ∈ (I • W).map ψ := by
      have h1 : ev (((gM - 1) ^ m) a) ∈ (I • (⊤ : Submodule (𝓞 E) La)).map ev := ⟨_, hu a, rfl⟩
      rw [Submodule.map_smul'', Submodule.map_top] at h1
      rw [Submodule.map_smul'']
      refine Submodule.smul_mono le_rfl ?_ h1
      rintro _ ⟨b, rfl⟩
      obtain ⟨μ, hμ⟩ := hevψ b
      exact ⟨μ, ⟨b, hμ.symm⟩, hμ⟩
    obtain ⟨z, hz, hzx⟩ := hmem
    have hd : ψ (((G - 1) ^ m) l - z) = 0 := by rw [map_sub, hzx, hx, sub_self]
    obtain ⟨b', hb'⟩ := (hψ _).1 hd
    have : ((G - 1) ^ m) l = z + n • b' := by rw [← hb']; abel
    rw [this]; exact Submodule.add_mem _ hz (hnW I hJI b')
  haveI := hfin; haveI := htf
  let Gr : Module.End (𝓞 E) W := G.restrict hGW
  have hGr : ∀ y : W, ((Gr y : W) : Λ) = G y := fun y => rfl
  have hGr1 : ∀ y : W, (((Gr - 1) y : W) : Λ) = (G - 1) y := fun y => rfl
  have hGN : G ^ N = 1 := by
    rw [hGdef, ← pow_mul, mul_comm, pow_mul, hFN, one_pow]
  have hGrN : Gr ^ N = 1 := by
    apply LinearMap.ext; intro y; apply Subtype.ext
    rw [GlobalTheory.NeatLevel.val_pow_apply W Gr G hGr, hGN]; rfl
  have hsub : ∀ I : Ideal (𝓞 E), J ≤ I → (∀ x, ((gM - 1) ^ m) x ∈ I • (⊤ : Submodule (𝓞 E) La)) →
      ∀ y : W, ((Gr - 1) ^ m) y ∈ I • (⊤ : Submodule (𝓞 E) W) := by
    intro I hJI hu y
    have h1 : ((((Gr - 1) ^ m) y : W) : Λ) ∈ (I • (⊤ : Submodule (𝓞 E) W)).map W.subtype := by
      rw [Submodule.map_smul'', Submodule.map_subtype_top, GlobalTheory.NeatLevel.val_pow_apply W (Gr - 1) (G - 1) hGr1]
      exact hunipW I hJI hu y y.2
    obtain ⟨z, hz, hzy⟩ := h1
    have hzz : z = ((Gr - 1) ^ m) y := Subtype.ext hzy
    rwa [← hzz]
  have hGr1' : Gr = 1 := GlobalTheory.eq_one_of_finite_order_unipotent_mod_two_primes E W Gr N m g₁ g₂ I₁ I₂
    hN hGrN hg₁ hg₂ hg hI₁ hI₂ hgI₁ hgI₂ (hsub I₁ hJI₁ hu₁) (hsub I₂ hJI₂ hu₂)
  intro a
  obtain ⟨l, hl⟩ := hevψ a
  have hlW : l ∈ W := ⟨a, hl.symm⟩
  have hGl : G l = l := by
    have := congrArg (fun T : Module.End (𝓞 E) W => ((T ⟨l, hlW⟩ : W) : Λ)) hGr1'
    exact (hGr ⟨l, hlW⟩).symm.trans (by simpa using this)
  have h := hkey l a hl
  rw [hGl, hl] at h
  rw [← hev, map_sub, ← h, sub_self]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrScaleNeZeroAt
section
noncomputable section

open NumberField Polynomial Formalism.BasicNotions Formalism.L2.DIV

namespace GlobalTheory.FamSep

section General

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
  {m : ℕ} (A : FamIn K G Pl0 T m)

theorem trScale_ne_zero_at {P : Pl0} (hq : A.q P ≠ 0) : trScale A.r m A.t A.q A.etaVal P ≠ 0 :=
  mul_ne_zero (Units.ne_zero _) (pow_ne_zero _ (Nat.cast_ne_zero.2 hq))

theorem typesSep_of_local (hq : ∀ P : (A.fam.R A.fam.μ0).Pl, A.q ((A.fam.R A.fam.μ0).pl P) ≠ 0)
    (h0 : ∀ P, A.heckeR A.μ0 (P, 0) = 1) : A.fam.TypesSep := by
  intro Sg hSg Sg' hSg' hne j
  obtain ⟨P, hP⟩ := (A.fam.R A.fam.μ0).sep_of_mem_ixFin hSg hSg' hne
  exact ⟨P, fun h => hP (dualPoly_inj (trScale_ne_zero_at A (hq P)) (A.const_of h0 Sg hSg _) (A.const_of h0 Sg' hSg' _) h)⟩

theorem typesSep_of_ok {s : ℕ} (hOk : A.fam.Ok s) (h0 : ∀ P, A.heckeR A.μ0 (P, 0) = 1) : A.fam.TypesSep :=
  typesSep_of_local A (fun P => ((hOk.what₂ A.fam.μ0).q_pos P).ne') h0

end General

section Real

open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

end Real

end GlobalTheory.FamSep

end
end

