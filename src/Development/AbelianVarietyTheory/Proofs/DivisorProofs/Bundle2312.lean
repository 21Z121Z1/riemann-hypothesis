import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0080
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2263
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2259
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0027
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2270
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2095

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardEqZeroOfTrivialOnDisjointCover
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PicDisj

open TopologicalSpace

theorem map_gm {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)ˣ) :
    Units.map (f.stalkMap y).hom.toMonoidHom (gm (𝟙 X) (f y) U a) = gm f y U a := by
  refine Units.ext ?_
  rw [gm, gm, dif_pos h, dif_pos (show (𝟙 X : X ⟶ X) (f y) ∈ U from h)]
  exact Scheme.Hom.germ_stalkMap_apply f U y h a.val

theorem gm_image {X Y : Scheme.{0}} (f : Y ⟶ X) [IsOpenImmersion f] (y : Y) (V : Y.Opens) (h : y ∈ V) (a : Γ(Y, V)ˣ) :
    gm f y (f ''ᵁ V) (Units.map (f.appIso V).inv.hom.toMonoidHom a) = gm (𝟙 Y) y V a := by
  refine Units.ext ?_
  have h' : f y ∈ f ''ᵁ V := ⟨y, h, rfl⟩
  rw [gm, gm, dif_pos h', dif_pos (show (𝟙 Y : Y ⟶ Y) y ∈ V from h)]
  change (Y.presheaf.germ (f ⁻¹ᵁ (f ''ᵁ V)) y h').hom (((f.appIso V).inv ≫ f.app (f ''ᵁ V)).hom a.val) =
    (Y.presheaf.germ V y h).hom a.val
  rw [Scheme.Hom.appIso_inv_app]
  exact Y.presheaf.germ_res_apply _ y _ _

theorem exists_gen_of_rel {Y : Scheme.{0}} {N : LB Y} (hN : N.IsLB) (P : N.ι → ∀ y : Y, (Y.presheaf.stalk y)ˣ → Prop)
    (loc : ∀ p, ∀ y ∈ N.U p, ∃ W : Y.Opens, W ≤ N.U p ∧ y ∈ W ∧ ∃ s : Γ(Y, W)ˣ, ∀ y' ∈ W, P p y' (gm (𝟙 Y) y' W s))
    (cmp : ∀ p q y u u', y ∈ N.U p → y ∈ N.U q → P p y u → P q y u' → u = gm (𝟙 Y) y _ (N.g p q) * u') :
    ∃ t : N.Gen, t.IsGen := by
  have uniq : ∀ p y u u', y ∈ N.U p → P p y u → P p y u' → u = u' := fun p y u u' hy h h' => by
    have e := gm_cocycle hN (𝟙 Y) y hy hy hy
    rw [cmp p p y u u' hy hy h h', mul_eq_left.1 e, _root_.one_mul]
  have key : ∀ p, ∃ a : Γ(Y, N.U p)ˣ, ∀ y ∈ N.U p, P p y (gm (𝟙 Y) y _ a) := fun p => by
    choose W hW hy s hs using fun y : (N.U p : Set Y) => loc p y.1 y.2
    have cp : ∀ k l, res (inf_le_left : W k ⊓ W l ≤ W k) (s k) = res inf_le_right (s l) := fun k l =>
      unit_ext fun y h => by
        rw [gm_res _ y _ h, gm_res _ y _ h]
        exact uniq p y _ _ (hW k h.1) (hs k y h.1) (hs l y h.2)
    have hc : N.U p ≤ iSup W := fun x hx => Opens.mem_iSup.2 ⟨⟨x, hx⟩, hy _⟩
    obtain ⟨b, hb, -⟩ := Y.sheaf.existsUnique_gluing' W (N.U p) (fun k => homOfLE (hW k)) hc (fun k => (s k).val)
      fun k l => congrArg Units.val (cp k l)
    have hu : IsUnit (M := Γ(Y, N.U p)) b := Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun x hx => by
      have := (s ⟨x, hx⟩).isUnit.map (Y.presheaf.germ _ x (hy ⟨x, hx⟩)).hom
      rw [← hb] at this
      exact (Y.presheaf.germ_res_apply (homOfLE (hW ⟨x, hx⟩)) x (hy ⟨x, hx⟩) b) ▸ this
    refine ⟨hu.unit, fun y h => ?_⟩
    have e : res (hW ⟨y, h⟩) hu.unit = s ⟨y, h⟩ := Units.ext (hb _)
    rw [← gm_res _ y (hW ⟨y, h⟩) (hy ⟨y, h⟩), e]
    exact hs _ y (hy _)
  choose a ha using key
  exact ⟨⟨a⟩, (isGen_iff_germ _).2 fun y i j hi hj => cmp i j y _ _ hi hj (ha i y hi) (ha j y hj)⟩

theorem eq_zero_of_pull_eq_zero : ∀ {Y : Scheme.{0}} {κ : Type} [Finite κ] {Z : κ → Scheme.{0}} (f : ∀ i, Z i ⟶ Y) [∀ i, IsOpenImmersion (f i)], (⨆ i, (f i).opensRange = ⊤) → (Pairwise fun i i' => Disjoint (f i).opensRange (f i').opensRange) → ∀ d : Pic Y, (∀ i, GlobalTheory.CechPic.pull (f i) d = 0) → d = 0 := by
  intro Y κ _ Z f _ hcov hdis d hd
  obtain ⟨L, hL, rfl⟩ := cls_surj d
  choose t ht using fun i => (cls_eq_zero_iff (pull_isLB hL (f i))).1 (hd i)
  have surj : ∀ y : Y, ∃ i z, f i z = y := fun y => by
    have : y ∈ ⨆ i, (f i).opensRange := by rw [hcov]; trivial
    obtain ⟨i, z, hz⟩ := Opens.mem_iSup.1 this
    exact ⟨i, z, hz⟩
  refine (cls_eq_zero_iff hL).2 (exists_gen_of_rel hL (fun p y u => ∀ i (z : Z i) (u' : (Y.presheaf.stalk (f i z))ˣ),
    f i z = y → HEq u' u → Units.map ((f i).stalkMap z).hom.toMonoidHom u' =
      gm (𝟙 _) z ((L.pull (f i)).U fun _ => p) ((t i).s fun _ => p)) ?_ ?_)
  · intro p y hy
    obtain ⟨i, z, rfl⟩ := surj y
    refine ⟨f i ''ᵁ ((L.pull (f i)).U fun _ => p), ?_, ⟨z, mem_pull.2 hy, rfl⟩,
      Units.map ((f i).appIso _).inv.hom.toMonoidHom ((t i).s fun _ => p), ?_⟩
    · rintro _ ⟨w, hw, rfl⟩
      exact mem_pull.1 hw
    · rintro y' ⟨w, hw, hy'⟩ j z' u' rfl hu
      obtain rfl : i = j := by
        by_contra hne
        have hm : f j z' ∈ (f i).opensRange ⊓ (f j).opensRange := ⟨⟨w, hy'⟩, ⟨z', rfl⟩⟩
        rw [(hdis hne).eq_bot] at hm
        exact hm
      obtain rfl : w = z' := (f i).isOpenEmbedding.injective hy'
      rw [eq_of_heq hu, map_gm (f i) w _ (show f i w ∈ f i ''ᵁ ((L.pull (f i)).U fun _ => p) from ⟨w, hw, rfl⟩), gm_image _ _ _ hw]
  · intro p q y u u' hp hq h h'
    obtain ⟨i, z, rfl⟩ := surj y
    apply Units.map_injective (f := ((f i).stalkMap z).hom.toMonoidHom)
      (ConcreteCategory.bijective_of_isIso ((f i).stalkMap z)).1
    rw [map_mul, h i z u rfl HEq.rfl, h' i z u' rfl HEq.rfl, map_gm (f i) z (L.U p ⊓ L.U q) ⟨hp, hq⟩,
      (isGen_iff_germ _).1 (ht i) z (fun _ => p) (fun _ => q) (mem_pull.2 hp) (mem_pull.2 hq),
      gm_pull_g L (f i) (𝟙 _) z _ _ (mem_pull.2 hp) (mem_pull.2 hq), Category.id_comp]

end GlobalTheory.PicDisj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardEqZeroOfTwoOpenCoverUnitsSplit
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CechPic

open TopologicalSpace

theorem exists_units_of_gen_restrict {Z : Scheme.{0}} (L : LB Z) (O : Z.Opens) (t : LB.Gen (L.pull O.ι))
    (ht : t.IsGen) : ∃ b : ∀ i, Γ(Z, L.U i ⊓ O)ˣ, ∀ (i j : L.ι) (x : Z), x ∈ L.U i → x ∈ L.U j → x ∈ O →
      gm (𝟙 Z) x (L.U i ⊓ O) (b i) = gm (𝟙 Z) x (L.U i ⊓ L.U j) (L.g i j) * gm (𝟙 Z) x (L.U j ⊓ O) (b j) := by
  choose c hc using fun i : L.ι => exists_ext_unit O.ι ((L.pull O.ι).U (fun _ => i)) (t.s (fun _ => i))
  have le : ∀ i, L.U i ⊓ O ≤ O.ι ''ᵁ ((L.pull O.ι).U (fun _ => i)) := by
    intro i x hx
    have m : (⟨x, hx.2⟩ : O.toScheme) ∈ (L.pull O.ι).U (fun _ => i) := mem_pull.2 hx.1
    exact ⟨⟨x, hx.2⟩, m, rfl⟩
  refine ⟨fun i => res (le i) (c i), fun i j x hi hj hx => ?_⟩
  let z : O.toScheme := ⟨x, hx⟩
  have mi : z ∈ (L.pull O.ι).U (fun _ => i) := mem_pull.2 hi
  have mj : z ∈ (L.pull O.ι).U (fun _ => j) := mem_pull.2 hj
  have hW : O.ι z ∈ L.U i ⊓ L.U j ⊓ O := ⟨⟨hi, hj⟩, hx⟩
  have hWi : O.ι z ∈ L.U i ⊓ O := ⟨hi, hx⟩
  have hWj : O.ι z ∈ L.U j ⊓ O := ⟨hj, hx⟩
  have hWij : O.ι z ∈ L.U i ⊓ L.U j := ⟨hi, hj⟩
  have l₁ : L.U i ⊓ L.U j ⊓ O ≤ L.U i ⊓ L.U j := inf_le_left
  have l₂ : L.U i ⊓ L.U j ⊓ O ≤ L.U j ⊓ O := le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have key := gm_inj O.ι z (U := L.U i ⊓ O) (U' := L.U i ⊓ L.U j ⊓ O) hWi hW
    (a := res (le i) (c i)) (b := res l₁ (L.g i j) * res l₂ (res (le j) (c j))) (by
      rw [map_mul, gm_res O.ι z l₁ hW, gm_res O.ι z l₂ hW, gm_res O.ι z (le j) hWj, gm_res O.ι z (le i) hWi]
      have e₁ := hc i O.toScheme (𝟙 _) z mi
      have e₂ := hc j O.toScheme (𝟙 _) z mj
      rw [Category.id_comp] at e₁ e₂
      rw [e₁, e₂, (isGen_iff_germ t).1 ht z _ _ mi mj, gm_pull_g L O.ι (𝟙 _) z _ _ mi mj, Category.id_comp])
  rw [map_mul, gm_res (𝟙 Z) (O.ι z) l₁ hW, gm_res (𝟙 Z) (O.ι z) l₂ hW] at key
  exact key

theorem eq_zero_of_pull_eq_zero_of_units_split : ∀ (Z : Scheme.{0}) (O O' : Z.Opens), O ⊔ O' = ⊤ →
    (∀ F : Γ(Z, O ⊓ O')ˣ, ∃ (u : Γ(Z, O)ˣ) (u' : Γ(Z, O')ˣ),
      F = res (inf_le_left : O ⊓ O' ≤ O) u * res (inf_le_right : O ⊓ O' ≤ O') u') →
    ∀ c : Pic Z, GlobalTheory.CechPic.pull O.ι c = 0 → GlobalTheory.CechPic.pull O'.ι c = 0 → c = 0 := by
  intro Z O O' hcov hsplit c hc hc'
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  rw [← cls_pull hL O.ι (pull_isLB hL O.ι)] at hc
  rw [← cls_pull hL O'.ι (pull_isLB hL O'.ι)] at hc'
  obtain ⟨t, ht⟩ := (cls_eq_zero_iff _).1 hc
  obtain ⟨t', ht'⟩ := (cls_eq_zero_iff _).1 hc'
  obtain ⟨b, hb⟩ := exists_units_of_gen_restrict L O t ht
  obtain ⟨b', hb'⟩ := exists_units_of_gen_restrict L O' t' ht'
  have key₁ : ∀ {G : Type} [CommGroup G] (a x y : G), a * x * (a * y)⁻¹ = x * y⁻¹ := fun a x y => by
    rw [← div_eq_mul_inv, ← div_eq_mul_inv, mul_div_mul_left_eq_div]
  have key₂ : ∀ {G : Type} [CommGroup G] (a x y : G), a * x * y * x⁻¹ = a * y := fun a x y => by
    rw [mul_right_comm, mul_inv_cancel_right]

  let W : L.ι → Z.Opens := fun i => L.U i ⊓ (O ⊓ O')
  have lw : ∀ i, W i ≤ L.U i ⊓ O := fun i => inf_le_inf_left _ inf_le_left
  have lw' : ∀ i, W i ≤ L.U i ⊓ O' := fun i => inf_le_inf_left _ inf_le_right
  let q : ∀ i, Γ(Z, W i)ˣ := fun i => res (lw i) (b i) * (res (lw' i) (b' i))⁻¹
  have gq : ∀ i x, x ∈ W i → gm (𝟙 Z) x (W i) (q i) =
      gm (𝟙 Z) x (L.U i ⊓ O) (b i) * (gm (𝟙 Z) x (L.U i ⊓ O') (b' i))⁻¹ := fun i x hx => by
    simp only [q, map_mul, map_inv, gm_res (𝟙 Z) x (lw i) hx, gm_res (𝟙 Z) x (lw' i) hx]
  obtain ⟨F, hF⟩ := glue_unit (O ⊓ O') W (fun i => inf_le_right) (fun x hx => by
      obtain ⟨i, hi⟩ := exists_chart hL x
      exact Opens.mem_iSup.2 ⟨i, hi, hx⟩) q (fun i j x hx => by
      rw [gq i x hx.1, gq j x hx.2, hb i j x hx.1.1 hx.2.1 hx.1.2.1, hb' i j x hx.1.1 hx.2.1 hx.1.2.2, key₁])
  obtain ⟨u, u', hu⟩ := hsplit F

  have gF : ∀ i x, x ∈ W i → gm (𝟙 Z) x (L.U i ⊓ O) (b i) =
      gm (𝟙 Z) x (L.U i ⊓ O') (b' i) * gm (𝟙 Z) x O u * gm (𝟙 Z) x O' u' := fun i x hx => by
    have e := congrArg (gm (𝟙 Z) x (W i)) (hF i)
    rw [gm_res (𝟙 Z) x _ hx, gq i x hx, hu, map_mul, gm_res (𝟙 Z) x _ hx.2, gm_res (𝟙 Z) x _ hx.2] at e
    rw [(mul_inv_eq_iff_eq_mul).1 e.symm]
    ac_rfl

  have loc : ∀ i, ∃ s : Γ(Z, L.U i)ˣ,
      (∀ y, y ∈ L.U i → y ∈ O → gm (𝟙 Z) y (L.U i) s = gm (𝟙 Z) y (L.U i ⊓ O) (b i) * (gm (𝟙 Z) y O u)⁻¹) ∧
      (∀ y, y ∈ L.U i → y ∈ O' → gm (𝟙 Z) y (L.U i) s = gm (𝟙 Z) y (L.U i ⊓ O') (b' i) * gm (𝟙 Z) y O' u') := by
    intro i
    let V : Bool → Z.Opens := fun β => Bool.rec (L.U i ⊓ O') (L.U i ⊓ O) β
    let v : ∀ β, Γ(Z, V β)ˣ := fun β => Bool.rec (motive := fun β => Γ(Z, V β)ˣ)
      (b' i * res (inf_le_right : L.U i ⊓ O' ≤ O') u') (b i * (res (inf_le_right : L.U i ⊓ O ≤ O) u)⁻¹) β
    have hV : ∀ β, V β ≤ L.U i := fun β => by cases β <;> exact inf_le_left
    have g₁ : ∀ y, y ∈ L.U i ⊓ O → gm (𝟙 Z) y (V true) (v true) =
        gm (𝟙 Z) y (L.U i ⊓ O) (b i) * (gm (𝟙 Z) y O u)⁻¹ := fun y hy => by
      show gm (𝟙 Z) y (L.U i ⊓ O) (b i * (res (inf_le_right : L.U i ⊓ O ≤ O) u)⁻¹) = _
      rw [map_mul, map_inv, gm_res (𝟙 Z) y _ hy]
    have g₀ : ∀ y, y ∈ L.U i ⊓ O' → gm (𝟙 Z) y (V false) (v false) =
        gm (𝟙 Z) y (L.U i ⊓ O') (b' i) * gm (𝟙 Z) y O' u' := fun y hy => by
      show gm (𝟙 Z) y (L.U i ⊓ O') (b' i * res (inf_le_right : L.U i ⊓ O' ≤ O') u') = _
      rw [map_mul, gm_res (𝟙 Z) y _ hy]
    obtain ⟨s, hs⟩ := glue_unit (L.U i) V hV (fun y hy => by
        have h : y ∈ O ⊔ O' := hcov ▸ (trivial : y ∈ (⊤ : Z.Opens))
        rcases Opens.mem_sup.1 h with h | h
        · exact Opens.mem_iSup.2 ⟨true, hy, h⟩
        · exact Opens.mem_iSup.2 ⟨false, hy, h⟩) v (fun β β₂ y hy => by
        cases β <;> cases β₂
        · rfl
        · rw [g₀ y hy.1, g₁ y hy.2, gF i y ⟨hy.1.1, hy.2.2, hy.1.2⟩, key₂]
        · rw [g₁ y hy.1, g₀ y hy.2, gF i y ⟨hy.1.1, hy.1.2, hy.2.2⟩, key₂]
        · rfl)
    refine ⟨s, fun y hi ho => ?_, fun y hi ho => ?_⟩
    · have e := congrArg (gm (𝟙 Z) y (V true)) (hs true)
      rw [gm_res (𝟙 Z) y (hV true) (show y ∈ L.U i ⊓ O from ⟨hi, ho⟩)] at e
      exact e.trans (g₁ y ⟨hi, ho⟩)
    · have e := congrArg (gm (𝟙 Z) y (V false)) (hs false)
      rw [gm_res (𝟙 Z) y (hV false) (show y ∈ L.U i ⊓ O' from ⟨hi, ho⟩)] at e
      exact e.trans (g₀ y ⟨hi, ho⟩)
  choose s hs using loc
  refine (cls_eq_zero_iff hL).2 ⟨⟨s⟩, (isGen_iff_germ _).2 fun y i j hi hj => ?_⟩
  have h : y ∈ O ⊔ O' := hcov ▸ (trivial : y ∈ (⊤ : Z.Opens))
  rcases Opens.mem_sup.1 h with h | h
  · show gm (𝟙 Z) y (L.U i) (s i) = _ * gm (𝟙 Z) y (L.U j) (s j)
    rw [(hs i).1 y hi h, (hs j).1 y hj h, hb i j y hi hj h, _root_.mul_assoc]
  · show gm (𝟙 Z) y (L.U i) (s i) = _ * gm (𝟙 Z) y (L.U j) (s j)
    rw [(hs i).2 y hi h, (hs j).2 y hj h, hb' i j y hi hj h, _root_.mul_assoc]

end GlobalTheory.CechPic
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardExtendOfLocallyTrivialNormalCodimTwo
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ExtendClass

open GlobalTheory.GlueLineBundle TopologicalSpace

variable {X : Scheme.{0}}

theorem gm_eq_map {Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (hy : f y ∈ U) (a : Γ(X, U)ˣ) :
    gm f y U a = Units.map (f.stalkMap y).hom.toMonoidHom (gm (𝟙 X) (f y) U a) := by
  apply Units.ext
  rw [gm_val f y U hy, Units.coe_map, gm_val (𝟙 X) (f y) U hy]
  show _ = (f.stalkMap y).hom ((X.presheaf.germ U (f y) hy).hom a.val)
  rw [Scheme.Hom.germ_stalkMap_apply]

theorem map_stalk_inj {Y : Scheme.{0}} (j : Y ⟶ X) [IsOpenImmersion j] (y : Y) :
    Function.Injective (Units.map (j.stalkMap y).hom.toMonoidHom) :=
  Units.map_injective (f := (j.stalkMap y).hom.toMonoidHom)
    (asIso (j.stalkMap y)).commRingCatIsoToRingEquiv.injective

theorem exists_res_eq {U V : X.Opens} (h : V ≤ U) (hb : Function.Bijective (resG X h)) (u : Γ(X, V)ˣ) :
    ∃ a : Γ(X, U)ˣ, res h a = u := by
  obtain ⟨a, ha⟩ := hb.2 u.val
  obtain ⟨b, hb'⟩ := hb.2 u.inv
  have e1 : a * b = 1 := hb.1 (by rw [map_mul, map_one, ha, hb']; exact u.val_inv)
  exact ⟨⟨a, b, e1, (mul_comm _ _).trans e1⟩, Units.ext ha⟩

theorem eq_of_gm_ι (W : X.Opens) (hW : ∀ V : X.Opens, Function.Bijective (resG X (inf_le_left : V ⊓ W ≤ V)))
    {V : X.Opens} {a b : Γ(X, V)ˣ} (h : ∀ w : W.toScheme, W.ι w ∈ V → gm W.ι w V a = gm W.ι w V b) : a = b := by
  have e : res (inf_le_left : V ⊓ W ≤ V) a = res inf_le_left b := by
    apply unit_ext_imm
    intro x hx
    have hxW : x ∈ W := hx.2
    have hxV : x ∈ V := hx.1
    have hx' : W.ι ⟨x, hxW⟩ ∈ V ⊓ W := hx
    refine ⟨_, W.ι, inferInstance, ⟨x, hxW⟩, rfl, ?_⟩
    exact (gm_res W.ι _ inf_le_left hx' a).trans ((h _ hxV).trans (gm_res W.ι _ inf_le_left hx' b).symm)
  exact Units.ext ((hW V).1 (congrArg Units.val e))

end GlobalTheory.ExtendClass

namespace GlobalTheory.ExtendClass
open GlobalTheory.GlueLineBundle TopologicalSpace
variable {X : Scheme.{0}}

theorem exists_sigma (W : X.Opens) {M : LB W.toScheme} (N : X.Opens)
    (t : LB.Gen (M.pull (X.homOfLE (inf_le_right : N ⊓ W ≤ W)))) (ht : t.IsGen) :
    ∃ σ : ∀ k, Γ(W.toScheme, W.ι ⁻¹ᵁ N ⊓ M.U k)ˣ, ∀ (z : W.toScheme) (k k' : M.ι), W.ι z ∈ N → z ∈ M.U k →
      z ∈ M.U k' → gm (𝟙 _) z _ (σ k) = gm (𝟙 _) z (M.U k ⊓ M.U k') (M.g k k') * gm (𝟙 _) z _ (σ k') := by
  revert t
  set ι₁ := X.homOfLE (inf_le_right : N ⊓ W ≤ W) with hι₁
  intro t ht
  have pre : ∀ z : W.toScheme, W.ι z ∈ N → ∃ a : (N ⊓ W : X.Opens).toScheme, ι₁ a = z := fun z hz =>
    ⟨⟨z.1, hz, z.2⟩, Subtype.ext (Scheme.homOfLE_apply _ _)⟩
  have hle : ∀ k, W.ι ⁻¹ᵁ N ⊓ M.U k ≤ ι₁ ''ᵁ (M.pull ι₁).U (fun _ => k) := fun k z hz => by
    obtain ⟨a, rfl⟩ := pre z hz.1
    exact ι₁.apply_mem_image_iff.2 (mem_pull.2 hz.2)
  refine ⟨fun k => res (hle k) (imU ι₁ _ (t.s fun _ => k)), fun z k k' hz hk hk' => ?_⟩
  obtain ⟨a, rfl⟩ := pre z hz
  have ev : ∀ k, ι₁ a ∈ M.U k → gm ι₁ a (W.ι ⁻¹ᵁ N ⊓ M.U k) (res (hle k) (imU ι₁ _ (t.s fun _ => k))) =
      gm (𝟙 _) a _ (t.s fun _ => k) := fun k hk => by
    have hm : ι₁ a ∈ W.ι ⁻¹ᵁ N ⊓ M.U k := ⟨hz, hk⟩
    rw [gm_res ι₁ a (hle k) hm]
    have := gm_imU ι₁ (𝟙 _) a ((M.pull ι₁).U fun _ => k) (mem_pull.2 hk) (t.s fun _ => k)
    rwa [Category.id_comp] at this
  have eg : gm ι₁ a (M.U k ⊓ M.U k') (M.g k k') = gm (𝟙 _) a _ ((M.pull ι₁).g (fun _ => k) (fun _ => k')) := by
    have := gm_pull_g M ι₁ (𝟙 _) a (fun _ => k) (fun _ => k') (mem_pull.2 hk) (mem_pull.2 hk')
    rw [Category.id_comp] at this
    exact this.symm
  have m1 : ι₁ a ∈ W.ι ⁻¹ᵁ N ⊓ M.U k := ⟨hz, hk⟩
  have m2 : ι₁ a ∈ M.U k ⊓ M.U k' := ⟨hk, hk'⟩
  have m3 : ι₁ a ∈ W.ι ⁻¹ᵁ N ⊓ M.U k' := ⟨hz, hk'⟩
  apply map_stalk_inj ι₁ a
  beta_reduce
  rw [map_mul, ← gm_eq_map ι₁ a _ m1, ← gm_eq_map ι₁ a _ m2, ← gm_eq_map ι₁ a _ m3,
    ev k hk, ev k' hk', eg]
  exact (isGen_iff_germ t).1 ht a (fun _ => k) (fun _ => k') (mem_pull.2 hk) (mem_pull.2 hk')

end GlobalTheory.ExtendClass

namespace GlobalTheory.ExtendClass
open GlobalTheory.GlueLineBundle TopologicalSpace
variable {X : Scheme.{0}}

theorem mul_ringHom_units_ratio {G : Type} [CommGroup G] (g a b : G) : g * a * (g * b)⁻¹ = a * b⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem exists_ratio (W : X.Opens) {M : LB W.toScheme} (hM : M.IsLB) {I : Type} (N : I → X.Opens)
    (σ : ∀ x k, Γ(W.toScheme, W.ι ⁻¹ᵁ N x ⊓ M.U k)ˣ)
    (hσ : ∀ x (z : W.toScheme) (k k' : M.ι), W.ι z ∈ N x → z ∈ M.U k → z ∈ M.U k' →
      gm (𝟙 _) z _ (σ x k) = gm (𝟙 _) z (M.U k ⊓ M.U k') (M.g k k') * gm (𝟙 _) z _ (σ x k')) (x y : I) :
    ∃ r : Γ(W.toScheme, W.ι ⁻¹ᵁ N x ⊓ W.ι ⁻¹ᵁ N y)ˣ, ∀ (z : W.toScheme) (k : M.ι), W.ι z ∈ N x → W.ι z ∈ N y →
      z ∈ M.U k → gm (𝟙 _) z _ r = gm (𝟙 _) z _ (σ y k) * (gm (𝟙 _) z _ (σ x k))⁻¹ := by
  let O : M.ι → W.toScheme.Opens := fun k => W.ι ⁻¹ᵁ N x ⊓ W.ι ⁻¹ᵁ N y ⊓ M.U k
  have l0 : ∀ k, O k ≤ W.ι ⁻¹ᵁ N x ⊓ W.ι ⁻¹ᵁ N y := fun k => inf_le_left
  have lx : ∀ k, O k ≤ W.ι ⁻¹ᵁ N x ⊓ M.U k := fun k z hz => ⟨hz.1.1, hz.2⟩
  have ly : ∀ k, O k ≤ W.ι ⁻¹ᵁ N y ⊓ M.U k := fun k z hz => ⟨hz.1.2, hz.2⟩
  have ev : ∀ k (z : W.toScheme) (hz : z ∈ O k),
      gm (𝟙 _) z (O k) (res (ly k) (σ y k) * (res (lx k) (σ x k))⁻¹) =
        gm (𝟙 _) z _ (σ y k) * (gm (𝟙 _) z _ (σ x k))⁻¹ := fun k z hz => by
    rw [map_mul, map_inv, gm_res _ z (ly k) hz, gm_res _ z (lx k) hz]
  obtain ⟨r, hr⟩ := glue_unit _ O l0 (fun z hz => by
      obtain ⟨k, hk⟩ := exists_chart hM z
      exact Opens.mem_iSup.2 ⟨k, show z ∈ O k from ⟨hz, hk⟩⟩) (fun k => res (ly k) (σ y k) * (res (lx k) (σ x k))⁻¹)
    (fun k k' z hz => by
      have h1 : z ∈ O k := hz.1
      have h2 : z ∈ O k' := hz.2
      have hx : W.ι z ∈ N x := h1.1.1
      have hy : W.ι z ∈ N y := h1.1.2
      have hk : z ∈ M.U k := h1.2
      have hk' : z ∈ M.U k' := h2.2
      rw [ev k z h1, ev k' z h2, hσ x z k k' hx hk hk', hσ y z k k' hy hk hk', mul_ringHom_units_ratio])
  refine ⟨r, fun z k hx hy hk => ?_⟩
  have hz : z ∈ O k := ⟨⟨hx, hy⟩, hk⟩
  rw [← gm_res _ z (l0 k) hz, hr k, ev k z hz]

theorem exists_ext (W : X.Opens) (hW : ∀ V : X.Opens, Function.Bijective (resG X (inf_le_left : V ⊓ W ≤ V)))
    (P Q : X.Opens) (r : Γ(W.toScheme, W.ι ⁻¹ᵁ P ⊓ W.ι ⁻¹ᵁ Q)ˣ) :
    ∃ g : Γ(X, P ⊓ Q)ˣ, ∀ z : W.toScheme, W.ι z ∈ P → W.ι z ∈ Q → gm W.ι z (P ⊓ Q) g = gm (𝟙 _) z _ r := by
  have hle : P ⊓ Q ⊓ W ≤ W.ι ''ᵁ (W.ι ⁻¹ᵁ P ⊓ W.ι ⁻¹ᵁ Q) := fun p hp => by
    have hpW : p ∈ W := hp.2
    have hpP : p ∈ P := hp.1.1
    have hpQ : p ∈ Q := hp.1.2
    have hm : (⟨p, hpW⟩ : W.toScheme) ∈ W.ι ⁻¹ᵁ P ⊓ W.ι ⁻¹ᵁ Q := ⟨hpP, hpQ⟩
    exact W.ι.apply_mem_image_iff.2 hm
  obtain ⟨g, hg⟩ := exists_res_eq (inf_le_left : P ⊓ Q ⊓ W ≤ P ⊓ Q) (hW _) (res hle (imU W.ι _ r))
  refine ⟨g, fun z hP hQ => ?_⟩
  have hz : W.ι z ∈ P ⊓ Q ⊓ W := ⟨⟨hP, hQ⟩, z.2⟩
  rw [← gm_res W.ι z inf_le_left hz, hg, gm_res W.ι z hle hz]
  have := gm_imU W.ι (𝟙 _) z _ (show z ∈ W.ι ⁻¹ᵁ P ⊓ W.ι ⁻¹ᵁ Q from ⟨hP, hQ⟩) r
  rwa [Category.id_comp] at this

end GlobalTheory.ExtendClass

namespace GlobalTheory.ExtendClass
open GlobalTheory.GlueLineBundle TopologicalSpace

theorem commGroup_cocycle_mul_inv_mul_mul_inv {G : Type} [CommGroup G] (a b c : G) : b * a⁻¹ * (c * b⁻¹) = c * a⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem commGroup_inv_eq_conj_twist_identity {G : Type} [CommGroup G] (a b g : G) : a⁻¹ = g * b * a⁻¹ * g⁻¹ * b⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.ExtendClass

open GlobalTheory.GlueLineBundle TopologicalSpace GlobalTheory.ExtendClass in

theorem GlobalTheory.extend_class_of_locally_trivial : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → ∀ W : X.Opens, (∀ z : X, ringKrullDim ((X).presheaf.stalk z) ≤ 1 → z ∈ W) → ∀ c : Pic W.toScheme, (∀ x : X, ∃ N : X.Opens, x ∈ N ∧ GlobalTheory.CechPic.pull (X.homOfLE (inf_le_right : N ⊓ W ≤ W)) c = 0) → ∃ c' : Pic X, GlobalTheory.CechPic.pull W.ι c' = c := by
  intro X _ hX W hW c hc
  obtain ⟨M, hM, rfl⟩ := cls_surj c
  have hbij : ∀ V : X.Opens, Function.Bijective (resG X (inf_le_left : V ⊓ W ≤ V)) :=
    ((extension_over_codim_two X hX).1 W hW).1
  choose N hN ht using hc
  have ht' : ∀ x, ∃ t : LB.Gen (M.pull (X.homOfLE (inf_le_right : N x ⊓ W ≤ W))), t.IsGen := fun x =>
    (cls_eq_zero_iff (pull_isLB hM _)).1 (ht x)
  choose t htg using ht'
  choose σ hσ using fun x => exists_sigma W (N x) (t x) (htg x)
  choose r hr using exists_ratio W hM N σ hσ
  choose g hg using fun x y => exists_ext W hbij (N x) (N y) (r x y)
  let L : LB X := ⟨↥X, N, g⟩
  have hgr : ∀ x y (z : W.toScheme) k, W.ι z ∈ N x → W.ι z ∈ N y → z ∈ M.U k →
      gm W.ι z (N x ⊓ N y) (g x y) = gm (𝟙 _) z _ (σ y k) * (gm (𝟙 _) z _ (σ x k))⁻¹ :=
    fun x y z k hx hy hk => (hg x y z hx hy).trans (hr x y z k hx hy hk)
  have hL : L.IsLB :=
    { cover := top_le_iff.1 fun x _ => Opens.mem_iSup.2 ⟨x, hN x⟩
      g_self := fun x => eq_of_gm_ι W hbij fun z hz => by
        obtain ⟨k, hk⟩ := exists_chart hM z
        dsimp only [L]
        rw [gm_res W.ι z _ hz, map_one]
        exact (hgr x x z k hz hz hk).trans (mul_inv_cancel _)
      cocycle := fun x y w => eq_of_gm_ι W hbij fun z hz => by
        obtain ⟨k, hk⟩ := exists_chart hM z
        have hx : W.ι z ∈ N x := hz.1.1
        have hy : W.ι z ∈ N y := hz.1.2
        have hw : W.ι z ∈ N w := hz.2
        have h1 : W.ι z ∈ N x ⊓ N y := ⟨hx, hy⟩
        have h2 : W.ι z ∈ N y ⊓ N w := ⟨hy, hw⟩
        have h3 : W.ι z ∈ N x ⊓ N w := ⟨hx, hw⟩
        dsimp only [L] at hz ⊢
        rw [map_mul, gm_res W.ι z _ hz, gm_res W.ι z _ hz, gm_res W.ι z _ hz]
        rw [hgr x y z k hx hy hk, hgr y w z k hy hw hk, hgr x w z k hx hw hk, commGroup_cocycle_mul_inv_mul_mul_inv] }
  have hle : ∀ p : (PUnit → L.ι) × M.ι, (L.pull W.ι).U p.1 ⊓ M.U p.2 ≤ W.ι ⁻¹ᵁ N (p.1 PUnit.unit) ⊓ M.U p.2 :=
    fun p z hz => ⟨mem_pull.1 hz.1, hz.2⟩
  let w : LB.Iso M (L.pull W.ι) := ⟨fun p => res (hle p) (σ (p.1 PUnit.unit) p.2)⁻¹⟩
  have ew : ∀ (p : (PUnit → L.ι) × M.ι) (z : W.toScheme) (hz : z ∈ (L.pull W.ι).U p.1 ⊓ M.U p.2),
      gm (𝟙 _) z _ (w.s p) = (gm (𝟙 _) z _ (σ (p.1 PUnit.unit) p.2))⁻¹ := fun p z hz =>
    (gm_res _ z (hle p) hz _).trans (map_inv _ _)
  have hw : w.IsGen := by
    rintro ⟨J, k⟩ ⟨J', k'⟩
    apply unit_ext
    intro z hz
    have hj : W.ι z ∈ L.U (J PUnit.unit) := mem_pull.1 hz.1.1
    have hj' : W.ι z ∈ L.U (J' PUnit.unit) := mem_pull.1 hz.2.1
    have hk : z ∈ M.U k := hz.1.2
    have hk' : z ∈ M.U k' := hz.2.2
    have e := gm_div_g (L := L) (L' := M) (F := W.ι) (𝟙 _) z (J PUnit.unit) (J' PUnit.unit) k k' hj hj' hk hk'
    rw [Category.id_comp] at e
    have e' : gm (𝟙 _) z _ ((LB.div (L.pull W.ι) M).g (J, k) (J', k')) = _ := e
    refine (gm_res _ z inf_le_left hz _).trans ?_
    rw [map_mul, gm_res _ z inf_le_right hz, e', ew _ z hz.1, ew _ z hz.2]
    show _ = gm W.ι z (N (J PUnit.unit) ⊓ N (J' PUnit.unit)) (g (J PUnit.unit) (J' PUnit.unit)) * _ * _
    rw [hgr _ _ z k hj hj' hk, hσ (J' PUnit.unit) z k k' hj' hk hk']
    exact commGroup_inv_eq_conj_twist_identity _ _ _
  refine ⟨cls L hL, ?_⟩
  rw [← cls_pull hL W.ι (pull_isLB hL _)]
  exact (cls_eq_iff _ _).2 (LBIso.symm ⟨w, hw⟩)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartRatioOnOverlapStatement
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
open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_ratio_on_overlap : ∀ (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) (Xw : X.Opens) (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]), (∀ yb, IsTest p Xw yb → (K yb).Nonempty) → ∀ (R1 R2 A : Type) [CommRing R1] [CommRing R2] [CommRing A] (ξ1 : Sp R1 ⟶ X) (ξ2 : Sp R2 ⟶ X) (w : Sp A ⟶ X) (c1 : (Localization.Away (p : R1))ˣ) (c2 : (Localization.Away (p : R2))ˣ) (a1 : R1 →+* A) (a2 : R2 →+* A), spMap a1 ≫ ξ1 = w → spMap a2 ≫ ξ2 = w → (∀ φ : R1 →+* 𝓞_ℂ_[p], IsTest p Xw (spMap φ ≫ ξ1) → ∀ ψ : Localization.Away (p : R1) →+* ℂ_[p], ψ.comp (algebraMap R1 _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ → ∀ κ ∈ K (spMap φ ≫ ξ1), ‖ψ (c1 : Localization.Away (p : R1)) - κ‖ < ‖κ‖) → (∀ φ : R2 →+* 𝓞_ℂ_[p], IsTest p Xw (spMap φ ≫ ξ2) → ∀ ψ : Localization.Away (p : R2) →+* ℂ_[p], ψ.comp (algebraMap R2 _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ → ∀ κ ∈ K (spMap φ ≫ ξ2), ‖ψ (c2 : Localization.Away (p : R2)) - κ‖ < ‖κ‖) → ∀ (χ1 : Localization.Away (p : R1) →+* Localization.Away (p : A)) (χ2 : Localization.Away (p : R2) →+* Localization.Away (p : A)), χ1.comp (algebraMap R1 _) = (algebraMap A _).comp a1 → χ2.comp (algebraMap R2 _) = (algebraMap A _).comp a2 → ∀ φ : A →+* 𝓞_ℂ_[p], IsTest p Xw (spMap φ ≫ w) → ∀ ψ : Localization.Away (p : A) →+* ℂ_[p], ψ.comp (algebraMap A _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ → ‖ψ (χ1 (c1 : Localization.Away (p : R1))) - ψ (χ2 (c2 : Localization.Away (p : R2)))‖ < ‖ψ (χ2 (c2 : Localization.Away (p : R2)))‖ := by
  first | exact @GlobalTheory.FlatModel.unit_ratio_close | exact GlobalTheory.FlatModel.unit_ratio_close | (intros; apply GlobalTheory.FlatModel.unit_ratio_close <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChowLemmaProjectiveModificationStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chow_lemma_projective_modification : ∀ (R : Type) [CommRing R] [IsNoetherianRing R], ∀ (W : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)), IsSeparated f → LocallyOfFiniteType f → QuasiCompact f → Nonempty W → ∃ (W' P : Scheme.{0}) (π : W' ⟶ W) (q : W' ⟶ P) (s : P ⟶ Spec (CommRingCat.of R)) (U : W.Opens), IsProper π ∧ (U : Set W).Nonempty ∧ IsIso (π ∣_ U) ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver s ∧ IsImmersion q ∧ q ≫ s = π ≫ f := by
  first | exact @GlobalTheory.FormalAlg.exists_isProper_isImmersion_isProjOver | exact GlobalTheory.FormalAlg.exists_isProper_isImmersion_isProjOver | (intros; apply GlobalTheory.FormalAlg.exists_isProper_isImmersion_isProjOver <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnPolynomialLocalDepthEqPlaceDepthStatement
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnPolynomial_localDepth_eq_placeDepth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e → ∀ (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (cx : Lt1 Dw → ℕ) (n : ℕ) (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V), IsCols c T io p cx B → ∀ k : ℕ, nuLocOf Ch (vV T.V (p : T.Fr)).toNat k (polyT B cx) = nuP p y cx := by
  first | exact @GlobalTheory.ColDepth.nuLocOf_eq_nuP | exact GlobalTheory.ColDepth.nuLocOf_eq_nuP | (intros; apply GlobalTheory.ColDepth.nuLocOf_eq_nuP <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallEstimateImpliesFrameAutomorphyStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.small_estimate_implies_frame_automorphy : GlobalTheory.ExpTie.SmallSt → GlobalTheory.FrameAut.AutSt := by
  first | exact @GlobalTheory.FrameAut.autSt_of_smallSt | exact GlobalTheory.FrameAut.autSt_of_smallSt | (intros; apply GlobalTheory.FrameAut.autSt_of_smallSt <;> assumption)
end

