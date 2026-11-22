import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2665
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2655
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2351
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2364
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2404
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2656
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2321
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2632
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerMatrixUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2657

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicardClassEqZeroAffineMilnorSquare
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.DualOpen

open TopologicalSpace

theorem exists_units_of_pull_eq_zero {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (f : Y ⟶ X)
    (h : CechPic.pull f (cls L hL) = 0) : ∃ b : ∀ i, Γ(Y, f ⁻¹ᵁ L.U i)ˣ,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i j : L.ι), f (r z) ∈ L.U i → f (r z) ∈ L.U j →
        gm r z _ (b i) = gm (r ≫ f) z _ (L.g i j) * gm r z _ (b j) := by
  rw [← cls_pull hL f (pull_isLB hL f)] at h
  obtain ⟨t, ht⟩ := (cls_eq_zero_iff _).1 h
  have le : ∀ i, f ⁻¹ᵁ L.U i ≤ (L.pull f).U (fun _ ↦ i) := fun i y hy ↦ mem_pull.2 hy
  refine ⟨fun i ↦ res (le i) (t.s fun _ ↦ i), fun Z r z i j hi hj ↦ ?_⟩
  have mi : r z ∈ (L.pull f).U (fun _ ↦ i) := mem_pull.2 hi
  have mj : r z ∈ (L.pull f).U (fun _ ↦ j) := mem_pull.2 hj
  have hm : r z ∈ (L.pull f).U (fun _ ↦ i) ⊓ (L.pull f).U (fun _ ↦ j) := ⟨mi, mj⟩
  have e := congrArg (gm r z _) (ht (fun _ ↦ i) (fun _ ↦ j))
  rw [map_mul, gm_res r z _ hm, gm_res r z _ hm, gm_pull_g L f r z _ _ mi mj] at e
  rw [gm_res r z (le i) hi, gm_res r z (le j) hj]
  exact e

theorem eq_zero_of_square {X X₁ X₂ X₀ : Scheme.{0}} (f₁ : X₁ ⟶ X) (f₂ : X₂ ⟶ X) (g₁ : X₀ ⟶ X₁) (g₂ : X₀ ⟶ X₂)
    (w : g₁ ≫ f₁ = g₂ ≫ f₂)
    (inj : ∀ (W : X.Opens) (a b : Γ(X, W)), f₁.app W a = f₁.app W b → f₂.app W a = f₂.app W b → a = b)
    (ex : ∀ (W : X.Opens) (h₂ : g₁ ⁻¹ᵁ (f₁ ⁻¹ᵁ W) ≤ g₂ ⁻¹ᵁ (f₂ ⁻¹ᵁ W)) (a₁ : Γ(X₁, f₁ ⁻¹ᵁ W))
      (a₂ : Γ(X₂, f₂ ⁻¹ᵁ W)), g₁.appLE _ _ le_rfl a₁ = g₂.appLE _ _ h₂ a₂ →
        ∃ a : Γ(X, W), f₁.app W a = a₁ ∧ f₂.app W a = a₂)
    (lift : Function.Surjective (Units.map g₂.appTop.hom.toMonoidHom))
    (c : Pic X) (h₁ : CechPic.pull f₁ c = 0) (h₂ : CechPic.pull f₂ c = 0) : c = 0 := by
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  obtain ⟨b₁, hb₁⟩ := exists_units_of_pull_eq_zero hL f₁ h₁
  obtain ⟨b₂, hb₂⟩ := exists_units_of_pull_eq_zero hL f₂ h₂
  have le : ∀ W : X.Opens, g₁ ⁻¹ᵁ (f₁ ⁻¹ᵁ W) ≤ g₂ ⁻¹ᵁ (f₂ ⁻¹ᵁ W) := fun W ↦ by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, w]
  have injU : ∀ (W : X.Opens) (a b : Γ(X, W)ˣ), pullU f₁ W a = pullU f₁ W b → pullU f₂ W a = pullU f₂ W b → a = b :=
    fun W a b e₁ e₂ ↦ Units.ext (inj W _ _ (congrArg Units.val e₁) (congrArg Units.val e₂))
  have exU : ∀ (W : X.Opens) (a₁ : Γ(X₁, f₁ ⁻¹ᵁ W)ˣ) (a₂ : Γ(X₂, f₂ ⁻¹ᵁ W)ˣ),
      res le_rfl (pullU g₁ _ a₁) = res (le W) (pullU g₂ _ a₂) →
        ∃ a : Γ(X, W)ˣ, pullU f₁ W a = a₁ ∧ pullU f₂ W a = a₂ := fun W a₁ a₂ e ↦ by
    have e' : res le_rfl (pullU g₁ _ a₁⁻¹) = res (le W) (pullU g₂ _ a₂⁻¹) := by
      rw [map_inv, map_inv, map_inv, map_inv, e]
    obtain ⟨a, p₁, p₂⟩ := ex W (le W) a₁.val a₂.val (congrArg Units.val e)
    obtain ⟨a', q₁, q₂⟩ := ex W (le W) (a₁⁻¹).val (a₂⁻¹).val (congrArg Units.val e')
    have k : a * a' = 1 := inj W _ _ (by rw [map_mul, map_one, p₁, q₁, Units.mul_inv])
      (by rw [map_mul, map_one, p₂, q₂, Units.mul_inv])
    exact ⟨⟨a, a', k, (mul_comm _ _).trans k⟩, Units.ext p₁, Units.ext p₂⟩
  have key : ∀ {G : Type} [CommGroup G] (a x y : G), a * x * (a * y)⁻¹ = x * y⁻¹ := fun a x y ↦ by
    rw [← div_eq_mul_inv, ← div_eq_mul_inv, mul_div_mul_left_eq_div]
  let V : L.ι → X₀.Opens := fun i ↦ g₁ ⁻¹ᵁ (f₁ ⁻¹ᵁ L.U i)
  let q : ∀ i, Γ(X₀, V i)ˣ := fun i ↦ pullU g₁ _ (b₁ i) * (res (le _) (pullU g₂ _ (b₂ i)))⁻¹
  have gq : ∀ i x, x ∈ V i → gm (𝟙 X₀) x (V i) (q i) = gm g₁ x _ (b₁ i) * (gm g₂ x _ (b₂ i))⁻¹ := fun i x hx ↦ by
    have e₁ := gm_pull (𝟙 X₀) g₁ x _ hx (b₁ i)
    have e₂ := (gm_res (𝟙 X₀) x (le (L.U i)) hx _).trans (gm_pull (𝟙 X₀) g₂ x _ (le _ hx) (b₂ i))
    rw [Category.id_comp] at e₁ e₂
    exact (map_mul _ _ _).trans (congrArg₂ (· * ·) e₁ ((map_inv _ _).trans (congrArg (·⁻¹) e₂)))
  obtain ⟨F, hF⟩ := glue_unit ⊤ V (fun _ ↦ le_top) (fun x _ ↦ by
      obtain ⟨i, hi⟩ := exists_chart hL (f₁ (g₁ x))
      exact Opens.mem_iSup.2 ⟨i, hi⟩) q (fun i j x hx ↦ by
      rw [gq i x hx.1, gq j x hx.2, hb₁ _ g₁ x i j hx.1 hx.2, hb₂ _ g₂ x i j (le _ hx.1) (le _ hx.2), w, key])
  obtain ⟨u, hu⟩ := lift F
  have hu' : pullU g₂ ⊤ u = F := hu
  have loc : ∀ i, ∃ s : Γ(X, L.U i)ˣ, pullU f₁ _ s = b₁ i ∧ pullU f₂ _ s = b₂ i * res le_top u := fun i ↦
    exU _ _ _ (unit_ext fun x hx ↦ by
      have e := congrArg (gm (𝟙 X₀) x (V i)) (hF i)
      rw [gm_res (𝟙 X₀) x _ hx, gq i x hx, ← hu'] at e
      have e₀ := gm_pull (𝟙 X₀) g₂ x ⊤ trivial u
      have e₁ := gm_pull (𝟙 X₀) g₁ x _ hx (b₁ i)
      have e₂ := gm_pull (𝟙 X₀) g₂ x _ (le _ hx) (b₂ i * res le_top u)
      rw [Category.id_comp] at e₀ e₁ e₂
      rw [gm_res (𝟙 X₀) x _ hx, gm_res (𝟙 X₀) x _ hx, e₁, e₂, map_mul, gm_res g₂ x _ (le _ hx), ← e₀]
      exact (mul_inv_eq_iff_eq_mul.1 e.symm).trans (mul_comm _ _))
  choose s hs₁ hs₂ using loc
  have gp : ∀ {Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (W : X.Opens) (a : Γ(X, W)ˣ), f y ∈ W →
      gm (𝟙 Y) y (f ⁻¹ᵁ W) (pullU f W a) = gm f y W a := fun f y W a hy ↦
    (gm_pull (𝟙 _) f y W hy a).trans (by rw [Category.id_comp])
  refine (cls_eq_zero_iff hL).2 ⟨⟨s⟩, fun i j ↦ injU _ _ _ (unit_ext fun y hy ↦ ?_) (unit_ext fun y hy ↦ ?_)⟩
  · have e := hb₁ _ (𝟙 _) y i j hy.1 hy.2
    rw [Category.id_comp, ← hs₁, ← hs₁, gp f₁ y _ _ hy.1, gp f₁ y _ _ hy.2] at e
    rw [gp f₁ y _ _ hy, gp f₁ y _ _ hy, map_mul, gm_res f₁ y _ hy, gm_res f₁ y _ hy]
    exact e
  · have e := hb₂ _ (𝟙 _) y i j hy.1 hy.2
    rw [Category.id_comp] at e
    have k : ∀ i, f₂ y ∈ L.U i → gm f₂ y _ (s i) = gm (𝟙 _) y _ (b₂ i) * gm (𝟙 _) y ⊤ u := fun i hi ↦ by
      rw [← gp f₂ y _ _ hi, hs₂, map_mul, gm_res (𝟙 _) y _ hi]
    rw [gp f₂ y _ _ hy, gp f₂ y _ _ hy, map_mul, gm_res f₂ y _ hy, gm_res f₂ y _ hy]
    exact (k i hy.1).trans (by rw [e, k j hy.2, _root_.mul_assoc])

theorem pic_eq_zero_of_milnor : ∀ (S : Scheme.{0}) (A T T₁ T₂ T₀ : Over S) [Flat A.hom] (j₁ : T₁ ⟶ T) (j₂ : T₂ ⟶ T)
    (k₁ : T₀ ⟶ T₁) (k₂ : T₀ ⟶ T₂), Milnor j₁.left j₂.left k₁.left k₂.left →
    Function.Surjective (Units.map (A ◁ k₂).left.appTop.hom.toMonoidHom) →
    ∀ c : Pic (A ⊗ T).left, GlobalTheory.CechPic.pull (A ◁ j₁).left c = 0 → GlobalTheory.CechPic.pull (A ◁ j₂).left c = 0 → c = 0 := by
  intro S A T T₁ T₂ T₀ _ j₁ j₂ k₁ k₂ h hs
  have H := GlobalTheory.T.sections_flat_baseChange_affineMilnorSquare_open S A T T₁ T₂ T₀ j₁ j₂ k₁ k₂ h
  have w : k₁ ≫ j₁ = k₂ ≫ j₂ := Over.OverMorphism.ext h.w
  refine eq_zero_of_square _ _ (A ◁ k₁).left (A ◁ k₂).left ?_ (fun W ↦ (H W).1)
    (fun W h₂ ↦ (H W).2 _ le_rfl h₂ le_rfl) hs
  rw [← Over.comp_left, ← Over.comp_left, ← MonoidalCategory.whiskerLeft_comp, ← MonoidalCategory.whiskerLeft_comp, w]

end GlobalTheory.DualOpen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PinchingSquareGlueLineBundleOfLocalGeneratorsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pinchingSquare_glue_lineBundle_of_local_generators : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), IsPullback i' p' p i → GlobalTheory.PinchLift.Glues p i i' p' → ∀ (L' : LB X') (LZ : LB Z) (hL' : L'.IsLB) (hLZ : LZ.IsLB) (w : LB.Iso (L'.pull i') (LZ.pull p')), w.IsGen → (∀ x : X, ∃ (W : X.Opens) (s' : ∀ k, Γ(X', L'.U k ⊓ p ⁻¹ᵁ W)ˣ) (sZ : ∀ j, Γ(Z, LZ.U j ⊓ i ⁻¹ᵁ W)ˣ), x ∈ W ∧ GlobalTheory.PinchLift.GenOn L' (p ⁻¹ᵁ W) s' ∧ GlobalTheory.PinchLift.GenOn LZ (i ⁻¹ᵁ W) sZ ∧ GlobalTheory.PinchLift.Matched i' p' L' LZ w (p ⁻¹ᵁ W) (i ⁻¹ᵁ W) s' sZ) → ∃ e : Pic X, GlobalTheory.CechPic.pull p e = cls L' hL' ∧ GlobalTheory.CechPic.pull i e = cls LZ hLZ := by
  first | exact @GlobalTheory.PinchLift.assemble | exact GlobalTheory.PinchLift.assemble | (intros; apply GlobalTheory.PinchLift.assemble <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PinchingSquareUnitsPatchStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pinchingSquare_unitsPatch : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), IsPullback i' p' p i → IsAffineHom p → IsClosedImmersion i → GlobalTheory.Pinch.Cond p i → GlobalTheory.Pinch.UnitsPatch p i i' p' := by
  first | exact @GlobalTheory.Pinch.unitsPatch | exact GlobalTheory.Pinch.unitsPatch | (intros; apply GlobalTheory.Pinch.unitsPatch <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceRingFractionEmbeddingStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.place_ring_fraction_embedding : ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l])
    (R : Subring ℂ) [IsDiscreteValuationRing R], GlobalTheory.LatModel.IsPlaceRing E l lam R →
    ∃ j : FractionRing R →+* ℂ, (∀ x : R, j (algebraMap R (FractionRing R) x) = x) ∧ CharZero R ∧
      (l : R) ∈ IsLocalRing.maximalIdeal R ∧ Nat.card (E →+* FractionRing R) = Module.finrank ℚ E ∧
      (∀ σ : E →+* ℂ, ∃ τ : E →+* FractionRing R, j.comp τ = σ) ∧
      ∀ (x : FractionRing R) (r : ℚ), ((-r : ℚ) : WithTop ℚ) ≤ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l x → Sz l lam (r : ℝ) (j x) := by
  first | exact @GlobalTheory.PlaceRingFacts.place_ring_facts | exact GlobalTheory.PlaceRingFacts.place_ring_facts | (intros; apply GlobalTheory.PlaceRingFacts.place_ring_facts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareBundleIsomorphismCompatStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poincare_bundle_isomorphism_compat : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (S : Scheme.{0}) (A : Over S) [GrpObj A]
    (rm : OAct (𝓞 F) A) (P : 𝔠.elt → LB (A ⊗ A).left), (∀ c, (P c).IsLB) →
    (∀ c, LBIso (P c) ((P c).pull (lift (snd A A) (fst A A)).left)) →
    (∀ (a : 𝓞 F) c, LBIso (P (a • c)) ((P c).pull (lift (fst A A) (snd A A ≫ rm.act a)).left)) →
    ∀ (c d : 𝔠.elt) (a b : 𝓞 F), a • d = b • c → ∀ (T : Over S) (y : T ⟶ A),
      HasGen ((P c).pull (lift (fst A T) (snd A T ≫ y)).left) →
      HasGen ((P d).pull (lift (fst A T) (snd A T ≫ (y ≫ rm.act a))).left) := by
  first | exact @GlobalTheory.KerShift.ker_shift | exact GlobalTheory.KerShift.ker_shift | (intros; apply GlobalTheory.KerShift.ker_shift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointCochainPullbackBaseChangeCocycleCoboundaryWStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointCochainPullbackBaseChange_cocycle_coboundary_whole : ∀ (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R') (X : Over (Sp R)) (X' : Over (Sp R')) (q : X'.left ⟶ X.left) (w : q ≫ X.hom = X'.hom ≫ spMap σ) (u : Fn1 X), (IsCoc (whole X) u → IsCoc (whole X') (bcPull w u)) ∧ ((∃ k, IsCob (whole X) u k) → ∃ k, IsCob (whole X') (bcPull w u) k) := by
  first | exact @GlobalTheory.PtExt.bcPull_keeps | exact GlobalTheory.PtExt.bcPull_keeps | (intros; apply GlobalTheory.PtExt.bcPull_keeps <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointDisjointUnionRepresentingFamilyUniqueStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.point_disjointUnion_representingFamily_unique : ∀ {S : Scheme.{0}} (A : Over S) [GrpObj A] {κ : Type} [Finite κ] (X : Over S) (V : κ → X.left.Opens), (⨆ i, V i = ⊤) → (Pairwise fun i i' => Disjoint (V i) (V i')) → ∀ (Bt : Over S) (B : κ → Over S) (j : ∀ i, B i ⟶ Bt) [∀ i, IsOpenImmersion (j i).left], (⨆ i, (j i).left.opensRange = ⊤) → (Pairwise fun i i' => Disjoint (j i).left.opensRange (j i').left.opensRange) → ∀ (b : ∀ i, B i ⟶ Over.mk ((V i).ι ≫ X.hom)) (bt : Bt ⟶ X), (∀ i, j i ≫ bt = b i ≫ Over.homMk (V i).ι) → ∀ (P : ∀ i, LB (A ⊗ B i).left) (Pt : LB (A ⊗ Bt).left), (∀ i, Rep A (b i) (P i)) → Pt.IsLB → (∀ i, LBIso (Pt.pull (A ◁ j i).left) (P i)) → ∀ (T : Over S) (x y : T ⟶ Bt), x ≫ bt = y ≫ bt → Same A Pt Pt x y → x = y := by
  first | exact @GlobalTheory.DualCon.ProdGlue.eq_of_same_of_disjoint_cover | exact GlobalTheory.DualCon.ProdGlue.eq_of_same_of_disjoint_cover | (intros; apply GlobalTheory.DualCon.ProdGlue.eq_of_same_of_disjoint_cover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointwiseCocycleLocalSectionsGlueBasicOpenCoverStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointwiseCocycle_local_sections_glue_basicOpen_cover : ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (K : Type) (W : K → X.left.Opens) (u : Fn1 X), IsCoc W u → ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt X D) (n : ℕ) (s : Fin n → D), Ideal.span (Set.range s) = ⊤ → ∀ τ : Fin n → ∀ (E : Type) [CommRing E] [Algebra R E], (D →ₐ[R] E) → E, (∀ (a : Fin n) (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (ψ : D →ₐ[R] E) (θ : E →ₐ[R] E'), IsUnit (ψ (s a)) → τ a E' (θ.comp ψ) - θ (τ a E ψ) = u E E' θ (spOver ψ ≫ x)) → (∀ (a b : Fin n) (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E), IsUnit (ψ (s a)) → IsUnit (ψ (s b)) → τ a E ψ = τ b E ψ) → ∃ σ : ∀ (E : Type) [CommRing E] [Algebra R E], (D →ₐ[R] E) → E, ∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (ψ : D →ₐ[R] E) (θ : E →ₐ[R] E'), Sm W (spOver ψ ≫ x) → σ E' (θ.comp ψ) - θ (σ E ψ) = u E E' θ (spOver ψ ≫ x) := by
  first | exact @GlobalTheory.PtExt.glue_sections | exact GlobalTheory.PtExt.glue_sections | (intros; apply GlobalTheory.PtExt.glue_sections <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationFormExistsForCmObjectStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarization_form_exists_for_cm_object : GlobalTheory.Published.AbelianDeRham → ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (R : Type) [CommRing R]
    (X : Obj F 𝔠 (Sp R)) (c : 𝔠.elt), ∃ ψ : LinearMap.BilinForm R (HdR X.A),
      GlobalTheory.AbDual.IsCorrForm (dp0 R) (𝟙 _) X.A X.A (X.P c) ψ ∧ IsPolForm (dp0 R) (𝟙 _) X.A (X.diag c) ((2 : R) • ψ) := by
  first | exact @GlobalTheory.PolPairing.exists_isCorrForm_diag | exact GlobalTheory.PolPairing.exists_isCorrForm_diag | (intros; apply GlobalTheory.PolPairing.exists_isCorrForm_diag <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationFormOverDvrPrimeToL
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
open GlobalTheory.AbDual GlobalTheory.AbLaw GlobalTheory.CechPic

set_option autoImplicit false
noncomputable section
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolPrimeTo

theorem perfect_of_primeTo (HR : GlobalTheory.Published.AbelianDeRham) (HD : GlobalTheory.Published.AbelianDualCrystal)
    (F : Type) [Field F] [NumberField F] (𝔠 : FracId F)
    (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (hunit : ∀ n : ℕ, n.Coprime l → IsUnit (n : R)) (X : Obj F 𝔠 (Sp R)) (c₀ : 𝔠.elt) (hc₀ : (c₀ : F) ≠ 0)
    (hgen : ∀ c : 𝔠.elt, ∃ (n : ℕ) (t : 𝓞 F), n.Coprime l ∧ n • c = t • c₀)
    (ψ : LinearMap.BilinForm R (HdR X.A)) (hψ : GlobalTheory.AbDual.IsCorrForm (dp0 R) (𝟙 _) X.A X.A (X.P c₀) ψ) :
    Function.Bijective ψ := by
  obtain ⟨m, hm0, hml, hm⟩ := exists_uniform 𝔠 l c₀ hgen

  obtain ⟨B, _, Q, hB, hBg, hd, hd'⟩ := HD.1 (Sp R) X.A X.ab
  have hBg := hBg _ X.dim
  haveI : IsCommMonObj B := hB.comm

  obtain ⟨c₁, hc₁⟩ := exists_totPos 𝔠 c₀ hc₀
  have hL := pull_isLB (X.isLB c₁) (lift (𝟙 X.A) (𝟙 X.A)).left
  obtain ⟨H, hH, hamp⟩ := GlobalTheory.BirigidLift.exists_relAmple_prod X.ab X.ab hL (X.pos c₁ hc₁) hL (X.pos c₁ hc₁)
  obtain ⟨a₁, a₂⟩ := GlobalTheory.BirigidLift.additive_of_triv X.ab X.ab hH hamp (X.isLB c₀) (X.rig₁ c₀) (X.rig₂ c₀)
  obtain ⟨lam, hlam, hcls⟩ := GlobalTheory.BirigidLift.exists_hom hd hd'.additive (X.isLB c₀) a₁ a₂

  have hker : ∀ (T : Over (Sp R)) (x : T ⟶ X.A), x ≫ lam = 1 → x ^ m = 1 := by
    intro T x hx
    have tr : Triv (ev (X.P c₀) (fst X.A T) (snd X.A T ≫ x)) := by
      rw [triv_ev_iff (X.isLB c₀), GlobalTheory.BirigidLift.evc_of_cls hd.isLB (X.isLB c₀) hcls, Category.assoc, hx,
        comp_one]
      exact evc_one_right hd.isLB hd.zero _
    have k := X.ker c₀ T x tr (m : 𝓞 F) hm
    rw [act_natCast, comp_pow, Category.comp_id] at k
    exact k
  obtain ⟨μ', hμ', e₁, e₂⟩ := GlobalTheory.IsogenyQuasiInverse.exists_quasiInverse R X.A B _ X.ab hB X.dim hBg lam hlam m hm0 hker
  have hpush := bijective_push (dp0 R) (𝟙 _) lam μ' m (hunit m hml) e₁ e₂

  obtain ⟨⟨φ, hφ, -⟩, hperf⟩ := GlobalTheory.Published.AbelianDualCrystal.duality HR X.ab X.dim hB hBg (hd.isPerfect hd')
  have C := cupSquare_of_free HR.1 (AbelianSchemeGerms.isAbelianScheme_tensor X.A X.A X.ab X.ab) (smooth_prod X.dim X.dim)
  have e : LBIso (ev Q (fst X.A X.A) (snd X.A X.A ≫ lam)) (ev (X.P c₀) (fst X.A X.A ≫ 𝟙 X.A) (snd X.A X.A)) := by
    refine (cls_eq_iff (pull_isLB hd.isLB _) (pull_isLB (X.isLB c₀) _)).1 ?_
    rw [cls_ev hd.isLB, cls_ev (X.isLB c₀), GlobalTheory.BirigidLift.evc_of_cls hd.isLB (X.isLB c₀) hcls, Category.comp_id]
  have hadj : ∀ x y, φ x (push (dp0 R) (𝟙 _) lam y) = ψ x y := fun x y ↦ by
    have k := IsCorrForm.adjoint C hd.isLB (X.isLB c₀) hφ hψ (𝟙 X.A) lam e x y
    rwa [push_id] at k
  haveI := (hperf φ hφ).1
  have hφb : Function.Bijective φ := LinearMap.IsPerfPair.bijective_left φ
  let E := LinearEquiv.ofBijective _ hpush
  have : ⇑ψ = ⇑E.dualMap ∘ ⇑φ := by
    funext x
    refine LinearMap.ext fun y ↦ ?_
    rw [Function.comp_apply, LinearEquiv.dualMap_apply, ← hadj]
    rfl
  rw [this]
  exact E.dualMap.bijective.comp hφb

end GlobalTheory.PolPrimeTo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationFormRingActionSymmetric
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbDual

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RealMultAdjoint

theorem polForm_adjoint_rm : GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}
    {R : Type} [CommRing R] (X : Obj F 𝔠 (Sp R)) (c : 𝔠.elt) (ψ : LinearMap.BilinForm R (HdR X.A)),
    IsPolForm (dp0 R) (𝟙 _) X.A (X.diag c) ψ → ∀ (b : 𝓞 F) (x y : HdR X.A),
      ψ (act (dp0 R) (𝟙 _) X.rm b x) y = ψ x (act (dp0 R) (𝟙 _) X.rm b y) := by
  intro HR HD F _ _ 𝔠 R _ X c ψ hψ b x y
  have hAB := AbelianSchemeGerms.isAbelianScheme_tensor X.A X.A X.ab X.ab
  have gAB := smooth_prod X.dim X.dim
  have C := cupSquare_of_free HR.1 hAB gAB
  have := X.rm.hom
  obtain ⟨φ, hφ, h2φ⟩ := GlobalTheory.PolPairing.exists_isCorrForm_diag HR F 𝔠 R X c
  obtain ⟨φ', hφ', h2φ'⟩ := GlobalTheory.PolPairing.exists_isCorrForm_diag HR F 𝔠 R X (b • c)
  have eψ : ψ = (2 : R) • φ := IsPolForm.unique HR.1 X.ab X.dim (pull_isLB (X.isLB c) _) hψ h2φ
  obtain ⟨χ, hχ, k⟩ := hφ.pull (X.isLB c) (homMor (dp0 R) (𝟙 _) (𝟙 X.A))
    (homMor (dp0 R) (𝟙 _) (X.rm.act b)) (h := (lift (fst X.A X.A) (snd X.A X.A ≫ X.rm.act b)).left)
    (by simp only [← Over.comp_left, lift_fst, lift_snd, Category.comp_id])
    (by simp only [← Over.comp_left, lift_fst, lift_snd, Category.comp_id])
    (X.isLB (b • c)) (LBIso.symm (X.smul b c))
  obtain rfl := hχ.unique C (X.isLB (b • c)) hφ'
  have key : ∀ u v, χ u v = φ u (push (dp0 R) (𝟙 _) (X.rm.act b) v) := fun u v ↦ by
    have e := k (push (dp0 R) (𝟙 _) (𝟙 X.A) u) u (push (dp0 R) (𝟙 _) (X.rm.act b) v) v (fun _ ↦ rfl) fun _ ↦ rfl
    rwa [push_id, LinearMap.id_apply, RingHom.id_apply] at e
  change ψ (push (dp0 R) (𝟙 _) (X.rm.act b) x) y = ψ x (push (dp0 R) (𝟙 _) (X.rm.act b) y)
  have e₁ := (LinearMap.IsAlt.neg hψ.isAlt y (push (dp0 R) (𝟙 _) (X.rm.act b) x)).symm
  have e₂ := LinearMap.IsAlt.neg h2φ'.isAlt y x
  rw [e₁, eψ]
  simp only [LinearMap.smul_apply, ← key] at e₂ ⊢
  exact e₂

end GlobalTheory.RealMultAdjoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationFormsCommensurableStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarization_forms_commensurable : GlobalTheory.Published.AbelianDeRham → ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (R : Type) [CommRing R]
    (X : Obj F 𝔠 (Sp R)) (c c₀ : 𝔠.elt), (c₀ : F) ≠ 0 → ∀ ψ ψ₀ : LinearMap.BilinForm R (HdR X.A),
    IsPolForm (dp0 R) (𝟙 _) X.A (X.diag c) ψ → IsPolForm (dp0 R) (𝟙 _) X.A (X.diag c₀) ψ₀ →
    ∃ (n : ℕ) (t : 𝓞 F), n ≠ 0 ∧ ∀ x y, (n : R) * ψ x y = ψ₀ x (act (dp0 R) (𝟙 _) X.rm t y) := by
  first | exact @GlobalTheory.RealMult.PolScale.exists_nat_mul_polForm_eq | exact GlobalTheory.RealMult.PolScale.exists_nat_mul_polForm_eq | (intros; apply GlobalTheory.RealMult.PolScale.exists_nat_mul_polForm_eq <;> assumption)
end

