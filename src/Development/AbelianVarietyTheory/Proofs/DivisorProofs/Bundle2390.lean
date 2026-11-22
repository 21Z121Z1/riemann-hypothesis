import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2351
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2317
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2349
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2364
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsIsGenOfUniqueFactorizationMonoid
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUnitSmulEqOfBijectiveToSpanSingleton
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthRestrictScalarsEqSumInertiaDegOfSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2329
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2331
import Development.AbelianVarietyTheory.Definitions.Divisors.ToBidualNaturalityDualSheafTranspose
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0644

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleGeneratorOffClosedSubscheme
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.PinchLift

theorem exists_gen_away_of_closed : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), IsPullback i' p' p i → IsAffineHom p → IsClosedImmersion i → GlobalTheory.PinchLift.Glues p i i' p' → ∀ (L' : LB X'), L'.IsLB → ∀ x : X, (∀ z : Z, i z ≠ x) → ∃ (W : X.Opens) (s' : ∀ k, Γ(X', L'.U k ⊓ p ⁻¹ᵁ W)ˣ), x ∈ W ∧ i ⁻¹ᵁ W = ⊥ ∧ GlobalTheory.PinchLift.GenOn L' (p ⁻¹ᵁ W) s' := by
  intro X X' Z Z' p i i' p' _ hp hi hG L' hL x hx
  let U : X.Opens := ⟨(Set.range i)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hxU : x ∈ U := by rintro ⟨z, rfl⟩; exact hx z rfl
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset hxU
  have hiV : ∀ {O : X.Opens}, O ≤ V → i ⁻¹ᵁ O = ⊥ := fun {O} hO =>
    eq_bot_iff.2 fun z hz => (hVU (hO hz) ⟨z, rfl⟩).elim
  have hbot : i ⁻¹ᵁ V = ⊥ := hiV le_rfl
  have hsZ : Subsingleton Γ(Z, i ⁻¹ᵁ V) := by rw [hbot]; infer_instance
  have hbot' : i' ⁻¹ᵁ (p ⁻¹ᵁ V) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ V) = ⊥ :=
    eq_bot_iff.2 fun z hz => (hVU (show i (p' z) ∈ V from hz.2) ⟨p' z, rfl⟩).elim
  have hsZ' : Subsingleton Γ(Z', i' ⁻¹ᵁ (p ⁻¹ᵁ V) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ V)) := by rw [hbot']; infer_instance
  have hbij : Function.Bijective (p.app V).hom := by
    constructor
    · intro s t hst
      have h1 := hG V ((p.app V).hom s) ((i.app V).hom s) (Subsingleton.elim _ _)
      exact h1.unique ⟨rfl, rfl⟩ ⟨hst.symm, Subsingleton.elim _ _⟩
    · intro a
      obtain ⟨s, hs, -⟩ := hG V a 0 (Subsingleton.elim _ _)
      exact ⟨s, hs.1⟩
  haveI : IsIso (p.app V) := (ConcreteCategory.isIso_iff_bijective (p.app V)).2 hbij
  haveI : IsIso (p ∣_ V) := (isIso_morphismRestrict_iff_isIso_app p hV).2 inferInstance
  have hg : ∀ y, (p ∣_ V ≫ V.ι) y = p ((p ⁻¹ᵁ V).ι y) := fun y => by rw [morphismRestrict_ι]; rfl
  obtain ⟨y, hy⟩ : ∃ y, (p ∣_ V ≫ V.ι) y = x := by
    obtain ⟨v, hv⟩ := (p ∣_ V).surjective ⟨x, hxV⟩
    exact ⟨v, by show V.ι ((p ∣_ V) v) = x; rw [hv]; rfl⟩
  obtain ⟨k₀, hk₀⟩ := exists_chart hL ((p ⁻¹ᵁ V).ι y)
  let W : X.Opens := (p ∣_ V ≫ V.ι) ''ᵁ ((p ⁻¹ᵁ V).ι ⁻¹ᵁ L'.U k₀)
  have hmemW : ∀ z, z ∈ W ↔ ∃ w, (p ⁻¹ᵁ V).ι w ∈ L'.U k₀ ∧ (p ∣_ V ≫ V.ι) w = z := fun z => Iff.rfl
  have hxW : x ∈ W := (hmemW x).2 ⟨y, hk₀, hy⟩
  have hWV : W ≤ V := by
    intro z hz
    obtain ⟨w, -, rfl⟩ := (hmemW z).1 hz
    rw [hg]; exact w.2
  have hWk : p ⁻¹ᵁ W ≤ L'.U k₀ := by
    intro x'' hx''
    obtain ⟨w, hw, hwe⟩ := (hmemW _).1 hx''
    have hv : x'' ∈ p ⁻¹ᵁ V := hWV hx''
    have : (⟨x'', hv⟩ : (p ⁻¹ᵁ V).toScheme) = w :=
      (p ∣_ V ≫ V.ι).isOpenEmbedding.injective (by rw [hwe]; exact hg _)
    rw [← this] at hw; exact hw
  refine ⟨W, fun k => res (le_inf inf_le_left (inf_le_right.trans hWk)) (L'.g k k₀), hxW, hiV hWV, ?_⟩
  intro k l z hk hl hz
  have hz0 : z ∈ L'.U k₀ := hWk hz
  rw [gm_res (𝟙 X') z _ (show z ∈ L'.U k ⊓ p ⁻¹ᵁ W from ⟨hk, hz⟩),
    gm_res (𝟙 X') z _ (show z ∈ L'.U l ⊓ p ⁻¹ᵁ W from ⟨hl, hz⟩)]
  exact (gm_cocycle hL (𝟙 X') z hk hl hz0).symm

end GlobalTheory.PinchLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleOfDescentInvariantFrames
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LBDescent

set_option autoImplicit false

namespace GlobalTheory.LBDescent

private theorem ratio_eq {G : Type} [CommGroup G] (A B C D g : G) (h1 : A = g * B) (h2 : C = g * D) :
    C * A⁻¹ = D * B⁻¹ := by
  subst h1 h2; rw [mul_inv_rev, mul_comm g D, _root_.mul_assoc, mul_inv_cancel_comm_assoc]

private theorem ratio_mul {G : Type} [CommGroup G] (A B C : G) : (B * A⁻¹) * (C * B⁻¹) = C * A⁻¹ := by
  rw [mul_comm (B * A⁻¹), _root_.mul_assoc, inv_mul_cancel_left]

private theorem ratio_inv {G : Type} [CommGroup G] (A S g T : G) (h : S = g * T) :
    A⁻¹ = S * A⁻¹ * g⁻¹ * T⁻¹ := by
  rw [_root_.mul_assoc _ g⁻¹, ← mul_inv, ← h, mul_inv_cancel_comm]

theorem exists_lb_of_invariant_frames : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) [QuasiCompact f] [Flat f] [Surjective f] (L : LB X), L.IsLB →
    ∀ (φ : ∀ i j, Γ(pullback f f, chart f L i j)ˣ),
    (∀ y : Y, ∃ V : Y.Opens, y ∈ V ∧ ∃ s : ∀ i, Γ(X, f ⁻¹ᵁ V ⊓ L.U i)ˣ,
      (∀ (i j : L.ι) (x : X), f x ∈ V → x ∈ L.U i → x ∈ L.U j →
        gm (𝟙 X) x _ (s i) = gm (𝟙 X) x _ (L.g i j) * gm (𝟙 X) x _ (s j)) ∧
      ∀ (z : ↥(pullback f f)) (i j : L.ι), f (pullback.fst f f z) ∈ V → pullback.fst f f z ∈ L.U i →
        pullback.snd f f z ∈ L.U j →
        gm (pullback.fst f f) z _ (s i) * gm (𝟙 _) z _ (φ i j) = gm (pullback.snd f f) z _ (s j)) →
    ∃ L' : LB Y, L'.IsLB ∧ LBIso L (L'.pull f) := by
  intro X Y f _ _ _ L hL φ H
  choose V hV s hs1 hs2 using H
  have hW : ∀ a b i, f ⁻¹ᵁ (V a ⊓ V b) ⊓ L.U i ≤ f ⁻¹ᵁ (V a ⊓ V b) := fun a b i => inf_le_left
  have lb : ∀ a b i, f ⁻¹ᵁ (V a ⊓ V b) ⊓ L.U i ≤ f ⁻¹ᵁ V b ⊓ L.U i := fun a b i x hx => ⟨hx.1.2, hx.2⟩
  have la : ∀ a b i, f ⁻¹ᵁ (V a ⊓ V b) ⊓ L.U i ≤ f ⁻¹ᵁ V a ⊓ L.U i := fun a b i x hx => ⟨hx.1.1, hx.2⟩
  have hex : ∀ a b, ∃ t : Γ(X, f ⁻¹ᵁ (V a ⊓ V b))ˣ, ∀ i,
      res (hW a b i) t = res (lb a b i) (s b i) * (res (la a b i) (s a i))⁻¹ := by
    intro a b
    refine glue_unit _ _ (hW a b) ?_ _ ?_
    · intro x hx
      obtain ⟨i, hi⟩ := exists_chart hL x
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hx, hi⟩
    · intro i j x hx
      simp only [map_mul, map_inv]
      rw [gm_res _ x (lb a b i) hx.1, gm_res _ x (la a b i) hx.1, gm_res _ x (lb a b j) hx.2,
        gm_res _ x (la a b j) hx.2]
      exact ratio_eq _ _ _ _ _ (hs1 a i j x hx.1.1.1 hx.1.2 hx.2.2) (hs1 b i j x hx.1.1.2 hx.1.2 hx.2.2)
  choose t ht using hex
  have tform : ∀ a b {Z : Scheme.{0}} (g : Z ⟶ X) (z : Z) (i : L.ι), f (g z) ∈ V a → f (g z) ∈ V b →
      g z ∈ L.U i → gm g z _ (t a b) = gm g z _ (s b i) * (gm g z _ (s a i))⁻¹ := by
    intro a b Z g z i ha hb hi
    have hm : g z ∈ f ⁻¹ᵁ (V a ⊓ V b) ⊓ L.U i := ⟨⟨ha, hb⟩, hi⟩
    rw [← gm_res g z (hW a b i) hm, ht a b i, map_mul, map_inv, gm_res g z (lb a b i) hm,
      gm_res g z (la a b i) hm]
  have hk : ∀ a b, ∃ k : Γ(Y, V a ⊓ V b)ˣ, pullU f _ k = t a b := by
    intro a b
    refine GlobalTheory.FlatDescent.exists_unit_of_gm_eq f (IsPullback.of_hasPullback f f) _ _ fun z hz => ?_
    obtain ⟨i, hi⟩ := exists_chart hL (pullback.fst f f z)
    obtain ⟨j, hj⟩ := exists_chart hL (pullback.snd f f z)
    have e : f (pullback.snd f f z) = f (pullback.fst f f z) :=
      congrArg (fun q : pullback f f ⟶ Y => q z) pullback.condition.symm
    rw [tform a b _ z i hz.1 hz.2 hi, tform a b _ z j (e ▸ hz.1) (e ▸ hz.2) hj,
      ← hs2 a z i j hz.1 hi hj, ← hs2 b z i j hz.2 hi hj]
    group
  choose k hk using hk
  have kform : ∀ a b (x : X) (i : L.ι), f x ∈ V a → f x ∈ V b → x ∈ L.U i →
      gm f x (V a ⊓ V b) (k a b) = gm (𝟙 X) x _ (s b i) * (gm (𝟙 X) x _ (s a i))⁻¹ := by
    intro a b x i ha hb hi
    have := gm_pull (𝟙 X) f x (V a ⊓ V b) ⟨ha, hb⟩ (k a b)
    rw [Category.id_comp, hk] at this
    rw [← this]
    exact tform a b (𝟙 X) x i ha hb hi
  have hL' : LB.IsLB (⟨Y, V, k⟩ : LB Y) := by
    refine ⟨?_, fun a => ?_, fun a b c => ?_⟩
    · exact eq_top_iff.2 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hV y⟩
    · refine GlobalTheory.FlatDescent.unit_ext_of_flat f fun x hx => ?_
      obtain ⟨i, hi⟩ := exists_chart hL x
      rw [gm_res f x _ hx, map_one]
      exact (kform a a x i hx hx hi).trans (mul_inv_cancel _)
    · refine GlobalTheory.FlatDescent.unit_ext_of_flat f fun x hx => ?_
      obtain ⟨i, hi⟩ := exists_chart hL x
      rw [map_mul, gm_res f x _ hx, gm_res f x _ hx, gm_res f x _ hx]
      exact ((congrArg₂ (· * ·) (kform a b x i hx.1.1 hx.1.2 hi) (kform b c x i hx.1.2 hx.2 hi)).trans
        (ratio_mul _ _ _)).trans (kform a c x i hx.1.1 hx.2 hi).symm
  have le1 : ∀ (J : PUnit → Y) (i : L.ι), ((⟨Y, V, k⟩ : LB Y).pull f).U J ⊓ L.U i ≤ f ⁻¹ᵁ V (J PUnit.unit) ⊓ L.U i :=
    fun J i x hx => ⟨mem_pull.1 hx.1, hx.2⟩
  refine ⟨⟨Y, V, k⟩, hL', ⟨fun p => (res (le1 p.1 p.2) (s (p.1 PUnit.unit) p.2))⁻¹⟩, ?_⟩
  rintro ⟨J, i⟩ ⟨J', i'⟩
  apply unit_ext
  intro x hx
  have hj := mem_pull.1 hx.1.1
  have hj' := mem_pull.1 hx.2.1
  have d := gm_div_g (L := (⟨Y, V, k⟩ : LB Y)) (L' := L) (F := f) (𝟙 X) x (J PUnit.unit) (J' PUnit.unit) i i'
    hj hj' hx.1.2 hx.2.2
  rw [map_mul, gm_res _ x _ hx, gm_res _ x _ hx]
  erw [d]
  erw [map_inv, map_inv, gm_res (𝟙 X) x (le1 J i) (show x ∈ ((⟨Y, V, k⟩ : LB Y).pull f).U J ⊓ L.U i from hx.1),
    gm_res (𝟙 X) x (le1 J' i') (show x ∈ ((⟨Y, V, k⟩ : LB Y).pull f).U J' ⊓ L.U i' from hx.2)]
  rw [Category.id_comp]
  erw [kform (J PUnit.unit) (J' PUnit.unit) x i hj hj' hx.1.2]
  exact ratio_inv _ _ _ _ (hs1 (J' PUnit.unit) i i' x hj' hx.1.2 hx.2.2)
end GlobalTheory.LBDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundlePinchedOfMatchingGenerators
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Pinch

theorem alg_cancel {G : Type*} [CommGroup G] (c a b : G) : a * b⁻¹ = (c * a) * (c * b)⁻¹ := by
  apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]; abel

theorem alg_chain {G : Type*} [CommGroup G] (a b c : G) : (b * a⁻¹) * (c * b⁻¹) = c * a⁻¹ := by
  apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]; abel

theorem alg_swap {G : Type*} [CommGroup G] (c a b : G) : c * a = c * (b * a⁻¹)⁻¹ * b := by
  apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]; abel

theorem ratio_unit {Y : Scheme.{0}} {L : LB Y} (hL : L.IsLB) {V V₁ V₂ : Y.Opens} (h₁ : V ≤ V₁) (h₂ : V ≤ V₂)
    {a₁ : ∀ k, Γ(Y, V₁ ⊓ L.U k)ˣ} {a₂ : ∀ k, Γ(Y, V₂ ⊓ L.U k)ˣ} (ha₁ : LocGen L V₁ a₁) (ha₂ : LocGen L V₂ a₂) :
    ∃ s : Γ(Y, V)ˣ, ∀ (T : Scheme.{0}) (f : T ⟶ Y) (t : T) (k : L.ι), f t ∈ V → f t ∈ L.U k →
      gm f t V s = gm f t (V₂ ⊓ L.U k) (a₂ k) * (gm f t (V₁ ⊓ L.U k) (a₁ k))⁻¹ := by
  have l₁ : ∀ k, V ⊓ L.U k ≤ V₁ ⊓ L.U k := fun k => inf_le_inf_right _ h₁
  have l₂ : ∀ k, V ⊓ L.U k ≤ V₂ ⊓ L.U k := fun k => inf_le_inf_right _ h₂
  obtain ⟨s, hs⟩ := glue_unit V (fun k => V ⊓ L.U k) (fun k => inf_le_left)
    (fun y hy => by
      obtain ⟨k, hk⟩ := exists_chart hL y
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hy, hk⟩)
    (fun k => res (l₂ k) (a₂ k) * (res (l₁ k) (a₁ k))⁻¹)
    (fun k k' y hy => by
      rw [map_mul, map_inv, map_mul, map_inv, gm_res _ y (l₂ k) hy.1, gm_res _ y (l₁ k) hy.1,
        gm_res _ y (l₂ k') hy.2, gm_res _ y (l₁ k') hy.2, ha₁ y k k' (h₁ hy.1.1) hy.1.2 hy.2.2,
        ha₂ y k k' (h₂ hy.1.1) hy.1.2 hy.2.2]
      exact (alg_cancel _ _ _).symm)
  refine ⟨s, fun T f t k ht hk => ?_⟩
  have hm : f t ∈ V ⊓ L.U k := ⟨ht, hk⟩
  rw [← gm_res f t (inf_le_left : V ⊓ L.U k ≤ V) hm s, hs k, map_mul, map_inv, gm_res f t (l₂ k) hm,
    gm_res f t (l₁ k) hm]

theorem eq_of_gm {X X' : Scheme.{0}} (p : X' ⟶ X) {V : X.Opens} (hinj : Function.Injective (pullU p V))
    {u v : Γ(X, V)ˣ} (h : ∀ x' : X', p x' ∈ V → gm p x' V u = gm p x' V v) : u = v :=
  hinj (unit_ext fun x' hx' => by
    rw [gm_pull (𝟙 X') p x' V hx', gm_pull (𝟙 X') p x' V hx', Category.id_comp]
    exact h x' hx')

end GlobalTheory.Pinch

namespace GlobalTheory.Pinch

theorem exists_lb_of_matching_gens : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z),
    i' ≫ p = p' ≫ i → GlobalTheory.Pinch.UnitsPatch p i i' p' → ∀ (L' : LB X') (N : LB Z), L'.IsLB → N.IsLB →
    ∀ (w : LB.Iso (L'.pull i') (N.pull p')) (W : X → X.Opens) (a : ∀ x k, Γ(X', p ⁻¹ᵁ (W x) ⊓ L'.U k)ˣ)
      (b : ∀ x l, Γ(Z, i ⁻¹ᵁ (W x) ⊓ N.U l)ˣ), (∀ x, x ∈ W x) →
      (∀ x, GlobalTheory.Pinch.LocGen L' (p ⁻¹ᵁ (W x)) (a x)) → (∀ x, GlobalTheory.Pinch.LocGen N (i ⁻¹ᵁ (W x)) (b x)) →
      (∀ x, GlobalTheory.Pinch.Matches i' p' w (a x) (b x)) → ∃ L : LB X, L.IsLB ∧ LBIso (L.pull p) L' := by
  intro X X' Z Z' p i i' p' hsq hU L' N hL' hN w W a b hW ha hb hm
  have pt : ∀ z : Z', p (i' z) = i (p' z) := fun z => congrArg (fun f => f z) hsq
  have key : ∀ x y, ∃ g : Γ(X, W x ⊓ W y)ˣ, ∀ (x' : X') (k : L'.ι), p x' ∈ W x ⊓ W y → x' ∈ L'.U k →
      gm p x' _ g = gm (𝟙 X') x' _ (a y k) * (gm (𝟙 X') x' _ (a x k))⁻¹ := by
    intro x y
    obtain ⟨s, hs⟩ := ratio_unit hL' (V := p ⁻¹ᵁ (W x ⊓ W y)) (fun _ h => h.1) (fun _ h => h.2) (ha x) (ha y)
    obtain ⟨t, ht⟩ := ratio_unit hN (V := i ⁻¹ᵁ (W x ⊓ W y)) (fun _ h => h.1) (fun _ h => h.2) (hb x) (hb y)
    obtain ⟨u, hu⟩ := (hU (W x ⊓ W y)).2 s t (fun z hz => by
      obtain ⟨k, hk⟩ := exists_chart hL' (i' z)
      obtain ⟨l, hl⟩ := exists_chart hN (p' z)
      have hz' : i (p' z) ∈ W x ⊓ W y := pt z ▸ hz
      rw [hs Z' i' z k hz hk, ht Z' p' z l hz' hl, hm x z k l hz.1 hz'.1 hk hl, hm y z k l hz.2 hz'.2 hk hl]
      exact alg_cancel _ _ _)
    refine ⟨u, fun x' k hx hk => ?_⟩
    have e := gm_pull (𝟙 X') p x' _ hx u
    rw [Category.id_comp] at e
    rw [← e, hu]
    exact hs X' (𝟙 X') x' k hx hk
  choose g hg using key
  have hL : (⟨X, W, g⟩ : LB X).IsLB :=
    { cover := eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hW x⟩
      g_self := fun x => eq_of_gm p (hU (W x)).1 fun x' hx => by
        obtain ⟨k, hk⟩ := exists_chart hL' x'
        refine (gm_res p x' _ hx _).trans ((hg x x x' k ⟨hx, hx⟩ hk).trans ?_)
        rw [mul_inv_cancel, map_one]
      cocycle := fun x y z => eq_of_gm p (hU _).1 fun x' hx => by
        obtain ⟨k, hk⟩ := exists_chart hL' x'
        exact ((map_mul _ _ _).trans (congrArg₂ (· * ·)
          ((gm_res p x' _ hx _).trans (hg x y x' k ⟨hx.1.1, hx.1.2⟩ hk))
          ((gm_res p x' _ hx _).trans (hg y z x' k ⟨hx.1.2, hx.2⟩ hk)))).trans
          ((alg_chain _ _ _).trans ((gm_res p x' _ hx _).trans (hg x z x' k ⟨hx.1.1, hx.2⟩ hk)).symm) }
  refine ⟨⟨X, W, g⟩, hL, ⟨fun P => res (fun x' hx' => ⟨mem_pull.1 hx'.2, hx'.1⟩ :
    L'.U P.1 ⊓ ((⟨X, W, g⟩ : LB X).pull p).U P.2 ≤ p ⁻¹ᵁ W (P.2 PUnit.unit) ⊓ L'.U P.1) (a (P.2 PUnit.unit) P.1)⟩, ?_⟩
  rintro ⟨k, J⟩ ⟨k', J'⟩
  apply unit_ext
  intro x' hx'
  have hJ : p x' ∈ W (J PUnit.unit) := mem_pull.1 hx'.1.2
  have hJ' : p x' ∈ W (J' PUnit.unit) := mem_pull.1 hx'.2.2
  have e : gm (𝟙 X') x' (((⟨X, W, g⟩ : LB X).pull p).U J ⊓ ((⟨X, W, g⟩ : LB X).pull p).U J')
      (((⟨X, W, g⟩ : LB X).pull p).g J J') = gm p x' _ (g (J PUnit.unit) (J' PUnit.unit)) := by
    show gm (𝟙 X') x' _ (∏ _k : PUnit, (res _ (pullU p _ (g (J PUnit.unit) (J' PUnit.unit)))) ^ (1 : ℤ)) = _
    rw [Fintype.prod_unique, zpow_one]
    have hq : x' ∈ ((⟨X, W, g⟩ : LB X).pull p).U J ⊓ ((⟨X, W, g⟩ : LB X).pull p).U J' := ⟨hx'.1.2, hx'.2.2⟩
    exact (gm_res _ x' _ hq _).trans ((gm_pull (𝟙 X') p x' (W (J PUnit.unit) ⊓ W (J' PUnit.unit))
      (⟨hJ, hJ'⟩ : p x' ∈ W (J PUnit.unit) ⊓ W (J' PUnit.unit)) _).trans (congrArg (fun f => gm f x' _ (g (J PUnit.unit) (J' PUnit.unit))) (Category.id_comp p)))
  have hdiv : gm (𝟙 X') x' _ ((LB.div L' ((⟨X, W, g⟩ : LB X).pull p)).g (k, J) (k', J')) =
      gm (𝟙 X') x' _ (L'.g k k') * (gm p x' _ (g (J PUnit.unit) (J' PUnit.unit)))⁻¹ :=
    (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ x' _ hx' _)
      ((map_inv _ _).trans (congrArg (·⁻¹) ((gm_res _ x' _ hx' _).trans e))))
  refine (gm_res _ x' _ hx' _).trans ((gm_res _ x' _ hx'.1 _).trans ?_)
  refine Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·) hdiv
    ((gm_res _ x' _ hx' _).trans (gm_res _ x' _ hx'.2 _)))).symm
  have h2 := hg (J PUnit.unit) (J' PUnit.unit) x' k' ⟨hJ, hJ'⟩ hx'.2.1
  rw [h2]
  exact (ha (J PUnit.unit) x' k k' hJ hx'.1.1 hx'.2.1).trans (alg_swap _ _ _)

end GlobalTheory.Pinch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleTrivialNearFibreFinite
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LBDescent

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LBDescent

theorem exists_smul_mem_span_away {R S M : Type} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [AddCommGroup M] [Module S M] [Module.Invertible S M]
    (p : Ideal R) [p.IsPrime] :
    ∃ r : R, r ∉ p ∧ ∃ m : M, ∀ x : M, ∃ a : S, algebraMap R S r • x = a • m := by
  classical
  let Q : Submonoid S := Algebra.algebraMapSubmonoid S p.primeCompl
  let T := Localization Q
  letI : Algebra (Localization.AtPrime p) T := localizationAlgebra p.primeCompl S
  haveI : Module.Finite (Localization.AtPrime p) T :=
    Module.Finite.of_isLocalization R S p.primeCompl
  haveI : Finite (MaximalSpectrum T) :=
    GlobalTheory.finite_maximalSpectrum_of_finite (Localization.AtPrime p) T
  obtain ⟨z, hz⟩ :=
    GlobalTheory.exists_bijective_toSpanSingleton_of_finite_maximalSpectrum T (LocalizedModule Q M)
  induction z using LocalizedModule.induction_on with
  | h m s =>
  have hloc : ∀ x : M, ∃ q ∈ Q, q • x ∈ Submodule.span S {m} := by
    intro x
    obtain ⟨c, hc⟩ := hz.2 (LocalizedModule.mk x 1)
    induction c using Localization.induction_on with
    | H c =>
    obtain ⟨a, t⟩ := c
    rw [LinearMap.toSpanSingleton_apply, LocalizedModule.mk_smul_mk, LocalizedModule.mk_eq] at hc
    obtain ⟨u, hu⟩ := hc
    refine ⟨(u : S) * ((t : S) * (s : S)), Q.mul_mem u.2 (Q.mul_mem t.2 s.2), ?_⟩
    rw [mul_smul, mul_smul]
    have hu' : (u : S) • (((t * s : Q) : S)) • x = (u : S) • ((1 : Q) : S) • a • m := hu.symm
    rw [Submonoid.coe_mul] at hu'
    rw [mul_smul] at hu'
    rw [hu', Submodule.mem_span_singleton]
    exact ⟨(u : S) * a, by simp [mul_smul]⟩
  choose q hqQ hq using hloc
  obtain ⟨F, hF⟩ := Module.Finite.fg_top (R := S) (M := M)
  let q₀ : S := ∏ x ∈ F, q x
  have hq₀ : q₀ ∈ Q := Q.prod_mem fun x _ => hqQ x
  have key : ∀ y ∈ Submodule.span S (F : Set M), q₀ • y ∈ Submodule.span S {m} := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      have : q₀ = (∏ x' ∈ F.erase x, q x') * q x := (Finset.prod_erase_mul F q hx).symm
      rw [this, mul_smul]
      exact Submodule.smul_mem _ _ (hq x)
    | zero => rw [smul_zero]; exact Submodule.zero_mem _
    | add y₁ y₂ _ _ h₁ h₂ => rw [smul_add]; exact Submodule.add_mem _ h₁ h₂
    | smul a y _ h => rw [smul_comm]; exact Submodule.smul_mem _ _ h
  obtain ⟨r, hr, hrq⟩ := hq₀
  refine ⟨r, hr, m, fun x => ?_⟩
  have := key x (hF ▸ Submodule.mem_top)
  rw [Submodule.mem_span_singleton] at this
  obtain ⟨a, ha⟩ := this
  exact ⟨a, by rw [hrq]; exact ha.symm⟩

theorem isFrame_res_of_smul_mem {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {U : X.Opens}
    (hU : IsAffineOpen U) (h : Γ(X, U)) (m : Γ(GlobalTheory.LB.toMod L, U))
    (hm : ∀ x : Γ(GlobalTheory.LB.toMod L, U), ∃ a : Γ(X, U), h • x = a • m) :
    GlobalTheory.LB.IsFrame ((GlobalTheory.LB.toMod L).presheaf.map (homOfLE (X.basicOpen_le h)).op m) := by
  haveI := GlobalTheory.LB.isQuasicoherent_toMod hL
  have hD : IsAffineOpen (X.basicOpen h) := hU.basicOpen h
  haveI := GlobalTheory.LB.invertible_sections hL hD
  rw [GlobalTheory.LB.isFrame_iff_bijective hD]
  have h₁ := ((GlobalTheory.QCoh.isLocalizedModule_resBasicOpen_iff (GlobalTheory.LB.toMod L) h).1
    (GlobalTheory.QCoh.isLocalizedModule_resBasicOpen (GlobalTheory.LB.toMod L) hU h)).1
  refine Module.Invertible.bijective_of_surjective
    (f := LinearMap.toSpanSingleton Γ(X, X.basicOpen h) _
      ((GlobalTheory.LB.toMod L).presheaf.map (homOfLE (X.basicOpen_le h)).op m)) ?_
  intro s
  obtain ⟨n, t, ht⟩ := h₁ s
  obtain ⟨a, ha⟩ := hm t
  obtain ⟨u, hu⟩ := GlobalTheory.QCoh.isUnit_res_of_le_basicOpen h (X.basicOpen_le h) le_rfl
  have e1 := GlobalTheory.LB.map_smul_resG (F := GlobalTheory.LB.toMod L) (X.basicOpen_le h) h t
  rw [ha, GlobalTheory.LB.map_smul_resG] at e1
  refine ⟨((u⁻¹ : Γ(X, X.basicOpen h)ˣ) : Γ(X, X.basicOpen h)) ^ (n + 1) *
    resG X (X.basicOpen_le h) a, ?_⟩
  rw [← hu] at ht
  have hu' : resG X (X.basicOpen_le h) h = (u : Γ(X, X.basicOpen h)) := hu.symm
  rw [hu', ← ht, ← mul_smul] at e1
  rw [LinearMap.toSpanSingleton_apply, mul_smul, e1, ← mul_smul, ← pow_succ', ← mul_pow,
    Units.inv_mul, one_pow, one_smul]

theorem exists_trivial_near_fibre : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] (L : LB X), L.IsLB →
    ∀ y : Y, ∃ V : Y.Opens, y ∈ V ∧
    ∃ t : ∀ i, Γ(X, f ⁻¹ᵁ V ⊓ L.U i)ˣ, ∀ (i j : L.ι) (x : X), f x ∈ V → x ∈ L.U i → x ∈ L.U j →
      gm (𝟙 X) x _ (t i) = gm (𝟙 X) x _ (L.g i j) * gm (𝟙 X) x _ (t j) := by
  intro X Y f _ L hL y
  obtain ⟨W, hW, hyW, -⟩ : ∃ W ∈ Y.affineOpens, y ∈ W ∧ W ≤ ⊤ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens)
    (show y ∈ (⊤ : Y.Opens) from trivial)
  let p : Ideal Γ(Y, W) :=
    (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)).comap (Y.presheaf.germ W y hyW).hom
  letI : Algebra Γ(Y, W) Γ(X, f ⁻¹ᵁ W) := (f.app W).hom.toAlgebra
  haveI : Module.Finite Γ(Y, W) Γ(X, f ⁻¹ᵁ W) := f.finite_app W hW
  have hW : IsAffineOpen W := hW
  have hU : IsAffineOpen (f ⁻¹ᵁ W) := hW.preimage f
  haveI := GlobalTheory.LB.invertible_sections hL hU
  obtain ⟨r, hr, m, hm⟩ := exists_smul_mem_span_away (R := Γ(Y, W)) (S := Γ(X, f ⁻¹ᵁ W))
    (M := Γ(GlobalTheory.LB.toMod L, f ⁻¹ᵁ W)) p
  have he := isFrame_res_of_smul_mem hL hU (f.app W r) m hm
  have hpre : f ⁻¹ᵁ Y.basicOpen r = X.basicOpen (f.app W r) := Scheme.preimage_basicOpen f r
  refine ⟨Y.basicOpen r, ?_, ?_⟩
  · rw [Scheme.mem_basicOpen (x := y) (hx := hyW)]
    by_contra hn
    exact hr ((IsLocalRing.mem_maximalIdeal _).2 hn)
  let F := GlobalTheory.LB.toMod L
  let e : Γ(F, f ⁻¹ᵁ Y.basicOpen r) :=
    F.presheaf.map (homOfLE hpre.le).op (F.presheaf.map (homOfLE (X.basicOpen_le _)).op m)
  have he' : GlobalTheory.LB.IsFrame e := he.map hpre.le
  let u : ∀ i, Γ(X, f ⁻¹ᵁ Y.basicOpen r ⊓ L.U i)ˣ := fun i =>
    (GlobalTheory.LB.isFrame_chartSec hL i).unit he' inf_le_right inf_le_left
  have hu : ∀ i, ((u i : Γ(X, f ⁻¹ᵁ Y.basicOpen r ⊓ L.U i)ˣ) : Γ(X, f ⁻¹ᵁ Y.basicOpen r ⊓ L.U i)) =
      GlobalTheory.LB.coord e i := fun i => by
    rw [GlobalTheory.LB.IsFrame.val_unit, GlobalTheory.LB.repr_chartSec, GlobalTheory.LB.chartEquiv_apply, GlobalTheory.LB.coord_map,
      GlobalTheory.LB.resG_resG, GlobalTheory.LB.resG_self]
  refine ⟨u, fun i j x hxV hi hj => ?_⟩
  have hxO : x ∈ f ⁻¹ᵁ Y.basicOpen r ⊓ L.U i ⊓ L.U j := ⟨⟨hxV, hi⟩, hj⟩
  rw [← gm_res (𝟙 X) x (inf_le_left : f ⁻¹ᵁ Y.basicOpen r ⊓ L.U i ⊓ L.U j ≤ _) hxO,
    ← gm_res (𝟙 X) x (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
      f ⁻¹ᵁ Y.basicOpen r ⊓ L.U i ⊓ L.U j ≤ L.U i ⊓ L.U j) hxO,
    ← gm_res (𝟙 X) x (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
      f ⁻¹ᵁ Y.basicOpen r ⊓ L.U i ⊓ L.U j ≤ f ⁻¹ᵁ Y.basicOpen r ⊓ L.U j) hxO, ← map_mul]
  congr 1
  apply Units.ext
  rw [Units.val_mul, GlobalTheory.LB.val_res, GlobalTheory.LB.val_res, GlobalTheory.LB.val_res, hu, hu]
  exact GlobalTheory.LB.coord_rel e i j _ _ _

end GlobalTheory.LBDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearSectionValueAbelianPowerStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linear_sectionValue_abelianPower : ∀ (K : Type) [Field K] (x : KeyIn K) (N : ℕ) (i : Fin 1 → x.P.L.ι) (B : Type) [CommRing B] [Algebra K B]
    (y : Sp B ⟶ (baseOver (Sp K) ⊗ x.P.A).left),
    y ≫ (fst (baseOver (Sp K)) x.P.A).left = spMap (algebraMap K B) →
    ∃ f : EA x.P (𝟙 (Sp K)) N →ₗ[K] B, ∀ s : EA x.P (𝟙 (Sp K)) N,
      f s = valR y ((LPow x.P.A x.P.L ((N : ℕ) : ℤ) (baseOver (Sp K))).U i) (s.sec.f i) := by
  first | exact @GlobalTheory.SecValLin.exists_linear_valR_sec | exact GlobalTheory.SecValLin.exists_linear_valR_sec | (intros; apply GlobalTheory.SecValLin.exists_linear_valR_sec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalGeneratorFiniteCoverNearPoint
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Pinch

theorem locGen_near_fibre_of_finite : (∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (W : X.Opens), IsAffineOpen W → ∀ F : Set X, F.Finite → F ⊆ W → ∃ (V : X.Opens) (a : ∀ k, Γ(X, V ⊓ L.U k)ˣ), F ⊆ V ∧ GlobalTheory.Pinch.LocGen L V a) → ∀ (X X' : Scheme.{0}) (p : X' ⟶ X), IsFinite p → ∀ (L : LB X'), L.IsLB → ∀ x : X, ∃ (W : X.Opens) (a : ∀ k, Γ(X', p ⁻¹ᵁ W ⊓ L.U k)ˣ), x ∈ W ∧ GlobalTheory.Pinch.LocGen L (p ⁻¹ᵁ W) a := by
  intro H X X' p hp L hL x
  obtain ⟨W₀, hW₀, hxW₀, -⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) (show x ∈ (⊤ : X.Opens) from trivial)
  have hA : IsAffineOpen (p ⁻¹ᵁ W₀) := IsAffineOpen.preimage hW₀ p
  have hF : (p.base ⁻¹' {x}).Finite := Scheme.Hom.finite_preimage_singleton p x
  have hFW : p.base ⁻¹' {x} ⊆ (p ⁻¹ᵁ W₀ : Set X') := by
    intro y hy
    show p.base y ∈ W₀
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hy
    rw [hy]; exact hxW₀
  obtain ⟨V, a, hFV, ha⟩ := H X' L hL (p ⁻¹ᵁ W₀) hA _ hF hFW
  have hcl : IsClosed (p.base '' (V : Set X')ᶜ) := p.isClosedMap _ V.isOpen.isClosed_compl
  let W : X.Opens := ⟨(p.base '' (V : Set X')ᶜ)ᶜ, hcl.isOpen_compl⟩
  have hWV : p ⁻¹ᵁ W ≤ V := by
    intro y hy
    by_contra h
    exact hy ⟨y, h, rfl⟩
  have hxW : x ∈ W := by
    rintro ⟨y, hy, hyx⟩
    exact hy (hFV (show p.base y = x from hyx))
  refine ⟨W, fun k ↦ res (inf_le_inf_right _ hWV) (a k), hxW, ?_⟩
  intro y k k' hy hk hk'
  rw [gm_res (𝟙 X') y (inf_le_inf_right _ hWV) ⟨hy, hk⟩, gm_res (𝟙 X') y (inf_le_inf_right _ hWV) ⟨hy, hk'⟩]
  exact ha y k k' (hWV hy) hk hk'

end GlobalTheory.Pinch
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocallyFreeSubsheafDetIsoStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_locallyFree_subsheaf_det_iso : ∀ (X : Scheme.{0}) (F : X.Modules) (r : ℕ) (L : LB X), L.IsLB → ∀ (s : ∀ k : L.ι, Fin r → Γ(F, L.U k)) (A : ∀ k k' : L.ι, Matrix (Fin r) (Fin r) Γ(X, L.U k ⊓ L.U k')), (∀ (k : L.ι) (V : X.Opens) (h : V ≤ L.U k), LinearIndependent Γ(X, V) fun i => GlobalTheory.Twist.resM F h (s k i)) → (∀ (k k' : L.ι) (i : Fin r), GlobalTheory.Twist.resM F (inf_le_right : L.U k ⊓ L.U k' ≤ L.U k') (s k' i) = ∑ j, A k k' j i • GlobalTheory.Twist.resM F (inf_le_left : L.U k ⊓ L.U k' ≤ L.U k) (s k j)) → (∀ k k' : L.ι, (L.g k k').val = (A k k').det) → ∃ (W : X.Modules) (ι : W ⟶ F), Mono ι ∧ GlobalTheory.VB.IsVB W r ∧ LBIso L (GlobalTheory.VB.det W r) := by
  first | exact @GlobalTheory.SubGlue.exists_sub_isVB_lbIso_det | exact GlobalTheory.SubGlue.exists_sub_isVB_lbIso_det | (intros; apply GlobalTheory.SubGlue.exists_sub_isVB_lbIso_det <;> assumption)
end

