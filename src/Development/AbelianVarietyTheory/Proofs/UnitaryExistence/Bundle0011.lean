import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0004
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0003

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FormallyUnramifiedMulN
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.MulUnramified

def affineComb {A R : Type} [CommRing A] [CommRing R] (a b c : A →+* R)
    (h : ∀ s t, (a s - c s) * (b t - c t) = 0) : A →+* R where
  toFun s := a s + b s - c s
  map_one' := by simp
  map_zero' := by simp
  map_add' s t := by simp only [map_add]; ring
  map_mul' s t := by
    simp only [map_mul]
    linear_combination - h s t - h t s

lemma appLE_congr {T X : Scheme.{0}} {f g : T ⟶ X} (h : f = g) (V : X.Opens) (W : T.Opens)
    (hf : W ≤ f ⁻¹ᵁ V) (hg : W ≤ g ⁻¹ᵁ V) : f.appLE V W hf = g.appLE V W hg := by
  subst h; rfl

lemma preimage_eq {T₀ T X : Scheme.{0}} (i : T₀ ⟶ T) (hi : Function.Surjective i) {f g : T ⟶ X}
    (h : i ≫ f = i ≫ g) (V : X.Opens) : f ⁻¹ᵁ V = g ⁻¹ᵁ V := by
  ext x
  obtain ⟨x, rfl⟩ := hi x
  have : f (i x) = g (i x) := congr($h x)
  simp [this]

lemma app_sub_eq_zero {T₀ T X : Scheme.{0}} (i : T₀ ⟶ T) {f g : T ⟶ X}
    (h : i ≫ f = i ≫ g) (V : X.Opens) (W : T.Opens)
    (hf : W ≤ f ⁻¹ᵁ V) (hg : W ≤ g ⁻¹ᵁ V) (s : Γ(X, V)) :
    i.app W (f.appLE V W hf s - g.appLE V W hg s) = 0 := by
  rw [map_sub, sub_eq_zero, ← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply,
    Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE,
    appLE_congr h]

lemma comp_appLE_apply {T P X : Scheme.{0}} (a : T ⟶ P) (p : P ⟶ X) {x : T ⟶ X} (h : a ≫ p = x)
    (V : X.Opens) (V' : P.Opens) (W : T.Opens) (h₁ : V' ≤ p ⁻¹ᵁ V) (h₂ : W ≤ a ⁻¹ᵁ V')
    (h₃ : W ≤ x ⁻¹ᵁ V) (s : Γ(X, V)) :
    a.appLE V' W h₂ (p.appLE V V' h₁ s) = x.appLE V W h₃ s := by
  rw [← CategoryTheory.comp_apply, Scheme.Hom.appLE_comp_appLE, appLE_congr h]

lemma le_preimage_of_comp {T P X : Scheme.{0}} (a : T ⟶ P) (p : P ⟶ X)
    {V : X.Opens} {V' : P.Opens} {W : T.Opens} (h₁ : V' ≤ p ⁻¹ᵁ V) (h₂ : W ≤ a ⁻¹ᵁ V') :
    W ≤ (a ≫ p) ⁻¹ᵁ V := fun _ hx ↦ h₁ (h₂ hx)

lemma parallelogram {T P X : Scheme.{0}} (p q : P ⟶ X)
    (hpq : ∀ (Z : Scheme.{0}) (u v : Z ⟶ P), u ≫ p = v ≫ p → u ≫ q = v ≫ q → u = v)
    (a b c d : T ⟶ P) (hap : a ≫ p = d ≫ p) (hbp : b ≫ p = c ≫ p)
    (haq : a ≫ q = c ≫ q) (hbq : b ≫ q = d ≫ q)
    {V : X.Opens} (hV : IsAffineOpen V) {V' : P.Opens} (hV' : IsAffineOpen V')
    {W : T.Opens} (hW : IsAffineOpen W) (hp : V' ≤ p ⁻¹ᵁ V) (hq : V' ≤ q ⁻¹ᵁ V)
    (ha : W ≤ a ⁻¹ᵁ V') (hb : W ≤ b ⁻¹ᵁ V') (hc : W ≤ c ⁻¹ᵁ V') (hd : W ≤ d ⁻¹ᵁ V')
    (h : ∀ s t, (a.appLE V' W ha s - c.appLE V' W hc s) *
      (b.appLE V' W hb t - c.appLE V' W hc t) = 0) (s : Γ(P, V')) :
    d.appLE V' W hd s = a.appLE V' W ha s + b.appLE V' W hb s - c.appLE V' W hc s := by
  let φ : Γ(P, V') ⟶ Γ(T, W) :=
    CommRingCat.ofHom (affineComb (a.appLE V' W ha).hom (b.appLE V' W hb).hom (c.appLE V' W hc).hom h)
  have hφ : ∀ s, φ s = a.appLE V' W ha s + b.appLE V' W hb s - c.appLE V' W hc s := fun _ ↦ rfl
  have key : Spec.map (d.appLE V' W hd) ≫ hV'.fromSpec = Spec.map φ ≫ hV'.fromSpec := by
    apply hpq
    · rw [Category.assoc, Category.assoc, ← hV.SpecMap_appLE_fromSpec p hV' hp,
        ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
      congr 2
      ext s
      simp only [CommRingCat.hom_comp, RingHom.comp_apply]
      rw [hφ, comp_appLE_apply a p hap _ _ _ _ _ (le_preimage_of_comp d p hp hd),
        comp_appLE_apply d p rfl _ _ _ _ _ (le_preimage_of_comp d p hp hd),
        comp_appLE_apply b p hbp _ _ _ _ _ (le_preimage_of_comp c p hp hc),
        comp_appLE_apply c p rfl _ _ _ _ _ (le_preimage_of_comp c p hp hc)]
      ring
    · rw [Category.assoc, Category.assoc, ← hV.SpecMap_appLE_fromSpec q hV' hq,
        ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
      congr 2
      ext s
      simp only [CommRingCat.hom_comp, RingHom.comp_apply]
      rw [hφ, comp_appLE_apply a q haq _ _ _ _ _ (le_preimage_of_comp c q hq hc),
        comp_appLE_apply d q rfl _ _ _ _ _ (le_preimage_of_comp d q hq hd),
        comp_appLE_apply b q hbq _ _ _ _ _ (le_preimage_of_comp d q hq hd),
        comp_appLE_apply c q rfl _ _ _ _ _ (le_preimage_of_comp c q hq hc)]
      ring
  rw [cancel_mono, Spec.map_inj] at key
  rw [key, hφ]

variable {S : Scheme.{0}}

lemma comp_mulN (G : Over S) [GrpObj G] {T : Over S} (x : T ⟶ G) (n : ℕ) :
    x ≫ mulN G n = x ^ n := by
  induction n with
  | zero => simp [mulN, Hom.one_def]
  | succ n ih => rw [mulN, pow_succ, Hom.mul_def, ← ih, comp_lift_assoc, Category.comp_id]

lemma eq_one_of_pow_eq_one (G : Over S) [GrpObj G] {T₀ T : Over S} (j : T₀ ⟶ T)
    (hj : Function.Surjective j.left)
    (hsq : ∀ (W : T.left.Opens), IsAffineOpen W → ∀ s t : Γ(T.left, W),
      j.left.app W s = 0 → j.left.app W t = 0 → s * t = 0)
    (n : ℕ) (hn : IsUnit (n : Γ(S, ⊤))) (z : T ⟶ G) (hz : j ≫ z = 1) (hzn : z ^ n = 1) :
    z = 1 := by
  apply Over.OverMorphism.ext
  refine Scheme.hom_ext_of_forall _ _ fun t ↦ ?_
  let e : T ⟶ G := 1
  have he : j ≫ e = 1 := by simp [e]
  obtain ⟨_, ⟨V, hV, rfl⟩, htV, -⟩ :=
    G.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (e.left t)) isOpen_univ
  have hcp : (lift e e).left ≫ (fst G G).left = e.left := by rw [← Over.comp_left, lift_fst]
  have hcq : (lift e e).left ≫ (snd G G).left = e.left := by rw [← Over.comp_left, lift_snd]
  have hcm : (lift e e).left ≫ (μ[G]).left = e.left := by
    rw [← Over.comp_left, ← Hom.mul_def, _root_.mul_one]
  obtain ⟨_, ⟨V', hV', rfl⟩, htV', hV'V : V' ≤ _⟩ :=
    (G ⊗ G).left.isBasis_affineOpens.exists_subset_of_mem_open (a := (lift e e).left t)
      (u := ((fst G G).left ⁻¹ᵁ V ⊓ (snd G G).left ⁻¹ᵁ V ⊓ (μ[G]).left ⁻¹ᵁ V : (G ⊗ G).left.Opens))
      ⟨⟨show ((lift e e).left ≫ (fst G G).left) t ∈ V by rwa [hcp],
        show ((lift e e).left ≫ (snd G G).left) t ∈ V by rwa [hcq]⟩,
        show ((lift e e).left ≫ (μ[G]).left) t ∈ V by rwa [hcm]⟩ (TopologicalSpace.Opens.isOpen _)
  have hp : V' ≤ (fst G G).left ⁻¹ᵁ V := hV'V.trans (inf_le_left.trans inf_le_left)
  have hq : V' ≤ (snd G G).left ⁻¹ᵁ V := hV'V.trans (inf_le_left.trans inf_le_right)
  have hm : V' ≤ (μ[G]).left ⁻¹ᵁ V := hV'V.trans inf_le_right
  obtain ⟨_, ⟨W, hW, rfl⟩, htW, hc : W ≤ (lift e e).left ⁻¹ᵁ V'⟩ :=
    T.left.isBasis_affineOpens.exists_subset_of_mem_open (a := t)
      (u := (lift e e).left ⁻¹ᵁ V') htV' (TopologicalSpace.Opens.isOpen _)
  refine ⟨W, htW, ?_⟩
  have heW : W ≤ e.left ⁻¹ᵁ V := hcp ▸ le_preimage_of_comp _ _ hp hc
  have near : ∀ x : T ⟶ G, j ≫ x = 1 → j.left ≫ x.left = j.left ≫ e.left := fun x hx ↦ by
    rw [← Over.comp_left, ← Over.comp_left, hx, he]
  have near₂ : ∀ x y : T ⟶ G, j ≫ x = 1 → j ≫ y = 1 →
      j.left ≫ (lift x y).left = j.left ≫ (lift e e).left := fun x y hx hy ↦ by
    rw [← Over.comp_left, ← Over.comp_left, comp_lift, comp_lift, hx, hy, he]
  have hW₁ : ∀ x : T ⟶ G, j ≫ x = 1 → W ≤ x.left ⁻¹ᵁ V := fun x hx ↦ by
    rw [preimage_eq j.left hj (near x hx)]; exact heW
  have hW₂ : ∀ x y : T ⟶ G, j ≫ x = 1 → j ≫ y = 1 → W ≤ (lift x y).left ⁻¹ᵁ V' :=
    fun x y hx hy ↦ by rw [preimage_eq j.left hj (near₂ x y hx hy)]; exact hc
  have add : ∀ (x y : T ⟶ G) (hx : j ≫ x = 1) (hy : j ≫ y = 1) (hxy : j ≫ (x * y) = 1)
      (s : Γ(G.left, V)), (x * y).left.appLE V W (hW₁ _ hxy) s =
        x.left.appLE V W (hW₁ _ hx) s + y.left.appLE V W (hW₁ _ hy) s - e.left.appLE V W heW s := by
    intro x y hx hy hxy s
    have := parallelogram (fst G G).left (snd G G).left
      (fun Z u v h₁ h₂ ↦ pullback.hom_ext h₁ h₂)
      (lift x e).left (lift e y).left (lift e e).left (lift x y).left
      (by simp only [← Over.comp_left, lift_fst]) (by simp only [← Over.comp_left, lift_fst])
      (by simp only [← Over.comp_left, lift_snd]) (by simp only [← Over.comp_left, lift_snd])
      hV hV' hW hp hq (hW₂ _ _ hx he) (hW₂ _ _ he hy) hc (hW₂ _ _ hx hy)
      (fun s t ↦ hsq W hW _ _ (app_sub_eq_zero _ (near₂ _ _ hx he) _ _ _ _ _)
        (app_sub_eq_zero _ (near₂ _ _ he hy) _ _ _ _ _)) ((μ[G]).left.appLE V V' hm s)
    rwa [comp_appLE_apply _ _ (x := (x * y).left) (by rw [← Over.comp_left, ← Hom.mul_def])
        _ _ _ _ _ (hW₁ _ hxy),
      comp_appLE_apply _ _ (x := x.left) (by rw [← Over.comp_left, ← Hom.mul_def, _root_.mul_one])
        _ _ _ _ _ (hW₁ _ hx),
      comp_appLE_apply _ _ (x := y.left) (by rw [← Over.comp_left, ← Hom.mul_def, _root_.one_mul])
        _ _ _ _ _ (hW₁ _ hy),
      comp_appLE_apply _ _ hcm _ _ _ _ _ heW] at this
  have hpow : ∀ k : ℕ, j ≫ (z ^ k) = 1 := fun k ↦ by rw [comp_pow, hz, one_pow]
  have ind : ∀ (k : ℕ) (s : Γ(G.left, V)), (z ^ k).left.appLE V W (hW₁ _ (hpow k)) s -
      e.left.appLE V W heW s = k * (z.left.appLE V W (hW₁ _ hz) s - e.left.appLE V W heW s) := by
    intro k s
    induction k with
    | zero =>
      rw [appLE_congr (g := e.left) (by rw [pow_zero]) _ _ _ heW]
      simp
    | succ k ih =>
      rw [appLE_congr (g := (z ^ k * z).left) (by rw [pow_succ]) _ _ _
        (hW₁ _ (by rw [← pow_succ]; exact hpow _)), add _ _ (hpow k) hz (by rw [← pow_succ]; exact hpow _)]
      push_cast
      linear_combination ih
  have hn' : IsUnit (n : Γ(T.left, W)) := by
    simpa using hn.map (T.hom.appLE ⊤ W le_top).hom
  have fin : z.left.appLE V W (hW₁ _ hz) = e.left.appLE V W heW := by
    ext s
    have := ind n s
    rw [appLE_congr (g := e.left) (by rw [hzn]) _ _ _ heW, sub_self] at this
    exact sub_eq_zero.mp (hn'.mul_right_eq_zero.mp this.symm)
  rw [← hW.isoSpec_hom_fromSpec, Category.assoc, Category.assoc,
    ← hV.SpecMap_appLE_fromSpec z.left hW (hW₁ _ hz), fin, hV.SpecMap_appLE_fromSpec e.left hW heW]

lemma mul_eq_zero_of_ker_sq {R R₀ : CommRingCat.{0}} (φ : R ⟶ R₀) (hφ : RingHom.ker φ.hom ^ 2 = ⊥)
    (W : (Spec R).Opens) (hW : IsAffineOpen W) (s t : Γ(Spec R, W))
    (hs : (Spec.map φ).app W s = 0) (ht : (Spec.map φ).app W t = 0) : s * t = 0 := by
  have h : (Spec.map φ).ker ^ 2 = ⊥ := by
    apply Scheme.IdealSheafData.ext_of_isAffine
    suffices RingHom.ker (Spec.map φ).appTop.hom ^ 2 = ⊥ by
      simp only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, Scheme.Hom.ker_apply,
        Scheme.IdealSheafData.ideal_bot, Pi.bot_apply]
      exact this
    have key : ∀ s ∈ RingHom.ker (Spec.map φ).appTop.hom,
        (Scheme.ΓSpecIso R).hom s ∈ RingHom.ker φ.hom := fun s hs ↦ by
      rw [RingHom.mem_ker] at hs ⊢
      rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_naturality, CommRingCat.comp_apply, hs,
        map_zero]
    rw [pow_two, eq_bot_iff, Ideal.mul_le]
    intro s hs t ht
    rw [Ideal.mem_bot]
    apply (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.injective
    rw [map_mul, map_zero, ← Ideal.mem_bot, ← hφ, pow_two]
    exact Ideal.mul_mem_mul (key s hs) (key t ht)
  have h' : RingHom.ker ((Spec.map φ).app W).hom ^ 2 = ⊥ := by
    simpa using congr(($h).ideal ⟨W, hW⟩)
  rw [← Ideal.mem_bot, ← h', pow_two]
  exact Ideal.mul_mem_mul hs ht

end GlobalTheory.MulUnramified

namespace GlobalTheory

open MulUnramified in

theorem formallyUnramified_mulN (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (n : ℕ)
    (hn : IsUnit (n : Γ(S, ⊤))) : FormallyUnramified (mulN G n).left := by
  refine FormallyUnramified.of_hom_ext _ fun R R₀ φ hφ hsq g₁ g₂ hi hg ↦ ?_
  have hS : g₂ ≫ G.hom = g₁ ≫ G.hom := by
    rw [← Over.w (mulN G n), reassoc_of% hg]
  let T : Over S := Over.mk (g₁ ≫ G.hom)
  let T₀ : Over S := Over.mk (Spec.map φ ≫ g₁ ≫ G.hom)
  let j : T₀ ⟶ T := Over.homMk (Spec.map φ) rfl
  let x : T ⟶ G := Over.homMk g₁ rfl
  let y : T ⟶ G := Over.homMk g₂ hS
  have hj : j ≫ x = j ≫ y := Over.OverMorphism.ext hi
  have hxy : x ^ n = y ^ n := by
    rw [← comp_mulN, ← comp_mulN]
    exact Over.OverMorphism.ext hg
  have hsurj : Function.Surjective (Spec.map φ) := by
    intro (p : PrimeSpectrum R)
    change p ∈ Set.range (PrimeSpectrum.comap φ.hom)
    rw [range_comap_of_surjective _ _ hφ, PrimeSpectrum.mem_zeroLocus]
    intro a ha
    refine p.isPrime.mem_of_pow_mem 2 ?_
    have : a ^ 2 ∈ RingHom.ker φ.hom ^ 2 := Ideal.pow_mem_pow ha 2
    rw [hsq, Ideal.mem_bot] at this
    rw [this]
    exact zero_mem _
  have := eq_one_of_pow_eq_one G j hsurj (mul_eq_zero_of_ker_sq φ hsq) n hn (x / y)
    (by rw [GrpObj.comp_div, hj, div_self']) (by rw [div_pow, hxy, div_self'])
  exact congrArg (·.left) (div_eq_one.mp this)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricallyReducedOfPerfectField
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ReducedSubgroup

section Cat

variable {𝒞 : Type*} [Category 𝒞] [CartesianMonoidalCategory 𝒞]

theorem exists_grpObj_of_mono {N B : 𝒞} [GrpObj B] (ν : N ⟶ B) [Mono ν] (e : 𝟙_ 𝒞 ⟶ N)
    (m : N ⊗ N ⟶ N) (i : N ⟶ N) (he : e ≫ ν = η[B]) (hm : m ≫ ν = (ν ⊗ₘ ν) ≫ μ[B])
    (hi : i ≫ ν = ν ≫ GrpObj.inv) : ∃ _ : GrpObj N, IsMonHom ν := by
  have hl : ∀ {T : 𝒞} (a b : T ⟶ N), lift a b ≫ m ≫ ν = (a ≫ ν) * (b ≫ ν) := by
    intro T a b
    rw [hm, lift_map_assoc, Hom.mul_def]
  have hm' : m ≫ ν = (fst N N ≫ ν) * (snd N N ≫ ν) := by
    rw [← hl, lift_fst_snd, Category.id_comp]
  have he' : ∀ {T : 𝒞} (a : T ⟶ 𝟙_ 𝒞), a ≫ e ≫ ν = 1 := by
    intro T a
    rw [he, Hom.one_def, toUnit_unique a (toUnit T)]
  have hi' : i ≫ ν = ν⁻¹ := by rw [hi, Hom.inv_def]
  letI M : MonObj N :=
    { one := e
      mul := m
      one_mul := by
        rw [← cancel_mono ν, Category.assoc, hm', comp_mul, whiskerRight_fst_assoc,
          whiskerRight_snd_assoc, he', _root_.one_mul, leftUnitor_hom]
      mul_one := by
        rw [← cancel_mono ν, Category.assoc, hm', comp_mul, whiskerLeft_fst_assoc,
          whiskerLeft_snd_assoc, he', _root_.mul_one, rightUnitor_hom]
      mul_assoc := by
        rw [← cancel_mono ν]
        simp only [Category.assoc]
        conv_lhs => rw [hm', comp_mul, whiskerRight_fst_assoc, whiskerRight_snd_assoc, hm',
          comp_mul]
        conv_rhs => rw [hm', comp_mul, whiskerLeft_fst_assoc, whiskerLeft_snd_assoc, hm',
          comp_mul, comp_mul, comp_mul]
        simp [_root_.mul_assoc] }
  refine ⟨{ inv := i, left_inv := ?_, right_inv := ?_ }, ⟨he, hm⟩⟩
  · rw [← cancel_mono ν, Category.assoc, Category.assoc]
    exact (hl i (𝟙 N)).trans (by rw [hi', Category.id_comp, inv_mul_cancel]; exact (he' _).symm)
  · rw [← cancel_mono ν, Category.assoc, Category.assoc]
    exact (hl (𝟙 N) i).trans (by rw [hi', Category.id_comp, mul_inv_cancel]; exact (he' _).symm)

end Cat

section Reduced

universe u

open Scheme.IdealSheafData in

theorem isReduced_subscheme_vanishingIdeal {X : Scheme.{u}} (Z : TopologicalSpace.Closeds X) :
    IsReduced (vanishingIdeal Z).subscheme := by
  have : ∀ U, IsReduced ((vanishingIdeal Z).subschemeCover.openCover.X U) := fun U => by
    refine (affine_isReduced_iff (.of (Γ(X, U.1) ⧸ (vanishingIdeal Z).ideal U))).mpr ?_
    refine (Ideal.isRadical_iff_quotient_reduced _).mp ?_
    exact PrimeSpectrum.isRadical_vanishingIdeal _
  exact IsReduced.of_openCover _ (vanishingIdeal Z).subschemeCover.openCover

open Scheme.IdealSheafData in

theorem vanishingIdeal_le_ker {T X : Scheme.{u}} [IsReduced T] (g : T ⟶ X)
    (Z : TopologicalSpace.Closeds X) (h : Set.range g ⊆ Z) : vanishingIdeal Z ≤ g.ker := by
  refine le_ofIdeals_iff.mpr fun U a ha => ?_
  rw [RingHom.mem_ker, ← basicOpen_eq_bot_iff, ← Scheme.preimage_basicOpen, eq_bot_iff]
  intro t ht
  have h1 : g t ∈ (vanishingIdeal Z).support := h ⟨t, rfl⟩
  have h2 := ((coe_support_inter (vanishingIdeal Z) U).le
    ⟨h1, X.basicOpen_le a ht⟩).1
  exact ((Scheme.mem_zeroLocus_iff _ _ _).mp h2 a ha ht).elim

theorem geometricallyReduced_of_perfectField {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} [IsReduced X] (f : X ⟶ Spec (.of k)) : GeometricallyReduced f := by
  refine ⟨geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms.mpr fun K _ _ => ?_⟩
  let 𝒰 := Scheme.Pullback.openCoverOfLeft X.affineOpenCover.openCover f
    (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  have : ∀ i, IsReduced (𝒰.X i) := fun i => by
    have := X.affineOpenCover.map_prop i
    have h0 : IsReduced (Spec (X.affineOpenCover.X i)) :=
      isReduced_of_isOpenImmersion (X.affineOpenCover.f i)
    have h1 := (affine_isReduced_iff _).mp h0
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.affineOpenCover.f i ≫ f)
    change IsReduced (pullback (X.affineOpenCover.f i ≫ f) _)
    rw [← hφ]
    letI : Algebra k (X.affineOpenCover.X i) := φ.hom.toAlgebra
    have h2 := ReducedAlg.isReduced_tensor (k := k) (X.affineOpenCover.X i) K
    have h3 := (affine_isReduced_iff
      (.of (TensorProduct k (X.affineOpenCover.X i) K))).mpr h2
    exact isReduced_of_isOpenImmersion (pullbackSpecIso k (X.affineOpenCover.X i) K).hom
  exact IsReduced.of_openCover _ 𝒰

end Reduced

theorem range_subset_of_points {k : Type} [Field k] [IsAlgClosed k] {T B : Over (Sp k)}
    [LocallyOfFiniteType T.hom] (g : T ⟶ B) {Z : Set B.left} (hZ : IsClosed Z)
    (h : ∀ x : 𝟙_ (Over (Sp k)) ⟶ T, Set.range (x ≫ g).left ⊆ Z) : Set.range g.left ⊆ Z := by
  have := LocallyOfFiniteType.jacobsonSpace T.hom
  rintro _ ⟨t, rfl⟩
  by_contra ht
  obtain ⟨x, hx, hxc⟩ := nonempty_inter_closedPoints (Z := (g.left ⁻¹' Z)ᶜ) ⟨t, ht⟩
    (hZ.preimage g.left.continuous).isOpen_compl.isLocallyClosed
  let x' : 𝟙_ (Over (Sp k)) ⟶ T :=
    Over.homMk (pointOfClosedPoint T.hom x hxc) (pointOfClosedPoint_comp T.hom x hxc)
  refine hx (h x' ⟨IsLocalRing.closedPoint k, ?_⟩)
  exact congrArg g.left (pointOfClosedPoint_apply T.hom x hxc _)

open Scheme.IdealSheafData in

theorem exists_smooth_closed_subgroup (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k))
    [GrpObj B] (hB : LocallyOfFiniteType B.hom) (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ B))
    (Z : Set B.left) (hZ : IsClosed Z) (hC : ∀ x, x ∈ C ↔ Set.range x.left ⊆ Z) :
    ∃ (N : Over (Sp k)) (_ : GrpObj N) (ν : N ⟶ B), IsMonHom ν ∧ IsClosedImmersion ν.left ∧
      Smooth N.hom ∧ Set.range ν.left = Z := by
  let I : B.left.IdealSheafData := vanishingIdeal ⟨Z, hZ⟩
  let N : Over (Sp k) := Over.mk (I.subschemeι ≫ B.hom)
  let ν : N ⟶ B := Over.homMk I.subschemeι rfl
  have hν : IsClosedImmersion ν.left := inferInstanceAs (IsClosedImmersion I.subschemeι)
  have hr : Set.range ν.left = Z := by
    change Set.range I.subschemeι = Z
    rw [range_subschemeι]
    rfl
  have : Mono ν := (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono ν.left))
  have hred : IsReduced N.left := isReduced_subscheme_vanishingIdeal _
  have hft : LocallyOfFiniteType N.hom :=
    inferInstanceAs (LocallyOfFiniteType (I.subschemeι ≫ B.hom))
  have hgr : GeometricallyReduced N.hom := geometricallyReduced_of_perfectField N.hom
  have hnoeth : IsLocallyNoetherian N.left := LocallyOfFiniteType.isLocallyNoetherian N.hom
  have hlift : ∀ {T : Over (Sp k)} [IsReduced T.left] [LocallyOfFiniteType T.hom] (g : T ⟶ B),
      (∀ x : 𝟙_ (Over (Sp k)) ⟶ T, x ≫ g ∈ C) → ∃ l : T ⟶ N, l ≫ ν = g := by
    intro T _ _ g hg
    have h1 := range_subset_of_points g hZ fun x => (hC _).mp (hg x)
    have h2 : I.subschemeι.ker ≤ g.left.ker := by
      rw [ker_subschemeι]
      exact vanishingIdeal_le_ker g.left ⟨Z, hZ⟩ h1
    have h3 := IsClosedImmersion.lift_fac I.subschemeι g.left h2
    refine ⟨Over.homMk (IsClosedImmersion.lift I.subschemeι g.left h2) ?_, ?_⟩
    · change _ ≫ I.subschemeι ≫ B.hom = _
      rw [← Category.assoc, h3, Over.w]
    · ext1
      exact h3
  have hmem : ∀ x : 𝟙_ (Over (Sp k)) ⟶ N, x ≫ ν ∈ C := fun x => by
    rw [hC, ← hr]
    rintro _ ⟨t, rfl⟩
    exact ⟨x.left t, rfl⟩
  have : IsReduced (𝟙_ (Over (Sp k))).left := inferInstanceAs (IsReduced (Sp k))
  have : LocallyOfFiniteType (𝟙_ (Over (Sp k))).hom :=
    inferInstanceAs (LocallyOfFiniteType (𝟙 (Sp k)))
  have : IsReduced (N ⊗ N).left := inferInstanceAs (IsReduced (pullback N.hom N.hom))
  have : LocallyOfFiniteType (N ⊗ N).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.fst N.hom N.hom ≫ N.hom))
  obtain ⟨e, he⟩ := hlift η[B] fun x => by
    rw [toUnit_unique x (toUnit _), ← Hom.one_def]
    exact C.one_mem
  obtain ⟨m, hm⟩ := hlift ((ν ⊗ₘ ν) ≫ μ[B]) fun x => by
    have : x ≫ (ν ⊗ₘ ν) ≫ μ[B] = ((x ≫ fst N N) ≫ ν) * ((x ≫ snd N N) ≫ ν) := by
      rw [Hom.mul_def, ← lift_map, Category.assoc, ← comp_lift, lift_fst_snd, Category.comp_id]
    rw [this]
    exact C.mul_mem (hmem _) (hmem _)
  obtain ⟨i, hi⟩ := hlift (ν ≫ GrpObj.inv) fun x => by
    rw [← Category.assoc, ← Hom.inv_def]
    exact C.inv_mem (hmem _)
  obtain ⟨G, hG⟩ := exists_grpObj_of_mono ν e m i he hm hi
  refine ⟨N, G, ν, hG, hν, ?_, hr⟩
  letI : GrpObj (Over.mk N.hom) := G
  exact smooth_of_grpObj N.hom

end GlobalTheory.ReducedSubgroup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsIntegralAndIsNormalSchemeOfSmoothDvr
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem isDominant_spMap_of_isFractionRing (T K : Type) [CommRing T] [IsDomain T] [Field K]
    [Algebra T K] [IsFractionRing T K] : IsDominant (spMap (algebraMap T K)) := by
  refine ⟨?_⟩
  change DenseRange (PrimeSpectrum.comap (algebraMap T K))
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
    (RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective T K)]
  exact bot_le

theorem isDominant_genericFibre_of_flat (T K : Type) [CommRing T] [IsDomain T] [Field K]
    [Algebra T K] [IsFractionRing T K] {X : Scheme.{0}} (f : X ⟶ Sp T) [Flat f] :
    IsDominant (pullback.fst f (spMap (algebraMap T K))) := by
  have := isDominant_spMap_of_isFractionRing T K
  have := IsSchemeTheoreticallyDominant.of_isDominant (spMap (algebraMap T K))
  infer_instance

theorem connectedSpace_of_flat_of_genericFibre (T K : Type) [CommRing T] [IsDomain T] [Field K]
    [Algebra T K] [IsFractionRing T K] {X : Scheme.{0}} (f : X ⟶ Sp T) [Flat f]
    [ConnectedSpace ↥(pullback f (spMap (algebraMap T K)))] : ConnectedSpace X := by
  have := isDominant_genericFibre_of_flat T K f
  let g := pullback.fst f (spMap (algebraMap T K))
  have h : _root_.IsConnected (closure (Set.range g)) := (isConnected_range g.continuous).closure
  rw [g.denseRange.closure_range] at h
  exact connectedSpace_iff_univ.mpr h

theorem isIntegral_and_isNormalScheme_of_smooth (T K : Type) [CommRing T] [IsDomain T]
    [IsNoetherianRing T] [IsIntegrallyClosed T] [Field K] [Algebra T K] [IsFractionRing T K]
    {X : Scheme.{0}} (f : X ⟶ Sp T) [Smooth f]
    [ConnectedSpace ↥(pullback f (spMap (algebraMap T K)))] :
    IsIntegral X ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X := by
  have hT : GlobalTheory.IsNormalScheme (Sp T) := inferInstance
  have hX : GlobalTheory.IsNormalScheme X := (isNormalScheme_iff X).mpr
    (forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth f ((isNormalScheme_iff _).mp hT))
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have := connectedSpace_of_flat_of_genericFibre T K f
  exact ⟨IsNormalScheme.isIntegral_of_connectedSpace X, hX.pred X⟩

theorem isIntegral_and_isNormalScheme_of_smooth_dvr :
    ∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K]
      [IsFractionRing T K] (G : Over (Sp T)), Smooth G.hom →
      ConnectedSpace ((Over.pullback (spMap (algebraMap T K))).obj G).left →
      IsIntegral G.left ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme G.left := by
  intro T K _ _ _ _ _ _ G hG hc
  have : ConnectedSpace ↥(pullback G.hom (spMap (algebraMap T K))) := hc
  exact isIntegral_and_isNormalScheme_of_smooth T K G.hom

end GlobalTheory
end

