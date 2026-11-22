import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0458
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0456
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0436
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0425
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0445
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0446
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyVanishesArtinian
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cohomology_vanishes_artinian : ∀ (q : ℕ) (K : Type) [CommRing K] [IsArtinianRing K] [IsReduced K] (n i : ℤ), (∀ M : MaximalSpectrum K, Subsingleton (Ht q (sp (K ⧸ M.asIdeal)) n i)) → Subsingleton (Ht q (sp K) n i) := by
  first | (exact @GlobalTheory.EtC.ArtCoh.ht_subsingleton_artinian) | (exact GlobalTheory.EtC.ArtCoh.ht_subsingleton_artinian) | (intros; apply GlobalTheory.EtC.ArtCoh.ht_subsingleton_artinian <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommaDescentInjective
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

namespace GlobalTheory.CatCoh

theorem pull2_restrict_injective_of_comma : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), (∀ (T : C) (x : (F).obj T), (∀ t (u : T ⟶ G.obj t), mp (F) u x = 0) → x = 0) → (∀ (T : C) (s : ∀ t, (T ⟶ G.obj t) → (F).obj (G.obj t)), (∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), s t' (u ≫ G.map a) = mp (F) (G.map a) (s t u)) → ∃ x : (F).obj T, ∀ t u, mp (F) u x = s t u) → (∀ (T : C) (y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → (F).obj (G.obj t')), (∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), y t t'' u (a ≫ b) = mp (F) (G.map b) (y t t' u a) + y t' t'' (u ≫ G.map a) b) → ∃ g : ∀ t, (T ⟶ G.obj t) → (F).obj (G.obj t), ∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), g t' (u ≫ G.map a) - mp (F) (G.map a) (g t u) = y t t' u a) → Function.Injective (CoefMap.restrict F G).pull2 := by
  intro R _ C _ C' _ F G hsep hglue hvan
  rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨z, rfl⟩ := H2.mk_surjective F c
  rw [CoefMap.pullCohomologyTwo_class, H2.mk_eq_zero] at hc
  obtain ⟨y0, hy0⟩ := hc
  obtain ⟨y, hy'⟩ : ∃ y : ∀ t t' (_ : t ⟶ t'), F.obj (G.obj t'), ∀ t t' t'' (a : t ⟶ t')
      (b : t' ⟶ t''), mp F (G.map b) (y t t' a) - y t t'' (a ≫ b) + y t' t'' b
        = z.1 _ _ _ (G.map a) (G.map b) := ⟨y0, fun t t' t'' a b ↦
    congrFun (congrFun (congrFun (congrFun (congrFun hy0 t) t') t'') a) b⟩
  have hg : ∀ T : C, ∃ g : ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t), ∀ t t' (u : T ⟶ G.obj t)
      (a : t ⟶ t'), g t' (u ≫ G.map a) - mp F (G.map a) (g t u)
        = z.1 _ _ _ u (G.map a) - y t t' a := fun T ↦
    hvan T (fun t t' u a ↦ z.1 _ _ _ u (G.map a) - y t t' a) fun t t' t'' u a b ↦ by
      have k1 := z.2 u (G.map a) (G.map b)
      have k2 := hy' t t' t'' a b
      rw [Functor.map_comp]
      simp only [map_sub]
      linear_combination k2 - k1
  choose g hg using hg
  have hx : ∀ T T' (φ : T ⟶ T'), ∃ x : F.obj T', ∀ t (u : T' ⟶ G.obj t),
      mp F u x = z.1 _ _ _ φ u - g T t (φ ≫ u) + g T' t u := by
    intro T T' φ
    refine hglue T' _ fun t t' u a ↦ ?_
    have k1 := z.2 φ u (G.map a)
    have k2 := hg T t t' (φ ≫ u) a
    have k3 := hg T' t t' u a
    rw [Category.assoc] at k2
    simp only [map_sub, map_add]
    linear_combination -k1 - k2 + k3
  choose x hx using hx
  refine H2.mk_eq_zero.2 ⟨x, ?_⟩
  funext T T' T'' φ ψ
  refine sub_eq_zero.1 (hsep T'' _ fun t u ↦ ?_)
  have k1 := z.2 φ ψ u
  have k2 := hx T T' φ t (ψ ≫ u)
  have k3 := hx T T'' (φ ≫ ψ) t u
  have k4 := hx T' T'' ψ t u
  rw [mp_comp] at k2
  rw [d1_apply]
  simp only [map_sub, map_add, Category.assoc] at k2 k3 ⊢
  linear_combination k2 - k3 + k4 - k1

end GlobalTheory.CatCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommaDescentRestrictionEquiv
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

namespace GlobalTheory.CatCoh.Desc

theorem pull2_surjective_of_comma : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), (∀ (T : C) (x : (F).obj T), (∀ t (u : T ⟶ G.obj t), mp (F) u x = 0) → x = 0) → (∀ (T : C) (s : ∀ t, (T ⟶ G.obj t) → (F).obj (G.obj t)), (∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), s t' (u ≫ G.map a) = mp (F) (G.map a) (s t u)) → ∃ x : (F).obj T, ∀ t u, mp (F) u x = s t u) → (∀ (T : C) (y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → (F).obj (G.obj t')), (∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), y t t'' u (a ≫ b) = mp (F) (G.map b) (y t t' u a) + y t' t'' (u ≫ G.map a) b) → ∃ g : ∀ t, (T ⟶ G.obj t) → (F).obj (G.obj t), ∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), g t' (u ≫ G.map a) - mp (F) (G.map a) (g t u) = y t t' u a) → (∀ (T : C) (z : ∀ t t' t'', (T ⟶ G.obj t) → (t ⟶ t') → (t' ⟶ t'') → (F).obj (G.obj t'')), (∀ t t' t'' t''' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t'') (c : t'' ⟶ t'''), mp (F) (G.map c) (z t t' t'' u a b) + z t t'' t''' u (a ≫ b) c = z t t' t''' u a (b ≫ c) + z t' t'' t''' (u ≫ G.map a) b c) → ∃ y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → (F).obj (G.obj t'), ∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), mp (F) (G.map b) (y t t' u a) - y t t'' u (a ≫ b) + y t' t'' (u ≫ G.map a) b = z t t' t'' u a b) → Function.Surjective (CoefMap.restrict F G).pull2 := by
  intro R _ C _ C' _ F G sep glue van1 van2 c
  obtain ⟨y, rfl⟩ := H2.mk_surjective _ c
  obtain ⟨Y, hY⟩ : ∃ Y : ∀ t t' t'' : C', (t ⟶ t') → (t' ⟶ t'') → F.obj (G.obj t''),
      ∀ t t' t'' a b, Y t t' t'' a b = y.1 t t' t'' a b := ⟨y.1, fun _ _ _ _ _ ↦ rfl⟩
  have hy : ∀ t t' t'' t''' (a : t ⟶ t') (b : t' ⟶ t'') (c : t'' ⟶ t'''),
      mp F (G.map c) (Y t t' t'' a b) + Y t t'' t''' (a ≫ b) c =
        Y t t' t''' a (b ≫ c) + Y t' t'' t''' b c := by
    intro t t' t'' t''' a b c
    simp only [hY]
    exact y.2 a b c
  choose h hh using fun T : C ↦ van2 T (fun t t' t'' _ a b ↦ Y t t' t'' a b)
    (fun t t' t'' t''' _ a b c ↦ hy t t' t'' t''' a b c)
  choose m hm using fun (T T' : C) (φ : T ⟶ T') ↦
    van1 T' (fun t t' u a ↦ h T t t' (φ ≫ u) a - h T' t t' u a) (fun t t' t'' u a b ↦ by
      have k1 := hh T t t' t'' (φ ≫ u) a b
      have k2 := hh T' t t' t'' u a b
      simp only [map_sub, Category.assoc] at k1 ⊢
      linear_combination k2 - k1)
  choose x hx using fun (T T' T'' : C) (φ : T ⟶ T') (ψ : T' ⟶ T'') ↦
    glue T'' (fun t u ↦ m T T' φ t (ψ ≫ u) + m T' T'' ψ t u - m T T'' (φ ≫ ψ) t u)
      (fun t t' u a ↦ by
        have k1 := hm T T' φ t t' (ψ ≫ u) a
        have k2 := hm T' T'' ψ t t' u a
        have k3 := hm T T'' (φ ≫ ψ) t t' u a
        simp only [map_sub, map_add, Category.assoc] at k1 k3 ⊢
        linear_combination k1 + k2 - k3)
  refine ⟨H2.mk F ⟨fun T T' T'' φ ψ ↦ x T T' T'' φ ψ,
    fun T T' T'' T''' φ ψ χ ↦ sub_eq_zero.1 (sep T''' _ fun t u ↦ ?_)⟩, ?_⟩
  · have k1 := hx _ _ _ φ ψ t (χ ≫ u)
    have k2 := hx _ _ _ (φ ≫ ψ) χ t u
    have k3 := hx _ _ _ φ (ψ ≫ χ) t u
    have k4 := hx _ _ _ ψ χ t u
    simp only [map_sub, map_add, Category.assoc, mp_comp] at k1 k2 k3 k4 ⊢
    linear_combination k1 + k2 - k3 - k4
  · rw [CoefMap.pullCohomologyTwo_class, H2.mk_eq_mk]
    refine ⟨fun t t' a ↦ m _ _ (G.map a) t' (𝟙 _) - h _ t t' (𝟙 _) a, ?_⟩
    funext t t' t'' a b
    simp only [Pi.sub_apply]
    rw [← hY]
    have k1 := hx _ _ _ (G.map a) (G.map b) t'' (𝟙 _)
    have k2 := hm _ _ (G.map a) t' t'' (𝟙 _) b
    have k3 := hh _ t t' t'' (𝟙 _) a b
    simp only [mp_id, Category.id_comp, Category.comp_id] at k1 k2 k3
    change mp F (G.map b) (m _ _ (G.map a) t' (𝟙 _) - h _ t t' (𝟙 _) a) -
        (m _ _ (G.map (a ≫ b)) t'' (𝟙 _) - h _ t t'' (𝟙 _) (a ≫ b)) +
        (m _ _ (G.map b) t'' (𝟙 _) - h _ t' t'' (𝟙 _) b) =
      x _ _ _ (G.map a) (G.map b) - Y t t' t'' a b
    rw [G.map_comp]
    simp only [map_sub]
    linear_combination -k1 - k2 - k3

end GlobalTheory.CatCoh.Desc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommaFirstOrderCocycleLift
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechDR

theorem pullHyp2_restrict_injective {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type}
    [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C)
    (h2 : Function.Injective (CoefMap.restrict F G).pull2)
    (h1 : Function.Surjective (CoefMap.restrict F G).pull1)
    (hc : ∀ κ : A1 F, (∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''),
        κ T T'' (φ ≫ ψ) = p1 F ψ (κ T T' φ) + κ T' T'' ψ) →
      ∀ θ' : ∀ t, Ω[F.obj (G.obj t)⁄R],
        (∀ ⦃t t' : C'⦄ (a : t ⟶ t'), κ _ _ (G.map a) = θ' t' - p1 F (G.map a) (θ' t)) →
        ∃ θ : A0 F, ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), κ T T' φ = θ T' - p1 F φ (θ T))
    (hf : Function.Surjective (pullGlob1 (CoefMap.restrict F G)))
    (hs : ∀ (T : C) (x : Om R (F.obj T) 2), (∀ t (u : T ⟶ G.obj t), pOm F 2 u x = 0) → x = 0) :
    Function.Injective (pullHyp2 (CoefMap.restrict F G)) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨c, rfl⟩ := Hyp2.mk_surjective F x
  rw [pullHyp2_mk, Hyp2.mk_eq_zero] at hx
  obtain ⟨⟨f₀, θ₀⟩, hfe⟩ := hx
  obtain ⟨f', rfl⟩ : ∃ f' : ∀ (t t' : C') (_ : t ⟶ t'), F.obj (G.obj t'), (f' : C1 (G ⋙ F)) = f₀ :=
    ⟨f₀, rfl⟩
  obtain ⟨θ', rfl⟩ : ∃ θ' : ∀ t, Ω[F.obj (G.obj t)⁄R], (θ' : A0 (G ⋙ F)) = θ₀ := ⟨θ₀, rfl⟩
  have hz : ∀ ⦃t t' t'' : C'⦄ (a : t ⟶ t') (b : t' ⟶ t''),
      mp F (G.map b) (f' t t' a) - f' t t'' (a ≫ b) + f' t' t'' b =
        c.1.1 _ _ _ (G.map a) (G.map b) :=
    fun t t' t'' a b ↦ congrArg (fun y : Tot2 (G ⋙ F) ↦ y.1 t t' t'' a b) hfe
  have ha : ∀ ⦃t t' : C'⦄ (a : t ⟶ t'),
      θ' t' - p1 F (G.map a) (θ' t) - D R _ (f' t t' a) = c.1.2.1 _ _ (G.map a) :=
    fun t t' a ↦ (congrArg (fun y : Tot2 (G ⋙ F) ↦ y.2.1 t t' a) hfe).trans (cechDeRhamCoefMapOneForms_restrictAlongFunctor F G t' _)
  have hη : ∀ t, dOne R _ (θ' t) = c.1.2.2 (G.obj t) :=
    fun t ↦ (congrArg (fun y : Tot2 (G ⋙ F) ↦ y.2.2 t) hfe).trans (qOm_restrict F G t _)

  have hz0 : H2.mk F ⟨c.1.1, (mem_cechDeRhamTotalCocyclesTwo_iff.1 c.2).1⟩ = 0 := h2 (by
    rw [CoefMap.pullCohomologyTwo_class, map_zero]
    exact H2.mk_eq_zero.2 ⟨f', by funext t t' t'' a b; exact hz a b⟩)
  obtain ⟨f, hfz⟩ := H2.mk_eq_zero.1 hz0
  have hf1 : ∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''),
      mp F ψ (f T T' φ) - f T T'' (φ ≫ ψ) + f T' T'' ψ = c.1.1 T T' T'' φ ψ :=
    fun T T' T'' φ ψ ↦ congrFun (congrFun (congrFun (congrFun (congrFun hfz T) T') T'') φ) ψ

  let u : Z1 (G ⋙ F) := ⟨fun t t' a ↦ f' t t' a - f _ _ (G.map a), fun t t' t'' a b ↦ by
    have e1 := hz a b
    have e2 := hf1 (G.map a) (G.map b)
    rw [← G.map_comp] at e2
    show f' t t'' (a ≫ b) - f _ _ (G.map (a ≫ b)) =
      mp F (G.map b) (f' t t' a - f _ _ (G.map a)) + (f' t' t'' b - f _ _ (G.map b))
    rw [map_sub]
    linear_combination e2 - e1⟩
  obtain ⟨g₀, hg₀⟩ := h1 (H1.mk _ u)
  obtain ⟨g, rfl⟩ := H1.mk_surjective F g₀
  rw [CoefMap.pullCohomologyOne_class, H1.mk_eq_mk] at hg₀
  obtain ⟨h₀, hh'⟩ := hg₀
  obtain ⟨h', rfl⟩ : ∃ h' : ∀ t, F.obj (G.obj t), (h' : C0 (G ⋙ F)) = h₀ := ⟨h₀, rfl⟩
  have hfu : ∀ ⦃t t' : C'⦄ (a : t ⟶ t'), f' t t' a =
      f _ _ (G.map a) + g.1 _ _ (G.map a) - (h' t' - mp F (G.map a) (h' t)) := fun t t' a ↦ by
    have e : h' t' - mp F (G.map a) (h' t) = g.1 _ _ (G.map a) - (f' t t' a - f _ _ (G.map a)) :=
      congrFun (congrFun (congrFun hh' t) t') a
    linear_combination e
  obtain ⟨f₁, hf₁⟩ : ∃ f₁ : C1 F, ∀ T T' φ, f₁ T T' φ = f T T' φ + g.1 T T' φ := ⟨_, fun _ _ _ ↦ rfl⟩
  have hf1' : ∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''),
      mp F ψ (f₁ T T' φ) - f₁ T T'' (φ ≫ ψ) + f₁ T' T'' ψ = c.1.1 T T' T'' φ ψ := fun T T' T'' φ ψ ↦ by
    rw [hf₁, hf₁, hf₁, map_add]
    linear_combination hf1 φ ψ - Z1.comp g φ ψ

  obtain ⟨a₁, ha₁⟩ : ∃ a₁ : A1 F, ∀ T T' φ, a₁ T T' φ = c.1.2.1 T T' φ + D R _ (f₁ T T' φ) :=
    ⟨_, fun _ _ _ ↦ rfl⟩
  have hac : ∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''),
      a₁ T T'' (φ ≫ ψ) = p1 F ψ (a₁ T T' φ) + a₁ T' T'' ψ := fun T T' T'' φ ψ ↦ by
    have e := cechDeRhamTotalCocyclesTwo.one c φ ψ
    rw [← hf1' φ ψ, map_add, map_sub] at e
    rw [ha₁, ha₁, ha₁, map_add, p1_D, e]
    abel
  obtain ⟨θ'', hθ''⟩ : ∃ θ'' : ∀ t, Ω[F.obj (G.obj t)⁄R], ∀ t, θ'' t = θ' t + D R _ (h' t) :=
    ⟨_, fun _ ↦ rfl⟩
  have hres : ∀ ⦃t t' : C'⦄ (a : t ⟶ t'), a₁ _ _ (G.map a) = θ'' t' - p1 F (G.map a) (θ'' t) :=
    fun t t' a ↦ by
      have e := ha a
      rw [hfu a] at e
      simp only [map_add, map_sub] at e
      rw [ha₁, hθ'', hθ'', hf₁]
      simp only [map_add, p1_D]
      linear_combination (norm := abel1) -e
  obtain ⟨θ, hθ⟩ := hc a₁ hac θ'' hres

  let ω' : Glob1 (G ⋙ F) := ⟨fun t ↦ θ (G.obj t) - θ'' t, fun t t' a ↦ by
    have e1 := hθ (G.map a)
    have e2 := hres a
    show θ (G.obj t') - θ'' t' = p1 F (G.map a) (θ (G.obj t) - θ'' t)
    rw [map_sub]
    linear_combination (norm := abel1) e2 - e1⟩
  obtain ⟨ω, hω⟩ := hf ω'
  have hωG : ∀ t, ω.1 (G.obj t) = θ (G.obj t) - θ'' t := fun t ↦
    (cechDeRhamCoefMapOneForms_restrictAlongFunctor F G t _).symm.trans (congrArg (fun y : Glob1 (G ⋙ F) ↦ y.1 t) hω)
  obtain ⟨θ₁, hθ₁⟩ : ∃ θ₁ : A0 F, ∀ T, θ₁ T = θ T - ω.1 T := ⟨_, fun _ ↦ rfl⟩
  have hθ1 : ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), a₁ T T' φ = θ₁ T' - p1 F φ (θ₁ T) := fun T T' φ ↦ by
    rw [hθ₁, hθ₁, map_sub, ← ω.2 φ, hθ φ]; abel
  have hθ1G : ∀ t, θ₁ (G.obj t) = θ'' t := fun t ↦ by rw [hθ₁, hωG]; abel

  obtain ⟨η₂, hη₂⟩ : ∃ η₂ : W0 F 2, ∀ T, η₂ T = c.1.2.2 T - dOne R _ (θ₁ T) := ⟨_, fun _ ↦ rfl⟩
  have hη2 : ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), η₂ T' = pOm F 2 φ (η₂ T) := fun T T' φ ↦ by
    have e1 := cechDeRhamTotalCocyclesTwo.two c φ
    have e2 := congrArg (dOne R _) (hθ1 φ)
    rw [ha₁] at e2
    simp only [map_add, map_sub, dOne_D, add_zero] at e2
    rw [hη₂, hη₂, map_sub, pOm_dOne]
    linear_combination (norm := abel1) e1 + e2
  have hη2G : ∀ t, η₂ (G.obj t) = 0 := fun t ↦ by
    rw [hη₂, hθ1G, hθ'', map_add, dOne_D, add_zero, ← hη t, sub_self]
  have hη0 : ∀ T, η₂ T = 0 := fun T ↦ hs T _ fun t u ↦ by rw [← hη2 u, hη2G]
  refine Hyp2.mk_eq_zero.2 ⟨(f₁, θ₁), Tot2.ext (fun T T' T'' φ ψ ↦ ?_) (fun T T' φ ↦ ?_) fun T ↦ ?_⟩
  · exact hf1' φ ψ
  · have e := hθ1 φ
    rw [ha₁] at e
    show θ₁ T' - p1 F φ (θ₁ T) - D R _ (f₁ T T' φ) = c.1.2.1 T T' φ
    linear_combination (norm := abel1) -e
  · have e := hη0 T
    rw [hη₂] at e
    exact (sub_eq_zero.1 e).symm

end GlobalTheory.CechDR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommaSecondOrderCocycleLift
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechDR

theorem pullHyp2_restrict_surjective : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), Function.Surjective (CoefMap.restrict F G).pull2 → (∀ κ : A2 F, (∀ ⦃T T' T'' T''' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T'') (χ : T'' ⟶ T'''), p1 F χ (κ T T' T'' φ ψ) + κ T T'' T''' (φ ≫ ψ) χ = κ T T' T''' φ (ψ ≫ χ) + κ T' T'' T''' ψ χ) → ∀ β' : ∀ t t', (t ⟶ t') → Ω[F.obj (G.obj t')⁄R], (∀ ⦃t t' t'' : C'⦄ (a : t ⟶ t') (b : t' ⟶ t''), κ _ _ _ (G.map a) (G.map b) = p1 F (G.map b) (β' t t' a) - β' t t'' (a ≫ b) + β' t' t'' b) → ∃ β : A1 F, ∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''), κ T T' T'' φ ψ = p1 F ψ (β T T' φ) - β T T'' (φ ≫ ψ) + β T' T'' ψ) → (∀ β' : ∀ t t', (t ⟶ t') → Ω[F.obj (G.obj t')⁄R], (∀ ⦃t t' t'' : C'⦄ (a : t ⟶ t') (b : t' ⟶ t''), β' t t'' (a ≫ b) = p1 F (G.map b) (β' t t' a) + β' t' t'' b) → ∃ β : A1 F, (∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''), β T T'' (φ ≫ ψ) = p1 F ψ (β T T' φ) + β T' T'' ψ) ∧ ∃ θ' : ∀ t, Ω[F.obj (G.obj t)⁄R], ∀ ⦃t t' : C'⦄ (a : t ⟶ t'), β _ _ (G.map a) - β' t t' a = θ' t' - p1 F (G.map a) (θ' t)) → (∀ κ : W1 F 2, (∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''), κ T T'' (φ ≫ ψ) = pOm F 2 ψ (κ T T' φ) + κ T' T'' ψ) → ∀ θ' : ∀ t, Om R (F.obj (G.obj t)) 2, (∀ ⦃t t' : C'⦄ (a : t ⟶ t'), κ _ _ (G.map a) = θ' t' - pOm F 2 (G.map a) (θ' t)) → ∃ θ : W0 F 2, ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), κ T T' φ = θ T' - pOm F 2 φ (θ T)) → (∀ η' : ∀ t, Om R (F.obj (G.obj t)) 2, (∀ ⦃t t' : C'⦄ (a : t ⟶ t'), η' t' = pOm F 2 (G.map a) (η' t)) → ∃ η : W0 F 2, (∀ ⦃T T' : C⦄ (φ : T ⟶ T'), η T' = pOm F 2 φ (η T)) ∧ ∀ t, η (G.obj t) = η' t) → (∀ (T : C) (x : Om R (F.obj T) 3), (∀ t (u : T ⟶ G.obj t), pOm F 3 u x = 0) → x = 0) → Function.Surjective (pullHyp2 (CoefMap.restrict F G)) := by
  intro R _ C _ C' _ F G hO hκ hl h2 he hs c'
  obtain ⟨c', rfl⟩ := Hyp2.mk_surjective _ c'
  obtain ⟨h0, hh⟩ := hO (H2.mk _ ⟨c'.1.1, (mem_cechDeRhamTotalCocyclesTwo_iff.1 c'.2).1⟩)
  obtain ⟨z, rfl⟩ := H2.mk_surjective F h0
  rw [CoefMap.pullCohomologyTwo_class, H2.mk_eq_mk] at hh
  obtain ⟨y', hy'⟩ := hh
  let z' : ∀ (t t' t'' : C') (_ : t ⟶ t') (_ : t' ⟶ t''), F.obj (G.obj t'') := c'.1.1
  let a' : ∀ (t t' : C') (_ : t ⟶ t'), Ω[F.obj (G.obj t')⁄R] := c'.1.2.1
  let η' : ∀ t : C', Om R (F.obj (G.obj t)) 2 := c'.1.2.2
  let y : ∀ (t t' : C') (_ : t ⟶ t'), F.obj (G.obj t') := y'
  have hz : ∀ ⦃t t' t'' : C'⦄ (a : t ⟶ t') (b : t' ⟶ t''), z.1 _ _ _ (G.map a) (G.map b) =
      z' t t' t'' a b + (mp F (G.map b) (y t t' a) - y t t'' (a ≫ b) + y t' t'' b) := by
    intro t t' t'' a b
    have e := congrFun (congrFun (congrFun (congrFun (congrFun hy' t) t') t'') a) b
    change mp F (G.map b) (y t t' a) - y t t'' (a ≫ b) + y t' t'' b =
      z.1 _ _ _ (G.map a) (G.map b) - z' t t' t'' a b at e
    rw [e]; ring
  let a2 : ∀ (t t' : C') (_ : t ⟶ t'), Ω[F.obj (G.obj t')⁄R] := fun t t' a ↦ a' t t' a - D R _ (y t t' a)
  have ha2 : ∀ ⦃t t' t'' : C'⦄ (a : t ⟶ t') (b : t' ⟶ t''), a2 t t'' (a ≫ b) =
      p1 F (G.map b) (a2 t t' a) + a2 t' t'' b + D R _ (z.1 _ _ _ (G.map a) (G.map b)) := by
    intro t t' t'' a b
    have e : a' t t'' (a ≫ b) = p1 F (G.map b) (a' t t' a) + a' t' t'' b +
      D R _ (z' t t' t'' a b) := cechDeRhamTotalCocyclesTwo.one c' a b
    simp only [a2]
    rw [e, hz, map_sub, p1_D]
    simp only [map_add, map_sub]
    abel

  obtain ⟨a₀, ha₀⟩ := hκ (fun T T' T'' φ ψ ↦ -D R _ (z.1 T T' T'' φ ψ)) (by
      intro T T' T'' T''' φ ψ χ
      have e := z.2 φ ψ χ
      simp only [p1_D, map_neg]
      rw [← neg_add, ← neg_add, ← map_add, ← map_add, e]) a2 (by
      intro t t' t'' a b
      beta_reduce
      rw [ha2]; abel)
  have ha₀' : ∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''),
      a₀ T T'' (φ ≫ ψ) = p1 F ψ (a₀ T T' φ) + a₀ T' T'' ψ + D R _ (z.1 T T' T'' φ ψ) := by
    intro T T' T'' φ ψ
    have e := ha₀ φ ψ
    beta_reduce at e
    linear_combination (norm := abel1) e
  obtain ⟨β, hβ, θ', hθ'⟩ := hl (fun t t' a ↦ a₀ _ _ (G.map a) - a2 t t' a) (by
      intro t t' t'' a b
      beta_reduce
      rw [G.map_comp, ha2, ha₀']
      simp only [a2, map_sub]
      abel)
  let a : A1 F := fun T T' φ ↦ a₀ T T' φ - β T T' φ
  have ha : ∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''),
      a T T'' (φ ≫ ψ) = p1 F ψ (a T T' φ) + a T' T'' ψ + D R _ (z.1 T T' T'' φ ψ) := by
    intro T T' T'' φ ψ
    simp only [a]
    rw [ha₀', hβ, map_sub]
    abel
  have haG : ∀ ⦃t t' : C'⦄ (b : t ⟶ t'), a _ _ (G.map b) =
      a2 t t' b - (θ' t' - p1 F (G.map b) (θ' t)) := by
    intro t t' b
    have e := hθ' b
    beta_reduce at e
    simp only [a]
    linear_combination (norm := abel1) -e
  let η3 : ∀ t : C', Om R (F.obj (G.obj t)) 2 := fun t ↦ η' t - dOne R _ (θ' t)
  have hη3 : ∀ ⦃t t' : C'⦄ (b : t ⟶ t'), dOne R _ (a _ _ (G.map b)) =
      η3 t' - pOm F 2 (G.map b) (η3 t) := by
    intro t t' b
    have e : η' t' = pOm F 2 (G.map b) (η' t) + dOne R _ (a' t t' b) := cechDeRhamTotalCocyclesTwo.two c' b
    simp only [η3]
    rw [haG, e]
    simp only [a2, map_sub, dOne_D, pOm_dOne]
    abel
  obtain ⟨η₀, hη₀⟩ := h2 (fun T T' φ ↦ dOne R _ (a T T' φ)) (by
      intro T T' T'' φ ψ
      beta_reduce
      rw [ha, map_add, map_add, dOne_D, pOm_dOne, add_zero]) η3 hη3
  obtain ⟨ε, hε, hεG⟩ := he (fun t ↦ η3 t - η₀ (G.obj t)) (by
      intro t t' b
      beta_reduce
      have e1 := hη3 b
      have e2 := hη₀ (G.map b)
      beta_reduce at e2
      rw [map_sub]
      linear_combination (norm := abel1) e2 - e1)
  let η : W0 F 2 := fun T ↦ η₀ T + ε T
  have hη : ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), η T' = pOm F 2 φ (η T) + dOne R _ (a T T' φ) := by
    intro T T' φ
    have e := hη₀ φ
    beta_reduce at e
    simp only [η]
    rw [hε φ, e, map_add]
    abel
  have hηG : ∀ t, η (G.obj t) = η3 t := by
    intro t
    simp only [η]
    rw [hεG t]
    abel
  have hclosed : ∀ T, dTwo R _ (η T) = 0 := by
    intro T
    refine hs T _ fun t u ↦ ?_
    have e : pOm F 2 u (η T) = η3 t - dOne R _ (a _ _ u) := by
      rw [← hηG, hη u]; abel
    have e3 : dTwo R _ (η' t) = 0 := cechDeRhamTotalCocyclesTwo.closed c' t
    rw [pOm_dTwo, e]
    simp only [η3, map_sub, dTwo_dOne, e3, sub_zero]
  let c : cechDeRhamTotalCocyclesTwo F := ⟨(z.1, a, η), mem_cechDeRhamTotalCocyclesTwo_iff.2 ⟨z.2, ha, hη, hclosed⟩⟩
  refine ⟨Hyp2.mk F c, ?_⟩
  rw [pullHyp2_mk, Hyp2.mk_eq_mk]
  refine ⟨(y, fun t ↦ -θ' t), Tot2.ext (fun t t' t'' b b' ↦ ?_) (fun t t' b ↦ ?_) fun t ↦ ?_⟩
  · change mp F (G.map b') (y t t' b) - y t t'' (b ≫ b') + y t' t'' b' =
      z.1 _ _ _ (G.map b) (G.map b') - z' t t' t'' b b'
    rw [hz]; ring
  · change -θ' t' - p1 F (G.map b) (-θ' t) - D R _ (y t t' b) =
      q1 (CoefMap.restrict F G) t' (a _ _ (G.map b)) - c'.1.2.1 t t' b
    have e4 : q1 (CoefMap.restrict F G) t' (a _ _ (G.map b)) =
        a2 t t' b - (θ' t' - p1 F (G.map b) (θ' t)) := (cechDeRhamCoefMapOneForms_restrictAlongFunctor F G t' _).trans (haG b)
    rw [e4]
    change -θ' t' - p1 F (G.map b) (-θ' t) - D R _ (y t t' b) =
      a2 t t' b - (θ' t' - p1 F (G.map b) (θ' t)) - a' t t' b
    simp only [a2, map_neg]
    abel
  · change dOne R _ (-θ' t) = qOm (CoefMap.restrict F G) 2 t (η (G.obj t)) - c'.1.2.2 t
    have e5 : qOm (CoefMap.restrict F G) 2 t (η (G.obj t)) = η3 t :=
      (qOm_restrict F G t _).trans (hηG t)
    rw [e5]
    change dOne R _ (-θ' t) = η3 t - η' t
    simp only [η3, map_neg]
    abel

end GlobalTheory.CechDR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatibleHigherFormsExtendAlongFunctor
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

namespace GlobalTheory

theorem compat_forms_extend : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), ∀ (j : ℕ), (∀ (T : C) (x : (FormExtJ.omjExt F j).obj T), (∀ t (u : T ⟶ G.obj t), mp (FormExtJ.omjExt F j) u x = 0) → x = 0) → (∀ (T : C) (s : ∀ t, (T ⟶ G.obj t) → (FormExtJ.omjExt F j).obj (G.obj t)), (∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), s t' (u ≫ G.map a) = mp (FormExtJ.omjExt F j) (G.map a) (s t u)) → ∃ x : (FormExtJ.omjExt F j).obj T, ∀ t u, mp (FormExtJ.omjExt F j) u x = s t u) → (∀ η' : ∀ t, Om R (F.obj (G.obj t)) j, (∀ ⦃t t' : C'⦄ (a : t ⟶ t'), η' t' = pOm F j (G.map a) (η' t)) → ∃ η : W0 F j, (∀ ⦃T T' : C⦄ (φ : T ⟶ T'), η T' = pOm F j φ (η T)) ∧ ∀ t, η (G.obj t) = η' t) := by
  intro R _ C _ C' _ F G j hsep hglue η' hη'
  obtain ⟨g, hg, hgG⟩ := compat_family_extend (FormExtJ.omjExt F j) G hsep hglue
    (fun t ↦ (TrivSqZeroExt.inr (η' t) : (FormExtJ.omjExt F j).obj (G.obj t)))
    (fun t t' a ↦ by rw [FormExtJ.mp_omjExt_inr, ← hη' a])
  refine ⟨fun T ↦ (g T).snd, fun T T' φ ↦ ?_, fun t ↦ ?_⟩
  · show (g T').snd = pOm F j φ (g T).snd
    rw [hg φ, FormExtJ.snd_mp_omjExt]
  · show (g (G.obj t)).snd = η' t
    rw [hgG t]
    rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovBy
section
set_option autoImplicit false

noncomputable section

open CategoryTheory GlobalTheory.CatCoh

namespace GlobalTheory.CatCoh.Desc.VandermondeTwoBasis

def CovBy {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
    (Φ : C → Prop) (S : C) : Prop :=
  ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧
    ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → Φ S'

theorem CovBy.mono {R : Type} [CommRing R] {C : Type} [Category.{0} C] {F : C ⥤ CommAlgCat.{0} R}
    {Φ Ψ : C → Prop} (h : ∀ S, Φ S → Ψ S) {S : C} (hS : CovBy F Φ S) : CovBy F Ψ S := by
  obtain ⟨n, b, hb, hc⟩ := hS
  exact ⟨n, b, hb, fun i S' u hu ↦ h _ (hc i S' u hu)⟩

end GlobalTheory.CatCoh.Desc.VandermondeTwoBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupProductAssocOfPairingAssocStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cupProduct_assoc_of_pairing_assoc : ∀ (R : Type) [CommRing R] {I J K M M' L : Cx R} (μ : Pair I J M) (ν : Pair M K L) (μ' : Pair J K M') (ν' : Pair I M' L), (∀ (U : Scheme.{0}) (s t u st tu w : ℤ) (h1 : s + t = st) (h2 : st + u = w) (h3 : t + u = tu) (h4 : s + tu = w) a b c, ν.mul U st u w h2 (μ.mul U s t st h1 a b) c = ν'.mul U s tu w h4 a (μ'.mul U t u tu h3 b c)) → ∀ (E : Spc) {n m k nm mk w : ℤ} (h1 : n + m = nm) (h2 : nm + k = w) (h3 : m + k = mk) (h4 : n + mk = w) a b c, ν.cup E h2 (μ.cup E h1 a b) c = ν'.cup E h4 a (μ'.cup E h3 b c) := by
  first | exact @GlobalTheory.EtC.Pair.cup_assoc_of_mul_assoc | exact GlobalTheory.EtC.Pair.cup_assoc_of_mul_assoc | (intros; apply GlobalTheory.EtC.Pair.cup_assoc_of_mul_assoc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupProductNaturalInSheafComplexPairingStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cupProduct_natural_in_sheafComplexPairing : ∀ (R : Type) [CommRing R] {I J K I' J' K' : Cx R} (μ : Pair I J K) (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J') (u : K ⟶ K'), μ.Compat ν f g u → ∀ (E : Spc) {n m k : ℤ} (hk : n + m = k) a b, cpush _ u k (μ.cup E hk a b) = ν.cup E hk (cpush _ f n a) (cpush _ g m b) := by
  first | (exact @GlobalTheory.cup_natural_in_pairing) | (exact GlobalTheory.cup_natural_in_pairing) | (intros; apply GlobalTheory.cup_natural_in_pairing  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterGLFiniteFieldFrobeniusPowStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidalCharacterGLFiniteField_frobenius_pow : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (t : F ≃+* F) (j : ℕ), (∀ x, t x = x ^ (ringChar F ^ j)) → ∀ (m k : ℕ) (x : GL (Fin m) F), cusp θ m k (gal (t : F →+* F) m x) = cusp θ m (k * ringChar F ^ j) x := by
  first | (exact @GlobalTheory.Shin.cusp_gal) | (exact GlobalTheory.Shin.cusp_gal) | (intros; apply GlobalTheory.Shin.cusp_gal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentialOperatorDepthIntegralCoordinatesStatement
section
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.differentialOperatorDepth_integral_coordinates : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (i d c : ℕ) (G : LogFGL v d) (u : Fin i → Fin d → C) (Φ Ψ : Fin d → MvPowerSeries (Fin d) C), (∀ a, MvIsInt v (Φ a) ∧ constantCoeff (Φ a) = 0 ∧ MvIsInt v (Ψ a) ∧ constantCoeff (Ψ a) = 0) → (∀ a, subst Ψ (Φ a) = X a ∧ subst Φ (Ψ a) = X a) → ∀ (t : Fin d → MvPowerSeries (Fin i) C), (∀ a, constantCoeff (t a) = 0) → (∀ e, subst t (subst Φ (G.lg e)) = ∑ a, u a e • X a) → detDepth G u c = ⨅ f : {f : MvPowerSeries (Σ _ : Fin i, Fin d) C // MvIsInt v f}, toE (v (derivAt0 (detPow C i c) (subst (fun x : (Σ _ : Fin i, Fin d) => subst (fun a : Fin i => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C)) (t x.2)) f.1))) := by
  first | exact @GlobalTheory.FGDepth.Coord.depth_in_coords | exact GlobalTheory.FGDepth.Coord.depth_in_coords | (intros; apply GlobalTheory.FGDepth.Coord.depth_in_coords <;> assumption)
end

