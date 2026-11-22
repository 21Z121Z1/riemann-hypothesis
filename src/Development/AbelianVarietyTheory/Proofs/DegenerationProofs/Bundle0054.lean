import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsEEOfSpanWeightSpaces
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem ThetaSys.FF_mem_ring (S : ThetaSys o Ω) (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N)
    (k : S.J × (T → ZMod ((S.r * S.N) ^ 2))) : S.FF T c k ∈ S.R := by
  unfold ThetaSys.FF
  refine finsum_induction (· ∈ S.R) (zero_mem _) (fun _ _ => add_mem) fun t => ?_
  exact mul_mem (S.R.algebraMap_mem _)
    (sum_mem fun j _ => mul_mem (S.R.algebraMap_mem _) (S.ev_mem _ _))

theorem RatModel.span_val_span {M : RatModel o Ω} {J : Type} {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ M.Z}
    {z : M.Z} (h : y (cPt p) = z) (w : Sp (PadicAlgCl p)) (G : Set (J → Ω))
    (hG : ∀ v ∈ G, ∀ j, v j ∈ M.O ((gPt p ≫ y) w)) :
    Submodule.span (OO p) ((fun (v : J → Ω) j => M.val (gPt p ≫ y) (v j)) '' (Submodule.span (M.O z) G)) =
      Submodule.span (OO p) ((fun (v : J → Ω) j => M.val (gPt p ≫ y) (v j)) '' G) := by
  have hs : ∀ w', (gPt p ≫ y) w' ⤳ (gPt p ≫ y) w :=
    RatModel.specializes_of_range_eq (RatModel.range_eq_singleton _ w)
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono (Set.image_mono Submodule.subset_span))
  rintro _ ⟨v, hv, rfl⟩
  suffices H : (∀ j, v j ∈ M.O ((gPt p ≫ y) w)) ∧ (fun j => M.val (gPt p ≫ y) (v j)) ∈
      Submodule.span (OO p) ((fun (v : J → Ω) j => M.val (gPt p ≫ y) (v j)) '' G) from H.2
  induction hv using Submodule.span_induction with
  | mem v hv => exact ⟨hG v hv, Submodule.subset_span ⟨v, hv, rfl⟩⟩
  | zero =>
    refine ⟨fun j => zero_mem _, ?_⟩
    have : (fun j => M.val (gPt p ≫ y) ((0 : J → Ω) j)) = 0 := funext fun j => RatModel.val_zero _
    rw [this]
    exact zero_mem _
  | add u v _ _ hu hv =>
    refine ⟨fun j => add_mem (hu.1 j) (hv.1 j), ?_⟩
    have : (fun j => M.val (gPt p ≫ y) ((u + v) j)) =
        (fun j => M.val (gPt p ≫ y) (u j)) + fun j => M.val (gPt p ≫ y) (v j) :=
      funext fun j => RatModel.val_add hs (hu.1 j) (hv.1 j)
    rw [this]
    exact add_mem hu.2 hv.2
  | smul a v _ hv =>
    have ha : (a : Ω) ∈ M.O ((gPt p ≫ y) w) := RatModel.O_le_of_specializes (RatModel.gPt_specializes h w) a.2
    refine ⟨fun j => mul_mem ha (hv.1 j), ?_⟩
    have : (fun j => M.val (gPt p ≫ y) ((a • v) j)) =
        (⟨M.val (gPt p ≫ y) a, (mem_OO_iff _).2 (RatModel.norm_val_le_one h a.2)⟩ : OO p) •
          fun j => M.val (gPt p ≫ y) (v j) :=
      funext fun j => RatModel.val_mul hs ha (hv.1 j)
    rw [this]
    exact Submodule.smul_mem _ _ hv.2

theorem RatModel.val_div_mul {M : RatModel o Ω} {K : Type} [Field K] {y : Sp K ⟶ M.Z} {z : M.Z}
    (h : ∀ w, y w ⤳ z) {a b c : Ω} (ha : a ∈ M.O z) (hb : b ∈ M.O z) (hb0 : b ≠ 0) (hb' : b⁻¹ ∈ M.O z)
    (hc : c ∈ M.O z) : M.val y (a / b * c) = M.val y a / M.val y b * M.val y c := by
  have h1 : M.val y b⁻¹ = (M.val y b)⁻¹ := by
    refine eq_inv_of_mul_eq_one_right ?_
    rw [← RatModel.val_mul h hb hb', mul_inv_cancel₀ hb0, RatModel.val_one]
  rw [div_eq_mul_inv, RatModel.val_mul h (mul_mem ha hb') hc, RatModel.val_mul h ha hb', h1, div_eq_mul_inv]

theorem ThetaSys.span_val_eq_testLattice (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens)
    (hA : S.admitted M U₀) {z : M.Z} {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ M.Z} {y₀ : S.R →+* PadicAlgCl p}
    (τ : S.Test p y₀) (hC : M.Cen U₀ z y) (hAt : S.At M y y₀)
    (hI : ∀ x ∈ S.supI M z, ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ)
    (T : AddSubgroup S.Gam) (hT : T = S.perp τ.yy.ker) (hF : ∀ c : T →+ ZMod S.N, S.FF T c ≠ 0)
    (hα : ∀ c : S.perp τ.yy.ker →+ ZMod S.N, ∃ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) ∧ τ.wt α = c)
    (hv : ∀ (c : T →+ ZMod S.N) (k : _) (α : τ.X), M.Div (S.FF T c) k z → (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) →
      (∀ (t : S.Gam) (h₁ : t ∈ T) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) →
      ‖M.val (gPt p ≫ y) (S.FF T c k)‖ = τ.δ * Real.exp (-(τ.q α / S.N))) :
    Submodule.span (OO p) ((fun (v : S.J → Ω) j => M.val (gPt p ≫ y) (v j)) '' (Submodule.span (M.O z)
      {v | ∃ (c : T →+ ZMod S.N) (k : _) (x₀ : S.Gam) (i : S.J), M.Div (S.FF T c) k z ∧ x₀ ∈ S.supI M z ∧
        v = fun j => S.th x₀ / S.FF _ c k * algebraMap o Ω (S.proj _ c j i)})) = τ.E := by
  subst hT
  let w : Sp (PadicAlgCl p) := IsLocalRing.closedPoint (PadicAlgCl p)
  have hw : (gPt p ≫ y) w ∈ (U₀ : Set M.Z) := hC.2 ⟨w, rfl⟩
  have hs : ∀ w', (gPt p ≫ y) w' ⤳ (gPt p ≫ y) w :=
    RatModel.specializes_of_range_eq (RatModel.range_eq_singleton _ w)
  have hR : S.R ≤ M.O ((gPt p ≫ y) w) := hA.1.le.trans (RatModel.ringOn_le_O hw)
  have hinv : ∀ c k, M.Div (S.FF (S.perp τ.yy.ker) c) k z → (S.FF _ c k)⁻¹ ∈ M.O ((gPt p ≫ y) w) :=
    fun c k hk => RatModel.ringOn_le_O hw (hA.1.FF_unit _ c k τ.isoFree hk.1)
  have hval : ∀ c k x₀ i, M.Div (S.FF (S.perp τ.yy.ker) c) k z →
      (fun j => M.val (gPt p ≫ y) (S.th x₀ / S.FF _ c k * algebraMap o Ω (S.proj _ c j i))) =
      fun j => M.val (gPt p ≫ y) (S.th x₀) / M.val (gPt p ≫ y) (S.FF _ c k) *
        y₀ (algebraMap o S.R (S.proj _ c j i)) := by
    intro c k x₀ i hk
    funext j
    rw [RatModel.val_div_mul hs (hR (S.th_mem _)) (hR (S.FF_mem_ring _ _ _)) hk.1 (hinv c k hk)
      (Subalgebra.algebraMap_mem _ _), hAt]
    rfl
  have hnorm : ∀ α k x₀, M.Div (S.FF (S.perp τ.yy.ker) (τ.wt α)) k z → x₀ ∈ S.supI M z →
      (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) →
      ‖M.val (gPt p ≫ y) (S.th x₀) / M.val (gPt p ≫ y) (S.FF _ (τ.wt α) k)‖ = Real.exp (τ.q α / S.N) := by
    intro α k x₀ hk hx hm
    rw [norm_div, hI x₀ hx, hv _ k α hk hm fun _ _ _ => rfl, Real.exp_neg]
    have := τ.δ_pos.ne'
    have := (Real.exp_pos (τ.q α / S.N)).ne'
    field_simp
  rw [RatModel.span_val_span hC.1 w]
  · refine le_antisymm (Submodule.span_mono ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨_, ⟨c, k, x₀, i, hk, hx, rfl⟩, rfl⟩
      obtain ⟨α, hm, rfl⟩ := hα c
      exact ⟨α, _, i, hm, (hnorm α k x₀ hk hx hm).le, hval _ k x₀ i hk⟩
    · rintro _ ⟨α, l, i, hm, hl, rfl⟩
      obtain ⟨k, hk⟩ := hA.2 _ (τ.wt α) τ.isoFree (hF _) z
      obtain ⟨x₀, hx⟩ := hA.1.div z
      have hn := hnorm α k x₀ hk hx hm
      have hv' := hval _ k x₀ i hk
      generalize M.val (gPt p ≫ y) (S.th x₀) / M.val (gPt p ≫ y) (S.FF _ (τ.wt α) k) = l₀ at hn hv'
      have hpos : 0 < ‖l₀‖ := hn ▸ Real.exp_pos _
      have h0 : l₀ ≠ 0 := norm_pos_iff.1 hpos
      have hq : l / l₀ ∈ OO p := by
        rw [mem_OO_iff, norm_div, div_le_one hpos, hn]
        exact hl
      have : (fun j => l * y₀ (algebraMap o S.R (S.proj _ (τ.wt α) j i))) =
          (⟨l / l₀, hq⟩ : OO p) • fun j => l₀ * y₀ (algebraMap o S.R (S.proj _ (τ.wt α) j i)) := by
        funext j
        show _ = l / l₀ * (l₀ * _)
        rw [← _root_.mul_assoc, div_mul_cancel₀ _ h0]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨_, k, x₀, i, hk, hx, rfl⟩, hv'⟩)
  · rintro _ ⟨c, k, x₀, i, hk, -, rfl⟩ j
    rw [div_eq_mul_inv]
    exact mul_mem (mul_mem (hR (S.th_mem _)) (hinv c k hk)) (Subalgebra.algebraMap_mem _ _)

theorem isEE_of_span_weightSpaces : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.admitted M U₀ → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → (∀ x, x ∈ S.supI M z ↔ ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ) ∧ S.HH M z = τ.yy.ker) → ((∀ ξ : M.Z, S.IsoFree (S.TT M ξ) ∧ S.perp (S.TT M ξ) = S.HH M ξ) ∧ (∀ ξ z : M.Z, ξ ⤳ z → S.supI M z ⊆ S.supI M ξ) ∧ (∀ ξ ∈ U₀, S.TT M ξ = ⊥) ∧ (∀ (ξ : M.Z) (W : M.Z.Opens), ξ ∈ W → ∃ x ∈ W, IsClosed ({x} : Set M.Z) ∧ ξ ⤳ x ∧ S.supI M x = S.supI M ξ)) → (∀ (ξ : M.Z) (c : S.TT M ξ →+ ZMod S.N), S.FF (S.TT M ξ) c ≠ 0) → (∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ c : S.perp τ.yy.ker →+ ZMod S.N, ∃ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) ∧ τ.wt α = c) ∧ ∀ (T : AddSubgroup S.Gam), S.IsoFree T → T ≤ S.perp τ.yy.ker → ∀ (w : S.Gam → τ.X), (∀ x, τ.yy x = QuotientAddGroup.mk (w x)) → ∀ (I : Set S.Gam), AddSubgroup.closure I = S.perp T → ∀ α : τ.X, (∀ (t : S.Gam) (h₂ : t ∈ S.perp τ.yy.ker), t ∈ T → τ.wt α ⟨t, h₂⟩ = 0) ↔ α ∈ AddSubgroup.closure (w '' I ∪ Set.range fun v₀ : τ.X => S.N • v₀)) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → ∀ (c : S.TT M z →+ ZMod S.N) (k : _) (α : τ.X), M.Div (S.FF (S.TT M z) c) k z → (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) → (∀ (t : S.Gam) (h₁ : t ∈ S.TT M z) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) → ‖M.val (gPt p ≫ y) (S.FF (S.TT M z) c k)‖ = τ.δ * Real.exp (-(τ.q α / S.N))) → (∀ z : M.Z, IsClosed ({z} : Set M.Z) → EE.E z = Submodule.span (M.O z) {v | ∃ (c : S.TT M z →+ ZMod S.N) (k : _) (x₀ : S.Gam) (i : S.J), M.Div (S.FF (S.TT M z) c) k z ∧ x₀ ∈ S.supI M z ∧ v = fun j => S.th x₀ / S.FF _ c k * algebraMap o Ω (S.proj _ c j i)}) → (∀ z ∈ U₀, EE.E z = Submodule.span (M.O z) (Set.range fun i => Pi.single i (1 : Ω))) → S.IsEE M U₀ EE := by
  intro o Ω _ _ _ hb S M U₀ EE hA h0 _ hF hα hv hE hU
  refine ⟨hU, fun z p _ y y₀ τ hC hAt => ?_⟩
  rw [hE z (hC.1 ▸ isClosed_singleton_cPt y)]
  obtain ⟨hI, hH⟩ := h0 z p y y₀ τ hC hAt
  exact S.span_val_eq_testLattice M U₀ hA τ hC hAt (fun x hx => (hI x).1 hx) _ (congrArg S.perp hH) (hF z)
    (hα p y₀ τ).1 (hv z p y y₀ τ hC hAt)

end GlobalTheory.ZH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsIsoMorphismRestrictOfLocalDominantSections
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

noncomputable section
namespace GlobalTheory.ZH

open GlobalTheory.Points

theorem isIso_pullback_snd_of_dominant_section {X Y V : Scheme.{0}} (f : X ⟶ Y) [IsSeparated f] [IsReduced X]
    (q : V ⟶ Y) [IsOpenImmersion q] (g : V ⟶ X) [IsDominant g] (h : g ≫ f = q) : IsIso (pullback.snd f q) := by
  let σ : V ⟶ pullback f q := pullback.lift g (𝟙 V) (by rw [h, Category.id_comp])
  have e1 : σ ≫ pullback.fst f q = g := pullback.lift_fst _ _ _
  have e2 : σ ≫ pullback.snd f q = 𝟙 V := pullback.lift_snd _ _ _
  have : IsReduced (pullback f q) := isReduced_of_isOpenImmersion (pullback.fst f q)
  have : IsDominant (σ ≫ pullback.fst f q) := e1 ▸ inferInstance
  have : IsDominant σ := IsDominant.of_comp_of_isOpenImmersion σ (pullback.fst f q)
  refine ⟨σ, ?_, e2⟩
  refine ext_of_isDominant_of_isSeparated (pullback.snd f q) ?_ σ ?_
  · rw [Category.assoc, e2, Category.comp_id, Category.id_comp]
  · rw [← Category.assoc, e2, Category.id_comp, Category.comp_id]

theorem isIso_of_local_dominant_sections {X Y : Scheme.{0}} (f : X ⟶ Y) [IsSeparated f] [IsReduced X]
    (h : ∀ y : Y, ∃ (V : Scheme.{0}) (q : V ⟶ Y) (_ : IsOpenImmersion q) (g : V ⟶ X),
      y ∈ Set.range q ∧ IsDominant g ∧ g ≫ f = q) : IsIso f := by
  choose V q hq g hy hg e using h
  let 𝒰 : Y.OpenCover := Scheme.Cover.mkOfCovers Y V q fun y => ⟨y, hy y⟩
  exact IsZariskiLocalAtTarget.of_openCover (P := MorphismProperty.isomorphisms _) 𝒰 fun y =>
    haveI := hq y
    haveI := hg y
    isIso_pullback_snd_of_dominant_section f (q y) (g y) (e y)

theorem isIso_morphismRestrict_of_local_dominant_sections {X Y : Scheme.{0}} (f : X ⟶ Y) [IsSeparated f] [IsReduced X]
    (W : Y.Opens) (h : ∀ y ∈ W, ∃ (V : Scheme.{0}) (q : V ⟶ Y) (_ : IsOpenImmersion q) (g : V ⟶ X),
      y ∈ Set.range q ∧ Set.range q ⊆ W ∧ IsDominant g ∧ g ≫ f = q) : IsIso (f ∣_ W) := by
  have : IsSeparated (f ∣_ W) := IsZariskiLocalAtTarget.restrict (P := @IsSeparated) ‹_› W
  refine isIso_of_local_dominant_sections _ fun y => ?_
  obtain ⟨V, q, hq, g, ⟨v, hv⟩, hW, hg, e⟩ := h y.1 y.2
  have h1 : Set.range q ⊆ Set.range W.ι := by rwa [Scheme.Opens.range_ι]
  have h2 : Set.range g ⊆ Set.range (f ⁻¹ᵁ W).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    exact hW ⟨w, by rw [← e]; rfl⟩
  have e1 := IsOpenImmersion.lift_fac W.ι q h1
  have e2 := IsOpenImmersion.lift_fac (f ⁻¹ᵁ W).ι g h2
  have : IsOpenImmersion (IsOpenImmersion.lift W.ι q h1 ≫ W.ι) := e1.symm ▸ hq
  have : IsDominant (IsOpenImmersion.lift (f ⁻¹ᵁ W).ι g h2 ≫ (f ⁻¹ᵁ W).ι) := e2.symm ▸ hg
  refine ⟨V, IsOpenImmersion.lift W.ι q h1, IsOpenImmersion.of_comp _ W.ι, IsOpenImmersion.lift (f ⁻¹ᵁ W).ι g h2,
    ⟨v, ?_⟩, IsDominant.of_comp_of_isOpenImmersion _ (f ⁻¹ᵁ W).ι, ?_⟩
  · refine Subtype.ext ?_
    rw [← hv]
    conv_rhs => rw [← e1]
    rfl
  · rw [← cancel_mono W.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, e2, e, e1]

namespace RatModel

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M M' : RatModel o Ω}

theorem IsNm.isIso_morphismRestrict {J : Type} [Finite J] {u : J → Ω} (h' : M'.IsNm u)
    (hn : ∀ z, IsIntegrallyClosed (M.O z)) {f : M'.Z ⟶ M.Z} (hf : M.IsHom M' (AlgHom.id o Ω) f) (W : M.Z.Opens)
    (hW : ∀ z ∈ W, ∃ i, M.Div u i z) : IsIso (f ∣_ W) := by
  have := M.sep
  have : IsSeparated (f ≫ M.s) := hf.inducedModelMorphism_comp_structureMap.symm ▸ M'.sep
  have : IsSeparated f := IsSeparated.of_comp f M.s
  refine isIso_morphismRestrict_of_local_dominant_sections f W fun z hz => ?_
  obtain ⟨i, hi⟩ := hW z hz
  obtain ⟨U, hU, hD, hR⟩ := h'.2 i hi.1
  obtain ⟨V, hV, hzV, hle⟩ :=
    exists_isAffineOpen_mem_and_subset (U := W ⊓ ⟨_, M.isOpen_setOf_div u i⟩) (x := z) ⟨hz, hi⟩
  obtain ⟨g, hg⟩ := exists_hom_of_map_ringOn (φ := AlgHom.id o Ω) hU
    ⟨genericPoint M'.Z, hD ▸ div_genericPoint hi.1⟩ (V := V) ⟨z, hzV⟩
    fun x hx => mem_ringOn.2 fun w hw =>
      Div.map_mem_O_of_isIntegral (M' := M) (φ := AlgHom.id o Ω) (t := u) (i := i) (z := w) (hle hw).2 ((hR x).1 hx)
  have hp := specMap_valMap_fromSpec hV M.pt (M.top_le_preimage_pt ⟨z, hzV⟩)
  have hid : ∀ {Y : Scheme.{0}} (a : Sp Ω ⟶ Y), spMap (AlgHom.id o Ω).toRingHom ≫ a = a := fun a =>
    (congrArg (· ≫ a) (Spec.map_id _)).trans (Category.id_comp _)
  have hdom : IsDominant (Spec.map (valMap M.pt V (M.top_le_preimage_pt ⟨z, hzV⟩)) ≫ g) := by
    rw [hg, hid]
    infer_instance
  refine ⟨_, hV.fromSpec, inferInstance, g, hV.range_fromSpec ▸ hzV, hV.range_fromSpec ▸ fun w hw => (hle hw).1,
    IsDominant.of_comp (Spec.map (valMap M.pt V (M.top_le_preimage_pt ⟨z, hzV⟩))) g, ?_⟩
  refine hom_ext_of_isOpenImmersion (φ := AlgHom.id o Ω) hV.fromSpec hp ?_ (hp.trans (hid _).symm)
  rw [← Category.assoc, hg, hid]
  exact hf

end RatModel

theorem isIso_morphismRestrict_of_isNm_prod : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (M' : RatModel o Ω) (J J' : Type) [Finite J] [Finite J'] (t : J → Ω) (t' : J' → Ω) (f : M'.Z ⟶ M.Z), M.IsNm t → M'.IsNm (fun q : J × J' => t q.1 * t' q.2) → IsProper M'.s → M.IsHom M' (AlgHom.id o Ω) f → ∀ W : M.Z.Opens, (∀ z ∈ W, ∃ i', M.Div t' i' z) → IsIso (f ∣_ W) := by
  intro o Ω _ _ _ M M' J J' _ _ t t' f h h' _ hf W hW
  refine h'.isIso_morphismRestrict (RatModel.isIntegrallyClosed_O h.isNormalScheme) hf W fun z hz => ?_
  obtain ⟨i, hi⟩ := h.1 z
  obtain ⟨i', hi'⟩ := hW z hz
  exact ⟨(i, i'), RatModel.div_prod_iff.2 ⟨hi, hi'⟩⟩

end GlobalTheory.ZH
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KbIsAlgClosedAndConj
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ

open IsLocalRing Polynomial

variable {p : ℕ} [Fact p.Prime]

theorem splits_of_monic_OO {q : (OO p)[X]} (hq : q.Monic) : q.Splits := by
  refine Splits.of_splits_map_of_injective (i := (OO p).subtype) Subtype.val_injective
    (IsAlgClosed.splits _) fun a ha => ?_
  have h : IsIntegral (OO p) a := ⟨q, hq, by
    have := isRoot_of_mem_roots ha
    rwa [IsRoot, Polynomial.eval_map] at this⟩
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  exact ⟨y, hy⟩

theorem exists_root_residue_OO {q : (OO p)[X]} (hq : q.Monic) {b : kb p}
    (hb : q.eval₂ (residue (OO p)) b = 0) : ∃ a : OO p, q.eval a = 0 ∧ residue (OO p) a = b := by
  have h0 : q.map (residue (OO p)) ≠ 0 := (hq.map _).ne_zero
  have h : b ∈ (q.map (residue (OO p))).roots := by
    rw [mem_roots h0, IsRoot, Polynomial.eval_map, hb]
  rw [(splits_of_monic_OO hq).roots_map_of_ne_zero h0, Multiset.mem_map] at h
  obtain ⟨a, ha, rfl⟩ := h
  exact ⟨a, isRoot_of_mem_roots ha, rfl⟩

theorem isAlgClosed_kb : IsAlgClosed (kb p) := by
  refine IsAlgClosed.of_exists_root _ fun f hf hirr => ?_
  obtain ⟨q, hq, -, hmon⟩ := lifts_and_degree_eq_and_monic
    (mem_lifts_of_surjective (residue_surjective (R := OO p)) f) hf
  have hs : f.Splits := hq ▸ (splits_of_monic_OO hmon).map _
  exact hs.exists_eval_eq_zero (degree_pos_of_irreducible hirr).ne'

theorem charP_kb : CharP (kb p) p :=
  (CharP.charP_iff_prime_eq_zero Fact.out).2 GlobalTheory.ZH.natCast_residueField_OO

theorem exists_pow_eq_one_kb (x : kb p) (hx : x ≠ 0) : ∃ n : ℕ, 1 ≤ n ∧ x ^ n = 1 := by
  haveI := charP_kb (p := p)
  letI := ZMod.algebra (kb p) p
  have h : (algebraMap (ZMod p) (kb p)).IsIntegral := by
    refine RingHom.IsIntegral.tower_top (Int.castRingHom (ZMod p)) _ ?_
    rw [RingHom.ext_int (RingHom.comp _ _) (Int.castRingHom _)]
    exact GlobalTheory.ZH.isIntegral_int_residueField_OO
  have h' : IsIntegral (ZMod p) x := h x
  let K := IntermediateField.adjoin (ZMod p) {x}
  haveI : FiniteDimensional (ZMod p) K := IntermediateField.adjoin.finiteDimensional h'
  haveI : Finite K := Module.finite_of_finite (ZMod p)
  let y : K := ⟨x, IntermediateField.mem_adjoin_simple_self _ x⟩
  have hy : y ≠ 0 := fun h0 => hx (congrArg Subtype.val h0)
  obtain ⟨n, hn, e⟩ := (isOfFinOrder_of_finite (Units.mk0 y hy)).exists_pow_eq_one
  exact ⟨n, hn, by simpa [y] using congrArg (fun u : Kˣ => ((u : K) : kb p)) e⟩

theorem algEquiv_mem_OO (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) {x : PadicAlgCl p} (hx : x ∈ OO p) :
    σ x ∈ OO p := by
  rw [GlobalTheory.ZH.mem_OO_iff, ← GlobalTheory.isIntegral_padicInt_iff_norm_le_one] at hx ⊢
  exact hx.map (σ.toAlgHom.restrictScalars ℤ_[p])

noncomputable def restrictOO (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) : OO p ≃+* OO p where
  toFun x := ⟨σ x, algEquiv_mem_OO σ x.2⟩
  invFun x := ⟨σ.symm x, algEquiv_mem_OO σ.symm x.2⟩
  left_inv x := Subtype.ext (σ.symm_apply_apply x)
  right_inv x := Subtype.ext (σ.apply_symm_apply x)
  map_mul' x y := Subtype.ext (map_mul σ (x : PadicAlgCl p) y)
  map_add' x y := Subtype.ext (map_add σ (x : PadicAlgCl p) y)

theorem exists_int_map_eq_kb (q : ℤ_[p][X]) : ∃ g : ℤ[X], g.map (Int.castRingHom (kb p)) =
    q.map ((residue (OO p)).comp (GlobalTheory.ZH.padicIntToOO p)) := by
  rw [← mem_lifts, lifts_iff_coeff_lifts]
  intro n
  rw [coeff_map]
  have h1 := PadicInt.sub_zmodRepr_mem (q.coeff n)
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at h1
  obtain ⟨c, hc⟩ := h1
  have h2 := congrArg ((residue (OO p)).comp (GlobalTheory.ZH.padicIntToOO p)) hc
  rw [map_sub, map_mul, map_natCast, map_natCast, GlobalTheory.ZH.natCast_residueField_OO, zero_mul, sub_eq_zero] at h2
  exact ⟨((q.coeff n).zmodRepr : ℤ), by rw [h2]; simp⟩

theorem exists_residue_restrictOO_eq (a : OO p) (b' : kb p)
    (h : ∀ g : ℤ[X], aeval (residue (OO p) a) g = 0 → aeval b' g = 0) :
    ∃ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, residue (OO p) (restrictOO σ a) = b' := by
  have ha : IsIntegral ℤ_[p] (a : PadicAlgCl p) :=
    (GlobalTheory.isIntegral_padicInt_iff_norm_le_one _).2 ((GlobalTheory.ZH.mem_OO_iff _).1 a.2)
  set f := minpoly ℤ_[p] (a : PadicAlgCl p) with hf
  have key : ∀ c : OO p, (((f.map (GlobalTheory.ZH.padicIntToOO p)).eval c : OO p) : PadicAlgCl p) =
      aeval (c : PadicAlgCl p) f := fun c => by
    rw [Polynomial.eval_map]
    exact hom_eval₂ f (GlobalTheory.ZH.padicIntToOO p) (OO p).subtype c
  obtain ⟨g, hg⟩ := exists_int_map_eq_kb f
  have e : ∀ b : kb p, aeval b g = (f.map (GlobalTheory.ZH.padicIntToOO p)).eval₂ (residue (OO p)) b := fun b => by
    rw [eval₂_map, ← Polynomial.eval_map, ← hg, Polynomial.eval_map]
    rfl
  have h1 : aeval (residue (OO p) a) g = 0 := by
    have : (f.map (GlobalTheory.ZH.padicIntToOO p)).eval a = 0 := Subtype.ext ((key a).trans (minpoly.aeval _ _))
    rw [e, eval₂_hom, this, map_zero]
  obtain ⟨a', ha', rfl⟩ := exists_root_residue_OO ((minpoly.monic ha).map (GlobalTheory.ZH.padicIntToOO p))
    ((e b').symm.trans (h g h1))
  have h2 : aeval (a' : PadicAlgCl p) (minpoly ℚ_[p] (a : PadicAlgCl p)) = 0 := by
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[p] ha, aeval_map_algebraMap, ← hf, ← key, ha']
    rfl
  obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root' (Algebra.IsAlgebraic.isAlgebraic _) h2
  exact ⟨σ, congrArg _ (Subtype.ext hσ)⟩

theorem exists_ringEquiv_residue_eq (F : Type) [Field F] [Finite F] (r r' : F →+* kb p) :
    ∃ σ : OO p ≃+* OO p, ∀ (x : F) (a : OO p), residue (OO p) a = r x → residue (OO p) (σ a) = r' x := by
  obtain ⟨u, hu⟩ := IsCyclic.exists_monoid_generator (α := Fˣ)
  obtain ⟨a₀, ha₀⟩ := residue_surjective (r u)
  obtain ⟨σ, hσ⟩ := exists_residue_restrictOO_eq a₀ (r' u) fun g hg => by
    rw [ha₀] at hg
    have h1 := aeval_algHom_apply r.toIntAlgHom (u : F) g
    have h2 := aeval_algHom_apply r'.toIntAlgHom (u : F) g
    have h3 : aeval (u : F) g = 0 := r.injective ((h1.symm.trans hg).trans (map_zero r).symm)
    exact h2.trans (by rw [h3, map_zero])
  refine ⟨restrictOO σ, fun x a ha => ?_⟩
  let τ := ResidueField.mapEquiv (restrictOO σ)
  have hτ : ∀ c : OO p, τ (residue (OO p) c) = residue (OO p) (restrictOO σ c) := fun c => rfl
  rw [← hτ, ha]
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  obtain ⟨n, hn⟩ := hu (Units.mk0 x hx)
  have hx' : x = (u : F) ^ n := by simpa using (congrArg Units.val hn).symm
  rw [hx', map_pow, map_pow, map_pow, ← ha₀, hτ, hσ]

theorem kb_isAlgClosed_and_conj : ∀ (p : ℕ) [Fact p.Prime], IsAlgClosed (kb p) ∧ (∀ x : kb p, x ≠ 0 → ∃ n : ℕ, 1 ≤ n ∧ x ^ n = 1) ∧ ∀ (F : Type) [Field F] [Finite F] (r r' : F →+* kb p), ∃ σ : OO p ≃+* OO p, ∀ (x : F) (a : OO p), IsLocalRing.residue (OO p) a = r x → IsLocalRing.residue (OO p) (σ a) = r' x :=
  fun _ _ => ⟨isAlgClosed_kb, exists_pow_eq_one_kb, exists_ringEquiv_residue_eq⟩

end GlobalTheory.ZJ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemSpanRowsIffCoordsMem
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

theorem mem_span_rows_iff_coords_mem {o Ω J : Type} [CommRing o] [Field Ω] [Algebra o Ω] [Fintype J]
    [DecidableEq J] (A : Subalgebra o Ω) {b : Matrix J J Ω} (hb : b.det ≠ 0) (u : J → Ω) :
    u ∈ Submodule.span A (Set.range b) ↔ ∀ i, Matrix.vecMul u b⁻¹ i ∈ A := by
  have hu : IsUnit b.det := isUnit_iff_ne_zero.2 hb
  have key : ∀ c : J → A, ∑ i, c i • b i = Matrix.vecMul (fun i => (c i : Ω)) b := by
    intro c
    ext j
    simp [Matrix.vecMul, dotProduct, Finset.sum_apply, Subalgebra.smul_def]
  refine (Submodule.mem_span_range_iff_exists_fun (v := fun i => b i) A).trans ?_
  constructor
  · rintro ⟨c, rfl⟩ i
    rw [key, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hu, Matrix.vecMul_one]
    exact (c i).2
  · intro h
    refine ⟨fun i => ⟨_, h i⟩, ?_⟩
    rw [key]
    show Matrix.vecMul (Matrix.vecMul u b⁻¹) b = u
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hu, Matrix.vecMul_one]

theorem RatModel.val_vecMul_eq_sum {o Ω J K : Type} [CommRing o] [Field Ω] [Algebra o Ω] [Fintype J] [Field K]
    {M : RatModel o Ω} {y : Sp K ⟶ M.Z} {z : M.Z} (h : ∀ w, y w ⤳ z) {u : J → Ω} {c : Matrix J J Ω}
    (hu : ∀ j, u j ∈ M.O z) (hc : ∀ j i, c j i ∈ M.O z) (i : J) :
    M.val y (Matrix.vecMul u c i) = ∑ j, M.val y (u j) * M.val y (c j i) := by
  have e := map_sum (RatModel.valHomOf y z h) (fun j => (⟨u j, hu j⟩ * ⟨c j i, hc j i⟩ : M.O z)) Finset.univ
  simp only [map_mul, RatModel.valHomOf_apply] at e
  rw [← e]
  congr 1
  simp [Matrix.vecMul, dotProduct]

theorem sum_mul_mem_of_mem_span {J K : Type} [Fintype J] [Field K] (V : ValuationSubring K) (c : J → K)
    {s : Set (J → K)} (hs : ∀ w ∈ s, ∑ j, w j * c j ∈ V) {w : J → K} (hw : w ∈ Submodule.span V s) :
    ∑ j, w j * c j ∈ V := by
  induction hw using Submodule.span_induction with
  | mem w hw => exact hs w hw
  | zero => simp
  | add w w' _ _ hw hw' =>
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    exact add_mem hw hw'
  | smul a w _ hw =>
    have : ∑ j, (a • w) j * c j = (a : K) * ∑ j, w j * c j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => mul_assoc _ _ _
    rw [this]
    exact mul_mem a.2 hw

theorem mem_EE_iff_forall_test :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.Over₀ M U₀ → ((∀ U₁ : M.Z.Opens, U₁ ≤ U₀ → (U₁ : Set M.Z).Nonempty → ∀ z : M.Z, IsClosed ({z} : Set M.Z) → (∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y) ∧ ∀ φ ∈ M.ringOn U₁, (∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y → ‖M.val (gPt p ≫ y) φ‖ ≤ 1) → φ ∈ M.O z) ∧ JacobsonSpace M.Z) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ z y → ∃ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ ∧ (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) ∧ Nonempty (S.Test p y₀)) → S.IsEE M U₀ EE → ∀ z : M.Z, IsClosed ({z} : Set M.Z) → ∀ v : S.J → Ω, (∀ j, v j ∈ M.ringOn U₀) → (v ∈ EE.E z ↔ ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → (fun j => M.val (gPt p ≫ y) (v j)) ∈ τ.E) := by
  intro o Ω _ _ _ _ S M U₀ EE hO hloc htest hEE z hz v hv
  refine ⟨fun h p _ y y₀ τ hc hat => ?_, fun h => ?_⟩
  · rw [← hEE.2 z p y y₀ τ hc hat]
    exact Submodule.subset_span ⟨v, h, rfl⟩
  obtain ⟨W, b, hzW, hb, hE⟩ := EE.loc z
  have hstd : ∀ z' ∈ U₀, ∀ u, u ∈ EE.E z' ↔ ∀ j, u j ∈ M.O z' := fun z' hz' u => by
    rw [hEE.1 z' hz']
    exact RatModel.Lat.mem_const_iff M
  have hrow : ∀ z' ∈ W, ∀ u, u ∈ EE.E z' ↔ ∀ i, Matrix.vecMul u b⁻¹ i ∈ M.O z' := fun z' hz' u => by
    rw [hE z' hz']
    exact mem_span_rows_iff_coords_mem _ hb u
  have hinv : ∀ z' ∈ U₀ ⊓ W, ∀ j i, b⁻¹ j i ∈ M.O z' := fun z' hz' j i => by
    have h1 := (hrow z' hz'.2 (Pi.single j 1)).1 ((hstd z' hz'.1 _).2 fun k => by
      rw [Pi.single_apply]
      split_ifs
      exacts [one_mem _, zero_mem _]) i
    simpa using h1
  rw [hrow z hzW]
  intro i
  refine (hloc.1 (U₀ ⊓ W) inf_le_left (M.nonempty_inf hO.ne ⟨z, hzW⟩) z hz).2 _ ?_ ?_
  · exact RatModel.mem_ringOn.2 fun z' hz' =>
      (hrow z' hz'.2 v).1 ((hstd z' hz'.1 v).2 fun j => RatModel.mem_ringOn.1 (hv j) z' hz'.1) i
  intro p _ y hc
  have hc₀ : M.Cen U₀ z y := ⟨hc.1, fun w hw => (hc.2 hw).1⟩
  obtain ⟨y₀, hat, -, ⟨τ⟩⟩ := htest z p y hc₀
  have hm := h p y y₀ τ hc₀ hat
  rw [← hEE.2 z p y y₀ τ hc₀ hat] at hm
  obtain ⟨ξ, hξU, hsp, hle⟩ : ∃ ξ ∈ U₀ ⊓ W, (∀ w, (gPt p ≫ y) w ⤳ ξ) ∧ M.O z ≤ M.O ξ :=
    ⟨(gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p)), hc.2 ⟨_, rfl⟩,
      RatModel.specializes_of_range_eq (RatModel.range_eq_singleton _ _),
      RatModel.O_le_of_specializes (RatModel.gPt_specializes hc.1 _)⟩
  rw [RatModel.val_vecMul_eq_sum hsp (fun j => RatModel.mem_ringOn.1 (hv j) ξ hξU.1) (hinv ξ hξU), ← mem_OO_iff]
  refine sum_mul_mem_of_mem_span (OO p) _ ?_ hm
  rintro _ ⟨u, huE, rfl⟩
  have h1 := (hrow z hzW u).1 huE
  have h2 : ∀ j, u j ∈ M.O ξ :=
    (hstd ξ hξU.1 u).1 ((hrow ξ hξU.2 u).2 fun k => hle (h1 k))
  have h3 := hc.norm_val_le_one (h1 i)
  rw [RatModel.val_vecMul_eq_sum hsp h2 (hinv ξ hξU)] at h3
  exact (mem_OO_iff _).2 h3

end GlobalTheory.ZH
end

