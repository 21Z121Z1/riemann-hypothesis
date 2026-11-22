import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Formalism.PadicSubsetSums.CentralIdempotents.GaloisConjCentralIdempotent
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrrParIffCuspidalProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalOfIrr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0318
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0623
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0703
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0655
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0699
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0764
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkGLOneCorner
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0786
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0663
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0770
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0777
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0787
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0356

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHeckeTranslateHarrisTaylorPullbackBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

set_option autoImplicit false
noncomputable section
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPel.HT.Hecke.PullHecke

theorem isGaloisCover_of_isPullback {X Y X' Y' : Scheme.{0}} {Ga Ga' : Type} [Group Ga] [Group Ga']
    {ρ : Ga → (X ⟶ X)} {π : X ⟶ Y} {ρ' : Ga' → (X' ⟶ X')} {π' : X' ⟶ Y'} {u : X' ⟶ X} {v : Y' ⟶ Y}
    (h : GlobalTheory.ZM.IsGaloisCover Ga ρ π) (hp : IsPullback u π' π v)
    (one' : ρ' 1 = 𝟙 X') (mul' : ∀ a c, ρ' (a * c) = ρ' a ≫ ρ' c) (inj' : Function.Injective ρ')
    (hπ : ∀ a, ρ' a ≫ π' = π')
    (up : ∀ a', ∃ a, ρ' a' ≫ u = u ≫ ρ a) (down : ∀ a, ∃ a', ρ' a' ≫ u = u ≫ ρ a) :
    GlobalTheory.ZM.IsGaloisCover Ga' ρ' π' where
  finite := by
    have := h.finite
    choose σ hσ using up
    refine Finite.of_injective σ fun a c e => inj' ?_
    exact hp.hom_ext (by rw [hσ, hσ, e]) (by rw [hπ, hπ])
  one := one'
  mul := mul'
  inv := hπ
  fin := MorphismProperty.of_isPullback (P := @IsFinite) hp h.fin
  etale := MorphismProperty.of_isPullback (P := @Etale) hp h.etale
  onto := MorphismProperty.of_isPullback (P := @Surjective) hp h.onto
  fibre K _ _ y y' e := by
    obtain ⟨a, ha, ha'⟩ := h.fibre K (y ≫ u) (y' ≫ u) (by simp only [Category.assoc, hp.w, reassoc_of% e])
    obtain ⟨a', ea'⟩ := down a
    have ex : y ≫ ρ' a' = y' := hp.hom_ext
      (by rw [Category.assoc, ea', ← Category.assoc, ha])
      (by rw [Category.assoc, hπ, e])
    refine ⟨a', ex, fun b' hb' => inj' ?_⟩
    obtain ⟨b, eb⟩ := up b'
    have hb'' : y ≫ ρ' b' = y' := hb'
    have hb : b = a := ha' b (by show (y ≫ u) ≫ ρ b = y' ≫ u; rw [Category.assoc, ← eb, ← Category.assoc, hb''])
    subst hb
    exact hp.hom_ext (by rw [eb, ea']) (by rw [hπ, hπ])

end GlobalTheory.UPel.HT.Hecke.PullHecke

namespace GlobalTheory.UPel.HT.Hecke.PullHecke

theorem transl_one {S : Scheme.{0}} {A : Over S} [GrpObj A] : transl (1 : 𝟙_ (Over S) ⟶ A) = 𝟙 A := by
  show 𝟙 A * (toUnit A ≫ 1) = 𝟙 A
  rw [MonObj.comp_one, _root_.mul_one]

theorem transl_mul {S : Scheme.{0}} {A : Over S} [GrpObj A] (a c : 𝟙_ (Over S) ⟶ A) :
    transl (a * c) = transl a ≫ transl c := by
  have e : transl a ≫ transl c = transl a * (toUnit A ≫ c) := by
    show transl a ≫ (𝟙 A * (toUnit A ≫ c)) = _
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, toUnit_unique (transl a ≫ toUnit A) (toUnit A)]
  rw [e]
  show 𝟙 A * (toUnit A ≫ (a * c)) = (𝟙 A * (toUnit A ≫ a)) * (toUnit A ≫ c)
  rw [MonObj.comp_mul, _root_.mul_assoc]

theorem transl_injective {S : Scheme.{0}} {A : Over S} [GrpObj A] {a c : 𝟙_ (Over S) ⟶ A}
    (h : (transl a).left = (transl c).left) : a = c := by
  have h' : transl a = transl c := Over.OverMorphism.ext h
  rw [← one_comp_transl a, h', one_comp_transl]

theorem grpScheme_square_hom_ext {S : Scheme.{0}} {A : Over S} {X : Scheme.{0}} (u u' : X ⟶ (A ⊗ A).left)
    (h₁ : u ≫ (fst A A).left = u' ≫ (fst A A).left) (h₂ : u ≫ (snd A A).left = u' ≫ (snd A A).left) : u = u' := by
  have hw : u' ≫ (A ⊗ A).hom = u ≫ (A ⊗ A).hom := by
    rw [← Over.w (fst A A), ← Category.assoc, ← h₁, Category.assoc]
  let U : Over.mk (u ≫ (A ⊗ A).hom) ⟶ A ⊗ A := Over.homMk u rfl
  let U' : Over.mk (u ≫ (A ⊗ A).hom) ⟶ A ⊗ A := Over.homMk u' hw
  have : U = U' := CartesianMonoidalCategory.hom_ext _ _ (Over.OverMorphism.ext h₁) (Over.OverMorphism.ext h₂)
  exact congrArg (fun z => z.left) this

theorem grpSchemeSquareProductMap_comp_fst {S : Scheme.{0}} {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A']
    (ψ : A ⟶ A') : sq2 ψ ≫ (fst A' A').left = (fst A A).left ≫ ψ.left := by
  show (lift (fst A A ≫ ψ) (snd A A ≫ ψ)).left ≫ _ = _
  rw [← Over.comp_left, lift_fst, Over.comp_left]

theorem grpSchemeSquareProductMap_comp_snd {S : Scheme.{0}} {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A']
    (ψ : A ⟶ A') : sq2 ψ ≫ (snd A' A').left = (snd A A).left ≫ ψ.left := by
  show (lift (fst A A ≫ ψ) (snd A A ≫ ψ)).left ≫ _ = _
  rw [← Over.comp_left, lift_snd, Over.comp_left]

theorem cls_heckePow {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (n : ℕ) (h : (GlobalTheory.UPel.HT.Hecke.lbPow L n).IsLB) :
    GlobalTheory.CechPic.cls (GlobalTheory.UPel.HT.Hecke.lbPow L n) h = n • GlobalTheory.CechPic.cls L hL := by
  unfold GlobalTheory.UPel.HT.Hecke.lbPow at h ⊢
  rw [GlobalTheory.CechPic.cls_linComb hL]
  simp [GlobalTheory.CechPic.pull_id]

end GlobalTheory.UPel.HT.Hecke.PullHecke

namespace GlobalTheory.UPel.HT.Hecke.PullHecke

theorem isHecke_pull : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R)
    (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), k.Coprime p → 3 ≤ N → N.Coprime p → ∀ (S S' : Scheme.{0}) (s : S ⟶ Sp R)
    (f : S' ⟶ S) (o : Obj b (N * k) s) (o' : Obj b N s) (ψ : o.A ⟶ o'.A) (o₁ : Obj b (N * k) (f ≫ s))
    (o₁' : Obj b N (f ≫ s)), IsHecke g c k N o o' ψ → ObjMap o₁ o f → ObjMap o₁' o' f →
    ∃ ψ₁ : o₁.A ⟶ o₁'.A, IsHecke g c k N o₁ o₁' ψ₁ := by
  intro p _ D R _ b g c k N _ _ _ S S' s f o o' ψ o₁ o₁' hH m m'
  obtain ⟨hmon, hlin, heta, hgal, ⟨hP⟩, hdvd⟩ := hH
  have w : (m.φ ≫ ψ.left) ≫ o'.A.hom = o₁.A.hom ≫ f := by
    rw [Category.assoc, Over.w]; exact m.cart.1.w
  let ψ₁ : o₁.A ⟶ o₁'.A := Over.homMk (m'.cart.1.lift (m.φ ≫ ψ.left) o₁.A.hom w) (m'.cart.1.lift_snd _ _ _)
  have hψ₁ : ψ₁.left ≫ m'.φ = m.φ ≫ ψ.left := m'.cart.1.lift_fst _ _ _
  have ext' : ∀ {T : Over S'} (x y : T ⟶ o₁'.A), x.left ≫ m'.φ = y.left ≫ m'.φ → x = y := fun x y e =>
    Over.OverMorphism.ext (m'.cart.1.hom_ext e (by rw [Over.w, Over.w]))

  have pa : ∀ {T : Over S'} (x : T ⟶ o₁.A), pushPt m'.cart.1.w (x ≫ ψ₁) = pushPt m.cart.1.w x ≫ ψ := fun x =>
    Over.OverMorphism.ext (by
      show (x ≫ ψ₁).left ≫ m'.φ = (x.left ≫ m.φ) ≫ ψ.left
      rw [Over.comp_left, Category.assoc, hψ₁, Category.assoc])
  have pm : ∀ {T : Over S'} (x y : T ⟶ o₁.A),
      pushPt m.cart.1.w (x * y) = pushPt m.cart.1.w x * pushPt m.cart.1.w y := fun x y => map_mul (pushHom m.cart _) x y
  have pm' : ∀ {T : Over S'} (x y : T ⟶ o₁'.A),
      pushPt m'.cart.1.w (x * y) = pushPt m'.cart.1.w x * pushPt m'.cart.1.w y := fun x y => map_mul (pushHom m'.cart _) x y
  have inj' : ∀ {T : Over S'} {x y : T ⟶ o₁'.A}, pushPt m'.cart.1.w x = pushPt m'.cart.1.w y → x = y := fun e =>
    ext' _ _ (congrArg (fun z => z.left) e)
  haveI := hmon
  have hmon₁ : IsMonHom ψ₁ := by
    refine isMonHom_of_mul ψ₁ fun T x y => ?_
    apply inj'
    rw [pa, pm, MonObj.mul_comp, ← pa, ← pa, pm']

  have tc : ∀ z, (transl (o₁.eta z)).left ≫ m.φ = m.φ ≫ (transl (o.eta z)).left := by
    intro z
    have hu : pushPt m.cart.1.w (toUnit o₁.A ≫ o₁.eta z) = toUnit _ ≫ o.eta z := Over.OverMorphism.ext (by
      show (toUnit o₁.A ≫ o₁.eta z).left ≫ m.φ = (toUnit (Over.mk (o₁.A.hom ≫ f)) ≫ o.eta z).left
      rw [Over.comp_left, Over.comp_left, Category.assoc, m.eta]
      simp)
    have e : pushPt m.cart.1.w (transl (o₁.eta z)) = pushPt m.cart.1.w (𝟙 o₁.A) ≫ transl (o.eta z) := by
      show pushPt m.cart.1.w (𝟙 o₁.A * (toUnit o₁.A ≫ o₁.eta z)) =
        pushPt m.cart.1.w (𝟙 o₁.A) ≫ (𝟙 o.A * (toUnit o.A ≫ o.eta z))
      rw [pm, hu, MonObj.comp_mul, Category.comp_id, ← Category.assoc, toUnit_unique (_ ≫ toUnit o.A) (toUnit _)]
    have e' : (transl (o₁.eta z)).left ≫ m.φ = ((𝟙 o₁.A : o₁.A ⟶ o₁.A).left ≫ m.φ) ≫ (transl (o.eta z)).left :=
      congrArg (fun z => z.left) e
    rw [e', Over.id_left, Category.id_comp]
  have hp : IsPullback m.φ ψ₁.left ψ.left m'.φ := by
    refine IsPullback.of_bot ?_ hψ₁.symm m'.cart.1
    rw [Over.w ψ₁, Over.w ψ]; exact m.cart.1
  refine ⟨ψ₁, hmon₁, fun c' => ?_, fun x => ?_, ?_, ?_, hdvd⟩
  · apply ext'
    have h₀ := congrArg (fun z => m.φ ≫ z.left) (hlin c')
    simp only [Over.comp_left, Category.assoc] at h₀ ⊢
    rw [hψ₁, m'.act, reassoc_of% hψ₁, reassoc_of% (m.act c')]
    exact h₀
  · apply ext'
    rw [m'.eta, heta]
    simp only [Over.comp_left, Category.assoc]
    rw [hψ₁, reassoc_of% (m.eta (g x))]
  · refine isGaloisCover_of_isPullback hgal hp ?_ (fun a c => ?_) (fun a c e => Subtype.ext (transl_injective e))
      (fun a => ?_) (fun a => ?_) (fun a => ?_)
    · show (transl 1).left = _
      rw [transl_one, Over.id_left]
    · show (transl (a.1 * c.1)).left = _
      rw [transl_mul, Over.comp_left]
    · obtain ⟨h, x, rfl⟩ := a
      have hi : (transl (o.eta (N • g x))).left ≫ ψ.left = ψ.left := hgal.inv ⟨_, mem_heckeSub o g N x⟩
      show (transl (o₁.eta (N • g x))).left ≫ ψ₁.left = ψ₁.left
      refine m'.cart.1.hom_ext ?_ ?_
      · rw [Category.assoc, hψ₁, ← Category.assoc, tc, Category.assoc, hi]
      · rw [Category.assoc, Over.w ψ₁, Over.w]
    · obtain ⟨h, x, rfl⟩ := a
      exact ⟨⟨_, mem_heckeSub o g N x⟩, tc _⟩
    · obtain ⟨h, x, rfl⟩ := a
      exact ⟨⟨_, mem_heckeSub o₁ g N x⟩, tc _⟩
  · have hs1 : m.φ₂ ≫ (fst o.A o.A).left = (fst o₁.A o₁.A).left ≫ m.φ := m.sq.1
    have hs2 : m.φ₂ ≫ (snd o.A o.A).left = (snd o₁.A o₁.A).left ≫ m.φ := m.sq.2
    have hn₀ : (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)).IsLB := LB.isLB_linComb o.isLB _ _
    have hn₁ : (GlobalTheory.UPel.HT.Hecke.lbPow o₁.P (k ^ 2 / c)).IsLB := LB.isLB_linComb o₁.isLB _ _
    have hsq : sq2 ψ₁ ≫ m'.φ₂ = m.φ₂ ≫ sq2 ψ := by
      apply grpScheme_square_hom_ext
      · rw [Category.assoc, m'.sq.1, ← Category.assoc, grpSchemeSquareProductMap_comp_fst, Category.assoc, hψ₁, Category.assoc, grpSchemeSquareProductMap_comp_fst,
          ← Category.assoc m.φ₂, hs1, Category.assoc]
      · rw [Category.assoc, m'.sq.2, ← Category.assoc, grpSchemeSquareProductMap_comp_snd, Category.assoc, hψ₁, Category.assoc, grpSchemeSquareProductMap_comp_snd,
          ← Category.assoc m.φ₂, hs2, Category.assoc]
    have c₁ : GlobalTheory.CechPic.cls o₁.P o₁.isLB = GlobalTheory.CechPic.pull m.φ₂ (GlobalTheory.CechPic.cls o.P o.isLB) :=
      (GlobalTheory.CechPic.cls_eq_iff o₁.isLB (pull_isLB o.isLB _)).2 m.pol
    have c₁' : GlobalTheory.CechPic.cls o₁'.P o₁'.isLB = GlobalTheory.CechPic.pull m'.φ₂ (GlobalTheory.CechPic.cls o'.P o'.isLB) :=
      (GlobalTheory.CechPic.cls_eq_iff o₁'.isLB (pull_isLB o'.isLB _)).2 m'.pol
    have c₀ : GlobalTheory.CechPic.pull (sq2 ψ) (GlobalTheory.CechPic.cls o'.P o'.isLB) = (k ^ 2 / c) • GlobalTheory.CechPic.cls o.P o.isLB := by
      rw [← GlobalTheory.CechPic.cls_pull o'.isLB _ (pull_isLB o'.isLB _),
        ← (GlobalTheory.CechPic.cls_eq_iff hn₀ (pull_isLB o'.isLB _)).2 hP, cls_heckePow o.isLB]
    refine ⟨(GlobalTheory.CechPic.cls_eq_iff hn₁ (pull_isLB o₁'.isLB _)).1 ?_⟩
    rw [cls_heckePow o₁.isLB, GlobalTheory.CechPic.cls_pull o₁'.isLB, c₁, c₁', ← GlobalTheory.CechPic.pull_comp, hsq,
      GlobalTheory.CechPic.pull_comp, c₀, map_nsmul]

end GlobalTheory.UPel.HT.Hecke.PullHecke
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIrrRepHarishChandraDistinctCuspidalLabels
section
noncomputable section
namespace GlobalTheory.HcIrr
open Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.DIV Polynomial CategoryTheory

theorem isIrrRep_of_equiv {G V V' : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (ρ : Representation ℂ G V) (ρ' : Representation ℂ G V') (A : G → G) (hA : Function.Surjective A)
    (Ψ : V ≃ₗ[ℂ] V') (h : ∀ g v, Ψ (ρ (A g) v) = ρ' g (Ψ v)) (hirr : IsIrrRep ρ') : IsIrrRep ρ := by
  obtain ⟨hn, hW⟩ := hirr
  refine ⟨Ψ.toEquiv.nontrivial, fun W hinv => ?_⟩
  have hinv' : ∀ g, ∀ v ∈ W.map (Ψ : V →ₗ[ℂ] V'), ρ' g v ∈ W.map (Ψ : V →ₗ[ℂ] V') := by
    rintro g _ ⟨w, hw, rfl⟩
    exact ⟨ρ (A g) w, hinv _ _ hw, h g w⟩
  rcases hW _ hinv' with h0 | h1
  · left
    refine eq_bot_iff.2 fun v hv => ?_
    have hv' : Ψ v ∈ W.map (Ψ : V →ₗ[ℂ] V') := ⟨v, hv, rfl⟩
    rw [h0, Submodule.mem_bot] at hv'
    simpa using hv'
  · right
    refine eq_top_iff.2 fun v _ => ?_
    have : Ψ v ∈ W.map (Ψ : V →ₗ[ℂ] V') := h1 ▸ Submodule.mem_top
    obtain ⟨w, hw, hwv⟩ := this
    rwa [← Ψ.injective hwv]

theorem isIrrRep_of_isIrreducible {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (h : ρ.IsIrreducible) : IsIrrRep ρ := by
  haveI := h
  refine ⟨?_, fun W hW => ?_⟩
  · by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    have : (⊥ : Subrepresentation ρ) = ⊤ := Subrepresentation.ext (Subsingleton.elim (α := Submodule ℂ V) _ _)
    exact bot_ne_top this
  · rcases eq_bot_or_eq_top (⟨W, fun g v hv => hW g v hv⟩ : Subrepresentation ρ) with h0 | h1
    · exact Or.inl (congrArg Subrepresentation.toSubmodule h0)
    · exact Or.inr (congrArg Subrepresentation.toSubmodule h1)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {r s : ℕ}

theorem isIrrRep_hcRep_of_parInd (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K))
    (h : (GlobalTheory.FinGL.parInd (natBlocks b) (leviTensor b lam)).IsIrreducible) : IsIrrRep (hcRep K b lam) := by
  let L : hcSpace K b lam ≃ₗ[ℂ] Representation.coindV (blockTri (κ := K) (natBlocks b)).subtype (leviTensor b lam) :=
    { toFun := fun f => ⟨f.1, fun p x => f.2 (Subgroup.inclusion (blockTri_le_parab b) p) x⟩
      invFun := fun f => ⟨f.1, fun p x => f.2 (Subgroup.inclusion (parab_le_blockTri b) p) x⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact isIrrRep_of_equiv (hcRep K b lam) _ id Function.surjective_id L (fun _ _ => rfl)
    (isIrrRep_of_isIrreducible _ h)

theorem exists_sorted {C : LabelConv K} (O : LabelMap K C) (b : Fin r → Fin s)
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)) (hb : Function.Surjective b)
    (hl : ∀ c, Simple (lam c) ∧ IsCuspidal K (lam c)) :
    ∃ (b' : Fin r → Fin s) (lam' : ∀ c : Fin s, FDRep ℂ (GL {i // b' i = c} K)), Function.Surjective b' ∧
      Monotone b' ∧ (∀ c, Simple (lam' c) ∧ IsCuspidal K (lam' c)) ∧ (∀ c, labO O (lam' c) = labO O (lam c)) ∧
      (IsIrrRep (hcRep K b' lam') → IsIrrRep (hcRep K b lam)) := by
  let e : Fin r ≃ Fin r := (Tuple.sort b).symm
  let b' : Fin r → Fin s := b ∘ e.symm
  let ec : ∀ c, {i // b i = c} ≃ {k // b' k = c} := fun c => e.subtypeEquiv (fun i => by simp [b'])
  let lam' : ∀ c : Fin s, FDRep ℂ (GL {k // b' k = c} K) := fun c => transp (ec c) (lam c)
  let A : GL (Fin r) K ≃* GL (Fin r) K := (glEquiv K e).symm
  have hpar : ∀ p : parab K b', A p.1 ∈ parab K b := by
    intro p
    obtain ⟨h1, h2⟩ := p.2
    refine ⟨fun i j hij => ?_, fun i j hij => ?_⟩
    · show Matrix.reindex e.symm e.symm (p.1 : Matrix (Fin r) (Fin r) K) i j = 0
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
      exact h1 _ _ (by simpa [b'] using hij)
    · rw [← map_inv]
      show Matrix.reindex e.symm e.symm ((p.1⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) i j = 0
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
      exact h2 _ _ (by simpa [b'] using hij)
  have hpar' : ∀ q : parab K b, A.symm q.1 ∈ parab K b' := by
    intro q
    obtain ⟨h1, h2⟩ := q.2
    refine ⟨fun i j hij => ?_, fun i j hij => ?_⟩
    · show Matrix.reindex e e (q.1 : Matrix (Fin r) (Fin r) K) i j = 0
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
      exact h1 _ _ hij
    · rw [← map_inv]
      show Matrix.reindex e e ((q.1⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) i j = 0
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
      exact h2 _ _ hij
  have hlevi : ∀ (p : parab K b') (c : Fin s),
      levi K b c ⟨A p.1, hpar p⟩ = (glEquiv K (ec c)).symm (levi K b' c p) := by
    intro p c
    apply Units.ext
    ext i j
    rfl
  have hinfl : ∀ p : parab K b', infl K b lam ⟨A p.1, hpar p⟩ = infl K b' lam' p := by
    intro p
    unfold infl
    congr 1
  have hinfl' : ∀ q : parab K b, infl K b lam q = infl K b' lam' ⟨A.symm q.1, hpar' q⟩ := by
    intro q
    rw [← hinfl]
    congr 2
    exact Subtype.ext (A.apply_symm_apply q.1).symm
  let Ψ : hcSpace K b lam ≃ₗ[ℂ] hcSpace K b' lam' :=
    { toFun := fun F => ⟨fun x => F.1 (A x), fun p x => by
        show F.1 (A (p.1 * x)) = infl K b' lam' p (F.1 (A x))
        rw [map_mul, ← hinfl]
        exact F.2 ⟨A p.1, hpar p⟩ (A x)⟩
      invFun := fun F => ⟨fun x => F.1 (A.symm x), fun q x => by
        show F.1 (A.symm (q.1 * x)) = infl K b lam q (F.1 (A.symm x))
        rw [map_mul, hinfl']
        exact F.2 ⟨A.symm q.1, hpar' q⟩ (A.symm x)⟩
      map_add' := fun F G => rfl
      map_smul' := fun a F => rfl
      left_inv := fun F => Subtype.ext (_root_.funext fun x => congrArg F.1 (A.apply_symm_apply x))
      right_inv := fun F => Subtype.ext (_root_.funext fun x => congrArg F.1 (A.symm_apply_apply x)) }
  refine ⟨b', lam', hb.comp e.symm.surjective, ?_, fun c => ⟨Formalism.L2.PT.simple_transp _ (hl c).1,
    Formalism.L2.PT.isCuspidal_transp _ (hl c).2⟩, fun c => GlobalTheory.SerOSys.TranspLabel.labO_transp O (ec c) (lam c), ?_⟩
  · exact Tuple.monotone_sort b
  · refine isIrrRep_of_equiv _ _ A A.surjective Ψ fun g F => ?_
    apply Subtype.ext
    funext x
    show F.1 (A x * A g) = F.1 (A (x * g))
    rw [map_mul]

theorem labO_eq_of_readings {C : LabelConv K} (O : LabelMap K C) {α β : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (d : ℕ) (e : α ≃ Fin d) (e' : β ≃ Fin d) (σ : FDRep ℂ (GL α K))
    (σ' : FDRep ℂ (GL β K)) (M : (σ : Type) ≃ₗ[ℂ] (σ' : Type))
    (hM : ∀ g v, M (σ.ρ ((glEquiv K e).symm g) v) = σ'.ρ ((glEquiv K e').symm g) (M v)) :
    labO O σ = labO O σ' := by
  rw [← GlobalTheory.SerOSys.TranspLabel.labO_transp O e σ, ← GlobalTheory.SerOSys.TranspLabel.labO_transp O e' σ']
  unfold labO
  apply O.lab_iso
  exact ⟨GlobalTheory.SerOSys.TranspLabel.repIsoOf _ _ M fun γ v => hM _ v⟩

theorem distinctFactors {C : LabelConv K} (O : LabelMap K C) (b : Fin r → Fin s)
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)) (hs : ∀ c, Simple (lam c))
    (hinj : Function.Injective (fun c => labO O (lam c))) :
    GlobalTheory.IndefiniteRowSideFullHecke.BlockEmbeddingFactors.DistinctFactors (natBlocks b) (leviTensor b lam) := by
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hne ⟨d, h, h', W, _, _, ρ, hf, hf'⟩
  obtain ⟨e, L, hL⟩ := GlobalTheory.T.hasCuspidalFactorAtBlock_leviPiTensor K r s b lam hs (b i) d h W ρ hf
  obtain ⟨e', L', hL'⟩ := GlobalTheory.T.hasCuspidalFactorAtBlock_leviPiTensor K r s b lam hs (b j) d h' W ρ hf'
  have hlab : labO O (lam (b i)) = labO O (lam (b j)) := by
    refine labO_eq_of_readings O d e e' _ _ (L.symm.trans L') fun g v => ?_
    obtain ⟨w, rfl⟩ := L.surjective v
    rw [← hL]
    simp [hL']
  exact hne (congrArg (fun c : Fin s => (c : ℕ)) (hinj hlab))

theorem isIrrRep_of_monotone {C : LabelConv K} (O : LabelMap K C) (b : Fin r → Fin s)
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K))
    (hl : ∀ c, Simple (lam c) ∧ IsCuspidal K (lam c))
    (hinj : Function.Injective (fun c => labO O (lam c))) (hm : Monotone b) : IsIrrRep (hcRep K b lam) := by
  have hd : GlobalTheory.FinGL.IsCuspDatum (natBlocks b) (leviTensor b lam) :=
    { mono := fun i j hij => hm hij
      irr := GlobalTheory.T.leviPiTensorRepresentation_isIrreducible K r s b lam fun c => (hl c).1
      infl := fun p hp => by
        rw [leviTensor_apply]
        have : ∀ c, (lam c).ρ (levi K b c (Subgroup.inclusion (blockTri_le_parab b) p)) = LinearMap.id := by
          intro c
          have h1 : levi K b c (Subgroup.inclusion (blockTri_le_parab b) p) = 1 := by
            apply Units.ext
            ext x y
            have := hp x.1 y.1 (by simp [natBlocks, x.2, y.2])
            show ((p : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) x.1 y.1 = (1 : Matrix _ _ K) x y
            rw [this]
            simp [Matrix.one_apply, Subtype.ext_iff]
          rw [h1, map_one]
          rfl
        simp only [this]
        exact PiTensorProduct.map_id
      cusp := fun S hS y hy => GlobalTheory.T.cuspidal_piTensor_no_blockUnipotent_fixed K r s b lam (fun c => (hl c).2) S hS y hy }
  exact isIrrRep_hcRep_of_parInd b lam
    ((GlobalTheory.CuspFactor.irrPar_iff_cuspidalProduct.1 GlobalTheory.FinGL.IrrProduct.irrPar).1 K r _ _ _ hd
      (distinctFactors O b lam (fun c => (hl c).1) hinj))

theorem isIrrRep_hcRep : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (r s : ℕ) (b : Fin r → Fin s)
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)), Function.Surjective b →
    (∀ c, Simple (lam c) ∧ IsCuspidal K (lam c)) → ∀ (C : LabelConv K) (O : LabelMap K C),
    Function.Injective (fun c => labO O (lam c)) → IsIrrRep (hcRep K b lam) := by
  intro K _ _ _ r s b lam hb hl C O hinj
  obtain ⟨b', lam', hb', hm, hl', hlab, hback⟩ := exists_sorted O b lam hb hl
  exact hback (isIrrRep_of_monotone O b' lam' hl'
    (fun c c' h => hinj (by simpa [hlab] using h)) hm)

end GlobalTheory.HcIrr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenDiagonalSliceLevelSubgroup
section
open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.SliceTwo

open GlobalTheory.LeviGA

theorem isOpen_levelSub : ∀ (E : Type) [Field E] [NumberField E] (a r : ℕ) (hr : r ≤ a) (t : GL (Fin a) (Af E))
    (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) →
      IsOpen (GlobalTheory.SliceTwo.levelSub hr t L : Set (GL (Fin (a - r)) (Af E))) := by
  intro E _ _ a r hr t L hL
  have hblk : Continuous fun l : GL (Fin (a - r)) (Af E) => blkGL hr (1, l) := by
    rw [Units.continuous_iff]
    refine ⟨?_, ?_⟩
    · show Continuous fun l : GL (Fin (a - r)) (Af E) =>
        Matrix.reindex (blkEquiv hr) (blkEquiv hr)
          (Matrix.fromBlocks ((1 : GL (Fin r) (Af E)) : Matrix _ _ (Af E)) 0 0 (l : Matrix _ _ (Af E)))
      exact (continuous_const.matrix_fromBlocks continuous_const continuous_const
        Units.continuous_val).matrix_reindex _ _
    · have e : ∀ l : GL (Fin (a - r)) (Af E), ((blkGL hr (1, l))⁻¹ : GL (Fin a) (Af E)) = blkGL hr (1, l⁻¹) := by
        intro l; rw [← map_inv]; rfl
      simp_rw [e]
      show Continuous fun l : GL (Fin (a - r)) (Af E) =>
        Matrix.reindex (blkEquiv hr) (blkEquiv hr)
          (Matrix.fromBlocks ((1 : GL (Fin r) (Af E)) : Matrix _ _ (Af E)) 0 0 ((l⁻¹ : GL _ _) : Matrix _ _ (Af E)))
      exact (continuous_const.matrix_fromBlocks continuous_const continuous_const
        Units.continuous_coe_inv).matrix_reindex _ _
  have hc : Continuous fun l : GL (Fin (a - r)) (Af E) => t⁻¹ * blkGL hr (1, l) * t :=
    (continuous_const.mul hblk).mul continuous_const
  have hs : (levelSub hr t L : Set (GL (Fin (a - r)) (Af E))) =
      (fun l : GL (Fin (a - r)) (Af E) => t⁻¹ * blkGL hr (1, l) * t) ⁻¹' (L : Set (GL (Fin a) (Af E))) := by
    ext l
    simp only [levelSub, Set.mem_preimage, SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_map,
      MonoidHom.coe_comp, Function.comp_apply, MonoidHom.inr_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨k, hk, e⟩
      rw [← e]; simpa [mul_assoc] using hk
    · intro h
      exact ⟨_, h, by group⟩
  rw [hs]
  exact hL.preimage hc

end GlobalTheory.SliceTwo
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSectionHolomorphicMulFrameExtendByZeroStatement
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSection_holomorphic_mul_frame_extendByZero : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (la : La) (U : Set Y) (z : Y → V n) (β : ι → Y → ℂ) (F0 : U → ℂ), Etale A U z → A.IsFrameOn la U β → Holo n (fun y : U => z y) F0 → A.IsSecOn la U (fun i y => β i y * GlobalTheory.OTY.TwEst.ext0 U F0 y) ∧ Measurable (GlobalTheory.OTY.TwEst.ext0 U F0) := by
  first | exact @GlobalTheory.OTY.TwEst.isSecOn_frame_mul_ext0_and_measurable | exact GlobalTheory.OTY.TwEst.isSecOn_frame_mul_ext0_and_measurable | (intros; apply GlobalTheory.OTY.TwEst.isSecOn_frame_mul_ext0_and_measurable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetFinsetLinearCombination
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

theorem GlobalTheory.ColNorms.jetC_sum_mul : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (cD : ι → ℂ) (α : Type) (R : Finset α) (c : α → ℂ) (F : α → VCx ι a b → ℂ), (∀ x ∈ R, Differentiable ℂ (F x)) → ∀ m, jetC cD (fun z => ∑ x ∈ R, c x * F x z) m = ∑ x ∈ R, c x * jetC cD (F x) m := by
  intro ι _ a b cD α R c F hF m
  have key : ∀ (k : ℕ) (v : Fin k → VCx ι a b),
      iteratedFDeriv ℂ k (fun w => ∑ i ∈ R, c i * F i w) 0 v =
        ∑ i ∈ R, c i * iteratedFDeriv ℂ k (F i) 0 v := by
    intro k v
    have hC : ∀ i ∈ R, ContDiff ℂ k (F i) := fun i hi =>
      GlobalTheory.SCV.contDiff_of_differentiable (hF i hi) _
    have h1 := iteratedFDeriv_sum (𝕜 := ℂ) (f := fun i w => c i * F i w) (u := R) (i := k)
      (fun i hi => contDiff_const.mul (hC i hi))
    rw [h1, Finset.sum_apply, ContinuousMultilinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i hi => ?_
    have h2 := iteratedFDeriv_const_smul_apply' (𝕜 := ℂ) (a := c i) (f := F i) (i := k) (x := 0)
      (hC i hi).contDiffAt
    simp only [smul_eq_mul] at h2
    rw [h2]
    simp
  unfold jetC derivAt0
  rw [key, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentCohomologyVanishingOfNoetherianHenselianStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laurentCohomology_vanishing_of_noetherian_henselian : ∀ (q : ℕ) [NeZero q], (∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) → ∀ n i : ℤ, 2 ≤ n → Subsingleton (Ht q (sp (LaurentPolynomial A)) n i)) → ∀ (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ n i : ℤ, 2 ≤ n → Subsingleton (Ht q (sp (LaurentPolynomial A)) n i) := by
  first | (exact @GlobalTheory.EtC.laurent_vanishing_of_noetherian) | (exact GlobalTheory.EtC.laurent_vanishing_of_noetherian) | (intros; apply GlobalTheory.EtC.laurent_vanishing_of_noetherian  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviRestrictionVanishingPreservedByOperatorStatement
section
open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_restriction_vanishing_preserved_by_operator : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ) (hr : r ≤ a) (f : Sm E a), (∀ (m₁ : GA E r) (m₂ : GA E (a - r)), f.1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂)) = 0) → ∀ (τ : E →+* ℂ) (i j : Fin a), ((i : ℕ) < r ↔ (j : ℕ) < r) → ∀ (m₁ : GA E r) (m₂ : GA E (a - r)), (Eop τ i j f).1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂)) = 0 := by
  first | exact @GlobalTheory.LeviDeriv.Eop_blkGL_eq_zero | exact GlobalTheory.LeviDeriv.Eop_blkGL_eq_zero | (intros; apply GlobalTheory.LeviDeriv.Eop_blkGL_eq_zero <;> assumption)
end

