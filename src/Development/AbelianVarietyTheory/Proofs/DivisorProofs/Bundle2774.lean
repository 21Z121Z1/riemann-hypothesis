import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0066
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2657
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulIncl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2676
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2621
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2595
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0033
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0084
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2677
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2464
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2248
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitScalarCancelOfIsField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.CancelField

theorem isIso_jK {R : Type} [CommRing R] [IsDomain R] (hR : IsField R) : IsIso (jK R) := by
  have hb : Function.Bijective (algebraMap R (FractionRing R)) :=
    ⟨IsFractionRing.injective R (FractionRing R), IsFractionRing.surjective_iff_isField.2 hR⟩
  have : IsIso (CommRingCat.ofHom (algebraMap R (FractionRing R))) :=
    (ConcreteCategory.isIso_iff_bijective _).2 hb
  infer_instance

theorem isIso_gp {R : Type} [CommRing R] [IsDomain R] (M : Modif R) (hR : IsField R) : IsIso M.gp := by
  haveI := isIso_jK hR
  haveI := M.integral
  haveI := M.proper
  haveI := M.dominant
  haveI : IsClosedImmersion M.gp :=
    isClosedImmersion_of_comp_eq_id (M.π ≫ inv (jK R)) M.gp (by rw [← Category.assoc, M.gp_π, IsIso.hom_inv_id])
  haveI : Surjective M.gp := ⟨by
    have h1 := M.gp.isClosedEmbedding.isClosed_range
    have h2 := M.gp.denseRange
    exact Set.range_eq_univ.1 (h1.closure_eq ▸ h2.closure_range)⟩
  exact isIso_of_isClosedImmersion_of_surjective M.gp

theorem sval_comp {X Y₀ Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y₀ ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (p : Z ⟶ Y) (r : Y ⟶ Y₀) (z : Z) (J : (Z ⟶ X) → L.ι) (hJ : Good L z J) :
    sval s (p ≫ r) z J = (p.stalkMap z).hom (sval s r (p z) (fun ψ => J (p ≫ ψ))) := by
  have hJ' : Good L (p z) (fun ψ => J (p ≫ ψ)) := fun ψ => hJ (p ≫ ψ)
  rw [sval_of s (p ≫ r) z J (fun k => J (p ≫ r ≫ φ k)) (fun k => by rw [Category.assoc])]
  exact gs_comp p r z _ (hJ'.mem φ r) _

theorem scal_cancel {W : Type} [CommRing W] [IsDomain W] {Y : Scheme.{0}} (f : Y ⟶ Sp W) [Flat f] (y : Y) {b : W}
    (hb : b ≠ 0) {u v : Y.presheaf.stalk y}
    (h : gs (𝟙 Y) y ⊤ (scal f b) * u = gs (𝟙 Y) y ⊤ (scal f b) * v) : u = v := by
  set c : Γ(Sp W, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom b with hc
  have e1 : gs (𝟙 Y) y ⊤ (scal f b) = (f.stalkMap y).hom (gs (𝟙 (Sp W)) (f y) ⊤ c) := by
    have := gs_pull (𝟙 Y) f y ⊤ trivial c
    rw [Category.id_comp] at this
    refine this.trans ?_
    have := gs_comp f (𝟙 (Sp W)) y ⊤ trivial c
    rwa [Category.comp_id] at this
  have hc0 : c ≠ 0 := by
    intro h0
    apply hb
    have hi : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom :=
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of W)).inv).1
    exact hi (h0.trans (map_zero _).symm)
  have he0 : gs (𝟙 (Sp W)) (f y) ⊤ c ≠ 0 := by
    rw [gs_eq (𝟙 (Sp W)) (f y) ⊤ trivial]
    intro h0
    apply hc0
    have hi := germ_injective_of_isIntegral (Sp W) (U := (𝟙 (Sp W)) ⁻¹ᵁ ⊤) (f y) trivial
    have := hi (h0.trans (map_zero _).symm)
    exact this
  letI := (f.stalkMap y).hom.toAlgebra
  haveI : Module.Flat _ (Y.presheaf.stalk y) := Flat.stalkMap f y
  have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := Y.presheaf.stalk y) (mem_nonZeroDivisors_of_ne_zero he0)
  apply hreg
  simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  rw [← e1]
  exact h

end GlobalTheory.Mum.CancelField

namespace GlobalTheory.Mum

open GlobalTheory.Mum.CancelField in

theorem cancel_field : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ) (σ : SecK C.P.L.L T.β k) (s : SecK C.P.L.L C.α k) (b : W) (c : FractionRing R), IsField R → b ≠ 0 → (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ z J, Good C.P.L.L z J → gs p z ⊤ (scal T.G.hom b) * sval σ p z J = gs p z ⊤ (scal T.G.hom b) * (gs p' z ⊤ (scal C.A.A.hom c) * sval s p' z J)) → ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ z J, Good C.P.L.L z J → sval σ p z J = gs p' z ⊤ (scal C.A.A.hom c) * sval s p' z J := by
  intro R _ _ _ _ D C W _ _ _ T k σ s b c hR hb H Z p p' hp z J hJ
  haveI : IsIso C.α := C.α_cart.1.isIso_fst_of_isIso (isIso_gp C.toModif hR)
  haveI : Smooth C.G.hom := C.semi.smooth
  haveI : Flat C.G.hom := inferInstance
  haveI : Flat T.G.hom := MorphismProperty.of_isPullback (P := @Flat) T.cart.1 inferInstance
  obtain ⟨q, hq⟩ : ∃ q : T.G.left ⟶ C.A.A.left, q ≫ C.α = T.β := ⟨T.β ≫ inv C.α, by simp⟩
  have key : ∀ y J', Good C.P.L.L y J' → sval σ (𝟙 _) y J' = gs q y ⊤ (scal C.A.A.hom c) * sval s q y J' := by
    intro y J' hJ'
    exact scal_cancel T.G.hom y hb (H _ (𝟙 _) q (by rw [hq, Category.id_comp]) y J' hJ')
  obtain rfl : p' = p ≫ q := (cancel_mono C.α).1 (by rw [Category.assoc, hq]; exact hp.symm)
  have hJ' : Good C.P.L.L (p z) (fun ψ => J (p ≫ ψ)) := fun ψ => hJ (p ≫ ψ)
  have e1 := sval_comp σ p (𝟙 _) z J hJ
  rw [Category.comp_id] at e1
  rw [e1, sval_comp s p q z J hJ, gs_comp p q z ⊤ trivial, ← map_mul, key (p z) _ hJ']

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslatedCubicalBundleClosedFibreUniformisation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.TranslateLevel
open GlobalTheory.UU

section Iso
variable {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {τ : X ⟶ X} {τ' : X' ⟶ X'}

theorem exists_translate (h : τ' ≫ F = F ≫ τ) (w₁ : LB.Iso L' (L.pull F)) (hw₁ : w₁.IsGen) :
    ∃ w : LB.Iso (L'.pull τ') ((L.pull τ).pull F), w.IsGen ∧
      ∀ (Y : Scheme.{0}) (r : Y ⟶ X') (y : Y) (j : L.ι) (k : L'.ι), τ (F (r y)) ∈ L.U j → τ' (r y) ∈ L'.U k →
        gw w r y (fun _ => j) (fun _ => k) = gw w₁ (r ≫ τ') y j k := by
  have e : ∀ x : X', F (τ' x) = τ (F x) := fun x => congrArg (fun g => g x) h
  have le : ∀ (j : L.ι) (k : L'.ι), ((L.pull τ).pull F).U (fun _ _ => j) ⊓ (L'.pull τ').U (fun _ => k) ≤
      τ' ⁻¹ᵁ ((L.pull F).U (fun _ => j) ⊓ L'.U k) := fun j k x hx =>
    ⟨mem_pull.2 (by rw [e]; exact mem_pull.1 (mem_pull.1 hx.1)), mem_pull.1 hx.2⟩
  let w : LB.Iso (L'.pull τ') ((L.pull τ).pull F) :=
    ⟨fun p => res (le (p.1 PUnit.unit PUnit.unit) (p.2 PUnit.unit))
      (pullU τ' _ (w₁.s (fun _ => p.1 PUnit.unit PUnit.unit, p.2 PUnit.unit)))⟩
  have key : ∀ (Y : Scheme.{0}) (r : Y ⟶ X') (y : Y) (j : L.ι) (k : L'.ι), τ (F (r y)) ∈ L.U j → τ' (r y) ∈ L'.U k →
      gw w r y (fun _ => j) (fun _ => k) = gw w₁ (r ≫ τ') y j k := fun Y r y j k hj hk => by
    have hm : r y ∈ ((L.pull τ).pull F).U (fun _ _ => j) ⊓ (L'.pull τ').U (fun _ => k) :=
      ⟨mem_pull.2 (mem_pull.2 hj), mem_pull.2 hk⟩
    exact (gm_res r y (le j k) hm _).trans (gm_pull r τ' y _ (@le j k (r y) hm) _)
  refine ⟨w, (isGen_iff w).2 fun Y r y j j' k k' hj hj' hk hk' => ?_, key⟩
  have a := (isGen_iff w₁).1 hw₁ Y (r ≫ τ') y (j PUnit.unit) (j' PUnit.unit) (k PUnit.unit) (k' PUnit.unit)
    (by show F (τ' (r y)) ∈ _; rw [e]; exact mem_pull.1 hj) (by show F (τ' (r y)) ∈ _; rw [e]; exact mem_pull.1 hj')
    ((mem_pull (F := τ')).1 hk) ((mem_pull (F := τ')).1 hk')
  rw [Category.assoc, h, ← Category.assoc] at a
  refine (key Y r y _ _ (mem_pull.1 hj) (mem_pull.1 hk)).trans (a.trans ?_)
  exact congrArg₂ (· * ·) (congrArg₂ (· * ·) (gm_pull_g L τ (r ≫ F) y j j' hj hj').symm
    (congrArg (·⁻¹) (gm_pull_g L' τ' r y k k' hk hk').symm))
    (key Y r y _ _ (mem_pull.1 hj') (mem_pull.1 hk')).symm

end Iso

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']

omit [IsCommMonObj G] in

theorem left_translate (a : 𝟙_ (Over S) ⟶ G) {T : Over S} (x : T ⟶ G) :
    x.left ≫ ((toUnit G ≫ a) * 𝟙 G).left = ((toUnit T ≫ a) * x).left := by
  rw [← Over.comp_left, MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit]

set_option maxHeartbeats 1000000 in

theorem exists_translate_pull {f : S' ⟶ S} {F : G'.left ⟶ G.left} {hw : F ≫ G.hom = G'.hom ≫ f}
    (Q P : CP G) (P₁ : CP G') (a : 𝟙_ (Over S) ⟶ G) (a' : 𝟙_ (Over S') ⟶ G') (ha : a'.left ≫ F = f ≫ a.left)
    (h2 : a' ^ 2 = 1) (hP : P.L.L = Q.L.L.pull ((toUnit G ≫ a) * 𝟙 G).left)
    (hs : ∀ (T : Over S) (x : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → Q.L.L.ι)
        (J' : (T.left ⟶ G.left) → P.L.L.ι), Good Q.L.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left))) →
        val P.sym x.left z J' =
          val Q.sym ((toUnit T ≫ a) * x).left z J * (val Q.sym (toUnit T ≫ a).left z J)⁻¹)
    (hc : ∀ (T : Over S) (x y u : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → Q.L.L.ι)
        (J' : (T.left ⟶ G.left) → P.L.L.ι), Good Q.L.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left))) →
        cubV P.c z J' x y u = cubV Q.c z J x y ((toUnit T ≫ a) * u) * (cubV Q.c z J x y (toUnit T ≫ a))⁻¹)
    {w₁ : LB.Iso P₁.L.L (Q.L.L.pull F)} (h₁ : IsCPMap P₁ Q f F hw w₁) :
    ∃ P₀ : CP G', (∃ w, IsCPMap P₀ P f F hw w) ∧ P₀.L.L = P₁.L.L.pull ((toUnit G' ≫ a') * 𝟙 G').left ∧
      (∀ (T : Over S') (x : T ⟶ G') (z : T.left) (J : (T.left ⟶ G'.left) → P₁.L.L.ι)
        (J' : (T.left ⟶ G'.left) → P₀.L.L.ι), Good P₁.L.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G' ≫ a') * 𝟙 G').left))) →
        val P₀.sym x.left z J' =
          val P₁.sym ((toUnit T ≫ a') * x).left z J * (val P₁.sym (toUnit T ≫ a').left z J)⁻¹) ∧
      (∀ (T : Over S') (x y u : T ⟶ G') (z : T.left) (J : (T.left ⟶ G'.left) → P₁.L.L.ι)
        (J' : (T.left ⟶ G'.left) → P₀.L.L.ι), Good P₁.L.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G' ≫ a') * 𝟙 G').left))) →
        cubV P₀.c z J' x y u = cubV P₁.c z J x y ((toUnit T ≫ a') * u) * (cubV P₁.c z J x y (toUnit T ≫ a'))⁻¹) := by
  obtain ⟨⟨L, rg, hL, hrg⟩, c, sy, g₁, g₂, g₃⟩ := P
  dsimp only at hP hs hc
  subst hP
  have hβ : ∀ T : Over S', toBase hw (toUnit T ≫ a') = toUnit (Over.mk (T.hom ≫ f)) ≫ a := fun T =>
    Over.OverMorphism.ext (by
      show ((toUnit T).left ≫ a'.left) ≫ F = (toUnit (Over.mk (T.hom ≫ f))).left ≫ a.left
      rw [Rosenlicht.toUnit_left, Rosenlicht.toUnit_left, Category.assoc, ha, ← Category.assoc]; rfl)
  have hpt : ∀ {T : Over S'} (x : T ⟶ G'), (x.left ≫ F) ≫ ((toUnit G ≫ a) * 𝟙 G).left =
      ((toUnit T ≫ a') * x).left ≫ F := fun {T} x => by
    refine (left_translate a (toBase hw x)).trans ?_
    rw [← hβ, ← h₁.mul]; rfl
  have hτ : ((toUnit G' ≫ a') * 𝟙 G').left ≫ F = F ≫ ((toUnit G ≫ a) * 𝟙 G).left :=
    (hpt (𝟙 G')).symm.trans (congrArg (· ≫ _) (Category.id_comp F))
  obtain ⟨w, hg, hv⟩ := exists_translate hτ w₁ h₁.gen
  obtain ⟨rig, hr, c₀, s₀, k₁, k₂, k₃, H⟩ := exists_isCPMap (hw := hw) ⟨⟨_, rg, hL, hrg⟩, c, sy, g₁, g₂, g₃⟩ h₁.mul _
    (pull_isLB P₁.L.isLB _) w hg
  have main : ∀ (T : Over S') (z : T.left) (J : (T.left ⟶ G'.left) → P₁.L.L.ι), Good P₁.L.L z J →
      (∀ x : T ⟶ G', val s₀ x.left z (fun r _ => J (r ≫ ((toUnit G' ≫ a') * 𝟙 G').left)) =
          val P₁.sym ((toUnit T ≫ a') * x).left z J * (val P₁.sym (toUnit T ≫ a').left z J)⁻¹) ∧
      ∀ x y u : T ⟶ G', cubV c₀ z (fun r _ => J (r ≫ ((toUnit G' ≫ a') * 𝟙 G').left)) x y u =
        cubV P₁.c z J x y ((toUnit T ≫ a') * u) * (cubV P₁.c z J x y (toUnit T ≫ a'))⁻¹ := by
    intro T z J hJ
    obtain ⟨I, hI⟩ := exists_good_pt Q.L.isLB z
    obtain ⟨W, hW⟩ : ∃ W : (T ⟶ G') → (T.left.presheaf.stalk z)ˣ,
      ∀ x, W x = gw w₁ x.left z (I (x.left ≫ F)) (J x.left) := ⟨_, fun _ => rfl⟩
    obtain ⟨-, a₂, a₃⟩ := h₁.vals T z J I hJ hI W hW
    obtain ⟨b, hb⟩ : ∃ b, b = toUnit T ≫ a' := ⟨_, rfl⟩
    have hbb : b⁻¹ = b := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← sq, hb, ← MonObj.comp_pow, h2, MonObj.comp_one]
    obtain ⟨-, b₂, b₃⟩ := H.vals T z (fun r _ => J (r ≫ ((toUnit G' ≫ a') * 𝟙 G').left))
      (fun r _ => I (r ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (fun r => mem_pull.2 (hJ (r ≫ _)))
      (fun r => mem_pull.2 (hI (r ≫ _))) (fun x => W (b * x)) (fun x => by
        refine Eq.trans ?_ (hv _ x.left z _ _ (hI ((x.left ≫ F) ≫ _)) (hJ (x.left ≫ _))).symm
        rw [hW, hpt, left_translate, hb])
    rw [← hb]
    refine ⟨fun x => ?_, fun x y u => ?_⟩
    · have e₀ := hs (Over.mk (T.hom ≫ f)) (toBase hw x) z I _ hI (fun _ => HEq.rfl)
      rw [← hβ, ← h₁.mul, ← hb] at e₀
      have e₁ : val Q.sym ((b * x).left ≫ F) z I * (val Q.sym (b.left ≫ F) z I)⁻¹ * W (b * x) =
          W (b * x⁻¹) * val s₀ x.left z (fun r _ => J (r ≫ ((toUnit G' ≫ a') * 𝟙 G').left)) :=
        (congrArg (· * W (b * x)) e₀).symm.trans (b₂ x)
      have e₂ := a₂ (b * x)
      have e₃ := a₂ b
      rw [mul_inv, hbb] at e₂
      rw [hbb] at e₃
      apply Additive.ofMul.injective
      have f₁ := congrArg Additive.ofMul e₁
      have f₂ := congrArg Additive.ofMul e₂
      have f₃ := congrArg Additive.ofMul e₃
      simp only [ofMul_mul, ofMul_inv] at f₁ f₂ f₃ ⊢
      linear_combination (norm := abel) f₂ - f₁ - f₃
    · have e₀ := hc (Over.mk (T.hom ≫ f)) (toBase hw x) (toBase hw y) (toBase hw u) z I _ hI (fun _ => HEq.rfl)
      rw [← hβ, ← h₁.mul, ← hb] at e₀
      obtain ⟨C, hC⟩ : ∃ C : (T ⟶ G') → (T.left.presheaf.stalk z)ˣ, ∀ v, C v =
        cubV Q.c (T := Over.mk (T.hom ≫ f)) z I (toBase hw x) (toBase hw y) (toBase hw v) := ⟨_, fun _ => rfl⟩
      have e₁ : C (b * u) * (C b)⁻¹ * W (b * (x * y)) * W (b * (x * u)) * W (b * (y * u)) * W (b * 1) =
          W (b * (x * y * u)) * W (b * x) * W (b * y) * W (b * u) *
            cubV c₀ z (fun r _ => J (r ≫ ((toUnit G' ≫ a') * 𝟙 G').left)) x y u := by
        rw [hC, hC]
        exact (congrArg (· * W (b * (x * y)) * W (b * (x * u)) * W (b * (y * u)) * W (b * 1)) e₀).symm.trans (b₃ x y u)
      have e₂ : ∀ v, C v * W (x * y) * W (x * v) * W (y * v) * W 1 =
          W (x * y * v) * W x * W y * W v * cubV P₁.c z J x y v := fun v => by rw [hC]; exact a₃ x y v
      have e₃ := e₂ (b * u)
      have e₄ := e₂ b
      rw [mul_left_comm x b, mul_left_comm y b, mul_left_comm (x * y) b] at e₃
      rw [mul_comm x b, mul_comm y b, mul_comm (x * y) b] at e₄
      rw [_root_.mul_one] at e₁
      apply Additive.ofMul.injective
      have f₁ := congrArg Additive.ofMul e₁
      have f₂ := congrArg Additive.ofMul e₃
      have f₃ := congrArg Additive.ofMul e₄
      simp only [ofMul_mul, ofMul_inv] at f₁ f₂ f₃ ⊢
      linear_combination (norm := abel) f₂ - f₁ - f₃
  refine ⟨⟨⟨_, rig, _, hr⟩, c₀, s₀, k₁, k₂, k₃⟩, ⟨w, H⟩, rfl, fun T x z J J' hJ h => ?_, fun T x y u z J J' hJ h => ?_⟩
  · obtain rfl : J' = fun r _ => J (r ≫ ((toUnit G' ≫ a') * 𝟙 G').left) := funext fun r => eq_of_heq (h r)
    exact (main T z J hJ).1 x
  · obtain rfl : J' = fun r _ => J (r ≫ ((toUnit G' ≫ a') * 𝟙 G').left) := funext fun r => eq_of_heq (h r)
    exact (main T z J hJ).2 x y u

theorem exists_section_pullback (f : S' ⟶ S) (a : 𝟙_ (Over S) ⟶ G) (h2 : a ^ 2 = 1) :
    ∃ a' : 𝟙_ (Over S') ⟶ (Over.pullback f).obj G, a'.left ≫ pullback.fst G.hom f = f ≫ a.left ∧ a' ^ 2 = 1 := by
  have h0 : (f ≫ a.left) ≫ G.hom = 𝟙 S' ≫ f := by
    rw [Category.assoc, Over.w a]; simp
  let a' : 𝟙_ (Over S') ⟶ (Over.pullback f).obj G :=
    Over.homMk (pullback.lift (f ≫ a.left) (𝟙 S') h0) (pullback.lift_snd _ _ _)
  have ha : a'.left ≫ pullback.fst G.hom f = f ≫ a.left := pullback.lift_fst _ _ _
  refine ⟨a', ha, ?_⟩
  let β := toBaseHom (toBase_mul_pullback G f) (𝟙_ (Over S'))
  have e : β a' = toUnit _ ≫ a := Over.OverMorphism.ext (by
    refine ha.trans ?_
    rw [Over.comp_left, Rosenlicht.toUnit_left]
    exact congrArg (· ≫ a.left) (Category.id_comp f).symm)
  have e' : β (a' ^ 2) = β 1 := by rw [map_pow, map_one, e, ← MonObj.comp_pow, h2, MonObj.comp_one]
  exact Over.OverMorphism.ext (pullback.hom_ext (congrArg (fun q => q.left) e')
    ((Over.w (a' ^ 2)).trans (Over.w (1 : 𝟙_ (Over S') ⟶ (Over.pullback f).obj G)).symm))

theorem exists_level_translate : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal R) D A G) (a : 𝟙_ (Over (Sp R)) ⟶ G), a ^ 2 = 1 →
    ∀ P : GlobalTheory.UU.CP G, P.L.L = U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left →
      (∀ (T : Over (Sp R)) (x : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → U.LG.L.ι)
        (J' : (T.left ⟶ G.left) → P.L.L.ι), Good U.LG.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left))) →
        val P.sym x.left z J' =
          val U.symG ((toUnit T ≫ a) * x).left z J * (val U.symG (toUnit T ≫ a).left z J)⁻¹) →
      (∀ (T : Over (Sp R)) (x y u : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → U.LG.L.ι)
        (J' : (T.left ⟶ G.left) → P.L.L.ι), Good U.LG.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left))) →
        cubV P.c z J' x y u = cubV U.cubG z J x y ((toUnit T ≫ a) * u) * (cubV U.cubG z J x y (toUnit T ≫ a))⁻¹) →
    ∀ P₁ : GlobalTheory.UU.CP (thickObj R (maximalIdeal R) 0 G),
      GlobalTheory.UU.IsLevelCP (maximalIdeal R) 0 P₁ (GlobalTheory.ValueForm.modelCP U.toUnifPre GlobalTheory.firstFiveLaws.1.globalFns) →
    ∃ (a₀ : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (0 + 1))))) ⟶ thickObj R (maximalIdeal R) 0 G)
      (P₀ : GlobalTheory.UU.CP (thickObj R (maximalIdeal R) 0 G)),
      a₀.left ≫ pullback.fst G.hom (thick R (maximalIdeal R) 0) = thick R (maximalIdeal R) 0 ≫ a.left ∧ a₀ ^ 2 = 1 ∧
      GlobalTheory.UU.IsLevelCP (maximalIdeal R) 0 P₀ P ∧
      P₀.L.L = P₁.L.L.pull ((toUnit (thickObj R (maximalIdeal R) 0 G) ≫ a₀) * 𝟙 (thickObj R (maximalIdeal R) 0 G)).left ∧
      (∀ (T : Over (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (0 + 1))))) (x : T ⟶ thickObj R (maximalIdeal R) 0 G) (z : T.left)
        (J : (T.left ⟶ (thickObj R (maximalIdeal R) 0 G).left) → P₁.L.L.ι)
        (J' : (T.left ⟶ (thickObj R (maximalIdeal R) 0 G).left) → P₀.L.L.ι), Good P₁.L.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit (thickObj R (maximalIdeal R) 0 G) ≫ a₀) * 𝟙 (thickObj R (maximalIdeal R) 0 G)).left))) →
        val P₀.sym x.left z J' =
          val P₁.sym ((toUnit T ≫ a₀) * x).left z J * (val P₁.sym (toUnit T ≫ a₀).left z J)⁻¹) ∧
      (∀ (T : Over (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (0 + 1))))) (x y u : T ⟶ thickObj R (maximalIdeal R) 0 G) (z : T.left)
        (J : (T.left ⟶ (thickObj R (maximalIdeal R) 0 G).left) → P₁.L.L.ι)
        (J' : (T.left ⟶ (thickObj R (maximalIdeal R) 0 G).left) → P₀.L.L.ι), Good P₁.L.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit (thickObj R (maximalIdeal R) 0 G) ≫ a₀) * 𝟙 (thickObj R (maximalIdeal R) 0 G)).left))) →
        cubV P₀.c z J' x y u = cubV P₁.c z J x y ((toUnit T ≫ a₀) * u) * (cubV P₁.c z J x y (toUnit T ≫ a₀))⁻¹) := by
  intro R _ _ _ D A G _ _ U a h2 P hP hs hc P₁ h₁
  obtain ⟨w₁, h₁⟩ := h₁
  obtain ⟨a₀, ha, h₀⟩ := exists_section_pullback (thick R (maximalIdeal R) 0) a h2
  obtain ⟨P₀, k⟩ := exists_translate_pull _ P P₁ a a₀ ha h₀ hP hs hc h₁
  exact ⟨a₀, P₀, ha, h₀, k⟩

end GlobalTheory.Mum.TranslateLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleFiberProductOverMulTwoIsPullback
section
set_option autoImplicit false
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwoTors.TripleProd

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

def pt {T : Over S} (a b c : T ⟶ A) (h₁ : a ≫ sq A = b ≫ sq A) (h₂ : b ≫ sq A = c ≫ sq A) : T ⟶ tripO A :=
  Over.homMk (GlobalTheory.PolRoot.tri (sq A).left a.left b.left c.left (congrArg CommaMorphism.left h₁)
    (congrArg CommaMorphism.left h₂)) (by
      show GlobalTheory.PolRoot.tri _ _ _ _ _ _ ≫ pullback.fst _ _ ≫ pullback.fst _ _ ≫ A.hom = _
      rw [GlobalTheory.PolRoot.tri, pullback.lift_fst_assoc, pullback.lift_fst_assoc, Over.w])

theorem pt_t₁ {T : Over S} (a b c : T ⟶ A) (h₁ h₂) : pt a b c h₁ h₂ ≫ t₁ A = a :=
  Over.OverMorphism.ext (by
    show GlobalTheory.PolRoot.tri _ _ _ _ _ _ ≫ pullback.fst _ _ ≫ pullback.fst _ _ = _
    rw [GlobalTheory.PolRoot.tri, pullback.lift_fst_assoc, pullback.lift_fst])

theorem pt_t₂ {T : Over S} (a b c : T ⟶ A) (h₁ h₂) : pt a b c h₁ h₂ ≫ t₂ A = b :=
  Over.OverMorphism.ext (by
    show GlobalTheory.PolRoot.tri _ _ _ _ _ _ ≫ pullback.fst _ _ ≫ pullback.snd _ _ = _
    rw [GlobalTheory.PolRoot.tri, pullback.lift_fst_assoc, pullback.lift_snd])

theorem pt_t₃ {T : Over S} (a b c : T ⟶ A) (h₁ h₂) : pt a b c h₁ h₂ ≫ t₃ A = c :=
  Over.OverMorphism.ext (by
    show GlobalTheory.PolRoot.tri _ _ _ _ _ _ ≫ pullback.snd _ _ ≫ pullback.snd _ _ = _
    rw [GlobalTheory.PolRoot.tri, pullback.lift_snd_assoc, pullback.lift_snd])

theorem ext₃ {T : Over S} {m n : T ⟶ tripO A} (h₁ : m ≫ t₁ A = n ≫ t₁ A) (h₂ : m ≫ t₂ A = n ≫ t₂ A)
    (h₃ : m ≫ t₃ A = n ≫ t₃ A) : m = n := by
  have e₁ : m.left ≫ pullback.fst _ _ ≫ pullback.fst _ _ = n.left ≫ pullback.fst _ _ ≫ pullback.fst _ _ :=
    congrArg CommaMorphism.left h₁
  have e₂ : m.left ≫ pullback.fst _ _ ≫ pullback.snd _ _ = n.left ≫ pullback.fst _ _ ≫ pullback.snd _ _ :=
    congrArg CommaMorphism.left h₂
  have e₃ : m.left ≫ pullback.snd _ _ ≫ pullback.snd _ _ = n.left ≫ pullback.snd _ _ ≫ pullback.snd _ _ :=
    congrArg CommaMorphism.left h₃
  have e₄ := e₂
  rw [pullback.condition] at e₄
  refine Over.OverMorphism.ext (pullback.hom_ext (pullback.hom_ext ?_ ?_) (pullback.hom_ext ?_ ?_))
  · exact (Category.assoc _ _ _).trans (e₁.trans (Category.assoc _ _ _).symm)
  · exact (Category.assoc _ _ _).trans (e₂.trans (Category.assoc _ _ _).symm)
  · exact (Category.assoc _ _ _).trans (e₄.trans (Category.assoc _ _ _).symm)
  · exact (Category.assoc _ _ _).trans (e₃.trans (Category.assoc _ _ _).symm)

theorem comp_ψ_fst {T : Over S} (m : T ⟶ tripO A) :
    ((m ≫ ψ A) ≫ fst _ _) ≫ incl A = (m ≫ t₁ A)⁻¹ * (m ≫ t₂ A) := by
  rw [Category.assoc, Category.assoc, ψ, lift_fst_assoc, dif_incl, MonObj.comp_mul, GrpObj.comp_inv]

theorem comp_ψ_snd {T : Over S} (m : T ⟶ tripO A) :
    ((m ≫ ψ A) ≫ snd _ _) ≫ incl A = (m ≫ t₂ A)⁻¹ * (m ≫ t₃ A) := by
  rw [Category.assoc, Category.assoc, ψ, lift_snd_assoc, dif_incl, MonObj.comp_mul, GrpObj.comp_inv]

theorem ext₂ {T : Over S} {m n : T ⟶ tripO A} (h₁ : m ≫ t₁ A = n ≫ t₁ A) (h : m ≫ ψ A = n ≫ ψ A) : m = n := by
  have e₂ := comp_ψ_fst m
  have e₃ := comp_ψ_snd m
  rw [h, comp_ψ_fst, h₁] at e₂
  have h₂ : m ≫ t₂ A = n ≫ t₂ A := (mul_left_cancel e₂).symm
  rw [h, comp_ψ_snd, h₂] at e₃
  exact ext₃ h₁ h₂ (mul_left_cancel e₃).symm

theorem mul_sq {T : Over S} (a : T ⟶ A) (x : T ⟶ Two A) : a ≫ sq A = (a * (x ≫ incl A)) ≫ sq A := by
  rw [comp_sq, comp_sq, mul_pow, incl_sq, _root_.mul_one]

theorem exists_pt {T : Over S} (a : T ⟶ A) (q : T ⟶ Two A ⊗ Two A) :
    ∃ m : T ⟶ tripO A, m ≫ t₁ A = a ∧ m ≫ ψ A = q := by
  refine ⟨pt a (a * ((q ≫ fst _ _) ≫ incl A)) ((a * ((q ≫ fst _ _) ≫ incl A)) * ((q ≫ snd _ _) ≫ incl A))
    (mul_sq _ _) (mul_sq _ _), pt_t₁ _ _ _ _ _, ?_⟩
  refine CartesianMonoidalCategory.hom_ext _ _ (two_ext ?_) (two_ext ?_)
  · rw [comp_ψ_fst, pt_t₁, pt_t₂, inv_mul_cancel_left]
  · rw [comp_ψ_snd, pt_t₂, pt_t₃, inv_mul_cancel_left]

theorem isPullback {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] :
    IsPullback (t₁ A).left (ψ A).left A.hom (Two A ⊗ Two A).hom := by
  have w : (t₁ A).left ≫ A.hom = (ψ A).left ≫ (Two A ⊗ Two A).hom := (Over.w _).trans (Over.w _).symm
  have key : ∀ s : PullbackCone A.hom (Two A ⊗ Two A).hom, ∃ l : s.pt ⟶ (tripO A).left,
      l ≫ (t₁ A).left = s.fst ∧ l ≫ (ψ A).left = s.snd := fun s => by
    obtain ⟨m, h₁, h₂⟩ := exists_pt (T := Over.mk (s.fst ≫ A.hom)) (Over.homMk s.fst rfl)
      (Over.homMk s.snd s.condition.symm)
    exact ⟨m.left, congrArg CommaMorphism.left h₁, congrArg CommaMorphism.left h₂⟩
  choose l hl₁ hl₂ using key
  refine ⟨⟨w⟩, ⟨PullbackCone.IsLimit.mk w l hl₁ hl₂ fun s m h₁ h₂ => ?_⟩⟩
  have hw : ∀ k : s.pt ⟶ (tripO A).left, k ≫ (t₁ A).left = s.fst → k ≫ (tripO A).hom = s.fst ≫ A.hom :=
    fun k hk => by rw [← hk, Category.assoc, Over.w]
  have e : (Over.homMk m (hw m h₁) : Over.mk (s.fst ≫ A.hom) ⟶ tripO A) = Over.homMk (l s) (hw _ (hl₁ s)) :=
    ext₂ (Over.OverMorphism.ext (h₁.trans (hl₁ s).symm)) (Over.OverMorphism.ext (h₂.trans (hl₂ s).symm))
  exact congrArg CommaMorphism.left e

end GlobalTheory.TwoTors.TripleProd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationCompleteTraitBaseChangeFiniteExtStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisation_completeTrait_baseChange_finite_ext : ∀ (R R₂ W W₂ : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R₂] [IsDomain R₂] [IsLocalRing R₂] [CommRing W] [IsDomain W] [IsLocalRing W] [CommRing W₂] [IsDomain W₂] [IsLocalRing W₂] (ρ : R →+* R₂) (φ : R →+* W) (σ : W →+* W₂) (φ₂ : R₂ →+* W₂), Base R → GlobalTheory.LN.CDvr W → GlobalTheory.LN.CDvr W₂ → FinExt σ → IsLocalHom σ → φ₂.comp ρ = σ.comp φ → Function.Injective φ₂ → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (G₂ : Over (Sp R₂)) [GrpObj G₂] [IsCommMonObj G₂] (β : G₂.left ⟶ G.left), IsGrpPullback G₂ G (spMap ρ) β → ∀ (GW : Over (Sp W)) [GrpObj GW] [IsCommMonObj GW] (βW : GW.left ⟶ G.left), IsGrpPullback GW G (spMap φ) βW → ∀ (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW), ∃ (GW' : Over (Sp W₂)) (_ : GrpObj GW') (_ : IsCommMonObj GW') (βW' : GW'.left ⟶ G₂.left) (τ : GW'.left ⟶ GW.left) (DW' : DegData W₂ (maximalIdeal W₂)) (AW' : PolAV (Sp (FractionRing W₂))) (UW' : Unif (maximalIdeal W₂) DW' AW' GW') (κ : pullback GW'.hom (jK W₂) ⟶ pullback G₂.hom (jK R₂)), IsGrpPullback GW' G₂ (spMap φ₂) βW' ∧ IsGrpPullback GW' GW (spMap σ) τ ∧ βW' ≫ β = τ ≫ βW ∧ κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ βW' ∧ LBIso (UW'.LG.L.pull (pullback.fst GW'.hom (jK W₂))) (UW.LG.L.pull (pullback.fst GW'.hom (jK W₂) ≫ τ)) := by
  first | exact @GlobalTheory.Mum.unif_trait_baseChange | exact GlobalTheory.Mum.unif_trait_baseChange | (intros; apply GlobalTheory.Mum.unif_trait_baseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupGaloisMapOne
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

open GlobalTheory.TorsionFormCompare in

theorem galMap_one : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), GalMap hD U' 1 (𝟙 _) := by
  intro R _ _ _ _ R' _ _ _ ρ hρ D D' hD A' G' _ _ _ U'
  obtain ⟨W, hW, hψ⟩ := GlobalTheory.psiOnExists R' (maximalIdeal R') hρ.1 D'
  obtain ⟨h, hid⟩ := exists_isIdPull R' D'.toPre W hW hψ
  have gp : IsGrpPullback G' G' (specOf (RingHom.id R')) (𝟙 _) :=
    (@isGrpPullback_of_iso _ _ _ _ _ (Iso.refl G') (inferInstanceAs (IsMonHom (𝟙 G')))).congr (specOf_id R').symm rfl
  obtain ⟨bc, -, hbc⟩ := grpPullback_iso gp (isGrpPullback_pullback G' (specOf (RingHom.id R')))
  have hP : PullOver hD h := ⟨hid.1, fun b c _ hc => by rw [hc, hid.2.1, Category.id_comp]⟩
  exact ⟨gp, h, bc, hbc, isPullUnif_refl U' h hid bc hbc, hP⟩

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedSemiAbelianSplitModMaximalIdealStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformised_semiAbelian_split_mod_maximalIdeal : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))), Unif (maximalIdeal V₁) D₀ A₀ G₀ → IsSemiAbelian G₀ → GlobalTheory.LN.SplitOver G₀ (maximalIdeal V₁) := by
  first | exact @GlobalTheory.SplitRed.splitOver_of_unif | exact GlobalTheory.SplitRed.splitOver_of_unif | (intros; apply GlobalTheory.SplitRed.splitOver_of_unif <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryGroupMeasureDecompositionStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_group_measure_decomposition : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (κ : Type) [Fintype κ] (p q : κ → ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (σ : κ ≃ Ψ) (A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ) (e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r) (a₀ : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ)) (π : (∀ ρ, UpqT (p ρ) (q ρ)) → realSU Ψ G) (m : ∀ ρ, Measure (UpqT (p ρ) (q ρ))), 1 ≤ r → 1 ≤ Ψ.card → IsIdent p q Ψ G x σ A e → Continuous π → IsProj p q Ψ G σ A a₀ π → (∀ (s : realSU Ψ G) (b₀ : ∀ ρ, UpqT (p ρ) (q ρ)), (∀ ρ, UpqT.mat (b₀ ρ) * A ρ = A ρ * ((s.1 (σ ρ) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) → ∀ b, π (b₀ * b) = s * π b) → (∀ ρ, IsMinf (m ρ)) → ∀ S : Set (realSU Ψ G), MeasurableSet S → Measure.pi m (π ⁻¹' S) ≤ ENNReal.ofReal ((1000 * (Ψ.card : ℝ) * (r : ℝ) ^ 3) ^ (Ψ.card * r ^ 2)) * riemHaar Ψ G x S := by
  first | exact @GlobalTheory.CovTop.VolUp.MassUp.massUp | exact GlobalTheory.CovTop.VolUp.MassUp.massUp | (intros; apply GlobalTheory.CovTop.VolUp.MassUp.massUp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorBundleLocallyFreeStatement
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vector_bundle_locally_free : ∀ (B : Scheme.{0}) (ι : Type) [Finite ι] (E : ι → B.Modules) (r : ι → ℕ), (∀ a, GlobalTheory.VB.IsVB (E a) (r a)) → ∀ b : B, ∃ U : B.Opens, b ∈ U ∧ ∀ a, Nonempty ((Scheme.Modules.pullback U.ι).obj (E a) ≅ SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin (r a))) := by
  first | exact @GlobalTheory.VB.exists_open_isVB_free_finite | exact GlobalTheory.VB.exists_open_isVB_free_finite | (intros; apply GlobalTheory.VB.exists_open_isVB_free_finite <;> assumption)
end

