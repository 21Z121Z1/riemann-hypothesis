import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0019
import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0033
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0027
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GramSpace
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0026
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0037
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0041
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0039
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroSplitOfLocalAndSum
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ModulusPosOfThirdHypothesis
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0124
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumFinitePlacesLeSumOverPrimes
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0002
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0032

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowPullbackSecModelUniversalBijective
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.SecTie

section Gen
variable {X Y Z X' X₁ X₂ Y₁ Y₂ B B₀ : Scheme.{0}} {L' : LB X'} {L₁ : LB X₁} {L₂ : LB X₂} {F₁ : X' ⟶ X₁} {F₂ : X' ⟶ X₂}

abbrev PSec (L : LB X) (φ : Y ⟶ X) (q : ℕ) : Type :=
  LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => (q : ℤ)))

theorem mem_one {L : LB X} {φ : Y ⟶ X} {j : Fin 1 → L.ι} {y : Y} :
    y ∈ LB.wchart L (fun _ : Fin 1 => φ) j ↔ φ y ∈ L.U (j 0) :=
  ⟨fun h => Set.mem_iInter.1 h 0, fun h => Set.mem_iInter.2 fun k => by
    obtain rfl : k = 0 := Subsingleton.elim _ _
    exact h⟩

theorem trans_one {L : LB X} {φ : Y ⟶ X} {q : ℕ} (s : PSec L φ q) (r : Z ⟶ Y) (z : Z) {j j' : Fin 1 → L.ι}
    (hj : r z ∈ LB.wchart L (fun _ : Fin 1 => φ) j) (hj' : r z ∈ LB.wchart L (fun _ : Fin 1 => φ) j') :
    gs r z (LB.wchart L (fun _ : Fin 1 => φ) j) (s.f j) =
      (gm (r ≫ φ) z (L.U (j 0) ⊓ L.U (j' 0)) (L.g (j 0) (j' 0)) ^ q).val *
        gs r z (LB.wchart L (fun _ : Fin 1 => φ) j') (s.f j') := by
  rw [sec_trans s r z hj hj', trF, Fin.prod_univ_one, zpow_natCast]

def ratio (w₁ : LB.Iso L' (L₁.pull F₁)) (w₂ : LB.Iso L' (L₂.pull F₂)) (r : Z ⟶ X') (z : Z) (j₁ : L₁.ι) (j₂ : L₂.ι)
    (k : L'.ι) : (Z.presheaf.stalk z)ˣ := gw w₁ r z j₁ k * (gw w₂ r z j₂ k)⁻¹

theorem ratio_trans {w₁ : LB.Iso L' (L₁.pull F₁)} {w₂ : LB.Iso L' (L₂.pull F₂)} (h₁ : PGen w₁) (h₂ : PGen w₂)
    (r : Z ⟶ X') (z : Z) {j₁ j₁' : L₁.ι} {j₂ j₂' : L₂.ι} {k k' : L'.ι} (a : F₁ (r z) ∈ L₁.U j₁) (a' : F₁ (r z) ∈ L₁.U j₁')
    (b : F₂ (r z) ∈ L₂.U j₂) (b' : F₂ (r z) ∈ L₂.U j₂') (c : r z ∈ L'.U k) (c' : r z ∈ L'.U k') :
    ratio w₁ w₂ r z j₁ j₂ k * gm (r ≫ F₂) z _ (L₂.g j₂ j₂') = gm (r ≫ F₁) z _ (L₁.g j₁ j₁') * ratio w₁ w₂ r z j₁' j₂' k' := by
  rw [ratio, ratio, h₁ _ r z j₁ j₁' k k' a a' c c', h₂ _ r z j₂ j₂' k k' b b' c c']
  generalize gm (r ≫ F₁) z _ (L₁.g j₁ j₁') = A
  generalize gm (r ≫ F₂) z _ (L₂.g j₂ j₂') = A'
  generalize gm r z _ (L'.g k k') = C
  generalize gw w₁ r z j₁' k' = D
  generalize gw w₂ r z j₂' k' = D'
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem exists_transport {w₁ : LB.Iso L' (L₁.pull F₁)} {w₂ : LB.Iso L' (L₂.pull F₂)} (h₁ : PGen w₁) (h₂ : PGen w₂)
    (hL' : L'.IsLB) (hL₁ : L₁.IsLB) (hL₂ : L₂.IsLB) {φ₁ : Y₁ ⟶ X₁} {φ₂ : Y₂ ⟶ X₂} (ρ : Y₁ ⟶ X') (e : Y₁ ⟶ Y₂)
    (e₁ : ρ ≫ F₁ = φ₁) (e₂ : e ≫ φ₂ = ρ ≫ F₂) (q : ℕ) (s₂ : PSec L₂ φ₂ q) :
    ∃ s₁ : PSec L₁ φ₁ q, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y₁) (z : Z) (j₁ : Fin 1 → L₁.ι) (j₂ : Fin 1 → L₂.ι) (k : L'.ι),
      r z ∈ LB.wchart L₁ (fun _ : Fin 1 => φ₁) j₁ → e (r z) ∈ LB.wchart L₂ (fun _ : Fin 1 => φ₂) j₂ → ρ (r z) ∈ L'.U k →
      gs r z (LB.wchart L₁ (fun _ : Fin 1 => φ₁) j₁) (s₁.f j₁) =
        (ratio w₁ w₂ (r ≫ ρ) z (j₁ 0) (j₂ 0) k ^ q).val *
          gs (r ≫ e) z (LB.wchart L₂ (fun _ : Fin 1 => φ₂) j₂) (s₂.f j₂) := by
  subst e₁
  have m₂ : ∀ (y : Y₁) (j₂ : Fin 1 → L₂.ι), e y ∈ LB.wchart L₂ (fun _ : Fin 1 => φ₂) j₂ ↔ F₂ (ρ y) ∈ L₂.U (j₂ 0) :=
    fun y j₂ => mem_one.trans (iff_of_eq (congrArg (fun f => f y ∈ L₂.U (j₂ 0)) e₂))
  have m₁ : ∀ (y : Y₁) (j₁ : Fin 1 → L₁.ι), y ∈ LB.wchart L₁ (fun _ : Fin 1 => ρ ≫ F₁) j₁ ↔ F₁ (ρ y) ∈ L₁.U (j₁ 0) :=
    fun y j₁ => mem_one
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y₁) (z : Z) (j₁ j₁' : Fin 1 → L₁.ι) (j₂ j₂' : Fin 1 → L₂.ι) (k k' : L'.ι),
      r z ∈ LB.wchart L₁ (fun _ : Fin 1 => ρ ≫ F₁) j₁ → e (r z) ∈ LB.wchart L₂ (fun _ : Fin 1 => φ₂) j₂ → ρ (r z) ∈ L'.U k →
      r z ∈ LB.wchart L₁ (fun _ : Fin 1 => ρ ≫ F₁) j₁' → e (r z) ∈ LB.wchart L₂ (fun _ : Fin 1 => φ₂) j₂' → ρ (r z) ∈ L'.U k' →
      (ratio w₁ w₂ (r ≫ ρ) z (j₁ 0) (j₂ 0) k ^ q).val *
          gs (r ≫ e) z (LB.wchart L₂ (fun _ : Fin 1 => φ₂) j₂) (s₂.f j₂) =
      (gm (r ≫ ρ ≫ F₁) z (L₁.U (j₁ 0) ⊓ L₁.U (j₁' 0)) (L₁.g (j₁ 0) (j₁' 0)) ^ q).val *
        ((ratio w₁ w₂ (r ≫ ρ) z (j₁' 0) (j₂' 0) k' ^ q).val *
          gs (r ≫ e) z (LB.wchart L₂ (fun _ : Fin 1 => φ₂) j₂') (s₂.f j₂')) := by
    intro Z r z j₁ j₁' j₂ j₂' k k' a b c a' b' c'
    have t := ratio_trans h₁ h₂ (r ≫ ρ) z ((m₁ _ _).1 a) ((m₁ _ _).1 a') ((m₂ _ _).1 b) ((m₂ _ _).1 b') c c'
    rw [trans_one s₂ (r ≫ e) z b b', Category.assoc, e₂, ← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul,
      ← Units.val_mul, ← mul_pow, ← mul_pow]
    rw [Category.assoc, Category.assoc] at t
    rw [t]
  have glue : ∀ j₁ : Fin 1 → L₁.ι, ∃ a : Γ(Y₁, LB.wchart L₁ (fun _ : Fin 1 => ρ ≫ F₁) j₁),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y₁) (z : Z) (j₂ : Fin 1 → L₂.ι) (k : L'.ι),
      r z ∈ LB.wchart L₁ (fun _ : Fin 1 => ρ ≫ F₁) j₁ → e (r z) ∈ LB.wchart L₂ (fun _ : Fin 1 => φ₂) j₂ → ρ (r z) ∈ L'.U k →
      gs r z (LB.wchart L₁ (fun _ : Fin 1 => ρ ≫ F₁) j₁) a =
        (ratio w₁ w₂ (r ≫ ρ) z (j₁ 0) (j₂ 0) k ^ q).val *
          gs (r ≫ e) z (LB.wchart L₂ (fun _ : Fin 1 => φ₂) j₂) (s₂.f j₂) := by
    intro j₁
    let W : (Fin 1 → L₂.ι) × L'.ι → Y₁.Opens := fun p =>
      LB.wchart L₁ (fun _ : Fin 1 => ρ ≫ F₁) j₁ ⊓ e ⁻¹ᵁ LB.wchart L₂ (fun _ : Fin 1 => φ₂) p.1 ⊓ ρ ⁻¹ᵁ L'.U p.2
    have l₁ : ∀ p, W p ≤ ρ ⁻¹ᵁ ((L₁.pull F₁).U (fun _ => j₁ 0) ⊓ L'.U p.2) := fun p y hy =>
      ⟨mem_pull.2 ((m₁ _ _).1 hy.1.1), hy.2⟩
    have l₂ : ∀ p, W p ≤ ρ ⁻¹ᵁ ((L₂.pull F₂).U (fun _ => p.1 0) ⊓ L'.U p.2) := fun p y hy =>
      ⟨mem_pull.2 ((m₂ _ _).1 hy.1.2), hy.2⟩
    have l₃ : ∀ p, W p ≤ e ⁻¹ᵁ LB.wchart L₂ (fun _ : Fin 1 => φ₂) p.1 := fun p y hy => hy.1.2
    obtain ⟨u, hu⟩ : ∃ u : ∀ p, Γ(Y₁, W p), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y₁) (z : Z) p, r z ∈ W p →
        gs r z (W p) (u p) = (ratio w₁ w₂ (r ≫ ρ) z (j₁ 0) (p.1 0) p.2 ^ q).val *
          gs (r ≫ e) z (LB.wchart L₂ (fun _ : Fin 1 => φ₂) p.1) (s₂.f p.1) :=
      ⟨fun p => ((res (l₁ p) (pullU ρ _ (w₁.s (fun _ => j₁ 0, p.2))) *
          (res (l₂ p) (pullU ρ _ (w₂.s (fun _ => p.1 0, p.2))))⁻¹) ^ q).val *
          (Y₁.presheaf.map (homOfLE (l₃ p)).op).hom ((e.app _).hom (s₂.f p.1)), fun Z r z p hz => by
        refine (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) ((gs_unit r z _ hz _).trans (congrArg Units.val ?_))
          ((gs_res r z _ hz _).trans (gs_pull r e z _ (l₃ p hz) _)))
        rw [map_pow, map_mul, map_inv, gm_res r z _ hz, gm_res r z _ hz]
        exact congrArg (· ^ q) (congrArg₂ (· * ·)
          (gm_pull r ρ z ((L₁.pull F₁).U (fun _ => j₁ 0) ⊓ L'.U p.2) (l₁ p hz) _)
          (congrArg (·⁻¹) (gm_pull r ρ z ((L₂.pull F₂).U (fun _ => p.1 0) ⊓ L'.U p.2) (l₂ p hz) _)))⟩
    obtain ⟨a, ha, -⟩ := Y₁.sheaf.existsUnique_gluing' W (LB.wchart L₁ (fun _ : Fin 1 => ρ ≫ F₁) j₁)
      (fun p => homOfLE (inf_le_left.trans inf_le_left)) (fun y hy => by
        obtain ⟨k, hk⟩ := exists_chart hL' (ρ y)
        obtain ⟨j, hj⟩ := exists_chart hL₂ (F₂ (ρ y))
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨(fun _ => j, k), ⟨hy, (m₂ _ _).2 hj⟩, hk⟩) u
      (fun p p' => fn_ext (V := W p ⊓ W p') fun y hy => by
        refine (gs_res (𝟙 Y₁) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 Y₁) y inf_le_right hy _).symm)
        rw [hu _ _ y p hy.1, hu _ _ y p' hy.2,
          key _ (𝟙 Y₁) y j₁ j₁ p.1 p'.1 p.2 p'.2 hy.1.1.1 hy.1.1.2 hy.1.2 hy.1.1.1 hy.2.1.2 hy.2.2,
          gm_self hL₁ (𝟙 Y₁ ≫ ρ ≫ F₁) y ((m₁ _ _).1 hy.1.1.1), one_pow, Units.val_one, _root_.one_mul])
    refine ⟨a, fun Z r z j₂ k a₁ a₂ a₃ => ?_⟩
    have hz : r z ∈ W (j₂, k) := ⟨⟨a₁, a₂⟩, a₃⟩
    exact (gs_res r z (inf_le_left.trans inf_le_left) hz a).symm.trans ((congrArg (gs r z (W (j₂, k))) (ha (j₂, k))).trans
      (hu Z r z (j₂, k) hz))
  choose a ha using glue
  refine ⟨⟨a, fun (j j' : Fin 1 → L₁.ι) => fn_ext fun y hy => ?_⟩, fun Z r z j₁ j₂ k => ha j₁ Z r z j₂ k⟩
  obtain ⟨k, hk⟩ := exists_chart hL' (ρ y)
  obtain ⟨i, hi⟩ := exists_chart hL₂ (F₂ (ρ y))
  have hi' := (m₂ y (fun _ => i)).2 hi
  have e₃ := gm_linComb L₁ (fun _ : Fin 1 => ρ ≫ F₁) (fun _ => (q : ℤ)) (𝟙 Y₁) y j j' hy.1 hy.2
  rw [Fin.prod_univ_one, zpow_natCast] at e₃
  have e₄ := ha j _ (𝟙 Y₁) y (fun _ => i) k hy.1 hi' hk
  have e₅ := ha j' _ (𝟙 Y₁) y (fun _ => i) k hy.2 hi' hk
  have e₆ := key _ (𝟙 Y₁) y j j' (fun _ => i) (fun _ => i) k k hy.1 hi' hk hy.2 hi' hk
  rw [← e₄, ← e₅, ← e₃] at e₆
  exact (gs_res (𝟙 Y₁) y _ hy _).trans (e₆.trans ((gs_mul (𝟙 Y₁) y _ hy _ _).trans (congrArg₂ (· * ·)
    (gs_unit (𝟙 Y₁) y _ hy _) (gs_res (𝟙 Y₁) y _ hy _))).symm)

def Comparison₂ (w₁ : LB.Iso L' (L₁.pull F₁)) (w₂ : LB.Iso L' (L₂.pull F₂)) (φ₁ : Y₁ ⟶ X₁) (φ₂ : Y₂ ⟶ X₂) (p₁ : Y₁ ⟶ B)
    (p₂ : Y₂ ⟶ B) (f : B ⟶ B₀) (π : X' ⟶ B₀) (q : ℕ) (s₂ : PSec L₂ φ₂ q) (s₁ : PSec L₁ φ₁ q) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z₂ : Z ⟶ Y₂) (z₁ : Z ⟶ Y₁), z₂ ≫ φ₂ = r ≫ F₂ → z₁ ≫ φ₁ = r ≫ F₁ →
    z₂ ≫ p₂ = z₁ ≫ p₁ → z₁ ≫ p₁ ≫ f = r ≫ π →
    ∀ (z : Z) (J₁ : (Z ⟶ X₁) → L₁.ι) (J₂ : (Z ⟶ X₂) → L₂.ι) (k : L'.ι), Good L₁ z J₁ → Good L₂ z J₂ → r z ∈ L'.U k →
      sval s₂ z₂ z J₂ * ((gw w₁ r z (J₁ (r ≫ F₁)) k).val) ^ q = sval s₁ z₁ z J₁ * ((gw w₂ r z (J₂ (r ≫ F₂)) k).val) ^ q

theorem Comparison₂.symm {w₁ : LB.Iso L' (L₁.pull F₁)} {w₂ : LB.Iso L' (L₂.pull F₂)} {φ₁ : Y₁ ⟶ X₁} {φ₂ : Y₂ ⟶ X₂} {p₁ : Y₁ ⟶ B}
    {p₂ : Y₂ ⟶ B} {f : B ⟶ B₀} {π : X' ⟶ B₀} {q : ℕ} {s₂ : PSec L₂ φ₂ q} {s₁ : PSec L₁ φ₁ q}
    (h : Comparison₂ w₁ w₂ φ₁ φ₂ p₁ p₂ f π q s₂ s₁) : Comparison₂ w₂ w₁ φ₂ φ₁ p₂ p₁ f π q s₁ s₂ :=
  fun Z r z₁ z₂ a b c d z J₂ J₁ k g₂ g₁ hk =>
    (h Z r z₂ z₁ b a c.symm (by rw [← d, ← Category.assoc, c, Category.assoc]) z J₁ J₂ k g₁ g₂ hk).symm

theorem existsUnique_tie {w₁ : LB.Iso L' (L₁.pull F₁)} {w₂ : LB.Iso L' (L₂.pull F₂)} (h₁ : PGen w₁) (h₂ : PGen w₂)
    (hL' : L'.IsLB) (hL₁ : L₁.IsLB) (hL₂ : L₂.IsLB) {φ₁ : Y₁ ⟶ X₁} {φ₂ : Y₂ ⟶ X₂} {p₁ : Y₁ ⟶ B}
    {p₂ : Y₂ ⟶ B} {f : B ⟶ B₀} {π : X' ⟶ B₀} {S₁ S₂ : Scheme.{0}} {π₁ : X₁ ⟶ S₁} {π₂ : X₂ ⟶ S₂} {b₁ : B₀ ⟶ S₁}
    {b₂ : B₀ ⟶ S₂} (c₁ : IsPullback F₁ π π₁ b₁) (c₂ : IsPullback F₂ π π₂ b₂) (d₁ : φ₁ ≫ π₁ = p₁ ≫ f ≫ b₁)
    (d₂ : IsPullback φ₂ p₂ π₂ (f ≫ b₂)) (q : ℕ) (s₂ : PSec L₂ φ₂ q) :
    ∃! s₁ : PSec L₁ φ₁ q, Comparison₂ w₁ w₂ φ₁ φ₂ p₁ p₂ f π q s₂ s₁ := by
  obtain ⟨ρ, r₁, r₂⟩ : ∃ ρ : Y₁ ⟶ X', ρ ≫ F₁ = φ₁ ∧ ρ ≫ π = p₁ ≫ f :=
    ⟨c₁.lift φ₁ (p₁ ≫ f) (by rw [d₁, Category.assoc]), c₁.lift_fst _ _ _, c₁.lift_snd _ _ _⟩
  obtain ⟨e, e₁, e₂⟩ : ∃ e : Y₁ ⟶ Y₂, e ≫ φ₂ = ρ ≫ F₂ ∧ e ≫ p₂ = p₁ :=
    ⟨d₂.lift (ρ ≫ F₂) p₁ (by rw [Category.assoc, c₂.w, ← Category.assoc, r₂, Category.assoc]), d₂.lift_fst _ _ _,
      d₂.lift_snd _ _ _⟩
  obtain ⟨s₁, hs⟩ := exists_transport h₁ h₂ hL' hL₁ hL₂ ρ e r₁ e₁ q s₂
  have T : Comparison₂ w₁ w₂ φ₁ φ₂ p₁ p₂ f π q s₂ s₁ := by
    intro Z r z₂ z₁ a b c d z J₁ J₂ k g₁ g₂ hk
    obtain rfl : r = z₁ ≫ ρ := c₁.hom_ext (by rw [Category.assoc, r₁, b]) (by rw [Category.assoc, r₂, d])
    obtain rfl : z₂ = z₁ ≫ e := d₂.hom_ext (by rw [a, Category.assoc, Category.assoc, e₁])
      (by rw [c, Category.assoc, e₂])
    have := hs Z z₁ z (fun _ => J₁ (z₁ ≫ φ₁)) (fun _ => J₂ ((z₁ ≫ e) ≫ φ₂)) k (g₁.mem (fun _ : Fin 1 => φ₁) z₁)
      (g₂.mem (fun _ : Fin 1 => φ₂) (z₁ ≫ e)) hk
    rw [← a, ← b]
    refine Eq.trans ?_ (congrArg (· * _) this).symm
    rw [ratio, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, mul_right_comm, ← Units.val_mul, ← mul_pow,
      inv_mul_cancel_right, _root_.mul_comm]
    rfl
  refine ⟨s₁, T, fun s₁' T' => ?_⟩
  have hf : ∀ j, s₁'.f j = s₁.f j := sec_ext_val hL₁ fun y J₁ g₁ => by
    choose J₂ g₂ using fun χ : Y₁ ⟶ X₂ => exists_chart hL₂ (χ y)
    obtain ⟨k, hk⟩ := exists_chart hL' (ρ y)
    have a := T Y₁ ρ e (𝟙 _) e₁ (by rw [Category.id_comp, r₁]) (by rw [Category.id_comp, e₂])
      (by rw [Category.id_comp, r₂]) y J₁ J₂ k g₁ g₂ hk
    have a' := T' Y₁ ρ e (𝟙 _) e₁ (by rw [Category.id_comp, r₁]) (by rw [Category.id_comp, e₂])
      (by rw [Category.id_comp, r₂]) y J₁ J₂ k g₁ g₂ hk
    exact ((Units.isUnit _).pow q).mul_right_cancel (a'.symm.trans a)
  obtain ⟨f', _⟩ := s₁'
  obtain ⟨f'', _⟩ := s₁
  obtain rfl : f' = f'' := funext hf
  rfl

theorem sval_scal {L : LB X} {φ : Y ⟶ X} {q : ℕ} {s s' : PSec L φ q} {p : Y ⟶ B} {u : Γ(B, ⊤)}
    (h : ∀ j, s'.f j = resTop _ (p.appTop.hom u) * s.f j) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (g : Good L z J) :
    sval s' r z J = gs (r ≫ p) z ⊤ u * sval s r z J := by
  have m := g.mem (fun _ : Fin 1 => φ) r
  exact (congrArg (gs r z _) (h _)).trans ((gs_mul r z _ m _ _).trans (congrArg (· * _)
    ((gs_res r z _ m _).trans (gs_pull r p z ⊤ trivial u))))

theorem Comparison₂.smul {w₁ : LB.Iso L' (L₁.pull F₁)} {w₂ : LB.Iso L' (L₂.pull F₂)} {φ₁ : Y₁ ⟶ X₁} {φ₂ : Y₂ ⟶ X₂} {p₁ : Y₁ ⟶ B}
    {p₂ : Y₂ ⟶ B} {f : B ⟶ B₀} {π : X' ⟶ B₀} {q : ℕ} {s₂ s₂' : PSec L₂ φ₂ q} {s₁ s₁' : PSec L₁ φ₁ q}
    (h : Comparison₂ w₁ w₂ φ₁ φ₂ p₁ p₂ f π q s₂ s₁) (u : Γ(B, ⊤)) (h₂ : ∀ j, s₂'.f j = resTop _ (p₂.appTop.hom u) * s₂.f j)
    (h₁ : ∀ j, s₁'.f j = resTop _ (p₁.appTop.hom u) * s₁.f j) : Comparison₂ w₁ w₂ φ₁ φ₂ p₁ p₂ f π q s₂' s₁' := by
  intro Z r z₂ z₁ a b c d z J₁ J₂ k g₁ g₂ hk
  rw [sval_scal h₂ z₂ z g₂, sval_scal h₁ z₁ z g₁, c, _root_.mul_assoc, _root_.mul_assoc,
    h Z r z₂ z₁ a b c d z J₁ J₂ k g₁ g₂ hk]

theorem isoCast_isGen {L L₀ : LB X} (h : L = L₀) {M : LB Y} (f : Y ⟶ X) (w : LB.Iso M (L.pull f)) (hw : w.IsGen) :
    (isoCast h f w).IsGen := by
  subst h
  exact hw

end Gen

set_option maxHeartbeats 800000 in

theorem secTie_bijective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : letI := io.toAlgebra; FrPt Xo c T.Fr) (I : IntData Xo c T io y) (P : PELUnif (maximalIdeal T.V) I.G) (F : Type) [Field F] [Algebra T.Fr F] (xF : Sp F ⟶ Xo.X), xF = spMap (algebraMap T.Fr F) ≫ (letI := io.toAlgebra; y.x) → ∀ q : ℕ, (∀ σ, ∃! hh, SecTieF I P F xF q σ hh) ∧ (∀ hh, ∃! σ, SecTieF I P F xF q σ hh) ∧ ∀ (u : F) (σ σ' : P.U.toUnifPre.SecGF F q) (hh hh' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L (q : ℤ) (ptO Xo xF))), SecTieF I P F xF q σ hh → (∀ jj, σ'.f jj = resTop _ (scal (fst (TFK (R := T.V) F) ((Over.pullback (jK T.V)).obj I.G.G)).left u) * σ.f jj) → (∀ jj, hh'.f jj = liftFun Xo.univ.t.G _ (toΓ F u) * hh.f jj) → SecTieF I P F xF q σ' hh' := by
  intro E _ _ _ H Dw l Xo c T io y I P F _ _ xF hx q
  have h₁ := (isGen_iff I.w1).1 I.rig1.1
  have h₂ := (isGen_iff _).1 (isoCast_isGen (congrArg RigLB.L P.bundle).symm I.m2.φ I.w2 I.rig2.1)
  have d₁ : IsPullback (snd (ptO Xo xF) Xo.univ.t.G).left (fst (ptO Xo xF) Xo.univ.t.G).left Xo.univ.t.G.hom
      (spMap (algebraMap T.Fr F) ≫ (letI := io.toAlgebra; y.x)) := by
    rw [← hx]
    exact (IsPullback.of_hasPullback xF Xo.univ.t.G.hom).flip
  have d₂ : IsPullback (UnifPre.gFK (R := T.V) (G := I.G.G) F)
      (fst (TFK (R := T.V) F) ((Over.pullback (jK T.V)).obj I.G.G)).left I.G.G.hom
      (spMap (algebraMap T.Fr F) ≫ spMap (algebraMap T.V T.Fr)) :=
    (IsPullback.of_hasPullback (jFK (R := T.V) F) (pullback.snd I.G.G.hom (jK T.V))).flip.paste_horiz
      (IsPullback.of_hasPullback I.G.G.hom (jK T.V))
  have key : ∀ σ hh, SecTieF I P F xF q σ hh ↔ Comparison₂ I.w1 (isoCast (congrArg RigLB.L P.bundle).symm I.m2.φ I.w2)
      (snd (ptO Xo xF) Xo.univ.t.G).left (UnifPre.gFK (R := T.V) (G := I.G.G) F) (fst (ptO Xo xF) Xo.univ.t.G).left
      (fst (TFK (R := T.V) F) ((Over.pullback (jK T.V)).obj I.G.G)).left (spMap (algebraMap T.Fr F)) I.t'.G.hom q σ hh :=
    fun σ hh => ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩
  simp only [key]
  refine ⟨fun σ => ?_, fun hh => ?_, fun u σ σ' hh hh' h a b => ?_⟩
  · exact existsUnique_tie h₁ h₂ I.t'.PP.isLB Xo.univ.t.PP.isLB P.U.LG.isLB I.m1.cart.1 I.m2.cart.1 d₁.w d₂ q σ
  · obtain ⟨σ, a, b⟩ := existsUnique_tie h₂ h₁ I.t'.PP.isLB P.U.LG.isLB Xo.univ.t.PP.isLB I.m2.cart.1 I.m1.cart.1 d₂.w d₁ q hh
    exact ⟨σ, a.symm, fun σ' h => b σ' (Comparison₂.symm h)⟩
  · exact Comparison₂.smul h (toΓ F u) a b

end GlobalTheory.SecTie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RootDiscriminantDegreeRatioLeRootDiscriminantSq
section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie
namespace GlobalTheory.PtTie

theorem lastPos_L_of_setC {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {large₂ : SizeData₂ D} {X : WeightAlgebra.PJ D B P j}
    {CK C1 A1 : ℝ} {ka wL wF : WeightFamilies.Wt D j} {T nP nW : ℕ} {h0 : ℝ}
    (h : WeightAlgebra.SetC large₂ X CK C1 A1 ka wL wF T nP nW h0) : wL.LastPos := by
  intro τ i hi1
  have hh := h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hL, -, -, hT, -, h40, hnW, -⟩ := hh
  have h2 := two_T_sq_le_last h τ i hi1
  have h3 := hL.2.1 τ i
  have hn : ¬ i.1 + 1 < (D.R.sigW j).1 := by omega
  rw [if_neg hn] at h3
  unfold WeightAlgebra.gapZ at h3
  rw [dif_neg hn] at h3
  have hTp : (0 : ℤ) < (WeightAlgebra.Tp D j T : ℤ) := by unfold WeightAlgebra.Tp; positivity
  rw [Int.fdiv_eq_ediv_of_nonneg _ hTp.le] at h3
  have h4 : (1 : ℤ) ≤ ((ka.aP τ i : ℤ) - ((WeightFamilies.dimY D j : ℤ) + 2) * nW - 2 * D.R.r) / (WeightAlgebra.Tp D j T : ℤ) := by
    rw [Int.le_ediv_iff_mul_le hTp, _root_.one_mul]
    unfold WeightAlgebra.Tp
    have e1 : (2 * (T : ℤ) ^ 2) ≤ (ka.aP τ i : ℤ) := by exact_mod_cast h2
    have e2 : ((WeightFamilies.dimY D j : ℤ) + 2) * nW + 2 * D.R.r ≤ T := by exact_mod_cast hnW
    have e3 : 40 * ((WeightFamilies.dimY D j : ℤ) + 2) ≤ T := by exact_mod_cast h40
    have e4 : (0 : ℤ) ≤ (WeightFamilies.dimY D j : ℤ) := Int.natCast_nonneg _
    push_cast
    nlinarith
  rw [← h3] at h4
  exact_mod_cast h4

theorem rootDiscriminantDegreeRatio_le_rootDiscriminant_sq (D : D7) : rr0 D ≤ D.host.rdE ^ (2 : ℝ) := by
  have hn : (1 : ℝ) ≤ Module.finrank ℚ D.host.E := by
    exact_mod_cast Module.finrank_pos (R := ℚ) (M := D.host.E)
  have e : D.host.rdE ^ (2 : ℝ) = |(NumberField.discr D.host.E : ℝ)| ^ ((2 : ℝ) / Module.finrank ℚ D.host.E) := by
    unfold Formalism.BasicNotions.Host.rdE
    rw [← Real.rpow_mul (abs_nonneg _)]
    congr 1
    ring
  rw [e]
  unfold rr0
  exact div_le_self (by positivity) (by linarith)

theorem runNum_of_sizes : ∀ (D : D7) (large₂ : SizeData₂ D) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ), InR D j → ∀ (X : WeightAlgebra.PJ D B P j) (H : WeightAlgebra.KHyp) (C2 A2 CR : ℝ) (S : WeightAlgebra.Scal B) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), WeightAlgebra.ParA large₂ H.CA → WeightAlgebra.SetC large₂ X H.CK H.C1 H.A1 ka wL wF Tn nP nW h0 → WeightAlgebra.H3 large₂ H C2 A2 CR 0 wL Tn → PageSupp D large₂ B C2 A2 nW S wL → 2 ≤ CR → RunNum D wL (WeightAlgebra.cc D large₂ C2 A2 CR wL) := by
  intro D large₂ B P j hj X H C2 A2 CR S ka wL wF Tn nP nW h0 hA hS h3 hP hCR
  have h1 := lastPos_L_of_setC hS
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hn, -, hL, -⟩ := hS
  have hw : wL.n = nW := hL.1
  obtain ⟨hP13, -, -, hr, hD⟩ := hP
  have hrd : 2 * (D.R.f : ℝ) * D.R.m ≤ D.host.rdE := hA.2.2.2.2.2.2.2.2.2
  have hf : 1 ≤ D.R.f := by
    have : 0 < D.R.f := by unfold Ranks.f Ranks.n; positivity
    omega
  have hm : 1 ≤ D.R.m := hj.1.trans hj.2
  have hfR : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf
  have hmR : (1 : ℝ) ≤ D.R.m := by exact_mod_cast hm
  have hDR : (3 : ℝ) ≤ WeightAlgebra.DF wL := by exact_mod_cast hD
  have h5 : (2 * D.R.f * D.R.m : ℝ) ^ 4 * wL.n + 2 * (2 * D.R.f * D.R.m : ℝ) ^ 3 ≤ WeightFamilies.PPv D large₂ C2 A2 := by
    rw [hw]
    exact ((le_max_left _ _).trans (le_max_right _ _)).trans hP13
  have hq := modulus_pos_of_third_hypothesis h3
  have h31 := h3.1
  rw [Real.rpow_zero, _root_.one_mul] at h31
  have hs : (2 : ℝ) ≤ 2 * D.R.f * D.R.m := by nlinarith
  have hRR : D.host.rdE ^ (2 : ℝ) ≤ WeightFamilies.RRv D CR :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) hCR
  have h4 : rr0 D ≤ WeightFamilies.RRv D CR := (rootDiscriminantDegreeRatio_le_rootDiscriminant_sq D).trans hRR
  have hqg : ∀ i, (WeightAlgebra.qq D : ℝ) ≤ D.host.g i := fun i => by
    have : WeightAlgebra.qq D ≤ D.host.g i := by
      fin_cases i
      exacts [min_le_left _ _, min_le_right _ _]
    exact_mod_cast this
  have r0 : 0 ≤ rr0 D := by unfold rr0; positivity
  generalize hsd : (2 * D.R.f * D.R.m : ℝ) = s at *
  have p0 : (1 : ℝ) ≤ s ^ 4 * wL.n + 2 * s ^ 3 := by
    have a : (0 : ℝ) ≤ s ^ 4 * wL.n := by positivity
    have b : (1 : ℝ) ≤ s ^ 3 := one_le_pow₀ (by linarith)
    linarith
  have hR2 : s ^ 2 ≤ WeightFamilies.RRv D CR := by
    refine le_trans ?_ hRR
    rw [Real.rpow_two]
    exact pow_le_pow_left₀ (by linarith) hrd 2
  have hR1 : 1 ≤ WeightFamilies.RRv D CR := by nlinarith
  have hP1 : 1 ≤ WeightFamilies.PPv D large₂ C2 A2 := p0.trans h5
  have hkey : s ^ 2 * (WeightAlgebra.DF wL : ℝ) ^ 2 ≤ WeightAlgebra.qq D := by
    refine le_trans ?_ h31
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    calc s ^ 2 ≤ WeightFamilies.RRv D CR := hR2
      _ ≤ WeightFamilies.RRv D CR ^ 4 := le_self_pow₀ hR1 (by norm_num)
      _ ≤ _ := le_mul_of_one_le_right (by positivity) (one_le_pow₀ hP1)
  refine ⟨h1, ?_, fun i => ?_, by unfold WeightAlgebra.cc; positivity, fun _ i => ⟨?_, ?_⟩⟩
  · rw [hw]
    refine le_trans ?_ hn
    nlinarith [Nat.mul_le_mul_left (D.R.f * D.R.r) (show 2 ≤ D.R.r + 1 by omega)]
  · have a : 4 * (WeightAlgebra.DF wL : ℝ) ^ 2 ≤ s ^ 2 * (WeightAlgebra.DF wL : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
    have b : 4 * (WeightAlgebra.DF wL : ℝ) + 4 ≤ D.host.g i := by nlinarith [hqg i]
    exact_mod_cast b
  · rw [hsd]
    have a : Real.sqrt s ≤ s := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
    have b : (WeightAlgebra.DF wL : ℝ) * (2 * Real.sqrt s) ≤ (WeightAlgebra.DF wL : ℝ) * s * 2 := by nlinarith
    have c : (6 : ℝ) ≤ (WeightAlgebra.DF wL : ℝ) * s := by nlinarith
    have d := hqg i
    nlinarith
  · rw [hsd]
    have d := hqg i
    unfold WeightAlgebra.cc
    gcongr

end GlobalTheory.PtTie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitsInLevelPrime
section
open NumberField Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.PtTie

namespace GlobalTheory.LevelSplit

theorem splitsIn_level_prime : ∀ (D : D7) (i : Fin 2), SplitsIn D.host.E (D.host.g i) := fun D i =>
  GlobalTheory.HalfGen.factors_of_ncard_places D.host.E (D.host.g i) (D.host.g_prime i) (D.nd.g_split i)

end GlobalTheory.LevelSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumFinitePlacesLeSumOverPrimesStatement
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_finitePlaces_le_sum_over_primes : ∀ (K : Type) [Field K] [NumberField K] (φ : ℕ → ℝ) (S : Finset ℕ), (∀ p ∈ S, p.Prime) → (∀ p, 0 ≤ φ p) → ∀ ν : HeightOneSpectrum (𝓞 K) → ℝ, (∀ la, 0 ≤ ν la) → (∀ la, ν la ≤ (ramOverZ la : ℝ) * φ (resCharOf la)) → (∀ la, resCharOf la ∉ S → ν la = 0) → (Function.support ν).Finite ∧ (∑ᶠ la, |ν la| * (Real.log (Ideal.absNorm la.asIdeal) / Module.finrank ℚ K)) ≤ ∑ p ∈ S, φ p * Real.log p := by
  first | exact @GlobalTheory.PlaceSum.finsum_le_sum_primes | exact GlobalTheory.PlaceSum.finsum_le_sum_primes | (intros; apply GlobalTheory.PlaceSum.finsum_le_sum_primes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumPrimeLogDivPredLeLogAddStatement
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_prime_log_div_pred_le_log_add : ∀ N : ℕ, ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log p / ((p : ℝ) - 1) ≤ Real.log N + 2.2 := by
  first | exact @GlobalTheory.PrimeLogSum.sum_log_div_pred_le | exact GlobalTheory.PrimeLogSum.sum_log_div_pred_le | (intros; apply GlobalTheory.PrimeLogSum.sum_log_div_pred_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TotalDegreeLeAndExistsCombinationOfMemFFV
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory

theorem totalDegree_le_and_exists_combination_of_mem_FFV :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (a : ((E →+* ℂ) × ℕ → ℕ)) (n : ℕ), ∀ P₀ ∈ FFV (Dw := Dw) T a n, P₀.totalDegree ≤ DF Dw a ∧ ∃ (k : ℕ) (cf : Fin k → T.V) (Pi : Fin k → MvPolynomial (LtN Dw n) c.F), (∀ i, Pi i ∈ harmA c a n) ∧ P₀ = ∑ i, algebraMap T.V T.Fr (cf i) • MvPolynomial.map io (Pi i) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io a n P₀ hP
  haveI : CharZero T.Fr := charZero_of_injective_algebraMap (IsFractionRing.injective T.V T.Fr)
  haveI : CharZero c.F := io.charZero
  refine ⟨?_, ?_⟩
  · refine Finset.sup_le fun m hm => le_of_eq ?_
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun i _ => hP.1.2.2 m hm σ i
  · obtain ⟨s, cf, Q, hcf, hQ, hs⟩ := GlobalTheory.exists_integral_combination_of_mem_HaO (E →+* ℂ) Dw.mult n ℤ ℚ T.Fr
      (Rat.castHom T.Fr) (algebraMap T.V T.Fr).range (fun x => ⟨(x : T.V), by simp⟩)
      ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) P₀ hP
    choose cf' hcf' using hcf
    refine ⟨s, cf', fun i => MvPolynomial.map (Rat.castHom c.F) (Q i), fun i => ?_, ?_⟩
    · obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hQ i
      refine ⟨⟨PullbackSections.harmK_map _ h1, PullbackSections.rowInv_map _ h2, PullbackSections.rowDeg_map _ h3⟩, fun m => ?_⟩
      rw [MvPolynomial.coeff_map]
      obtain ⟨z, hz⟩ := h4 m
      rw [← hz]
      have : (Rat.castHom c.F) (algebraMap ℤ ℚ z) = (z : c.F) := by simp
      rw [this]
      exact intCast_mem _ z
    · rw [hs]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [MvPolynomial.map_map, hcf' i, MvPolynomial.smul_eq_C_mul,
        Subsingleton.elim (io.comp (Rat.castHom c.F)) (Rat.castHom T.Fr)]

end GlobalTheory
end

