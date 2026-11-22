import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0036
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0070
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0057
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0134
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0078
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SegreCoordinates
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0056
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0003
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0133
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0114

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.MemOfMemImage
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.GlueTwoLB

variable {X Y Z : Scheme.{0}}

def stU (f : Z ⟶ Y) (z : Z) : (Y.presheaf.stalk (f z))ˣ →* (Z.presheaf.stalk z)ˣ :=
  Units.map (f.stalkMap z).hom.toMonoidHom

theorem stU_gm (f : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (h : g (f z) ∈ U) (a : Γ(X, U)ˣ) :
    stU f z (gm g (f z) U a) = gm (f ≫ g) z U a := by
  rw [← gm_pull f g z U h]
  apply Units.ext
  rw [gm_val f z (g ⁻¹ᵁ U) h]
  show (f.stalkMap z).hom (gm g (f z) U a).val = _
  rw [gm_val g (f z) U h]
  exact Scheme.Hom.germ_stalkMap_apply f _ z h _

theorem stU_injective (f : Z ⟶ Y) [IsOpenImmersion f] (z : Z) : Function.Injective (stU f z) :=
  Units.map_injective (ConcreteCategory.bijective_of_isIso (f.stalkMap z)).1

theorem stU_gm_id (f : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : f z ∈ U) (a : Γ(Y, U)ˣ) :
    stU f z (gm (𝟙 Y) (f z) U a) = gm f z U a := by
  rw [stU_gm f (𝟙 Y) z U h, Category.comp_id]

theorem exists_push (ψ : Z ⟶ Y) [IsOpenImmersion ψ] (W : Z.Opens) (V : Y.Opens)
    (h : ∀ y ∈ V, ∃ z ∈ W, ψ z = y) (a : Γ(Z, W)ˣ) :
    ∃ b : Γ(Y, V)ˣ, ∀ z : Z, ψ z ∈ V → gm ψ z V b = gm (𝟙 Z) z W a := by
  have hle : V ≤ ψ ''ᵁ W := fun y hy => h y hy
  refine ⟨res hle (Units.map (ψ.appIso W).inv.hom.toMonoidHom a), fun z hz => ?_⟩
  have hW : z ∈ W := by
    obtain ⟨z', hz', e⟩ := h _ hz
    rwa [← ψ.isOpenEmbedding.injective e]
  rw [gm_res ψ z hle hz]
  apply Units.ext
  rw [gm_val ψ z _ (hle hz), gm_val (𝟙 Z) z W hW]
  have e := congrArg (fun q => q.hom a.val) (ψ.appIso_inv_app W)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  exact (congrArg (Z.presheaf.germ (ψ ⁻¹ᵁ ψ ''ᵁ W) z (hle hz)).hom e).trans
    (TopCat.Presheaf.germ_res_apply Z.presheaf _ z (hle hz) _)

theorem iso_self {L : LB X} (hL : L.IsLB) : LBIso L L := by
  refine ⟨⟨fun p => L.g p.1 p.2⟩, fun p q => unit_ext fun y hy => ?_⟩
  refine (gm_res _ y _ hy _).trans (Eq.symm ((map_mul _ _ _).trans ((congrArg₂ (· * ·)
    (gm_div L L (𝟙 X) y p q hy) (gm_res _ y _ hy _)).trans ?_)))
  have a := gm_cocycle hL (𝟙 X) y hy.1.1 hy.2.1 hy.2.2
  have b := gm_cocycle hL (𝟙 X) y hy.1.1 hy.1.2 hy.2.2
  show gm (𝟙 X) y _ (L.g p.1 q.1) * (gm (𝟙 X) y _ (L.g p.2 q.2))⁻¹ * gm (𝟙 X) y _ (L.g q.1 q.2) =
    gm (𝟙 X) y _ (L.g p.1 p.2)
  rw [mul_right_comm, a, ← b, mul_inv_cancel_right]

theorem isLB_of_stalk {L : LB X} (hc : ∀ x, ∃ i, x ∈ L.U i)
    (h : ∀ x i j k, x ∈ L.U i → x ∈ L.U j → x ∈ L.U k →
      gm (𝟙 X) x _ (L.g i j) * gm (𝟙 X) x _ (L.g j k) = gm (𝟙 X) x _ (L.g i k)) : L.IsLB where
  cover := top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 (hc y)
  g_self i := unit_ext fun y hy => by
    rw [gm_res (𝟙 X) y _ hy, map_one]
    exact mul_eq_left.1 (h y i i i hy hy hy)
  cocycle i j k := unit_ext fun y hy => by
    rw [map_mul, gm_res (𝟙 X) y _ hy, gm_res (𝟙 X) y _ hy, gm_res (𝟙 X) y _ hy]
    exact h y i j k hy.1.1 hy.1.2 hy.2

theorem cocycle_descend {L : LB Y} (ψ : Z ⟶ Y) [IsOpenImmersion ψ] (z : Z) {i j k : L.ι}
    (hi : ψ z ∈ L.U i) (hj : ψ z ∈ L.U j) (hk : ψ z ∈ L.U k)
    (h : gm ψ z _ (L.g i j) * gm ψ z _ (L.g j k) = gm ψ z _ (L.g i k)) :
    gm (𝟙 Y) (ψ z) _ (L.g i j) * gm (𝟙 Y) (ψ z) _ (L.g j k) = gm (𝟙 Y) (ψ z) _ (L.g i k) := by
  apply stU_injective ψ z
  rw [map_mul, stU_gm_id ψ z (L.U i ⊓ L.U j) ⟨hi, hj⟩, stU_gm_id ψ z (L.U j ⊓ L.U k) ⟨hj, hk⟩,
    stU_gm_id ψ z (L.U i ⊓ L.U k) ⟨hi, hk⟩, h]

theorem mem_of_mem_image (ψ : Z ⟶ Y) [IsOpenImmersion ψ] {W : Z.Opens} {z : Z} (h : ψ z ∈ ψ ''ᵁ W) : z ∈ W := by
  obtain ⟨z', hz', e⟩ := h
  rwa [← ψ.isOpenEmbedding.injective e]

theorem exists_push_inf (ψ : Z ⟶ Y) [IsOpenImmersion ψ] (W W' : Z.Opens) (a : Γ(Z, W ⊓ W')ˣ) :
    ∃ b : Γ(Y, ψ ''ᵁ W ⊓ ψ ''ᵁ W')ˣ, ∀ z : Z, z ∈ W → z ∈ W' →
      gm ψ z (ψ ''ᵁ W ⊓ ψ ''ᵁ W') b = gm (𝟙 Z) z (W ⊓ W') a := by
  obtain ⟨b, hb⟩ := exists_push ψ (W ⊓ W') (ψ ''ᵁ W ⊓ ψ ''ᵁ W') (by
    rintro y ⟨⟨z, hz, rfl⟩, h'⟩
    exact ⟨z, ⟨hz, mem_of_mem_image ψ h'⟩, rfl⟩) a
  exact ⟨b, fun z h h' => hb z ⟨⟨z, h, rfl⟩, ⟨z, h', rfl⟩⟩⟩

theorem gen_stalk {Y₀ Y₁ Y₂ : Scheme.{0}} {φ₁ : Y₀ ⟶ Y₁} {φ₂ : Y₀ ⟶ Y₂} {L₁ : LB Y₁} {L₂ : LB Y₂}
    {w : LB.Iso (L₁.pull φ₁) (L₂.pull φ₂)} (hw : w.IsGen) (y : Y₀) {i i' : L₁.ι} {k k' : L₂.ι}
    (hi : φ₁ y ∈ L₁.U i) (hi' : φ₁ y ∈ L₁.U i') (hk : φ₂ y ∈ L₂.U k) (hk' : φ₂ y ∈ L₂.U k') :
    gw w (𝟙 Y₀) y k (fun _ => i) = gm φ₂ y _ (L₂.g k k') * (gm φ₁ y _ (L₁.g i i'))⁻¹ *
      gw w (𝟙 Y₀) y k' (fun _ => i') := by
  have := (isGen_iff w).1 hw Y₀ (𝟙 Y₀) y k k' (fun _ => i) (fun _ => i') hk hk' (mem_pull.2 hi) (mem_pull.2 hi')
  rw [gm_pull_g L₁ φ₁ (𝟙 Y₀) y _ _ (mem_pull.2 hi) (mem_pull.2 hi'), Category.id_comp, Category.id_comp] at this
  exact this

def pullChart (L : LB X) (F : Y ⟶ X) : ChartPull (L.pull F) L F where
  idx J := J PUnit.unit
  le _ _ hy := mem_pull.1 hy
  g y J J' hj hj' := (gm_pull_g L F (𝟙 _) y J J' hj hj').trans (by rw [Category.id_comp])

theorem glue : ∀ (Y Y₀ Y₁ Y₂ : Scheme.{0}) (ψ₁ : Y₁ ⟶ Y) (ψ₂ : Y₂ ⟶ Y) (φ₁ : Y₀ ⟶ Y₁) (φ₂ : Y₀ ⟶ Y₂) (L₁ : LB Y₁) (L₂ : LB Y₂), IsOpenImmersion ψ₁ → IsOpenImmersion ψ₂ → IsPullback φ₁ φ₂ ψ₁ ψ₂ → Set.range ψ₁ ∪ Set.range ψ₂ = Set.univ → L₁.IsLB → L₂.IsLB → LBIso (L₁.pull φ₁) (L₂.pull φ₂) → ∃ L : LB Y, L.IsLB ∧ LBIso L₁ (L.pull ψ₁) ∧ LBIso L₂ (L.pull ψ₂) := by
  intro Y Y₀ Y₁ Y₂ ψ₁ ψ₂ φ₁ φ₂ L₁ L₂ o₁ o₂ hp hcov h₁ h₂ ⟨w, hw⟩
  have p₁ : IsOpenImmersion φ₁ := MorphismProperty.of_isPullback hp.flip o₂
  have hpt : ∀ y, ψ₁ (φ₁ y) = ψ₂ (φ₂ y) := fun y => congrArg (fun g => g y) hp.w
  have lift : ∀ y₁ y₂, ψ₁ y₁ = ψ₂ y₂ → ∃ y, φ₁ y = y₁ ∧ φ₂ y = y₂ := fun y₁ y₂ e =>
    Scheme.exists_preimage_of_isPullback hp y₁ y₂ e
  have hsq := hp.w
  choose g₁ hg₁ using fun i j => exists_push_inf ψ₁ _ _ (L₁.g i j)
  choose g₂ hg₂ using fun i j => exists_push_inf ψ₂ _ _ (L₂.g i j)
  have hm : ∀ (k : L₂.ι) (i : L₁.ι), ∃ b : Γ(Y, ψ₂ ''ᵁ L₂.U k ⊓ ψ₁ ''ᵁ L₁.U i)ˣ, ∀ y : Y₀,
      φ₂ y ∈ L₂.U k → φ₁ y ∈ L₁.U i → gm (φ₁ ≫ ψ₁) y _ b = gw w (𝟙 Y₀) y k (fun _ => i) := by
    intro k i
    obtain ⟨b, hb⟩ := exists_push (φ₁ ≫ ψ₁) ((L₂.pull φ₂).U (fun _ => k) ⊓ (L₁.pull φ₁).U (fun _ => i))
      (ψ₂ ''ᵁ L₂.U k ⊓ ψ₁ ''ᵁ L₁.U i) (by
        rintro y ⟨⟨y₂, h₂, rfl⟩, ⟨y₁, h₁, e⟩⟩
        obtain ⟨z, rfl, rfl⟩ := lift y₁ y₂ e
        exact ⟨z, ⟨mem_pull.2 h₂, mem_pull.2 h₁⟩, e⟩) (w.s (fun _ => k, fun _ => i))
    exact ⟨b, fun y hk hi => hb y ⟨⟨_, hk, (hpt y).symm⟩, ⟨_, hi, rfl⟩⟩⟩
  choose m hm using hm
  let L : LB Y :=
    { «ι» := L₁.ι ⊕ L₂.ι
      U := Sum.elim (fun i => ψ₁ ''ᵁ L₁.U i) (fun k => ψ₂ ''ᵁ L₂.U k)
      g := fun p q => match p, q with
        | .inl i, .inl j => g₁ i j
        | .inr k, .inr l => g₂ k l
        | .inr k, .inl i => m k i
        | .inl i, .inr k => (res (le_inf inf_le_right inf_le_left) (m k i))⁻¹ }

  have key : ∀ y : Y₀, ∃ t : L.ι → (Y₀.presheaf.stalk y)ˣ, ∀ p q, ψ₁ (φ₁ y) ∈ L.U p → ψ₁ (φ₁ y) ∈ L.U q →
      gm (φ₁ ≫ ψ₁) y _ (L.g p q) = t p * (t q)⁻¹ := by
    intro y
    obtain ⟨i₀, hi₀⟩ := exists_chart h₁ (φ₁ y)
    have ml : ∀ i, ψ₁ (φ₁ y) ∈ L.U (.inl i) → φ₁ y ∈ L₁.U i := fun i h => mem_of_mem_image ψ₁ h
    have mr : ∀ k, ψ₁ (φ₁ y) ∈ L.U (.inr k) → φ₂ y ∈ L₂.U k := fun k h => mem_of_mem_image ψ₂ (hpt y ▸ h)
    have mix : ∀ k i, φ₂ y ∈ L₂.U k → φ₁ y ∈ L₁.U i → gm (φ₁ ≫ ψ₁) y _ (m k i) =
        gw w (𝟙 Y₀) y k (fun _ => i₀) * (gm φ₁ y _ (L₁.g i i₀))⁻¹ := fun k i hk hi => by
      rw [hm k i y hk hi, gen_stalk hw y hi hi₀ hk hk, gm_self h₂ φ₂ y hk, _root_.one_mul, mul_comm]
    refine ⟨Sum.elim (fun i => gm φ₁ y _ (L₁.g i i₀)) (fun k => gw w (𝟙 Y₀) y k (fun _ => i₀)), ?_⟩
    rintro (i | k) (j | l) hp hq
    · have e := congrArg (stU φ₁ y) (hg₁ i j _ (ml i hp) (ml j hq))
      rw [stU_gm φ₁ ψ₁ y (ψ₁ ''ᵁ L₁.U i ⊓ ψ₁ ''ᵁ L₁.U j) ⟨hp, hq⟩, stU_gm_id φ₁ y (L₁.U i ⊓ L₁.U j) ⟨ml i hp, ml j hq⟩] at e
      refine e.trans ?_
      exact eq_mul_inv_of_mul_eq (gm_cocycle h₁ φ₁ y (ml i hp) (ml j hq) hi₀)
    · refine ((map_inv _ _).trans (congrArg (·⁻¹) ((gm_res (φ₁ ≫ ψ₁) y _
        (show (φ₁ ≫ ψ₁) y ∈ ψ₁ ''ᵁ L₁.U i ⊓ ψ₂ ''ᵁ L₂.U l from ⟨hp, hq⟩) _).trans
        (mix l i (mr l hq) (ml i hp))))).trans ?_
      rw [mul_inv_rev, inv_inv]; rfl
    · exact mix k j (mr k hp) (ml j hq)
    · have e := congrArg (stU φ₂ y) (hg₂ k l _ (mr k hp) (mr l hq))
      rw [stU_gm φ₂ ψ₂ y (ψ₂ ''ᵁ L₂.U k ⊓ ψ₂ ''ᵁ L₂.U l) ⟨⟨_, mr k hp, rfl⟩, ⟨_, mr l hq, rfl⟩⟩,
        stU_gm_id φ₂ y (L₂.U k ⊓ L₂.U l) ⟨mr k hp, mr l hq⟩, ← hsq] at e
      refine e.trans (eq_mul_inv_of_mul_eq ?_)
      have := gen_stalk hw y hi₀ hi₀ (mr k hp) (mr l hq)
      rw [gm_self h₁ φ₁ y hi₀, inv_one, _root_.mul_one] at this
      exact this.symm
  have hL : L.IsLB := by
    refine isLB_of_stalk (fun x => ?_) ?_
    · rcases (hcov.symm ▸ Set.mem_univ x : x ∈ Set.range ψ₁ ∪ Set.range ψ₂) with ⟨y, rfl⟩ | ⟨y, rfl⟩
      · obtain ⟨i, hi⟩ := exists_chart h₁ y
        exact ⟨.inl i, y, hi, rfl⟩
      · obtain ⟨i, hi⟩ := exists_chart h₂ y
        exact ⟨.inr i, y, hi, rfl⟩
    have ov : ∀ x p q r (i : L₁.ι) (k : L₂.ι), x ∈ L.U (.inl i) → x ∈ L.U (.inr k) →
        x ∈ L.U p → x ∈ L.U q → x ∈ L.U r →
        gm (𝟙 Y) x _ (L.g p q) * gm (𝟙 Y) x _ (L.g q r) = gm (𝟙 Y) x _ (L.g p r) := by
      rintro x p q r i k ⟨y₁, -, rfl⟩ ⟨y₂, -, e⟩ hp hq hr
      obtain ⟨y, rfl, rfl⟩ := lift y₁ y₂ e.symm
      obtain ⟨t, ht⟩ := key y
      refine cocycle_descend (φ₁ ≫ ψ₁) y hp hq hr ?_
      rw [ht p q hp hq, ht q r hq hr, ht p r hp hr, _root_.mul_assoc, inv_mul_cancel_left]
    rintro x (i | i) (j | j) (k | k) hi hj hk
    · obtain ⟨y, hy, rfl⟩ := id hi
      have hj' := mem_of_mem_image ψ₁ hj
      have hk' := mem_of_mem_image ψ₁ hk
      refine cocycle_descend ψ₁ y hi hj hk ?_
      exact (congrArg₂ (· * ·) (hg₁ i j y hy hj') (hg₁ j k y hj' hk')).trans
        ((gm_cocycle h₁ (𝟙 _) y hy hj' hk').trans (hg₁ i k y hy hk').symm)
    · exact ov x _ _ _ i k hi hk hi hj hk
    · exact ov x _ _ _ i j hi hj hi hj hk
    · exact ov x _ _ _ i j hi hj hi hj hk
    · exact ov x _ _ _ j i hj hi hi hj hk
    · exact ov x _ _ _ j i hj hi hi hj hk
    · exact ov x _ _ _ k i hk hi hi hj hk
    · obtain ⟨y, hy, rfl⟩ := id hi
      have hj' := mem_of_mem_image ψ₂ hj
      have hk' := mem_of_mem_image ψ₂ hk
      refine cocycle_descend ψ₂ y hi hj hk ?_
      exact (congrArg₂ (· * ·) (hg₂ i j y hy hj') (hg₂ j k y hj' hk')).trans
        ((gm_cocycle h₂ (𝟙 _) y hy hj' hk').trans (hg₂ i k y hy hk').symm)
  let c₁ : ChartPull L₁ L ψ₁ := ⟨Sum.inl, fun i y hy => ⟨y, hy, rfl⟩, fun y i j hi hj => (hg₁ i j y hi hj).symm⟩
  let c₂ : ChartPull L₂ L ψ₂ := ⟨Sum.inr, fun i y hy => ⟨y, hy, rfl⟩, fun y i j hi hj => (hg₂ i j y hi hj).symm⟩
  exact ⟨L, hL, LBIso.chartPull c₁ (pullChart L ψ₁) (iso_self hL),
    LBIso.chartPull c₂ (pullChart L ψ₂) (iso_self hL)⟩

end GlobalTheory.GlueTwoLB
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PowEqOneIffOfIsGrpPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
open GlobalTheory.UU

namespace GlobalTheory.TorsionSection

theorem pow_eq_one_iff_left {S : Scheme.{0}} {G T : Over S} [GrpObj G] (y : T ⟶ G) (n : ℕ) :
    y ^ n = 1 ↔ y.left ≫ (mulN G n).left = T.hom ≫ η[G].left := by
  have e : (1 : T ⟶ G).left = T.hom ≫ η[G].left := by
    rw [Hom.one_def, Over.comp_left]; rfl
  rw [← e, ← Over.comp_left, GrpTangent.comp_mulN]
  exact ⟨fun h => by rw [h], fun h => Over.OverMorphism.ext h⟩

theorem pow_eq_one_iff_of_isGrpPullback {S S' : Scheme.{0}} {G : Over S} {G' T : Over S'} [GrpObj G]
    [GrpObj G'] {f : S' ⟶ S} {F : G'.left ⟶ G.left} (h : IsGrpPullback G' G f F) (y : T ⟶ G')
    (n : ℕ) :
    y ^ n = 1 ↔ (y.left ≫ F) ≫ (mulN G n).left = (T.hom ≫ f) ≫ η[G].left := by
  let φ : (T ⟶ G') →* (Over.mk (T.hom ≫ f) ⟶ G) := MonoidHom.mk' (Out.toBase h.1.w)
    fun a b => Over.OverMorphism.ext (h.2 T a b _ _ rfl rfl).symm
  have hφ : Function.Injective φ := fun a b hab => Over.OverMorphism.ext
    (h.1.hom_ext (congrArg Over.Hom.left hab) ((Over.w a).trans (Over.w b).symm))
  rw [← map_eq_one_iff φ hφ, map_pow]
  exact pow_eq_one_iff_left (φ y) n

theorem exists_section_extending_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (X U : Scheme.{0}) (j : U ⟶ X) (s : U ⟶ Sp B) (o : Obj D l b s) (t : SAB H X) (μ₀ : SABMap o.t t j), IsLocallyNoetherian X → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsPreimmersion j → Flat j → IsDominant j → QuasiCompact j → IsUnit (l.A : Γ(X, ⊤)) → ∀ (k : Type) [Field k] (x : Sp k ⟶ X) (p : Over.mk x ⟶ t.G), p ^ l.A = 1 → ∃ (a : D.La) (V : Scheme.{0}) (v : V ⟶ X) (_ : IsOpenImmersion v) (σ : V ⟶ t.G.left) (xV : Sp k ⟶ V), xV ≫ v = x ∧ σ ≫ t.G.hom = v ∧ pullback.fst v j ≫ σ = pullback.snd v j ≫ (o.etaA a).left ≫ μ₀.φ ∧ xV ≫ σ = p.left := by
  intro E _ _ _ H D l B _ b X U j s o t μ₀ hX hN h₁ h₂ h₃ h₄ hA k _ x p hp
  have := t.semi.smooth
  have := t.semi.separated
  have hP := GrpTangent.isPullback_torsion t.G l.A
  have hEt := GrpTangent.etale_torsion t.G hA
  have hι : (torsion.ι t.G l.A).left ≫ t.G.hom = (torsion t.G l.A).hom := Over.w _
  have hsep : IsSeparated (torsion t.G l.A).hom := by
    have : IsSeparated ((mulN t.G l.A).left ≫ t.G.hom) := by rw [Over.w]; infer_instance
    exact MorphismProperty.of_isPullback (P := @IsSeparated) hP (IsSeparated.of_comp _ t.G.hom)
  have := D.fin
  have : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  have : AddGroup.FG D.La := Module.Finite.iff_addGroup_fg.mp this
  let K : AddSubgroup D.La := (nsmulAddMonoidHom (α := D.La) l.A).range
  have : K.FiniteIndex := AddSubgroup.finiteIndex_range_nsmulAddMonoidHom_of_fg _ l.A_pos.ne'
  let e : Multiplicative D.La →* (𝟙_ (Over U) ⟶ o.t.G) :=
    MonoidHom.mk' (fun a => o.etaA a.toAdd) fun a c => o.etaA_add _ _
  have hpow (a : D.La) : o.etaA a ^ l.A = 1 :=
    (map_pow e (.ofAdd a) l.A).symm.trans (o.etaA_ker a)
  have hout (a : D.La) : o.etaA (QuotientAddGroup.mk (s := K) a).out = o.etaA a := by
    obtain ⟨⟨_, c, rfl⟩, hc⟩ := QuotientAddGroup.mk_out_eq_add K a
    rw [hc, o.etaA_add]
    exact (congrArg (o.etaA a * ·) (o.etaA_ker c)).trans (_root_.mul_one _)
  have hw (a : D.La) : ((o.etaA a).left ≫ μ₀.φ) ≫ (mulN t.G l.A).left = j ≫ η[t.G].left :=
    ((pow_eq_one_iff_of_isGrpPullback μ₀.cart (o.etaA a) l.A).mp (hpow a)).trans
      (congrArg (· ≫ _) (Category.id_comp j))
  let σ (a : D.La) : U ⟶ (torsion t.G l.A).left := hP.lift _ _ (hw a)
  have hσ (a : D.La) : σ a ≫ (torsion.ι t.G l.A).left = (o.etaA a).left ≫ μ₀.φ := hP.lift_fst _ _ _
  let p' : Sp k ⟶ (torsion t.G l.A).left := hP.lift p.left x ((pow_eq_one_iff_left p l.A).mp hp)
  obtain ⟨i, W, hW, hW₁, hW₂⟩ := exists_opens_isOpenImmersion_extending_section X U j hN h₁ h₂ h₃ h₄
    (torsion t.G l.A).left (torsion t.G l.A).hom (D.La ⧸ K) (fun i => σ i.out) hEt hsep
    (fun i => hP.lift_snd _ _ _) (fun Ω _ _ u y hy => by
      have hy' : (y ≫ (torsion.ι t.G l.A).left) ≫ t.G.hom = u ≫ j := by
        rw [Category.assoc, hι, hy]
      let z : Over.mk u ⟶ o.t.G := Over.homMk (μ₀.cart.1.lift _ _ hy') (μ₀.cart.1.lift_snd _ _ _)
      have hz : z.left ≫ μ₀.φ = y ≫ (torsion.ι t.G l.A).left := μ₀.cart.1.lift_fst _ _ _
      have hzA : z ^ l.A = 1 := by
        refine (pow_eq_one_iff_of_isGrpPullback μ₀.cart z l.A).mpr ?_
        rw [hz, Category.assoc, hP.w, reassoc_of% hy]
        exact (Category.assoc _ _ _).symm
      obtain ⟨β, hβ⟩ := Spec.map_surjective (u ≫ s)
      obtain ⟨-, I, -, hI, -⟩ := o.geom Ω u β.hom hβ.symm
      obtain ⟨a, ha⟩ := (I.onto l.A l.A_pos z).mp hzA
      refine ⟨QuotientAddGroup.mk a, hP.hom_ext ?_ ?_⟩
      · rw [Category.assoc, hσ, hout, ← hz, ← ha, ← hI, Over.comp_left, Category.assoc]
        rfl
      · rw [hy, Category.assoc, hP.lift_snd])
    (p' (IsLocalRing.closedPoint k))
  have hr : Set.range p' ⊆ Set.range W.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Subsingleton.elim w (IsLocalRing.closedPoint k), Scheme.Opens.range_ι]
    exact hW
  refine ⟨i.out, W, W.ι ≫ (torsion t.G l.A).hom, hW₁, W.ι ≫ (torsion.ι t.G l.A).left,
    IsOpenImmersion.lift W.ι p' hr, ?_, ?_, ?_, ?_⟩
  · rw [IsOpenImmersion.lift_fac_assoc]; exact hP.lift_snd _ _ _
  · rw [Category.assoc, hι]
  · rw [reassoc_of% hW₂, hσ]
  · rw [IsOpenImmersion.lift_fac_assoc]; exact hP.lift_fst _ _ _

end GlobalTheory.TorsionSection
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ProjRepGraphSegreCoordinatesFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.GraphSegre

theorem idealOf_eq_graphIdeal {K σ₁ σ₂ : Type} [CommRing K] {Y X₁ X₂ : Scheme.{0}} (s : Y ⟶ Sp K)
    (M₁ : LB X₁) (th₁ : σ₁ → M₁.Sec) (a₁ : Y ⟶ X₁) (M₂ : LB X₂) (th₂ : σ₂ → M₂.Sec) (a₂ : Y ⟶ X₂)
    (N : LB Y) (ty : σ₁ × σ₂ → N.Sec) (h₁ : M₁.IsLB) (h₂ : M₂.IsLB) (hN : N.IsLB)
    (H : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ Y) (v₁ : σ₁ → T) (v₂ : σ₂ → T), SecCoord M₁ th₁ (y ≫ a₁) v₁ →
      SecCoord M₂ th₂ (y ≫ a₂) v₂ → SecCoord N ty y (fun i => v₁ i.1 * v₂ i.2)) :
    idealOf s N ty (𝟙 Y) = graphIdeal s M₁ th₁ a₁ M₂ th₂ a₂ := by
  ext F
  simp only [idealOf, graphIdeal, Ideal.mem_iInf, RingHom.mem_ker, Category.comp_id]
  constructor
  · intro hF T _ β y v₁ v₂ h
    exact hF T _ β y _ ⟨h.1, H T y v₁ v₂ h.2.1 h.2.2⟩
  · intro hF T _ β y v h
    refine eq_zero_of_localization _ fun J hJ => ?_
    set φ := algebraMap T (Localization.AtPrime J) with hφ
    obtain ⟨v₁, hv₁⟩ := (GlobalTheory.ZM.LocalCoord.secCoord_local X₁ M₁ σ₁ th₁ h₁).1 (Localization.AtPrime J) ((spMap φ ≫ y) ≫ a₁)
    obtain ⟨v₂, hv₂⟩ := (GlobalTheory.ZM.LocalCoord.secCoord_local X₂ M₂ σ₂ th₂ h₂).1 (Localization.AtPrime J) ((spMap φ ≫ y) ≫ a₂)
    have hv := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique Y N _ ty T y v hN h.2).1 _ φ
    obtain ⟨u, hu⟩ := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique Y N _ ty _ _ _ hN (H _ _ v₁ v₂ hv₁ hv₂)).2.2 _ hv
    have hv₁' := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique X₁ M₁ _ th₁ _ _ _ h₁ hv₁).2.1 u
    have hs : (spMap φ ≫ y) ≫ s = spMap (φ.comp β) := by
      rw [Category.assoc, h.1]
      exact (Spec.map_comp (CommRingCat.ofHom β) (CommRingCat.ofHom φ)).symm
    have key := hF _ _ (φ.comp β) (spMap φ ≫ y) _ v₂ ⟨hs, hv₁', hv₂⟩
    rw [MvPolynomial.map_eval₂Hom, ← key]
    congr 2
    funext i
    rw [hu i, _root_.mul_assoc]

theorem projRep_graph : ∀ (R K σ₁ σ₂ : Type) [CommRing R] [CommRing K] [Finite σ₁] [Finite σ₂] (x : R →+* K) (I₁ : Ideal (MvPolynomial σ₁ R)) (I₂ : Ideal (MvPolynomial σ₂ R)) (Z₁ Z₂ : Over (Sp R)) (M₁ : LB Z₁.left) (M₂ : LB Z₂.left) (th₁ : σ₁ → M₁.Sec) (th₂ : σ₂ → M₂.Sec) (Y : Scheme.{0}) (s : Y ⟶ Sp K) (a₁ : Y ⟶ Z₁.left) (a₂ : Y ⟶ Z₂.left), ProjRep I₁ Z₁.hom M₁ th₁ → ProjRep I₂ Z₂.hom M₂ th₂ → IsPullback a₁ s Z₁.hom (spMap x) → a₂ ≫ Z₂.hom = s ≫ spMap x → ∃ (N : LB Y) (ty : σ₁ × σ₂ → N.Sec), ProjRep (graphIdeal s M₁ th₁ a₁ M₂ th₂ a₂) s N ty ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ Y) (v₁ : σ₁ → T) (v₂ : σ₂ → T), SecCoord M₁ th₁ (y ≫ a₁) v₁ → SecCoord M₂ th₂ (y ≫ a₂) v₂ → SecCoord N ty y (fun i => v₁ i.1 * v₂ i.2) := by
  intro R K σ₁ σ₂ _ _ _ _ x I₁ I₂ Z₁ Z₂ M₁ M₂ th₁ th₂ Y s a₁ a₂ r₁ r₂ hp ha₂
  obtain ⟨I₃, M₃, th₃, r₃, hseg⟩ := GlobalTheory.ZM.SegreCoord.segre_coordinates R σ₁ σ₂ I₁ I₂ Z₁ Z₂ M₁ M₂ th₁ th₂ r₁ r₂
  have hprop : IsProper Z₂.hom := (GlobalTheory.ZM.projRep_projective_ample R σ₂ I₂ Z₂ M₂ th₂ r₂).2.1
  have hP : IsPullback (fst Z₁ Z₂).left (snd Z₁ Z₂).left Z₁.hom Z₂.hom := IsPullback.of_hasPullback Z₁.hom Z₂.hom
  have hW := IsPullback.of_hasPullback (Z₁ ⊗ Z₂).hom (spMap x)
  generalize pullback.fst (Z₁ ⊗ Z₂).hom (spMap x) = π at hW
  generalize pullback.snd (Z₁ ⊗ Z₂).hom (spMap x) = s' at hW
  generalize pullback (Z₁ ⊗ Z₂).hom (spMap x) = Wd at π s' hW
  obtain ⟨th', r', hbc⟩ := GlobalTheory.ZM.RepBC.projRep_baseChange R K _ x I₃ _ Wd _ s' π M₃ th₃ r₃ hW
  have hfw : (fst Z₁ Z₂).left ≫ Z₁.hom = (Z₁ ⊗ Z₂).hom := Over.w _
  let a : Y ⟶ (Z₁ ⊗ Z₂).left := hP.lift a₁ a₂ (hp.w.trans ha₂.symm)
  have e₁ : a ≫ (fst Z₁ Z₂).left = a₁ := hP.lift_fst _ _ _
  have e₂ : a ≫ (snd Z₁ Z₂).left = a₂ := hP.lift_snd _ _ _
  let i : Y ⟶ Wd := hW.lift a s (by rw [← hfw, ← Category.assoc, e₁, hp.w])
  have i₁ : i ≫ π = a := hW.lift_fst _ _ _
  have i₂ : i ≫ s' = s := hW.lift_snd _ _ _
  let q : Wd ⟶ Y := hp.lift (π ≫ (fst Z₁ Z₂).left) s' (by rw [Category.assoc, hfw, hW.w])
  have q₁ : q ≫ a₁ = π ≫ (fst Z₁ Z₂).left := hp.lift_fst _ _ _
  have q₂ : q ≫ s = s' := hp.lift_snd _ _ _
  have hq : IsPullback π q (fst Z₁ Z₂).left a₁ := by
    refine IsPullback.of_bot ?_ q₁.symm hp
    rw [q₂, hfw]; exact hW
  have hsf : IsSeparated (fst Z₁ Z₂).left :=
    MorphismProperty.of_isPullback (P := @IsSeparated) hP.flip inferInstance
  have hsq : IsSeparated q := MorphismProperty.of_isPullback (P := @IsSeparated) hq hsf
  have hiq : i ≫ q = 𝟙 Y := by
    refine hp.hom_ext ?_ ?_
    · rw [Category.assoc, q₁, ← Category.assoc, i₁, e₁, Category.id_comp]
    · rw [Category.assoc, q₂, i₂, Category.id_comp]
  have hci : IsClosedImmersion i := by
    have : IsClosedImmersion (i ≫ q) := by rw [hiq]; infer_instance
    exact IsClosedImmersion.of_comp i q
  have hN : ((M₃.pull π).pull i).IsLB := pull_isLB r'.1 i
  have hc : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ Y) (v : σ₁ × σ₂ → T),
      SecCoord ((M₃.pull π).pull i) (fun j => GlobalTheory.ZM.RepBC.secPull _ i (th' j)) y v ↔
        SecCoord (M₃.pull π) th' (y ≫ i) v := fun T _ y v => GlobalTheory.ZM.RepBC.secCoord_pull _ th' i y v
  have rY := GlobalTheory.ZM.ClosedCoord.projRep_closed K _ _ Wd Y s' _ th' i _ _ r' hci hN hc
  have H : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ Y) (v₁ : σ₁ → T) (v₂ : σ₂ → T), SecCoord M₁ th₁ (y ≫ a₁) v₁ →
      SecCoord M₂ th₂ (y ≫ a₂) v₂ →
      SecCoord ((M₃.pull π).pull i) (fun j => GlobalTheory.ZM.RepBC.secPull _ i (th' j)) y (fun i => v₁ i.1 * v₂ i.2) := by
    intro T _ y v₁ v₂ h₁ h₂
    rw [hc, hbc, Category.assoc, i₁]
    refine hseg T _ v₁ v₂ ?_ ?_
    · rwa [Category.assoc, e₁]
    · rwa [Category.assoc, e₂]
  rw [i₂, idealOf_eq_graphIdeal s M₁ th₁ a₁ M₂ th₂ a₂ _ _ r₁.1 r₂.1 hN H] at rY
  exact ⟨_, _, rY, H⟩

end GlobalTheory.ZM.GraphSegre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PulledSectionsFormBasisIdOfPulledSectionsFormBas
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum

namespace GlobalTheory.ModelSum

theorem exists_pull_LPow_sec {Z : Scheme.{0}} (G : Over Z) (L : LB G.left) (hL : L.IsLB) (N : ℕ) {T T' : Over Z}
    (h : T' ⟶ T) (b : LB.Sec (Out.LPow G L (N : ℤ) T)) :
    ∃ b' : LB.Sec (Out.LPow G L (N : ℤ) T'), ∀ (Y : Scheme.{0}) (r : Y ⟶ (T' ⊗ G).left) (z : Y) (J), Good L z J →
      sval (L := L) (φ := fun _ : Fin 1 => (snd T' G).left) (ε := fun _ => (N : ℤ)) b' r z J =
        sval (L := L) (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => (N : ℤ)) b (r ≫ (h ▷ G).left) z J := by
  have hu : (LB.oneGen L (Y := (T' ⊗ G).left)).IsGen := by
    intro (i : PEmpty → L.ι) (j : PEmpty → L.ι)
    simp [LB.oneGen, LB.LinComb, res]
    ext
    erw [Units.val_mul, Units.coe_map, Units.coe_map, Units.val_one, _root_.one_mul, map_one, map_one]
  have hf : FormEq (Sum.elim (fun _ : Fin 1 => (h ▷ G).left ≫ (snd T G).left)
      (PEmpty.elim : PEmpty → ((T' ⊗ G).left ⟶ G.left))) (Sum.elim (fun _ => (N : ℤ)) PEmpty.elim)
      (fun _ : Fin 1 => (snd T' G).left) (fun _ => (N : ℤ)) := by
    intro U _ f
    simp [Fintype.prod_sum_type]
  obtain ⟨b', hb'⟩ := exists_sec hL hf
    (pullMulSec (L := L) (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => (N : ℤ)) b (h ▷ G).left
      (LB.oneGen L (Y := (T' ⊗ G).left)) hu)
  refine ⟨b', fun Y r z J hJ => (hb' Y r z J hJ).trans ((sval_pullMulSec _ _ _ hu r z hJ).trans ?_)⟩
  rw [val_one, Units.val_one, _root_.mul_one]

theorem basisAlong_id_of_basisAlong : ∀ (Z : Scheme.{0}) (G : Over Z) (L : LB G.left) (N n : ℕ) (T T' : Over Z) (h : T' ⟶ T) (b : Fin n → LB.Sec (Out.LPow G L (N : ℤ) T)), L.IsLB → GlobalTheory.LN.BasisAlong G L N h b → ∃ b' : Fin n → LB.Sec (Out.LPow G L (N : ℤ) T'), GlobalTheory.LN.BasisAlong G L N (𝟙 T') b' := by
  intro Z G L N n T T' h b hL hB
  choose b' hb' using fun i => exists_pull_LPow_sec G L hL N h (b i)
  have key : ∀ s c, GlobalTheory.LN.Lin G L N (𝟙 T') b' c s ↔ GlobalTheory.LN.Lin G L N h b c s := by
    intro s c
    have e : ∀ i (z : (T' ⊗ G).left) J, Good L z J →
        sval (L := L) (φ := fun _ : Fin 1 => (snd T' G).left) (ε := fun _ => (N : ℤ)) (b' i) ((𝟙 T') ▷ G).left z J =
          sval (L := L) (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => (N : ℤ)) (b i) (h ▷ G).left z J := by
      intro i z J hJ
      rw [hb' i _ _ z J hJ]
      simp
    unfold GlobalTheory.LN.Lin
    refine forall_congr' fun z => forall_congr' fun J => imp_congr_right fun hJ => ?_
    simp only [e _ z J hJ]
  unfold GlobalTheory.LN.BasisAlong at hB ⊢
  refine ⟨b', fun s => ?_⟩
  obtain ⟨c, hc, hu⟩ := hB s
  exact ⟨c, (key s c).2 hc, fun c' hc' => hu c' ((key s c').1 hc')⟩

end GlobalTheory.ModelSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfFaithfullyFlat
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM

namespace GlobalTheory.AmpleDescent

theorem relAmple_of_faithfullyFlat : ∀ (R R' : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing R'] [IsLocalRing R'] [Algebra R R'] [Module.FaithfullyFlat R R'] (B : Over (Sp R)) (B' : Over (Sp R')) [GrpObj B] [GrpObj B'] (φ : B'.left ⟶ B.left) (L : LB B.left) (L' : LB B'.left), IsAbelianScheme B → IsGrpPullback B' B (spMap (algebraMap R R')) φ → L.IsLB → L'.IsLB → LBIso L' (L.pull φ) → RelAmple B' L' → RelAmple B L := by
  intro R R' _ _ _ _ _ _ _ B B' _ _ φ L L' hB h hL hL' hw hA
  have : Flat (Out.specOf (algebraMap R R')) :=
    (HasRingHomProperty.Spec_iff (P := @Flat)).2 (RingHom.flat_algebraMap_iff.2 inferInstance)
  have : Surjective (Out.specOf (algebraMap R R')) :=
    ⟨PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := R) (B := R')⟩
  have : IsProper B.hom := hB.proper
  have : IsProper B'.hom :=
    MorphismProperty.of_isPullback (P := @IsProper) h.1 inferInstance
  have : CompactSpace B.left := QuasiCompact.compactSpace_of_compactSpace B.hom
  have : QuasiSeparatedSpace B.left := quasiSeparatedSpace_of_quasiSeparated B.hom
  refine (relAmple_iff_isAmpleLB_of_isAffine B hL).2 (isAmpleLB_of_pull (algebraMap R R') h.1 hL ?_)
  exact (isAmpleLB_of_relAmple_of_isAffine B' hL' hA).of_lbIso (LB.isLB_pull hL φ) hw.symm

end GlobalTheory.AmpleDescent
end

