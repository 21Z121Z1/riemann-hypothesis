import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0053
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SymmetricLiftTorsionPointActionOnTheta
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0059

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.GeneratorIsoExtendFromOpenContainingCharts
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.GenPush

variable {X Y : Scheme.{0}}

private theorem gm_res_eq_gm {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) {U V : X.Opens} {h : V ≤ U} (hy : f y ∈ V)
    (a : Γ(X, U)ˣ) : gm f y V (res h a) = gm f y U a := by
  apply Units.ext
  rw [← gs_unit f y V hy, ← gs_unit f y U (h hy)]
  exact gs_res f y h hy a.val

private theorem gm_id_pullU_eq_gm {X Y : Scheme.{0}} (c : Y ⟶ X) (y : Y) {U : X.Opens} (hy : c y ∈ U)
    (a : Γ(X, U)ˣ) : gm (𝟙 Y) y (c ⁻¹ᵁ U) (pullU c U a) = gm c y U a := by
  have hy' : (𝟙 Y ≫ c) y ∈ U := by simpa using hy
  apply Units.ext
  rw [← gs_unit (𝟙 Y) y (c ⁻¹ᵁ U) (by simpa using hy), ← gs_unit c y U hy]
  have e := gs_pull (𝟙 Y) c y U (by simpa using hy) a.val
  rw [Category.id_comp] at e
  exact e

private theorem mem_pull_U_of_mem {X Y : Scheme.{0}} (N : LB X) (c : Y ⟶ X) {y : Y} {a : N.ι} (ha : c y ∈ N.U a) :
    y ∈ (N.pull c).U (fun _ => a) := by
  unfold LB.pull LB.LinComb LB.wchart
  exact Set.mem_iInter.2 fun _ => ha

private theorem gm_id_pull_g_eq_gm_g {X Y : Scheme.{0}} (N : LB X) (c : Y ⟶ X) (y : Y) {a b : N.ι} (ha : c y ∈ N.U a)
    (hb : c y ∈ N.U b) :
    gm (𝟙 Y) y ((N.pull c).U (fun _ => a) ⊓ (N.pull c).U (fun _ => b)) ((N.pull c).g (fun _ => a) (fun _ => b)) =
      gm c y (N.U a ⊓ N.U b) (N.g a b) := by
  have hm : (𝟙 Y) y ∈ (N.pull c).U (fun _ => a) ⊓ (N.pull c).U (fun _ => b) :=
    ⟨mem_pull_U_of_mem N c (by simpa using ha), mem_pull_U_of_mem N c (by simpa using hb)⟩
  revert hm
  unfold LB.pull LB.LinComb
  dsimp only
  intro hm
  simp only [Finset.univ_unique, Finset.prod_singleton, zpow_one]
  exact (gm_res_eq_gm (𝟙 Y) y hm _).trans (gm_id_pullU_eq_gm c y (show c y ∈ N.U a ⊓ N.U b from ⟨ha, hb⟩) _)

private theorem gm_div_g_eq_mul_inv {X Y : Scheme.{0}} (A B : LB X) (f : Y ⟶ X) (y : Y) (p q : (A.div B).ι)
    (hp : f y ∈ A.U p.1 ⊓ B.U p.2) (hq : f y ∈ A.U q.1 ⊓ B.U q.2) :
    gm f y ((A.div B).U p ⊓ (A.div B).U q) ((A.div B).g p q) =
      gm f y (A.U p.1 ⊓ A.U q.1) (A.g p.1 q.1) * (gm f y (B.U p.2 ⊓ B.U q.2) (B.g p.2 q.2))⁻¹ := by
  unfold LB.div
  dsimp only
  rw [map_mul, map_inv, gm_res_eq_gm f y (V := (A.U p.1 ⊓ B.U p.2) ⊓ (A.U q.1 ⊓ B.U q.2)) ⟨hp, hq⟩,
    gm_res_eq_gm f y (V := (A.U p.1 ⊓ B.U p.2) ⊓ (A.U q.1 ⊓ B.U q.2)) ⟨hp, hq⟩]

theorem exists_gen_of_units (c : Y ⟶ X) [IsOpenImmersion c] (N : LB X) (hN : ∀ a, N.U a ≤ c.opensRange)
    (V : N.ι → Y.Opens) (hV : ∀ a y, c y ∈ N.U a → y ∈ V a) (s : ∀ a, Γ(Y, V a)ˣ)
    (hs : ∀ (y : Y) a b, c y ∈ N.U a → c y ∈ N.U b →
      gm (𝟙 Y) y (V a) (s a) = gm c y (N.U a ⊓ N.U b) (N.g a b) * gm (𝟙 Y) y (V b) (s b)) :
    ∃ t : N.Gen, t.IsGen := by
  have hW : ∀ a, c ⁻¹ᵁ N.U a ≤ V a := fun a y hy => hV a y hy
  choose b hb using fun a => exists_ext_unit c (c ⁻¹ᵁ N.U a) (res (hW a) (s a))
  have hE : ∀ a, N.U a ≤ c ''ᵁ (c ⁻¹ᵁ N.U a) := by
    intro a x hx
    obtain ⟨y, rfl⟩ : x ∈ Set.range c := hN a hx
    exact ⟨y, hx, rfl⟩
  have key : ∀ (y : Y) a, c y ∈ N.U a → gm c y (c ''ᵁ (c ⁻¹ᵁ N.U a)) (b a) = gm (𝟙 Y) y (V a) (s a) := by
    intro y a ha
    have e := hb a Y (𝟙 Y) y (by simpa using ha)
    rw [Category.id_comp] at e
    rw [e, gm_res_eq_gm (𝟙 Y) y (by simpa using ha)]
  refine ⟨⟨fun a => res (hE a) (b a)⟩, ?_⟩
  unfold LB.Gen.IsGen
  intro a a'
  apply Units.ext
  apply fn_ext
  intro x hx
  obtain ⟨y, rfl⟩ : x ∈ Set.range c := hN a hx.1
  have hx' : (𝟙 X) (c y) ∈ N.U a ⊓ N.U a' := by simpa using hx
  rw [gs_unit (𝟙 X) (c y) _ hx', gs_unit (𝟙 X) (c y) _ hx']
  congr 1
  apply gm_inj c y hx hx
  rw [map_mul, gm_res_eq_gm c y hx, gm_res_eq_gm c y hx.1, gm_res_eq_gm c y hx, gm_res_eq_gm c y hx.2,
    key y a hx.1, key y a' hx.2]
  exact hs y a a' hx.1 hx.2

theorem gen_stalk {N : LB Y} {t : N.Gen} (ht : t.IsGen) (y : Y) (i j : N.ι) (hi : y ∈ N.U i) (hj : y ∈ N.U j) :
    gm (𝟙 Y) y (N.U i) (t.s i) = gm (𝟙 Y) y (N.U i ⊓ N.U j) (N.g i j) * gm (𝟙 Y) y (N.U j) (t.s j) := by
  unfold LB.Gen.IsGen at ht
  have hm : (𝟙 Y) y ∈ N.U i ⊓ N.U j := by simpa using (⟨hi, hj⟩ : y ∈ N.U i ⊓ N.U j)
  have e := congrArg (gm (𝟙 Y) y (N.U i ⊓ N.U j)) (ht i j)
  rw [map_mul, gm_res_eq_gm (𝟙 Y) y hm, gm_res_eq_gm (𝟙 Y) y hm] at e
  exact e

theorem gen_iso_of_charts_le_range : ∀ (X Y : Scheme.{0}) (c : Y ⟶ X) [IsOpenImmersion c], (∀ N : LB X, (∀ a, N.U a ≤ c.opensRange) → (∃ t : (N.pull c).Gen, t.IsGen) → ∃ t : N.Gen, t.IsGen) ∧ ∀ M M' : LB X, (∀ a b, M.U a ⊓ M'.U b ≤ c.opensRange) → LBIso (M.pull c) (M'.pull c) → LBIso M M' := by
  intro X Y c _
  refine ⟨fun N hN ⟨t, ht⟩ => ?_, fun M M' hM ⟨w, hw⟩ => ?_⟩
  · refine exists_gen_of_units c N hN (fun a => (N.pull c).U (fun _ => a)) (fun a y hy => mem_pull_U_of_mem N c hy)
      (fun a => t.s (fun _ => a)) ?_
    intro y a b ha hb
    rw [gen_stalk ht y (fun _ => a) (fun _ => b) (mem_pull_U_of_mem N c ha) (mem_pull_U_of_mem N c hb),
      gm_id_pull_g_eq_gm_g N c y ha hb]
  · have hN : ∀ p : (M'.div M).ι, (M'.div M).U p ≤ c.opensRange := by
      intro p
      show M'.U p.1 ⊓ M.U p.2 ≤ _
      rw [inf_comm]
      exact hM p.2 p.1
    have hV : ∀ (p : (M'.div M).ι) (y : Y), c y ∈ (M'.div M).U p →
        y ∈ ((M'.pull c).div (M.pull c)).U ((fun _ => p.1, fun _ => p.2) : (M'.pull c).ι × (M.pull c).ι) :=
      fun p y hy => ⟨mem_pull_U_of_mem M' c hy.1, mem_pull_U_of_mem M c hy.2⟩
    obtain ⟨t, ht⟩ := exists_gen_of_units c (M'.div M) hN
      (fun p => ((M'.pull c).div (M.pull c)).U ((fun _ => p.1, fun _ => p.2) : (M'.pull c).ι × (M.pull c).ι)) hV
      (fun p => w.s ((fun _ => p.1, fun _ => p.2) : (M'.pull c).ι × (M.pull c).ι)) (by
        intro y p q hp hq
        rw [gen_stalk hw y _ _ (hV p y hp) (hV q y hq)]
        congr 1
        have m1 : (𝟙 Y) y ∈ (M'.pull c).U (fun _ => p.1) ⊓ (M.pull c).U (fun _ => p.2) := by
          have h : y ∈ (M'.pull c).U (fun _ => p.1) ⊓ (M.pull c).U (fun _ => p.2) := hV p y hp
          simpa using h
        have m2 : (𝟙 Y) y ∈ (M'.pull c).U (fun _ => q.1) ⊓ (M.pull c).U (fun _ => q.2) := by
          have h : y ∈ (M'.pull c).U (fun _ => q.1) ⊓ (M.pull c).U (fun _ => q.2) := hV q y hq
          simpa using h
        have e1 := gm_div_g_eq_mul_inv (M'.pull c) (M.pull c) (𝟙 Y) y
          ((fun _ => p.1, fun _ => p.2) : (M'.pull c).ι × (M.pull c).ι)
          ((fun _ => q.1, fun _ => q.2) : (M'.pull c).ι × (M.pull c).ι) m1 m2
        have e2 := gm_div_g_eq_mul_inv M' M c y p q hp hq
        refine e1.trans (Eq.trans ?_ e2.symm)
        dsimp only
        rw [gm_id_pull_g_eq_gm_g M' c y hp.1 hq.1, gm_id_pull_g_eq_gm_g M c y hp.2 hq.2])
    exact ⟨t, ht⟩

end GlobalTheory.GenPush
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.GlueSchemesOverOpensAlongCocycle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.CocycleGlue

theorem exists_desc (D : Scheme.GlueData.{0}) {S : Scheme.{0}} (p : ∀ i, D.U i ⟶ S)
    (h : ∀ i j, D.f i j ≫ p i = (D.t i j ≫ D.f j i) ≫ p j) :
    ∃ F : D.glued ⟶ S, ∀ i, D.ι i ≫ F = p i := by
  exact GlobalTheory.CoverGlue.exists_hom (ψ := D.ι) (fun i => inferInstance)
    (fun x => by
      obtain ⟨i, y, hy⟩ := D.ι_jointly_surjective x
      exact ⟨i, y, hy⟩)
    p (B := fun i j => D.V (i, j)) (a := fun i j => D.f i j) (b := fun i j => D.t i j ≫ D.f j i)
    (fun i j => IsPullback.of_isLimit (D.vPullbackConeIsLimit i j)) h

theorem exists_glue {S : Scheme.{0}} {I : Type} (V X : I → Scheme.{0}) (κ : ∀ i, V i ⟶ S)
    (hκ : ∀ i, IsOpenImmersion (κ i)) (g : ∀ i, X i ⟶ V i) (B : I → I → Scheme.{0})
    (a : ∀ i j, B i j ⟶ X i) (b : ∀ i j, B i j ⟶ X j)
    (ha : ∀ i j, IsPullback (a i j) (b i j ≫ g j) (g i ≫ κ i) (κ j))
    (hb : ∀ i j, IsPullback (b i j) (a i j ≫ g i) (g j ≫ κ j) (κ i))
    (hc : ∀ i j k (T : Scheme.{0}) (x : T ⟶ B i j) (y : T ⟶ B j k) (z : T ⟶ B i k),
      x ≫ b i j = y ≫ a j k → x ≫ a i j = z ≫ a i k → y ≫ b j k = z ≫ b i k) :
    ∃ (A : Scheme.{0}) (F : A ⟶ S) (ψ : ∀ i, X i ⟶ A),
      (∀ i, IsPullback (ψ i) (g i) F (κ i)) ∧ ∀ i j, IsPullback (a i j) (b i j) (ψ i) (ψ j) := by
  classical
  have hma : ∀ i j, IsOpenImmersion (a i j) := fun i j =>
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (ha i j).flip (hκ j)
  have mono_a : ∀ i j, Mono (a i j) := fun i j => by
    have := hma i j
    infer_instance
  have mono_κ : ∀ i, Mono (κ i) := fun i => by
    have := hκ i
    infer_instance
  have ext_a : ∀ i j {T : Scheme.{0}} (x y : T ⟶ B i j), x ≫ a i j = y ≫ a i j → x = y :=
    fun i j _ x y h => (mono_a i j).right_cancellation x y h
  have ext_κ : ∀ i {T : Scheme.{0}} (x y : T ⟶ V i), x ≫ κ i = y ≫ κ i → x = y :=
    fun i _ x y h => (mono_κ i).right_cancellation x y h
  have hbw : ∀ i j, b i j ≫ g j ≫ κ j = a i j ≫ g i ≫ κ i := fun i j => by
    simpa only [Category.assoc] using (hb i j).w
  have iso_a : ∀ i, IsIso (a i i) := fun i => by
    have hw : a i i ≫ g i = b i i ≫ g i := ext_κ i _ _ (by
      rw [Category.assoc]
      exact (ha i i).w)
    refine ⟨⟨(ha i i).lift (𝟙 _) (g i) (by simp), ?_, (ha i i).lift_fst _ _ _⟩⟩
    apply ext_a i i
    rw [Category.assoc, (ha i i).lift_fst, Category.comp_id, Category.id_comp]
  have iso_b : ∀ i, IsIso (b i i) := fun i => by
    have hw : b i i ≫ g i = a i i ≫ g i := ext_κ i _ _ (by
      rw [Category.assoc]
      exact (hb i i).w)
    have hmb : Mono (b i i) := by
      have := MorphismProperty.of_isPullback (P := @IsOpenImmersion) (hb i i).flip (hκ i)
      infer_instance
    refine ⟨⟨(hb i i).lift (𝟙 _) (g i) (by simp), ?_, (hb i i).lift_fst _ _ _⟩⟩
    apply hmb.right_cancellation
    rw [Category.assoc, (hb i i).lift_fst, Category.comp_id, Category.id_comp]
  have diag : ∀ i, a i i = b i i := fun i => by
    have := iso_a i
    have := iso_b i
    have h := hc i i i (B i i) (𝟙 _) (b i i ≫ inv (a i i)) (𝟙 _) (by simp) (by simp)
    have h2 : inv (a i i) ≫ b i i = 𝟙 _ := by
      rw [← cancel_epi (b i i)]
      simpa using h
    rw [IsIso.inv_comp_eq, Category.comp_id] at h2
    exact h2.symm
  have ht : ∀ i j, ∃ t : B i j ⟶ B j i, t ≫ a j i = b i j ∧ t ≫ b j i = a i j := fun i j => by
    have := iso_a i
    refine ⟨(ha j i).lift (b i j) (a i j ≫ g i) (hb i j).w, (ha j i).lift_fst _ _ _, ?_⟩
    have h := hc i j i (B i j) (𝟙 _) ((ha j i).lift (b i j) (a i j ≫ g i) (hb i j).w)
      (a i j ≫ inv (a i i)) (by rw [IsPullback.lift_fst, Category.id_comp]) (by simp)
    rw [h, ← diag i]
    simp
  choose t ht_a ht_b using ht
  have t_id : ∀ i, t i i = 𝟙 _ := fun i =>
    ext_a i i _ _ (by rw [ht_a, Category.id_comp, diag])
  have t_inv : ∀ i j, t i j ≫ t j i = 𝟙 _ := fun i j =>
    ext_a i j _ _ (by rw [Category.assoc, ht_a, ht_b, Category.id_comp])
  have ht' : ∀ i j k, ∃ τ : pullback (a i j) (a i k) ⟶ pullback (a j k) (a j i),
      τ ≫ pullback.snd _ _ = pullback.fst _ _ ≫ t i j ∧
        τ ≫ pullback.fst _ _ ≫ a j k = pullback.fst _ _ ≫ b i j := fun i j k => by
    have w : (pullback.fst (a i j) (a i k) ≫ b i j) ≫ g j ≫ κ j =
        (pullback.snd (a i j) (a i k) ≫ b i k ≫ g k) ≫ κ k := by
      calc (pullback.fst (a i j) (a i k) ≫ b i j) ≫ g j ≫ κ j
          = pullback.fst (a i j) (a i k) ≫ a i j ≫ g i ≫ κ i := by rw [Category.assoc, hbw]
        _ = pullback.snd (a i j) (a i k) ≫ a i k ≫ g i ≫ κ i := by rw [pullback.condition_assoc]
        _ = (pullback.snd (a i j) (a i k) ≫ b i k ≫ g k) ≫ κ k := by
          rw [← hbw]
          simp only [Category.assoc]
    refine ⟨pullback.lift ((ha j k).lift _ _ w) (pullback.fst _ _ ≫ t i j) ?_, pullback.lift_snd _ _ _, ?_⟩
    · rw [IsPullback.lift_fst, Category.assoc, ht_a]
    · rw [pullback.lift_fst_assoc, IsPullback.lift_fst]
  choose t' ht'_snd ht'_fst using ht'
  have cocycle : ∀ i j k, t' i j k ≫ t' j k i ≫ t' k i j = 𝟙 _ := fun i j k => by
    have c1 := hc i j k _ (pullback.fst (a i j) (a i k)) (t' i j k ≫ pullback.fst _ _)
      (pullback.snd (a i j) (a i k)) (by rw [Category.assoc, ht'_fst]) pullback.condition
    have c2 : (t' i j k ≫ t' j k i) ≫ pullback.fst _ _ = pullback.snd (a i j) (a i k) ≫ t i k := by
      apply ext_a k i
      simp only [Category.assoc, ht'_fst, ht_a]
      simpa only [Category.assoc] using c1
    have c2' : ∀ {Z : Scheme.{0}} (h : B k i ⟶ Z),
        t' i j k ≫ t' j k i ≫ pullback.fst _ _ ≫ h = pullback.snd (a i j) (a i k) ≫ t i k ≫ h := by
      intro Z h
      simp only [← Category.assoc, c2]
    apply pullback.hom_ext
    · apply ext_a i j
      simp only [Category.assoc, Category.id_comp, ht'_fst]
      rw [c2' (b k i), ht_b]
      exact pullback.condition.symm
    · simp only [Category.assoc, Category.id_comp, ht'_snd]
      rw [c2' (t k i), t_inv, Category.comp_id]
  let D : Scheme.GlueData.{0} :=
    { J := I, U := X, V := fun p => B p.1 p.2, f := a, f_mono := mono_a,
      f_hasPullback := fun _ _ _ => inferInstance, f_id := iso_a, t := t, t_id := t_id,
      t' := t', t_fac := ht'_snd, cocycle := cocycle, f_open := hma }
  obtain ⟨F, hF⟩ := exists_desc D (fun i => g i ≫ κ i) (fun i j => by
    change a i j ≫ g i ≫ κ i = (t i j ≫ a j i) ≫ g j ≫ κ j
    rw [ht_a]
    exact (hbw i j).symm)
  have hV : ∀ i j, IsPullback (a i j) (b i j) (D.ι i) (D.ι j) := fun i j => by
    have h : IsPullback (D.f i j) (D.t i j ≫ D.f j i) (D.ι i) (D.ι j) :=
      IsPullback.of_isLimit (D.vPullbackConeIsLimit i j)
    have e : D.t i j ≫ D.f j i = b i j := ht_a i j
    rw [e] at h
    exact h
  refine ⟨D.glued, F, fun i => D.ι i, fun i => ?_, hV⟩
  have hw : D.ι i ≫ F = g i ≫ κ i := hF i
  have hιi : IsOpenImmersion (D.ι i) := D.ι_isOpenImmersion i
  have hr : ∀ {T : Scheme.{0}} (u : T ⟶ D.glued) (v : T ⟶ V i), u ≫ F = v ≫ κ i →
      Set.range u ⊆ Set.range (D.ι i) := by
    intro T u v huv x hx
    obtain ⟨t0, rfl⟩ := hx
    obtain ⟨j, y, hy⟩ := D.ι_jointly_surjective (u t0)
    have e1 : (g j ≫ κ j) y = κ i (v t0) := by
      have h1 := congrArg (fun φ : T ⟶ S => φ t0) huv
      have h2 := congrArg (fun φ : D.U j ⟶ S => φ y) (hF j)
      simp only [Scheme.Hom.comp_apply] at h1 h2 ⊢
      rw [← h2, hy]
      exact h1
    obtain ⟨z', hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := g j ≫ κ j) (g := κ i) y (v t0) e1
    refine ⟨b j i ((ha j i).isoPullback.inv z'), ?_⟩
    have h3 := congrArg (fun φ : pullback (g j ≫ κ j) (κ i) ⟶ D.glued => φ z')
      (congrArg (fun φ => (ha j i).isoPullback.inv ≫ φ) (hV j i).w)
    simp only [Scheme.Hom.comp_apply] at h3
    rw [← h3, ← hy, ← hz1, ← IsPullback.isoPullback_inv_fst (ha j i), Scheme.Hom.comp_apply]
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk hw
    (fun s => IsOpenImmersion.lift (D.ι i) s.fst (hr s.fst s.snd s.condition)) ?_ ?_ ?_)
  · intro s
    exact IsOpenImmersion.lift_fac _ _ _
  · intro s
    apply ext_κ i
    rw [Category.assoc, ← hw, ← Category.assoc, IsOpenImmersion.lift_fac, s.condition]
  · intro s m h1 _
    apply (cancel_mono (D.ι i)).1
    rw [h1, IsOpenImmersion.lift_fac]

theorem glue_over_opens : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (G : ∀ i, Over (U i).toScheme) (B : ∀ i j, Over (U i ⊓ U j).toScheme) (a : ∀ i j, (B i j).left ⟶ (G i).left) (b : ∀ i j, (B i j).left ⟶ (G j).left), (∀ i j, IsPullback (a i j) (B i j).hom (G i).hom (S.homOfLE inf_le_left)) → (∀ i j, IsPullback (b i j) (B i j).hom (G j).hom (S.homOfLE inf_le_right)) → (∀ i j k (T : Scheme.{0}) (x : T ⟶ (B i j).left) (y : T ⟶ (B j k).left) (z : T ⟶ (B i k).left), x ≫ b i j = y ≫ a j k → x ≫ a i j = z ≫ a i k → y ≫ b j k = z ≫ b i k) → ∃ (A : Over S) (ψ : ∀ i, (G i).left ⟶ A.left), (∀ i, IsPullback (ψ i) (G i).hom A.hom (U i).ι) ∧ ∀ i j, IsPullback (a i j) (b i j) (ψ i) (ψ j) := by
  intro S I U G B a b h1 h2 h3
  have ha : ∀ i j, IsPullback (a i j) (b i j ≫ (G j).hom) ((G i).hom ≫ (U i).ι) (U j).ι := by
    intro i j
    have h := (h1 i j).paste_vert (isPullback_opens_inf (U i) (U j))
    rw [← (h2 i j).w] at h
    exact h
  have hb : ∀ i j, IsPullback (b i j) (a i j ≫ (G i).hom) ((G j).hom ≫ (U j).ι) (U i).ι := by
    intro i j
    have h := (h2 i j).paste_vert (isPullback_opens_inf (U i) (U j)).flip
    rw [← (h1 i j).w] at h
    exact h
  obtain ⟨A, F, ψ, hψ, hab⟩ := exists_glue (fun i => (U i).toScheme) (fun i => (G i).left)
    (fun i => (U i).ι) (fun i => inferInstance) (fun i => (G i).hom) (fun i j => (B i j).left)
    a b ha hb h3
  exact ⟨Over.mk F, ψ, hψ, hab⟩

end GlobalTheory.CocycleGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.GroupLawsOnCoverAgreeOnCommonPoints
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.CoverOpCompat

section
variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

private lemma isGrpPullback_one_left (h : IsGrpPullback G' G f φ) {T : Scheme.{0}} (ρ : T ⟶ S') :
    (1 : Over.mk (ρ ≫ f) ⟶ G).left = (1 : Over.mk ρ ⟶ G').left ≫ φ := by

  have hw : ((1 : Over.mk ρ ⟶ G').left ≫ φ) ≫ G.hom = (Over.mk (ρ ≫ f)).hom := by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w]
    rfl
  let u : Over.mk (ρ ≫ f) ⟶ G := Over.homMk _ hw
  have huu : (u * u).left = ((1 : Over.mk ρ ⟶ G') * 1).left ≫ φ := h.2 (Over.mk ρ) 1 1 u u rfl rfl
  rw [_root_.mul_one] at huu
  have hsq : u * u = u := Over.OverMorphism.ext huu
  have hu : u = 1 := by
    calc u = u * u * u⁻¹ := (_root_.mul_inv_cancel_right u u).symm
      _ = 1 := by rw [hsq, _root_.mul_inv_cancel]
  rw [← hu]
  rfl

theorem push_mul (h : IsGrpPullback G' G f φ) {T : Scheme.{0}} {ρ : T ⟶ S'} {r : T ⟶ S} (e : r = ρ ≫ f)
    (p q : Over.mk ρ ⟶ G') (x y : Over.mk r ⟶ G) (hx : x.left = p.left ≫ φ) (hy : y.left = q.left ≫ φ) :
    (x * y).left = (p * q).left ≫ φ := by
  subst e
  exact h.2 (Over.mk ρ) p q x y hx hy

theorem push_inv (h : IsGrpPullback G' G f φ) {T : Scheme.{0}} {ρ : T ⟶ S'} {r : T ⟶ S} (e : r = ρ ≫ f)
    (p : Over.mk ρ ⟶ G') (x : Over.mk r ⟶ G) (hx : x.left = p.left ≫ φ) :
    (x⁻¹).left = (p⁻¹).left ≫ φ := by
  subst e

  have hw : ((p⁻¹).left ≫ φ) ≫ G.hom = (Over.mk (ρ ≫ f)).hom := by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w]
    rfl
  let z : Over.mk (ρ ≫ f) ⟶ G := Over.homMk _ hw
  have hxz : (x * z).left = (p * p⁻¹).left ≫ φ := push_mul h rfl p p⁻¹ x z hx rfl
  rw [_root_.mul_inv_cancel, ← isGrpPullback_one_left h ρ] at hxz
  have hxz' : x * z = 1 := Over.OverMorphism.ext hxz
  have hz : x⁻¹ = z := (_root_.eq_inv_of_mul_eq_one_right hxz').symm
  rw [hz]
  rfl

theorem push_one (h : IsGrpPullback G' G f φ) :
    f ≫ (1 : Out.baseOver S ⟶ G).left = (1 : Out.baseOver S' ⟶ G').left ≫ φ := by

  let c : Over.mk ((Out.baseOver S').hom ≫ f) ⟶ Out.baseOver S :=
    Over.homMk f (by simp [Out.baseOver])
  have hc : c ≫ (1 : Out.baseOver S ⟶ G) = 1 := MonObj.comp_one c
  have hl : f ≫ (1 : Out.baseOver S ⟶ G).left = (1 : Over.mk ((Out.baseOver S').hom ≫ f) ⟶ G).left := by
    rw [← hc]
    rfl
  rw [hl]
  exact isGrpPullback_one_left h (Out.baseOver S').hom

end

theorem opCompat : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left) (B : ∀ i j, Over (U i ⊓ U j).toScheme) [∀ i j, GrpObj (B i j)] (a : ∀ i j, (B i j).left ⟶ (G i).left) (b : ∀ i j, (B i j).left ⟶ (G j).left), (∀ i, IsPullback (ψ i) (G i).hom A.hom (U i).ι) → (∀ i j, IsGrpPullback (B i j) (G i) (S.homOfLE inf_le_left) (a i j)) → (∀ i j, IsGrpPullback (B i j) (G j) (S.homOfLE inf_le_right) (b i j)) → (∀ i j, IsPullback (a i j) (b i j) (ψ i) (ψ j)) → (∀ i j (T : Scheme.{0}) (r : T ⟶ (U i).toScheme) (r' : T ⟶ (U j).toScheme) (x y : Over.mk r ⟶ G i) (x' y' : Over.mk r' ⟶ G j), x.left ≫ ψ i = x'.left ≫ ψ j → y.left ≫ ψ i = y'.left ≫ ψ j → (x * y).left ≫ ψ i = (x' * y').left ≫ ψ j ∧ (x⁻¹).left ≫ ψ i = (x'⁻¹).left ≫ ψ j) ∧ ∀ i j, S.homOfLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ (1 : Out.baseOver (U i).toScheme ⟶ G i).left ≫ ψ i = S.homOfLE (inf_le_right : U i ⊓ U j ≤ U j) ≫ (1 : Out.baseOver (U j).toScheme ⟶ G j).left ≫ ψ j := by
  intro S I U A G _ ψ B _ a b _ ha hb hsq
  refine ⟨fun i j T r r' x y x' y' hx hy => ?_, fun i j => ?_⟩
  ·
    let p : T ⟶ (B i j).left := (hsq i j).lift x.left x'.left hx
    let q : T ⟶ (B i j).left := (hsq i j).lift y.left y'.left hy
    have hpa : p ≫ a i j = x.left := (hsq i j).lift_fst _ _ _
    have hpb : p ≫ b i j = x'.left := (hsq i j).lift_snd _ _ _
    have hqa : q ≫ a i j = y.left := (hsq i j).lift_fst _ _ _
    have hqb : q ≫ b i j = y'.left := (hsq i j).lift_snd _ _ _
    let ρ : T ⟶ (U i ⊓ U j).toScheme := p ≫ (B i j).hom
    have er : r = ρ ≫ S.homOfLE (inf_le_left : U i ⊓ U j ≤ U i) := by
      show r = (p ≫ (B i j).hom) ≫ _
      rw [Category.assoc, ← (ha i j).1.w, ← Category.assoc, hpa]
      exact (Over.w x).symm
    have er' : r' = ρ ≫ S.homOfLE (inf_le_right : U i ⊓ U j ≤ U j) := by
      show r' = (p ≫ (B i j).hom) ≫ _
      rw [Category.assoc, ← (hb i j).1.w, ← Category.assoc, hpb]
      exact (Over.w x').symm
    have eq : q ≫ (B i j).hom = ρ := by
      apply (cancel_mono (S.homOfLE (inf_le_left : U i ⊓ U j ≤ U i))).1
      rw [Category.assoc, ← (ha i j).1.w, ← Category.assoc, hqa]
      exact (Over.w y).trans er
    let P : Over.mk ρ ⟶ B i j := Over.homMk p rfl
    let Q : Over.mk ρ ⟶ B i j := Over.homMk q eq
    have m1 := push_mul (ha i j) er P Q x y hpa.symm hqa.symm
    have m2 := push_mul (hb i j) er' P Q x' y' hpb.symm hqb.symm
    have i1 := push_inv (ha i j) er P x hpa.symm
    have i2 := push_inv (hb i j) er' P x' hpb.symm
    refine ⟨?_, ?_⟩
    · rw [m1, m2]
      simp only [Category.assoc]
      rw [(hsq i j).w]
    · rw [i1, i2]
      simp only [Category.assoc]
      rw [(hsq i j).w]
  ·
    have e1 := congrArg (· ≫ ψ i) (push_one (ha i j))
    have e2 := congrArg (· ≫ ψ j) (push_one (hb i j))
    simp only [Category.assoc] at e1 e2
    rw [e1, e2, (hsq i j).w]

end GlobalTheory.CoverOpCompat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SymmetricLiftTorsionPointActionOnThetaStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.symmetricLift_torsionPoint_action_on_theta : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (N : ℕ) (l : u.Λ) (f : (Fin P.g → ℂ) → ℂ) (T : Over (Sp ℂ)) [IsIso T.hom] (p : 𝟙_ (Over (Sp ℂ)) ⟶ T) (x : T ⟶ P.A) (U : Out.ThetaGrp P.A P.L ((N : ℤ) ^ 2) T) (s s' : LB.Sec (Out.LPow P.A P.L ((N : ℤ) ^ 2) T)), u.IsAH Hm χ → Odd N → p ≫ x = u.ex (((N : ℂ) ^ 2)⁻¹ • (l : Fin P.g → ℂ)) → Out.SymLift P.A P.L ((N : ℤ) ^ 2) (N ^ 2) x U → Out.IsActOf P.A P.L ((N : ℤ) ^ 2) U s s' → (∀ (j : Fin 1 → P.L.ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U (j 0) → valAt' (lift p (u.ex z)).left ((Out.LPow P.A P.L ((N : ℤ) ^ 2) T).U j) (s.f j) = f z * u.fr (j 0) z ^ (((N : ℤ) ^ 2) : ℤ)) → (∀ (j : Fin 1 → P.L.ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U (j 0) → valAt' (lift p (u.ex z)).left ((Out.LPow P.A P.L ((N : ℤ) ^ 2) T).U j) (s'.f j) = (χ l * Complex.exp (-(Real.pi / 2 / (N : ℂ) ^ 2) * hermForm Hm l l - Real.pi * hermForm Hm z l) * f (z + ((N : ℂ) ^ 2)⁻¹ • (l : Fin P.g → ℂ))) * u.fr (j 0) z ^ (((N : ℤ) ^ 2) : ℤ)) := by
  first | exact @GlobalTheory.symLift_act_in_frame | exact GlobalTheory.symLift_act_in_frame | (intros; apply GlobalTheory.symLift_act_in_frame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaPointsVanishingIdealRadicalHomogeneousStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
theorem _root_.GlobalTheory.T.thetaPointsVanishingIdeal_radical_homogeneous : ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (C : TObj g (N' ^ 2) J b (spMap em) → Prop), Function.Injective em → (thIdeal em C).IsRadical ∧ (∀ F ∈ thIdeal em C, ∀ e, MvPolynomial.homogeneousComponent e F ∈ thIdeal em C) ∧ ∀ (c : o) F, c ≠ 0 → MvPolynomial.C c * F ∈ thIdeal em C → F ∈ thIdeal em C := by
  first | exact @GlobalTheory.ZM.ThIdeal.thIdeal_radical_homogeneous_torsionFree | exact GlobalTheory.ZM.ThIdeal.thIdeal_radical_homogeneous_torsionFree | (intros; apply GlobalTheory.ZM.ThIdeal.thIdeal_radical_homogeneous_torsionFree <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TransportThetaLevelUniformisationCoordinatesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transport_thetaLevel_uniformisation_coordinates : ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (em : o →+* ℂ) (w w' : J) (t : TObj g k J b (spMap em)) (La : Type) [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (lam : Fin (2 * g) → La) (ac : J → La → La) (Q : La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (La' : Type) [AddCommGroup La'] (EF' : LinearMap.BilinForm ℤ La') (lam' : Fin (2 * g) → La') (ac' : J → La' → La') (Q' : La' →+ (Fin g → ℂ)) (Hm' : Matrix (Fin g) (Fin g) ℂ) (e : La ≃+ La') (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = EF x y) → (Function.Injective Q' ∧ DiscreteTopology (Q').range ∧ Submodule.span ℝ (Set.range Q') = ⊤ ∧ (Hm').IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm' z z).re) ∧ ∀ x y, (hermForm Hm' (Q' x) (Q' y)).im = EF' x y) → (∀ x, Q' (e x) = h (Q x)) → (∀ x y, EF' (e x) (e y) = EF x y) → (∀ j x, e (ac j x) = ac' j (e x)) → (∀ i, ∃ y, e (lam i) = lam' i + k • y) → (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH Hm χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ (Q).range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = Q x → χ' l = (-1) ^ EF x (ac w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((k : ℕ) : ℂ)⁻¹ • Q (lam i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q (ac j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) → (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH Hm' χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ (Q').range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = Q' x → χ' l = (-1) ^ EF' x (ac' w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((k : ℕ) : ℂ)⁻¹ • Q' (lam' i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q' x) = Q' (ac' j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) := by
  first | exact @GlobalTheory.UnifTransport.transport_uniformisation | exact GlobalTheory.UnifTransport.transport_uniformisation | (intros; apply GlobalTheory.UnifTransport.transport_uniformisation <;> assumption)
end

