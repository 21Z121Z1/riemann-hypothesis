import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0019
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0015
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaOfTranslDiff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0090
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecEqZeroAndHomEqOfThickenings

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.InKSubgroupTwist
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UU.KTwist

open GlobalTheory.KerPow

section General

variable {X Y B : Scheme.{0}} {N N' : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

theorem gen_div_of_gen {M M' : LB Y} (h : ∃ t : LB.Gen M, t.IsGen) (h' : ∃ t : LB.Gen M', t.IsGen) :
    ∃ t : LB.Gen (LB.div M M'), t.IsGen := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨t', ht'⟩ := h'
  refine ⟨⟨fun p => res (inf_le_left : M.U p.1 ⊓ M'.U p.2 ≤ _) (t.s p.1) *
    (res (inf_le_right : M.U p.1 ⊓ M'.U p.2 ≤ _) (t'.s p.2))⁻¹⟩, fun p q => unit_ext fun y hy => ?_⟩
  have v : ∀ p : M.ι × M'.ι, y ∈ M.U p.1 ⊓ M'.U p.2 → gm (𝟙 Y) y (M.U p.1 ⊓ M'.U p.2)
      (res (inf_le_left : M.U p.1 ⊓ M'.U p.2 ≤ _) (t.s p.1) *
        (res (inf_le_right : M.U p.1 ⊓ M'.U p.2 ≤ _) (t'.s p.2))⁻¹) =
      gm (𝟙 Y) y _ (t.s p.1) * (gm (𝟙 Y) y _ (t'.s p.2))⁻¹ := fun p hp =>
    (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ y _ hp _)
      ((map_inv _ _).trans (congrArg (·⁻¹) (gm_res _ y _ hp _))))
  have tr : ∀ {A : LB Y} {a : LB.Gen A}, a.IsGen → ∀ i j, y ∈ A.U i ⊓ A.U j →
      gm (𝟙 Y) y _ (a.s i) = gm (𝟙 Y) y _ (A.g i j) * gm (𝟙 Y) y _ (a.s j) := fun ha i j hm =>
    (gm_res _ y _ hm _).symm.trans ((congrArg (gm (𝟙 Y) y _) (ha i j)).trans
      ((map_mul _ _ _).trans (congrArg _ (gm_res _ y _ hm _))))
  refine ((gm_res _ y _ hy _).trans (v p hy.1)).trans (Eq.trans ?_ ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (gm_div M' M (𝟙 Y) y p q hy) ((gm_res _ y _ hy _).trans (v q hy.2)))).symm)
  rw [tr ht p.1 q.1 ⟨hy.1.1, hy.2.1⟩, tr ht' p.2 q.2 ⟨hy.1.2, hy.2.2⟩, mul_inv, _root_.mul_mul_mul_comm]

theorem hasGen_div_iff (hN : N.IsLB) (hN' : N'.IsLB) (h' : HasGen N' φ ε) :
    HasGen (LB.div N N') φ ε ↔ HasGen N φ ε := by
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨u', hu'⟩ := h'
    obtain ⟨u, hu, -⟩ := DescendedPrincipal.exists_gen_mul_div hN hN' u' hu' q hq
    exact ⟨u, hu⟩
  · intro h
    obtain ⟨w, hw⟩ := gen_div_of_gen h h'
    exact gen_chartPull (DescendedPrincipal.chartPullDiv N N' φ ε) w hw

theorem locGen_div_iff (hN : N.IsLB) (hN' : N'.IsLB) {π : Y ⟶ B} (h' : LocGen N' π φ ε) :
    LocGen (LB.div N N') π φ ε ↔ LocGen N π φ ε := by
  have shrink : ∀ {A : LB X} {V W : B.Opens}, W ≤ V → HasGen A (fun k => (π ⁻¹ᵁ V).ι ≫ φ k) ε →
      HasGen A (fun k => (π ⁻¹ᵁ W).ι ≫ φ k) ε := fun {A V W} hle t =>
    t.pull (Y.homOfLE (show π ⁻¹ᵁ W ≤ π ⁻¹ᵁ V from fun _ h => hle h))
      (fun k => by rw [← Category.assoc, Scheme.homOfLE_ι])
  constructor <;> intro H p <;> obtain ⟨V, hV, t⟩ := H p <;> obtain ⟨V', hV', t'⟩ := h' p
  · exact ⟨V ⊓ V', ⟨hV, hV'⟩, (hasGen_div_iff hN hN' (shrink inf_le_right t')).1 (shrink inf_le_left t)⟩
  · exact ⟨V ⊓ V', ⟨hV, hV'⟩, (hasGen_div_iff hN hN' (shrink inf_le_right t')).2 (shrink inf_le_left t)⟩

end General

variable {S : Scheme.{0}} {B : Over S} [GrpObj B] {T : Over S}

theorem inK_div_iff {L O : LB B.left} (hL : L.IsLB) (hO : O.IsLB) {x : T ⟶ B} (hx : InK B O x) :
    InK B (LB.div L O) x ↔ InK B L x :=
  (inK_iff_locGen x).trans ((locGen_div_iff hL hO ((inK_iff_locGen x).1 hx)).trans (inK_iff_locGen x).symm)

theorem inK_of_lam [IsCommMonObj B] {O : LB B.left} (hO : O.IsLB) (hu : ∃ u : LB.Gen (abelian₂ B O), u.IsGen)
    (x : T ⟶ B) : InK B O x := by
  have H₀ : HasGen O (PrimCocycle.lamφ B) PrimCocycle.lamε := hu
  have H₁ : LocGen O (fst T B).left
      (fun I => (lift (fst T B ≫ x) (snd T B)).left ≫ PrimCocycle.lamφ B I) PrimCocycle.lamε := fun _ =>
    ⟨⊤, trivial, H₀.pull (((fst T B).left ⁻¹ᵁ ⊤).ι ≫ (lift (fst T B ≫ x) (snd T B)).left)
      fun _ => Category.assoc _ _ _⟩
  have H₂ := BoxKernel.locGen_base hO (fst T B).left (K := Fin 2) ![x.left, (1 : T ⟶ B).left] ![-1, 1]
  refine (inK_iff_locGen x).2 (H₁.comb hO H₂ fun U _ h => ?_)
  rw [PrimCocycle.prod_lam (fst T B ≫ x) (snd T B) h, Fin.prod_univ_two, Fin.prod_univ_two]
  have e₁ : (fst T B).left ≫ (1 : T ⟶ B).left = (1 : T ⊗ B ⟶ B).left :=
    congrArg (fun q : T ⊗ B ⟶ B => q.left) (MonObj.comp_one (fst T B))
  show h (translPt B x).left * (h ((fst T B).left ≫ x.left))⁻¹ * (h (snd T B).left)⁻¹ * h (1 : T ⊗ B ⟶ B).left *
      (h ((fst T B).left ≫ x.left) ^ (-1 : ℤ) * h ((fst T B).left ≫ (1 : T ⟶ B).left) ^ (1 : ℤ))⁻¹ =
    h (translPt B x).left ^ (1 : ℤ) * h (snd T B).left ^ (-1 : ℤ)
  rw [e₁]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  module

end GlobalTheory.UU.KTwist

namespace GlobalTheory.UU

end GlobalTheory.UU

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfQuasiAffine
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.AmpleStabFinite
open GlobalTheory.CechPic

theorem eq_pull_of_local {Y S : Scheme.{0}} (p : Y ⟶ S) (e : S ⟶ Y) (he : e ≫ p = 𝟙 S)
    (hp : ∀ V : S.Opens, Function.Surjective (pullback.snd p V.ι).appTop.hom) (c : CechPic.Pic Y)
    (h : ∀ s : S, ∃ U : S.Opens, s ∈ U ∧ CechPic.pull (p ⁻¹ᵁ U).ι c = 0) : c = CechPic.pull (p ≫ e) c := by
  obtain ⟨M, hM, rfl⟩ := cls_surj c
  have key := exists_gen_of_local_on_base hM (K := Fin 2) ![𝟙 Y, p ≫ e] ![1, -1] p e he hp
    (fun U _ k => by
      rw [Fin.prod_univ_two]
      show k (e ≫ 𝟙 Y) ^ (1 : ℤ) * k (e ≫ p ≫ e) ^ (-1 : ℤ) = 1
      rw [← Category.assoc e, he, Category.comp_id, Category.id_comp]; simp)
    (fun s => by
      obtain ⟨U, hs, hU⟩ := h s
      refine ⟨U, hs, (cls_eq_zero_iff (LB.isLB_linComb hM _ _)).1 ?_⟩
      obtain ⟨n, n₁⟩ : ∃ n : (p ⁻¹ᵁ U).toScheme ⟶ (p ⁻¹ᵁ U).toScheme,
          n ≫ (p ⁻¹ᵁ U).ι = (p ⁻¹ᵁ U).ι ≫ p ≫ e :=
        ⟨IsOpenImmersion.lift (p ⁻¹ᵁ U).ι ((p ⁻¹ᵁ U).ι ≫ p ≫ e) (by
          rintro _ ⟨y, rfl⟩
          rw [Scheme.Opens.range_ι]
          have e' := congrArg (fun q => q (p y.1)) he
          exact (congrArg (· ∈ U) e').mpr y.2), IsOpenImmersion.lift_fac _ _ _⟩
      rw [cls_linComb hM, Fin.sum_univ_two]
      show (1 : ℤ) • CechPic.pull ((p ⁻¹ᵁ U).ι ≫ 𝟙 Y) (cls M hM) +
        (-1 : ℤ) • CechPic.pull ((p ⁻¹ᵁ U).ι ≫ p ≫ e) (cls M hM) = 0
      rw [← n₁, Category.comp_id, pull_comp, hU, map_zero]; simp)
  have k2 := (cls_eq_zero_iff (LB.isLB_linComb hM _ _)).2 key
  rw [cls_linComb hM, Fin.sum_univ_two] at k2
  have k3 : (1 : ℤ) • CechPic.pull (𝟙 Y) (cls M hM) + (-1 : ℤ) • CechPic.pull (p ≫ e) (cls M hM) = 0 := k2
  rw [pull_id, one_zsmul, neg_one_zsmul, ← sub_eq_add_neg, sub_eq_zero] at k3
  exact k3

theorem surj_of_isPullback (hG : GlobalFnsSt) {S : Scheme.{0}} {B : Over S} [GrpObj B] (hB : IsAbelianScheme B)
    {Y T : Scheme.{0}} {a : Y ⟶ B.left} {q : Y ⟶ T} {b : T ⟶ S} (h : IsPullback a q B.hom b) :
    Function.Surjective q.appTop.hom := by
  rw [← h.isoPullback_hom_snd]
  exact surj_comp (ConcreteCategory.bijective_of_isIso (h.isoPullback.hom.app ⊤)).2 (surj_snd hG hB (Over.mk b))

theorem cls_pw {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (d : ℤ) : cls (pw L d) (isLB_pw hL d) = d • cls L hL := by
  have h := LB.isLB_linComb hL (fun _ : PUnit => 𝟙 X) (fun _ => d)
  have e := cls_linComb hL _ _ h
  rw [Fintype.sum_unique, pull_id] at e
  rw [← e]
  refine (cls_eq_iff _ h).2 (iso_of_chart h ⟨fun i _ => i, fun _ _ hy => Set.mem_iInter.2 fun _ => hy, ?_⟩)
  intro y i j hi hj
  refine Eq.trans (map_zpow _ _ _) (Eq.symm ((gm_linComb L (fun _ : PUnit => 𝟙 X) (fun _ => d) (𝟙 X) y (fun _ => i) (fun _ => j)
    (Set.mem_iInter.2 fun _ => hi) (Set.mem_iInter.2 fun _ => hj)).trans ?_))
  rw [Fintype.prod_unique, Category.id_comp]
  rfl

theorem pull_spec_local {K : Type} [CommRing K] [IsLocalRing K] {X : Scheme.{0}} (y : Spec (CommRingCat.of K) ⟶ X)
    (c : CechPic.Pic X) : CechPic.pull y c = 0 := by
  obtain ⟨M, hM, rfl⟩ := cls_surj c
  exact (cls_eq_zero_iff (pull_isLB hM y)).2 (DVR.exists_gen_of_local M hM _ _)

theorem isAffine_of_quasiAffine {X S : Scheme.{0}} [IsAffine S] [X.IsQuasiAffine] (f : X ⟶ S) [UniversallyClosed f] :
    IsAffine X := by
  have : UniversallyClosed (X.toSpecΓ ≫ Spec.map f.appTop) := by
    rw [← Scheme.toSpecΓ_naturality]; infer_instance
  have : UniversallyClosed X.toSpecΓ := .of_comp_of_isSeparated _ (Spec.map f.appTop)
  have : Surjective X.toSpecΓ := inferInstance
  exact ⟨isIso_of_isOpenImmersion_of_opensRange_eq_top _
    (top_unique fun x _ => X.toSpecΓ.surjective x)⟩

theorem quasiAffine_of_pull_add {X Y : Scheme.{0}} [CompactSpace X] (f g : X ⟶ Y) [IsAffineHom f] {M : LB Y}
    (hM : M.IsLB) {I : Type} (s : I → M.Sec) (hc : ⨆ i, nonzeroLocus (s i) = ⊤)
    (ha : ∀ i, IsAffineOpen (nonzeroLocus (s i)))
    (h : CechPic.pull f (cls M hM) + CechPic.pull g (cls M hM) = 0) : X.IsQuasiAffine := by
  refine Scheme.IsQuasiAffine.of_forall_exists_mem_basicOpen X fun x => ?_
  obtain ⟨a, hxa⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc.ge (Set.mem_univ (f x)))
  obtain ⟨b, hxb⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc.ge (Set.mem_univ (g x)))
  have hN := LB.isLB_linComb hM (Sum.elim (fun _ : PUnit => g) (fun _ : PUnit => f))
    (Sum.elim (fun _ => 1) (fun _ => 1))
  have h0 : cls _ hN = 0 := by
    rw [cls_linComb hM, Fintype.sum_sum_type]
    simpa [add_comm] using h
  obtain ⟨t, ht⟩ := exists_sec_nonzeroLocus_eq_of_lbIso (LB.isLB_triv X) hN
    ((cls_eq_iff _ _).1 h0.symm)
    (DVR.mulSec M _ _ _ _ (secPull (s b) g) (secPull (s a) f))
  rw [nonzeroLocus_mulSec, nonzeroLocus_secPull (s a)] at ht
  have e : nonzeroLocus t = X.basicOpen (show Γ(X, ⊤) from t.f PUnit.unit) :=
    le_antisymm (iSup_le fun _ => le_rfl) (basicOpen_le_nonzeroLocus t PUnit.unit)
  refine ⟨t.f PUnit.unit, ?_, ?_⟩
  · rw [← e, ht]
    exact isAffineOpen_nonzeroLocus_inf (pull_isLB hM g) _ ((ha a).preimage f)
  · rw [← e, ht, nonzeroLocus_secPull]
    exact ⟨hxb, hxa⟩

section Points

variable {S : Scheme.{0}} {B : Over S} [GrpObj B] {L O : LB B.left}

theorem transl_const (hG : GlobalFnsSt) (hB : IsAbelianScheme B) (hL : L.IsLB) (hO : O.IsLB) {T : Over S} (x : T ⟶ B)
    (h : ∀ p : T.left, ∃ U : T.left.Opens, p ∈ U ∧
      Triv ((LB.div (translDiff B L x) (O.pull (snd T B).left)).pull ((fst T B).left ⁻¹ᵁ U).ι)) (b : T ⟶ B) :
    CechPic.pull (x * b).left (cls L hL) - CechPic.pull b.left (cls L hL) - CechPic.pull b.left (cls O hO) =
      CechPic.pull x.left (cls L hL) - CechPic.pull (1 : T ⟶ B).left (cls L hL) -
        CechPic.pull (1 : T ⟶ B).left (cls O hO) := by
  have h₁ : (translDiff B L x).IsLB := LB.isLB_linComb hL _ _
  have h₂ := pull_isLB hO (snd T B).left
  have hM := LB.isLB_div h₁ h₂
  have val : ∀ b : T ⟶ B, CechPic.pull (lift (𝟙 T) b).left (cls _ hM) =
      CechPic.pull (x * b).left (cls L hL) - CechPic.pull b.left (cls L hL) - CechPic.pull b.left (cls O hO) := by
    intro b
    have e₁ : cls _ h₁ = CechPic.pull (lift (fst T B ≫ x) (snd T B) ≫ μ[B]).left (cls L hL) -
        CechPic.pull (snd T B).left (cls L hL) := by
      refine (cls_linComb hL _ _ h₁).trans ?_
      rw [Fin.sum_univ_two, sub_eq_add_neg]
      exact congrArg₂ (· + ·) (one_zsmul _) (neg_one_zsmul _)
    have a₁ : lift (𝟙 T) b ≫ (lift (fst T B ≫ x) (snd T B) ≫ μ[B]) = x * b := by
      rw [comp_lift_assoc, lift_fst_assoc, lift_snd, Category.id_comp]; rfl
    rw [cls_div h₁ h₂, e₁, cls_pull hO, map_sub, map_sub, ← pull_comp, ← pull_comp, ← pull_comp,
      ← Over.comp_left, ← Over.comp_left, a₁, lift_snd]
  have sec : ∀ b : T ⟶ B, (lift (𝟙 T) b).left ≫ (fst T B).left = 𝟙 _ := fun b => by
    rw [← Over.comp_left, lift_fst]; rfl
  have key := eq_pull_of_local (fst T B).left (lift (𝟙 T) (1 : T ⟶ B)).left (sec 1)
    (fun V => surj_of_isPullback hG hB
      ((IsPullback.of_hasPullback (fst T B).left V.ι).paste_horiz
        (IsPullback.of_hasPullback T.hom B.hom).flip)) (cls _ hM)
    (fun p => by
      obtain ⟨U, hU, ht⟩ := h p
      exact ⟨U, hU, (cls_eq_zero_iff (pull_isLB hM _)).2 ht⟩)
  have k := congrArg (CechPic.pull (lift (𝟙 T) b).left) key
  rw [← pull_comp, ← Category.assoc, sec, Category.id_comp, val, val, _root_.mul_one] at k
  exact k

theorem add_inv_eq [IsCommMonObj B] (hG : GlobalFnsSt) (hB : IsAbelianScheme B) (hL : L.IsLB) (hO : O.IsLB)
    {T : Over S} (x y : T ⟶ B)
    (hx : ∀ p : T.left, ∃ U : T.left.Opens, p ∈ U ∧
      Triv ((LB.div (translDiff B L x) (O.pull (snd T B).left)).pull ((fst T B).left ⁻¹ᵁ U).ι))
    (hy : ∀ p : T.left, ∃ U : T.left.Opens, p ∈ U ∧
      Triv ((LB.div (translDiff B L y) (O.pull (snd T B).left)).pull ((fst T B).left ⁻¹ᵁ U).ι)) :
    CechPic.pull x.left (cls L hL) + CechPic.pull (x⁻¹).left (cls L hL) =
      CechPic.pull y.left (cls L hL) + CechPic.pull (y⁻¹).left (cls L hL) := by
  have a := transl_const hG hB hL hO x hx (x⁻¹ * y⁻¹)
  have b := transl_const hG hB hL hO y hy (x⁻¹ * y⁻¹)
  rw [mul_inv_cancel_left] at a
  rw [mul_comm x⁻¹ y⁻¹, mul_inv_cancel_left, mul_comm y⁻¹ x⁻¹] at b
  linear_combination (norm := abel) b - a

end Points

theorem isFinite_of_relAmple : GlobalFnsSt → ∀ (R : Type) [CommRing R] (B : Over (Spec (CommRingCat.of R))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ L O : LB B.left, L.IsLB → O.IsLB → RelAmple B L → ∀ (H : Over (Spec (CommRingCat.of R))) (j : H ⟶ B), IsClosedImmersion j.left → (∀ (T : Over (Spec (CommRingCat.of R))) (x : T ⟶ B), (∀ p : (T).left, ∃ U : (T).left.Opens, p ∈ U ∧ Triv ((LB.div (translDiff B L x) (O.pull (snd (T) B).left)).pull ((fst (T) B).left ⁻¹ᵁ U).ι)) ↔ ∃ y : T ⟶ H, y ≫ j = x) → IsFinite H.hom := by
  intro hG R _ B _ _ hB L O hL hO hA H j hj hH
  obtain ⟨d, -, n, s, hc, ha⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy R B L hL).1 hA
  have := hB.proper
  have : IsProper H.hom := by rw [← Over.w j]; infer_instance
  suffices LocallyQuasiFinite H.hom from .of_isProper_of_locallyQuasiFinite _
  refine LocallyQuasiFinite.of_finite_preimage_singleton _ fun z => ?_
  rcases Set.eq_empty_or_nonempty (H.hom ⁻¹' {z}) with h0 | ⟨h, hh⟩
  · rw [h0]; exact Set.finite_empty
  let K : Type := H.left.residueField h
  let y₀ : Spec (CommRingCat.of K) ⟶ H.left := H.left.fromSpecResidueField h
  let P : Over (Spec (CommRingCat.of R)) := Over.mk (y₀ ≫ H.hom)
  let y : P ⟶ H := Over.homMk y₀ rfl
  let π : (H ⊗ P).left ⟶ H.left := (fst H P).left
  let q : (H ⊗ P).left ⟶ Spec (CommRingCat.of K) := (snd H P).left
  have hpb : IsPullback π q H.hom (y₀ ≫ H.hom) := IsPullback.of_hasPullback H.hom P.hom
  have : IsProper q := MorphismProperty.of_isPullback hpb inferInstance
  have : IsAffineHom π := MorphismProperty.of_isPullback hpb.flip inferInstance
  have key := add_inv_eq hG hB hL hO (fst H P ≫ j) (snd H P ≫ y ≫ j) ((hH _ _).2 ⟨_, rfl⟩)
    ((hH _ _).2 ⟨snd H P ≫ y, Category.assoc _ _ _⟩)
  rw [← GrpObj.comp_inv (snd H P), Over.comp_left _ _ _ (snd H P), Over.comp_left _ _ _ (snd H P), pull_comp (snd H P).left,
    pull_comp (snd H P).left, pull_spec_local (K := K) (y ≫ j).left, pull_spec_local (K := K) (y ≫ j)⁻¹.left,
    map_zero, add_zero] at key
  have : CompactSpace (H ⊗ P).left := QuasiCompact.compactSpace_of_compactSpace q
  have : IsAffineHom (fst H P ≫ j).left := inferInstanceAs (IsAffineHom (π ≫ j.left))
  have : (H ⊗ P).left.IsQuasiAffine := quasiAffine_of_pull_add (fst H P ≫ j).left ((fst H P ≫ j)⁻¹).left
    (isLB_pw hL d) s hc (fun i => (ha i).1) (by
      rw [cls_pw hL, map_zsmul, map_zsmul, ← zsmul_add, key, zsmul_zero])
  have : IsAffine (H ⊗ P).left := isAffine_of_quasiAffine q
  have : IsFinite q := IsFinite.iff_isProper_and_isAffineHom.2 ⟨inferInstance, inferInstance⟩
  have hfin : (Set.univ : Set (H ⊗ P).left).Finite := by
    have := q.finite_preimage_singleton (IsLocalRing.closedPoint K)
    refine this.subset fun t _ => Subsingleton.elim _ _
  refine (hfin.image π).subset fun w hw => ?_
  have e : H.hom w = (y₀ ≫ H.hom) (IsLocalRing.closedPoint K) := by
    have e₀ : y₀ (IsLocalRing.closedPoint K) = h := Scheme.fromSpecResidueField_apply h _
    exact (show H.hom w = z from hw).trans ((show H.hom h = z from hh).symm.trans (congrArg H.hom e₀).symm)
  obtain ⟨t, ht, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := H.hom) (g := y₀ ≫ H.hom) w _ e
  exact ⟨t, trivial, ht⟩

end GlobalTheory.AmpleStabFinite
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsHomogeneousXPowMulAddXPowMul
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ProjQuot

open MvPolynomial GlobalTheory.ProjSpace GlobalTheory.ThickeningDetermines

attribute [local instance] MvPolynomial.gradedAlgebra

section Algebra

variable {R A σ : Type} [CommRing R] [CommRing A] [Algebra R A] {r : σ → A} {i : σ}

theorem aeval_X_pow_mul (hi : r i = 1) (k : ℕ) (F : MvPolynomial σ R) :
    aeval r (X i ^ k * F) = aeval r F := by
  rw [map_mul, map_pow, aeval_X, hi, one_pow, _root_.one_mul]

theorem isHomogeneous_X_pow_mul_add_X_pow_mul (i : σ) {n m : ℕ} {F G : MvPolynomial σ R} (hF : F.IsHomogeneous n)
    (hG : G.IsHomogeneous m) : (X i ^ m * F + X i ^ n * G).IsHomogeneous (m + n) := by
  have h₁ : (X i ^ m * F).IsHomogeneous (m + n) := (isHomogeneous_X_pow i m).mul hF
  have h₂ : (X i ^ n * G).IsHomogeneous (m + n) := by
    simpa only [Nat.add_comm n m] using (isHomogeneous_X_pow i n).mul hG
  exact h₁.add h₂

theorem exists_isHomogeneous_aeval_eq (hi : r i = 1) (p : MvPolynomial σ R) :
    ∃ (n : ℕ) (G : MvPolynomial σ R), G.IsHomogeneous n ∧ aeval r G = aeval r p := by
  induction p using MvPolynomial.induction_on with
  | C a => exact ⟨0, C a, isHomogeneous_C _ a, rfl⟩
  | add p q hp hq =>
    obtain ⟨a, F, hF, eF⟩ := hp
    obtain ⟨b, G, hG, eG⟩ := hq
    refine ⟨b + a, X i ^ b * F + X i ^ a * G, isHomogeneous_X_pow_mul_add_X_pow_mul i hF hG, ?_⟩
    rw [map_add, aeval_X_pow_mul hi, aeval_X_pow_mul hi, eF, eG, map_add]
  | mul_X p j hp =>
    obtain ⟨a, F, hF, eF⟩ := hp
    exact ⟨a + 1, F * X j, hF.mul (isHomogeneous_X R j), by rw [map_mul, map_mul, eF]⟩

def valueIdeal (hi : r i = 1) (hr : Function.Surjective (aeval (R := R) r))
    (J : Ideal (MvPolynomial σ R)) : Ideal A where
  carrier := {a | ∃ (n : ℕ) (G : MvPolynomial σ R), G.IsHomogeneous n ∧ G ∈ J ∧ aeval r G = a}
  zero_mem' := ⟨0, 0, isHomogeneous_zero _ R 0, J.zero_mem, map_zero _⟩
  add_mem' := by
    rintro _ _ ⟨n, F, hF, jF, rfl⟩ ⟨m, G, hG, jG, rfl⟩
    refine ⟨_, _, isHomogeneous_X_pow_mul_add_X_pow_mul i hF hG,
      J.add_mem (J.mul_mem_left _ jF) (J.mul_mem_left _ jG), ?_⟩
    rw [map_add, aeval_X_pow_mul hi, aeval_X_pow_mul hi]
  smul_mem' := by
    rintro c _ ⟨m, G, hG, jG, rfl⟩
    obtain ⟨p, rfl⟩ := hr c
    obtain ⟨n, F, hF, eF⟩ := exists_isHomogeneous_aeval_eq hi p
    exact ⟨_, _, hF.mul hG, J.mul_mem_left _ jG, by rw [map_mul, eF, smul_eq_mul]⟩

end Algebra

variable {R : Type} [CommRing R] {n : ℕ}

def formIdeal (J : Ideal (MvPolynomial (Fin (n + 1)) R)) : (PSpace R n).IdealSheafData :=
  ⨆ p : {p : ℕ × MvPolynomial (Fin (n + 1)) R // p.2.IsHomogeneous p.1 ∧ p.2 ∈ J},
    secIdeal (On_isLB R n p.1.1) (formSec p.1.1 p.1.2 p.2.1)

theorem ideal_secIdeal_formSec (i : Fin (n + 1)) (d : ℕ) (G : MvPolynomial (Fin (n + 1)) R)
    (hG : G.IsHomogeneous d) :
    (secIdeal (On_isLB R n d) (formSec d G hG)).ideal ⟨chart R n i, isAffineOpen_chart R n i⟩ =
      Ideal.span {aeval (ratio R n i) G} := by
  have hle : chart R n i ≤ (On R n (d : ℤ)).U (fun _ => i) := (On_U R n d (fun _ => i)).ge
  rw [GlobalTheory.ThickeningDetermines.secIdeal]
  refine (GlobalTheory.EffCartierData.ideal_locIdeal _ _ _ _ _ (fun _ => i) hle).trans ?_
  rw [formSec_f, resG_formOn, formOn_eq_aeval]

private theorem mem_valueIdeal_of_eq_one {S A σ : Type} [CommRing S] [CommRing A] [Algebra S A] {r : σ → A}
    {i : σ} (hi : r i = 1) (hr : Function.Surjective (aeval (R := S) r)) (J : Ideal (MvPolynomial σ S))
    (a : A) : a ∈ valueIdeal hi hr J ↔
      ∃ (m : ℕ) (G : MvPolynomial σ S), G.IsHomogeneous m ∧ G ∈ J ∧ aeval r G = a :=
  Iff.rfl

theorem aeval_mem_formIdeal_iff (J : Ideal (MvPolynomial (Fin (n + 1)) R)) (i : Fin (n + 1))
    {t : ℕ} {F : MvPolynomial (Fin (n + 1)) R} (hF : F.IsHomogeneous t) :
    aeval (ratio R n i) F ∈ (formIdeal J).ideal ⟨chart R n i, isAffineOpen_chart R n i⟩ ↔
      ∃ k : ℕ, X i ^ k * F ∈ J := by
  have hone : ratio R n i i = 1 := ratioOn_self
  have hsurj := aeval_ratio_surjective R n i
  have key : (formIdeal J).ideal ⟨chart R n i, isAffineOpen_chart R n i⟩ = valueIdeal hone hsurj J := by
    rw [formIdeal, Scheme.IdealSheafData.ideal_iSup, iSup_apply]
    simp only [ideal_secIdeal_formSec]
    apply le_antisymm
    · refine iSup_le fun p => ?_
      rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, mem_valueIdeal_of_eq_one]
      exact ⟨p.1.1, p.1.2, p.2.1, p.2.2, rfl⟩
    · intro a ha
      obtain ⟨m, G, hG, jG, rfl⟩ := (mem_valueIdeal_of_eq_one hone hsurj J a).1 ha
      refine Ideal.mem_iSup_of_mem
        (⟨(m, G), hG, jG⟩ : {p : ℕ × MvPolynomial (Fin (n + 1)) R // p.2.IsHomogeneous p.1 ∧ p.2 ∈ J}) ?_
      exact Ideal.subset_span (Set.mem_singleton _)
  rw [key, mem_valueIdeal_of_eq_one]
  constructor
  · rintro ⟨m, G, hG, jG, e⟩
    refine ⟨m, ?_⟩
    have h₁ : (X i ^ m * F).IsHomogeneous (m + t) := (isHomogeneous_X_pow i m).mul hF
    have h₂ : (X i ^ t * G).IsHomogeneous (m + t) := by
      simpa only [Nat.add_comm t m] using (isHomogeneous_X_pow i t).mul hG
    have hEq : X i ^ m * F = X i ^ t * G := by
      rw [← formOn_chart_inj R n i h₁ h₂, formOn_eq_aeval, formOn_eq_aeval]
      change aeval (ratio R n i) (X i ^ m * F) = aeval (ratio R n i) (X i ^ t * G)
      rw [aeval_X_pow_mul hone, aeval_X_pow_mul hone, e]
    rw [hEq]
    exact J.mul_mem_left _ jG
  · rintro ⟨k, hk⟩
    exact ⟨k + t, X i ^ k * F, (isHomogeneous_X_pow i k).mul hF, hk, aeval_X_pow_mul hone k F⟩

private theorem resG_refl' {Y : Scheme.{0}} {U : Y.Opens} (h : U ≤ U) (a : Γ(Y, U)) :
    resG Y h a = a := by
  have e : homOfLE h = 𝟙 U := Subsingleton.elim _ _
  rw [resG, e, op_id, CategoryTheory.Functor.map_id, CommRingCat.hom_id, RingHom.id_apply]

private theorem appLE_congr_of_eq' {Y Z : Scheme.{0}} (φ : Y ⟶ Z) {U : Z.Opens} {V : Y.Opens} (e : V ≤ φ ⁻¹ᵁ U)
    (a : Γ(Z, U)) : (φ.appLE U V e).hom a = resG Y e ((φ.app U).hom a) := by
  rw [Scheme.Hom.appLE, CommRingCat.comp_apply]

private theorem cst_comp_eq_resG_app {Y Z : Scheme.{0}} {S : Type} [CommRing S] (φ : Y ⟶ Z)
    (g : Z ⟶ Spec (CommRingCat.of S)) (U : Z.Opens) (V : Y.Opens) (e : V ≤ φ ⁻¹ᵁ U)
    (h : U ≤ g ⁻¹ᵁ ⊤) (a : S) :
    GlobalTheory.AbLaw.cst (φ ≫ g) V a = resG Y e ((φ.app U).hom ((g.appLE ⊤ U h).hom
      ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom a))) := by
  rw [← appLE_congr_of_eq', ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, appLE_congr_of_eq']
  rfl

theorem eval₂Hom_secPull_coord {Y : Scheme.{0}} (φ : Y ⟶ PSpace R n) (k : PUnit → Fin (n + 1))
    (F : MvPolynomial (Fin (n + 1)) R) :
    eval₂Hom (cst (φ ≫ PSpace.str R n) (((O1 R n).pull φ).U k))
        (fun j => (Cartier.secPull (coord R n j) φ).f k) F =
      resG Y (Cartier.pull_U (O1 R n) φ k).le
        ((φ.app (chart R n (k ⟨⟩))).hom (aeval (ratio R n (k ⟨⟩)) F)) := by
  have hle := (Cartier.pull_U (O1 R n) φ k).le
  have key : (eval₂Hom (cst (φ ≫ PSpace.str R n) (((O1 R n).pull φ).U k))
      fun j => (Cartier.secPull (coord R n j) φ).f k) =
      (resG Y hle).comp ((φ.app (chart R n (k ⟨⟩))).hom.comp (aeval (ratio R n (k ⟨⟩))).toRingHom) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun j => ?_)
    · show _ = resG Y hle ((φ.app (chart R n (k ⟨⟩))).hom (aeval (ratio R n (k ⟨⟩)) (C a)))
      rw [eval₂Hom_C, aeval_C, algebraMap_sections_eq, CommRingCat.comp_apply]
      exact cst_comp_eq_resG_app φ (PSpace.str R n) _ _ hle le_top a
    · show _ = resG Y hle ((φ.app (chart R n (k ⟨⟩))).hom (aeval (ratio R n (k ⟨⟩)) (X j)))
      rw [eval₂Hom_X', aeval_X, ← resG_refl' (le_refl (((O1 R n).pull φ).U k)) ((Cartier.secPull (coord R n j) φ).f k),
        resG_secPull_coord φ j k (le_refl _), pullRatio, appLE_congr_of_eq']
      rfl
  exact RingHom.congr_fun key F

private theorem eq_zero_of_resG_eq_zero_of_eq {Y : Scheme.{0}} {U V : Y.Opens} (hUV : V = U) {h : V ≤ U}
    {a : Γ(Y, U)} (ha : resG Y h a = 0) : a = 0 := by
  subst hUV
  have e : homOfLE h = 𝟙 V := Subsingleton.elim _ _
  rwa [resG, e, op_id, CategoryTheory.Functor.map_id, CommRingCat.hom_id, RingHom.id_apply] at ha

theorem exists_veryAmpleBy_of_ideal : ∀ (R : Type) [CommRing R] (n : ℕ) (J : Ideal (MvPolynomial (Fin (n + 1)) R)), (∀ F ∈ J, ∀ t, MvPolynomial.homogeneousComponent t F ∈ J) → ∃ (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (H : LB X) (s : Fin (n + 1) → LB.Sec H), H.IsLB ∧ VeryAmpleBy f H s ∧ ∀ (t : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous t → ((∀ k : (H).ι, MvPolynomial.eval₂Hom (cst (f) ((H).U k)) (fun j => (s j).f k) (F) = 0) ↔ ∀ i, ∃ k : ℕ, MvPolynomial.X i ^ k * F ∈ J) := by
  intro R _ n J _
  refine ⟨(formIdeal J).subscheme, (formIdeal J).subschemeι ≫ PSpace.str R n,
    (O1 R n).pull (formIdeal J).subschemeι,
    fun j => Cartier.secPull (coord R n j) (formIdeal J).subschemeι,
    pull_isLB (O1_isLB R n) _, veryAmpleBy_secPull_coord _, fun t F hF => ?_⟩
  constructor
  · intro h i
    rw [← aeval_mem_formIdeal_iff J i hF, ← Scheme.IdealSheafData.ker_subschemeι_app, RingHom.mem_ker]
    exact eq_zero_of_resG_eq_zero_of_eq (Cartier.pull_U (O1 R n) _ (fun _ => i))
      ((eval₂Hom_secPull_coord _ (fun _ => i) F).symm.trans (h (fun _ => i)))
  · intro h k
    obtain ⟨m, hm⟩ := h (k ⟨⟩)
    have hz := (aeval_mem_formIdeal_iff J (k ⟨⟩) hF).2 ⟨m, hm⟩
    rw [← Scheme.IdealSheafData.ker_subschemeι_app, RingHom.mem_ker] at hz
    exact ((eval₂Hom_secPull_coord _ k F).trans (congrArg _ hz)).trans (map_zero _)

end GlobalTheory.ProjQuot
end
end

