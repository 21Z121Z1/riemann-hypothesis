import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBoxGenOfSection
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2274
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2291
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2367
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3087
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2280
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0067
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0083
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0113
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3090
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3059
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2801
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2925
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0018
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0567
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionValueAtTorsionPointEqSumTerms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3060
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3089
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3075
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3078
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2180
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2174
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2179
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2290
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2299
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2292
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2262
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2289
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2278
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2670
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0587
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2416
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2786
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3046
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2878
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2859

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigAlongBox
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

noncomputable section

namespace GlobalTheory.ProdUnif

open GlobalTheory.UnifPullRig

theorem rigAlong_box : ∀ {B B₁ B₂ G G₁ G₂ T T₁ T₂ : Scheme.{0}} {M : LB B} {M₁ : LB B₁} {M₂ : LB B₂} {L : LB G} {L₁ : LB G₁} {L₂ : LB G₂} {b₁ : B ⟶ B₁} {b₂ : B ⟶ B₂} {g₁ : G ⟶ G₁} {g₂ : G ⟶ G₂} {p : T ⟶ B} {f : T ⟶ G} {p₁ : T₁ ⟶ B₁} {f₁ : T₁ ⟶ G₁} {p₂ : T₂ ⟶ B₂} {f₂ : T₂ ⟶ G₂} {h₁ : T ⟶ T₁} {h₂ : T ⟶ T₂} (wM : LB.Iso M (extLB M₁ M₂ b₁ b₂)) (wL : LB.Iso L (extLB L₁ L₂ g₁ g₂)) (we₁ : LB.Iso (L₁.pull f₁) (M₁.pull p₁)) (we₂ : LB.Iso (L₂.pull f₂) (M₂.pull p₂)), M.IsLB → M₁.IsLB → M₂.IsLB → L.IsLB → L₁.IsLB → L₂.IsLB → p ≫ b₁ = h₁ ≫ p₁ → p ≫ b₂ = h₂ ≫ p₂ → f ≫ g₁ = h₁ ≫ f₁ → f ≫ g₂ = h₂ ≫ f₂ → ∀ (we : LB.Iso (L.pull f) (M.pull p)), BoxSq wM wL we we₁ we₂ h₁ h₂ → ∀ {S S₀ : Scheme.{0}} (u : S ⟶ T) (u₁ : S ⟶ T₁) (u₂ : S ⟶ T₂) (s : S ⟶ S₀) {eG : S₀ ⟶ G} {eG₁ : S₀ ⟶ G₁} {eG₂ : S₀ ⟶ G₂} {eB : S₀ ⟶ B} {eB₁ : S₀ ⟶ B₁} {eB₂ : S₀ ⟶ B₂} (rL : LB.Gen (L.pull eG)) (rL₁ : LB.Gen (L₁.pull eG₁)) (rL₂ : LB.Gen (L₂.pull eG₂)) (rM : LB.Gen (M.pull eB)) (rM₁ : LB.Gen (M₁.pull eB₁)) (rM₂ : LB.Gen (M₂.pull eB₂)), u ≫ h₁ = u₁ → u ≫ h₂ = u₂ → u ≫ f = s ≫ eG → u ≫ p = s ≫ eB → u₁ ≫ f₁ = s ≫ eG₁ → u₁ ≫ p₁ = s ≫ eB₁ → u₂ ≫ f₂ = s ≫ eG₂ → u₂ ≫ p₂ = s ≫ eB₂ → IsBoxGen wL (𝟙 S₀) (𝟙 S₀) rL rL₁ rL₂ → IsBoxGen wM (𝟙 S₀) (𝟙 S₀) rM rM₁ rM₂ → GlobalTheory.UnifPullRig.RigAlong we₁ u₁ s rL₁ rM₁ → GlobalTheory.UnifPullRig.RigAlong we₂ u₂ s rL₂ rM₂ → GlobalTheory.UnifPullRig.RigAlong we u s rL rM := by
  intro B B₁ B₂ G G₁ G₂ T T₁ T₂ M M₁ M₂ L L₁ L₂ b₁ b₂ g₁ g₂ p f p₁ f₁ p₂ f₂ h₁ h₂ wM wL we₁ we₂ hM hM₁ hM₂
    hL hL₁ hL₂ hpb₁ hpb₂ hfg₁ hfg₂ we hQ S S₀ u u₁ u₂ s eG eG₁ eG₂ eB eB₁ eB₂ rL rL₁ rL₂ rM rM₁ rM₂ hu₁ hu₂
    hf hp hf₁ hp₁ hf₂ hp₂ bL bM H₁ H₂
  rintro ⟨qM, qL⟩ V a₁ a₂ a₃
  refine unit_ext fun y hy => ?_
  obtain ⟨J, hJ, eJ⟩ := exists_good M hM y (K := PUnit) (fun _ => s ≫ eB) (fun _ => qM ⟨⟩)
    (fun _ _ _ => rfl) (fun _ => (mem_pull (F := eB) (x := s y)).1 (a₃ hy))
  obtain ⟨N, hN, eN⟩ := exists_good L hL y (K := PUnit) (fun _ => s ≫ eG) (fun _ => qL ⟨⟩)
    (fun _ _ _ => rfl) (fun _ => (mem_pull (F := eG) (x := s y)).1 (a₂ hy))
  obtain ⟨J₁, hJ₁⟩ := BoxFamily.exists_good_at hM₁ y
  obtain ⟨J₂, hJ₂⟩ := BoxFamily.exists_good_at hM₂ y
  obtain ⟨N₁, hN₁⟩ := BoxFamily.exists_good_at hL₁ y
  obtain ⟨N₂, hN₂⟩ := BoxFamily.exists_good_at hL₂ y
  have m₁ : (u ≫ p) ≫ b₁ = s ≫ eB₁ := by rw [Category.assoc, hpb₁, ← Category.assoc, hu₁, hp₁]
  have m₂ : (u ≫ p) ≫ b₂ = s ≫ eB₂ := by rw [Category.assoc, hpb₂, ← Category.assoc, hu₂, hp₂]
  have n₁ : (u ≫ f) ≫ g₁ = s ≫ eG₁ := by rw [Category.assoc, hfg₁, ← Category.assoc, hu₁, hf₁]
  have n₂ : (u ≫ f) ≫ g₂ = s ≫ eG₂ := by rw [Category.assoc, hfg₂, ← Category.assoc, hu₂, hf₂]
  have Q := hQ S u y J₁ J₂ J N₁ N₂ N hJ₁ hJ₂ hJ hN₁ hN₂ hN
  rw [m₁, m₂, n₁, n₂, hu₁, hu₂, hp, hf] at Q
  have HM := bM S s y J₁ J₂ J hJ₁ hJ₂ hJ
  have HL := bL S s y N₁ N₂ N hN₁ hN₂ hN
  simp only [Category.comp_id] at HM HL
  have E₁ := H₁.stalk hf₁ hp₁ (𝟙 S) y (J₁ (s ≫ eB₁)) (N₁ (s ≫ eG₁))
    ((pt_of_eq hp₁ y).symm ▸ hJ₁ (s ≫ eB₁)) ((pt_of_eq hf₁ y).symm ▸ hN₁ (s ≫ eG₁))
  have E₂ := H₂.stalk hf₂ hp₂ (𝟙 S) y (J₂ (s ≫ eB₂)) (N₂ (s ≫ eG₂))
    ((pt_of_eq hp₂ y).symm ▸ hJ₂ (s ≫ eB₂)) ((pt_of_eq hf₂ y).symm ▸ hN₂ (s ≫ eG₂))
  simp only [Category.id_comp] at E₁ E₂
  have key := rel_alg (K := PUnit) (fun _ => 1) (fun _ => om wM y J₁ J₂ J (s ≫ eB))
    (fun _ => om wL y N₁ N₂ N (s ≫ eG)) (fun _ => gw we u y (J (s ≫ eB)) (fun _ => N (s ≫ eG)))
    (fun _ => gw we₁ u₁ y (J₁ (s ≫ eB₁)) (fun _ => N₁ (s ≫ eG₁)))
    (fun _ => gw we₂ u₂ y (J₂ (s ≫ eB₂)) (fun _ => N₂ (s ≫ eG₂))) (fun _ => Q) HM HL
    (by rw [Fintype.prod_unique, zpow_one]; exact E₁.symm) (by rw [Fintype.prod_unique, zpow_one]; exact E₂.symm)
  rw [Fintype.prod_unique, zpow_one, val_of rM s y J qM (fun k => eJ k), val_of rL s y N qL (fun k => eN k),
    eJ ⟨⟩, eN ⟨⟩] at key
  refine (map_mul _ _ _).trans ((congrArg₂ (· * ·) (gm_res_pull _ u y a₁ hy _)
    (gm_res_pull _ s y a₂ hy _)).trans (Eq.trans ?_ (gm_res_pull _ s y a₃ hy _).symm))
  simp only [Category.id_comp]
  exact key.symm

end GlobalTheory.ProdUnif
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiConditionDescendsGaloisCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.RosatiDescent

open GlobalTheory.CechPic

theorem lift_left_fst {S : Scheme.{0}} {A T : Over S} (f g : T ⟶ A) :
    (lift f g).left ≫ (fst A A).left = f.left :=
  congrArg (fun q => q.left) (lift_fst f g)

theorem lift_left_snd {S : Scheme.{0}} {A T : Over S} (f g : T ⟶ A) :
    (lift f g).left ≫ (snd A A).left = g.left :=
  congrArg (fun q => q.left) (lift_snd f g)

theorem eSec_comp_of_isMonHom {S : Scheme.{0}} {A : Over S} [GrpObj A] (u : A ⟶ A) [IsMonHom u] :
    eSec A ≫ u.left = eSec A := by
  show (η[A] ≫ u).left = η[A].left
  rw [IsMonHom.one_hom]

theorem lbIso_act_descent : ∀ (O : Type) [Ring O] (star : O → O) (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (φ₂ : (G2 A).left ⟶ (G2 A₀).left) (P : LB (G2 A).left) (P₀ : LB (G2 A₀).left) (act : OActN O A) (act₀ : OActN O A₀), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → (∃ t : (P₀.pull (eSec (G2 A₀))).Gen, t.IsGen) → (∀ c, (act.act c).left ≫ φ = φ ≫ (act₀.act c).left) → (∀ c, LBIso (P.pull (lift (fst A A ≫ act.act c) (snd A A)).left) (P.pull (lift (fst A A) (snd A A ≫ act.act (star c))).left)) → ∀ c, LBIso (P₀.pull (lift (fst A₀ A₀ ≫ act₀.act c) (snd A₀ A₀)).left) (P₀.pull (lift (fst A₀ A₀) (snd A₀ A₀ ≫ act₀.act (star c))).left) := by
  intro O _ star X Y π Ga _ ρ A _ _ A₀ _ _ φ φ₂ P P₀ act act₀ hG hA hA₀ gp hsq hP hP₀ iP _ hact hros c
  have := hG.fin
  have := hG.etale
  have := hG.onto
  have hB : IsAbelianScheme (G2 A₀) := AbelianSchemeGerms.isAbelianScheme_tensor _ _ hA₀ hA₀
  have h₁ := pull_isLB hP₀ (lift (fst A₀ A₀ ≫ act₀.act c) (snd A₀ A₀)).left
  have h₂ := pull_isLB hP₀ (lift (fst A₀ A₀) (snd A₀ A₀ ≫ act₀.act (star c))).left
  have hN := LB.isLB_div h₂ h₁
  have cN := cls_div h₂ h₁ hN
  rw [cls_pull hP₀, cls_pull hP₀] at cN
  have m₀ := act₀.hom c
  have m₀' := act₀.hom (star c)
  have c₁ : φ₂ ≫ (lift (fst A₀ A₀ ≫ act₀.act c) (snd A₀ A₀)).left =
      (lift (fst A A ≫ act.act c) (snd A A)).left ≫ φ₂ := by
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst A₀ A₀).left = (_ ≫ _) ≫ (fst A₀ A₀).left
      rw [Category.assoc, lift_left_fst, Category.assoc, hsq.1, ← Category.assoc, lift_left_fst]
      show φ₂ ≫ (fst A₀ A₀).left ≫ (act₀.act c).left = (fst A A).left ≫ (act.act c).left ≫ φ
      rw [reassoc_of% hsq.1, hact]
    · show (_ ≫ _) ≫ (snd A₀ A₀).left = (_ ≫ _) ≫ (snd A₀ A₀).left
      rw [Category.assoc, lift_left_snd, Category.assoc, hsq.2, ← Category.assoc, lift_left_snd]
  have c₂ : φ₂ ≫ (lift (fst A₀ A₀) (snd A₀ A₀ ≫ act₀.act (star c))).left =
      (lift (fst A A) (snd A A ≫ act.act (star c))).left ≫ φ₂ := by
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst A₀ A₀).left = (_ ≫ _) ≫ (fst A₀ A₀).left
      rw [Category.assoc, lift_left_fst, Category.assoc, hsq.1, ← Category.assoc, lift_left_fst]
    · show (_ ≫ _) ≫ (snd A₀ A₀).left = (_ ≫ _) ≫ (snd A₀ A₀).left
      rw [Category.assoc, lift_left_snd, Category.assoc, hsq.2, ← Category.assoc, lift_left_snd]
      show φ₂ ≫ (snd A₀ A₀).left ≫ (act₀.act (star c)).left = (snd A A).left ≫ (act.act (star c)).left ≫ φ
      rw [reassoc_of% hsq.2, hact]
  have e₁ : eSec (G2 A₀) ≫ (lift (fst A₀ A₀ ≫ act₀.act c) (snd A₀ A₀)).left = eSec (G2 A₀) := by
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst A₀ A₀).left = _ ≫ (fst A₀ A₀).left
      rw [Category.assoc, lift_left_fst, GlobalTheory.SquareDescent.eSec_fst]
      show eSec (G2 A₀) ≫ (fst A₀ A₀).left ≫ (act₀.act c).left = _
      rw [reassoc_of% GlobalTheory.SquareDescent.eSec_fst, eSec_comp_of_isMonHom]
    · show (_ ≫ _) ≫ (snd A₀ A₀).left = _ ≫ (snd A₀ A₀).left
      rw [Category.assoc, lift_left_snd]
  have e₂ : eSec (G2 A₀) ≫ (lift (fst A₀ A₀) (snd A₀ A₀ ≫ act₀.act (star c))).left = eSec (G2 A₀) := by
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst A₀ A₀).left = _ ≫ (fst A₀ A₀).left
      rw [Category.assoc, lift_left_fst]
    · show (_ ≫ _) ≫ (snd A₀ A₀).left = _ ≫ (snd A₀ A₀).left
      rw [Category.assoc, lift_left_snd, GlobalTheory.SquareDescent.eSec_snd]
      show eSec (G2 A₀) ≫ (snd A₀ A₀).left ≫ (act₀.act (star c)).left = _
      rw [reassoc_of% GlobalTheory.SquareDescent.eSec_snd, eSec_comp_of_isMonHom]
  have hPφ : pull φ₂ (cls _ hP₀) = cls _ hP := ((cls_eq_iff hP (pull_isLB hP₀ φ₂)).2 iP).symm
  have hR : pull (lift (fst A A ≫ act.act c) (snd A A)).left (cls _ hP) =
      pull (lift (fst A A) (snd A A ≫ act.act (star c))).left (cls _ hP) :=
    (cls_eq_iff (pull_isLB hP _) (pull_isLB hP _)).2 (hros c)
  have hpb := GlobalTheory.SiegelDescent.isPullback_square gp.1 φ₂ hsq
  have z₁ : pull (eSec (G2 A₀)) (cls _ hN) = 0 := by
    rw [cN, map_sub, ← pull_comp, ← pull_comp, e₁, e₂, sub_self]
  have z₂ : pull (pullback.fst (G2 A₀).hom π) (cls _ hN) = 0 := by
    rw [cN, ← hpb.isoPullback_inv_fst, pull_comp, map_sub, ← pull_comp φ₂, ← pull_comp φ₂, c₁, c₂,
      pull_comp, pull_comp, hPφ, hR, sub_self, map_zero]
  obtain ⟨t, ht⟩ := GlobalTheory.exists_gen_of_rigidified_of_flat_baseChange GlobalTheory.SemiRigid.globalFns Y X π (G2 A₀) _ hB hN
    inferInstance inferInstance inferInstance
    ((cls_eq_zero_iff (pull_isLB hN _)).1 ((cls_pull hN _ _).trans z₁))
    ((cls_eq_zero_iff (pull_isLB hN _)).1 ((cls_pull hN _ _).trans z₂))
  have h0 : cls _ hN = 0 := (cls_eq_zero_iff hN).2 ⟨t, ht⟩
  rw [cN, sub_eq_zero, ← cls_pull hP₀ _ h₁, ← cls_pull hP₀ _ h₂] at h0
  exact (cls_eq_iff h₁ h₂).1 h0.symm

end GlobalTheory.RosatiDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RuleEqOfAgreeRapoport
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.RealMult.rule_eq_of_agree_rapoport : GlobalTheory.Published.DelignePappasModel → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (R₀ : Type) [CommRing R₀]
  (k : ℕ) (r s : Rule (trivialObjectCondition 𝔠) R₀ k),
  (∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)), X.IsRapoport → ∀ δ : X.DetGen,
    r.val R X trivial δ = s.val R X trivial δ) → r = s :=
  GlobalTheory.RealMult.rule_eq_of_agree_rapoport_of_level GlobalTheory.RealMult.exists_faithfullyFlat_level
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernFormPullbackStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.second_chern_form_pullback : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsRegVar p D) (σ : k →+* ℂ),
    ∀ (Y : Scheme.{0}) (p' : Y ⟶ Sp k) (D' : ℕ) (hY : IsRegVar p' D') (π : Y ⟶ X) (w : π ≫ p = p'),
    ∀ (E : X.Modules) (h : VMetric p E 2) (H : h.IsCInf) (fl : Vert.Flag E 2) (fl' : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    fld _ (c2F hY σ (h.pull π w) fl') = pullF hX hY σ π w (fld _ (c2F hX σ h fl)) := by
  first | exact @GlobalTheory.SecondChernPull.c2F_pull_eq_pullF_c2F | exact GlobalTheory.SecondChernPull.c2F_pull_eq_pullF_c2F | (intros; apply GlobalTheory.SecondChernPull.c2F_pull_eq_pullF_c2F <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueIntegralPointEqAdicSumTerms
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.IntEval

theorem eval_at_integral : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V) D A G) (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ (x : TFK (R := V) (FractionRing V) ⟶ A.A) (e : FrAt x) (h : 𝟙_ (Over (Sp V)) ⟶ G) (g : GtPt D.toPre (𝟙_ (Over (Sp V)))) (g' : GtPtF D.toPre (FractionRing V)) (l : FractionRing V), l ≠ 0 → GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.FormalEq U.toUnifPre h g → IntTerm.Ext U.toUnifPre x h → GtPt.IsPullF (FractionRing V) (toUnit (TF (R := V) (FractionRing V))).left g g' → IntTerm.FrRel U.toUnifPre w₀ x e h l → ∃ w : Frm D.toPre (FractionRing V) 1 g'.b, w.IsGen ∧ IntTerm.IntFrm D.toPre g.b w l ∧ IntTerm.Lies U.toUnifPre w₀ g' w x e := by
  intro V _ _ _ hV D A G _ _ hG U w₀ hw₀ x e h g g' l hl hF hExt hP hR
  obtain ⟨f, hf, hfv⟩ := hR
  obtain ⟨t, ht, htl⟩ := GlobalTheory.T.exists_integral_generator_rigidification_all_levels V hV D A G U.toUnifPre h g hF f hf
  have hφ : DegPre.lineφ D.toPre (FractionRing V) g'.b = fun i =>
      (toUnit (TF (R := V) (FractionRing V))).left ≫ (![(η[D.toPre.P.A]).left, g.b.left] : Fin 2 → _) i := by
    funext i
    fin_cases i
    · exact Over.comp_left (f := toUnit (TF (R := V) (FractionRing V))) (g := η[D.toPre.P.A])
    · exact hP.1
  obtain ⟨w₁, hw₁, hv₁⟩ := exists_gen D.toPre.P.isLB (φ' := DegPre.lineφ D.toPre (FractionRing V) g'.b)
    (ε' := DegPre.lineε 1) (by rw [hφ]; exact fun _ _ _ => rfl)
    (LB.pullGen D.toPre.P.L _ _ t (toUnit (TF (R := V) (FractionRing V))).left) (pullGen_isGen _ _ _ _ ht _)
  obtain ⟨w, hw, hwv⟩ := TorsionValue.exists_frm_scale w₁ hw₁ (inv_ne_zero hl)
  have hwt : ∀ z J, Good D.toPre.P.L z J → UT.cst (FractionRing V) z l * (val w (𝟙 _) z J).val =
      (val t (toUnit (TF (R := V) (FractionRing V))).left z J).val := by
    intro z J hJ
    rw [hwv z J hJ, hv₁ _ _ z J hJ, val_pull hJ, Category.id_comp, ← _root_.mul_assoc, GlobalTheory.UT.CoefBasic.cst_eq,
      GlobalTheory.UT.CoefBasic.cst_eq, ← map_mul, mul_inv_cancel₀ hl, map_one, _root_.one_mul]
  refine ⟨w, hw, ⟨t, ht, hwt⟩, ?_⟩
  intro k hk wk hwk hwkg s s' v hExp hVal
  obtain ⟨σ', hIso, n, c, σ, fs, hE, hσ, hs⟩ := hExp
  choose xs hxs using fun i => GlobalTheory.ExpansionValueZero.exists_coeff (A := V) U.LG.isLB (σ i) h.left
    (GeneratorPullback.powGen U.LG.L _ _ f k) (powGen_isGen _ _ _ _ hf k) (fun W _ q => by simp)
  have hxs' : ∀ i (Z : Scheme.{0}) (r : Z ⟶ Sp V) z J, Good U.LG.L z J →
      sval (σ i) (r ≫ h.left) z J = Geo.Tor.cst r z (xs i) * (val f r z J ^ k).val :=
    fun i Z r z J hJ => (hxs i Z r z J hJ).trans (by rw [val_pow])
  choose a ha using fun i α => GlobalTheory.T.exists_integral_coefficient_section_coordinate_rig V D.toPre g t ht k α (fs i α)
  have hv := GlobalTheory.T.section_value_generic_point_integral_section V (maximalIdeal V) D A G U.toUnifPre w₀ x e h l f hExt hfv k s σ' hIso n c σ hσ xs hxs' v hVal
  have hwk' : ∀ z J, Good D.toPre.P.L z J → UT.cst (FractionRing V) z (l ^ k) * (val wk (𝟙 _) z J).val =
      (val t (toUnit (TF (R := V) (FractionRing V))).left z J ^ k).val := by
    intro z J hJ
    rw [hwk z J hJ, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, ← hwt z J hJ, mul_pow,
      GlobalTheory.UT.CoefBasic.cst_eq, GlobalTheory.UT.CoefBasic.cst_eq, map_pow]
  have hc := GlobalTheory.T.integral_combination_terms_rational_point_frame V D.toPre g g' hP t l hl k wk hwkg hwk' s' n c fs hs a ha
  have hI := admissibleBase_of_completeNormalLocalCharZero hV
  have key := EvalZero.sumF_comb hI (FractionRing V) Finset.univ (fun i => c i * (l ^ k)⁻¹) _ _ fun i =>
    EvalZero.sumF_map (maximalIdeal V) (FractionRing V) (a i) (xs i) fun e' =>
      GlobalTheory.T.section_value_integral_point_congruent_term_sum V (maximalIdeal V) D A G U.toUnifPre h g hF f t e' k (htl e') (σ i) (fs i) (hE i e') (xs i) (hxs' i)
        (a i) (ha i)
  have hlk : l ^ k ≠ 0 := pow_ne_zero _ hl
  convert key using 1
  · funext α
    simp only [Algebra.algebraMap_self, RingHom.id_apply]
    rw [show (∑ i, c i * (l ^ k)⁻¹ * algebraMap V (FractionRing V) (a i α)) =
        (l ^ k)⁻¹ * ∑ i, c i * algebraMap V (FractionRing V) (a i α) by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring,
      ← hc α, ← _root_.mul_assoc, inv_mul_cancel₀ hlk, _root_.one_mul]
  · simp only [Algebra.algebraMap_self, RingHom.id_apply]
    rw [show (∑ i, c i * (l ^ k)⁻¹ * algebraMap V (FractionRing V) (xs i)) =
        (l ^ k)⁻¹ * ∑ i, c i * algebraMap V (FractionRing V) (xs i) by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring,
      ← hv, mul_comm v, ← _root_.mul_assoc, inv_mul_cancel₀ hlk, _root_.one_mul]

end GlobalTheory.Poinc.IntEval
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsAdjointNefSeparateEtaleFibre
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open GlobalTheory.Discrepancy GlobalTheory.QCoh

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.EtaleSep

set_option maxHeartbeats 1000000 in

theorem sections_separate_fibre : GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.NefNumerics → ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (p : W ⟶ Sp ℂ) (f : M ⟶ W) [IsDominant f] (n : ℕ) [SmoothOfRelativeDimension n p] [SmoothOfRelativeDimension n (f ≫ p)], IsProjOver p → IsProjOver (f ≫ p) → 1 ≤ n → letI := algebraΓOfHom p; letI := algebraΓOfHom (f ≫ p); ∀ (K : CanonLB (f ≫ p) n) (N : LB W) (hN : N.IsLB) (N' B : LB M) (hN' : N'.IsLB) (hB : B.IsLB) (m : ℕ) (x : Sp ℂ ⟶ W) (U : W.Opens), IsNef ℂ N → IsBig ℂ N → IsNef ℂ (N.pull f) → IsBig ℂ (N.pull f) → IsNef ℂ N' → (n + 1).choose 2 < m → cls B hB = m • CechPic.pull f (cls N hN) + cls N' hN' → x ≫ p = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ U → Etale (f ∣_ U) → (∀ (Z : Closeds W) (e : ℕ), IsIrreducible (Z : Set W) → Set.range x ⊆ Z → 1 ≤ e → topologicalKrullDim (Z : Set W) = e → 0 < interNumRed ℂ Z fun _ : Fin e => N) → ∀ (J : Type) [Fintype J] (z : J → (Sp ℂ ⟶ M)), Function.Injective z → (∀ j, z j ≫ f = x) → ∀ (k : J → (tens K.bundle B).ι) (hk : ∀ j, ⊤ ≤ z j ⁻¹ᵁ (tens K.bundle B).U (k j)) (a : J → ℂ), (∀ g : H0 (f ≫ p) (tens K.bundle B) ⊤, ∑ j, a j * H0.val (z j) (k j) le_top (hk j) g = 0) → a = 0 := by
  intro hK hNN M W _ _ p f _ n _ _ hp hpM hn1
  letI := algebraΓOfHom p
  letI := algebraΓOfHom (f ≫ p)
  intro K N hN N' B hN' hB m x U hNn hNb hNfn hNfb hN'n hm hBc hxp hxU hEt hpos J _ z hzi hz k hk a hrel
  haveI : IsLocallyNoetherian W := by
    haveI := SmoothOfRelativeDimension.smooth n p; exact LocallyOfFiniteType.isLocallyNoetherian p
  haveI : IsLocallyNoetherian M := by
    haveI := SmoothOfRelativeDimension.smooth n (f ≫ p); exact LocallyOfFiniteType.isLocallyNoetherian (f ≫ p)
  set c₀ := (n + 1).choose 2 with hc₀def
  set pt : Sp ℂ := IsLocalRing.closedPoint ℂ with hpt
  set x₀ : W := x pt with hx₀
  have hrange : ∀ Z : Closeds W, x₀ ∈ Z → Set.range x ⊆ Z := by
    rintro Z h _ ⟨q, rfl⟩
    rwa [Subsingleton.elim q pt]
  have hx₀c : IsClosed ({x₀} : Set W) := GlobalTheory.T.isClosed_image_section_projective_over_field ℂ W p x hp hxp
  have hx₀U : x₀ ∈ U := hxU (Set.mem_univ pt)

  obtain ⟨N₀, h₀, hc₀, hn₀, hb₀⟩ := GlobalTheory.nef_big_of_cls_eq_smul_add_smul hNN ℂ W p hp N N hN hN (2 * c₀ + 1) 0
    hNn hNb hNn (by omega)
  obtain ⟨m', D₀, U', hm', hD₀, hcur, hxU', hklt, hnk⟩ := GlobalTheory.KollarApp.isolatedNonKlt_smooth hK.2 W p n hp hn1
    N₀ 2 x₀ two_pos hn₀ hb₀ hx₀c (fun Z e hZ hxZ he hdim => by
      have h1 := hpos Z e hZ (hrange Z hxZ) he hdim
      have h2 := GlobalTheory.mixExp_interNumRed hNN ℂ W p hp N N N₀ hN hN h₀ (2 * c₀ + 1) 0 Z e hNn hNn hc₀ hdim
      have h3 : ((2 * c₀ + 1 : ℕ) : ℤ) ^ e ≤ interNumRed ℂ Z (fun _ : Fin e => N₀) := by
        have : (0 : ℤ) ≤ ((2 * c₀ + 1 : ℕ) : ℤ) ^ e := by positivity
        nlinarith
      have h3' : (((2 * c₀ + 1 : ℕ) : ℝ)) ^ e ≤ (interNumRed ℂ Z (fun _ : Fin e => N₀) : ℝ) := by
        exact_mod_cast h3
      have h4 : (((c₀ : ℕ) : ℝ) * 2) ^ e < ((2 * c₀ + 1 : ℕ) : ℝ) ^ e := by
        refine pow_lt_pow_left₀ ?_ (by positivity) (by omega)
        exact_mod_cast (by omega : c₀ * 2 < 2 * c₀ + 1)
      rw [lt_div_iff₀ (by positivity), ← mul_pow]
      push_cast at h4 h3' ⊢
      linarith)

  obtain ⟨D₁, hD₁, heq⟩ := GlobalTheory.T.exists_effective_cartierDivisorPullback_of_dominant M W f D₀ hD₀
  have hcls := GlobalTheory.T.cechPicardClass_cartierDivisorPullback_eq_pullback M W f D₀ D₁ heq

  obtain ⟨M₀, hM₀, hcM, hnM, hbM⟩ := GlobalTheory.nef_big_of_cls_eq_smul_add_smul hNN ℂ M (f ≫ p) hpM (N.pull f) N'
    (pull_isLB hN f) hN' (2 * m - 2 * c₀ - 1) 2 hNfn hNfb hN'n (by omega)
  have hclsN : cls (N.pull f) (pull_isLB hN f) = CechPic.pull f (cls N hN) := cls_pull hN f _
  obtain ⟨Jd, hJ, hvan⟩ := GlobalTheory.NadelApp.nadel_canonical_add hK.1 M (f ≫ p) n hpM K B M₀ hB D₁ m' 2 hm' two_pos
    hD₁ hnM hbM (fun C hC => by
      have e1 := GlobalTheory.interNumRed_of_cls_eq_nsmul_add ℂ M (f ≫ p) hpM B (N.pull f) N' hB (pull_isLB hN f) hN' m 1
        C hC (by rw [hBc, one_smul, hclsN])
      have e2 := GlobalTheory.interNumRed_of_cls_eq_nsmul_add ℂ M (f ≫ p) hpM M₀ (N.pull f) N' hM₀ (pull_isLB hN f) hN'
        (2 * m - 2 * c₀ - 1) 2 C hC hcM
      have e3 := interNumRed_one_congr (k := ℂ) (isLB_toLB D₁) (pull_isLB (isLB_toLB D₀) f)
        (hcls.trans (cls_pull (isLB_toLB D₀) f _).symm) C
      have e4 := GlobalTheory.T.intersectionNumber_pullback_proportional_of_proportional M W p f hp hpM (toLB D₀) N₀ (isLB_toLB D₀) h₀ 2 m' (fun C' hC' => by
        have := hcur C' hC'
        have hm'0 : (m' : ℚ) ≠ 0 := by exact_mod_cast hm'.ne'
        rw [Nat.cast_ofNat, div_eq_div_iff hm'0 two_ne_zero] at this
        have h' : ((2 * interNumRed ℂ C' ![toLB D₀] : ℤ) : ℚ) = ((m' * interNumRed ℂ C' ![N₀] : ℤ) : ℚ) := by
          push_cast; linarith
        push_cast
        exact_mod_cast h') C hC
      have e5 := GlobalTheory.interNumRed_of_cls_eq_nsmul_add ℂ M (f ≫ p) hpM (N₀.pull f) (N.pull f) (N.pull f)
        (pull_isLB h₀ f) (pull_isLB hN f) (pull_isLB hN f) (2 * c₀ + 1) 0 C hC
        (by rw [cls_pull h₀ f _, hc₀, hclsN, zero_smul, add_zero, zero_smul, add_zero, map_nsmul])
      rw [e1, e3, e2]
      have hm'0 : (m' : ℚ) ≠ 0 := by exact_mod_cast hm'.ne'
      have e4' : ((interNumRed ℂ C ![(toLB D₀).pull f] : ℤ) : ℚ) = m' * (2 * c₀ + 1) / 2 * interNumRed ℂ C ![N.pull f] := by
        have : (2 : ℚ) * interNumRed ℂ C ![(toLB D₀).pull f] = m' * interNumRed ℂ C ![N₀.pull f] := by exact_mod_cast e4
        rw [e5] at this
        push_cast at this
        linarith
      have hsub : ((2 * m - 2 * c₀ - 1 : ℕ) : ℚ) = 2 * m - 2 * c₀ - 1 := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
      rw [e4']
      push_cast [hsub]
      field_simp
      ring)

  set UM : M.Opens := f ⁻¹ᵁ (U ⊓ U') with hUM
  have hEtM : Etale (UM.ι ≫ f) := by
    haveI := hEt
    have hle : UM ≤ f ⁻¹ᵁ U := fun y hy => hy.1
    have e : UM.ι ≫ f = M.homOfLE hle ≫ (f ∣_ U) ≫ U.ι := by
      rw [morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]
    rw [e]; infer_instance
  have hkl := GlobalTheory.T.kawamataLogTerminal_iff_etale_pullback M W p f n m' UM D₀ D₁ hEtM hm' heq
  have hsupp : ∀ y ∈ UM, (y ∈ Jd.support ↔ f y = x₀) := by
    intro y hy
    rw [hJ, hkl y hy]
    have hyU' : f y ∈ U' := hy.2
    constructor
    · intro h; by_contra hne; exact h (hklt _ hyU' hne)
    · intro e; rw [e]; exact hnk
  have hfz : ∀ j, f (z j pt) = x₀ := fun j => by
    have := congrArg (fun h : Sp ℂ ⟶ W => h pt) (hz j)
    simpa using this
  have hzM : ∀ j, z j pt ∈ UM := fun j => by
    show f (z j pt) ∈ U ⊓ U'
    rw [hfz j]; exact ⟨hx₀U, hxU'⟩
  have hzp : ∀ j, z j ≫ f ≫ p = 𝟙 _ := fun j => by rw [← Category.assoc, hz j, hxp]
  have hzne : ∀ i j, i ≠ j → z i pt ≠ z j pt := fun i j hij e =>
    hij (hzi (GlobalTheory.T.section_over_field_eq_of_closedPoint_image_eq ℂ M (f ≫ p) (z i) (z j) (hzp i) (hzp j) e))
  funext j
  show a j = 0
  obtain ⟨V, hzV, hV⟩ := GlobalTheory.T.isolated_in_fibre_of_etale_restriction M W f U hEt (z j pt) (by rw [hfz j]; exact hx₀U)
  obtain ⟨s, hs, hs'⟩ := GlobalTheory.T.exists_section_separating_closed_point ℂ M (f ≫ p) hpM (tens K.bundle B) (isLB_tens K.isLB hB) Jd (z j pt) (V ⊓ UM)
    (GlobalTheory.T.isClosed_image_section_projective_over_field ℂ M (f ≫ p) (z j) hpM (hzp j)) ⟨hzV, hzM j⟩ (fun y hy => by
      rw [hsupp y hy.2, ← hfz j]
      exact ⟨hV y hy.1, fun e => e ▸ rfl⟩) (hvan 1 one_pos)
  have h1 := hrel (H0.ofSec (f ≫ p) ⊤ s)
  rw [Finset.sum_eq_single j (fun i _ hij => by
      have : H0.val (z i) (k i) le_top (hk i) (H0.ofSec (f ≫ p) ⊤ s) = 0 := by
        by_contra hne
        exact hs' _ ((hsupp _ (hzM i)).2 (hfz i)) (hzne i j hij)
          ((GlobalTheory.T.lineBundleValueAtPoint_ne_zero_iff_mem_nonzeroLocus ℂ M (f ≫ p) _ s (z i) (k i) (hk i)).1 hne)
      rw [this, mul_zero]) (fun h => absurd (Finset.mem_univ j) h)] at h1
  exact (mul_eq_zero.1 h1).resolve_right ((GlobalTheory.T.lineBundleValueAtPoint_ne_zero_iff_mem_nonzeroLocus ℂ M (f ≫ p) _ s (z j) (k j) (hk j)).2 hs)

end GlobalTheory.EtaleSep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawLeftRestrictionIsPair
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatModel

theorem exists_obj_of_isogenous_model : GlobalTheory.Published.AbelianDualCrystal → GlobalTheory.Published.AbelianDeRham →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ →
    ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ → ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l])
    (𝔠 : FracId (FR E)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ (lattice c y) 0 X),
    (∀ a : orderC c, ∃ (α : X.A ⟶ X.A) (_ : IsMonHom α), ∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) →
    ∀ (k₀ : IntermediateField ℚ ℂ) (R₀ : Subring ℂ), FiniteDimensional ℚ k₀ → IsPlaceOver l lam k₀ R₀ →
    (∀ x ∈ R₀, x ∈ k₀) →
    ∀ (G₀ : Over (Sp R₀)) [GrpObj G₀] (p₀ : X.A.left ⟶ G₀.left) (P₀ : Out.PolAV (Sp R₀)) (Ψ₀ : P₀.A ⟶ G₀),
      IsAbelianScheme G₀ → IsGrpPullback X.A G₀ (spMap R₀.subtype) p₀ → IsMonHom Ψ₀ → IsFinite Ψ₀.left →
      Flat Ψ₀.left → Surjective Ψ₀.left →
      Eventually l lam fun R ↦ ∃ (X₀ : Obj (FR E) 𝔠 (Sp R)) (p : X.A.left ⟶ X₀.A.left) (cm : OAct (orderC c) X₀.A),
        X.IsPullBy X₀ (spMap R.subtype) p ∧
        (∀ a : OF E, cm.act (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF c a) = X₀.rm.act a) ∧
        (∀ (a : orderC c) (α : X.A ⟶ X.A), IsMonHom α →
          (∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) → α.left ≫ p = p ≫ (cm.act a).left) ∧
        ∀ (v₀ : epsR R₀ ⟶ G₀) (v' : X.Lie), IsTangent v₀ →
          v'.hom.left ≫ p₀ = spMap (Chart.dualMapR R₀.subtype) ≫ v₀.left → ∃ v : X₀.Lie, Obj.LieCorr R.subtype p v v' := by
  intro HD HR E _ _ _ I _ φ hφ c y hc l _ lam 𝔠 X U hα k₀ R₀ hk₀ hR₀ hR₀k G₀ _ p₀ P₀ Ψ₀ hG₀ hp₀ hΨ hfin hfl hsurj
  let σ : R₀ →+* Qb :=
    { toFun := fun x ↦ ⟨x, (hR₀.2.1 x x.2).1⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  obtain ⟨XQ, pQ, gQ, cmQ, hQ, hgQ, epQ, hrmQ, hαQ⟩ :=
    GlobalTheory.T.cm_uniformization_algebraic_model HD E I φ c (lattice c y) 𝔠 X U hα R₀ σ (fun _ ↦ rfl) G₀ p₀ hG₀ hp₀
  obtain ⟨k, hk, H⟩ := GlobalTheory.T.cm_endomorphism_place_integral HD HR (FR E) 𝔠 (orderC c) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF c) l lam k₀ R₀ (GlobalTheory.T.conductor_order_finite_integers E c) hk₀ hR₀
    hR₀k σ (fun _ ↦ rfl) G₀ P₀ Ψ₀ hG₀ hΨ hfin hfl hsurj XQ gQ cmQ hgQ hrmQ
  refine ⟨k ⊔ k₀, inferInstance, fun R hR ↦ ?_⟩
  have hle : R₀ ≤ R := fun x hx ↦ (hR.mono le_sup_right).2.2 x (hR₀k x hx) (hR₀.2.1 x hx)
  let j : R →+* Qb :=
    { toFun := fun x ↦ ⟨x, (hR.2.1 x x.2).1⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  obtain ⟨X₀, pj, g, cm, hj, hg, epj, hrm, hcm⟩ :=
    H R (hR.mono le_sup_left) (Subring.inclusion hle) j (fun _ ↦ rfl) (fun _ ↦ rfl)
  have hspec : spMap (algebraMap Qb ℂ) ≫ spMap j = spMap R.subtype := by
    rw [GlobalTheory.HomDescent.spMap_comp]; rfl
  have hX : X.IsPullBy X₀ (spMap R.subtype) (pQ ≫ pj) := hspec ▸ Obj.IsPullBy.trans hQ hj
  refine ⟨X₀, pQ ≫ pj, cm, hX, hrm, fun a α hα' hu ↦ ?_, fun v₀ v' hv₀ hv' ↦ ?_⟩
  · rw [← Category.assoc, hαQ a α hα' hu, Category.assoc, hcm, Category.assoc]
  · obtain ⟨v, hv, ev⟩ := GlobalTheory.T.tangent_pullback_chain_compat R₀ R (Subring.inclusion hle) (fun _ ↦ rfl) G₀ X₀.A X.A g (pQ ≫ pj) hg hX.grp v₀ v'.hom
      hv₀ (by rw [Category.assoc, epj, epQ]; exact hv')
    exact ⟨Serre.Lie.mk _ v hv, ev⟩

end GlobalTheory.LatModel
end
end

