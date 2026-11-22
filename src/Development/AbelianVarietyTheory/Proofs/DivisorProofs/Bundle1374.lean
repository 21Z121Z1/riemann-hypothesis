import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
import ReciprocityTheory.SemistableReduction.Bundle0025
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0165
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0160
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1351
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1359
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0522
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1358
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinFirst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0739
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0738
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0567
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0566
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0638
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0041
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StabTransitiveOfLemmas
import Formalism.HarderNarasimhan.StatementPl
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1361
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0104
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1352
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralRelation
section
set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

namespace GlobalTheory.SecIntegral

theorem exists_integral_relation : ∀ (F : Type) [Field F] (S : LinSys F), S.IsVariety → ∀ (r e : ℕ) (u : Fin r → Fin S.N → F) (th : (lbPow S.L e).Sec), (∀ y : S.Y, ∃ i, y ∈ nonzeroLocus (S.comb (u i))) → ∃ (m : ℕ) (a : Fin m → MvPolynomial (Fin r) F), (∀ k, (a k).IsHomogeneous (e * (m - k))) ∧ ∀ (K : Type) [Field K] [Algebra F K] (x : S.Pt K), S.powVal x.1 th ^ m + ∑ k, aeval (fun i => ∑ j, algebraMap F K (u i j) * S.coords x.1 j) (a k) * S.powVal x.1 th ^ (k : ℕ) = 0 := by
  intro F _ S hS r e u th hcov
  have hI : AlgebraicGeometry.IsIntegral S.Y := hS.isIntegral
  have hη : IsGenericPoint (genericPoint S.Y) Set.univ := by
    simpa using genericPoint_spec S.Y
  obtain ⟨m, b, hb⟩ := GlobalTheory.T.exists_integral_relation_C_mul_X_pow_of_valuationSubring F (S.Y.residueField (genericPoint S.Y)) (S.baseHom (resPt (genericPoint S.Y))) r e
    (fun i => S.val (resPt (genericPoint S.Y)) (S.comb (u i))) (S.powVal (resPt (genericPoint S.Y)) th)
    (GlobalTheory.T.exists_ratio_mem_valuationSubring_at_generic_point F S hS r e u th hcov _ hη)
  obtain ⟨a, ha, h0⟩ := GlobalTheory.T.homogeneous_components_of_cone_integral_equation _ _ _ r e m _ _ b hb
  exact ⟨m, a, ha, GlobalTheory.T.linearSystem_relation_of_generic_point F S hI r e u th _ hη m a ha h0⟩

end GlobalTheory.SecIntegral
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoAlgebraisation
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AlgUniq

theorem isPullback_square {S S' : Scheme.{0}} {G : Over S} {A : Over S'} {f : S' ⟶ S}
    {a : A.left ⟶ G.left} (hA : IsPullback a A.hom G.hom f)
    {φ₂ : (A ⊗ A).left ⟶ (G ⊗ G).left} (h : Geo.Tor.IsSquare a φ₂) :
    IsPullback φ₂ (A ⊗ A).hom (G ⊗ G).hom f := by
  have w₁ : (fst G G).left ≫ G.hom = (G ⊗ G).hom := Over.w _
  have w₂ : (snd G G).left ≫ G.hom = (G ⊗ G).hom := Over.w _
  have v₁ : (fst A A).left ≫ A.hom = (A ⊗ A).hom := Over.w _
  have v₂ : (snd A A).left ≫ A.hom = (A ⊗ A).hom := Over.w _
  have h₁ := h.1
  have h₂ := h.2
  refine ⟨⟨by rw [← w₁, reassoc_of% h₁, hA.w, reassoc_of% v₁]⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => pullback.lift
      (hA.lift (s.fst ≫ (fst G G).left) s.snd (by rw [Category.assoc, w₁, s.condition]))
      (hA.lift (s.fst ≫ (snd G G).left) s.snd (by rw [Category.assoc, w₂, s.condition]))
      (by rw [IsPullback.lift_snd, IsPullback.lift_snd])) (fun s => ?_) (fun s => ?_)
    (fun s m h1 h2 => ?_)⟩⟩
  · apply pullback.hom_ext
    · change _ ≫ (fst G G).left = _ ≫ (fst G G).left
      rw [Category.assoc, h₁, ← Category.assoc]
      exact (congrArg (· ≫ a) (pullback.lift_fst _ _ _)).trans (IsPullback.lift_fst _ _ _ _)
    · change _ ≫ (snd G G).left = _ ≫ (snd G G).left
      rw [Category.assoc, h₂, ← Category.assoc]
      exact (congrArg (· ≫ a) (pullback.lift_snd _ _ _)).trans (IsPullback.lift_fst _ _ _ _)
  · rw [← v₁, ← Category.assoc]
    exact (congrArg (· ≫ A.hom) (pullback.lift_fst _ _ _)).trans (IsPullback.lift_snd _ _ _ _)
  · apply pullback.hom_ext
    · refine Eq.trans ?_ (pullback.lift_fst _ _ _).symm
      change _ ≫ (fst A A).left = _
      apply hA.hom_ext
      · rw [IsPullback.lift_fst, ← h1, Category.assoc, Category.assoc, h₁]
      · rw [IsPullback.lift_snd, ← h2, Category.assoc, v₁]
    · refine Eq.trans ?_ (pullback.lift_snd _ _ _).symm
      change _ ≫ (snd A A).left = _
      apply hA.hom_ext
      · rw [IsPullback.lift_fst, ← h1, Category.assoc, Category.assoc, h₂]
      · rw [IsPullback.lift_snd, ← h2, Category.assoc, v₂]

theorem lbIso_pull_comp {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (a : Y ⟶ X) (b : Z ⟶ Y)
    (c : Z ⟶ X) (e : b ≫ a = c) : LBIso (L.pull c) ((L.pull a).pull b) := by
  subst e
  exact LBIso.symm (LBIso.chartPull (chartPullLinComb L a (fun _ : PUnit => b)
      (fun _ => b ≫ a) (fun _ => 1) (𝟙 _) fun _ => (Category.id_comp _).symm)
      (chartPullId _) (PolBaseChange.lbIso_refl (pull_isLB hL _)))

theorem square_comp {S S' : Scheme.{0}} {G G' : Over S} {A : Over S'} {a : A.left ⟶ G.left}
    {a' : A.left ⟶ G'.left} {g : G ⟶ G'} (hg : a ≫ g.left = a')
    {φ₂ : (A ⊗ A).left ⟶ (G ⊗ G).left} {φ₂' : (A ⊗ A).left ⟶ (G' ⊗ G').left}
    (h : Geo.Tor.IsSquare a φ₂) (h' : Geo.Tor.IsSquare a' φ₂') : φ₂ ≫ (g ⊗ₘ g).left = φ₂' := by
  have h₁ := h.1
  have h₂ := h.2
  apply pullback.hom_ext
  · change _ ≫ (fst G' G').left = _ ≫ (fst G' G').left
    rw [Category.assoc, ← Over.comp_left, tensorHom_fst, Over.comp_left, reassoc_of% h₁, hg, h'.1]
  · change _ ≫ (snd G' G').left = _ ≫ (snd G' G').left
    rw [Category.assoc, ← Over.comp_left, tensorHom_snd, Over.comp_left, reassoc_of% h₂, hg, h'.2]

theorem exists_iso_algebraisation : GlobalTheory.Published.FormalAlgebraisation.Morphisms → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) [∀ e, GrpObj (Y e)] (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (B B' : Over (Spec (CommRingCat.of R))) [GrpObj B] [GrpObj B'], IsAbelianScheme B → IsAbelianScheme B' → IsProjBy B.hom → ∀ (b : ∀ e, (Y e).left ⟶ B.left) (b' : ∀ e, (Y e).left ⟶ B'.left), (∀ e, IsGrpPullback (Y e) B (thick R I e) (b e)) → (∀ e, β e ≫ b (e + 1) = b e) → (∀ e, IsGrpPullback (Y e) B' (thick R I e) (b' e)) → (∀ e, β e ≫ b' (e + 1) = b' e) → ∃ g : B ≅ B', IsMonHom g.hom ∧ (∀ e, b e ≫ g.hom.left = b' e) ∧ (∀ g' : B ⟶ B', (∀ e, b e ≫ g'.left = b' e) → g' = g.hom) ∧ (∀ (M : LB B.left) (M' : LB B'.left), M.IsLB → M'.IsLB → (∀ e, LBIso (M.pull (b e)) (M'.pull (b' e))) → LBIso M (M'.pull g.hom.left)) ∧ ∀ (P : LB (B ⊗ B).left) (P' : LB (B' ⊗ B').left) (b₂ : ∀ e, (Y e ⊗ Y e).left ⟶ (B ⊗ B).left) (b₂' : ∀ e, (Y e ⊗ Y e).left ⟶ (B' ⊗ B').left), P.IsLB → P'.IsLB → (∀ e, Geo.Tor.IsSquare (b e) (b₂ e)) → (∀ e, Geo.Tor.IsSquare (b' e) (b₂' e)) → (∀ e, LBIso (P.pull (b₂ e)) (P'.pull (b₂' e))) → LBIso P (P'.pull (g.hom ⊗ₘ g.hom).left) := by
  intro H R _ _ I hI Y _ β B B' _ _ hB hB' hp b b' hb hβ hb' hβ'
  have := hB.proper
  have := hB'.proper
  obtain ⟨g, hg, hu⟩ := H.exists_iso hI (fun e => (hb e).1) hβ (fun e => (hb' e).1) hβ'
  obtain ⟨k, hk, hk', -⟩ := GlobalTheory.T.grpHom_algebraisation_of_reductions H R I hI B B' hB.proper hB'.proper Y Y β β b b' hb hβ hb' hβ'
    (fun e => 𝟙 _) (fun e => inferInstance)
    (fun e => by rw [Over.id_left, Over.id_left, Category.comp_id, Category.id_comp])
  have hkg : k = g.hom := hu k fun e => by rw [hk', Over.id_left, Category.id_comp]
  refine ⟨g, hkg ▸ hk, hg, hu, fun M M' hM hM' h => ?_, fun P P' b₂ b₂' hP hP' hs hs' h => ?_⟩
  · exact GlobalTheory.T.lineBundle_iso_of_iso_on_all_reductions R I hI B hB.smooth hp hB.geomConnected Y b (fun e => (hb e).1) M _ hM
      (pull_isLB hM' _) fun e => (h e).trans (pull_isLB hM _) (pull_isLB hM' _)
        (pull_isLB (pull_isLB hM' _) _) (lbIso_pull_comp hM' _ _ _ (hg e))
  · have hBB := AbelianSchemeGerms.isAbelianScheme_tensor B B hB hB
    exact GlobalTheory.T.lineBundle_iso_of_iso_on_all_reductions R I hI (B ⊗ B) hBB.smooth (isProjBy_tensor R B B hp hp) hBB.geomConnected
      (fun e => Y e ⊗ Y e) b₂ (fun e => isPullback_square (hb e).1 (hs e)) P _ hP
      (pull_isLB hP' _) fun e => (h e).trans (pull_isLB hP _) (pull_isLB hP' _)
        (pull_isLB (pull_isLB hP' _) _) (lbIso_pull_comp hP' _ _ _ (square_comp (hg e) (hs e) (hs' e)))

end GlobalTheory.AlgUniq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsJointShapeGenerated
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.FockAlg.MinFirst

noncomputable section
namespace GlobalTheory.RealLift.GenLift

section Objects

variable {P Q R S : ℕ}

theorem trace_Eab {p q : ℕ} (a b : Ix p q) : (Eab a b).trace = if a = b then 1 else 0 := by
  split_ifs with h
  · subst h; simp [Eab, Matrix.trace_single_eq_same]
  · simp [Eab, Matrix.trace_single_eq_of_ne _ _ _ h]

def chAct (p q : ℕ) (x : ℚ) : Mat p q →ₗ[ℂ] Module.End ℂ ℂ :=
  ((x : ℂ) • Matrix.traceLinearMap (Ix p q) ℂ ℂ).smulRight LinearMap.id

theorem chAct_apply (p q : ℕ) (x : ℚ) (X : Mat p q) (z : ℂ) :
    chAct p q x X z = ((x : ℂ) * X.trace) • z := by
  simp [chAct]

abbrev chMod (p q : ℕ) (x : ℚ) : GKMod p q where
  V := ℂ
  act := chAct p q x
  lie := by
    intro X Y
    ext
    simp [chAct_apply, Matrix.trace_sub, Matrix.trace_mul_comm X Y]
    ring
  kfin := fun _ => ⟨⊤, inferInstance, Submodule.mem_top, fun _ _ _ _ => Submodule.mem_top⟩
  wts := fun v => by
    refine Submodule.mem_iSup_of_mem (fun _ => x) ?_
    simp only [wtSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply]
    intro a
    rw [chAct_apply, trace_Eab, if_pos rfl, mul_one, sub_self]

abbrev shiftMod {r s : ℕ} (M : GKMod r s) (t : ℚ) : GKMod r s where
  V := M.V
  act := M.act - ((t : ℂ) • Matrix.traceLinearMap (Ix r s) ℂ ℂ).smulRight LinearMap.id
  lie := by
    intro X Y
    ext v
    have h := LinearMap.congr_fun (M.lie X Y) v
    simp only [LinearMap.sub_apply, LinearMap.smulRight_apply, LinearMap.smul_apply,
      Matrix.traceLinearMap_apply, Module.End.mul_apply, LinearMap.id_apply, map_sub, map_smul,
      Matrix.trace_sub, Matrix.trace_mul_comm X Y, sub_self, smul_zero, zero_smul, sub_zero] at h ⊢
    linear_combination (norm := module) h
  kfin := fun v => by
    obtain ⟨W, fW, hv, sW⟩ := M.kfin v
    refine ⟨W, fW, hv, fun X hX w hw => ?_⟩
    simp only [LinearMap.sub_apply, LinearMap.smulRight_apply, LinearMap.smul_apply,
      Matrix.traceLinearMap_apply, LinearMap.id_apply]
    exact W.sub_mem (sW X hX w hw) (W.smul_mem _ hw)
  wts := fun v => by
    refine (iSup_le fun μ => le_iSup_of_le (fun c => μ c - t) ?_ : (⨆ μ, wtSub M.act μ) ≤ _) (M.wts v)
    intro w hw
    simp only [wtSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
      Matrix.traceLinearMap_apply] at hw ⊢
    intro a
    have := hw a
    rw [trace_Eab, if_pos rfl]
    linear_combination (norm := module) this

theorem shiftMod_act {r s : ℕ} (M : GKMod r s) (t : ℚ) (Y : Mat r s) (v : M.V) :
    (shiftMod M t).act Y v = M.act Y v - ((t : ℂ) * Y.trace) • v := by
  show ((M.act - ((t : ℂ) • Matrix.traceLinearMap (Ix r s) ℂ ℂ).smulRight LinearMap.id :
    Mat r s →ₗ[ℂ] Module.End ℂ M.V) Y) v = _
  rw [LinearMap.sub_apply, LinearMap.sub_apply]
  simp [mul_smul]

end Objects

section Main

variable {P Q R S : ℕ}

theorem tmul_one_eq_zero {V : Type} [AddCommGroup V] [Module ℂ V] {v : V}
    (h : (1 : ℂ) ⊗ₜ[ℂ] v = 0) : v = 0 := by
  have := congrArg (TensorProduct.lid ℂ V) h
  simpa using this

def fMap (x t : ℚ) {M : GKMod R S} (pr : Pol P Q R S →ₗ[ℂ] M.V) :
    Pol P Q R S →ₗ[ℂ] TensorProduct ℂ (chMod P Q x).V (shiftMod M t).V :=
  TensorProduct.mk ℂ ℂ M.V 1 ∘ₗ pr

theorem fMap_apply (x t : ℚ) {M : GKMod R S} (pr : Pol P Q R S →ₗ[ℂ] M.V) (f : Pol P Q R S) :
    fMap x t pr f = (1 : ℂ) ⊗ₜ[ℂ] pr f := rfl

theorem fMap_eq_zero {x t : ℚ} {M : GKMod R S} {pr : Pol P Q R S →ₗ[ℂ] M.V} {f : Pol P Q R S}
    (h : fMap x t pr f = 0) : pr f = 0 := tmul_one_eq_zero h

theorem intw_fMap {x t : ℚ} {M : GKMod R S} {pr : Pol P Q R S →ₗ[ℂ] M.V} (hL : IsLift x t M pr) :
    Intw (chMod P Q x) (shiftMod M t) (fMap x t pr) := by
  refine ⟨fun X => LinearMap.ext fun f => ?_, fun Y => LinearMap.ext fun f => ?_⟩
  · change (1 : ℂ) ⊗ₜ[ℂ] pr (fockAct1 P Q R S X f) =
      TensorProduct.map (chAct P Q x X) LinearMap.id ((1 : ℂ) ⊗ₜ[ℂ] pr f)
    rw [TensorProduct.map_tmul, LinearMap.id_apply, hL.2.1 X f, chAct_apply, TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  · change (1 : ℂ) ⊗ₜ[ℂ] pr (fockAct2 P Q R S Y f) =
      TensorProduct.map LinearMap.id ((shiftMod M t).act Y) ((1 : ℂ) ⊗ₜ[ℂ] pr f)
    rw [TensorProduct.map_tmul, LinearMap.id_apply, shiftMod_act, hL.2.2 Y f, add_sub_cancel_right]

theorem hw_chMod (p q : ℕ) (x : ℚ) : IsHW (chMod p q x).act (fun _ => x) (1 : ℂ) := by
  refine ⟨one_ne_zero, (mem_hwSub _ _ _).2 ⟨fun a => ?_, fun a b hab => ?_⟩⟩
  · change chAct p q x _ 1 - _ = 0
    rw [chAct_apply, trace_Eab, if_pos rfl]; simp [smul_eq_mul]
  · change chAct p q x _ 1 = 0
    have : a ≠ b := by
      rintro rfl
      cases a <;> simp [posC] at hab
    rw [chAct_apply, trace_Eab, if_neg this]; simp

theorem hw_chMod_eq {p q : ℕ} {x : ℚ} {ν : Ix p q → ℚ} {w : (chMod p q x).V}
    (h : IsHW (chMod p q x).act ν w) : ν = fun _ => x := by
  funext a
  have h1 := ((mem_hwSub _ _ _).1 h.2).1 a
  change chAct p q x _ w - _ = 0 at h1
  rw [chAct_apply, trace_Eab, if_pos rfl, mul_one, ← sub_smul, smul_eq_zero] at h1
  rcases h1 with h1 | h1
  · exact_mod_cast (sub_eq_zero.1 h1).symm
  · exact absurd h1 h.1

theorem irr_chMod (p q : ℕ) (x : ℚ) : IrrGK (chMod p q x) :=
  ⟨inferInstanceAs (Nontrivial ℂ), fun N _ => Ideal.eq_bot_or_top N⟩

theorem admissible_traceCharacterGKModule (p q : ℕ) (x : ℚ) : AdmGK (chMod p q x) := fun _ =>
  inferInstanceAs (FiniteDimensional ℂ ↥(hwSub (chAct p q x) _))

end Main

theorem genBy_of_isLift : ∀ (P Q R S : ℕ) (x t : ℚ) (M : Formalism.BasicNotions.TH.GKMod R S)
    (pr : Formalism.BasicNotions.TH.Pol P Q R S →ₗ[ℂ] M.V), GlobalTheory.RealLift.IsLift x t M pr → Nontrivial M.V →
    ∃ μ' : Formalism.BasicNotions.TH.Ix R S → ℚ, Formalism.BasicNotions.TH.JointShape P Q R S (fun _ => x) μ' ∧
      GlobalTheory.RealLift.GenBy M (fun c => μ' c + t) := by
  intro P Q R S x t M pr hL hM
  have hI := intw_fMap (P := P) (Q := Q) hL
  have hf : fMap x t pr ≠ 0 := by
    obtain ⟨v, hv⟩ := exists_ne (0 : M.V)
    obtain ⟨f, rfl⟩ := hL.1 v
    intro h
    exact hv (fMap_eq_zero (LinearMap.congr_fun h f))
  have hmin : ∀ ν w, IsHW (chMod P Q x).act ν w →
      degW (cPair R S) (fun _ : Ix P Q => x) ≤ degW (cPair R S) ν := by
    intro ν w h
    rw [hw_chMod_eq h]
  obtain ⟨⟨μ', P0, hJ0, h10, h20, hf0⟩, -⟩ := GlobalTheory.FockAlg.min_first P Q R S (chMod P Q x)
    (shiftMod M t) (fMap x t pr) (irr_chMod P Q x) (admissible_traceCharacterGKModule P Q x) hI hf (fun _ => x)
    ⟨1, hw_chMod P Q x⟩ hmin
  have hpr0 : pr P0 ≠ 0 := fun h => hf0 (by rw [fMap_apply, h, TensorProduct.tmul_zero])
  have hP0mem : P0 ∈ hwSub (fockAct1 P Q R S) (fun _ => x) ⊓ hwSub (fockAct2 P Q R S) μ' ⊓
      Submodule.span ℂ (jointHarm P Q R S) := ⟨⟨h10.2, h20.2⟩, Submodule.subset_span hJ0⟩
  have hshape : JointShape P Q R S (fun _ => x) μ' := by
    by_contra h
    have := hP0mem
    rw [GlobalTheory.FockAlg.jointHarm_hw_eq_bot P Q R S _ _ h, Submodule.mem_bot] at this
    exact h10.1 this

  have hw0 : IsHW M.act (fun c => μ' c + t) (pr P0) := by
    refine ⟨hpr0, (mem_hwSub _ _ _).2 ⟨fun a => ?_, fun a b hab => ?_⟩⟩
    · have e := ((mem_hwSub _ _ _).1 h20.2).1 a
      rw [hL.2.2, trace_Eab, if_pos rfl, sub_eq_zero.1 e, map_smul]
      push_cast
      module
    · have e := ((mem_hwSub _ _ _).1 h20.2).2 a b hab
      have : a ≠ b := by
        rintro rfl
        cases a <;> simp [posC] at hab
      rw [hL.2.2, trace_Eab, if_neg this, e, map_zero]
      simp
  refine ⟨μ', hshape, pr P0, hw0, ?_⟩

  set G := genSub M.act {pr P0} with hG
  set T : Submodule ℂ (Pol P Q R S) := G.comap pr with hT
  have hT1 : ∀ X, ∀ y ∈ T, fockAct1 P Q R S X y ∈ T := by
    intro X y hy
    rw [Submodule.mem_comap, hL.2.1]
    exact G.smul_mem _ hy
  have hT2 : ∀ Z, ∀ y ∈ T, fockAct2 P Q R S Z y ∈ T := by
    intro Z y hy
    have e := hL.2.2 Z y
    rw [Submodule.mem_comap, eq_sub_of_add_eq e.symm]
    exact G.sub_mem (genSub_stable _ _ Z hy) (G.smul_mem _ hy)
  have hker : LinearMap.ker (fMap x t pr) ≤ T := by
    intro y hy
    rw [Submodule.mem_comap, fMap_eq_zero (LinearMap.mem_ker.1 hy)]
    exact G.zero_mem
  have hP0T : P0 ∈ T := subset_genSub M.act {pr P0} rfl
  have hJ : ∀ P' ∈ jointHarm P Q R S, P' ∈ hwSub (fockAct1 P Q R S) (fun _ => x) → P' ∈ T := by
    intro P' hJ' hh
    obtain ⟨U, fU, hU, sU⟩ := ((GlobalTheory.FockPolGK.pol_locFin_weights P Q R S).2 P').1
    obtain ⟨-, -, s2, -⟩ := GlobalTheory.FockAlg.harm_graded_stable P Q R S _ (Or.inr (Or.inr rfl))
    have sH : KStable (fockAct2 P Q R S) (hwSub (fockAct1 P Q R S) (fun _ => x)) :=
      fun Z _ w hw => hw_map (fockAct2 P Q R S Z) (fun Y _ v => fockAct1_fockAct2_commute Y Z v) hw
    by_contra hPT
    obtain ⟨ν, u, hu, hhw, hN⟩ := exists_hw_notMem kLie2 wts2
      (W := U ⊓ (Submodule.span ℂ (jointHarm P Q R S) ⊓ hwSub (fockAct1 P Q R S) (fun _ => x)))
      (N := T) inferInstance (kStable_inf sU (kStable_inf s2 sH)) (fun Z _ y hy => hT2 Z y hy)
      (fun h => hPT (h ⟨hU, Submodule.subset_span hJ', hh⟩))
    have hmem : u ∈ hwSub (fockAct1 P Q R S) (fun _ => x) ⊓ hwSub (fockAct2 P Q R S) ν ⊓
        Submodule.span ℂ (jointHarm P Q R S) := ⟨⟨hu.2.2, hhw.2⟩, hu.2.1⟩
    have hsh : JointShape P Q R S (fun _ => x) ν := by
      by_contra h
      rw [GlobalTheory.FockAlg.jointHarm_hw_eq_bot P Q R S _ _ h, Submodule.mem_bot] at hmem
      exact hhw.1 hmem
    obtain rfl : ν = μ' :=
      (GlobalTheory.JointShapeUniq.jointShape_unique_deg P Q R S _ _ _ _ hsh hshape).1.1 rfl
    have hline := GlobalTheory.JointHarm.finrank_joint_highest_of_shape P Q R S _ _ hshape
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨P0, hP0mem⟩ : ↥(hwSub (fockAct1 P Q R S)
      (fun _ => x) ⊓ hwSub (fockAct2 P Q R S) ν ⊓ Submodule.span ℂ (jointHarm P Q R S)))
      (fun h => h10.1 (congrArg Subtype.val h))).1 hline ⟨u, hmem⟩
    have hu' : u = c • P0 := (congrArg Subtype.val hc).symm
    exact hN (hu' ▸ T.smul_mem c hP0T)
  have hall : ∀ P', P' ∈ T := by
    intro P'
    obtain ⟨W, fW, hW, sW⟩ := ((GlobalTheory.FockPolGK.pol_locFin_weights P Q R S).1 P').1
    by_contra hPT
    obtain ⟨ν, u, hu, hhw, hN⟩ := exists_hw_notMem kLie1 wts1 fW sW (fun X _ y hy => hT1 X y hy)
      (fun h => hPT (h hW))
    have hpru : pr u ≠ 0 := fun h => hN (by rw [Submodule.mem_comap, h]; exact G.zero_mem)
    obtain rfl : ν = fun _ => x := by
      funext a
      have e := ((mem_hwSub _ _ _).1 hhw.2).1 a
      have e2 := congrArg pr e
      rw [map_sub, map_smul, hL.2.1, trace_Eab, if_pos rfl, mul_one, map_zero, ← sub_smul,
        smul_eq_zero] at e2
      rcases e2 with e2 | e2
      · exact_mod_cast (sub_eq_zero.1 e2).symm
      · exact absurd e2 hpru
    exact hN (hw_mem hI hmin T hker hT2 hJ hhw.2)
  refine eq_top_iff.2 fun v _ => ?_
  obtain ⟨f, rfl⟩ := hL.1 v
  exact hall f

end GlobalTheory.RealLift.GenLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLagrangianDecompositionInert
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertWitt

def stdLat (E : Type) [Field E] [NumberField E] (n : ℕ) : Submodule (𝓞 E) (Fin n → E) :=
  LinearMap.range (LinearMap.pi fun i : Fin n => (Algebra.linearMap (𝓞 E) E).comp (LinearMap.proj i))

theorem mem_stdLat {E : Type} [Field E] [NumberField E] {n : ℕ} (x : Fin n → E) :
    x ∈ stdLat E n ↔ ∀ i, IsIntegral ℤ (x i) := by
  constructor
  · rintro ⟨y, rfl⟩ i
    exact (y i).2
  · intro h
    refine ⟨fun i => ⟨x i, h i⟩, funext fun i => rfl⟩

theorem stdLat_isLattice (E : Type) [Field E] [NumberField E] (n : ℕ) : (stdLat E n).IsLattice E := by
  refine ⟨?_, ?_⟩
  · rw [stdLat, LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map _
  · rw [eq_top_iff]
    intro x _
    have hx : x = ∑ i, x i • Pi.single i (1 : E) := by
      ext j; simp [Pi.single_apply]
    rw [hx]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    refine (mem_stdLat _).2 fun j => ?_
    by_cases h : j = i
    · subst h; simpa using isIntegral_one
    · simpa [Pi.single_apply, h] using isIntegral_zero

end GlobalTheory.InertWitt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalLiftSectionsOnClosedSubscheme
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Vanishing

open TopologicalSpace Opposite H0

theorem exists_local_lift_H0On : ∀ (k : Type) [Field k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (B : LB Y), B.IsLB → ∀ (I : Y.IdealSheafData) (g : sectionsOnClosedSubscheme p B I) (y : Y), ∃ (W : Y.Opens) (_ : y ∈ W) (b : Vanishing.H0 p B W), ∀ (z : I.subscheme) (hz : I.subschemeι z ∈ W) (j : (B.pull I.subschemeι).ι) (hj : z ∈ (B.pull I.subschemeι).U j), Vanishing.H0.germ j z (TopologicalSpace.Opens.mem_top z) hj g = (I.subschemeι.stalkMap z).hom (Vanishing.H0.germ (j PUnit.unit) (I.subschemeι z) hz (mem_pull.1 hj) b) := by
  intro k _ Y p B hB I g y
  obtain ⟨i, hi⟩ := exists_chart hB y
  obtain ⟨W, hyW, hWi⟩ := exists_affine hi
  obtain ⟨J, rfl⟩ : ∃ J : (B.pull I.subschemeι).ι, J PUnit.unit = i := ⟨fun _ => i, rfl⟩
  have hJ (z : I.subscheme) (hz : I.subschemeι z ∈ W.1) : z ∈ (B.pull I.subschemeι).U J :=
    mem_pull.2 (hWi hz)
  have hle : I.subschemeι ⁻¹ᵁ W.1 ≤ ⊤ ⊓ (B.pull I.subschemeι).U J :=
    fun z hz => ⟨trivial, hJ z hz⟩
  obtain ⟨a, ha⟩ := I.subschemeι_app_surjective W (resG I.subscheme hle (g.loc J))
  let b : H0 p B W.1 := (LB.chartEquiv hB (J PUnit.unit) hWi).symm a
  have hb (x : Y) (hx : x ∈ W.1) : germ (J PUnit.unit) x hx (hWi hx) b = ger x hx a := by
    conv_rhs =>
      rw [← (LB.chartEquiv hB (J PUnit.unit) hWi).apply_symm_apply a, LB.chartEquiv_apply,
        ger_resG]
    rfl
  refine ⟨W.1, hyW, b, fun z hz j hj => ?_⟩
  have h0 : germ J z (Opens.mem_top z) (hJ z hz) g =
      (I.subschemeι.stalkMap z).hom (germ (J PUnit.unit) (I.subschemeι z) hz (hWi hz) b) := by
    rw [hb, germ_apply, ← ger_resG hle z hz, ← ha]
    exact (Scheme.Hom.germ_stalkMap_apply _ _ z hz a).symm
  rw [germ_change j J z _ hj (hJ z hz), h0,
    germ_change (j PUnit.unit) (J PUnit.unit) _ hz (mem_pull.1 hj) (hWi hz), map_mul,
    tr_pull B I.subschemeι z hj (hJ z hz), Units.coe_map]
  rfl

end GlobalTheory.Vanishing
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemSectionConj
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT

theorem exists_mem_section_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (S : Set (Pl E)), IsSection S →
    ∀ u : Pl E, u ∉ S → ∃ w ∈ S, ∀ x : E, u.valuation E x = w.valuation E (IsCMField.complexConj E x) := by
  intro E _ _ _ S hS u hu
  obtain ⟨w, ⟨hwS, hwu⟩, -⟩ := hS u
  refine ⟨w, hwS, ?_⟩
  have hr : Module.finrank (maximalRealSubfield E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  rcases (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E) hr (IsCMField.complexConj_ne_one E) u w).1 hwu
    with h | h
  · exact absurd (h ▸ hwS) hu
  · intro x
    exact (h x).symm

end GlobalTheory.BCT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenCompactLevelSphericalOffTypesStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_openCompact_level_sphericalOffTypes : ∀ (D : D7) (V : HSp D) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V), ∃ K : Subgroup (GfC V), IsOpen (K : Set (GfC V)) ∧ IsCompact (K : Set (GfC V)) ∧ ∀ (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)), (∀ v, (μf v).IsHaarMeasure) → ∀ ff, IsTestFin T U μf ff → SphRest T U ff → IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff ∧ ∀ k ∈ K, ∀ g, finFn V ff (k * g) = finFn V ff g := by
  first | exact @GlobalTheory.TrMult.oneLevel | exact GlobalTheory.TrMult.oneLevel | (intros; apply GlobalTheory.TrMult.oneLevel <;> assumption)
end

