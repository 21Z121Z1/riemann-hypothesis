import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0004
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0010
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0090
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0095
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0109
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0108
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0114
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0127
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0077
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0038
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueOfIsAdicComplete
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0019
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0040
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0092
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0004
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0101
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0110
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0093
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0094
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0013
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfSectionRingEquiv
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfSectionRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecOfLbIso
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UU.EffSpecial

theorem exists_sec_of_lbIso {Y : Scheme.{0}} {A B : LB Y} (hA : A.IsLB) (hB : B.IsLB) (h : LBIso A B)
    (hs : ∃ s : LB.Sec B, ∃ j, s.f j ≠ 0) : ∃ s : LB.Sec A, ∃ j, s.f j ≠ 0 := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨t, b, hb⟩ := hs
  refine ⟨DVR.secOfIso t hu hA hB, ?_⟩
  by_contra hn
  push_neg at hn
  refine hb (fn_ext fun y hy => ?_)
  obtain ⟨a, ha⟩ := exists_chart hA y
  have e := (DVR.secOfIso_spec t hu hA hB a b).symm
  rw [hn a] at e
  have e' := (DVR.isoCand_rs u t a b le_rfl).symm.trans ((congrArg (DVR.rs le_rfl) (e.trans (map_zero _))).trans
    (map_zero _))
  have e'' := (Units.mul_right_eq_zero _).1 e'
  have hm : (𝟙 Y : Y ⟶ Y) y ∈ A.U a ⊓ B.U b := ⟨ha, hy⟩
  refine (gs_res (𝟙 Y) y inf_le_right hm _).symm.trans ((congrArg (gs (𝟙 Y) y _) e'').trans ?_)
  rw [gs_eq _ y _ hm, gs_eq _ y _ hy, map_zero, map_zero, map_zero, map_zero]

theorem lbIso_pw {Y : Scheme.{0}} {A B : LB Y} (h : LBIso A B) (t : ℤ) : LBIso (AbLaw.pw A t) (AbLaw.pw B t) := by
  obtain ⟨w, hw⟩ := h
  refine ⟨⟨fun p => w.s p ^ t⟩, fun p q => ?_⟩
  have e := congrArg (· ^ t) (hw p q)
  simp only [mul_zpow, ← map_zpow] at e
  refine e.trans (congrArg₂ (· * ·) ?_ rfl)
  exact (mul_zpow _ _ t).trans (congrArg₂ (· * ·) (map_zpow _ _ t).symm
    ((inv_zpow _ t).trans (congrArg (·⁻¹) (map_zpow _ _ t).symm)))

theorem ne_zero_of_mem {Y : Scheme.{0}} {M : LB Y} (s : LB.Sec M) {y : Y} (hy : y ∈ nonzeroLocus s) :
    ∃ j, s.f j ≠ 0 := by
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  refine ⟨j, fun e => ?_⟩
  rw [e, Scheme.basicOpen_zero] at hj
  exact hj

theorem isIntegral_special {V : Type} [CommRing V] [IsLocalRing V]
    (B : Over (Spec (CommRingCat.of (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1))))) [GrpObj B]
    (hB : IsAbelianScheme B) : IsIntegral B.left := by
  have hm : (IsLocalRing.maximalIdeal V ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  letI := Ideal.Quotient.field (IsLocalRing.maximalIdeal V ^ (0 + 1))
  have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ B.hom hB.smooth hB.geomConnected
  exact GeometricallyIntegral.geometrically_isIntegral (f := B.hom) _ _ _ (IsPullback.of_id_fst (f := B.hom))

theorem exists_sec_special : Laws → AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ t : Tower s, ∃ (k : ℕ) (σ : LB.Sec (pw (t.l 0).D.M.L.L k)), 1 ≤ k ∧ ∃ j, σ.f j ≠ 0 := by
  intro hL V _ _ _ A G _ _ s t
  have := s.cdvr.1
  have := s.semi.smooth
  have := s.semi.separated
  have := s.semi.quasiCompact
  have := s.semi.geomConnected
  obtain ⟨d, hd, n, a, ha, -⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy _ A.A A.L A.isLB).1 A.ample
  have hP := s.P.L.isLB

  have h₁ : ∃ σ : LB.Sec ((AbLaw.pw s.P.L.L d).pull (pullback.fst G.hom (jK V))), ∃ j, σ.f j ≠ 0 := by
    have iso : LBIso ((AbLaw.pw s.P.L.L d).pull (pullback.fst G.hom (jK V)))
        ((AbLaw.pw A.L d).pull s.gen.hom.left) := by
      rw [TrivLocus.pull_pw, TrivLocus.pull_pw]
      exact lbIso_pw (LBIso.symm ⟨s.wA, s.wA_gen⟩) d
    obtain ⟨w, hw⟩ := iso
    let y : ((Over.pullback (jK V)).obj G).left :=
      s.gen.inv.left (eSec A.A (IsLocalRing.closedPoint (FractionRing V)))
    have hy : s.gen.hom.left y ∈ ⨆ i, nonzeroLocus (a i) := by rw [ha]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    obtain ⟨⟨σ, hσ, -⟩, H⟩ := SecPullIso.section_pull _ _ s.gen.hom.left _ _ w (isLB_pw A.isLB d)
      (pull_isLB (isLB_pw hP d) _) hw (a i)
    exact ⟨σ, ne_zero_of_mem σ (y := y) (by rw [H σ hσ]; exact hi)⟩

  have h₂ := GlobalTheory.SpreadSec.exists_ne_zero_closed_fibre V G _ (isLB_pw hP d) h₁
  obtain ⟨w, hw⟩ := (t.l 0).lev
  have hM := (t.l 0).D.M.L.isLB
  have hE := (t.l 0).Pe.L.isLB
  have h₃ : ∃ σ : LB.Sec ((AbLaw.pw (t.l 0).D.M.L.L d).pull (t.l 0).Q.q.left), ∃ j, σ.f j ≠ 0 := by
    refine exists_sec_of_lbIso (pull_isLB (isLB_pw hM d) _) (pull_isLB (isLB_pw hP d) _) ?_ h₂
    rw [TrivLocus.pull_pw, TrivLocus.pull_pw]
    exact lbIso_pw (LBIso.trans (pull_isLB hM _) hE (pull_isLB hP _)
      (LBIso.symm ⟨_, (t.l 0).D.map.gen⟩) ⟨w, hw.gen⟩) d

  have hm : (IsLocalRing.maximalIdeal V ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  have : IsLocalRing (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)) :=
    letI := Ideal.Quotient.field (IsLocalRing.maximalIdeal V ^ (0 + 1))
    inferInstance
  obtain ⟨O, hO, hu, h₄⟩ := GlobalTheory.T.exists_section_primitive_twist_torus_extension hL.globalFns _ _ _ (t.l 0).Q _ (isLB_pw hM d) h₃
  have := isIntegral_special (t.l 0).Q.B (t.l 0).Q.isAb
  obtain ⟨σ, hσ⟩ := SymSec.exists_sec_sq _ (t.l 0).Q.B (t.l 0).D.M d O hO hu h₄
  exact ⟨2 * d, σ, by omega, hσ⟩

end GlobalTheory.UU.EffSpecial
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSymmetricVeryAmpleBy
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SymVeryAmple

open GlobalTheory.CechPic in

theorem exists_of_involution {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))
    (σ : X ⟶ X) (hσ : σ ≫ σ = 𝟙 X) (h : IsProjBy f) :
    ∃ (H : LB X) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB ∧ VeryAmpleBy f H s ∧
      Triv (LB.LinComb H (K := Fin 2) ![σ, 𝟙 X] ![1, -1]) := by
  obtain ⟨L, hL, m, s, hs⟩ := h
  have : IsProper f := isProper_of_veryAmpleBy hs
  have : IsIso σ := ⟨σ, hσ, hσ⟩
  have hA : IsAmpleLB L := isAmpleLB_of_veryAmpleBy hs
  have hP : IsAmpleLB (L.pull σ) := hA.pull_of_isAffineHom σ
  have hN : (tens L (L.pull σ)).IsLB := isLB_tens hL hP.isLB
  have hT : IsAmpleLB (tens L (L.pull σ)) := by
    refine hA.tensor hP hN ((cls_eq_zero_iff (LB.isLB_div (LB.isLB_div hN hL) hP.isLB)).1 ?_)
    rw [cls_div (LB.isLB_div hN hL) hP.isLB, cls_div hN hL, cls_tens hL hP.isLB]
    abel
  obtain ⟨n, -, M, t, ht⟩ := hT.exists_veryAmpleBy f
  have hH := isLB_lbPow hN n
  refine ⟨_, M, t, hH, ht, (cls_eq_zero_iff (LB.isLB_linComb hH _ _)).1 ?_⟩
  rw [cls_linComb hH, Fin.sum_univ_two, cls_lbPow hN, cls_tens hL hP.isLB, cls_pull hL]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, pull_id, map_nsmul, map_add, ← pull_comp, hσ]
  rw [add_comm (pull σ (cls L hL)), one_zsmul, neg_one_zsmul, Category.id_comp, add_neg_cancel]

theorem exists_symmetric_veryAmpleBy : ∀ (R : Type) [CommRing R] (B : Over (Spec (CommRingCat.of R))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → IsProjBy B.hom → ∃ (H : LB B.left) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB ∧ VeryAmpleBy B.hom H s ∧ Triv (LB.LinComb H (K := Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1]) := by
  intro R _ B _ _ _ h
  refine exists_of_involution B.hom _ ?_ h
  rw [← Over.comp_left, GrpObj.inv_comp_inv, Over.id_left]

end GlobalTheory.SymVeryAmple
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProperAndRelAmpleLPow
section
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem isProper_and_relAmple_lPow :
    ∀ (F : Type) [CommRing F] (S : Scheme.{0}) (P : PolAV S) (t : Spec (CommRingCat.of F) ⟶ S) [IsLocalRing F] (N : ℕ), 1 ≤ N → IsProper (fst (Over.mk t) P.A).left ∧ RelAmple (S := Spec (CommRingCat.of F)) (Over.mk (fst (Over.mk t) P.A).left) (LPow P.A P.L (N : ℤ) (Over.mk t)) := by
  intro F _ S P t _ N hN
  have hP := P.isAb.proper
  have H : IsPullback (snd (Over.mk t) P.A).left (fst (Over.mk t) P.A).left P.A.hom t :=
    (IsPullback.of_hasPullback t P.A.hom).flip
  have hp : IsProper (fst (Over.mk t) P.A).left := MorphismProperty.of_isPullback (P := @IsProper) H hP
  refine ⟨hp, ?_⟩
  have hp' : IsProper (Over.mk (X := Spec (CommRingCat.of F)) (fst (Over.mk t) P.A).left).hom := hp
  have hL := LB.isLB_pull P.isLB (snd (Over.mk t) P.A).left
  have hM : (LPow P.A P.L (N : ℤ) (Over.mk t)).IsLB := LB.isLB_linComb P.isLB _ _
  have h₁ := (relAmple_iff_isAmpleLB_of_isAffine
    (Over.mk (X := Spec (CommRingCat.of F)) (fst (Over.mk t) P.A).left) hL).1
    (AmpleBaseChange.relAmple_of_isPullback P.isLB P.ample H)
  refine (relAmple_iff_isAmpleLB_of_isAffine
    (Over.mk (X := Spec (CommRingCat.of F)) (fst (Over.mk t) P.A).left) hM).2
    (((isAmpleLB_pow_iff hL hN).2 h₁).of_lbIso hM ?_)
  exact LBIso.chartPull (CoprimeTorsion.chartPullLPow P.A P.L (Over.mk t) N) (chartPullPowPull P.L _ N)
    (lbIso_refl (isLB_lbPow P.isLB N))

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PairingNondegenerate
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section
namespace GlobalTheory.UU.SpecialPairing

theorem card_map {A₀ A A' : Type} [CommGroup A₀] [CommGroup A] [CommGroup A'] (r : A →* A₀) (j : A →* A') (N : ℕ)
    (ri : ∀ y y', y ^ N = 1 → y' ^ N = 1 → r y = r y' → y = y') (rs : ∀ x, x ^ N = 1 → ∃ y, y ^ N = 1 ∧ r y = x)
    (hj : Function.Injective j) (K : Subgroup A₀) :
    Nat.card (((powMonoidHom N).ker ⊓ K.comap r).map j) = Nat.card {x : A₀ // x ^ N = 1 ∧ x ∈ K} := by
  rw [Subgroup.card_map_of_injective hj]
  refine Nat.card_congr (Equiv.ofBijective (fun y => ⟨r y.1, by rw [← map_pow, show y.1 ^ N = 1 from y.2.1, map_one],
    y.2.2⟩) ⟨fun y y' h => Subtype.ext (ri _ _ y.2.1 y'.2.1 (congrArg Subtype.val h)), fun x => ?_⟩)
  obtain ⟨y, hy, e⟩ := rs x.1 x.2.1
  exact ⟨⟨y, hy, show r y ∈ K from e ▸ x.2.2⟩, Subtype.ext e⟩

theorem core {A₀ A A' B : Type} [CommGroup A₀] [CommGroup A] [CommGroup A'] [CommGroup B] (r : A →* A₀)
    (j : A →* A') (q : A₀ →* B) (N M : ℕ) (P' : A' → A' → Prop) (P : B → B → Prop)
    (ri : ∀ y y', y ^ N = 1 → y' ^ N = 1 → r y = r y' → y = y') (rs : ∀ x, x ^ N = 1 → ∃ y, y ^ N = 1 ∧ r y = x)
    (hj : Function.Injective j) (qs : ∀ b, b ^ N = 1 → ∃ x, x ^ N = 1 ∧ q x = b)
    (hP : ∀ y y', y ^ N = 1 → y' ^ N = 1 → P (q (r y)) (q (r y')) → P' (j y) (j y'))
    (h1 : ∀ b, b ^ N = 1 → P 1 b)
    (hc : Nat.card {x : A₀ // x ^ N = 1 ∧ q x = 1} * Nat.card {x : A₀ // x ^ N = 1} = M)
    (rad : ∀ T H : Subgroup A', (∀ x ∈ T, x ^ N = 1) → (∀ x ∈ H, x ^ N = 1) → Nat.card T * Nat.card H = M →
      (∀ x ∈ T, ∀ y ∈ H, P' x y) → ∀ x, x ^ N = 1 → (∀ y ∈ H, P' x y) → x ∈ T)
    (b : B) (hb : b ^ N = 1) (h : ∀ b', b' ^ N = 1 → P b b') : b = 1 := by
  have tq : ∀ y : A, y ^ N = 1 → q (r y) ^ N = 1 := fun y hy => by rw [← map_pow, ← map_pow, hy, map_one, map_one]
  have tj : ∀ y : A, y ^ N = 1 → j y ^ N = 1 := fun y hy => by rw [← map_pow, hy, map_one]
  obtain ⟨x, hx, rfl⟩ := qs b hb
  obtain ⟨y, hy, rfl⟩ := rs x hx
  obtain ⟨y', hy', e⟩ := rad (((powMonoidHom N).ker ⊓ q.ker.comap r).map j)
    (((powMonoidHom N).ker ⊓ (⊤ : Subgroup A₀).comap r).map j)
    (by rintro _ ⟨z, hz, rfl⟩; exact tj z hz.1) (by rintro _ ⟨z, hz, rfl⟩; exact tj z hz.1)
    (by
      rw [card_map r j N ri rs hj, card_map r j N ri rs hj, ← hc]
      simp only [Subgroup.mem_top, and_true, MonoidHom.mem_ker])
    (by
      rintro _ ⟨z, hz, rfl⟩ _ ⟨z', hz', rfl⟩
      refine hP z z' hz.1 hz'.1 ?_
      rw [show q (r z) = 1 from hz.2]
      exact h1 _ (tq _ hz'.1))
    (j y) (tj y hy) (by
      rintro _ ⟨z', hz', rfl⟩
      exact hP y z' hy hz'.1 (h _ (tq _ hz'.1)))
  obtain rfl := hj e
  exact hy'.2

theorem exists_embedding (V W : Type) [CommRing V] [IsDomain V] [CommRing W] [IsDomain W] [Algebra V W]
    [Module.Finite V W] (h : Function.Injective (algebraMap V W)) :
    ∃ φ : W →+* AlgebraicClosure (FractionRing V), Function.Injective φ ∧ φ.comp (algebraMap V W) =
      (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp (algebraMap V (FractionRing V)) := by
  have i : Function.Injective (algebraMap V (AlgebraicClosure (FractionRing V))) := by
    rw [IsScalarTower.algebraMap_eq V (FractionRing V)]
    exact (algebraMap (FractionRing V) _).injective.comp (IsFractionRing.injective V (FractionRing V))
  have : FaithfulSMul V W := (faithfulSMul_iff_algebraMap_injective _ _).2 h
  have : FaithfulSMul V (AlgebraicClosure (FractionRing V)) := (faithfulSMul_iff_algebraMap_injective _ _).2 i
  let φ : W →ₐ[V] AlgebraicClosure (FractionRing V) := IsAlgClosed.lift
  refine ⟨φ.toRingHom, ?_, ?_⟩
  · rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := V) ?_
    rw [RingHom.comap_ker, show φ.toRingHom.comp (algebraMap V W) = algebraMap V _ from φ.comp_algebraMap]
    exact (RingHom.injective_iff_ker_eq_bot _).1 i
  · rw [← IsScalarTower.algebraMap_eq]; exact φ.comp_algebraMap

theorem torsion_ext (W : Type) [CommRing W] [IsLocalRing W] [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (p : Spec (CommRingCat.of W) ⟶ S) (N : ℕ)
    (hN : IsUnit (N : W)) {Ω : Type} [Field Ω] (f : W →+* Ω) [IsLocalHom f] (y y' : Over.mk p ⟶ G) (hy : y ^ N = 1)
    (hy' : y' ^ N = 1) (e : Spec.map (CommRingCat.ofHom f) ≫ y.left = Spec.map (CommRingCat.ofHom f) ≫ y'.left) :
    y = y' := by
  have := GlobalTheory.TorsionSeparable.epi_specMap (IsLocalRing.ResidueField.lift f)
  rw [← IsLocalRing.ResidueField.lift_comp_residue f, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
    Category.assoc, cancel_epi] at e
  let ρ : Over.mk (Spec.map (CommRingCat.ofHom (IsLocalRing.residue W)) ≫ p) ⟶ Over.mk p :=
    Over.homMk (Spec.map (CommRingCat.ofHom (IsLocalRing.residue W))) rfl
  exact (GlobalTheory.existsUnique_torsion_lift W S G p N hN (ρ ≫ y)
    (by rw [← MonObj.comp_pow, hy, MonObj.comp_one])).unique ⟨hy, rfl⟩ ⟨hy', e.symm⟩

theorem toBase_bijective {S S' : Scheme.{0}} (G : Over S) (f : S' ⟶ S) (T : Over S') :
    Function.Bijective (toBase (A := G) (A' := (Over.pullback f).obj G) (g := pullback.fst G.hom f)
      pullback.condition (T := T)) :=
  ⟨fun x y h => Over.OverMorphism.ext (pullback.hom_ext (congrArg (fun z => z.left) h)
    ((Over.w x).trans (Over.w y).symm)), fun x =>
    ⟨Over.homMk (pullback.lift x.left T.hom (Over.w x)) (pullback.lift_snd _ _ _),
      Over.OverMorphism.ext (pullback.lift_fst _ _ _)⟩⟩

set_option maxHeartbeats 800000 in

theorem pairing_nondegenerate : (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (n : k) ≠ 0 → Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} = n ^ (2 * g)) → Laws → AllSet fun {V} _ _ _ {_} {_} _ _ s => ∀ (t : Tower s) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (p : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)))) (N : ℕ), IsUnit (N : V) → ∀ x : Over.mk p ⟶ (t.l 0).Q.B, x ^ N = 1 → (∀ y : Over.mk p ⟶ (t.l 0).Q.B, y ^ N = 1 → CubWeil (t.l 0).D.M.c N x y 1) → x = 1 := by
  intro hAb hL V _ _ _ A G _ _ s t Ω _ _ p N hN
  obtain ⟨dvr, cpl, -⟩ := s.cdvr
  have := s.semi.smooth
  have := s.semi.separated
  have := (t.l 0).Q.q_hom
  obtain ⟨φ₀, rfl⟩ : ∃ φ₀ : (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)) →+* Ω, p = Spec.map (CommRingCat.ofHom φ₀) :=
    ⟨(Spec.preimage p).hom, (Spec.map_preimage p).symm⟩
  let f : V →+* Ω := φ₀.comp (Ideal.Quotient.mk _)
  have hf : IsLocalHom f := ⟨fun a ha => by
    by_contra h
    have : Ideal.Quotient.mk (IsLocalRing.maximalIdeal V ^ (0 + 1)) a = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (by rw [zero_add, pow_one]; exact h)
    exact ha.ne_zero (by rw [RingHom.comp_apply, this, map_zero])⟩
  have hNΩ : (N : Ω) ≠ 0 := by simpa using (hN.map f).ne_zero
  have hN0 : N ≠ 0 := by rintro rfl; simp at hNΩ
  obtain ⟨g', hg'⟩ : ∃ g', SmoothOfRelativeDimension g' (t.l 0).Q.B.hom := by
    have : Nontrivial (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)) := φ₀.domain_nontrivial
    have : IsLocalRing (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)) :=
      IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
    exact GlobalTheory.AbelianDim.exists_relDim _ _ (t.l 0).Q.isAb
  have hd := (GlobalTheory.UU.Tower.dim_eq_add_finrank V A G s t g').1 hg'
  obtain ⟨c₁, c₂⟩ := torusQuotient_card_torsion _ _ _ (t.l 0).Q Ω (Spec.map (CommRingCat.ofHom φ₀)) N hNΩ
  rw [GlobalTheory.card_torsion_geometricPoint_of_field hAb _ _ (t.l 0).Q.isAb g' hg' Ω _ N hNΩ] at c₂
  let T₀ : Over (Spec (CommRingCat.of (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)))) :=
    Over.mk (Spec.map (CommRingCat.ofHom φ₀))
  have hpf : Spec.map (CommRingCat.ofHom f) = T₀.hom ≫ thick V (IsLocalRing.maximalIdeal V) 0 := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp]; rfl
  let β : (T₀ ⟶ thickObj V (IsLocalRing.maximalIdeal V) 0 G) ≃*
      (Over.mk (T₀.hom ≫ thick V (IsLocalRing.maximalIdeal V) 0) ⟶ G) :=
    MulEquiv.ofBijective (toBaseHom (toBase_mul_pullback G _) T₀) (toBase_bijective G _ T₀)
  have hβ : ∀ x, (β x).left = x.left ≫ (fstG _ 0 G).left := fun _ => rfl
  let ι₀ : Over.mk (Spec.map (CommRingCat.ofHom f)) ⟶ Over.mk (T₀.hom ≫ thick V (IsLocalRing.maximalIdeal V) 0) :=
    Over.homMk (𝟙 _) ((Category.id_comp _).trans hpf.symm)
  have fin : Finite {x : T₀ ⟶ thickObj V (IsLocalRing.maximalIdeal V) 0 G // x ^ N = 1} :=
    Nat.finite_of_card_ne_zero (by rw [c₂]; positivity)
  have fin' := (show Set.Finite {x : T₀ ⟶ thickObj V (IsLocalRing.maximalIdeal V) 0 G | x ^ N = 1} from fin).image
    (fun x => ι₀ ≫ β x)
  obtain ⟨W, _, _, _, _, _, f', _, inj, _, _, hf', lifts⟩ := GlobalTheory.exists_finite_extension_torsion_lift hL.unramExt V G N
    hN Ω f hf fin'.toFinset (by
      intro x hx
      obtain ⟨u, hu, rfl⟩ := fin'.mem_toFinset.1 hx
      show (ι₀ ≫ β u) ^ N = 1
      rw [← MonObj.comp_pow, ← map_pow, show u ^ N = 1 from hu, map_one, MonObj.comp_one])
  obtain ⟨φ, φi, hφ⟩ := exists_embedding V W inj
  let TW : Over (Spec (CommRingCat.of V)) := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W)))
  let ρ : Over.mk (T₀.hom ≫ thick V (IsLocalRing.maximalIdeal V) 0) ⟶ TW :=
    Over.homMk (Spec.map (CommRingCat.ofHom f')) (by
      refine Eq.trans ?_ hpf
      rw [← hf', CommRingCat.ofHom_comp, Spec.map_comp]; rfl)
  let σ : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ TW :=
    Over.homMk (Spec.map (CommRingCat.ofHom φ)) (by
      have e := congrArg (fun z => Spec.map (CommRingCat.ofHom z)) hφ
      simp only [CommRingCat.ofHom_comp, Spec.map_comp] at e
      exact e)
  let r : (TW ⟶ G) →* (T₀ ⟶ thickObj V (IsLocalRing.maximalIdeal V) 0 G) := β.symm.toMonoidHom.comp (preHom ρ)
  have hr : ∀ y, (r y).left ≫ (fstG _ 0 G).left = Spec.map (CommRingCat.ofHom f') ≫ y.left := fun y =>
    (hβ _).symm.trans (congrArg (fun z => z.left) (β.apply_symm_apply (ρ ≫ y)))
  let q : (T₀ ⟶ thickObj V (IsLocalRing.maximalIdeal V) 0 G) →* (T₀ ⟶ (t.l 0).Q.B) :=
    MonoidHom.mk' (· ≫ (t.l 0).Q.q) fun x y => MonObj.mul_comp x y _
  refine core r (preHom σ) q N (N ^ (2 * A.g)) (fun x y => CubWeil s.P.c N x y 1)
    (fun x y => CubWeil (t.l 0).D.M.c N x y 1) (fun y y' hy hy' e => ?_) (fun x hx => ?_) (fun y y' e => ?_)
    ?_ (fun y y' hy hy' h => ?_) (fun b hb => cubWeil_one_left _ hb) ?_
    (mem_of_cubWeil_orthogonal hL V A G s _ N (Nat.one_le_iff_ne_zero.2 hN0))
  · refine torsion_ext W G _ N (by simpa using hN.map (algebraMap V W)) f' y y' hy hy' ?_
    rw [← hr, ← hr, e]
  · obtain ⟨y, hy, e⟩ := lifts (ι₀ ≫ β x) (fin'.mem_toFinset.2 ⟨x, hx, rfl⟩)
    refine ⟨y, hy, β.injective (Over.OverMorphism.ext ?_)⟩
    have e' : (ι₀ ≫ β x).left = (β x).left := Category.id_comp _
    rw [hβ, hr y, e, e']
  · exact GlobalTheory.over_points_ext_of_injective _ G W _ φ φi _ y y' (congrArg (fun z => z.left) e)
  · refine (torusQuotient_points_lift _ _ _ (t.l 0).Q Ω _).2 N fun a => ?_
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq a.val (Nat.pos_of_ne_zero hN0)
    have hz0 : z ≠ 0 := by rintro rfl; exact a.ne_zero (by rw [← hz, zero_pow hN0])
    exact ⟨Units.mk0 z hz0, Units.ext hz⟩
  · have := ((cubWeil_one_iff_closedFibre V A G s t W Ω f' inferInstance _ N hN y y' (r y) (r y') hy hy' (hr y) (hr y')).2 h).comp σ
    rwa [map_one] at this
  · have e : N ^ (2 * A.g) = N ^ Module.finrank ℤ s.X * (N ^ Module.finrank ℤ s.X * N ^ (2 * g')) := by
      rw [hd]; ring
    rw [e]
    exact congrArg₂ (· * ·) ((Nat.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)).trans c₁) c₂

end GlobalTheory.UU.SpecialPairing
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PolAVNonzeroLocusCoverAffine
section
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem polAV_nonzeroLocus_cover_affine (hA : AmpleSt) {S : Scheme.{0}} [IsAffine S] [IsLocallyNoetherian S]
    (P : PolAV S) {N : ℕ} (hN : 4 ≤ N) :
    (∀ x : P.A.left, ∃ s : H0 P.L N, x ∈ nonzeroLocus s) ∧ ∀ s : H0 P.L N, IsAffineOpen (nonzeroLocus s) := by
  classical
  have := P.isAb.proper
  let := P.grp
  obtain ⟨M, s, hs⟩ := AmpleSpan.exists_embedsBy_of_isPullback P.A P.isLB (hA S P N hN).2 (isAffineOpen_top S)
    (φ := 𝟙 P.A.left) (f' := P.A.hom) (g := 𝟙 S ≫ S.topIso.inv)
    (by rw [AmpleSpan.comp_topIso_inv_ι]; exact IsPullback.of_id_fst) (K := Fin 1) (ε := fun _ => (N : ℤ)) (by simp)
  refine ⟨fun x => ?_, fun t => (hs.affine_and_surjective (t := s) (fun j => ⟨Pi.single j 1, fun k => ?_⟩) t).1⟩
  · obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hs.1.ge (Set.mem_univ x))
    exact ⟨s i, hi⟩
  · rw [Finset.sum_eq_single j]
    · rw [Pi.single_eq_same, map_one, _root_.one_mul]
    · intro l _ hl
      rw [Pi.single_eq_of_ne hl, map_zero, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ j) h

theorem exists_iso_of_polAV_sectionRing : Laws → ∀ (K : Type) [Field K] (P P' : PolAV (Spec (CommRingCat.of K))), ∀ θ : ∀ n : ℕ, 1 ≤ n → (H0 P'.L n ≃ H0 P.L n), (∀ (n : ℕ) (hn : 1 ≤ n) (c : K) (a b d : H0 P'.L n), (∀ j, d.f j = a.f j + resTop _ (scal P'.A.hom c) * b.f j) → ∀ j, (θ n hn d).f j = (θ n hn a).f j + resTop _ (scal P.A.hom c) * (θ n hn b).f j) → (∀ (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (a : H0 P'.L n) (b : H0 P'.L m) (d : H0 P'.L (n + m)), (∀ j : Fin 1 → P'.L.ι, (show Γ(P'.A.left, LB.wchart P'.L (fun _ : Fin 1 => 𝟙 P'.A.left) j) from d.f j) = (show Γ(P'.A.left, LB.wchart P'.L (fun _ : Fin 1 => 𝟙 P'.A.left) j) from a.f j) * (show Γ(P'.A.left, LB.wchart P'.L (fun _ : Fin 1 => 𝟙 P'.A.left) j) from b.f j)) → ∀ j : Fin 1 → P.L.ι, (show Γ(P.A.left, LB.wchart P.L (fun _ : Fin 1 => 𝟙 P.A.left) j) from (θ (n + m) (hn.trans (Nat.le_add_right n m)) d).f j) = (show Γ(P.A.left, LB.wchart P.L (fun _ : Fin 1 => 𝟙 P.A.left) j) from (θ n hn a).f j) * (show Γ(P.A.left, LB.wchart P.L (fun _ : Fin 1 => 𝟙 P.A.left) j) from (θ m hm b).f j)) → ∃ Φ₀ : P'.A ≅ P.A, ∃ w : LB.Iso P'.L (P.L.pull Φ₀.hom.left), w.IsGen ∧ ∀ (n : ℕ) (hn : 1 ≤ n) (a : H0 P'.L n), (∀ (Z : Scheme.{0}) (r : Z ⟶ P'.A.left) (z : Z) (p : Fin 1 → P.L.ι) (q : Fin 1 → P'.L.ι), (∀ κ, (Φ₀.hom.left) ((fun _ : Fin 1 => 𝟙 P'.A.left) κ (r z)) ∈ P.L.U (p κ)) → (∀ κ, (fun _ : Fin 1 => 𝟙 P'.A.left) κ (r z) ∈ P'.L.U (q κ)) → Geo.Tor.gs (r ≫ Φ₀.hom.left) z (LB.wchart P.L (fun _ : Fin 1 => 𝟙 P.A.left) p) ((θ n hn a).f p) = (∏ κ, Geo.Tor.gw w (r ≫ (fun _ : Fin 1 => 𝟙 P'.A.left) κ) z (p κ) (q κ) ^ (fun _ : Fin 1 => (n : ℤ)) κ).val * Geo.Tor.gs r z (LB.wchart P'.L (fun _ : Fin 1 => 𝟙 P'.A.left) q) ((a).f q)) := by
  intro hL K _ P P' θ hlin hmul
  have := P.isAb.proper
  have := P'.isAb.proper
  have : CompactSpace P.A.left := QuasiCompact.compactSpace_of_compactSpace P.A.hom
  have : CompactSpace P'.A.left := QuasiCompact.compactSpace_of_compactSpace P'.A.hom
  have : QuasiSeparatedSpace P.A.left := quasiSeparatedSpace_of_quasiSeparated P.A.hom
  have : QuasiSeparatedSpace P'.A.left := quasiSeparatedSpace_of_quasiSeparated P'.A.hom
  obtain ⟨c, a⟩ := polAV_nonzeroLocus_cover_affine hL.ample P (le_refl 4)
  obtain ⟨c', a'⟩ := polAV_nonzeroLocus_cover_affine hL.ample P' (le_refl 4)
  obtain ⟨c₅, -⟩ := polAV_nonzeroLocus_cover_affine hL.ample P' (N := 4 + 1) (by norm_num)
  obtain ⟨Φ, hΦ⟩ := exists_iso_of_sectionRing_equiv K P.A P'.A P.L P'.L P.isLB P'.isLB θ hlin hmul
    ⟨4, by norm_num, H0 P'.L 4, id, top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 (c' x),
      top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 (by
        obtain ⟨s, hs⟩ := c x
        obtain ⟨t, rfl⟩ := (θ 4 (by norm_num)).surjective s
        exact ⟨t, hs⟩), fun i => ⟨a' _, a _⟩⟩
  refine ⟨Φ, exists_iso_of_sectionRing K P.A P'.A P.L P'.L P.isLB P'.isLB θ hlin hmul Φ.hom.left hΦ fun x => ?_⟩
  obtain ⟨s, hs⟩ := c' x
  obtain ⟨t, ht⟩ := c₅ x
  exact ⟨4, by norm_num, s, t, hs, ht⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SmallTorusPointKeepingRatiosIsZeroStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smallTorusPoint_keeping_ratios_isZero : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllDV fun {V} _ _ _ {ϖ} hϖ D Q {F} _ _ {v} hv => ∀ (k : ℕ), 1 ≤ k → ∀ (d o : GtPtF D.toPre F) (l : D.toPre.X → ℚ), o.IsZero → GtV hϖ hv d l → (∀ m, |l m| ≤ Q m) → (∀ (n j : ℕ), 1 ≤ n → j = k * n → ∀ (w₁ : Frm D.toPre F j o.b), FrmOne w₁ → ∃ w : Frm D.toPre F j d.b, w.IsGen ∧ ∀ S₁ S₂ : Fam D.toPre F j, ¬ SumV v (coef S₂ o w₁) 0 → ∀ α, SumV v (fun χ => coef S₁ d w χ * coef S₂ o w₁ (α - χ) - coef S₂ d w χ * coef S₁ o w₁ (α - χ)) 0) → d.IsZero := by
  first | exact @GlobalTheory.UT.SmallZero.main | exact GlobalTheory.UT.SmallZero.main | (intros; apply GlobalTheory.UT.SmallZero.main <;> assumption)
end

