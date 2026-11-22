import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2838
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCAndCoordCorrespond
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsLocalRingQuotientPow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0084
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2554
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2643
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2804
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAbelianSchemeAway
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RangeSubsetAbLocusOfIsProper
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharactersRestrictLinearToTraitUniformisation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0577
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0562
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0021
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0085
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2800
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2829
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2801
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0183
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHormanderPeakOrthonormalFrameL2Bound
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsTauZeroNonzeroAll
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2114
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KronHolPsiStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CuspStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0038
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0037
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0026
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1528
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralGaugeFiniteExtension
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorTransportLinCombIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.GenTransport

theorem exists_unflat {X X' Y : Scheme.{0}} {L : LB X} {J K : Type} [Fintype J] [Fintype K]
    (F : J → (X' ⟶ X)) (ε : J → ℤ) (ψ : K → (Y ⟶ X')) (δ : K → ℤ)
    (T : LB.Gen (LB.LinComb (LB.LinComb L F ε) ψ δ)) (hT : T.IsGen) :
    ∃ t : LB.Gen (LB.LinComb L (K := K × J) (fun p => ψ p.1 ≫ F p.2) (fun p => δ p.1 * ε p.2)), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (I : (Z ⟶ X) → L.ι), Good L z I →
        val t r z I = val T r z (fun χ j => I (χ ≫ F j)) := by
  have le : ∀ p : K × J → L.ι, LB.wchart L (K := K × J) (fun p => ψ p.1 ≫ F p.2) p ≤
      LB.wchart (LB.LinComb L F ε) ψ (fun k j => p (k, j)) := fun p y hy =>
    Set.mem_iInter.2 fun k => by
      have h1 : ψ k y ∈ LB.wchart L F (fun j => p (k, j)) :=
        Set.mem_iInter.2 fun j => Set.mem_iInter.1 hy (k, j)
      exact h1
  let t : LB.Gen (LB.LinComb L (K := K × J) (fun p => ψ p.1 ≫ F p.2) (fun p => δ p.1 * ε p.2)) :=
    ⟨fun p => res (le p) (T.s fun k j => p (k, j))⟩
  refine ⟨t, isGen_of_gm _ fun y p q hp hq => ?_, fun Z r z I hI => ?_⟩
  · refine (gm_res _ y (le p) hp _).trans (Eq.trans ?_ (congrArg _ (gm_res _ y (le q) hq _)).symm)
    refine (gen_trans hT (𝟙 Y) y (le p hp) (le q hq)).trans (congrArg (· * _) ?_)
    refine (Finset.prod_congr rfl fun k _ => congrArg (· ^ δ k)
      (gm_linComb L F ε (𝟙 Y ≫ ψ k) y (fun j => p (k, j)) (fun j => q (k, j)) (Set.mem_iInter.1 (le p hp) k)
        (Set.mem_iInter.1 (le q hq) k))).trans ?_
    simp only [trF, Fintype.prod_prod_type, ← Finset.prod_zpow, ← zpow_mul, Category.assoc, mul_comm]
  · refine (gm_res r z (le _) (hI.mem (fun p : K × J => ψ p.1 ≫ F p.2) r) _).trans ?_
    exact (val_of T r z (fun χ j => I (χ ≫ F j)) _ fun k => funext fun j => congrArg I (Category.assoc _ _ _)).symm

theorem exists_transport : ∀ {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {J K : Type} [Fintype J] [Fintype K], L.IsLB → L'.IsLB → ∀ (pr : J → (X' ⟶ X)) (ε : J → ℤ) (w : LB.Iso L' (LB.LinComb L pr ε)), w.IsGen → ∀ (φ' : K → (Y ⟶ X')) (δ : K → ℤ) (a : LB.Gen (LB.LinComb L' φ' δ)), a.IsGen → ∃ t : LB.Gen (LB.LinComb L (fun p : K × J => φ' p.1 ≫ pr p.2) (fun p => δ p.1 * ε p.2)), t.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (I : (Z ⟶ X) → L.ι) (I' : (Z ⟶ X') → L'.ι), Good L z I → Good L' z I' → val t r z I = (∏ k, gv w (r ≫ φ' k) z (fun j => I ((r ≫ φ' k) ≫ pr j)) (I' (r ≫ φ' k)) ^ δ k) * val a r z I' := by
  intro X X' Y L L' J K _ _ hL hL' pr ε w hw φ' δ a ha
  obtain ⟨T, hT, hv⟩ := GlobalTheory.WtTower.exists_gen_of_iso (LB.isLB_linComb hL' φ' δ)
    (LB.isLB_linComb (LB.isLB_linComb hL pr ε) φ' δ) (LB.linCombIso w φ' δ) (DVR.linCombIso_isGen w hw _ _) a ha
  obtain ⟨t, ht, hv'⟩ := exists_unflat pr ε φ' δ T hT
  refine ⟨t, ht, fun Z r z I I' hI hI' => (hv' Z r z I hI).trans ?_⟩
  have hI'' : Good (LB.LinComb L pr ε) z (fun χ j => I (χ ≫ pr j)) := fun χ => hI.mem pr χ
  refine (hv Z r z _ (fun k => I' (r ≫ φ' k)) (hI''.mem φ' r) (hI'.mem φ' r)).trans (congrArg₂ (· * ·) ?_ rfl)
  exact GlobalTheory.WtTower.gm_linCombIso w φ' δ (fun k j => I ((r ≫ φ' k) ≫ pr j), fun k => I' (r ≫ φ' k)) r z
    ⟨hI''.mem φ' r, hI'.mem φ' r⟩

end GlobalTheory.Mum.GenTransport

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorTransportMumfordBundleIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.GenTransport

section Nest

variable {X X' Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (X' ⟶ X)} {ε : K → ℤ} {p : Y ⟶ X'}

theorem trF_nest (r : Z ⟶ Y) (z : Z) (j j' : PUnit.{1} → K → L.ι)
    (hj : (r ≫ p) z ∈ LB.wchart L φ (j PUnit.unit)) (hj' : (r ≫ p) z ∈ LB.wchart L φ (j' PUnit.unit)) :
    trF (L := LB.LinComb L φ ε) (fun _ : PUnit.{1} => p) (fun _ => -1) r z j j' =
      trF (fun k => p ≫ φ k) (fun k => - ε k) r z (j PUnit.unit) (j' PUnit.unit) := by
  unfold trF
  refine (Fintype.prod_unique _).trans ?_
  refine (zpow_neg_one _).trans ?_
  refine (congrArg (·⁻¹) (gm_linComb L φ ε (r ≫ p) z _ _ hj hj')).trans ?_
  simp only [← Finset.prod_inv_distrib, zpow_neg, Category.assoc]

theorem mem_nest {y : Y} {j : PUnit.{1} → K → L.ι} :
    y ∈ LB.wchart (LB.LinComb L φ ε) (fun _ : PUnit.{1} => p) j ↔
      y ∈ LB.wchart L (fun k => p ≫ φ k) (j PUnit.unit) :=
  ⟨fun h => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (Set.mem_iInter.1 h PUnit.unit) k,
    fun h => Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun k => Set.mem_iInter.1 h k⟩

theorem exists_nest (t : LB.Gen (LB.LinComb L (fun k => p ≫ φ k) (fun k => - ε k))) (ht : t.IsGen) :
    ∃ a : LB.Gen (LB.LinComb (LB.LinComb L φ ε) (fun _ : PUnit.{1} => p) (fun _ => -1)), a.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : K → L.ι), r z ∈ LB.wchart L (fun k => p ≫ φ k) j →
        gm r z (LB.wchart (LB.LinComb L φ ε) (fun _ : PUnit.{1} => p) (fun _ => j)) (a.s fun _ => j) =
          gm r z (LB.wchart L (fun k => p ≫ φ k) j) (t.s j) := by
  refine ⟨⟨fun j => res (fun _ hy => mem_nest.1 hy) (t.s (j PUnit.unit))⟩, isGen_of_gm _ fun y j j' hj hj' => ?_,
    fun Z r z j hj => gm_res r z _ (mem_nest.2 hj) _⟩
  refine (gm_res _ y _ hj _).trans ((gen_trans ht (𝟙 Y) y (mem_nest.1 hj) (mem_nest.1 hj')).trans
    (congrArg₂ (· * ·) (trF_nest (𝟙 Y) y j j' (Set.mem_iInter.1 hj PUnit.unit)
      (Set.mem_iInter.1 hj' PUnit.unit)).symm (gm_res _ y _ hj' _).symm))

theorem exists_unnest (a : LB.Gen (LB.LinComb (LB.LinComb L φ ε) (fun _ : PUnit.{1} => p) (fun _ => -1)))
    (ha : a.IsGen) : ∃ t : LB.Gen (LB.LinComb L (fun k => p ≫ φ k) (fun k => - ε k)), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : K → L.ι), r z ∈ LB.wchart L (fun k => p ≫ φ k) j →
        gm r z (LB.wchart L (fun k => p ≫ φ k) j) (t.s j) =
          gm r z (LB.wchart (LB.LinComb L φ ε) (fun _ : PUnit.{1} => p) (fun _ => j)) (a.s fun _ => j) := by
  have mk : ∀ {y : Y} {j : K → L.ι}, y ∈ LB.wchart L (fun k => p ≫ φ k) j →
      y ∈ LB.wchart (LB.LinComb L φ ε) (fun _ : PUnit.{1} => p) (fun _ => j) := fun h => mem_nest.2 h
  refine ⟨⟨fun j => res (fun _ hy => mk hy) (a.s fun _ => j)⟩, isGen_of_gm _ fun y j j' hj hj' => ?_,
    fun Z r z j hj => gm_res r z _ hj _⟩
  refine (gm_res _ y _ hj _).trans ((gen_trans ha (𝟙 Y) y (mk hj) (mk hj')).trans
    (congrArg₂ (· * ·) (trF_nest (𝟙 Y) y (fun _ => j) (fun _ => j') (Set.mem_iInter.1 (mk hj) PUnit.unit)
      (Set.mem_iInter.1 (mk hj') PUnit.unit)) (gm_res _ y _ hj' _).symm))

end Nest

open GlobalTheory.PrimCocycle in

theorem prod_neg_lam {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] {T : Over S} (x y : T ⟶ B)
    {U : Type} [CommGroup U] (k : (T.left ⟶ B.left) → U) :
    ∏ I, k ((lift x y).left ≫ lamφ B I) ^ (- lamε I) = ∏ i, k (lamPts x y i) ^ negε i := by
  have a := prod_lam x y (fun q => (k q)⁻¹)
  have b := Wit.prod_neg_lamPts x y (fun q => (k q)⁻¹)
  simp only [inv_inv, Category.id_comp] at a b
  rw [b, ← a]
  simp only [zpow_neg, inv_zpow]

open GlobalTheory.PrimCocycle in

theorem gen_transport : ∀ (SB SC : Scheme.{0}) (B : Over SB) [GrpObj B] [IsCommMonObj B] (C : Over SC) [GrpObj C] [IsCommMonObj C] (M : LB B.left) (N : LB C.left), M.IsLB → N.IsLB → ∀ (m : (G2 B).left ⟶ (G2 C).left) (w : LB.Iso (abelian₂ B M) ((abelian₂ C N).pull m)), w.IsGen → ∀ (T : Over SB) (T₀ : Over SC) (x y : T ⟶ B) (x₀ y₀ : T₀ ⟶ C) (h : T.left ⟶ T₀.left), (lift x y).left ≫ m = h ≫ (lift x₀ y₀).left → ∀ t₀ : LB.Gen (LB.LinComb N (lamPts x₀ y₀) negε), t₀.IsGen → ∃ u : LB.Gen (LB.LinComb M (lamPts x y) negε), u.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) J J', Good N z J → Good M z J' → val u r z J' = lamVal w (r ≫ (lift x y).left) z J J' * val t₀ (r ≫ h) z J := by
  intro SB SC B _ _ C _ _ M N hM hN m w hw T T₀ x y x₀ y₀ h hm t₀ ht₀
  have lM : (abelian₂ B M).IsLB := DVR.linComb_isLB _ hM _ _
  have lN : (abelian₂ C N).IsLB := DVR.linComb_isLB _ hN _ _
  obtain ⟨t₁, h₁, v₁⟩ := exists_gen hN (φ' := fun I => (lift x₀ y₀).left ≫ lamφ C I) (ε' := fun I => - lamε I)
    (fun U _ k => (prod_neg_lam x₀ y₀ k).symm) t₀ ht₀
  obtain ⟨t₂, h₂, v₂⟩ := exists_nest t₁ h₁
  obtain ⟨t₃, h₃, v₃⟩ := DegPull.exists_pmaps (L := abelian₂ C N) (L' := abelian₂ B M) ((isGen_iff w).1 hw) lN lM
    (φ' := fun _ : PUnit.{1} => (lift x y).left) h (fun _ => hm) t₂ h₂
  obtain ⟨t₄, h₄, v₄⟩ := exists_unnest (L := M) (φ := lamφ B) (ε := lamε) t₃ h₃
  obtain ⟨u, hu, vu⟩ := exists_gen hM (fun U _ k => prod_neg_lam x y k) t₄ h₄
  refine ⟨u, hu, fun Z r z J J' hJ hJ' => ?_⟩
  have e : ∀ I, (r ≫ h) ≫ (lift x₀ y₀).left ≫ lamφ C I = (r ≫ (lift x y).left) ≫ m ≫ lamφ C I := fun I => by
    rw [Category.assoc, Category.assoc, ← Category.assoc h, ← hm, Category.assoc]
  have E := v₃ Z r z (fun _ I => J ((r ≫ (lift x y).left) ≫ m ≫ lamφ C I))
    (fun _ I => J' ((r ≫ (lift x y).left) ≫ lamφ B I))
    (fun _ => Set.mem_iInter.2 fun I => hJ ((r ≫ (lift x y).left) ≫ m ≫ lamφ C I))
    (fun _ => Set.mem_iInter.2 fun I => hJ' ((r ≫ (lift x y).left) ≫ lamφ B I))
  rw [Fintype.prod_unique, zpow_neg_one] at E
  have a := v₂ Z (r ≫ h) z (fun I => J ((r ≫ (lift x y).left) ≫ m ≫ lamφ C I)) (Set.mem_iInter.2 fun I => by
    have := hJ ((r ≫ (lift x y).left) ≫ m ≫ lamφ C I)
    have e' := congrArg (fun q : Z ⟶ C.left => q z) (e I)
    exact (congrArg (· ∈ N.U _) e').mpr this)
  have b := v₄ Z r z (fun I => J' ((r ≫ (lift x y).left) ≫ lamφ B I))
    (Set.mem_iInter.2 fun I => hJ' ((r ≫ (lift x y).left) ≫ lamφ B I))
  rw [vu Z r z J' hJ', ← v₁ Z (r ≫ h) z J hJ,
    val_of t₄ r z J' (fun I => J' ((r ≫ (lift x y).left) ≫ lamφ B I)) (fun I => by rw [Category.assoc]),
    val_of t₁ (r ≫ h) z J (fun I => J ((r ≫ (lift x y).left) ≫ m ≫ lamφ C I)) (fun I => by rw [e]), b, ← a]
  exact (mul_inv_cancel_left _ _).symm.trans (congrArg (_ * ·) E.symm)

end GlobalTheory.GenTransport

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericPointOfLiesOverGeneric
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open Classical

namespace GlobalTheory.Mum

theorem eq_gp_of_lies_over_bot {R : Type} [CommRing R] [IsDomain R] {S : Scheme.{0}} [IsReduced S] (π : S ⟶ Sp R)
    (gp : Sp (FractionRing R) ⟶ S) (hgp : gp ≫ π = jK R) (hd : IsDominant gp)
    {B : CommRingCat} (e₀ : Spec B ⟶ S) [he₀ : IsOpenImmersion e₀] (P : Spec B)
    (hP : π (e₀ P) = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)) (k : Sp (FractionRing R)) : e₀ P = gp k := by
  have hsub : Set.range gp ⊆ Set.range e₀ := by
    obtain ⟨a, ha⟩ := hd.denseRange.exists_mem_open e₀.isOpenEmbedding.isOpen_range ⟨e₀ P, P, rfl⟩
    rintro _ ⟨x, rfl⟩
    rwa [Subsingleton.elim x a]
  set g' := IsOpenImmersion.lift e₀ gp hsub with hg'
  have hfac : g' ≫ e₀ = gp := IsOpenImmersion.lift_fac _ _ _
  set g := Spec.preimage g' with hg
  set ρ := Spec.preimage (e₀ ≫ π) with hρ
  have hgg : Spec.map g = g' := Spec.map_preimage _
  have hρρ : Spec.map ρ = e₀ ≫ π := Spec.map_preimage _
  have hcomp : ρ ≫ g = CommRingCat.ofHom (algebraMap R (FractionRing R)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hgg, hρρ, ← Category.assoc, hfac, hgp]
  have hcomp' : ∀ r, g.hom (ρ.hom r) = algebraMap R (FractionRing R) r := fun r => by
    have := congrArg (fun f => f.hom r) hcomp
    simpa using this
  have hden : DenseRange g' := by
    rw [denseRange_iff_closure_range, e₀.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image,
      ← Set.range_comp]
    have : (e₀ ∘ g') = gp := by funext x; rw [← hfac]; rfl
    rw [this, hd.denseRange.closure_range, Set.preimage_univ]
  have hred : _root_.IsReduced B := by
    have : IsReduced (Spec B) := isReduced_of_isOpenImmersion e₀
    exact (affine_isReduced_iff B).1 this
  have hinj : Function.Injective g.hom := by
    have h1 : DenseRange (PrimeSpectrum.comap g.hom) := by rw [← hgg] at hden; exact hden
    have h2 := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical g.hom).1 h1
    rw [nilradical_eq_zero] at h2
    exact (RingHom.injective_iff_ker_eq_bot _).2 (le_bot_iff.1 h2)
  have hPρ : Ideal.comap ρ.hom P.asIdeal = ⊥ := by
    have h2 : (Spec.map ρ) P = π (e₀ P) := by rw [hρρ]; rfl
    rw [hP] at h2
    exact congrArg PrimeSpectrum.asIdeal h2
  have hPb : P.asIdeal = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨a, s, hs, hxs⟩ := IsFractionRing.div_surjective (A := R) (g.hom x)
    have hs0 : algebraMap R (FractionRing R) s ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
    have h0 : ρ.hom s * x - ρ.hom a = 0 := by
      apply hinj
      rw [map_sub, map_mul, hcomp', hcomp', ← hxs, map_zero, mul_div_cancel₀ _ hs0, sub_self]
    have ha : a ∈ Ideal.comap ρ.hom P.asIdeal := by
      rw [Ideal.mem_comap, ← sub_eq_zero.1 h0]
      exact P.asIdeal.mul_mem_left _ hx
    rw [hPρ, Ideal.mem_bot] at ha
    have hx0 : g.hom x = 0 := by rw [← hxs, ha, map_zero, zero_div]
    rw [Ideal.mem_bot]
    exact hinj (by rw [hx0, map_zero])
  rw [← hfac]
  show e₀ P = e₀ (g' k)
  congr 1
  rw [← hgg]
  apply PrimeSpectrum.ext
  show P.asIdeal = Ideal.comap g.hom k.asIdeal
  have hk : k.asIdeal = ⊥ := @Ideal.eq_bot_of_prime _ _ _ k.isPrime
  rw [hPb, hk, Ideal.comap_bot_of_injective _ hinj]

theorem modif_pt_over_gen : ∀ (R : Type) [CommRing R] [IsDomain R] (M' : Modif R) (W : Type) [CommRing W] [IsDomain W] (φ : R →+* W) (ξ : Sp W ⟶ M'.S), Function.Injective φ → ξ ≫ M'.π = spMap φ → ∃ (w : Sp W) (k : Sp (FractionRing R)), ξ w = M'.gp k := by
  intro R _ _ M' W _ _ φ ξ hφ hξ
  have : IsReduced M'.S := by have := M'.integral; infer_instance
  let w : Sp W := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum W)
  let k : Sp (FractionRing R) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing R))
  refine ⟨w, k, ?_⟩
  let j := M'.S.affineCover.idx (ξ w)
  have hoi : IsOpenImmersion (M'.S.affineCover.f j) := M'.S.affineCover.map_prop j
  obtain ⟨P, hP⟩ := M'.S.affineCover.covers (ξ w)
  rw [← hP]
  refine eq_gp_of_lies_over_bot (he₀ := hoi) M'.π M'.gp M'.gp_π M'.dominant (M'.S.affineCover.f j) P ?_ k
  refine (congrArg M'.π hP).trans ?_
  have h1 : M'.π (ξ w) = (spMap φ) w := by rw [← hξ]; rfl
  rw [h1]
  apply PrimeSpectrum.ext
  show Ideal.comap φ ⊥ = ⊥
  exact Ideal.comap_bot_of_injective _ hφ

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericPointsUniformisationsWeilPairingGal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open MonObj
open Classical

namespace GlobalTheory.GenRestrict

theorem exists_genericPoints_equiv_any : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → IsDiscreteValuationRing V → ∀ g : R →+* V, Function.Injective g → ∀ (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'] (β : G'.left ⟶ G.left), IsGrpPullback G' G (spMap g) β → IsSemiAbelian G' → ∀ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G'), LBIso U'.LG.L (U.LG.L.pull β) →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing V) F],
      (∀ r, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) = algebraMap (FractionRing V) F (algebraMap V (FractionRing V) (g r))) →
      ∃ e : (TFK (R := V) F ⟶ A'.A) ≃* (TFK (R := R) F ⟶ A.A),
        (∀ (k : ℕ) (x y : TFK (R := V) F ⟶ A'.A) (c : Fˣ), WeilIs A'.A A'.L (k : ℤ) x y (unitOn c) → WeilIs A.A A.L (k : ℤ) (e x) (e y) (unitOn c)) ∧
        (∀ (σ : F →ₐ[FractionRing V] F) (x x' : TFK (R := V) F ⟶ A'.A), x'.left = spMap σ.toRingHom ≫ x.left → (e x').left = spMap σ.toRingHom ≫ (e x).left) ∧
        ∀ x : TFK (R := V) F ⟶ A'.A, (e x).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) = x.left ≫ U'.gen.inv.left ≫ pullback.fst G'.hom (jK V) ≫ β := by
  intro R _ _ _ hR G _ _ hG D A U V _ _ _ hV hDVR g hinj G' _ _ β h hG' D' A' U' hL F _ _ _ _ hc
  obtain ⟨gR, lR⟩ := unifPre_generic U.toUnifPre
  obtain ⟨gV, lV⟩ := unifPre_generic U'.toUnifPre
  have gVG : IsGrpPullback A'.A G (jK V ≫ spMap g) ((U'.gen.inv.left ≫ pullback.fst G'.hom (jK V)) ≫ β) :=
    gV.comp h
  have hcomp : jFK (R := V) F ≫ jK V ≫ spMap g = jFK (R := R) F ≫ jK R := by
    have e1 : (algebraMap (FractionRing V) F).comp ((algebraMap V (FractionRing V)).comp g) =
        (algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R)) := RingHom.ext fun r => (hc r).symm
    calc jFK (R := V) F ≫ jK V ≫ spMap g
        = spMap ((algebraMap (FractionRing V) F).comp ((algebraMap V (FractionRing V)).comp g)) := by
          rw [spMap_comp_eq (algebraMap (FractionRing V) F), spMap_comp_eq (algebraMap V (FractionRing V)) g]
      _ = spMap ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))) := by rw [e1]
      _ = jFK (R := R) F ≫ jK R := spMap_comp_eq _ _
  obtain ⟨eV, heV⟩ := GlobalTheory.LiePull.exists_pushEquiv gVG (TFK (R := V) F) (jFK (R := V) F ≫ jK V ≫ spMap g) rfl
  obtain ⟨eR, heR⟩ := GlobalTheory.LiePull.exists_pushEquiv gR (TFK (R := R) F) (jFK (R := V) F ≫ jK V ≫ spMap g) hcomp
  obtain ⟨eR₀, heR₀⟩ := GlobalTheory.LiePull.exists_pushEquiv gR (TFK (R := R) F) (jFK (R := R) F ≫ jK R) rfl
  have hlast : ∀ x, (eR.symm (eV x)).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) =
      x.left ≫ U'.gen.inv.left ≫ pullback.fst G'.hom (jK V) ≫ β := fun x => by
    rw [← heR, MulEquiv.apply_symm_apply, heV]
    simp only [Category.assoc]
  have lVG : LBIso A'.L (U.LG.L.pull ((U'.gen.inv.left ≫ pullback.fst G'.hom (jK V)) ≫ β)) :=
    LBIso.trans A'.isLB (pull_isLB U'.LG.isLB _) (pull_isLB U.LG.isLB _) lV
      (LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull U'.LG.L _ _ rfl)
        (chartPullSame U.LG.L _ (fun _ => β) _ (U'.gen.inv.left ≫ pullback.fst G'.hom (jK V)) fun _ => rfl) hL)
  refine ⟨eV.trans eR.symm, fun k x y c hw => ?_, fun σ x x' hx => ?_, fun x => ?_⟩
  · have h1 := (GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ G A'.A _ _ U.LG.L A'.L U.LG.isLB A'.isLB gVG lVG
      (TFK (R := V) F) k x y (eV x) (eV y) (unitOn c) (heV x) (heV y)).1 hw
    have h2 := (weilIs_congr_base G U.LG.L k hcomp (eV x) (eV y) (eR₀ (eR.symm (eV x))) (eR₀ (eR.symm (eV y)))
      (by rw [heR₀, ← heR, MulEquiv.apply_symm_apply]) (by rw [heR₀, ← heR, MulEquiv.apply_symm_apply]) _).1 h1
    exact (GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ G A.A _ _ U.LG.L A.L U.LG.isLB A.isLB gR lR
      (TFK (R := R) F) k _ _ _ _ (unitOn c) (heR₀ _) (heR₀ _)).2 h2
  · have hσ : σ.toRingHom.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F := by
      refine IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => ?_)
      simp only [RingHom.comp_apply, AlgHom.coe_toRingHom]
      rw [hc r]
      exact σ.commutes _
    refine gR.1.hom_ext ?_ ?_
    · simp only [MulEquiv.trans_apply, Category.assoc, hlast, hx]
    · rw [Over.w, Category.assoc, Over.w]
      show jFK (R := R) F = spMap σ.toRingHom ≫ jFK (R := R) F
      rw [← spMap_comp_eq, hσ]
  · exact hlast x

end GlobalTheory.GenRestrict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGluedLineBundleSectionOverCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin.ThBdl

theorem resG_resG_glue {X : Scheme.{0}} {A B C : X.Opens} (h : B ≤ A) (h' : C ≤ B) (f : Γ(X, A)) :
    resG X h' (resG X h f) = resG X (h'.trans h) f := by
  simp only [resG]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem locSec_glue : ∀ (S : Scheme.{0}) (G : Over S) (L : LB G.left) (V : S.Opens) (κ : Type) (N : κ → S.Opens)
    (s : ∀ k, LocSec G L (N k)) (hN : ∀ k, N k ≤ V), (⨆ k, N k) = V → (∀ k, IsLocSec (s k)) →
    (∀ k k' i, resG _ (fun _ hx => ⟨hx.1, hx.2.1⟩ : L.U i ⊓ G.hom ⁻¹ᵁ (N k ⊓ N k') ≤ L.U i ⊓ G.hom ⁻¹ᵁ N k) (s k i) =
      resG _ (fun _ hx => ⟨hx.1, hx.2.2⟩ : L.U i ⊓ G.hom ⁻¹ᵁ (N k ⊓ N k') ≤ L.U i ⊓ G.hom ⁻¹ᵁ N k') (s k' i)) →
    ∃ s' : LocSec G L V, IsLocSec s' ∧ ∀ k i,
      resG _ (fun _ hx => ⟨hx.1, hN k hx.2⟩ : L.U i ⊓ G.hom ⁻¹ᵁ N k ≤ L.U i ⊓ G.hom ⁻¹ᵁ V) (s' i) = s k i := by
  intro S G L V κ N s hN hV hs hc
  have hmem : ∀ x : G.left, G.hom.base x ∈ V → ∃ k, G.hom.base x ∈ N k := by
    intro x hx
    have : G.hom.base x ∈ (⨆ k, N k) := by rw [hV]; exact hx
    exact TopologicalSpace.Opens.mem_iSup.1 this
  have hcov : ∀ i, L.U i ⊓ G.hom ⁻¹ᵁ V ≤ ⨆ k, (L.U i ⊓ G.hom ⁻¹ᵁ N k) := by
    intro i x hx
    obtain ⟨k, hk⟩ := hmem x hx.2
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hx.1, hk⟩
  have hWV : ∀ i k, L.U i ⊓ G.hom ⁻¹ᵁ N k ≤ L.U i ⊓ G.hom ⁻¹ᵁ V := fun i k _ hx => ⟨hx.1, hN k hx.2⟩
  have hglue : ∀ i, ∃! t : Γ(G.left, L.U i ⊓ G.hom ⁻¹ᵁ V), ∀ k, resG _ (hWV i k) t = s k i := by
    intro i
    refine G.left.sheaf.existsUnique_gluing' (fun k => L.U i ⊓ G.hom ⁻¹ᵁ N k) (L.U i ⊓ G.hom ⁻¹ᵁ V)
      (fun k => homOfLE (hWV i k)) (hcov i) (fun k => s k i) ?_
    intro k k'
    have hle : (L.U i ⊓ G.hom ⁻¹ᵁ N k) ⊓ (L.U i ⊓ G.hom ⁻¹ᵁ N k') ≤ L.U i ⊓ G.hom ⁻¹ᵁ (N k ⊓ N k') :=
      fun _ hx => ⟨hx.1.1, hx.1.2, hx.2.2⟩
    have e := congrArg (resG _ hle) (hc k k' i)
    exact (resG_resG_glue _ _ _).symm.trans (e.trans (resG_resG_glue _ _ _))
  choose s' hs' _ using hglue
  refine ⟨s', ?_, fun k i => hs' i k⟩
  intro i j
  have hTV : ∀ k, L.U i ⊓ L.U j ⊓ G.hom ⁻¹ᵁ N k ≤ L.U i ⊓ L.U j ⊓ G.hom ⁻¹ᵁ V := fun k _ hx => ⟨hx.1, hN k hx.2⟩
  refine G.left.sheaf.eq_of_locally_eq' (fun k => L.U i ⊓ L.U j ⊓ G.hom ⁻¹ᵁ N k) (L.U i ⊓ L.U j ⊓ G.hom ⁻¹ᵁ V)
    (fun k => homOfLE (hTV k)) ?_ _ _ ?_
  · intro x hx
    obtain ⟨k, hk⟩ := hmem x hx.2
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hx.1, hk⟩
  · intro k
    have hi1 : L.U i ⊓ L.U j ⊓ G.hom ⁻¹ᵁ N k ≤ L.U i ⊓ G.hom ⁻¹ᵁ N k := fun _ hx => ⟨hx.1.1, hx.2⟩
    have hj1 : L.U i ⊓ L.U j ⊓ G.hom ⁻¹ᵁ N k ≤ L.U j ⊓ G.hom ⁻¹ᵁ N k := fun _ hx => ⟨hx.1.2, hx.2⟩
    have e1 : resG _ (hi1.trans (hWV i k)) (s' i) = resG _ hi1 (s k i) := by
      rw [← hs' i k, resG_resG_glue]
    have e2 : resG _ (hj1.trans (hWV j k)) (s' j) = resG _ hj1 (s k j) := by
      rw [← hs' j k, resG_resG_glue]
    change resG _ (hTV k) (resG _ _ (s' i)) =
      resG _ (hTV k) (resG _ _ (L.g i j : Γ(G.left, L.U i ⊓ L.U j)) * resG _ _ (s' j))
    rw [map_mul]
    refine ((resG_resG_glue _ _ _).trans e1).trans ((hs k i j).trans ?_)
    congr 1
    · exact (resG_resG_glue _ _ _).symm
    · exact ((resG_resG_glue _ _ _).trans e2).symm

end GlobalTheory.UMin.ThBdl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHilbertEisensteinFourierCoeffFamilyStatement
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hilbertEisenstein_fourierCoeffFamily : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (𝔞 𝔟 : Frac F) (s : ℕ), 1 ≤ s → ∃ (Z : ℂ → ℂ) (a : F → ℂ), IsPartialZeta (ClassGroup.mk F 𝔞)⁻¹ Z ∧ IsCoef (2 * s) 𝔞 𝔟 ((2 : ℂ)⁻¹ ^ Module.finrank ℚ F * Z (1 - ((2 * s : ℕ) : ℂ))) a := by
  first | exact @GlobalTheory.HilbFam.exists_isCoef | exact GlobalTheory.HilbFam.exists_isCoef | (intros; apply GlobalTheory.HilbFam.exists_isCoef <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomogeneousCorrectionNextThickeningStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_homogeneous_correction_next_thickening : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (H : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (H e) ((H (e + 1)).pull (β e))), (∀ e, (H e).IsLB ∧ (v e).IsGen) → ∀ (n : ℕ) (s : ∀ e, Fin (n + 1) → LB.Sec (H e)), (∀ e j, Rel (β e) (v e) (s (e + 1) j) (s e j)) → VeryAmpleBy (Y 0).hom (H 0) (s 0) → ∃ t₀ : ℕ, ∀ t, t₀ ≤ t → ∀ (e : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous t → F ∈ vanIdeal ((Y e).hom ≫ thick R I e) (s e) → ∃ G : MvPolynomial (Fin (n + 1)) R, G.IsHomogeneous t ∧ (∀ d, MvPolynomial.coeff d G ∈ I ^ (e + 1)) ∧ F - G ∈ vanIdeal ((Y (e + 1)).hom ≫ thick R I (e + 1)) (s (e + 1)) := by
  first | exact @GlobalTheory.FormalAlg.exists_homogeneous_correction_succ | exact GlobalTheory.FormalAlg.exists_homogeneous_correction_succ | (intros; apply GlobalTheory.FormalAlg.exists_homogeneous_correction_succ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHormanderPeakOrthonormalFrameL2BoundStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
open ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hormanderPeak_orthonormalFrame_l2Bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (x : Frame X.Ψ r), 0 < X.p0 → X.p0 < r → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → (∀ τ (a b : Fin r), (b : ℕ) = a + 1 → (b : ℕ) ≠ X.p0 → C * ((X.Ψ.card : ℝ) * r) ^ 8 ≤ (la τ a : ℝ) - la τ b) → (∀ τ (a b : Fin r), (a : ℕ) = 0 → (b : ℕ) = r - 1 → C * ((X.Ψ.card : ℝ) * r) ^ 8 ≤ (la τ b : ℝ) - la τ a) → (∀ γ ∈ X.Γ, ∀ z z' : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ‖z'‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ∀ b ∈ Bor X.Ψ r, lact γ (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) = rmul (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z') b → γ = 1) → ∃ (F : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X) → ℂ) (P0 : Frame X.Ψ r → ℂ), DifferentiableOn ℂ F (ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x) ∧ ReciprocityTheory.ChartRestriction.G.AR.Up.IsBEq X la P0 ∧ (∀ z ∈ ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x, P0 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) = F z) ∧ P0 x = 1 ∧ (∀ γ ∈ X.Γ, γ ≠ 1 → P0 (lact γ x) = 0) ∧ ReciprocityTheory.ChartRestriction.G.AR.Up.InAt X x (ReciprocityTheory.ChartRestriction.G.AR.Up.IW.Wpsi X la (fun _ => 0)) (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) F ∧ ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2 / ReciprocityTheory.ChartRestriction.G.AR.Up.kaF X x (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) z) * ReciprocityTheory.ChartRestriction.G.AR.Up.IW.Wpsi X la (fun _ => 0) (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x) ≤ ENNReal.ofReal (Real.exp (C * ((∑ τ, ∑ a, |(la τ a : ℝ)|) + ((X.Ψ.card : ℝ) * r) ^ 8))) * ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x (Metric.ball 0 (1 / (100 * (r : ℝ) ^ 2)) ∩ ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x) := by
  first | exact @GlobalTheory.HormanderPeak.hormander_peak | exact GlobalTheory.HormanderPeak.hormander_peak | (intros; apply GlobalTheory.HormanderPeak.hormander_peak <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInjectiveListMSqTorsionPolarisedFibreStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_injective_list_m_sq_torsion_polarisedFibre : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (g m : ℕ) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S), (m : K) ≠ 0 → PolFib G L g x → ∃ pt : Fin (m ^ (4 * g)) → (Over.mk x ⟶ G), Function.Injective pt ∧ (∀ a, pt a ^ (m ^ 2) = 1) ∧ ∀ (K' : Type) [Field K'] [IsAlgClosed K'] (i : K →+* K') (p : Over.mk (spMap i ≫ x) ⟶ G), p ^ (m ^ 2) = 1 → ∃ a, p.left = spMap i ≫ (pt a).left := by
  first | exact @GlobalTheory.UMin.TorsList.exists_torsion_list | exact GlobalTheory.UMin.TorsList.exists_torsion_list | (intros; apply GlobalTheory.UMin.TorsList.exists_torsion_list <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralGaugeFiniteExtensionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_gauge_finite_extension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (N : GlobalTheory.Ex.NumD (Kb R)) (ν : GlobalTheory.Ex.NumOf D.toPre (Kb R) N) (m : ℕ), Odd m → IsUnit (m : R) → ∀ (p : QkPt D.toPre (Kb R) (m ^ 2)), ∃ (N' : GlobalTheory.Ex.NumD (Kb R)) (ν' : GlobalTheory.Ex.NumOf D.toPre (Kb R) N') (q' : N'.QT (m ^ 2)) (S : Subalgebra R (Kb R)), ν'.th = ν.th ∧ ν'.QPt p q' ∧ Module.Finite R S ∧ (∀ x ∈ Subgroup.closure (Set.range N'.c ∪ {(q'.1.2 ^ m).b}), ∀ x' ∈ Subgroup.closure (Set.range N'.c ∪ {(q'.1.2 ^ m).b}), ∀ x'' ∈ Subgroup.closure (Set.range N'.c ∪ {(q'.1.2 ^ m).b}), (N'.θ x x' x'' : Kb R) ∈ S ∧ (((N'.θ x x' x'')⁻¹ : (Kb R)ˣ) : Kb R) ∈ S) ∧ (∀ x ∈ Subgroup.closure (Set.range N'.c ∪ {(q'.1.2 ^ m).b}), (N'.σ x : Kb R) ∈ S ∧ (((N'.σ x)⁻¹ : (Kb R)ˣ) : Kb R) ∈ S) ∧ (∀ χ, N'.th (N'.c χ * (q'.1.2 ^ m).b) ∈ S) ∧ (∀ χ, (N'.ψ χ : Kb R) ∈ S) ∧ ∀ n : ℕ, {χ | ¬ ∃ s ∈ (maximalIdeal R ^ n • ⊤ : Submodule R S), (s : Kb R) = N'.ψ χ}.Finite := by
  first | exact @GlobalTheory.FinGauge.gauge | exact GlobalTheory.FinGauge.gauge | (intros; apply GlobalTheory.FinGauge.gauge <;> assumption)
end

