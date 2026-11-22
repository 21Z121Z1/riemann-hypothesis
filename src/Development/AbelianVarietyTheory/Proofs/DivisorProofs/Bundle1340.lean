import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1150
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0732
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0683
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
import Formalism.HarderNarasimhan.StatementPl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1314
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1313
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1315
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0183
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpehPartIsRun
section
open NumberField IsDedekindDomain
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GalDef.RunPart

open GlobalTheory.DefiniteBC

theorem map_le_spehInf (d k : ℕ) (hk : k < d) (m : Multiset ℂ) :
    m.map (· + (((d : ℂ) - 1) / 2 - k)) ≤ spehInf d m := by
  unfold spehInf
  exact List.le_sum_of_mem (List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩)

theorem mem_infOfWeight {n : ℕ} (lam : DomWeight n) (x : ℂ) (hx : x ∈ infOfWeight lam) :
    ∃ j < n, x = (wAt lam j : ℂ) + (((n : ℂ) - 1) / 2 - (j : ℕ)) := by
  unfold infOfWeight at hx
  obtain ⟨k, -, rfl⟩ := Multiset.mem_map.1 hx
  refine ⟨k, k.2, ?_⟩
  simp [wAt, k.2]

theorem entry_of_run {n t : ℕ} (lam : DomWeight n) (p : ℕ) (hn : n < 2 * t) (hrun : IsRunAt lam p t)
    (d : ℕ) (m : Multiset ℂ) (hle : spehInf d m ≤ infOfWeight lam) (htd : t ≤ d) (z : ℂ) (hz : z ∈ m) :
    d = t ∧ z = (wAt lam p : ℂ) + ((n : ℂ) - 1) / 2 - (p : ℕ) - ((t : ℂ) - 1) / 2 := by
  obtain ⟨hpt, hconst, hleft, hright⟩ := hrun
  have hval : ∀ k < d, ∃ j < n,
      z + (((d : ℂ) - 1) / 2 - k) = (wAt lam j : ℂ) + (((n : ℂ) - 1) / 2 - (j : ℕ)) := fun k hk =>
    mem_infOfWeight lam _ (Multiset.mem_of_le hle
      (Multiset.mem_of_le (map_le_spehInf d k hk m) (Multiset.mem_map_of_mem _ hz)))
  have ht0 : 0 < t := by omega
  obtain ⟨j0, hj0, e0⟩ := hval 0 (by omega)
  set c : ℤ := wAt lam j0 - j0 with hc
  have hvalc : ∀ k < d, ∃ j < n, wAt lam j - (j : ℤ) = c - k := by
    intro k hk
    obtain ⟨j, hj, e⟩ := hval k hk
    refine ⟨j, hj, ?_⟩
    have : ((wAt lam j - (j : ℤ) : ℤ) : ℂ) = ((c - k : ℤ) : ℂ) := by
      rw [hc]; push_cast
      push_cast at e0 e
      linear_combination e0 - e
    exact_mod_cast this
  have hmono : ∀ i j, i ≤ j → j < n → wAt lam j ≤ wAt lam i := by
    intro i j hij hj
    simp only [wAt, hj, dif_pos, show i < n by omega]
    exact lam.anti (Fin.mk_le_mk.2 hij)
  have hB := fun (c' : ℤ) (h : ∀ i < t, ∃ j < n, wAt lam j - j = c' - i) =>
    GlobalTheory.block_is_the_run n p t (wAt lam) c' hmono hpt (by omega) (by omega) hconst hleft hright h
  have hcp : c = wAt lam p - p := hB c fun i hi => hvalc i (by omega)
  have hdt : d = t := by
    by_contra hne
    have := hB (c - 1) fun i hi => by
      obtain ⟨j, hj, e⟩ := hvalc (i + 1) (by omega)
      exact ⟨j, hj, by push_cast at e; linarith⟩
    omega
  refine ⟨hdt, ?_⟩
  have hc' : (c : ℂ) = (wAt lam p : ℂ) - (p : ℕ) := by rw [hcp]; push_cast; ring
  have : (c : ℂ) = (wAt lam j0 : ℂ) - (j0 : ℕ) := by rw [hc]; push_cast; ring
  subst hdt
  push_cast at e0
  linear_combination e0 - this + hc'

end GlobalTheory.GalDef.RunPart

open GlobalTheory.GalDef.RunPart in

theorem GlobalTheory.GalDef.spehPart_is_run : ∀ (n t : ℕ) (lam : DomWeight n) (p : ℕ), n < 2 * t → GlobalTheory.GalDef.IsRunAt lam p t →
  ∀ (c : ℕ) (d : Fin c → ℕ) (M : Fin c → Multiset ℂ), (∀ i, 1 ≤ d i) → (∀ i, M i ≠ 0) →
    ∑ i, spehInf (d i) (M i) = infOfWeight lam →
    ∀ i, t ≤ d i → d i = t ∧
      M i = {(GlobalTheory.GalDef.wAt lam p : ℂ) + ((n : ℂ) - 1) / 2 - (p : ℕ) - ((t : ℂ) - 1) / 2} ∧ ∀ j, j ≠ i → d j < t := by
  intro n t lam p hn hrun c d M hd hM hsum i hti
  have hle : ∀ j, spehInf (d j) (M j) ≤ infOfWeight lam := fun j => by
    rw [← hsum]
    exact Finset.single_le_sum (f := fun j => spehInf (d j) (M j)) (fun _ _ => Multiset.zero_le _) (Finset.mem_univ j)
  obtain ⟨z, hz⟩ := Multiset.exists_mem_of_ne_zero (hM i)
  obtain ⟨hdi, hzv⟩ := entry_of_run lam p hn hrun (d i) (M i) (hle i) hti z hz
  set v : ℂ := (wAt lam p : ℂ) + ((n : ℂ) - 1) / 2 - (p : ℕ) - ((t : ℂ) - 1) / 2 with hv
  have hall : ∀ z' ∈ M i, z' = v := fun z' hz' => (entry_of_run lam p hn hrun (d i) (M i) (hle i) hti z' hz').2
  have hnd : ∀ j, (spehInf (d j) (M j)).Nodup := fun j =>
    Multiset.nodup_of_le (hle j) (nodup_infOfWeight lam)
  refine ⟨hdi, ?_, ?_⟩
  · have hnodup : (M i).Nodup :=
      (Multiset.nodup_of_le (map_le_spehInf (d i) 0 (by omega) (M i)) (hnd i)).of_map _
    rw [Multiset.eq_replicate.2 ⟨rfl, hall⟩] at hnodup ⊢
    have hc1 : Multiset.card (M i) ≤ 1 := by
      by_contra h
      push_neg at h
      obtain ⟨k, hk⟩ : ∃ k, Multiset.card (M i) = k + 2 := ⟨Multiset.card (M i) - 2, by omega⟩
      rw [hk, Multiset.replicate_succ, Multiset.replicate_succ, Multiset.nodup_cons] at hnodup
      exact hnodup.1 (Multiset.mem_cons_self _ _)
    have hc0 : Multiset.card (M i) ≠ 0 := fun h => hM i (Multiset.card_eq_zero.1 h)
    rw [show Multiset.card (M i) = 1 by omega, Multiset.replicate_one]
  · intro j hji
    by_contra hlt
    push_neg at hlt
    obtain ⟨z', hz'⟩ := Multiset.exists_mem_of_ne_zero (hM j)
    obtain ⟨hdj, hz'v⟩ := entry_of_run lam p hn hrun (d j) (M j) (hle j) hlt z' hz'
    have ht0 : 0 < t := by omega
    have hmem : ∀ k, 0 < d k → ∀ w ∈ M k, w + (((d k : ℂ) - 1) / 2 - ((0 : ℕ) : ℂ)) ∈ spehInf (d k) (M k) :=
      fun k hk w hw => Multiset.mem_of_le (map_le_spehInf (d k) 0 hk (M k)) (Multiset.mem_map_of_mem _ hw)
    have hpair : spehInf (d i) (M i) + spehInf (d j) (M j) ≤ infOfWeight lam := by
      rw [← hsum]
      calc spehInf (d i) (M i) + spehInf (d j) (M j) = ∑ k ∈ {i, j}, spehInf (d k) (M k) :=
            (Finset.sum_pair (f := fun k => spehInf (d k) (M k)) hji.symm).symm
        _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    have hdis := (Multiset.nodup_add.1 (Multiset.nodup_of_le hpair (nodup_infOfWeight lam))).2.2
    have h1 := hmem i (by omega) z hz
    have h2 := hmem j (by omega) z' hz'
    rw [hdi, hzv] at h1
    rw [hdj, hz'v] at h2
    rw [hdi, hdj] at hdis
    exact Multiset.disjoint_left.1 hdis h1 h2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumSqNormEqDot
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open Matrix

noncomputable section

open scoped MatrixOrder ComplexOrder

namespace GlobalTheory.HermFamFrame

def formRight {K V : Type} [Field K] [AddCommGroup V] [Module K V] (nm : HermFam K V)
    (σ : K →+* ℂ) (x : V) : V →+ ℂ :=
  AddMonoidHom.mk' (nm.form σ x) (nm.add_right σ x)

theorem form_sum_right {K V : Type} [Field K] [AddCommGroup V] [Module K V] (nm : HermFam K V)
    (σ : K →+* ℂ) (x : V) {ι : Type} (s : Finset ι) (a : ι → K) (w : ι → V) :
    nm.form σ x (∑ j ∈ s, a j • w j) = ∑ j ∈ s, σ (a j) * nm.form σ x (w j) := by
  have := map_sum (formRight nm σ x) (fun j => a j • w j) s
  simp only [formRight, AddMonoidHom.mk'_apply] at this
  rw [this]
  exact Finset.sum_congr rfl fun j _ => nm.smul_right σ (a j) x (w j)

theorem form_sum_left {K V : Type} [Field K] [AddCommGroup V] [Module K V] (nm : HermFam K V)
    (σ : K →+* ℂ) (y : V) {ι : Type} (s : Finset ι) (a : ι → K) (w : ι → V) :
    nm.form σ (∑ i ∈ s, a i • w i) y = ∑ i ∈ s, starRingEnd ℂ (σ (a i)) * nm.form σ (w i) y := by
  rw [← nm.conj_symm, form_sum_right, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, nm.conj_symm]

def basisGram {K V : Type} [Field K] [AddCommGroup V] [Module K V] (nm : HermFam K V)
    (σ : K →+* ℂ) {ι : Type} (b : Module.Basis ι K V) : Matrix ι ι ℂ :=
  Matrix.of fun i j => nm.form σ (b i) (b j)

end GlobalTheory.HermFamFrame

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPhiInjectiveCriterionStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_Phi_injective_criterion : ∀ (p : ℕ) (O : Type) [CommRing O] (G : GlobalTheory.PDivGroup p O) (A : Over (Sp O)) [GrpObj A] (t : G.TorsionTower A), (∀ (M : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] (z z' : TM O M ⟶ A) (h : zeroSec O M ≫ z = η[A]) (h' : zeroSec O M ≫ z' = η[A]), (∀ w, Phi z h w = Phi z' h' w) → z = z') → (∀ (M : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] (n : ℕ) (φ : G.A n →ₐ[O] TrivSqZeroExt O M) (hφ : (TrivSqZeroExt.fstHom O O M).comp φ = Bialgebra.counitAlgHom O (G.A n)) (w : Wmod A), Phi (spOver φ ≫ t.y n) (zeroSec_spOver_y t n φ hφ) w = GlobalTheory.AugCot.sqZeroEquiv (Bialgebra.counitAlgHom O (G.A n)) M ⟨φ, hφ⟩ (cn t n w)) → ∀ n : ℕ, Function.Surjective (cn t n) := by
  first | exact @GlobalTheory.SqZeroPt.CnSurj.cn_surjective | exact GlobalTheory.SqZeroPt.CnSurj.cn_surjective | (intros; apply GlobalTheory.SqZeroPt.CnSurj.cn_surjective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPhiNaturalityFamilyStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_Phi_naturality_family : ∀ (p : ℕ) (O : Type) [CommRing O] (G : GlobalTheory.PDivGroup p O) (A : Over (Sp O)) [GrpObj A] (t : G.TorsionTower A), Module.Finite O (Wmod A) → Module.Projective O (Wmod A) → (∀ (M N : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] [AddCommGroup N] [Module O N] [Module Oᵐᵒᵖ N] [IsCentralScalar O N] (l : M →ₗ[O] N) (z : TM O M ⟶ A) (h : zeroSec O M ≫ z = η[A]) (h' : zeroSec O N ≫ (GlobalTheory.GrpTangent.sqZeroMap l ≫ z) = η[A]) (w : Wmod A), Phi (GlobalTheory.GrpTangent.sqZeroMap l ≫ z) h' w = l (Phi z h w)) → (∀ (l : Wmod A →ₗ[O] O), ∃ (v : TM O O ⟶ A) (h : zeroSec O O ≫ v = η[A]), ∀ w, Phi v h w = l w) → (∀ (M : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] (n : ℕ) (φ : G.A n →ₐ[O] TrivSqZeroExt O M) (hφ : (TrivSqZeroExt.fstHom O O M).comp φ = Bialgebra.counitAlgHom O (G.A n)) (w : Wmod A), Phi (spOver φ ≫ t.y n) (zeroSec_spOver_y t n φ hφ) w = GlobalTheory.AugCot.sqZeroEquiv (Bialgebra.counitAlgHom O (G.A n)) M ⟨φ, hφ⟩ (cn t n w)) → ∀ (n : ℕ) (w : Wmod A), cn t n w = 0 → w ∈ (Ideal.span {(p : O) ^ n} • ⊤ : Submodule O (Wmod A)) := by
  first | exact @GlobalTheory.LieKer.ker_cn_le | exact GlobalTheory.LieKer.ker_cn_le | (intros; apply GlobalTheory.LieKer.ker_cn_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPhiNaturalityLinearStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_Phi_naturality_linear : ∀ (p : ℕ) (O : Type) [CommRing O] (G : GlobalTheory.PDivGroup p O) (A : Over (Sp O)) [GrpObj A] (t : G.TorsionTower A), (∀ (M N : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] [AddCommGroup N] [Module O N] [Module Oᵐᵒᵖ N] [IsCentralScalar O N] (l : M →ₗ[O] N) (z : TM O M ⟶ A) (h : zeroSec O M ≫ z = η[A]) (h' : zeroSec O N ≫ (GlobalTheory.GrpTangent.sqZeroMap l ≫ z) = η[A]) (w : Wmod A), Phi (GlobalTheory.GrpTangent.sqZeroMap l ≫ z) h' w = l (Phi z h w)) → ∀ (n : ℕ) (w : Wmod A), GlobalTheory.PDiv.cotMap (G.res n) (cn t (n + 1) w) = cn t n w := by
  first | exact @GlobalTheory.SqZeroPt.cotMap_res_cn | exact GlobalTheory.SqZeroPt.cotMap_res_cn | (intros; apply GlobalTheory.SqZeroPt.cotMap_res_cn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPhiNaturalityModuleStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_Phi_naturality_module : ∀ (p : ℕ) (O : Type) [CommRing O] (G : GlobalTheory.PDivGroup p O) (A : Over (Sp O)) [GrpObj A] (t : G.TorsionTower A), (∀ (M N : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] [AddCommGroup N] [Module O N] [Module Oᵐᵒᵖ N] [IsCentralScalar O N] (l : M →ₗ[O] N) (z : TM O M ⟶ A) (h : zeroSec O M ≫ z = η[A]) (h' : zeroSec O N ≫ (GlobalTheory.GrpTangent.sqZeroMap l ≫ z) = η[A]) (w : Wmod A), Phi (GlobalTheory.GrpTangent.sqZeroMap l ≫ z) h' w = l (Phi z h w)) → (∀ (M : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] (n : ℕ) (φ : G.A n →ₐ[O] TrivSqZeroExt O M) (hφ : (TrivSqZeroExt.fstHom O O M).comp φ = Bialgebra.counitAlgHom O (G.A n)) (w : Wmod A), Phi (spOver φ ≫ t.y n) (zeroSec_spOver_y t n φ hφ) w = GlobalTheory.AugCot.sqZeroEquiv (Bialgebra.counitAlgHom O (G.A n)) M ⟨φ, hφ⟩ (cn t n w)) := by
  first | exact @GlobalTheory.SqZeroPt.Phi_spOver_y | exact GlobalTheory.SqZeroPt.Phi_spOver_y | (intros; apply GlobalTheory.SqZeroPt.Phi_spOver_y <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPhiNaturalityPairStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_Phi_naturality_pair : ∀ (p : ℕ) (O : Type) [CommRing O] (G : GlobalTheory.PDivGroup p O) (A : Over (Sp O)) [GrpObj A] (t : G.TorsionTower A), (∀ (M N : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] [AddCommGroup N] [Module O N] [Module Oᵐᵒᵖ N] [IsCentralScalar O N] (l : M →ₗ[O] N) (z : TM O M ⟶ A) (h : zeroSec O M ≫ z = η[A]) (h' : zeroSec O N ≫ (GlobalTheory.GrpTangent.sqZeroMap l ≫ z) = η[A]) (w : Wmod A), Phi (GlobalTheory.GrpTangent.sqZeroMap l ≫ z) h' w = l (Phi z h w)) → (∀ (M : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] (n : ℕ) (φ : G.A n →ₐ[O] TrivSqZeroExt O M) (hφ : (TrivSqZeroExt.fstHom O O M).comp φ = Bialgebra.counitAlgHom O (G.A n)) (w : Wmod A), Phi (spOver φ ≫ t.y n) (zeroSec_spOver_y t n φ hφ) w = GlobalTheory.AugCot.sqZeroEquiv (Bialgebra.counitAlgHom O (G.A n)) M ⟨φ, hφ⟩ (cn t n w)) → ∀ (v : epsR O ⟶ A) (hv : IsTangent v) (h : zeroSec O O ≫ v = η[A]) (n : ℕ) (w : Wmod A), t.tanDer hv n (cn t n w) = Ideal.Quotient.mk _ (Phi v h w) := by
  first | exact @GlobalTheory.SqZeroPt.tanDer_cn | exact GlobalTheory.SqZeroPt.tanDer_cn | (intros; apply GlobalTheory.SqZeroPt.tanDer_cn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPhiSmulStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_Phi_smul : ∀ (O : Type) [CommRing O] (M : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] (A : Over (Sp O)) [GrpObj A] (z : TM O M ⟶ A) (h : zeroSec O M ≫ z = η[A]) (c : O) (w : Wmod A), Phi z h (c • w) = c • Phi z h w := by
  first | exact @GlobalTheory.SqZeroPt.Phi_smul | exact GlobalTheory.SqZeroPt.Phi_smul | (intros; apply GlobalTheory.SqZeroPt.Phi_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPhiSqZeroNaturalityStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_Phi_sqZero_naturality : ∀ (O : Type) [CommRing O] (M N : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] [AddCommGroup N] [Module O N] [Module Oᵐᵒᵖ N] [IsCentralScalar O N] (A : Over (Sp O)) [GrpObj A] (l : M →ₗ[O] N) (z : TM O M ⟶ A) (h : zeroSec O M ≫ z = η[A]) (h' : zeroSec O N ≫ (GlobalTheory.GrpTangent.sqZeroMap l ≫ z) = η[A]) (w : Wmod A), Phi (GlobalTheory.GrpTangent.sqZeroMap l ≫ z) h' w = l (Phi z h w) := by
  first | exact @GlobalTheory.SqZeroPt.Phi_sqZeroMap_comp | exact GlobalTheory.SqZeroPt.Phi_sqZeroMap_comp | (intros; apply GlobalTheory.SqZeroPt.Phi_sqZeroMap_comp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPhiSurjectiveOntoDualStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_Phi_surjective_onto_dual : ∀ (O : Type) [CommRing O] (A : Over (Sp O)) [GrpObj A], (GlobalTheory.LieVB.omega A).IsQuasicoherent → (∀ (l : Wmod A →ₗ[O] O), ∃ (v : TM O O ⟶ A) (h : zeroSec O O ≫ v = η[A]), ∀ w, Phi v h w = l w) := by
  first | exact @GlobalTheory.SqZeroPt.exists_phi_eq | exact GlobalTheory.SqZeroPt.exists_phi_eq | (intros; apply GlobalTheory.SqZeroPt.exists_phi_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningTowerChartsPreimageAndGermPullback
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

set_option autoImplicit false

namespace GlobalTheory.FormalAlg

theorem Charts.tower_preimage_germ : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (n : ℕ) (C : Charts I Y β n) (γ : ∀ e, (Y 0).left ⟶ (Y e).left), γ 0 = 𝟙 _ → (∀ e, γ e ≫ β e = γ (e + 1)) → ∀ (e : ℕ) (i : Fin (n + 1)), γ e ⁻¹ᵁ C.D e i = C.D 0 i ∧ ∀ (j : Fin (n + 1)) (z : (Y 0).left), z ∈ C.D 0 i → gs (γ e) z (C.D e i) (C.ρ e i j) = gs (𝟙 _) z (C.D 0 i) (C.ρ 0 i j) := by
  intro R _ I Y β n C γ h0 hγ e
  induction e with
  | zero =>
    intro i
    subst_vars
    refine ⟨?_, fun j z _ => ?_⟩
    · rw [h0]; rfl
    · rw [h0]
  | succ e ih =>
    intro i
    obtain ⟨hpre, hgerm⟩ := ih i
    have hp : γ (e + 1) ⁻¹ᵁ C.D (e + 1) i = C.D 0 i := by
      rw [← hγ e, Scheme.Hom.comp_preimage, C.pre, hpre]
    refine ⟨hp, fun j z hz => ?_⟩
    have hz' : γ e z ∈ C.D e i := by rw [← hpre] at hz; exact hz
    have hz'' : β e (γ e z) ∈ C.D (e + 1) i := by
      have : γ e z ∈ β e ⁻¹ᵁ C.D (e + 1) i := by rw [C.pre]; exact hz'
      exact this
    rw [← hgerm j z hz, ← C.ρ_pull e i j, ← hγ e, ← gs_pull (γ e) (β e) z _ hz'',
      ← gs_res (γ e) z (C.pre e i).ge hz']
    rfl

end GlobalTheory.FormalAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusElementDualFrameRowsEigenInverseStatement
section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusElement_dualFrameRows_eigen_inverse : ∀ (R : Type) [CommRing R] (m r : ℕ) (X Y : Matrix (Fin m) (Fin r) R) (X' Y' : Matrix (Fin r) (Fin m) R) (d e : Matrix (Fin r) (Fin r) R) (A B : Matrix (Fin m) (Fin m) R), X' * X = 0 → Y' * Y = 0 → X' * Y = 1 → Y' * X = 1 → d * e = 1 → e * d = 1 → A * X = X * d → A * Y = Y * e → A * (1 - X * Y' - Y * X') = 1 - X * Y' - Y * X' → A * B = 1 → Y' * B = e * Y' ∧ X' * B = d * X' ∧ (1 - X * Y' - Y * X') * B = 1 - X * Y' - Y * X' := by
  first | exact @GlobalTheory.torus_dual_frame_rows_eigen | exact GlobalTheory.torus_dual_frame_rows_eigen | (intros; apply GlobalTheory.torus_dual_frame_rows_eigen <;> assumption)
end

