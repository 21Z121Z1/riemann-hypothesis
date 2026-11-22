import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2219
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0609
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2259
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0629
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineLeOrDisjoint
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2243
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulShortNonneg
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IndexRangeMatrix
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2032
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2036
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2204
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0005
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0318
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCosetOfIsTensor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoefficientBound
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0575
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0501
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0325
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0027
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2230
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2242
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2245
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2220
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.MemRangeOfIsAlgebraicRatFun
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartPullbackLineBundleTransitionEqAppLEStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartPullback_lineBundle_transition_eq_appLE : ∀ (Y Y' : Scheme.{0}) (A' : LB Y') (A : LB Y) (h : Y' ⟶ Y) (cp : ChartPull A' A h) (i j : A'.ι), ((A'.g i j : Γ(Y', A'.U i ⊓ A'.U j)ˣ) : Γ(Y', A'.U i ⊓ A'.U j)) = (h.appLE (A.U (cp.idx i) ⊓ A.U (cp.idx j)) (A'.U i ⊓ A'.U j) (le_inf (inf_le_left.trans (cp.le i)) (inf_le_right.trans (cp.le j)))).hom ((A.g (cp.idx i) (cp.idx j) : Γ(Y, A.U (cp.idx i) ⊓ A.U (cp.idx j))ˣ) : Γ(Y, A.U (cp.idx i) ⊓ A.U (cp.idx j))) := by
  first | exact @GlobalTheory.chartPull_g_appLE | exact GlobalTheory.chartPull_g_appLE | (intros; apply GlobalTheory.chartPull_g_appLE <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartRatioOnOverlap
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel

theorem unit_ratio_norm_sub_le_max {p : ℕ} [Fact p.Prime] (x y : ℂ_[p]) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  rw [sub_eq_add_neg, ← norm_neg y]
  exact IsUltrametricDist.norm_add_le_max _ _

theorem unit_ratio_close : ∀ (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) (Xw : X.Opens) (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]), (∀ yb, IsTest p Xw yb → (K yb).Nonempty) → ∀ (R1 R2 A : Type) [CommRing R1] [CommRing R2] [CommRing A] (ξ1 : Sp R1 ⟶ X) (ξ2 : Sp R2 ⟶ X) (w : Sp A ⟶ X) (c1 : (Localization.Away (p : R1))ˣ) (c2 : (Localization.Away (p : R2))ˣ) (a1 : R1 →+* A) (a2 : R2 →+* A), spMap a1 ≫ ξ1 = w → spMap a2 ≫ ξ2 = w → (∀ φ : R1 →+* 𝓞_ℂ_[p], IsTest p Xw (spMap φ ≫ ξ1) → ∀ ψ : Localization.Away (p : R1) →+* ℂ_[p], ψ.comp (algebraMap R1 _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ → ∀ κ ∈ K (spMap φ ≫ ξ1), ‖ψ (c1 : Localization.Away (p : R1)) - κ‖ < ‖κ‖) → (∀ φ : R2 →+* 𝓞_ℂ_[p], IsTest p Xw (spMap φ ≫ ξ2) → ∀ ψ : Localization.Away (p : R2) →+* ℂ_[p], ψ.comp (algebraMap R2 _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ → ∀ κ ∈ K (spMap φ ≫ ξ2), ‖ψ (c2 : Localization.Away (p : R2)) - κ‖ < ‖κ‖) → ∀ (χ1 : Localization.Away (p : R1) →+* Localization.Away (p : A)) (χ2 : Localization.Away (p : R2) →+* Localization.Away (p : A)), χ1.comp (algebraMap R1 _) = (algebraMap A _).comp a1 → χ2.comp (algebraMap R2 _) = (algebraMap A _).comp a2 → ∀ φ : A →+* 𝓞_ℂ_[p], IsTest p Xw (spMap φ ≫ w) → ∀ ψ : Localization.Away (p : A) →+* ℂ_[p], ψ.comp (algebraMap A _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ → ‖ψ (χ1 (c1 : Localization.Away (p : R1))) - ψ (χ2 (c2 : Localization.Away (p : R2)))‖ < ‖ψ (χ2 (c2 : Localization.Away (p : R2)))‖ := by
  intro p _ X Xw K hK R1 R2 A _ _ _ ξ1 ξ2 w c1 c2 a1 a2 h1 h2 H1 H2 χ1 χ2 hχ1 hχ2 φ hφ ψ hψ
  have e1 : spMap (φ.comp a1) ≫ ξ1 = spMap φ ≫ w := by rw [← sp_sp, h1]
  have e2 : spMap (φ.comp a2) ≫ ξ2 = spMap φ ≫ w := by rw [← sp_sp, h2]
  have hψ1 : (ψ.comp χ1).comp (algebraMap R1 _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp (φ.comp a1) := by
    rw [RingHom.comp_assoc, hχ1, ← RingHom.comp_assoc, hψ, RingHom.comp_assoc]
  have hψ2 : (ψ.comp χ2).comp (algebraMap R2 _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp (φ.comp a2) := by
    rw [RingHom.comp_assoc, hχ2, ← RingHom.comp_assoc, hψ, RingHom.comp_assoc]
  obtain ⟨κ, hκ⟩ := hK _ hφ
  have k1 := H1 (φ.comp a1) (by rw [e1]; exact hφ) (ψ.comp χ1) hψ1 κ (by rw [e1]; exact hκ)
  have k2 := H2 (φ.comp a2) (by rw [e2]; exact hφ) (ψ.comp χ2) hψ2 κ (by rw [e2]; exact hκ)
  simp only [RingHom.comp_apply] at k1 k2
  set a := ψ (χ1 (c1 : Localization.Away (p : R1)))
  set b := ψ (χ2 (c2 : Localization.Away (p : R2)))
  have hab : ‖a - b‖ < ‖κ‖ := by
    have : a - b = (a - κ) - (b - κ) := by ring
    rw [this]
    exact lt_of_le_of_lt (unit_ratio_norm_sub_le_max _ _) (max_lt k1 k2)
  have hb : ‖b‖ = ‖κ‖ := by
    apply le_antisymm
    · have : b = (b - κ) + κ := by ring
      rw [this]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le k2.le le_rfl)
    · have : κ = b - (b - κ) := by ring
      calc ‖κ‖ = ‖b - (b - κ)‖ := by rw [← this]
        _ ≤ max ‖b‖ ‖b - κ‖ := unit_ratio_norm_sub_le_max _ _
        _ ≤ ‖b‖ := by
            refine max_le le_rfl ?_
            by_contra hc
            push_neg at hc
            have h3 : ‖κ‖ ≤ max ‖b‖ ‖b - κ‖ := by
              calc ‖κ‖ = ‖b - (b - κ)‖ := by rw [← this]
                _ ≤ max ‖b‖ ‖b - κ‖ := unit_ratio_norm_sub_le_max _ _
            rw [max_eq_right hc.le] at h3
            linarith
  rw [hb]; exact hab

end GlobalTheory.FlatModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChowLemmaProjectiveModification
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.FormalAlg

theorem exists_isProper_isImmersion_isProjOver : ∀ (R : Type) [CommRing R] [IsNoetherianRing R], ∀ (W : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)), IsSeparated f → LocallyOfFiniteType f → QuasiCompact f → Nonempty W → ∃ (W' P : Scheme.{0}) (π : W' ⟶ W) (q : W' ⟶ P) (s : P ⟶ Spec (CommRingCat.of R)) (U : W.Opens), IsProper π ∧ (U : Set W).Nonempty ∧ IsIso (π ∣_ U) ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver s ∧ IsImmersion q ∧ q ≫ s = π ≫ f := by
  first
  | exact @_root_.GlobalTheory.DenseClosedAffineSubsets.chow
  | exact _root_.GlobalTheory.DenseClosedAffineSubsets.chow
  | (apply _root_.GlobalTheory.DenseClosedAffineSubsets.chow <;> assumption)
  | (intros; apply _root_.GlobalTheory.DenseClosedAffineSubsets.chow <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DenseClosedAffineSubsets.chow <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DenseClosedAffineSubsets.chow ..)

end GlobalTheory.FormalAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassSumNormEqOfUniqueLeast
section
open GlobalTheory.Poinc
open Classical

namespace GlobalTheory.UPoinc

theorem classSum_norm_eq_of_unique_least : ∀ (p : ℕ) [Fact p.Prime] (X Y : Type) [AddCommGroup X] [AddCommGroup Y] (e : X ≃+ Y) (β : LinearMap.BilinForm ℤ X) (be : LinearMap.BilinForm ℤ Y) (sc sc' : ℝ), 0 < sc → (∀ a b, sc * (β a b : ℝ) = sc' * (be (e a) (e b) : ℝ)) → ∀ (m : ℕ) (t : Y → PadicAlgCl p), (∀ μ, ‖t μ‖ ≤ Real.exp (-(sc' * (be μ μ : ℝ) / 2))) → ∀ (v : PadicAlgCl p) (ν : Y), (∀ δ : ℝ, 0 < δ → ∃ S₀ : Finset Y, ∀ S : Finset Y, (∀ μ ∈ S, CongMod m μ ν) → (∀ μ ∈ S₀, CongMod m μ ν → μ ∈ S) → ‖v - ∑ μ ∈ S, t μ‖ ≤ δ) → ∀ μ : X, CongMod m (e μ) ν → ‖t (e μ)‖ = Real.exp (-(sc' * (be (e μ) (e μ) : ℝ) / 2)) → (∀ μ' : X, CongMod m μ' μ → μ' ≠ μ → β μ μ < β μ' μ') → ‖v‖ = Real.exp (-(sc * (β μ μ : ℝ)) / 2) := by
  intro p _ X Y _ _ e β be sc sc' hsc hid m t ht v ν hv μ hμν htμ hmin
  have hR' : ‖t (e μ)‖ = Real.exp (-(sc * (β μ μ : ℝ)) / 2) := by
    rw [htμ, hid μ μ]; congr 1; ring
  have hlt1 : Real.exp (-(sc * ((β μ μ : ℝ) + 1)) / 2) < Real.exp (-(sc * (β μ μ : ℝ)) / 2) :=
    Real.exp_lt_exp.2 (by nlinarith)
  have hbound : ∀ y : Y, CongMod m y ν → y ≠ e μ →
      ‖t y‖ ≤ Real.exp (-(sc * ((β μ μ : ℝ) + 1)) / 2) := by
    intro y h1 h2
    obtain ⟨w1, hw1⟩ := h1
    obtain ⟨w2, hw2⟩ := hμν
    have hx : CongMod m (e.symm y) μ := by
      refine ⟨e.symm (w1 - w2), ?_⟩
      apply e.injective
      rw [e.apply_symm_apply, map_add, map_nsmul, e.apply_symm_apply, hw1, hw2, smul_sub]
      abel
    have hne : e.symm y ≠ μ := by
      intro h; apply h2; rw [← h, e.apply_symm_apply]
    have hlt := Int.add_one_le_of_lt (hmin (e.symm y) hx hne)
    have hle : (β μ μ : ℝ) + 1 ≤ (β (e.symm y) (e.symm y) : ℝ) := by exact_mod_cast hlt
    calc ‖t y‖ ≤ Real.exp (-(sc' * (be y y : ℝ) / 2)) := ht y
      _ = Real.exp (-(sc * (β (e.symm y) (e.symm y) : ℝ)) / 2) := by
          have h3 := hid (e.symm y) (e.symm y)
          rw [e.apply_symm_apply] at h3
          rw [h3]; congr 1; ring
      _ ≤ Real.exp (-(sc * ((β μ μ : ℝ) + 1)) / 2) := Real.exp_le_exp.2 (by nlinarith)
  have hRpos : 0 < Real.exp (-(sc * (β μ μ : ℝ)) / 2) := Real.exp_pos _
  obtain ⟨S₀, hS₀⟩ := hv (Real.exp (-(sc * (β μ μ : ℝ)) / 2) / 2) (by positivity)
  have hSc : ∀ x ∈ insert (e μ) (S₀.filter (fun x => CongMod m x ν)), CongMod m x ν := by
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact hμν
    · exact (Finset.mem_filter.1 hx).2
  have hclose := hS₀ (insert (e μ) (S₀.filter (fun x => CongMod m x ν))) hSc
    (fun x hx hc => Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hx, hc⟩))
  set S := insert (e μ) (S₀.filter (fun x => CongMod m x ν)) with hSdef
  have hsum : ∑ x ∈ S, t x = t (e μ) + ∑ x ∈ S.erase (e μ), t x :=
    (Finset.add_sum_erase S t (Finset.mem_insert_self _ _)).symm
  have hrest : ‖∑ x ∈ S.erase (e μ), t x‖ ≤ Real.exp (-(sc * ((β μ μ : ℝ) + 1)) / 2) := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (Real.exp_pos _).le
    intro x hx
    exact hbound x (hSc x (Finset.mem_of_mem_erase hx)) (Finset.ne_of_mem_erase hx)
  have hnS : ‖∑ x ∈ S, t x‖ = Real.exp (-(sc * (β μ μ : ℝ)) / 2) := by
    rw [hsum, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hR']; linarith), hR']
    exact max_eq_left (by linarith)
  have hv' : v = (v - ∑ x ∈ S, t x) + ∑ x ∈ S, t x := by abel
  rw [hv', IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hnS]; linarith), hnS]
  exact max_eq_right (by linarith)

end GlobalTheory.UPoinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClearingIntegerShortSeriesIntegralCoprimeLevel
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open GlobalTheory.CovInt IsDedekindDomain
open MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out Formalism.MainNotions.ModuliIntegralCharts.H1 ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt GlobalTheory.PlaceInt.ShortTriv GlobalTheory.IntCuspLat GlobalTheory.ShortBound
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section

namespace GlobalTheory.CovInt

set_option maxHeartbeats 1000000 in

theorem smul_intZ_nonneg_coprime : ∀ (D : D7) (H : Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ)
    (d : DeltaDat Xo c n) [StarRing (𝓞 D.host.E)], d.IsLev → IsNab d.Xo₂ d.c₂ d.nab₂ →
    (∀ (k : Type) [Field k] [Algebra d.c₂.F k] (y₂ : FrPt d.Xo₂ d.c₂ k), evR d.Xo₂ d.c₂ d.cδ y₂ = 1) →
    (∀ (x0 : Fin n → Dw.La) (q : Fin n → LevQ Dw d.l₂), IsIntegral ℤ (d.w x0 q)) → d.l₂.M ≠ 0 →
    ∀ (Λ : GenLat D.host.E n) (N : ℕ), Λ.Unimod → Λ.TrivAt d.l₂.M → Λ.LevOK N d.l₂.M →
    ∀ (w : (D.host.E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmL c Λ w →
    ∀ (x0 : Fin n → Dw.La) (g : Rul Xo c), g ∈ sec Xo c w n → IsShortRule Xo c d Λ N x0 P g →
    ∀ la : HeightOneSpectrum (𝓞 c.F), (∀ ℓ : ℕ, ℓ.Prime → (ℓ : 𝓞 c.F) ∈ la.asIdeal → ¬ ℓ ∣ d.l₂.M) →
    ∀ s : c.F, Submodule.span (𝓞 c.F) {s} * ∏ τ : D.host.E →+* ℂ, idealAt c Λ.Ln τ ^ Dw.mult τ ≤
      ∏ τ : D.host.E →+* ℂ, idealAt c Λ.La τ ^ Dw.mult τ →
    ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v ((s * betaH (Dw := Dw) c Λ * (intZ D Dw d.l₂ n w : c.F)) • g) := by
  intro D H Dw l Xo c n d _ hlev hnab hroot hwi hM0 Λ N hU hTM hN w P hP x0 g hsec hR la hla s hs v hv
  have hroot1 : ∀ (k : Type) [Field k] [Algebra d.c₂.F k] (y₂ : FrPt d.Xo₂ d.c₂ k),
      evR d.Xo₂ d.c₂ d.cδ y₂ ^ 1 = 1 := fun k _ _ y₂ => by rw [pow_one]; exact hroot k y₂
  have hβ : betaH (Dw := Dw) c Λ ≠ 0 := by
    unfold betaH
    split_ifs with h
    exacts [h.choose_spec.1, one_ne_zero]
  have hc0 : Nat.card (Fin n → LevQ Dw d.l₂) ≠ 0 := by
    rw [GlobalTheory.PlaceInt.card_fun_levQ]; exact pow_ne_zero _ hM0
  obtain ⟨P₀, hP₀⟩ : ∃ P₀ : ℕ, P₀ = (NumberField.discr D.host.E).natAbs := ⟨_, rfl⟩
  have hP0 : P₀ ≠ 0 := hP₀ ▸ Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero _)
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = P₀ ^ Formalism.L2.Pj.DF Dw w * d.l₂.M ^ Formalism.L2.Pj.DF Dw w *
    Nat.card (Fin n → LevQ Dw d.l₂) := ⟨_, rfl⟩
  have hK0 : K ≠ 0 := hK ▸ mul_ne_zero (mul_ne_zero (pow_ne_zero _ hP0) (pow_ne_zero _ hM0)) hc0
  have hKZ : intZ D Dw d.l₂ n w = K := by rw [intZ, hK, hP₀]; ring
  rw [hKZ, mul_comm]
  obtain ⟨⟨_, Tc, io, e, ho, yI, hy, eta, heta, rfl⟩, rfl⟩ := hv
  show 0 ≤ nval Tc.V e (evI yI _)
  rw [evI_smul]
  obtain ⟨-, ef2, -⟩ := GlobalTheory.PlaceInt.eF_transfer _ _ _ _ Xo c n d Λ
  obtain ⟨T', iT, r, io₂, y₂, C, ζ, z, tp, F, hr, hiT, hfr, hio, hC, hrat, hζ, hz, hgi, htp, hF, hval⟩ :=
    GlobalTheory.PlaceInt.short_value_on_cover _ _ _ _ Xo c n d hlev hnab 1 hroot1 Λ N hU hTM hN w P hP x0 g hsec hR
      Tc io yI hy
  haveI : CharZero T'.Fr := algebraRat.charZero _
  have ho' := ho.bc iT hr hiT
  have he' : 0 < r * e := ho'.1
  have heR : (0 : ℝ) < ((r * e : ℕ) : ℝ) := by exact_mod_cast he'
  rw [← nval_bc iT hr hiT e, map_mul, hval, ← hio]
  obtain ⟨ℓ, hℓ, hu⟩ := GlobalTheory.ShortBound.exists_resChar T' hfr
  have hmem : (ℓ : 𝓞 c.F) ∈ la.asIdeal := by
    by_contra hnm
    have h2 := ho'.2 (ℓ : c.F)
    have hv1 : la.valuation c.F (ℓ : c.F) = 1 := by
      rw [← map_natCast (algebraMap (𝓞 c.F) c.F)]
      exact la.valuation_eq_one_iff_notMem.2 hnm
    have hv0 : vLa la (ℓ : c.F) = 0 := by simp [vLa, hv1]
    rw [map_natCast, hv0, mul_zero] at h2
    have h0 : (ℓ : T'.V) ≠ 0 := fun h0 => by
      have : algebraMap T'.V T'.Fr (ℓ : T'.V) = 0 := by rw [h0, map_zero]
      rw [map_natCast] at this
      exact hℓ.ne_zero (by exact_mod_cast this)
    have h3 := GlobalTheory.PlaceExtField.vV_pos (K' := T'.Fr) h0 hu
    rw [map_natCast] at h3
    omega
  have hd : ¬ ℓ ∣ d.l₂.M := hla ℓ hℓ hmem
  obtain ⟨α, hα1⟩ : ∃ α : ℕ, α = 1 := ⟨1, rfl⟩
  obtain ⟨α', hα'⟩ : ∃ α' : ℕ, d.l₂.M = α * α' := ⟨d.l₂.M, by rw [hα1, Nat.one_mul]⟩
  have ha0 : α ≠ 0 := by rw [hα1]; exact one_ne_zero
  have ha0' : α' ≠ 0 := right_ne_zero_of_mul (hα' ▸ hM0)
  have hch := GlobalTheory.PlaceInt.HostChart.chBound_host D _ Dw _ d.Xo₂ d.c₂ hnab.1 T' io₂ y₂ C (r * e) he' w n _ le_rfl
  haveI := Nat.finite_of_card_ne_zero hc0
  have hu0 : io₂ (nrm Dw d.c₂ w (α : 𝓞 D.host.E)) ≠ 0 :=
    (map_ne_zero io₂).2 (nrm_ne_zero _ _ (Nat.cast_ne_zero.2 ha0))
  have hsA : ∀ A : GlobalTheory.PlaceInt.Adapt Λ N ℓ, 0 ≤ nval T'.V (r * e)
      (io₂ (d.eF s * ∏ τ : D.host.E →+* ℂ, embK d.c₂ τ A.p.det ^ Dw.mult τ)) := by
    intro A
    have h := GlobalTheory.T.intersectedLattice_detIdeal_typeNorm_integral D.host.E H Dw l c n Λ N d.l₂.M ℓ hN hℓ A s hs T'
      (io₂.comp (d.eF : c.F →+* d.c₂.F)) hu (r * e)
    simpa [embK, map_prod, map_pow, GlobalTheory.PlaceInt.eF_embF] using h
  obtain ⟨t1, -⟩ := GlobalTheory.TorsFac.factorisation D.host.E H Dw d.l₂ d.Xo₂ N ℓ hN.1 hN.2.1 hℓ
  obtain ⟨n', j, -, -, h5⟩ := t1 hd
  have hcop : ∀ q, ∃ m : ℕ, Nat.Coprime m ℓ ∧ ∀ b, tp q b ^ m = 1 := fun q => by
    have hk : ∀ b, KilledBy d.Xo₂ d.l₂.Mb (tp q b ^ N) := fun b => by
      rw [(htp q b).1]; exact levPt_killed d.Xo₂ _ _
    choose i hi using fun b => (h5 _ _ (hk b) (htp q b).2).2.2
    refine ⟨d.l₂.M ^ (∑ b, i b), Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hℓ).2 hd).symm, fun b => ?_⟩
    obtain ⟨m, hm⟩ : d.l₂.M ^ i b ∣ d.l₂.M ^ (∑ b, i b) :=
      pow_dvd_pow _ (Finset.single_le_sum (f := i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ b))
    rw [hm, pow_mul, hi b, one_pow]
  have hN2 : ∀ q b, tp q b ^ (N ^ 2) = 1 := fun q b => by
    have hk : KilledBy d.Xo₂ d.l₂.Mb (tp q b ^ N) := by rw [(htp q b).1]; exact levPt_killed d.Xo₂ _ _
    exact (h5 _ _ hk (htp q b).2).1
  have hterm := fun q => GlobalTheory.T.shortSeries_bound_coprime_torsion_mul D.host.E H Dw d.l₂ d.Xo₂ d.c₂ hnab.1 T' io₂ y₂ C hC _ hnab (r * e) _ w n he'
    hch ℓ hℓ hu Λ N d.l₂.M hU hN _ (ef2 _ P hP).1 z (tp q) (F q) hz hgi (hN2 q) (hF q) hrat (hcop q) (d.eF s) hsA
  have hX1 : ∀ {J : Type} (bb : T'.Fr) (X : J → T'.Fr) (ρ : ℝ),
      (∀ q, ((-ρ : ℝ) : EReal) ≤ nval T'.V (r * e) (bb * X q)) →
      ∀ q, ((-ρ : ℝ) : EReal) ≤ nval T'.V (r * e) (io₂ (nrm Dw d.c₂ w (α : 𝓞 D.host.E)) * bb * X q) := by
    intro J bb X ρ h q
    rw [hα1, Nat.cast_one, nrm_one, map_one, _root_.one_mul]
    exact h q
  have key := le_nval_avg (V := T'.V) (r * e) (fun q => io₂ (d.w x0 q)) _ ζ _
    ((Nat.card (Fin n → LevQ Dw d.l₂) : ℕ) : T'.Fr) _ 1 one_pos hζ hu0 (by exact_mod_cast hc0)
    (fun q => map_isIntegral_int io₂ (hwi x0 q)) _ (hX1 _ _ _ hterm)
  have hb0 : io₂ (d.eF (betaH (Dw := Dw) c Λ)) ≠ 0 := (map_ne_zero io₂).2 ((map_ne_zero d.eF).2 hβ)
  have hKv := add_le_add (le_refl (nval T'.V (r * e) (K : T'.Fr))) key
  rw [← nval_mul, nval_of_ne (Nat.cast_ne_zero.2 hK0), ← EReal.coe_add] at hKv
  refine le_trans (EReal.coe_nonneg.2 ?_) (hKv.trans (le_of_eq ?_))
  · have b0 : ∀ p : ℕ, (0 : ℝ) ≤ vV T'.V (p : T'.Fr) := fun p => by
      exact_mod_cast GlobalTheory.PlaceInt.HostChart.vV_nat_nonneg T' p
    have b1 : (vV T'.V (K : T'.Fr) : ℝ) = (Formalism.L2.Pj.DF Dw w : ℕ) * (vV T'.V (P₀ : T'.Fr) : ℝ) +
        (Formalism.L2.Pj.DF Dw w : ℕ) * ((vV T'.V (α : T'.Fr) : ℝ) + vV T'.V (α' : T'.Fr)) +
        vV T'.V ((Nat.card (Fin n → LevQ Dw d.l₂) : ℕ) : T'.Fr) := by
      rw [hK, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow,
        vV_mul (mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 hP0)) (pow_ne_zero _ (Nat.cast_ne_zero.2 hM0)))
          (Nat.cast_ne_zero.2 hc0),
        vV_mul (pow_ne_zero _ (Nat.cast_ne_zero.2 hP0)) (pow_ne_zero _ (Nat.cast_ne_zero.2 hM0)),
        vV_pow (Nat.cast_ne_zero.2 hP0), vV_pow (Nat.cast_ne_zero.2 hM0)]
      conv_lhs => rw [show ((d.l₂.M : ℕ) : T'.Fr) = (α : T'.Fr) * (α' : T'.Fr) by rw [hα', Nat.cast_mul],
        vV_mul (Nat.cast_ne_zero.2 ha0) (Nat.cast_ne_zero.2 ha0')]
      push_cast
      ring
    have b2 : (vV T'.V (io₂ (nrm Dw d.c₂ w (α : 𝓞 D.host.E))) : ℝ) = (Formalism.L2.Pj.DF Dw w : ℕ) * vV T'.V (α : T'.Fr) := by
      rw [nrm_nat, map_pow, map_natCast, vV_pow (Nat.cast_ne_zero.2 ha0)]
      push_cast
      ring
    have b3 : ∑ p ∈ D.host.condN.primeFactors, (vV T'.V (p : T'.Fr) : ℝ) / (r * e : ℕ) *
        D.host.vdH p * (Formalism.L2.Pj.DF Dw w : ℝ) / 2 ≤ (Formalism.L2.Pj.DF Dw w : ℕ) * (vV T'.V (P₀ : T'.Fr) : ℝ) / (r * e : ℕ) := by
      have h := ram_sum_le_vV_discr D.host.E T' _ (fun p (hp : p ∈ D.host.condN.primeFactors) => Nat.prime_of_mem_primeFactors hp)
        (r * e) (Formalism.L2.Pj.DF Dw w)
      rw [Nat.cast_pow, vV_pow (Nat.cast_ne_zero.2 (hP₀ ▸ hP0)), Int.cast_mul, Int.cast_natCast] at h
      rw [hP₀]
      exact h
    have b4 : (0 : ℝ) ≤ (Formalism.L2.Pj.DF Dw w : ℕ) * (vV T'.V (α' : T'.Fr) : ℝ) / (r * e : ℕ) :=
      div_nonneg (mul_nonneg (Nat.cast_nonneg _) (b0 _)) heR.le
    rw [b1, b2, add_div, add_div, mul_add, add_div]
    linarith
  · congr 1
    simp only [map_mul, map_inv₀, map_natCast]
    field_simp

end GlobalTheory.CovInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypeFromConjugateComplementStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_type_from_conjugate_complement : ∀ D : D7, letI : IsCMField D.host.E := D.host.isCMField_hostE; (∀ τ : D.host.E →+* ℂ, τ ∈ GlobalTheory.MassLink.psi D ↔ ComplexEmbedding.conjugate τ ∉ GlobalTheory.MassLink.psi D) ∧ ∃ eΨ : D.what₂.Tau ≃ GlobalTheory.MassLink.psi D, ∀ ρ, ((eΨ ρ : GlobalTheory.MassLink.psi D) : D.host.E →+* ℂ) = TH.tauE D ρ := by
  first | exact @GlobalTheory.MassLink.psi_cmType_equiv | exact GlobalTheory.MassLink.psi_cmType_equiv | (intros; apply GlobalTheory.MassLink.psi_cmType_equiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffValuationLossFinsetSumAndInvPowStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)
open MeasureTheory ValuativeRel GlobalTheory.UnfoldLoss

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeffValuationLoss_finsetSum_and_invPow : ∀ {D : D7} (w : PlL D),
    (∀ {ι : Type} (s : Finset ι) (z : ι → ℂ) (a : ℝ), (∀ i ∈ s, LossLe w (z i) a) → LossLe w (∑ i ∈ s, z i) a) ∧
    ∀ q M : ℕ, 0 < q → LossLe w ((((q : ℝ)⁻¹ ^ M : ℝ)) : ℂ) ((M : ℝ) * (vw w ((q : ℕ) : D.what₂.LL) : ℝ)) := by
  first | exact @GlobalTheory.LossSum.lossLe_sum_and_pow | exact GlobalTheory.LossSum.lossLe_sum_and_pow | (intros; apply GlobalTheory.LossSum.lossLe_sum_and_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnPolynomialLocalDepthEqPlaceDepth
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ColDepth

open GlobalTheory.FGDepth

section Ultra

variable {C : Type} [Field C] (v : AddValuation C (WithTop ℝ))

theorem val_eq_of_lt_sub (x y : C) (h : v x < v (x - y)) : v y = v x := by
  have h1 : min (v x) (v (x - y)) ≤ v (x - (x - y)) := AddValuation.map_sub v _ _
  rw [sub_sub_cancel, min_eq_left h.le] at h1
  have h2 : min (v y) (v (x - y)) ≤ v (y + (x - y)) := AddValuation.map_add v _ _
  rw [add_sub_cancel] at h2
  rcases le_total (v y) (v (x - y)) with h3 | h3
  · rw [min_eq_left h3] at h2
    exact le_antisymm h2 h1
  · rw [min_eq_right h3] at h2
    exact absurd (lt_of_le_of_lt h2 h) (lt_irrefl _)

theorem iInf_le_of_approx {S U : Type} (a : S → C) (b : U → C)
    (h : ∀ (s : S) (N : ℕ), ∃ t, ((N : ℝ) : WithTop ℝ) ≤ v (a s - b t)) :
    ⨅ t, toE (v (b t)) ≤ ⨅ s, toE (v (a s)) := by
  refine le_iInf fun s => ?_
  by_cases hs : v (a s) = ⊤
  · rw [hs]
    exact le_top
  · obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 hs
    obtain ⟨N, hN⟩ := exists_nat_gt r
    obtain ⟨t, ht⟩ := h s N
    have hlt : v (a s) < v (a s - b t) :=
      lt_of_lt_of_le (by rw [← hr]; exact WithTop.coe_lt_coe.2 hN) ht
    rw [← val_eq_of_lt_sub v _ _ hlt]
    exact iInf_le _ t

theorem iInf_eq_of_approx {S U : Type} (a : S → C) (b : U → C)
    (h1 : ∀ (s : S) (N : ℕ), ∃ t, ((N : ℝ) : WithTop ℝ) ≤ v (a s - b t))
    (h2 : ∀ (t : U) (N : ℕ), ∃ s, ((N : ℝ) : WithTop ℝ) ≤ v (a s - b t)) :
    ⨅ s, toE (v (a s)) = ⨅ t, toE (v (b t)) := by
  refine le_antisymm ?_ (iInf_le_of_approx v a b h1)
  refine iInf_le_of_approx v b a fun t N => ?_
  obtain ⟨s, hs⟩ := h2 t N
  exact ⟨s, by rwa [AddValuation.map_sub_swap]⟩

end Ultra

theorem nuLocOf_eq_nuP : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e → ∀ (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (cx : Lt1 Dw → ℕ) (n : ℕ) (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V), IsCols c T io p cx B → ∀ k : ℕ, nuLocOf Ch (vV T.V (p : T.Fr)).toNat k (polyT B cx) = nuP p y cx := by
  intro E _ _ _ H Dw l Xo c p _ la T io e ho y Ch cx n B hB k
  letI := H.starRing
  obtain ⟨X⟩ := nonempty_valExt_of_overLa la ho
  have hmid : GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.nuLocX_vp Ch X cx B k = GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.nuH_vp Ch X cx := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.nuLocX_vp GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.nuH_vp depth
    refine iInf_eq_of_approx (vX_vp X)
      (fun g : {g : PS X.C n (chD Ch.ch) // MvIsInt (vX_vp X) g} => GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.nabX Ch X cx B k g.1)
      (fun f : {f : MvPowerSeries (Σ _ : GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.Col cx, Fin (chD Ch.ch)) X.C // MvIsInt (vX_vp X) f} =>
        derivAt0 (GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.polyH X.C cx) (MvPowerSeries.subst (GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.expH Ch X cx) f.1))
      (fun g N => ?_) (fun f N => ?_)
    · obtain ⟨f, hf, hN⟩ := GlobalTheory.T.exists_integral_germ_on_columns_same_value E H Dw l Xo c p la T io e ho y Ch X cx n B hB N k g.1 g.2
      exact ⟨⟨f, hf⟩, hN⟩
    · obtain ⟨g, hg, hN⟩ := GlobalTheory.T.exists_integral_germ_on_copies_same_value E H Dw l Xo c p la T io e ho y Ch X cx n B hB N k f.1 f.2
      exact ⟨⟨g, hg⟩, hN⟩
  exact (GlobalTheory.T.localDepth_over_dvr_eq_over_closed_field E H Dw l Xo c p la T io e ho y Ch X cx n B k).trans
    (hmid.trans (GlobalTheory.T.isotropicFactor_depth_eq_sum_factor_depths E H Dw l Xo c p T io y Ch X cx).1)

end GlobalTheory.ColDepth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComparisonStatementHoldsStatement
section
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comparison_statement_holds : CmpSt := by
  first | exact @GlobalTheory.FlatModel.cmpSt_holds | exact GlobalTheory.FlatModel.cmpSt_holds | (intros; apply GlobalTheory.FlatModel.cmpSt_holds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformisationComponentsCovolumeEqStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexUniformisation_components_covolume_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → (∀ p : ℕ, p.Prime → l.GoodAt p) → 1 ≤ Dw.p → 1 ≤ Dw.q → ∀ k k' : U.Comp, GlobalTheory.TrueCx.covol (U.X k) = GlobalTheory.TrueCx.covol (U.X k') := by
  first | exact @GlobalTheory.EqCovol.covol_eq_of_isUnf | exact GlobalTheory.EqCovol.covol_eq_of_isUnf | (intros; apply GlobalTheory.EqCovol.covol_eq_of_isUnf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentGeometricallyIrreducibleStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.component_geometrically_irreducible : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l), FnAlgClosed Xo c → ∀ Z : Comp Xo c,
    ∃ U : (Xo.XF c).Opens, (U : Set (Xo.XF c)) = Z ∧ ∀ (k : Type) [Field k] (f : c.F →+* k),
      IrreducibleSpace ↑(pullback (U.ι ≫ pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) (spMap f)) := by
  first | exact @GlobalTheory.GeomIrrComp.exists_open_irreducibleSpace_baseChange | exact GlobalTheory.GeomIrrComp.exists_open_irreducibleSpace_baseChange | (intros; apply GlobalTheory.GeomIrrComp.exists_open_irreducibleSpace_baseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentStabilizerActsByLevelChangeStatement
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.componentStabilizer_acts_by_levelChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → l.A = 1 → ∀ S : Subgroup (LevelAut Dw l), ∃ (Γ : Subgroup (LevelAut Dw l)) (ρ : Γ →* Aut (V₀ Y Z)), Γ ≤ S ∧ ActsBy Γ.subtype ρ ∧ ∀ h ∈ S, ∀ y : FrPt Xo c ℂ, LiesOn Z y → LiesOn Z (move Xo c h⁻¹ y) → h ∈ Γ := by
  first | exact @GlobalTheory.CompLevelStab.stab_acts | exact GlobalTheory.CompLevelStab.stab_acts | (intros; apply GlobalTheory.CompLevelStab.stab_acts <;> assumption)
end

