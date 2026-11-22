import Mathlib
import Formalism.SharpRestriction.Divisibility.ThetaNormsAndLinks
import Formalism.LocalRingCardinality.DataParams
import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle0003
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0003
import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes

-- bundled from Formalism.SharpRestriction.Divisibility.ChainOperators.GeometricGenericity
section
namespace ConditionalKappaBounds.G2

open Formalism.BasicNotions Formalism.MainNotions

def UCard (D : D7) : Prop :=
  (Nat.card D.nexp.U : ℝ) = ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) ^ (D.R.f * (D.R.r * (D.R.r - 1) / 2))

theorem geometric_generic_of_hypothesis (hc : GaussianProductPowerBound) (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (hU : UCard D) : ThetaNormsAndLinks.admG2 D := by
  obtain ⟨Y, hY8, -, -, hYg⟩ := P.g_Y
  have hf1 : 1 ≤ D.R.f := by
    unfold Ranks.f Ranks.n; have := D.R.ord_pos; omega
  have hfk : D.R.f ≤ D.R.k := D.R.f_le_k
  have hb : 2 ≤ L.sc.b := by
    unfold Scale.b Scale.L
    have h1 : 1 < L.sc.x ^ L.sc.eps := Real.one_lt_rpow L.sc.one_lt_alt L.sc.eps_pos
    have h2 : Real.exp 1 < Real.exp (L.sc.x ^ L.sc.eps) := Real.exp_lt_exp.mpr h1
    have h3 := Real.exp_one_gt_d9
    linarith
  have h := hc D.R.f D.R.k D.R.r L.sc.b (D.host.g 0) (D.host.g 1) hf1 hfk hb
    (hY8.trans (hYg 0).1) (hY8.trans (hYg 1).1)
  unfold ThetaNormsAndLinks.admG2 ThetaNormsAndLinks.eSh LiftErrorLocal.delq
  rw [hU]
  exact h

theorem uCard_of_tied (D : D7) (T : Formalism.L2.NExpTied D) : UCard D := by
  unfold UCard
  rw [Formalism.L2.NExpTied.uCard T]
  push_cast
  ring

theorem geometric_generic_of_layer_two (hc : GaussianProductPowerBound) (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (T : Formalism.L2.NExpTied D) :
    ThetaNormsAndLinks.admG2 D :=
  geometric_generic_of_hypothesis hc D L P (uCard_of_tied D T)

end ConditionalKappaBounds.G2

namespace Formalism.MainNotions.DIV.GeometricGenericity

open Formalism.BasicNotions Formalism.MainNotions

theorem geometric_generic_of_layer_two (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (T : Formalism.L2.NExpTied D) : ThetaNormsAndLinks.admG2 D :=
  ConditionalKappaBounds.G2.geometric_generic_of_layer_two geometric_product_power D L P T

end Formalism.MainNotions.DIV.GeometricGenericity
end

-- bundled from Formalism.SharpRestriction.Divisibility.ChainOperators.PerCol
section
noncomputable section

open Formalism.BasicNotions

namespace Formalism.MainNotions.DIV

theorem chainOpM_smul {Rg : Type} [CommSemiring Rg] {ι : ℕ → Type} [∀ j, Fintype (ι j)]
    {M : ℕ → Type} [∀ j, AddCommMonoid (M j)] [∀ j, Module Rg (M j)]
    (w : ∀ j, ι j → Rg) (Km : ∀ j, ι j → ι (j + 1) → (M j →ₗ[Rg] M (j + 1))) (m : ℕ) (c : Rg) (f : ι 0 → M 0) :
    Formalism.ThetaLiftIndependence.chainOpM w Km m (c • f) = c • Formalism.ThetaLiftIndependence.chainOpM w Km m f := by
  induction m with
  | zero => rfl
  | succ m ih =>
    show Formalism.ThetaLiftIndependence.kerOpM (w m) (Km m) (Formalism.ThetaLiftIndependence.chainOpM w Km m (c • f)) =
      c • Formalism.ThetaLiftIndependence.kerOpM (w m) (Km m) (Formalism.ThetaLiftIndependence.chainOpM w Km m f)
    rw [ih]
    funext j
    simp only [Formalism.ThetaLiftIndependence.kerOpM, Pi.smul_apply, map_smul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_comm]

theorem col_smul {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R} (C : ColumnChain R ι hc)
    (c : ℂ) (f : C.cls 0 → C.Y 0 → ℂ) : C.col (c • f) = c • C.col f := chainOpM_smul C.wt C.Kmap R.m c f

theorem ptilCol_smul {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R} {C : ColumnChain R ι hc} (P : PeriodMap R C)
    (c : ℂ) (f : C.cls 0 → C.Y 0 → ℂ) (F : P.Mt) : P.PtilCol (c • f) F = c * P.PtilCol f F := by
  show P.Ptil (C.col (c • f)) F = c * P.Ptil (C.col f) F
  rw [col_smul]
  simp only [Formalism.BasicNotions.PeriodMap.Ptil, map_smul, LinearMap.smul_apply, smul_eq_mul]

theorem perColSmul (D : D7) : WeightDegreeSizes.PerColSmul D := by
  intro u μ c φ F
  by_cases h : μ = D.what₂.mu0
  · subst h
    rw [D.perCol_base_eq_PtilCol, D.perCol_base_eq_PtilCol, map_smul]
    exact ptilCol_smul _ c _ _
  · rw [D.perCol_tie u μ h, D.perCol_tie u μ h, map_smul]
    have : (((c • D.eMu u φ : (D.mem u).A.Mram)) : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) =
        c • ((D.eMu u φ : (D.mem u).A.Mram) : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) := rfl
    rw [this, map_smul]
    exact ptilCol_smul _ c _ _

end Formalism.MainNotions.DIV

end
end

-- bundled from Formalism.SharpRestriction.Divisibility.ChainOperators.ProjectorStatementOfIntegrality
section
noncomputable section

open Formalism.BasicNotions

namespace Formalism.MainNotions.DIV

def AIntO (D : D7) : Prop :=
  ∀ (i : D.ntw.Tw) (b : Bool), ∃ c : MonoidAlgebra (D.ntw.O i) (G0g D.nd),
    MonoidAlgebra.map (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).toAddMonoidHom c =
      ((D.what₂.restRowsFiniteGroupCard : ℕ) : FractionRing (D.ntw.O i)) • D.nexp.eAlg i b

theorem projector_statement_of_integrality (D : D7) (h1 : AIntO D) (hS : ThetaNormsAndLinks.SupLatticeGroupStable D) : PDVN.ConjugationNormInvariance D := by
  refine ⟨h1, ?_⟩
  rintro i j hj b _ ⟨x, hx, rfl⟩
  obtain ⟨hxB, hxF⟩ := hx
  obtain ⟨c, hc⟩ := h1 i b
  have hz : IntegralHeckeForms.AO D.nexp i j b x = IntegralHeckeForms.zO D.nexp i j b c x := by
    simp only [IntegralHeckeForms.AO, IntegralHeckeForms.zO, IntegralHeckeForms.eO, IntegralHeckeForms.eG, hc, LinearMap.smul_apply, LinearMap.coe_restrictScalars,
      Nat.cast_smul_eq_nsmul]
    rw [map_nsmul, LinearMap.smul_apply]
  have hB : IntegralHeckeForms.AO D.nexp i j b x ∈ D.nexp.Bsup i j b := by
    rw [hz]
    exact ThetaNormsAndLinks.zO_mem D i j b (fun g => hS i j hj b g) c x hxB
  have hV : IntegralHeckeForms.AO D.nexp i j b x ∈ IntegralHeckeForms.V0 D.nexp i j b := by
    have e : IntegralHeckeForms.AO D.nexp i j b x = IntegralHeckeForms.eG D.nexp i j b ((D.what₂.restRowsFiniteGroupCard : ℕ) • x) := by
      simp only [IntegralHeckeForms.AO, IntegralHeckeForms.eO, LinearMap.smul_apply, LinearMap.coe_restrictScalars, Nat.cast_smul_eq_nsmul, map_nsmul]
    rw [e]
    exact ⟨_, Submodule.smul_of_tower_mem _ _ hxF, rfl⟩
  exact ⟨⟨hB, ThetaNormsAndLinks.hermFramePairNormalForm_frameSpan_le_of_generators D i j b hV⟩, hV⟩

end Formalism.MainNotions.DIV

end
end

