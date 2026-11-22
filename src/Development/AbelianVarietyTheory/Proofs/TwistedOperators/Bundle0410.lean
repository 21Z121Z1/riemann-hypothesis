import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0026
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0362
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0386
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1425
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0395
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0372
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0387
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0397
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0174
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0176
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0350
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1368

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRankSubmoduleChainBounded
section
noncomputable section

open GlobalTheory.SplitWeil GlobalTheory.ThetaGLSub GlobalTheory.ThetaGLRank GlobalTheory.SmGL

namespace GlobalTheory.ThetaGLLayer

theorem exists_chain_bound {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] (h : IsFiniteLength R M) :
    ∃ L : ℕ, ∀ (r : ℕ) (s : Fin r → Submodule R M), StrictMono s → r ≤ L := by
  refine ⟨(Module.length R M).toNat + 1, fun r s hs => ?_⟩
  rcases r with _ | r
  · exact Nat.zero_le _
  let p : LTSeries (Submodule R M) := ⟨r, s, fun i => hs Fin.castSucc_lt_succ⟩
  have h1 : (r : ℕ∞) ≤ Module.length R M := by
    rw [Module.length_eq_height]
    exact (Order.length_le_height_last (p := p)).trans (Order.height_mono le_top)
  have h2 : Module.length R M ≠ ⊤ := Module.length_ne_top_iff.2 h
  have h3 : r ≤ (Module.length R M).toNat := by
    rw [← ENat.coe_le_coe, ENat.coe_toNat h2]; exact h1
  omega

theorem exists_subrep_chain_bound {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ G V} (h : HasFiniteLength π) :
    ∃ L : ℕ, ∀ (r : ℕ) (s : Fin r → Subrepresentation π), StrictMono s → r ≤ L := by
  obtain ⟨L, hL⟩ := exists_chain_bound h
  exact ⟨L, fun r s hs => hL r _ (Subrepresentation.subrepresentationSubmoduleOrderIso.strictMono.comp hs)⟩

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n m : ℕ}

theorem layer_bound_of_cover (χ : GL (Fin n) k →* ℂˣ) (ρ : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin m) k) V) (hπ : HasFiniteLength π)
    (f : V →ₗ[ℂ] (Matrix (Fin n) (Fin m) k → ℂ))
    (hf : ∀ (g : GL (Fin m) k) (v : V),
      f (π g v) - om 1 g (1 : GL (Fin n) k) (f v) ∈ aug m χ ⊔ rkSub k n m (ρ + 1))
    (hs : rkSub k n m ρ ≤ aug m χ ⊔ rkSub k n m (ρ + 1) ⊔ LinearMap.range f) :
    ∃ L : ℕ, ∀ (r : ℕ) (N : Fin r → Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ)),
      StrictMono N → (∀ i, IsSub χ (N i) ∧
        aug m χ ⊔ rkSub k n m (ρ + 1) ≤ N i ∧ N i ≤ aug m χ ⊔ rkSub k n m ρ) → r ≤ L := by
  obtain ⟨L, hL⟩ := exists_subrep_chain_bound hπ
  refine ⟨L, fun r N hN hNi => ?_⟩
  set C1 := aug m χ ⊔ rkSub k n m (ρ + 1) with hC1

  have key : ∀ i, N i = C1 ⊔ ((N i).comap f).map f := by
    intro i
    have hle : N i ≤ C1 ⊔ LinearMap.range f := by
      refine (hNi i).2.2.trans (sup_le ?_ ?_)
      · exact (le_sup_left : aug m χ ≤ C1).trans (le_sup_left : C1 ≤ C1 ⊔ LinearMap.range f)
      · exact hs
    rw [Submodule.map_comap_eq, ← sup_inf_assoc_of_le _ (hNi i).2.1]
    exact (inf_eq_left.2 hle).symm.trans (inf_comm _ _)
  let S : Fin r → Subrepresentation π := fun i =>
    ⟨(N i).comap f, fun g v hv => by
      show f (π g v) ∈ N i
      have h1 := (hNi i).1.2.2 g (f v) hv
      have h2 : f (π g v) - om 1 g (1 : GL (Fin n) k) (f v) ∈ N i := (hNi i).2.1 (hf g v)
      simpa using Submodule.add_mem _ h2 h1⟩
  have hS : StrictMono S := by
    intro i j hij
    have hle : S i ≤ S j := fun v hv => (hN hij).le hv
    refine lt_of_le_of_ne hle fun he => (hN hij).ne ?_
    have he' : (N i).comap f = (N j).comap f := congrArg Subrepresentation.toSubmodule he
    rw [key i, key j, he']
  exact hL r S hS

end GlobalTheory.ThetaGLLayer

namespace GlobalTheory.ThetaGLLayer

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n m : ℕ}

theorem rkSub_eq_bot_of_lt {ρ : ℕ} (h : m < ρ) : rkSub k n m ρ = ⊥ := by
  refine eq_bot_iff.2 fun Φ hΦ => ?_
  refine funext fun x => hΦ.2 x ?_
  have : x.rank ≤ m := by simpa using Matrix.rank_le_width x
  omega

theorem om_zero (g : GL (Fin m) k) :
    om (1 : kˣ →* ℂˣ) g (1 : GL (Fin n) k) (0 : Matrix (Fin n) (Fin m) k → ℂ) = 0 :=
  funext fun x => by simp [om]

end GlobalTheory.ThetaGLLayer

open GlobalTheory.ThetaGLLayer in

theorem GlobalTheory.ThetaGLLayer.layer_bound : GlobalTheory.FunPr.Hypotheses₂ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n m : ℕ) (χ : GL (Fin n) k →* ℂˣ), IsOpen {g | χ g = 1} → ∀ ρ : ℕ,
    ∃ L : ℕ, ∀ (r : ℕ) (N : Fin r → Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ)),
      StrictMono N → (∀ i, GlobalTheory.ThetaGLSub.IsSub χ (N i) ∧
        GlobalTheory.ThetaGLSub.aug m χ ⊔ GlobalTheory.ThetaGLRank.rkSub k n m (ρ + 1) ≤ N i ∧
        N i ≤ GlobalTheory.ThetaGLSub.aug m χ ⊔ GlobalTheory.ThetaGLRank.rkSub k n m ρ) → r ≤ L := by
  intro hP k _ _ _ _ n m χ hχ ρ
  by_cases hρ : ρ ≤ m
  · have h : ρ + (m - ρ) = m := Nat.add_sub_cancel' hρ
    obtain ⟨W, _, _, τ, hτs, hτl, f, hf, hs⟩ := GlobalTheory.T.exists_finite_length_levi_quotient k n m χ hχ ρ (m - ρ) h
    have hπ := ((hP.bernsteinZelevinskyFiniteness k).2.2.1).lower (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h)) hτs hτl
    exact layer_bound_of_cover χ ρ _ hπ f hf hs
  · have hπ : GlobalTheory.SmGL.HasFiniteLength (GlobalTheory.SmGL.ofChar (1 : GL (Fin m) k →* ℂˣ)) :=
      GlobalTheory.SmGL.hasFiniteLength_of_isIrreducible (GlobalTheory.SmGL.isIrreducible_ofChar _)
    refine layer_bound_of_cover χ ρ _ hπ 0 (fun g v => ?_) ?_
    · simp [om_zero]
    · rw [rkSub_eq_bot_of_lt (by omega)]; exact bot_le
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryAtSplitPlaceLocalBases
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

namespace GlobalTheory.UnitFv

theorem unitary_split {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl F) (π₁ π₂ : AE F E →+* Fv F v) (b₁ b₂ : GL (Fin d) (Fv F v))
  (hπ : ∀ z, π₁ (cA σ z) = π₂ z) (g : GlobalTheory.DblVac.UD σ W) :   (Matrix.fromBlocks (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (GlobalTheory.DblVac.matD g).toBlocks₁₁.map π₁ * (b₁ : Matrix (Fin d) (Fin d) (Fv F v))) (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (GlobalTheory.DblVac.matD g).toBlocks₁₂.map π₁ * (b₁ : Matrix (Fin d) (Fin d) (Fv F v)))
      (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (GlobalTheory.DblVac.matD g).toBlocks₂₁.map π₁ * (b₁ : Matrix (Fin d) (Fin d) (Fv F v))) (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (GlobalTheory.DblVac.matD g).toBlocks₂₂.map π₁ * (b₁ : Matrix (Fin d) (Fin d) (Fv F v))))ᵀ *
    Matrix.fromBlocks ((b₁ : Matrix (Fin d) (Fin d) (Fv F v))ᵀ * (incM F W.J).map π₁ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v))) 0 0 (-((b₁ : Matrix (Fin d) (Fin d) (Fv F v))ᵀ * (incM F W.J).map π₁ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v)))) *
    (Matrix.fromBlocks (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (GlobalTheory.DblVac.matD g).toBlocks₁₁.map π₂ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v))) (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (GlobalTheory.DblVac.matD g).toBlocks₁₂.map π₂ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v)))
      (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (GlobalTheory.DblVac.matD g).toBlocks₂₁.map π₂ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v))) (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (GlobalTheory.DblVac.matD g).toBlocks₂₂.map π₂ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v)))) =
  Matrix.fromBlocks ((b₁ : Matrix (Fin d) (Fin d) (Fv F v))ᵀ * (incM F W.J).map π₁ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v))) 0 0 (-((b₁ : Matrix (Fin d) (Fin d) (Fv F v))ᵀ * (incM F W.J).map π₁ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v)))) := by
  set M := GlobalTheory.DblVac.matD g with hMdef
  set J₁ : Matrix (Fin d) (Fin d) (Fv F v) := (incM F W.J).map π₁ with hJ₁
  have hg : Mᵀ * dbl (incM F W.J) * M.map (cA σ) = dbl (incM F W.J) := g.2
  have hmap := congrArg (fun X => X.map π₁) hg
  simp only [Matrix.map_mul, Matrix.transpose_map] at hmap
  have h2 : (M.map (cA σ)).map π₁ = M.map π₂ := by
    rw [Matrix.map_map]; ext i j; simp [hπ]
  have hD : (dbl (incM F W.J)).map π₁ = Matrix.fromBlocks J₁ 0 0 (-J₁) := by
    simp [dbl, Matrix.fromBlocks_map, hJ₁]
    try (ext i j; simp)
  rw [h2, hD] at hmap

  have hblk : ∀ (π : AE F E →+* Fv F v) (b : GL (Fin d) (Fv F v)),
      Matrix.fromBlocks (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * M.toBlocks₁₁.map π * (b : Matrix (Fin d) (Fin d) (Fv F v)))
        (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * M.toBlocks₁₂.map π * (b : Matrix (Fin d) (Fin d) (Fv F v)))
        (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * M.toBlocks₂₁.map π * (b : Matrix (Fin d) (Fin d) (Fv F v)))
        (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * M.toBlocks₂₂.map π * (b : Matrix (Fin d) (Fin d) (Fv F v)))
      = Matrix.fromBlocks ((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) 0 0 ((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v))
        * M.map π * Matrix.fromBlocks (b : Matrix (Fin d) (Fin d) (Fv F v)) 0 0 (b : Matrix (Fin d) (Fin d) (Fv F v)) := by
    intro π b
    have : M.map π = Matrix.fromBlocks (M.toBlocks₁₁.map π) (M.toBlocks₁₂.map π) (M.toBlocks₂₁.map π) (M.toBlocks₂₂.map π) := by
      rw [← Matrix.fromBlocks_map, Matrix.fromBlocks_toBlocks]
    rw [this, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp [Matrix.mul_assoc]
  have hmid : Matrix.fromBlocks ((b₁ : Matrix (Fin d) (Fin d) (Fv F v))ᵀ * J₁ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v))) 0 0 (-((b₁ : Matrix (Fin d) (Fin d) (Fv F v))ᵀ * J₁ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v))))
      = (Matrix.fromBlocks (b₁ : Matrix (Fin d) (Fin d) (Fv F v)) 0 0 (b₁ : Matrix (Fin d) (Fin d) (Fv F v)))ᵀ * Matrix.fromBlocks J₁ 0 0 (-J₁)
        * Matrix.fromBlocks (b₂ : Matrix (Fin d) (Fin d) (Fv F v)) 0 0 (b₂ : Matrix (Fin d) (Fin d) (Fv F v)) := by
    rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp [Matrix.mul_assoc]
  have hinv : ∀ b : GL (Fin d) (Fv F v),
      Matrix.fromBlocks (b : Matrix (Fin d) (Fin d) (Fv F v)) 0 0 (b : Matrix (Fin d) (Fin d) (Fv F v)) *
      Matrix.fromBlocks ((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) 0 0 ((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) = 1 := by
    intro b
    rw [Matrix.fromBlocks_multiply]
    simp [Matrix.fromBlocks_one]
  rw [hblk π₁ b₁, hblk π₂ b₂, hmid]
  set P₁ := Matrix.fromBlocks (b₁ : Matrix (Fin d) (Fin d) (Fv F v)) 0 0 (b₁ : Matrix (Fin d) (Fin d) (Fv F v))
  set P₂ := Matrix.fromBlocks (b₂ : Matrix (Fin d) (Fin d) (Fv F v)) 0 0 (b₂ : Matrix (Fin d) (Fin d) (Fv F v))
  set Q₁ := Matrix.fromBlocks ((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) 0 0 ((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v))
  set Q₂ := Matrix.fromBlocks ((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) 0 0 ((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v))
  have e1 : Q₁ᵀ * P₁ᵀ = 1 := by rw [← Matrix.transpose_mul, hinv b₁, Matrix.transpose_one]
  have e2 : P₂ * Q₂ = 1 := hinv b₂
  set D := Matrix.fromBlocks J₁ 0 0 (-J₁)
  calc (Q₁ * M.map π₁ * P₁)ᵀ * (P₁ᵀ * D * P₂) * (Q₂ * M.map π₂ * P₂)
      = P₁ᵀ * ((M.map π₁)ᵀ * (Q₁ᵀ * P₁ᵀ) * D * (P₂ * Q₂) * M.map π₂) * P₂ := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = P₁ᵀ * D * P₂ := by
        rw [e1, e2, Matrix.mul_one, Matrix.mul_one, hmap, Matrix.mul_assoc]

end GlobalTheory.UnitFv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilMatrixCoeffEqZeroOfDistinctEigencharactersStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate TensorProduct
open Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilMatrixCoeff_eq_zero_of_distinct_eigencharacters : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    ∀ (m : Measure (WO S T)) (X : Set (WO S T)), IsCovolOne (ratL T S) m X → ∀ F : WO S T → ℂ, IsThetaFunO ψ S T F →
    ∀ (g : GA D T) (y : WO S T) (a b : AF D.host.F), heisO ψ S T y F = ψ a • F →
    heisO ψ S T (actO S T 1 g⁻¹ y) F = ψ b • F → ψ a ≠ ψ b → ∫ w in X, om (1, g) F w * conj (F w) ∂m = 0 := by
  first | exact @GlobalTheory.TargetCoef.coef_zero_of_target_eigen | exact GlobalTheory.TargetCoef.coef_zero_of_target_eigen | (intros; apply GlobalTheory.TargetCoef.coef_zero_of_target_eigen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelProjectionFactorisation
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.PureLift

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem exists_sep (vac : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F v) → ℂ)
    (hstd : ∀ᶠ v in Filter.cofinite, vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (lam : SInf F κ →ₗ[ℂ] ℂ) (l : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ)
    (hl : {v | l v (vac v) ≠ 1}.Finite) :
    ∃ Λ : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ, ∀ (f : SInf F κ) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F v) → ℂ),
      (∀ᶠ v in Filter.cofinite, φ v = vac v) → Λ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = lam f * ∏ᶠ v, l v (φ v) := by
  first
  | exact @_root_.GlobalTheory.FiniteAdelicPoints.exists_functional_pure
  | exact _root_.GlobalTheory.FiniteAdelicPoints.exists_functional_pure
  | (apply _root_.GlobalTheory.FiniteAdelicPoints.exists_functional_pure <;> assumption)
  | (intros; apply _root_.GlobalTheory.FiniteAdelicPoints.exists_functional_pure <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FiniteAdelicPoints.exists_functional_pure <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FiniteAdelicPoints.exists_functional_pure ..)

theorem exists_pureLift : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n d : ℕ}
    (Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Z) (ψ : AddChar (AF F) ℂ),
    M.IsGood ψ → ∀ (P : Type) [AddCommGroup P] [Module ℂ P] (pr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d) →ₗ[ℂ] P)
    (N : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F → Type) [∀ v, AddCommGroup (N v)] [∀ v, Module ℂ (N v)]
    (pv : ∀ v, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] N v) (s : ∀ v, N v),
    (∀ᶠ v in Filter.cofinite, pv v (M.vac v) = s v) →
    ∃ q : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] P ⊗[ℂ] GlobalTheory.SmallThetaModules.RTens s,
      ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin d → Fv F v) → ℂ),
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
        q (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = pr f ⊗ₜ GlobalTheory.SmallThetaModules.pureT s (fun v => pv v (φ v)) := by
  intro F E _ _ _ _ _ σ n d Y Z M ψ hM P _ _ pr N _ _ pv s hs
  classical
  let b := Module.Free.chooseBasis ℂ P
  have hsep : ∀ (i : Module.Free.ChooseBasisIndex ℂ P) (l : GlobalTheory.SmallThetaModules.AdmFun s),
      ∃ Λ : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ, ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))
        (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin d → Fv F v) → ℂ), (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
        Λ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = (b.coord i) (pr f) * ∏ᶠ v, l.1 v (pv v (φ v)) := by
    intro i l
    refine exists_sep M.vac hM.std ((b.coord i).comp pr) (fun v => (l.1 v).comp (pv v)) ?_
    refine ((Filter.eventually_cofinite.1 hs).union l.2).subset fun v hv => ?_
    by_cases e : pv v (M.vac v) = s v
    · right
      simp only [Set.mem_setOf_eq, LinearMap.comp_apply, e] at hv ⊢
      exact hv
    · left
      exact e
  choose Λ hΛ using hsep
  let ι' : P ⊗[ℂ] GlobalTheory.SmallThetaModules.RTens s →ₗ[ℂ]
      (Module.Free.ChooseBasisIndex ℂ P → GlobalTheory.SmallThetaModules.AdmFun s → ℂ) :=
    (LinearMap.compLeft (GlobalTheory.SmallThetaModules.RTens s).subtype _) ∘ₗ Finsupp.lcoeFun ∘ₗ
      (TensorProduct.equivFinsuppOfBasisLeft b).toLinearMap
  have hinj : Function.Injective ι' := by
    intro t t' h
    apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
    ext i : 1
    apply Subtype.ext
    exact congrFun h i
  obtain ⟨r, hr⟩ := ι'.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨r ∘ₗ LinearMap.pi (fun i => LinearMap.pi (fun l => Λ i l)), fun f φ _ hφ => ?_⟩
  have hR : Formalism.MainNotions.KudlaSiegelWeil.Restr s (fun v => pv v (φ v)) := by
    refine ((Filter.eventually_cofinite.1 hφ).union (Filter.eventually_cofinite.1 hs)).subset fun v hv => ?_
    by_cases e : φ v = M.vac v
    · right
      simp only [Set.mem_setOf_eq, e] at hv ⊢
      exact hv
    · left
      exact e
  have h1 : LinearMap.pi (fun i => LinearMap.pi (fun l => Λ i l)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) =
      ι' (pr f ⊗ₜ GlobalTheory.SmallThetaModules.pureT s (fun v => pv v (φ v))) := by
    funext i l
    rw [LinearMap.pi_apply, LinearMap.pi_apply, hΛ i l f φ hφ]
    simp only [ι', LinearMap.comp_apply, LinearEquiv.coe_coe, Finsupp.lcoeFun_apply, LinearMap.compLeft_apply,
      Function.comp_apply, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply, Submodule.subtype_apply,
      Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, GlobalTheory.SmallThetaModules.coe_pureT hR,
      GlobalTheory.SmallThetaModules.evFam, Module.Basis.coord_apply]
  rw [LinearMap.comp_apply, h1, ← LinearMap.comp_apply, hr, LinearMap.id_apply]

end GlobalTheory.PureLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilOperatorLeftIntertwinesHeisenbergDerivativeStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_operator_left_intertwines_heisenberg_derivative : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    IsStd ψ → M.IsWeil ψ χX χW om → ∀ (g : UA σ X.J) (Tg : SInf F (Fin n × Fin d) → SInf F (Fin n × Fin d)),
    (∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (g, 1)) f (Tg f)) → ∀ u : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u →
    ∀ f f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine ψ u) f f₁ → ∀ y,
      Tg f₁ y = GlobalTheory.HeisOrbit.dOp (GlobalTheory.HeisOrbit.archCo M.co (mat g * u)).1 (GlobalTheory.HeisOrbit.archCo M.co (mat g * u)).2 (Tg f) y := by
  first | exact @GlobalTheory.HeisOrbit.weil_heisDeriv_intertw_left | exact GlobalTheory.HeisOrbit.weil_heisDeriv_intertw_left | (intros; apply GlobalTheory.HeisOrbit.weil_heisDeriv_intertw_left <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilOperatorRightIntertwinesHeisenbergDerivativeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical
open GlobalTheory.HeisOrbit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_operator_right_intertwines_heisenberg_derivative : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    IsStd ψ → M.IsWeil ψ χX χW om → ∀ (h : UA σ W.J) (Th : SInf F (Fin n × Fin d) → SInf F (Fin n × Fin d)),
    (∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (1, h)) f (Th f)) → ∀ u : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u →
    ∀ f f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine ψ u) f f₁ → ∀ y,
      Th f₁ y = GlobalTheory.HeisOrbit.dOp (GlobalTheory.HeisOrbit.archCo M.co (u * (mat h)ᵀ)).1 (GlobalTheory.HeisOrbit.archCo M.co (u * (mat h)ᵀ)).2 (Th f) y := by
  first | exact @GlobalTheory.HeisOrbit.weil_heisDeriv_intertw | exact GlobalTheory.HeisOrbit.weil_heisDeriv_intertw | (intros; apply GlobalTheory.HeisOrbit.weil_heisDeriv_intertw <;> assumption)
end

