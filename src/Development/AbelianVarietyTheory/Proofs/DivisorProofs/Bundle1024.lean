import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0047
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0876
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankWeightComponentEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0994
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0989
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0934
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0975
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0199
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0138
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0137
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0279
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DsumEqZeroOfFibreSums
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0033
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0042
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0120
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0863
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0159
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0988
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0858

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteTopologyRationalUnitary
section
open scoped TensorProduct Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.RatUDiscrete

theorem discreteTopology_ratU : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), DiscreteTopology (ratU σ J) := by
  intro F E _ _ _ _ _ σ n J
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := F) (E := E)
  obtain ⟨U, hU, h⟩ := GlobalTheory.RationalDiscrete.exists_nhds_zero_inclR (F := F) (E := E)
  refine discreteTopology_of_isOpen_singleton_one ?_
  let f : ratU σ J → Matrix (Fin n) (Fin n) (AF F ⊗[F] E) :=
    fun g => ((g.1.1 : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) - 1
  have hf : Continuous f :=
    (Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)).sub
      continuous_const
  have hf1 : f 1 = 0 := sub_self _
  rw [isOpen_singleton_iff_nhds_eq_pure]
  refine le_antisymm (fun s hs => Filter.mem_of_superset (x := {1}) ?_ (Set.singleton_subset_iff.2 hs))
    (pure_le_nhds _)
  have hW : (⋂ i, ⋂ j, (fun g => f g i j) ⁻¹' U) ∈ 𝓝 (1 : ratU σ J) :=
    Filter.iInter_mem.2 fun i => Filter.iInter_mem.2 fun j =>
      (hf.matrix_elem i j).continuousAt.preimage_mem_nhds (by
        show U ∈ 𝓝 (f 1 i j)
        rw [hf1]; exact hU)
  refine Filter.mem_of_superset hW fun g hg => ?_
  obtain ⟨γ, hγ⟩ := MonoidHom.mem_range.1 (Subgroup.mem_subgroupOf.1 g.2)
  have hfg : ∀ i j, f g i j =
      inclR (F := F) (AF F) (((γ : Matrix (Fin n) (Fin n) E) - 1 : Matrix (Fin n) (Fin n) E) i j) := by
    intro i j
    show (((g.1.1 : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) - 1) i j = _
    rw [← hγ, Matrix.sub_apply, Matrix.sub_apply, map_sub, Matrix.one_apply, Matrix.one_apply,
      apply_ite (inclR (F := F) (AF F)), map_one, map_zero]
    rfl
  have hγ1 : γ = 1 := by
    refine Units.ext (sub_eq_zero.1 (Matrix.ext fun i j => h _ ?_))
    rw [Units.val_one, ← hfg]
    exact Set.mem_iInter.1 (Set.mem_iInter.1 hg i) j
  refine Subtype.ext (Subtype.ext ?_)
  rw [← hγ, hγ1, map_one]
  rfl

end GlobalTheory.RatUDiscrete
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorSupportTransferRank
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult Formalism.IndefR.Links GlobalTheory.SphPar
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DivMove

theorem exists_place {D : D7} {P : HeightOneSpectrum (𝓞 D.host.E)} {e f : Formalism.L2.Theta.AE D}
    (h : IsPrimeIdem P e f) :
    ∃ v : HeightOneSpectrum (𝓞 D.host.F), GlobalTheory.PlaceComp.IsIdemOf D.host.E v f ∧ f * e = e := by
  rcases h with ⟨he, rfl⟩ | ⟨rfl, ⟨v, ε, ⟨a, rfl, h1, h2⟩, he⟩, -⟩
  · obtain ⟨hee, hec, v, ε, ⟨a, rfl, h1, h2⟩, hs⟩ := he.1
    refine ⟨v, ?_, ?_⟩
    · rw [hs]; exact GlobalTheory.PlaceComp.isIdemOf_algebraMap h1 h2
    · rw [add_mul, hee, mul_comm, hec, add_zero]
  · have hi : GlobalTheory.PlaceComp.IsIdemOf D.host.E v f := by
      rw [he]; exact GlobalTheory.PlaceComp.isIdemOf_algebraMap h1 h2
    exact ⟨v, hi, (GlobalTheory.SuppLocal.idem_mul_iff hi f).2 ⟨hi.1, hi.2.2⟩⟩

theorem exists_divAt_of_rank_eq : ∀ {D : D7} (V V' : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e f : Formalism.L2.Theta.AE D) (ϖ : D.host.E) (d : List ℤ) (α : GA D V), V'.rank = V.rank → IsPrimeIdem P e f → SuppF V f α → DivAt V e ϖ d α → ∃ α' : GA D V', SuppF V' f α' ∧ DivAt V' e ϖ d α' := by
  intro D V V' P e f ϖ d α hr hP hα hd
  obtain ⟨v, hf, hfe⟩ := exists_place hP
  obtain ⟨φ, ψ, h1, h2, hJ, hL⟩ := GlobalTheory.LocalIsometryEqualRank.exists_local_isometry D V V' hr v
  obtain ⟨α', hs, hm, -⟩ :=
    GlobalTheory.IsomTransport.transport D.host.F D.host.E D.sp.cm V V' v f φ ψ hf h1 h2 hL hJ α hα
  exact ⟨α', hs, hd.1.trans hr.symm,
    GlobalTheory.DivTransport.divG_of_local_isometry D.host.F D.host.E D.sp.cm V V' v f φ ψ hf h1 h2 hL hr e ϖ
      (fun i => d.getD i.1 0) α α' hfe hm hd.2⟩

end GlobalTheory.DivMove
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleCosetVolumeWeightedSumConjStatement
section
open MeasureTheory Matrix
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleCosetVolumeWeightedSum_conj : ∀ (H : Type) [Group H] (T L U : Subgroup H) (Ψ : H → ℂ) (c : H),
  (∀ s ∈ T, ∀ t ∈ T, s * t = t * s) → (∀ t ∈ T, ∀ x, Ψ (t * x) = Ψ x) → (∀ l ∈ L, ∀ x, Ψ (x * l) = Ψ x) →
  GlobalTheory.OrbDesc.dsum T L U Ψ = GlobalTheory.OrbDesc.dsum (T.map (MulAut.conj c).toMonoidHom) (L.map (MulAut.conj c).toMonoidHom)
    (U.map (MulAut.conj c).toMonoidHom) (fun x => Ψ (c⁻¹ * x * c)) := by
  first | exact @GlobalTheory.OrbDesc.dsum_conj | exact GlobalTheory.OrbDesc.dsum_conj | (intros; apply GlobalTheory.OrbDesc.dsum_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryRationalEqDiagonalFixersProduct
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

noncomputable section
namespace GlobalTheory.ThetaRatGen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem inclR_inj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
  Algebra.TensorProduct.includeRight_injective (NumberField.AdeleRing.algebraMap_injective (R := 𝓞 F) (K := F))

theorem cA_inclR (σ : E →ₐ[F] E) (e : E) : cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  simp [cA, inclR]

theorem exists_eval_ne (ψ : Polynomial E) (hψ : ψ ≠ 0) : ∃ t : F, ψ.eval (algebraMap F E t) ≠ 0 := by
  classical
  haveI : Infinite F := Infinite.of_injective (Nat.cast : ℕ → F) Nat.cast_injective
  have hinf : (Set.range (algebraMap F E)).Infinite := Set.infinite_range_of_injective (algebraMap F E).injective
  obtain ⟨y, ⟨t, rfl⟩, hy⟩ := hinf.exists_notMem_finset ψ.roots.toFinset
  refine ⟨t, fun h => hy ?_⟩
  rw [Multiset.mem_toFinset, Polynomial.mem_roots hψ]
  exact h

theorem hyp1 : ∀ ψ : Polynomial E, (∀ (Ω : Type) [Field Ω] (φ : E →+* Ω), φ 1 = 1 → ψ.map φ ≠ 0) →
    ∃ t : F, IsUnit ((1 : E) * ψ.eval (algebraMap F E t) + (1 - 1)) := by
  intro ψ h
  have hψ : ψ ≠ 0 := by simpa using h E (RingHom.id E) (map_one _)
  obtain ⟨t, ht⟩ := exists_eval_ne (F := F) ψ hψ
  exact ⟨t, by simpa using ht⟩

theorem invol {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem exists_anti {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : ∃ ρ : E, ρ ≠ 0 ∧ σ ρ = -ρ := by
  have hne : σ ≠ AlgHom.id F E := by
    intro hσ
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have := h.2.1
    apply IsTotallyComplex.complexEmbedding_not_isReal τ
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have := h.2.2.2 τ x
    rw [hσ] at this
    simpa [ComplexEmbedding.conjugate_coe_eq] using this.symm
  obtain ⟨x, hx⟩ : ∃ x, σ x ≠ x := by
    by_contra hc
    push_neg at hc
    exact hne (AlgHom.ext hc)
  refine ⟨x - σ x, sub_ne_zero.mpr (Ne.symm hx), ?_⟩
  rw [map_sub, invol h]
  ring

variable (F) in
theorem incM_mul {m n k : Type} [Fintype n] (A : Matrix m n E) (B : Matrix n k E) :
    incM F (A * B) = incM F A * incM F B := Matrix.map_mul

variable (F) in
theorem incM_dbl {β : Type} (J : Matrix β β E) : incM F (dbl J) = dbl (incM F J) := by
  ext i j
  cases i <;> cases j <;> simp [incM, dbl]

theorem incM_map (σ : E →ₐ[F] E) {m n : Type} (A : Matrix m n E) : (incM F A).map (cA σ) = incM F (A.map σ) := by
  ext i j
  simp [incM, cA_inclR]

variable (F) in
theorem incM_transpose {m n : Type} (A : Matrix m n E) : (incM F A)ᵀ = incM F Aᵀ := rfl

variable (F) in
theorem incM_diag {β : Type} [DecidableEq β] :
    incM F (Matrix.fromRows (1 : Matrix β β E) (1 : Matrix β β E)) = Matrix.fromRows (1 : Matrix β β (AE F E)) 1 := by
  simp [incM, Matrix.fromRows_map]

variable (F) in
theorem incM_nabla {β : Type} [DecidableEq β] :
    incM F (Matrix.fromRows (1 : Matrix β β E) (-1 : Matrix β β E)) = Matrix.fromRows (1 : Matrix β β (AE F E)) (-1) := by
  simp [incM, Matrix.fromRows_map, Matrix.map_neg _ (map_neg (inclR (F := F) (E := E) (AF F)))]

theorem incM_inj {m n : Type} {A B : Matrix m n E} (h : incM F A = incM F B) : A = B := by
  ext i j
  exact inclR_inj (congrFun (congrFun h i) j)

def up (σ : E →ₐ[F] E) {b : ℕ} (JB : Matrix (Fin b) (Fin b) E) (p : UG σ (dbl JB)) : UG (cA σ) (dbl (incM F JB)) :=
  ⟨Matrix.GeneralLinearGroup.map (inclR (F := F) (E := E) (AF F)) p.1, by
    have hp : ((p.1 : Matrix _ _ E))ᵀ * dbl JB * (p.1 : Matrix _ _ E).map σ = dbl JB := p.2
    show (incM F (p.1 : Matrix _ _ E))ᵀ * dbl (incM F JB) * (incM F (p.1 : Matrix _ _ E)).map (cA σ) = dbl (incM F JB)
    rw [incM_map, ← incM_dbl, incM_transpose, ← incM_mul, ← incM_mul, hp]⟩

theorem up_mul (σ : E →ₐ[F] E) {b : ℕ} (JB : Matrix (Fin b) (Fin b) E) (p q : UG σ (dbl JB)) :
    up σ JB (p * q) = up σ JB p * up σ JB q :=
  Subtype.ext (map_mul _ _ _)

theorem down (σ : E →ₐ[F] E) {b : ℕ} (JB : Matrix (Fin b) (Fin b) E) (g : UG (cA σ) (dbl (incM F JB)))
    (g₀ : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E)
    (hg : ((g : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix _ _ (AE F E)) = incM F g₀) :
    ∃ g₁ : UG σ (dbl JB), ((g₁ : GL (Fin b ⊕ Fin b) E) : Matrix _ _ E) = g₀ ∧ g = up σ JB g₁ := by
  have hdet : IsUnit g₀.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    have hu : IsUnit (g.1 : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)).det :=
      (Matrix.isUnit_iff_isUnit_det (g.1 : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E))).mp (Units.isUnit _)
    have e : (incM F g₀).det = inclR (F := F) (AF F) g₀.det := (RingHom.map_det _ _).symm
    rw [hg, e, h0, map_zero, isUnit_zero_iff] at hu
    exact zero_ne_one (inclR_inj (F := F) (E := E) (by rw [map_zero, map_one]; exact hu))
  have hu : IsUnit g₀ := (Matrix.isUnit_iff_isUnit_det _).mpr hdet
  have hmem : hu.unit ∈ UG σ (dbl JB) := by
    show (hu.unit : Matrix _ _ E)ᵀ * dbl JB * (hu.unit : Matrix _ _ E).map σ = dbl JB
    rw [IsUnit.unit_spec]
    have h2 : ((g : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix _ _ (AE F E))ᵀ * dbl (incM F JB) *
        ((g : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix _ _ (AE F E)).map (cA σ) = dbl (incM F JB) := g.2
    rw [hg, incM_map, ← incM_dbl, incM_transpose, ← incM_mul, ← incM_mul] at h2
    exact incM_inj h2
  refine ⟨⟨hu.unit, hmem⟩, IsUnit.unit_spec hu, Subtype.ext (Units.ext ?_)⟩
  rw [hg]
  exact (congrArg (incM F) (IsUnit.unit_spec hu)).symm

end GlobalTheory.ThetaRatGen

namespace GlobalTheory.ThetaRatGen

theorem gen : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (b : ℕ) (JB : Matrix (Fin b) (Fin b) E) (ε : ℤˣ), (∀ i j, σ (JB j i) = ((ε : ℤ) : E) * JB i j) → JB.det ≠ 0 → ∀ (g : UG (cA σ) (dbl (incM F JB))) (g₀ : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E), ((g : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) = incM F g₀ → ∃ (p q p' : UG (cA σ) (dbl (incM F JB))) (p₀ q₀ p₀' : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E) (t s t' : GL (Fin b) (AE F E)), ((p : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) = incM F p₀ ∧ ((q : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) = incM F q₀ ∧ ((p' : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) = incM F p₀' ∧ ((p : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) * diagCols (Fin b) = diagCols (Fin b) * (t : Matrix (Fin b) (Fin b) (AE F E)) ∧ ((q : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) * Matrix.fromRows (1 : Matrix (Fin b) (Fin b) (AE F E)) (-1) = Matrix.fromRows (1 : Matrix (Fin b) (Fin b) (AE F E)) (-1) * (s : Matrix (Fin b) (Fin b) (AE F E)) ∧ ((p' : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) * diagCols (Fin b) = diagCols (Fin b) * (t' : Matrix (Fin b) (Fin b) (AE F E)) ∧ g = p * q * p' := by
  intro F E _ _ _ _ _ σ hσ b JB ε hJ hdet g g₀ hg
  haveI : Invertible (2 : E) := invertibleOfNonzero two_ne_zero
  obtain ⟨g₁, -, rfl⟩ := down σ JB g g₀ hg
  set G : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E := (g₁.1 : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E) with hG
  set H : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E :=
    ((g₁.1⁻¹ : GL (Fin b ⊕ Fin b) E) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E) with hH
  set Nt : Matrix (Fin b) (Fin b ⊕ Fin b) E := Matrix.fromCols 1 (-1) with hNt
  set N : Matrix (Fin b ⊕ Fin b) (Fin b) E := Matrix.fromRows 1 (-1) with hN
  set Dt : Matrix (Fin b) (Fin b ⊕ Fin b) E := Matrix.fromCols 1 1 with hDt
  set Δ : Matrix (Fin b ⊕ Fin b) (Fin b) E := Matrix.fromRows 1 1 with hΔ
  have hGH : G * H = 1 := by rw [hG, hH, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hNN : Nt * N = (2 : E) • 1 := by
    rw [hNt, hN, Matrix.fromCols_mul_fromRows]
    simp [two_smul]
  have e2' : Δ * Dt + N * Nt = (2 : E) • 1 := GlobalTheory.BigCell.e2
  have hPQ : (Nt * G * N) * ((4 : E)⁻¹ • (Nt * H * N)) + (Nt * G * Δ) * ((4 : E)⁻¹ • (Dt * H * N)) = 1 := by
    calc _ = (4 : E)⁻¹ • (Nt * G * (Δ * Dt + N * Nt) * H * N) := by
          simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, smul_add, Matrix.mul_assoc]
          abel
      _ = 1 := by
          rw [e2']
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, smul_smul]
          rw [show Nt * G * H * N = Nt * N by rw [Matrix.mul_assoc Nt G H, hGH, Matrix.mul_one], hNN, smul_smul]
          norm_num
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.T.exists_corner_unit_of_right_inverse' (F := F) (1 : E) (mul_one 1) hyp1 _ _ _ _ hPQ
  obtain ⟨ρ, hρ0, hρ⟩ := exists_anti hσ
  have hJ' : (JB.map (σ : E →+* E))ᵀ = ((ε : ℤ) : E) • JB := by
    ext i j
    simp [hJ]
  obtain ⟨x, hxS, hx⟩ := GlobalTheory.T.exists_conj_skew_det_unit_of_avoidance' (F := F) (σ : E →+* E) (invol hσ) (fun t => σ.commutes t) 1 hyp1 ρ
    (isUnit_iff_ne_zero.mpr hρ0) hρ JB ε hJ' (isUnit_iff_ne_zero.mpr hdet) _ _ x₀ hx₀
  obtain ⟨p, hpΔ, hcorner⟩ := GlobalTheory.T.siegelUnipotent_antidiagonal_corner (R₀ := F) σ JB x hxS
  have hunit : IsUnit (Matrix.fromCols (1 : Matrix (Fin b) (Fin b) E) (-1 : Matrix (Fin b) (Fin b) E) *
      (((g₁ * p : UG σ (dbl JB)) : GL (Fin b ⊕ Fin b) E) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E) *
      Matrix.fromRows (1 : Matrix (Fin b) (Fin b) E) (-1 : Matrix (Fin b) (Fin b) E)).det := by
    rw [Subgroup.coe_mul, Units.val_mul, hcorner]
    have hx' : IsUnit (Nt * G * N + Nt * G * Δ * x).det := by simpa using hx
    exact hx'
  obtain ⟨p₀, q₀, t, s, hp₀, hq₀, hpq⟩ := GlobalTheory.BigCell.bigCell_factor F E σ (Fin b) JB (g₁ * p) hunit
  have hg₁ : g₁ = p₀ * q₀ * p⁻¹ := eq_mul_inv_of_mul_eq hpq
  have hpinv : ((p⁻¹ : UG σ (dbl JB)).1 : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E) *
      (diagCols (Fin b) : Matrix (Fin b ⊕ Fin b) (Fin b) E) = (diagCols (Fin b) : Matrix (Fin b ⊕ Fin b) (Fin b) E) := by
    have h1 : (p.1 : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E) * (diagCols (Fin b) : Matrix (Fin b ⊕ Fin b) (Fin b) E) =
        (diagCols (Fin b) : Matrix (Fin b ⊕ Fin b) (Fin b) E) := by
      exact hpΔ.trans (Matrix.mul_one _)
    calc _ = ((p⁻¹ : UG σ (dbl JB)).1 : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E) *
          ((p.1 : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E) *
            (diagCols (Fin b) : Matrix (Fin b ⊕ Fin b) (Fin b) E)) := by rw [h1]
      _ = diagCols (Fin b) := by
          rw [← Matrix.mul_assoc, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one,
            Matrix.one_mul]
  refine ⟨up σ JB p₀, up σ JB q₀, up σ JB p⁻¹, p₀.1, q₀.1, (p⁻¹).1,
    Matrix.GeneralLinearGroup.map (inclR (F := F) (E := E) (AF F)) t,
    Matrix.GeneralLinearGroup.map (inclR (F := F) (E := E) (AF F)) s, 1, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · have h := congrArg (incM F) hp₀
    rw [incM_mul, incM_mul, incM_diag] at h
    exact h
  · have h := congrArg (incM F) hq₀
    rw [incM_mul, incM_mul, incM_nabla] at h
    exact h
  · have h := congrArg (incM F) hpinv
    rw [incM_mul, diagCols, incM_diag] at h
    exact h.trans (Matrix.mul_one _).symm
  · rw [hg₁, up_mul, up_mul]

end GlobalTheory.ThetaRatGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DsumEqZeroOfFibreSumsStatement
section
open MeasureTheory Matrix
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dsum_eq_zero_of_fibre_sums' : ∀ (H : Type) [Group H] (T P N L U : Subgroup H) (Ψ : H → ℂ), T ≤ P → N ≤ P → L ≤ P →
  (∀ p ∈ P, ∀ n ∈ N, p * n * p⁻¹ ∈ N) → (∀ s ∈ T, ∀ t ∈ T, s * t = t * s) →
  (∀ t ∈ T, ∀ x, Ψ (t * x) = Ψ x) → (∀ l ∈ L, ∀ x, Ψ (x * l) = Ψ x) → (∀ x, x ∉ P → Ψ x = 0) →
  (∀ x ∈ P, (T ⊓ L.map (MulAut.conj x).toMonoidHom).relIndex (T ⊓ (L ⊔ N).map (MulAut.conj x).toMonoidHom) ≠ 0) →
  (∀ m ∈ P, ∑ᶠ q : H ⧸ (N ⊓ L), (if Quotient.out q ∈ N then Ψ (m * Quotient.out q) else 0) = 0) →
  GlobalTheory.OrbDesc.dsum T L U Ψ = 0 := by
  first | (exact @GlobalTheory.OrbDesc.dsum_eq_zero_of_fibre_sums) | (exact GlobalTheory.OrbDesc.dsum_eq_zero_of_fibre_sums) | (intros; apply GlobalTheory.OrbDesc.dsum_eq_zero_of_fibre_sums  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffOfSec
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

noncomputable section

namespace GlobalTheory.EffBound

open GlobalTheory.CechPic

def Eff {X : Scheme.{0}} (c : Pic X) : Prop :=
  ∃ (N : LB X) (hN : N.IsLB), cls N hN = c ∧ ∃ (σ : LB.Sec N) (j : N.ι), σ.f j ≠ 0

theorem eff_of_sec {X : Scheme.{0}} (N : LB X) (hN : N.IsLB) (σ : LB.Sec N) (j : N.ι) (h : σ.f j ≠ 0) :
    Eff (cls N hN) :=
  ⟨N, hN, rfl, σ, j, h⟩

theorem cls_pw {X : Scheme.{0}} {H : LB X} (hH : H.IsLB) (t : ℤ) :
    cls (pw H t) (isLB_pw hH t) = t • cls H hH := by
  have hL := LB.isLB_linComb hH (fun _ : PUnit => 𝟙 X) (fun _ => t)
  have e : LBIso (LB.LinComb H (fun _ : PUnit => 𝟙 X) (fun _ => t)) (pw H t) :=
    iso_of_chart (isLB_pw hH t)
      { idx := fun j => j PUnit.unit
        le := fun j y hy => Set.mem_iInter.1 hy PUnit.unit
        g := fun y j j' hj hj' => by
          refine (gm_linComb H (fun _ : PUnit => 𝟙 X) (fun _ => t) (𝟙 X) y j j' hj hj').trans ?_
          rw [Fintype.prod_unique]
          change _ = gm (𝟙 X) y _ (H.g (j PUnit.unit) (j' PUnit.unit) ^ t)
          rw [map_zpow, Category.comp_id] }
  rw [← (cls_eq_iff hL (isLB_pw hH t)).2 e, cls_linComb hH, Fintype.sum_unique, pull_id]

end GlobalTheory.EffBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenvalueBarCompatibility
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjInner

theorem inner_eq_integral {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (μ : Measure (GA D V))
    (𝓕 : Set (GA D V)) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (e : H →ₗ[ℂ] MMap M) (c : ℂ)
    (h : ∀ x y, inner ℂ x y = c * ipM M μ 𝓕 (e x) (e y)) (v : M.Vec) (hv : ∀ τ, ‖(v τ : M.H τ)‖ = 1) (x y : H) :
    inner ℂ x y = c * ∫ g in 𝓕, star (e x v g) * e y v g ∂μ := by
  have hd : ∀ z : H, ∃ a, IsMultIP M μ 𝓕 (e z) (e z) a := by
    intro z
    by_cases hz : z = 0
    · refine ⟨0, fun v v' => ?_⟩
      subst hz
      simp
    · by_contra hn
      have := h z z
      simp only [ipM, dif_neg hn, mul_zero] at this
      exact hz (inner_self_eq_zero.1 this)
  obtain ⟨a, ha⟩ := hd x
  obtain ⟨b, hb⟩ := hd y
  obtain ⟨s, hs⟩ := hd (x + y)
  obtain ⟨t, ht⟩ := hd (x + Complex.I • y)
  rw [map_add] at hs ht
  rw [map_smul] at ht
  have h1 := (ipM_spec M μ 𝓕 _ _ ⟨_, GlobalTheory.SchurPolar.exists_of_diag M μ 𝓕 _ _ ha hb hs ht⟩ v v).2
  rw [h, h1, Finset.prod_eq_one, mul_one]
  intro τ _
  rw [inner_self_eq_norm_sq_to_K, hv]
  simp

theorem conj_integral {X : Type} [MeasurableSpace X] (μ : Measure X) (q : ℂ) (hq : starRingEnd ℂ q = q) {a b a' b' : X → ℂ}
    (ha : ∀ g, a g = starRingEnd ℂ (a' g)) (hb : ∀ g, b g = starRingEnd ℂ (b' g)) :
    q * ∫ g, star (a g) * b g ∂μ = starRingEnd ℂ (q * ∫ g, star (a' g) * b' g ∂μ) := by
  rw [map_mul, hq, ← integral_conj]
  congr 2
  funext g
  rw [ha, hb, map_mul]
  rfl

theorem inner_conj_of_span {L W H H' : Type} [Field L] [AddCommGroup W] [Module L W] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (σ : L →+* ℂ) (j : W →ₛₗ[σ] H)
    (j' : W →ₛₗ[(starRingEnd ℂ).comp σ] H') (s : Set W) (hs : Submodule.span L s = ⊤)
    (h : ∀ x ∈ s, ∀ y ∈ s, ⟪j x, j y⟫_ℂ = starRingEnd ℂ ⟪j' x, j' y⟫_ℂ) (x y : W) :
    ⟪j x, j y⟫_ℂ = starRingEnd ℂ ⟪j' x, j' y⟫_ℂ := by
  have hx : x ∈ Submodule.span L s := hs ▸ Submodule.mem_top
  have hy : y ∈ Submodule.span L s := hs ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx =>
    induction hy using Submodule.span_induction with
    | mem y hy => exact h x hx y hy
    | zero => simp
    | add y z _ _ h1 h2 => rw [map_add, map_add, inner_add_right, inner_add_right, map_add, h1, h2]
    | smul a y _ h1 =>
      rw [map_smulₛₗ, map_smulₛₗ, inner_smul_right, inner_smul_right, map_mul, h1, RingHom.comp_apply, Complex.conj_conj]
  | zero => simp
  | add x z _ _ h1 h2 => rw [map_add, map_add, inner_add_left, inner_add_left, map_add, h1, h2]
  | smul a x _ h1 =>
    rw [map_smulₛₗ, map_smulₛₗ, inner_smul_left, inner_smul_left, map_mul, h1, RingHom.comp_apply, Complex.conj_conj]

theorem dim_conj {D : D7} (W : HSp D) (σ : D.what₂.LL →+* ℂ) :
    (∏ ρ, ((dimK _ _ (kapAt W ((starRingEnd ℂ).comp σ) ρ) : ℚ) : ℂ)) = ∏ ρ, ((dimK _ _ (kapAt W σ ρ) : ℚ) : ℂ) := by
  refine Finset.prod_congr rfl fun ρ _ => ?_
  unfold kapAt
  rw [GlobalTheory.ConjEval.lab_conj]

theorem dim_real {D : D7} (W : HSp D) (σ : D.what₂.LL →+* ℂ) :
    starRingEnd ℂ (∏ ρ, ((dimK _ _ (kapAt W σ ρ) : ℚ) : ℂ)) = ∏ ρ, ((dimK _ _ (kapAt W σ ρ) : ℚ) : ℂ) := by
  rw [map_prod]
  exact Finset.prod_congr rfl fun ρ _ => map_ratCast _ _

set_option maxHeartbeats 1000000 in

theorem inner_conj_of_values {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (he : R.models_HW) (i : Fin D.R.m)
    (σ : D.what₂.LL →+* ℂ) {v : (R.MW i σ).Vec} {v' : (R.MW i ((starRingEnd ℂ).comp σ)).Vec} (hv : IsUnitV v) (hv' : IsUnitV v')
    {x y : (R.HW i σ).H} {x' y' : (R.HW i ((starRingEnd ℂ).comp σ)).H}
    (hx : ∀ g, evAt R i σ v x g = starRingEnd ℂ (evAt R i _ v' x' g))
    (hy : ∀ g, evAt R i σ v y g = starRingEnd ℂ (evAt R i _ v' y' g)) :
    ⟪x, y⟫_ℂ = starRingEnd ℂ ⟪x', y'⟫_ℂ := by
  have h1 := inner_eq_integral (R.MW i σ) (R.νW i) (R.fdW i) (R.HW i σ).e _ (he i σ).2.2 v hv x y
  have h2 := inner_eq_integral (R.MW i _) (R.νW i) (R.fdW i) (R.HW i _).e _ (he i _).2.2 v' hv' x' y'
  rw [dim_conj] at h2
  exact h1.trans ((conj_integral _ _ (dim_real _ σ) hx hy).trans (congrArg (starRingEnd ℂ) h2).symm)

set_option maxHeartbeats 1000000 in

theorem inner_reading_conj : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.Char F → ∀ (fw : FWTie T R κw v₀) (i : Fin D.R.m), JEvExists T R κw v₀ → JEvBar T R κw → BarTie fw → ∀ (σ : D.what₂.LL →+* ℂ), ¬ GoodEmb T.Q.c (res T σ) → ∀ y y', ⟪(R.FW i).j σ y, (R.FW i).j σ y'⟫_ℂ = starRingEnd ℂ ⟪(R.FW i).j ((starRingEnd ℂ).comp σ) y, (R.FW i).j ((starRingEnd ℂ).comp σ) y'⟫_ℂ := by
  intro D G _ _ Pl0 T0 A T _ R F κw v₀ hC fw i hE hB hT σ hσ
  have hg : GoodEmb T.Q.c (resC T σ) := good_resC T hσ
  have hV : T.V ((i : ℕ) + 1) (resC T σ) = Wc D i := fw.laws.spaceW _ (inR i) _ hg
  have h1 := (hT i σ hσ hV).1 (hB i σ hσ hV)
  obtain ⟨v, hv, h1⟩ := h1
  have h2 := fw.evaluates hE i ((starRingEnd ℂ).comp σ) hg hV
  have h3 : ∀ f g, evAt R i σ v (fw.jK i σ f) g =
      starRingEnd ℂ (evAt R i _ (v₀ i ((starRingEnd ℂ).comp σ)) (fw.jK i ((starRingEnd ℂ).comp σ) f) g) := fun f g =>
    (congrFun (h1 f) g).trans (congrArg (starRingEnd ℂ) (congrFun (h2 f) g).symm)
  have h4 : ∀ f f', ⟪fw.jK i σ f, fw.jK i σ f'⟫_ℂ =
      starRingEnd ℂ ⟪fw.jK i ((starRingEnd ℂ).comp σ) f, fw.jK i ((starRingEnd ℂ).comp σ) f'⟫_ℂ := fun f f' =>
    inner_conj_of_values R hC.models.HW i σ hv (fun τ => ((fw.hv₀ i _).1 τ).1) (h3 f) (h3 f')
  have h5 := fw.ks i
  obtain ⟨n, b, hb, -, -, -, h5⟩ := h5
  refine inner_conj_of_span σ _ _ _ h5 ?_
  rintro _ ⟨k, rfl⟩ _ ⟨l, rfl⟩
  have e : ∀ k, ∃ f, ((fw.e i f : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL) = b k := fun k =>
    ⟨(fw.e i).symm ⟨b k, hb k⟩, congrArg Subtype.val ((fw.e i).apply_symm_apply _)⟩
  have e1 := e k
  have e2 := e l
  obtain ⟨f, e1⟩ := e1
  obtain ⟨f', e2⟩ := e2
  rw [← e1, ← e2]
  exact h4 f f'

end GlobalTheory.ConjInner
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardComplexPointFibreEqEncardRingHomExtensionsStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Points
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.encard_complexPointFibre_eq_encard_ringHom_extensions : ∀ {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} (π : Y ⟶ X) (hπ : π ≫ p = q) (U : X.Opens), IsAffineOpen U → IsAffineOpen (π ⁻¹ᵁ U) → ∀ (σ : k →+* ℂ) (y : GlobalTheory.CxPts p σ) (hy : y ∈ GlobalTheory.CxPts.ptsIn p σ U), (GlobalTheory.Points.PtsOver.map π hπ (spMap σ) ⁻¹' {y}).encard = {ψ : Γ(Y, π ⁻¹ᵁ U) →+* ℂ | ψ.comp (π.app U).hom = GlobalTheory.CxPts.evHom hy}.encard := by
  first | exact @GlobalTheory.encard_fibre_eq_encard_ringHom | exact GlobalTheory.encard_fibre_eq_encard_ringHom | (intros; apply GlobalTheory.encard_fibre_eq_encard_ringHom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardComplexPointsFiniteEtaleFreeEqRankStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Points
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.encard_complexPoints_finiteEtaleFree_eq_rank : ∀ {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (δ : ℕ), f.Etale → f.Finite → (letI := f.toAlgebra; Module.Free A B ∧ Module.finrank A B = δ) → ∀ φ : A →+* ℂ, {ψ : B →+* ℂ | ψ.comp f = φ}.encard = (δ : ℕ∞) := by
  first | exact @GlobalTheory.EtaleComplexPoints.encard_complexPoints_eq_rank | exact GlobalTheory.EtaleComplexPoints.encard_complexPoints_eq_rank | (intros; apply GlobalTheory.EtaleComplexPoints.encard_complexPoints_eq_rank <;> assumption)
end

