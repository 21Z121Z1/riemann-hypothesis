import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LimitIdempotentRangeLeSumEigenspaces
import Formalism.LocalToGlobal.CharacterGerms.Bundle0013
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0053
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.Bundle0026
import ReciprocityTheory.DualLattices.Bundle0015
import ReciprocityTheory.DualLattices.Bundle0033
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NilChartOfIsChartJ
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0054
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0049
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LimitIdempotentRangeLeSumEigenspacesStatement
section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.limitIdempotent_range_le_sum_eigenspaces : ∀ (C : Type) [Field C] [IsAlgClosed C] (V : VF C) (O : Type) [CommRing O] (κ : Type) [Fintype κ] [DecidableEq κ] (L : O →+* Matrix κ κ C), (∀ x i j, V.Ge 0 (L x i j)) → ∀ (d : ℕ) [NeZero d] (em : ZMod d → (O →+* C)), (∀ a x, V.Ge 0 (em a x)) → (∀ a x, V.MM (em (a + 1) x - em a x ^ V.l)) → ∀ ε : O, (∃ y, ε * ε - ε = (V.l : O) * y) → (∀ x : O, (∀ a, V.MM (em a x)) → ∃ y, ε * x = (V.l : O) * y) → ∀ E : Matrix κ κ C, (∀ (N : ℕ) (v : κ → C) i, ∃ n0 : ℕ, ∀ n ≥ n0, V.Ge N (E.mulVec v i - (L (ε ^ (V.l ^ n))).mulVec v i)) → ∀ v : κ → C, ∃ w : ZMod d → κ → C, (∀ a x, (L x).mulVec (w a) = em a x • w a) ∧ E.mulVec v = ∑ a, w a := by
  first | exact @GlobalTheory.IdemRange.limit_idempotent_range | exact GlobalTheory.IdemRange.limit_idempotent_range | (intros; apply GlobalTheory.IdemRange.limit_idempotent_range <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LinMulFAndCompAndSpanLeAndMemPowStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mulF_span_mul_le_and_mulF_pow_mem_ideal_pow : ∀ (R : Type) [CommRing R] (d : ℕ) (F : FGLaw R d), (∀ N : ℕ, lin (mulF F.F N) = (N : R) • (1 : Matrix (Fin d) (Fin d) R)) ∧ (∀ N M : ℕ, mulF F.F (N * M) = comp1 (mulF F.F N) (mulF F.F M)) ∧ (∀ N M : ℕ, Ideal.span (Set.range (mulF F.F (N * M))) ≤ Ideal.span (Set.range (mulF F.F M))) ∧ ∀ (p k : ℕ) (j : Fin d), mulF F.F (p ^ k) j ∈ ((Ideal.span {(p : R)}).map (MvPowerSeries.C : R →+* PS R 1 d) ⊔ Ideal.span (Set.range (MvPowerSeries.X : Fin 1 × Fin d → PS R 1 d))) ^ (k + 1) := by
  first | exact @GlobalTheory.ChF.lin_mulF_and_comp_and_span_le_and_mem_pow | exact GlobalTheory.ChF.lin_mulF_and_comp_and_span_le_and_mem_pow | (intros; apply GlobalTheory.ChF.lin_mulF_and_comp_and_span_le_and_mem_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LinearDataHodgeTateInclusionStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearData_hodgeTate_inclusion : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] [StarRing OE] (cp : O), HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp → ∀ (g : ℕ) (H : HodgeTateDatum p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (d r m : ℕ) (A : Matrix (Fin d) (Fin r) O) (B : Matrix (Fin g) (Fin d) O) (ρG : OE →+* Matrix (Fin d) (Fin d) O) (N : OE →+* Matrix (Fin r) (Fin r) ℤ) (s : Fin m → Fin d → O), LinDat H A B ρG N s → ∀ c : O, v (algebraMap O C c) ^ (p - 1) ≤ v (algebraMap O C (p : O)) → ∀ f : Fin d → O, c • f ∈ Submodule.span O (Set.range s) := by
  first | exact @GlobalTheory.ChF.linDat_hodgeTate_inclusion | exact GlobalTheory.ChF.linDat_hodgeTate_inclusion | (intros; apply GlobalTheory.ChF.linDat_hodgeTate_inclusion <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LinearPartPairingSeriesEqHeightStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_part_pairing_series_eq_height : ∀ (R₀ : Type) [CommRing R₀] (B : BX R₀) (p : ℕ) (Tw : ATowerL R₀ p) (Dt : DualTower Tw) (g : ℕ) (Y : ∀ R : LAlg R₀, LHom Tw.O R → (Fin g → (R : Type)) → B.G R) (gb : Module.Basis (Fin g) R₀ B.gg) (S : Matrix (Fin g) (Fin g) (Tw.O : Type)), TanMat B Tw.O Y gb S → ∀ (τ : ℕ → B.G Tw.O) (u : PS (Tw.O : Type) 1 g), MvPowerSeries.constantCoeff u = 1 → PairSer B Tw.O Y p τ u → ∀ ht : B.gg →ₗ[R₀] (Tw.O : Type), (∀ n, B.IsHeight (Dt.Dp n) (p ^ (n + 1)) (B.map (Tw.q n) (τ n)) ((Tw.q n).1.toLinearMap ∘ₗ ht)) → Sᵀ *ᵥ dl u = fun l => ht (gb l) := by
  first | exact @GlobalTheory.ChF.dl_pairSer_eq_height | exact GlobalTheory.ChF.dl_pairSer_eq_height | (intros; apply GlobalTheory.ChF.dl_pairSer_eq_height <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NilChartOfIsChartJStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nilChart_reads_of_isChartJ : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], Smooth G.hom → ∀ (d : ℕ) (F : FGLaw R d) (x : ∀ m : ℕ, Geo.Tor.algOver R (Geo.Tor.JetR R (Fin 1 × Fin d) m) ⟶ G), IsChartJ G F x → ∃ X : Fam G d, NilChart G F.F X ∧ ∀ (OE : Type) [CommRing OE] (io : Out.RingAct G OE) (act : Geo.Tor.Germ.OAct OE F), ChartActs G x io act → ∀ a, Reads X X (io.act a) (act.act a) := by
  first | exact @GlobalTheory.ChF.nilChart_of_isChartJ | exact GlobalTheory.ChF.nilChart_of_isChartJ | (intros; apply GlobalTheory.ChF.nilChart_of_isChartJ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PadicPlaceBasisOfIdempotent
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem exists_eps {C B OE : Type} [Field C] [CommRing B] [Algebra C B] [CommRing OE]
    (σ : B →ₐ[C] C) (j : OE →+* B) (hj : Submodule.span C (Set.range j) = ⊤)
    (hsup : (⨆ τ : OE →+* C, ⨅ a : OE,
      Module.End.eigenspace (((Algebra.lmul C B).toRingHom.comp j) a) (τ a)) = ⊤) :
    ∃ ε : B, σ ε = 1 ∧ ∀ z, z * ε = σ z • ε := by
  have key : ∀ z : B, ∃ ε : B, σ ε = σ z ∧ ∀ a, j a * ε = σ (j a) • ε := by
    intro z
    have hz : z ∈ (⨆ τ : OE →+* C, ⨅ a : OE,
      Module.End.eigenspace (((Algebra.lmul C B).toRingHom.comp j) a) (τ a)) := by
      rw [hsup]; trivial
    induction hz using Submodule.iSup_induction' with
    | mem τ x hx =>
      have hx' : ∀ a, j a * x = τ a • x := fun a => by
        have := (Submodule.mem_iInf _).1 hx a
        rw [Module.End.mem_eigenspace_iff] at this
        exact this
      by_cases h0 : σ x = 0
      · exact ⟨0, by simp [h0], by simp⟩
      · refine ⟨x, rfl, fun a => ?_⟩
        have h1 := congrArg σ (hx' a)
        rw [map_mul, map_smul, smul_eq_mul] at h1
        rw [hx' a, mul_right_cancel₀ h0 h1]
    | zero => exact ⟨0, rfl, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, ha'⟩ := hx
      obtain ⟨b, hb, hb'⟩ := hy
      exact ⟨a + b, by simp [ha, hb], fun c => by rw [mul_add, smul_add, ha', hb']⟩
  obtain ⟨ε, h1, h2⟩ := key 1
  refine ⟨ε, by simpa using h1, fun z => ?_⟩
  have hz : z ∈ Submodule.span C (Set.range j) := by rw [hj]; trivial
  induction hz using Submodule.span_induction with
  | mem x hx => obtain ⟨a, rfl⟩ := hx; exact h2 a
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul, hx, hy, map_add, add_smul]
  | smul c x _ hx => rw [smul_mul_assoc, hx, map_smul, smul_eq_mul, mul_smul]

private theorem core {C B OE κ I H : Type} [Field C] [CommRing B] [Algebra C B] [CommRing OE]
    [Fintype κ] [DecidableEq κ] [Fintype I] [Fintype H]
    (σ : B →ₐ[C] C) (j : OE →+* B) (hj : Submodule.span C (Set.range j) = ⊤)
    (hsup : (⨆ τ : OE →+* C, ⨅ a : OE,
      Module.End.eigenspace (((Algebra.lmul C B).toRingHom.comp j) a) (τ a)) = ⊤)
    (ρ : B →ₐ[C] Matrix κ κ C) (e : B) (he : σ e = 1) (b : I → B)
    (hb : ∀ z, z * e ∈ Submodule.span C (Set.range b)) (y : H → κ → C)
    (hli : LinearIndependent C (fun q : I × H => ρ (b q.1) *ᵥ y q.2))
    (hsp : ∀ x, ρ e *ᵥ x ∈ Submodule.span C (Set.range fun q : I × H => ρ (b q.1) *ᵥ y q.2)) :
    Module.finrank C ↥(⨅ a : OE, Module.End.eigenspace (Matrix.toLin' (ρ (j a))) (σ (j a))) =
      Fintype.card H := by
  obtain ⟨ε, h1, h2⟩ := exists_eps σ j hj hsup
  have hεe : ε * e = ε := by rw [mul_comm, h2, he, one_smul]
  obtain ⟨t, ht⟩ := (Submodule.mem_span_range_iff_exists_fun C).1 (hb ε)
  rw [hεe] at ht
  have hmul : ∀ (z : B) (x : κ → C), ρ z *ᵥ (ρ ε *ᵥ x) = σ z • (ρ ε *ᵥ x) := fun z x => by
    rw [Matrix.mulVec_mulVec, ← map_mul, h2, map_smul, Matrix.smul_mulVec]
  have hmul' : ∀ (z : B) (x : κ → C), ρ ε *ᵥ (ρ z *ᵥ x) = σ z • (ρ ε *ᵥ x) := fun z x => by
    rw [Matrix.mulVec_mulVec, ← map_mul, mul_comm, h2, map_smul, Matrix.smul_mulVec]
  have hli' : LinearIndependent C (fun l : H => ρ ε *ᵥ y l) := by
    rw [Fintype.linearIndependent_iff] at hli ⊢
    intro c hc l
    have h3 := hli (fun q => c q.2 * t q.1) (by
      rw [← hc, Fintype.sum_prod_type_right]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [← ht, map_sum, Matrix.sum_mulVec, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, Matrix.smul_mulVec, mul_smul])
    by_contra hl
    have h4 : ∀ i, t i = 0 := fun i => (mul_eq_zero.1 (h3 (i, l))).resolve_left hl
    have h5 : ε = 0 := by rw [← ht]; simp [h4]
    rw [h5, map_zero] at h1
    exact zero_ne_one h1
  have hE : (⨅ a : OE, Module.End.eigenspace (Matrix.toLin' (ρ (j a))) (σ (j a))) =
      Submodule.span C (Set.range fun l : H => ρ ε *ᵥ y l) := by
    apply le_antisymm
    · intro x hx
      have hx' : ∀ a, ρ (j a) *ᵥ x = σ (j a) • x := fun a => by
        have := (Submodule.mem_iInf _).1 hx a
        rw [Module.End.mem_eigenspace_iff] at this
        simpa using this
      have hx2 : ∀ z, ρ z *ᵥ x = σ z • x := fun z => by
        have hz : z ∈ Submodule.span C (Set.range j) := by rw [hj]; trivial
        induction hz using Submodule.span_induction with
        | mem x hx => obtain ⟨a, rfl⟩ := hx; exact hx' a
        | zero => simp
        | add x y _ _ hx hy => rw [map_add, Matrix.add_mulVec, hx, hy, map_add, add_smul]
        | smul c x _ hx => rw [map_smul, Matrix.smul_mulVec, hx, map_smul, smul_eq_mul, mul_smul]
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun C).1 (hsp x)
      have : x = ρ ε *ᵥ (ρ e *ᵥ x) := by rw [hx2 e, he, one_smul, hx2, h1, one_smul]
      rw [this, ← hc, Matrix.mulVec_sum]
      refine Submodule.sum_mem _ fun q _ => ?_
      rw [Matrix.mulVec_smul, hmul']
      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨q.2, rfl⟩))
    · rw [Submodule.span_le]
      rintro _ ⟨l, rfl⟩
      refine (Submodule.mem_iInf _).2 fun a => ?_
      rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
      exact hmul _ _
  rw [hE, finrank_span_eq_card hli']

theorem eigDim_eq_of_basis : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] (w : PlaceU p OE) (b : Module.Basis (Fin w.n) ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e))) (κ : Type) [Fintype κ] [DecidableEq κ] (ρ : (ℤ_[p] ⊗[ℤ] OE) →ₐ[ℤ_[p]] Matrix κ κ ℤ_[p]) (h : ℕ) (y : Fin h → κ → ℤ_[p]), LinearIndependent ℤ_[p] (fun q : Fin w.n × Fin h => ρ (b q.1 : ℤ_[p] ⊗[ℤ] OE) *ᵥ y q.2) → Submodule.span ℤ_[p] (Set.range fun q : Fin w.n × Fin h => ρ (b q.1 : ℤ_[p] ⊗[ℤ] OE) *ᵥ y q.2) = LinearMap.range (Matrix.mulVecLin (ρ w.e)) → ∀ τ ∈ Emb (O := O) w.e, eigDim C (fun a : OE => (ρ (1 ⊗ₜ[ℤ] a)).map (algebraMap ℤ_[p] O)) ((algebraMap O C).comp τ) = h := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ OE _ _ _ _ _ w b κ _ _ ρ h y hli hsp τ hτ
  letI : Algebra ℤ_[p] C := ((algebraMap O C).comp (algebraMap ℤ_[p] O)).toAlgebra
  haveI : IsScalarTower ℤ_[p] O C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hinj : Function.Injective (algebraMap ℤ_[p] C) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra h0
    rw [PadicInt.unitCoeff_spec h0, map_mul, map_pow, map_natCast] at hx
    rcases mul_eq_zero.1 hx with h1 | h1
    · exact ((PadicInt.unitCoeff h0).isUnit.map (algebraMap ℤ_[p] C)).ne_zero h1
    · exact (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) (pow_eq_zero_iff'.1 h1).1
  haveI : FaithfulSMul ℤ_[p] C := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  let σ : (C ⊗[ℤ_[p]] (ℤ_[p] ⊗[ℤ] OE)) →ₐ[C] C := Algebra.TensorProduct.lift (AlgHom.id C C)
    ((IsScalarTower.toAlgHom ℤ_[p] O C).comp (tauExt τ)) (fun _ _ => Commute.all _ _)
  let ρB : (C ⊗[ℤ_[p]] (ℤ_[p] ⊗[ℤ] OE)) →ₐ[C] Matrix κ κ C :=
    Algebra.TensorProduct.lift (Algebra.ofId C (Matrix κ κ C))
    ((Algebra.ofId ℤ_[p] C).mapMatrix.comp ρ) (fun _ _ => Algebra.commutes _ _)
  let j : OE →+* (C ⊗[ℤ_[p]] (ℤ_[p] ⊗[ℤ] OE)) :=
    (Algebra.TensorProduct.includeRight (R := ℤ_[p]) (A := C) (B := ℤ_[p] ⊗[ℤ] OE)).toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℤ_[p]) (B := OE)).toRingHom
  have hj : ∀ a, j a = 1 ⊗ₜ (1 ⊗ₜ a) := fun a => rfl
  have hσ : ∀ a, σ (1 ⊗ₜ a) = algebraMap O C (tauExt τ a) := fun a => by simp [σ]
  have hρ : ∀ a, ρB (1 ⊗ₜ a) = (ρ a).map (algebraMap ℤ_[p] C) := fun a => by
    refine (Algebra.TensorProduct.lift_tmul _ _ _ _ _).trans ?_
    rw [map_one, _root_.one_mul]
    rfl
  have hmv : ∀ a x, ρB (1 ⊗ₜ a) *ᵥ (algebraMap ℤ_[p] C ∘ x) = algebraMap ℤ_[p] C ∘ (ρ a *ᵥ x) := by
    intro a x
    funext i
    rw [hρ]
    exact (RingHom.map_mulVec _ _ _ _).symm
  have hs : ∀ (c : C) (r : ℤ_[p]) (a : ℤ_[p] ⊗[ℤ] OE),
      (c ⊗ₜ[ℤ_[p]] (r • a)) = (r • c) • ((1 : C) ⊗ₜ[ℤ_[p]] a) := fun c r a => by
    rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
  have H := core (I := Fin w.n) (H := Fin h) σ j ?_ ((GlobalTheory.order_rep_diagonalisable C OE).2 _ _).2 ρB (1 ⊗ₜ w.e)
    (by rw [hσ, show tauExt τ w.e = 1 from hτ, map_one])
    (fun i => 1 ⊗ₜ (b i : ℤ_[p] ⊗[ℤ] OE)) ?_ (fun l => algebraMap ℤ_[p] C ∘ y l) ?_ ?_
  · rw [Fintype.card_fin] at H
    have h1 : ∀ a, ρB (j a) = ((ρ (1 ⊗ₜ[ℤ] a)).map (algebraMap ℤ_[p] O)).map (algebraMap O C) := by
      intro a
      rw [hj, hρ, Matrix.map_map]
      rfl
    have h2 : ∀ a, σ (j a) = ((algebraMap O C).comp τ) a := by
      intro a
      rw [hj, hσ]
      simp [tauExt]
    have h3 : (⨅ a : OE, Module.End.eigenspace (Matrix.toLin' (ρB (j a))) (σ (j a))) = ⨅ a : OE,
        Module.End.eigenspace (Matrix.toLin' (((ρ (1 ⊗ₜ[ℤ] a)).map (algebraMap ℤ_[p] O)).map (algebraMap O C)))
          (((algebraMap O C).comp τ) a) := iInf_congr fun a => by rw [h1, h2]
    rw [h3] at H
    exact H
  · rw [eq_top_iff]
    rintro z -
    induction z using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | add x y hx hy => exact Submodule.add_mem _ hx hy
    | tmul c a =>
      induction a using TensorProduct.induction_on with
      | zero => rw [TensorProduct.tmul_zero]; exact Submodule.zero_mem _
      | add x y hx hy => rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ hx hy
      | tmul r a =>
        have : r ⊗ₜ[ℤ] a = r • ((1 : ℤ_[p]) ⊗ₜ[ℤ] a) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
        rw [this, hs]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  · intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [zero_mul]; exact Submodule.zero_mem _
    | add x y hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
    | tmul c a =>
      have h1 := congrArg Subtype.val (b.sum_repr ⟨w.e * a, a, rfl⟩)
      simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul] at h1
      rw [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, mul_comm a, ← h1, TensorProduct.tmul_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [hs]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · simp only [hmv]
    exact linearIndependent_algebraMap_comp_iff.2 hli
  · intro x
    simp only [hmv]
    rw [← Finset.univ_sum_single x, Matrix.mulVec_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    have h1 : (Pi.single k (x k) : κ → C) = x k • (algebraMap ℤ_[p] C ∘ (Pi.single k 1 : κ → ℤ_[p])) := by
      funext i
      by_cases hi : i = k
      · subst hi; simp
      · simp [hi]
    rw [h1, Matrix.mulVec_smul, hmv]
    refine Submodule.smul_mem _ _ ?_
    have h2 : ρ w.e *ᵥ (Pi.single k 1 : κ → ℤ_[p]) ∈ LinearMap.range (Matrix.mulVecLin (ρ w.e)) := ⟨_, rfl⟩
    rw [← hsp] at h2
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h2
    refine (Submodule.mem_span_range_iff_exists_fun _).2 ⟨fun q => algebraMap ℤ_[p] C (c q), ?_⟩
    rw [← hc]
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, map_sum, map_mul]

end GlobalTheory.ChF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PadicUnitQuotientPrincipalBasisStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padic_unit_quotient_principal_basis : ∀ (p : ℕ) [Fact p.Prime] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] (w : PlaceU p OE), IsDomain ((ℤ_[p] ⊗[ℤ] OE) ⧸ Ideal.span {1 - w.e}) ∧ IsPrincipalIdealRing ((ℤ_[p] ⊗[ℤ] OE) ⧸ Ideal.span {1 - w.e}) ∧ ∃ (α : ℤ_[p] ⊗[ℤ] OE) (b : Module.Basis (Fin w.n) ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e))), ∀ k, (b k : ℤ_[p] ⊗[ℤ] OE) = w.e * α ^ (k : ℕ) := by
  first | exact @GlobalTheory.PlaceMono.place_monogenic | exact GlobalTheory.PlaceMono.place_monogenic | (intros; apply GlobalTheory.PlaceMono.place_monogenic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PointsAddCommMonoidStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_addCommMonoid_algHom_powerSeries_fgLaw : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (d : ℕ) (F : FGLaw O d), ∃ inst : AddCommMonoid (PS O 1 d →ₐ[O] O), letI := inst; (∀ φ φ' ψ, IsSum F.F φ φ' ψ ↔ ψ = φ + φ') ∧ (∀ f, (0 : PS O 1 d →ₐ[O] O) f = MvPowerSeries.constantCoeff f) ∧ ∀ (N : ℕ) (φ : PS O 1 d →ₐ[O] O), N • φ = 0 ↔ Killed F.F N φ := by
  first | exact @GlobalTheory.FormalPts.points_addCommMonoid | exact GlobalTheory.FormalPts.points_addCommMonoid | (intros; apply GlobalTheory.FormalPts.points_addCommMonoid <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.RangeIdempotentRankSumEigenspaceDim
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem finrank_iSup_indep {K V I : Type} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]
    [Fintype I] (S : I → Submodule K V) (hi : iSupIndep S) :
    Module.finrank K ↥(⨆ i, S i) = ∑ i, Module.finrank K (S i) := by
  classical
  rw [Submodule.iSup_eq_range_dfinsupp_lsum, LinearMap.finrank_range_of_inj hi.dfinsupp_lsum_injective]
  exact Module.finrank_directSum (R := K) (fun i => S i)

private theorem range_idem {O : Type} [CommRing O] [IsLocalRing O] {g : ℕ} (P : Matrix (Fin g) (Fin g) O)
    (h : P * P = P) : ∃ r : ℕ, Matrix.trace P = (r : O) ∧ Module.finrank O (LinearMap.range (Matrix.mulVecLin P)) = r ∧
      Nonempty (LinearMap.range (Matrix.mulVecLin P) ≃ₗ[O] (Fin r → O)) := by
  have hf : IsIdempotentElem (Matrix.mulVecLin P) := by
    show Matrix.mulVecLin P ∘ₗ Matrix.mulVecLin P = _
    rw [← Matrix.mulVecLin_mul, h]
  have hp := LinearMap.IsIdempotentElem.isProj_range _ hf
  haveI : Module.Projective O (LinearMap.range (Matrix.mulVecLin P)) :=
    Module.Projective.of_split (LinearMap.range (Matrix.mulVecLin P)).subtype hp.codRestrict (by
      ext x : 1
      exact hp.codRestrict_apply_cod x)
  haveI : Module.Free O (LinearMap.range (Matrix.mulVecLin P)) := Module.free_of_flat_of_isLocalRing
  haveI : Module.Projective O (LinearMap.ker (Matrix.mulVecLin P)) := by
    have hq := LinearMap.IsIdempotentElem.isProj_range _ hf.one_sub
    have : LinearMap.range (1 - Matrix.mulVecLin P) = LinearMap.ker (Matrix.mulVecLin P) :=
      (LinearMap.IsIdempotentElem.ker_eq_range_one_sub hf).symm
    rw [this] at hq
    exact Module.Projective.of_split (LinearMap.ker (Matrix.mulVecLin P)).subtype hq.codRestrict (by
      ext x : 1
      exact hq.codRestrict_apply_cod x)
  haveI : Module.Finite O (LinearMap.ker (Matrix.mulVecLin P)) := by
    rw [LinearMap.IsIdempotentElem.ker_eq_range_one_sub hf]
    infer_instance
  haveI : Module.Free O (LinearMap.ker (Matrix.mulVecLin P)) := Module.free_of_flat_of_isLocalRing
  refine ⟨_, ?_, rfl, ⟨(Module.finBasis O _).equivFun⟩⟩
  rw [← hp.trace, ← Matrix.toLin'_apply', Matrix.trace_toLin'_eq]

theorem range_idempotent_equiv_sum_eigDim : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] [StarRing OE] (g : ℕ) (ρ : (ℤ_[p] ⊗[ℤ] OE) →+* Matrix (Fin g) (Fin g) O) (e : ℤ_[p] ⊗[ℤ] OE), e * e = e → ∀ (n : ℕ) (t : Fin n ≃ Emb (O := O) e), Nonempty (LinearMap.range (Matrix.mulVecLin (ρ e)) ≃ₗ[O] (Fin (∑ j, eigDim C (fun a : OE => ρ (1 ⊗ₜ[ℤ] a)) ((algebraMap O C).comp ((t j : Emb (O := O) e) : OE →+* O))) → O)) := by
  intro p _ C _ _ _ v O _ _ hv _ _ _ OE _ _ _ _ _ _ g ρ e he n t
  haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  have hP : ρ e * ρ e = ρ e := by rw [← map_mul, he]
  obtain ⟨r, htr, -, hne⟩ := range_idem (ρ e) hP
  have hPC : (ρ e).map (algebraMap O C) * (ρ e).map (algebraMap O C) = (ρ e).map (algebraMap O C) := by
    rw [← Matrix.map_mul, hP]
  obtain ⟨r', htr', hrk, -⟩ := range_idem _ hPC
  have hrr : r = r' := by
    have : ((r : ℕ) : C) = r' := by
      rw [← htr', ← AddMonoidHom.map_trace (algebraMap O C) (ρ e), htr]
      simp
    exact_mod_cast this
  let σ : (ℤ_[p] ⊗[ℤ] OE) →+* Module.End C (Fin g → C) :=
    (Matrix.toLinAlgEquiv' (R := C) (n := Fin g)).toRingEquiv.toRingHom.comp
      ((algebraMap O C).mapMatrix.comp ρ)
  have hσ : ∀ x, σ x = Matrix.toLin' ((ρ x).map (algebraMap O C)) := fun x => rfl
  let ρE : OE →+* Module.End C (Fin g → C) :=
    σ.comp (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℤ_[p]) (B := OE)).toRingHom
  obtain ⟨-, hd⟩ := GlobalTheory.order_rep_diagonalisable C OE
  obtain ⟨hind, htop⟩ := hd (Fin g → C) ρE
  obtain ⟨hex, h01, -⟩ := GlobalTheory.ChF.embeddings_idempotents_conjugation p C v O hv OE
  have hz := (GlobalTheory.ChF.padicInt_algebra_of_isAdicComplete_and_matrix_unique p O).2 g
    (ρ.comp (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := ℤ_[p]) (B := OE)))
  set E : (OE →+* C) → Submodule C (Fin g → C) :=
    fun τ => ⨅ a : OE, Module.End.eigenspace (ρE a) (τ a) with hE
  have hact : ∀ (τ : OE →+* O) (y : Fin g → C), y ∈ E ((algebraMap O C).comp τ) →
      ∀ x, σ x y = algebraMap O C (tauExt τ x) • y := by
    intro τ y hy x
    have hy' : ∀ a, σ (1 ⊗ₜ[ℤ] a) y = algebraMap O C (τ a) • y := by
      intro a
      have := (Submodule.mem_iInf _).1 hy a
      exact Module.End.mem_eigenspace_iff.1 this
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x x' h h' => rw [map_add, map_add, map_add, LinearMap.add_apply, h, h', add_smul]
    | tmul c a =>
      have h1 : (c ⊗ₜ[ℤ] a : ℤ_[p] ⊗[ℤ] OE) = (c ⊗ₜ[ℤ] 1) * (1 ⊗ₜ[ℤ] a) := by simp
      have h2 : ρ (c ⊗ₜ[ℤ] 1) = algebraMap ℤ_[p] O c • (1 : Matrix (Fin g) (Fin g) O) := hz c
      have h3 : ∀ z, σ (c ⊗ₜ[ℤ] 1) z = algebraMap O C (algebraMap ℤ_[p] O c) • z := by
        intro z
        have : (algebraMap ℤ_[p] O c • (1 : Matrix (Fin g) (Fin g) O)).map (algebraMap O C)
            = algebraMap O C (algebraMap ℤ_[p] O c) • (1 : Matrix (Fin g) (Fin g) C) := by
          ext i j
          rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, map_mul,
            Matrix.one_apply, Matrix.one_apply]
          split_ifs
          · rw [map_one]
          · rw [map_zero]
        rw [hσ, h2, this, map_smul, Matrix.toLin'_one]
        rfl
      have h4 : tauExt τ (c ⊗ₜ[ℤ] a) = algebraMap ℤ_[p] O c * τ a := by
        simp [tauExt, Algebra.ofId_apply]
      rw [h4, h1, map_mul, Module.End.mul_apply, h3, hy', smul_smul, map_mul]
  have hinj : Function.Injective
      (fun j : Fin n => (algebraMap O C).comp ((t j : Emb (O := O) e) : OE →+* O)) := by
    intro i j hij
    apply t.injective
    apply Subtype.ext
    exact (hex _).unique hij rfl
  have hrange : LinearMap.range (σ e) =
      ⨆ j : Fin n, E ((algebraMap O C).comp ((t j : Emb (O := O) e) : OE →+* O)) := by
    apply le_antisymm
    · rw [LinearMap.range_eq_map, ← htop, Submodule.map_iSup]
      refine iSup_le fun τ => ?_
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨τ', rfl, -⟩ := hex τ
      rw [hact τ' y hy e]
      rcases h01 e τ' he with h | h
      · rw [h]; simp
      · rw [h, map_one, one_smul]
        refine Submodule.mem_iSup_of_mem (t.symm ⟨τ', h⟩) ?_
        rw [Equiv.apply_symm_apply]
        exact hy
    · refine iSup_le fun j => fun y hy => ⟨y, ?_⟩
      have h : tauExt ((t j : Emb (O := O) e) : OE →+* O) e = 1 := (t j).2
      rw [hact _ y hy e, h, map_one, one_smul]
  have hsum := finrank_iSup_indep _ (hind.comp hinj)
  have hfin : r' = ∑ j, eigDim C (fun a : OE => ρ (1 ⊗ₜ[ℤ] a))
      ((algebraMap O C).comp ((t j : Emb (O := O) e) : OE →+* O)) := by
    have h1 : Module.finrank C (LinearMap.range (σ e)) = r' := hrk
    rw [← h1, hrange]
    exact hsum
  rw [← hfin, ← hrr]
  exact hne

end GlobalTheory.ChF
end

