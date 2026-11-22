import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0383
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0369
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
import GroundTheory.AutomorphicForms.SupercuspidalCoefficients
import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.DiscreteSeriesHilbert.StepSqInt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0382
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.InUQT
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.ResVq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothModelRestrictionBijective
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0053

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedActionSmooth
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

noncomputable section

namespace GlobalTheory.CompanionTheory.BZMir

def stabSub {M W : Type} [Group M] [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ M W) (w : W) :
    Subgroup M where
  carrier := {m | σ m w = w}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, Module.End.mul_apply, hb, ha]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem twAct_isSmooth {G M V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group M]
    [TopologicalSpace M] [IsTopologicalGroup M] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) (N : Subgroup G) (θ : N →* ℂˣ) (s : M →* G)
    (hsc : Continuous s)
    (hs : ∀ (m : M) (n : N), ∃ h : s m * (n : G) * (s m)⁻¹ ∈ N, θ ⟨_, h⟩ = θ n) :
    IsSmooth (twAct ρ N θ s hs) := by
  intro x
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hle : ((stabSub ρ v).comap s) ≤ stabSub (twAct ρ N θ s hs) (Submodule.Quotient.mk v) := by
    intro m hm
    change ρ (s m) v = v at hm
    change (twAct ρ N θ s hs) m (Submodule.Quotient.mk v) = Submodule.Quotient.mk v
    exact congrArg (Submodule.Quotient.mk (p := twKer ρ N θ)) hm
  have hop : IsOpen (((stabSub ρ v).comap s : Subgroup M) : Set M) :=
    (hρ v).preimage hsc
  exact Subgroup.isOpen_mono hle hop

end GlobalTheory.CompanionTheory.BZMir
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformizerPowTendstoZero
section
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.UnifPow

theorem valuation_unifU_lt_one (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : valuation k ((Zls.unifU k : kˣ) : k) < 1 := by
  have hle : valuation k ((Zls.unif k : 𝒪[k]) : k) ≤ 1 := (Zls.unif k).2
  refine lt_of_le_of_ne hle fun h1 => (Zls.irreducible_unif (k := k)).not_isUnit ?_
  exact ((Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one).2 h1

theorem tendsto_unifU_pow : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k],
    Filter.Tendsto (fun n : ℕ => ((Zls.unifU k : kˣ) : k) ^ n) Filter.atTop (nhds 0) := by
  intro k _ _ _ _
  rw [(IsValuativeTopology.hasBasis_nhds_zero' k).tendsto_right_iff]
  intro γ hγ
  have h := valuation_unifU_lt_one k
  have : MulArchimedean (ValueGroupWithZero k) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨n, hn⟩ := exists_pow_lt₀ h (Units.mk0 γ hγ)
  filter_upwards [eventually_ge_atTop n] with m hm
  rw [map_pow]
  exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' h.le hm) hn

end GlobalTheory.CompanionTheory.UnifPow
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentFiniteSetCompactSubgroup
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir ValuativeRel
open scoped Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.DerExhaust

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem t2 : T2Space k := by
  letI := IsTopologicalAddGroup.rightUniformSpace k
  haveI := isUniformAddGroup_of_addCommGroup (G := k)
  infer_instance

theorem isOpen_O : IsOpen (𝒪[k] : Set k) := Valuation.isOpen_integer

theorem isCompact_O : IsCompact (𝒪[k] : Set k) := IsNonarchimedeanLocalField.isCompact_closedBall k 1

theorem exists_ne_zero_mem {U : Set k} (hU : U ∈ 𝓝 (0 : k)) : ∃ z : k, z ≠ 0 ∧ z ∈ U := by
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff U).mp hU
  obtain ⟨y, hy⟩ := ValuativeRel.valuation_surjective (γ : ValueGroupWithZero k)
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact γ.ne_zero (by simpa using hy.symm)
  obtain ⟨r, hr, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  have hr0 : r ≠ 0 := by simpa using hr
  refine ⟨r * y, mul_ne_zero hr0 hy0, hγ ?_⟩
  show valuation k (r * y) < γ
  rw [map_mul, hy]
  exact mul_lt_of_lt_one_left (by simp [zero_lt_iff]) hr1

variable (k) in

def intGL (N : ℕ) : Subgroup (GL (Fin N) k) where
  carrier := {g | ∀ i j, (g : Matrix (Fin N) (Fin N) k) i j ∈ 𝒪[k] ∧
    ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j ∈ 𝒪[k]}
  mul_mem' {a b} ha hb := by
    intro i j
    simp only [_root_.mul_inv_rev, Units.val_mul, Matrix.mul_apply]
    exact ⟨Subring.sum_mem _ fun l _ => Subring.mul_mem _ (ha i l).1 (hb l j).1,
      Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hb i l).2 (ha l j).2⟩
  one_mem' := by
    intro i j
    simp only [inv_one, Units.val_one, Matrix.one_apply, and_self]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  inv_mem' {a} ha := by
    intro i j
    simpa [and_comm] using ha i j

theorem isCompact_intGL (N : ℕ) : IsCompact (intGL k N : Set (GL (Fin N) k)) := by
  haveI := t2 (k := k)
  let S : Set (Matrix (Fin N) (Fin N) k) := Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => (𝒪[k] : Set k)
  have hS : IsCompact S := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_O
  have hS' : IsCompact (S ×ˢ (MulOpposite.op '' S)) :=
    hS.prod (hS.image MulOpposite.continuous_op)
  convert Units.isClosedEmbedding_embedProduct.isCompact_preimage hS' using 1
  ext g
  constructor
  · intro h
    refine ⟨fun i _ j _ => (h i j).1, ⟨_, fun i _ j _ => (h i j).2, rfl⟩⟩
  · rintro ⟨h1, ⟨x, hx, hxe⟩⟩ i j
    have hx' : x = ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) := MulOpposite.op_injective hxe
    subst hx'
    exact ⟨h1 i (Set.mem_univ _) j (Set.mem_univ _), hx i (Set.mem_univ _) j (Set.mem_univ _)⟩

theorem isClosed_derUnip (N n : ℕ) : IsClosed (derUnip k N n : Set (GL (Fin N) k)) := by
  haveI := t2 (k := k)
  have hv : Continuous fun g : GL (Fin N) k => (g : Matrix (Fin N) (Fin N) k) := Units.continuous_val
  have he : ∀ i j : Fin N, Continuous fun g : GL (Fin N) k => (g : Matrix (Fin N) (Fin N) k) i j :=
    fun i j => hv.matrix_elem i j
  have h1 : (unipB k (Fin N) : Set (GL (Fin N) k)) =
      (⋂ i, ⋂ j, ⋂ (_ : j < i), {g : GL (Fin N) k | (g : Matrix (Fin N) (Fin N) k) i j = 0}) ∩
        ⋂ i, {g : GL (Fin N) k | (g : Matrix (Fin N) (Fin N) k) i i = 1} := by
    ext g
    simp only [SetLike.mem_coe, mem_unipB, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
  have h2 : (colFix k N n : Set (GL (Fin N) k)) =
      ⋂ i : Fin N, ⋂ (_ : (i : ℕ) < n),
        {g : GL (Fin N) k | (g : Matrix (Fin N) (Fin N) k).mulVec (Pi.single i 1) = Pi.single i 1} := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_iInter, Set.mem_setOf_eq]
    rfl
  show IsClosed ((unipB k (Fin N) ⊓ colFix k N n : Subgroup _) : Set (GL (Fin N) k))
  rw [Subgroup.coe_inf, h1, h2]
  refine IsClosed.inter (IsClosed.inter ?_ ?_) ?_
  · exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_eq (he i j) continuous_const
  · exact isClosed_iInter fun i => isClosed_eq (he i i) continuous_const
  · exact isClosed_iInter fun i => isClosed_iInter fun _ =>
      isClosed_eq (hv.matrix_mulVec continuous_const) continuous_const

theorem conj_entry_mem {N : ℕ} (y : kˣ) (hy : (y : k) ∈ 𝒪[k]) {u : GL (Fin N) k}
    (hu : u ∈ unipB k (Fin N)) (hyu : ∀ i j, (y : k) * (u : Matrix (Fin N) (Fin N) k) i j ∈ 𝒪[k])
    (i j : Fin N) :
    (((diagT k (Fin N) (fun l : Fin N => y ^ (l : ℕ)))⁻¹ * u *
      diagT k (Fin N) (fun l : Fin N => y ^ (l : ℕ)) : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j
      ∈ 𝒪[k] := by
  obtain ⟨h0, h1⟩ := (mem_unipB k).1 hu
  rw [← map_inv, Units.val_mul, Units.val_mul, val_diagT, val_diagT, Matrix.mul_diagonal,
    Matrix.diagonal_mul]
  simp only [Pi.inv_apply, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
  have ha0 : (y : k) ≠ 0 := y.ne_zero
  rcases lt_trichotomy (i : ℕ) j with hij | hij | hij
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hij
    rw [hd]
    have e : ((y : k) ^ (i : ℕ))⁻¹ * (u : Matrix (Fin N) (Fin N) k) i j * (y : k) ^ ((i : ℕ) + d + 1) =
        ((y : k) * (u : Matrix (Fin N) (Fin N) k) i j) * (y : k) ^ d := by
      rw [pow_succ, pow_add]
      field_simp
    rw [e]
    exact Subring.mul_mem _ (hyu i j) (Subring.pow_mem _ hy d)
  · have : i = j := Fin.ext hij
    subst this
    rw [h1 i, mul_one, inv_mul_cancel₀ (pow_ne_zero _ ha0)]
    exact Subring.one_mem _
  · rw [h0 i j (Fin.lt_def.2 hij), mul_zero, zero_mul]
    exact Subring.zero_mem _

theorem exhaust : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (N n : ℕ) (s : Finset (GL (Fin N) k)), (↑s : Set (GL (Fin N) k)) ⊆ derUnip k N n →
    ∃ L : Subgroup (GL (Fin N) k), L ≤ derUnip k N n ∧ (↑s : Set (GL (Fin N) k)) ⊆ L ∧
      IsCompact (L : Set (GL (Fin N) k)) := by
  intro k _ _ _ _ N n s hs
  have hmul : ∀ c : k, ∀ᶠ z in 𝓝 (0 : k), z * c ∈ 𝒪[k] := by
    intro c
    have h := (continuous_mul_right c).tendsto (0 : k)
    rw [zero_mul] at h
    exact h (isOpen_O.mem_nhds (Subring.zero_mem _))
  have hU : ∀ᶠ z in 𝓝 (0 : k), z ∈ 𝒪[k] ∧ ∀ g ∈ s, ∀ i j : Fin N,
      z * (g : Matrix (Fin N) (Fin N) k) i j ∈ 𝒪[k] ∧
        z * ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j ∈ 𝒪[k] :=
    (show ∀ᶠ z in 𝓝 (0 : k), z ∈ 𝒪[k] from isOpen_O.mem_nhds (Subring.zero_mem _)).and ((Filter.eventually_all_finset _).2 fun g _ =>
      Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => (hmul _).and (hmul _))
  obtain ⟨y, hy0, hyO, hyS⟩ := exists_ne_zero_mem hU
  set t := diagT k (Fin N) (fun l : Fin N => (Units.mk0 y hy0) ^ (l : ℕ)) with ht
  refine ⟨(intGL k N).map (MulAut.conj t).toMonoidHom ⊓ derUnip k N n, inf_le_right, ?_, ?_⟩
  · intro g hg
    have hgu : g ∈ unipB k (Fin N) := (hs hg).1
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_map.2 ⟨t⁻¹ * g * t, ?_, ?_⟩, hs hg⟩
    · intro i j
      have hinv : (t⁻¹ * g * t)⁻¹ = t⁻¹ * g⁻¹ * t := by group
      rw [hinv]
      exact ⟨conj_entry_mem (Units.mk0 y hy0) hyO hgu (fun i j => (hyS g hg i j).1) i j,
        conj_entry_mem (Units.mk0 y hy0) hyO (inv_mem hgu) (fun i j => (hyS g hg i j).2) i j⟩
    · show t * (t⁻¹ * g * t) * t⁻¹ = g
      group
  · rw [Subgroup.coe_inf, Subgroup.coe_map]
    have hc : Continuous fun g : GL (Fin N) k => t * g * t⁻¹ := by fun_prop
    exact ((isCompact_intGL N).image hc).inter_right (isClosed_derUnip N n)

end GlobalTheory.CompanionTheory.DerExhaust
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentRadicalDecompositionNormalStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_radical_decomposition_normal : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N), (∀ n ∈ unipB k (Fin N), ∃ a ∈ unipL k d hd, ∃ u ∈ unipU k d hd, n = a * u) ∧ ∀ n ∈ unipB k (Fin N), ∀ u ∈ unipU k d hd, n * u * n⁻¹ ∈ unipU k d hd := by
  first | exact @GlobalTheory.CompanionTheory.Rodier.unipB_eq_levi_mul_rad | exact GlobalTheory.CompanionTheory.Rodier.unipB_eq_levi_mul_rad | (intros; apply GlobalTheory.CompanionTheory.Rodier.unipB_eq_levi_mul_rad <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentRadicalStdBlocksEq
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.ParabolicCompare

theorem unipRad_stdBlocks_eq_unipotentRadical (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) :
    unipRad k (stdBlocks d hd) = GroundTheory.Automorphic.Parabolic.unipotentRadical k N (Zl.JC.blockIdx d hd) := by
  ext g
  rw [GlobalTheory.SmGL.mem_unipRad, GroundTheory.Automorphic.Parabolic.mem_unipotentRadical,
    GroundTheory.Automorphic.Iwasawa.mem_blockUpper, GlobalTheory.SmGL.mem_parab]
  refine and_congr Iff.rfl ⟨fun H i j hij => ?_, fun H a i j => ?_⟩
  · obtain ⟨⟨a, i⟩, rfl⟩ := (stdBlocks d hd).surjective i
    obtain ⟨⟨b, j⟩, rfl⟩ := (stdBlocks d hd).surjective j
    obtain rfl : a = b := by simpa [Zl.JC.blockIdx] using hij
    have := H a i j
    rw [this]
    by_cases e : i = j
    · subst e; simp
    · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne]
      intro h'
      exact e (by simpa using (stdBlocks d hd).injective h')
  · rw [H _ _ (by simp [Zl.JC.blockIdx])]
    by_cases e : i = j
    · subst e; simp
    · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne]
      intro h'
      exact e (by simpa using (stdBlocks d hd).injective h')

end GlobalTheory.CompanionTheory.ParabolicCompare
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationLtOneOfPowTendstoZero
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.Val

theorem valuation_lt_one_of_tendsto_pow_zero :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
      ∀ t : kˣ, Filter.Tendsto (fun n : ℕ => (t : k) ^ n) Filter.atTop (nhds 0) →
        ValuativeRel.valuation k (t : k) < 1 := by
  intro k _ _ _ _ t ht
  by_contra hge
  have hge' : 1 ≤ ValuativeRel.valuation k (t : k) := not_lt.mp hge
  have hU : {x : k | ValuativeRel.valuation k x < 1} ∈ nhds (0 : k) :=
    (IsValuativeTopology.hasBasis_nhds_zero' k).mem_of_mem one_ne_zero
  obtain ⟨n, hn⟩ := (ht.eventually hU).exists
  have hn' : ValuativeRel.valuation k ((t : k) ^ n) < 1 := hn
  rw [map_pow] at hn'
  exact absurd hn' (not_lt.mpr (one_le_pow₀ hge'))

end GlobalTheory.CompanionTheory.Val
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VoganMinimalTypeStatementStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vogan_minimal_type_statement : PositivityTheory.RgDs.Hilb.StepVogan := by
  first | exact @GlobalTheory.CompanionTheory.DiscreteSeries.stepVogan | exact GlobalTheory.CompanionTheory.DiscreteSeries.stepVogan | (intros; apply GlobalTheory.CompanionTheory.DiscreteSeries.stepVogan <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightVectorsSpanDenseStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_vectors_span_dense : PositivityTheory.RgDs.Hilb.StepWtSpan := by
  first | exact @GlobalTheory.CompanionTheory.RgDsHilb.stepWtSpan | exact GlobalTheory.CompanionTheory.RgDsHilb.stepWtSpan | (intros; apply GlobalTheory.CompanionTheory.RgDsHilb.stepWtSpan <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittChartDescendLevelStatement
section
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsG CrystallineSemistableComparison.Pb.SubquotientResolution CrystallineSemistableComparison.Pb.LsQ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_chart_descend_level : ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) {n : ℕ} (hn : n ≠ 0) {W : X.Opens} {d : ℕ} (c' : Chart (Wc.pd l k (n + 1)) l q ((Wc.res l k (n + 1)).comp ρ) W d), ∃ (c : Chart (Wc.pd l k n) l q ((Wc.res l k n).comp ρ) W d) (e : c.D ≅ (qF (F := B.schFn q) (ρ := ρ) hn).obj c'.D), (∀ i, e.hom.φ (c.t i) = Ideal.Quotient.mk _ (c'.t i)) ∧ (FlatT ((qF (F := B.schFn q) (ρ := ρ) hn).obj c'.D) → FlatT c.D) := by
  first | exact @GlobalTheory.CompanionTheory.ChartRed.chart_q | exact GlobalTheory.CompanionTheory.ChartRed.chart_q | (intros; apply GlobalTheory.CompanionTheory.ChartRed.chart_q <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittSiteRestrictBijective
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsG CrystallineSemistableComparison.Pb.SubquotientResolution

noncomputable section

namespace GlobalTheory.CompanionTheory.FlatZar

section Main
variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O] {X : Scheme.{0}}

def resG (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) (m : ℕ)
    (P Q : ObjectProperty (Thick (Wc.L l (B.schFn q) ρ m))) (h : Q ≤ P) :
    CH.Mor (P.ι ⋙ Wc.OM l (B.schFn q) ρ m) (Q.ι ⋙ Wc.OM l (B.schFn q) ρ m) (RingHom.id (WittVector l k)) where
  G := ObjectProperty.ιOfLE h
  τ _ := LinearMap.id
  nat _ _ := rfl

set_option maxHeartbeats 1600000 in
theorem resG_bij (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) (m : ℕ) (𝒱 : Set X.Opens) (hU : sSup 𝒱 = ⊤)
    (P : ObjectProperty (Thick (Wc.L l (B.schFn q) ρ m))) (hP : P = stF q ρ m {⊤}) (h : stF q ρ m 𝒱 ≤ P) (j : ℕ) :
    Function.Bijective ((resG q ρ m P (stF q ρ m 𝒱) h).pull j) := by
  subst hP
  have z := (zar (γ := Wc.pd l k m) (p := l) (q := q) (κ := (Wc.res l k m).comp ρ) FlatT
    (Or.inr ⟨(Fact.out : l.Prime).ne_zero, Or.inr rfl⟩) 𝒱 {⊤} h
    (fun W _ => by rw [hU]; exact le_top) j).2.2
  have c1 := GlobalTheory.CompanionTheory.FlatRes.scM_bij q ρ m (stF q ρ m {⊤}) j
  have c2 := GlobalTheory.CompanionTheory.FlatRes.scM_bij q ρ m (stF q ρ m 𝒱) j
  refine (Function.Bijective.of_comp_iff' c2 _).1 ?_
  have e : ⇑((GlobalTheory.CompanionTheory.FlatRes.scM q ρ m (stF q ρ m 𝒱)).pull j) ∘ ⇑((resG q ρ m _ (stF q ρ m 𝒱) h).pull j) =
      ⇑((incl h).o.pull j) ∘ ⇑((GlobalTheory.CompanionTheory.FlatRes.scM q ρ m (stF q ρ m {⊤})).pull j) := by
    funext x
    obtain ⟨a, ha, rfl⟩ := CrystallineSemistableComparison.CechClassBoundaries.clsSurj x
    rfl
  rw [e]
  exact z.comp c1

theorem resV_bij : ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) (m : ℕ) (𝒱 : Set X.Opens), sSup 𝒱 = ⊤ → ∀ j, Function.Bijective ((resV q ρ m 𝒱).pull j) := by
  intro l _ k _ _ _ O _ X q ρ m 𝒱 hU j
  exact resG_bij q ρ m 𝒱 hU (fl l (B.schFn q) ρ m)
    (GlobalTheory.CompanionTheory.FlatRes.st_top_eq (γ := Wc.pd l k m) (p := l) (q := q) (κ := (Wc.res l k m).comp ρ) FlatT).symm
    (fun _ h => h.1) j

end Main

end GlobalTheory.CompanionTheory.FlatZar

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WordOccursOfSubquotient
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace GlobalTheory.CompanionTheory.Words

theorem wd_of_isSubquotient {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (π : Representation ℂ (GL (Fin N) k) V) (σ : Representation ℂ (GL (Fin N) k) W)
    (hπ : IsSmooth π) (h : IsSubquotient σ π) (w : List (IrrGL k)) (hw : Wd σ w) : Wd π w := by
  obtain ⟨hd, hne⟩ := hw
  refine ⟨hd, ?_⟩
  exact jhMult_ne_zero_iff.2
    ((jhMult_ne_zero_iff.1 hne).trans (GlobalTheory.JacquetExact.isSubquotient_jac _ hπ h))

end GlobalTheory.CompanionTheory.Words
end

