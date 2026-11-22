import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0043
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsClosedFlagsIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniMatBlockTriangular
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0041
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0040
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0042

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialRepTransvectionEntries
section
open Matrix GlobalTheory.AlgWtHW

namespace GlobalTheory

theorem eval_transvection_polynomial_X_entry {n : ℕ} (i j : Fin n) (c : ℂ) (a b : Fin n) :
    Polynomial.eval c ((transvection i j (Polynomial.X : Polynomial ℂ)) a b) = transvection i j c a b := by
  simp only [transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  split_ifs <;> simp_all

theorem eval_transvection_polynomial_neg_X_entry {n : ℕ} (i j : Fin n) (c : ℂ) (a b : Fin n) :
    Polynomial.eval c ((transvection i j (-Polynomial.X : Polynomial ℂ)) a b) = transvection i j (-c) a b := by
  simp only [transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  split_ifs <;> simp_all

theorem eval_aeval_mv {σ : Type} (g : σ → Polynomial ℂ) (Q : MvPolynomial σ ℂ) (s : ℂ) :
    Polynomial.eval s (MvPolynomial.aeval g Q) = MvPolynomial.eval (fun v => (g v).eval s) Q := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p v hp => simp [hp]

theorem polyRep_transvection_entries_poly :
    ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ), IsPolyRep Φ →
      ∀ (i j : Fin n), i ≠ j → ∃ P : ι → ι → Polynomial ℂ, ∀ (s : ℂ) (B : GL (Fin n) ℂ),
        B.val = transvection i j s → ∀ a b, Φ B a b = (P a b).eval s := by
  intro n ι _ _ Φ hΦ i j hij
  choose Q hQ using hΦ.poly
  let g : (Fin n × Fin n) ⊕ (Fin n × Fin n) → Polynomial ℂ :=
    Sum.elim (fun p => transvection i j (Polynomial.X : Polynomial ℂ) p.1 p.2)
      (fun p => transvection i j (-Polynomial.X : Polynomial ℂ) p.1 p.2)
  refine ⟨fun a b => MvPolynomial.aeval g (Q a b), ?_⟩
  intro s B hB a b
  have hinv : (B⁻¹).val = transvection i j (-s) := by
    apply Units.inv_eq_of_mul_eq_one_right
    rw [hB]
    have := transvection_mul_transvection_same (R := ℂ) i j hij s (-s)
    rw [this, add_neg_cancel, transvection_zero]
  rw [hQ a b B, eval_aeval_mv]
  congr 2
  funext v
  rcases v with p | p
  · simp [g, eval_transvection_polynomial_X_entry, hB]
  · simp [g, eval_transvection_polynomial_neg_X_entry, hinv]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictHomApply
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module

namespace GlobalTheory.WeilDeligne.PrimDecomp

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

def IsSubWD (a : WDRep h V) (S : Submodule ℂ V) : Prop :=
  (∀ σ, ∀ v ∈ S, a.ρ σ v ∈ S) ∧ ∀ v ∈ S, a.N v ∈ S

def restrictHom (a : WDRep h V) (S : Submodule ℂ V) (hS : ∀ σ, ∀ v ∈ S, a.ρ σ v ∈ S) :
    Representation ℂ (Weil h) S where
  toFun σ := (a.ρ σ).restrict (hS σ)
  map_one' := by ext; simp
  map_mul' σ τ := by ext; simp

@[simp] theorem restrictHom_apply (a : WDRep h V) (S : Submodule ℂ V)
    (hS : ∀ σ, ∀ v ∈ S, a.ρ σ v ∈ S) (σ : Weil h) (v : S) :
    ((restrictHom a S hS σ v : S) : V) = a.ρ σ v := rfl

def restrict (a : WDRep h V) (S : Submodule ℂ V) (hS : IsSubWD a S) : WDRep h S where
  ρ := restrictHom a S hS.1
  N := a.N.restrict hS.2
  smooth := a.smooth.of_le fun σ hσ => by
    ext v; simp [restrictHom, hσ]
  semisimple σ := End.IsSemisimple.restrict (f := a.ρ σ) ((End.mem_invtSubmodule _).mpr (hS.1 σ))
    (a.semisimple σ)
  nilpotent := by
    obtain ⟨k, hk⟩ := a.nilpotent
    have hp : ∀ (j : ℕ) (v : S), (((a.N.restrict hS.2) ^ j) v : V) = (a.N ^ j) v := by
      intro j
      induction j with
      | zero => intro v; simp
      | succ j ih =>
        intro v
        rw [pow_succ', End.mul_apply, pow_succ', End.mul_apply, ← ih]
        rfl
    refine ⟨k, LinearMap.ext fun v => Subtype.ext ?_⟩
    rw [hp, hk]
    rfl
  comm σ := by
    ext v
    simp [restrictHom, a.comm_apply]

@[simp] theorem restrict_ρ_apply (a : WDRep h V) (S : Submodule ℂ V) (hS : IsSubWD a S)
    (σ : Weil h) (v : S) : (((restrict a S hS).ρ σ v : S) : V) = a.ρ σ v := rfl

@[simp] theorem restrict_N_apply (a : WDRep h V) (S : Submodule ℂ V) (hS : IsSubWD a S) (v : S) :
    (((restrict a S hS).N v : S) : V) = a.N v := rfl

def restrictρ (a : WDRep h V) (S : Submodule ℂ V) (hS : ∀ σ, ∀ v ∈ S, a.ρ σ v ∈ S) :
    WDRep h S where
  ρ := restrictHom a S hS
  N := 0
  smooth := a.smooth.of_le fun σ hσ => by
    ext v; simp [restrictHom, hσ]
  semisimple σ := End.IsSemisimple.restrict (f := a.ρ σ) ((End.mem_invtSubmodule _).mpr (hS σ))
    (a.semisimple σ)
  nilpotent := IsNilpotent.zero
  comm σ := by simp

@[simp] theorem restrictρ_ρ_apply (a : WDRep h V) (S : Submodule ℂ V)
    (hS : ∀ σ, ∀ v ∈ S, a.ρ σ v ∈ S) (σ : Weil h) (v : S) :
    (((restrictρ a S hS).ρ σ v : S) : V) = a.ρ σ v := rfl

@[simp] theorem restrictρ_N (a : WDRep h V) (S : Submodule ℂ V)
    (hS : ∀ σ, ∀ v ∈ S, a.ρ σ v ∈ S) : (restrictρ a S hS).N = 0 := rfl

def wtSpace (a : WDRep h V) (k : ℤ) : Submodule ℂ V :=
  absSpace (a.ρ (frob h)) (((normV w : ℕ) : ℝ) ^ ((k : ℝ) / 2))

def strand (N : End ℂ V) (S : Submodule ℂ V) (m : ℕ) : Submodule ℂ V :=
  ⨆ j : Fin (m + 1), S.map (N ^ (j : ℕ))

def lowPart (U : ℤ → Submodule ℂ V) (N : End ℂ V) (m : ℕ) : Submodule ℂ V :=
  ⨆ k : ℤ, U k ⊓ LinearMap.ker (N ^ (((m : ℤ) - k + 1) / 2).toNat)

example (a : WDRep h V) : IsSubWD a ⊤ ∧ IsSubWD a ⊥ :=
  ⟨⟨fun _ _ _ => trivial, fun _ _ => trivial⟩, ⟨fun _ v hv => by simp_all, fun v hv => by simp_all⟩⟩

theorem le_strand (N : End ℂ V) (S : Submodule ℂ V) (m : ℕ) : S ≤ strand N S m := by
  intro v hv
  exact Submodule.mem_iSup_of_mem (0 : Fin (m + 1)) ⟨v, hv, by simp⟩

end GlobalTheory.WeilDeligne.PrimDecomp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictScalarsHomContinuousKrull
section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat

namespace GlobalTheory

theorem restrictScalarsHom_continuous_krull (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω]
    (K : IntermediateField E Ω) :
    Continuous (AlgEquiv.restrictScalarsHom E : G K Ω →* G E Ω) := by
  apply continuous_of_continuousAt_one
  rw [ContinuousAt, map_one]
  intro s hs
  rw [krullTopology_mem_nhds_one_iff] at hs
  obtain ⟨L, hL, hLs⟩ := hs
  let b := Module.finBasis E L
  have hint : ∀ i, IsIntegral K ((b i : L) : Ω) := fun i =>
    ((IsIntegral.of_finite E (b i)).map (IsScalarTower.toAlgHom E L Ω)).tower_top
  have hN : ⋂ i, ((IntermediateField.adjoin K {((b i : L) : Ω)}).fixingSubgroup : Set (G K Ω))
      ∈ nhds (1 : G K Ω) := Filter.iInter_mem.mpr fun i => by
    haveI := IntermediateField.adjoin.finiteDimensional (hint i)
    exact (IntermediateField.fixingSubgroup_isOpen _).mem_nhds (Subgroup.one_mem _)
  rw [Filter.mem_map]
  refine Filter.mem_of_superset hN ?_
  intro σ hσ
  apply hLs
  simp only [Set.mem_iInter, SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hσ
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have hb : ∀ i, σ ((b i : L) : Ω) = ((b i : L) : Ω) := fun i =>
    hσ i _ (IntermediateField.mem_adjoin_simple_self K _)
  obtain ⟨y, rfl⟩ : ∃ y : L, (y : Ω) = x := ⟨⟨x, hx⟩, rfl⟩
  rw [← b.sum_repr y]
  change (AlgEquiv.restrictScalars E σ) _ = _
  simp only [IntermediateField.coe_sum, IntermediateField.coe_smul, map_sum, map_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [AlgEquiv.restrictScalars_apply, hb]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanRationalPointOrbitAlgebraicWeight
section
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

namespace GlobalTheory.AlgWtHW

theorem span_ratPt_orbit : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : AlgWt L n) (ι : Type) [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ a.W) (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ), Agrees a b P → ∀ v : ι → ℂ, v ≠ 0 → ∀ w : ι → ℂ, w ∈ Submodule.span ℂ {x | ∃ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n ∧ x = evM P (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) *ᵥ v} := by
  intro L _ _ _ n a ι _ _ b P hA v hv w
  classical
  set x : a.W := b.equivFun.symm v with hx
  have hxv : b.repr x = v := by
    rw [← Module.Basis.equivFun_apply, hx, LinearEquiv.apply_symm_apply]
  have hx0 : x ≠ 0 := by
    intro h
    apply hv
    rw [← hxv, h, map_zero]
    rfl
  let S0 : Submodule ℂ a.W := Submodule.span ℂ (Set.range fun γ : GQ L n => a.ρ γ x)
  have hinv : ∀ (g : GQ L n) (y : a.W), y ∈ S0 → a.ρ g y ∈ S0 := by
    intro g y hy
    have hle : S0 ≤ S0.comap (a.ρ g) := by
      rw [Submodule.span_le]
      rintro _ ⟨γ, rfl⟩
      show a.ρ g (a.ρ γ x) ∈ S0
      rw [← Module.End.mul_apply, ← map_mul]
      exact Submodule.subset_span ⟨g * γ, rfl⟩
    exact hle hy
  let S : Subrepresentation a.ρ := ⟨S0, hinv⟩
  have hxS : x ∈ S0 := Submodule.subset_span ⟨1, by simp⟩
  have hS0 : S0 = ⊤ := by
    haveI := a.irr
    rcases IsSimpleOrder.eq_bot_or_eq_top S with h | h
    · exfalso
      apply hx0
      have h2 : S.toSubmodule = (⊥ : Subrepresentation a.ρ).toSubmodule := congrArg _ h
      have h3 : x ∈ (⊥ : Subrepresentation a.ρ).toSubmodule := h2 ▸ hxS
      change x ∈ (⊥ : Submodule ℂ a.W) at h3
      exact (Submodule.mem_bot ℂ).1 h3
    · have h2 : S.toSubmodule = (⊤ : Subrepresentation a.ρ).toSubmodule := congrArg _ h
      exact h2
  have hw : w = b.equivFun.toLinearMap (b.equivFun.symm w) := (b.equivFun.apply_symm_apply w).symm
  have hmem : b.equivFun.symm w ∈ S0 := by rw [hS0]; trivial
  rw [hw]
  have hmap : Submodule.map b.equivFun.toLinearMap S0 ≤ Submodule.span ℂ {x | ∃ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n ∧ x = evM P (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) *ᵥ v} := by
    rw [Submodule.map_span_le]
    rintro _ ⟨γ, rfl⟩
    apply Submodule.subset_span
    have hγ : (γ : GA L n) ∈ ((GQ0 L n).map (Matrix.GeneralLinearGroup.map
        (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L))).subgroupOf (GA L n) := γ.2
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map] at hγ
    obtain ⟨γ₀, hγ₀, he⟩ := hγ
    refine ⟨γ₀, hγ₀, ?_⟩
    have hE : (((γ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
        (γ₀ : Matrix (Fin n) (Fin n) L).map (Algebra.TensorProduct.includeLeftRingHom) := by
      rw [← he]; rfl
    have hM := hA γ γ₀ hE
    show b.equivFun (a.ρ γ x) = _
    rw [Module.Basis.equivFun_apply, ← LinearMap.toMatrix_mulVec_repr b b, hxv, hM]
    rfl
  exact hmap (Submodule.mem_map_of_mem hmem)

end GlobalTheory.AlgWtHW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TemperedFrobeniusEigenvalueSizes
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne

theorem IsPurePair.absSpace_eq_bot_of_finrank_le {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] {q : ℝ} {f N : End ℂ V} (hp : IsPurePair q f N) (hN : IsNilpotent N)
    {i : ℤ} (hi : (finrank ℂ V : ℤ) ≤ |i|) : absSpace f (q ^ ((i : ℝ) / 2)) = ⊥ := by
  have h0 : N ^ finrank ℂ V = 0 := by
    have h1 := LinearMap.aeval_self_charpoly N
    rwa [hN.charpoly_eq_X_pow_finrank, map_pow, aeval_X] at h1
  have hk : ∀ k : ℕ, finrank ℂ V ≤ k → N ^ k = 0 := fun k hk => pow_eq_zero_of_le hk h0
  rw [eq_bot_iff]
  intro v hv
  rcases le_total 0 i with h | h
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le h
    have hv' : v ∈ absSpace f (q ^ ((k : ℝ) / 2)) := by simpa using hv
    obtain ⟨u, -, hu⟩ := (hp.2 k).2.2 hv'
    rw [hk k (by simpa using hi)] at hu
    simpa using hu.symm
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, i = -(k : ℤ) := ⟨(-i).toNat, by omega⟩
    have hv' : v ∈ absSpace f (q ^ (-(k : ℝ) / 2)) := by simpa using hv
    have := (hp.2 k).2.1 hv' (zero_mem _) (by simp [hk k (by simpa using hi)])
    simpa using this

end GlobalTheory.WeilDeligne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimFlags
section
set_option autoImplicit false

noncomputable section

open Module TopologicalSpace

namespace GlobalTheory.FlagPts

theorem card_lowerPairs (d : ℕ) : Fintype.card {p : Fin d × Fin d // p.2 < p.1} = d * (d - 1) / 2 := by
  rw [Fintype.card_subtype, ← Finset.sum_range_id, Finset.card_filter, ← Finset.univ_product_univ,
    Finset.sum_product, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.card_filter, Finset.filter_gt_eq_Iio, Fin.card_Iio]

theorem card_cellIdx {k : Type} [Field k] {ι : Type} [Fintype ι] {V : ι → Type} [∀ i, AddCommGroup (V i)]
    [∀ i, Module k (V i)] {n : ℕ} (hn : ∀ i, finrank k (V i) = n) :
    Fintype.card (CellIdx k V) = Fintype.card ι * (n * (n - 1) / 2) := by
  have h1 : Fintype.card (CellIdx k V) =
      ∑ i, Fintype.card {p : Fin (finrank k (V i)) × Fin (finrank k (V i)) // p.2 < p.1} := by
    unfold CellIdx
    convert Fintype.card_sigma (α := fun i => {p : Fin (finrank k (V i)) × Fin (finrank k (V i)) // p.2 < p.1})
  rw [h1]
  simp only [card_lowerPairs, hn, Finset.sum_const, Finset.card_univ, smul_eq_mul]

theorem isOpenEmbedding_cellMap {k : Type} [Field k] {ι : Type} [Fintype ι] {V : ι → Type} [∀ i, AddCommGroup (V i)]
    [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)] (b : Frames k V) :
    Topology.IsOpenEmbedding (cellMap b) :=
  .of_continuous_injective_isOpenMap (GlobalTheory.T.continuous_cellMap' k ι V b) (GlobalTheory.T.injective_cellMap k ι V b) (GlobalTheory.T.isOpenMap_cellMap' k ι V b)

theorem topologicalKrullDim_flags (k : Type) [Field k] [IsAlgClosed k] (ι : Type) [Fintype ι] (V : ι → Type)
    [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)] (n : ℕ)
    (hn : ∀ i, finrank k (V i) = n) :
    topologicalKrullDim (Flags k V) = (Fintype.card ι * (n * (n - 1) / 2) : ℕ) := by
  have hU : topologicalKrullDim (Set.univ : Set (Flags k V)) = topologicalKrullDim (Flags k V) :=
    (Homeomorph.Set.univ (Flags k V)).isHomeomorph.topologicalKrullDim_eq
  rw [← hU, ← card_cellIdx (k := k) (V := V) hn, ← GlobalTheory.T.topologicalKrullDim_affine_points k (CellIdx k V)]
  refine GlobalTheory.topologicalKrullDim_eq_of_forall_exists_isOpen Set.univ_nonempty fun F _ => ?_
  obtain ⟨b, rfl⟩ := flags_surjective F
  have he := isOpenEmbedding_cellMap b
  refine ⟨Set.range (cellMap b), he.isOpen_range, ⟨0, cellMap_zero b⟩, ?_⟩
  rw [Set.inter_univ]
  exact GlobalTheory.topologicalKrullDim_eq_of_isEmbedding he.isEmbedding rfl

example : ∀ (k : Type) [Field k] [IsAlgClosed k] (ι : Type) [Fintype ι] (V : ι → Type) [∀ i, AddCommGroup (V i)]
    [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)] (n : ℕ), (∀ i, finrank k (V i) = n) →
    topologicalKrullDim (Flags k V) = (Fintype.card ι * (n * (n - 1) / 2) : ℕ) :=
  topologicalKrullDim_flags

end GlobalTheory.FlagPts
end
end

