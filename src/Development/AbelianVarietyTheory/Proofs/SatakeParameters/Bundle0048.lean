import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Development.AutomorphicArithmetic.CyclotomicBounds.Bundle0001
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TateDualCrystalline
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0042

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JumpsMemBoxNegMH
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory

theorem HTW.WordData.jumps_mem_box {n : ℕ} (W : WordData n) (hsz : ∀ i, 0 ≤ W.sz i) (hT : W.T1) :
    ∀ i, ∀ u ∈ W.J1 i, -(W.Mi i : ℤ) ≤ u ∧ u ≤ W.hi i := by
  intro i u hu
  have h0 := hsz i
  have ht := Int.self_le_toNat (W.sz i + W.S)
  have hT' := hT i u hu
  have hm1 : (W.η : ℤ) ≤ max (W.η : ℤ) ((W.sz i + W.S).toNat : ℤ) := le_max_left _ _
  have hm2 : (((W.sz i + W.S).toNat : ℕ) : ℤ) ≤ max (W.η : ℤ) ((W.sz i + W.S).toNat : ℤ) :=
    le_max_right _ _
  rcases hT' with h | h
  · by_cases hup : W.up i
    · rw [if_pos hup] at h
      simp only [WordData.Mi, WordData.hi, if_pos hup, Nat.cast_max]
      omega
    · rw [if_neg hup] at h
      simp only [WordData.Mi, WordData.hi, if_neg hup, Nat.cast_max]
      omega
  · have h' := abs_le.mp h
    by_cases hup : W.up i
    · simp only [WordData.Mi, WordData.hi, if_pos hup, Nat.cast_max]
      omega
    · simp only [WordData.Mi, WordData.hi, if_neg hup, Nat.cast_max]
      omega

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LeastPowerDepthSpec
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory

theorem depth_spec : ∀ {D : D7} (L : SizeData₂ D) (_ : ParameterChoice' D L) (l : ℕ), 11 ≤ l →
    LevelStarExponents.lA L ≤ ((l : ℝ) - 1) ^ depth L l ∧ 2 * depth L l + 2 ≤ D.host.Lw ∧
      ((l : ℝ) < LevelStarExponents.lA L → 2 ≤ depth L l) := by
  intro D L P l hl
  obtain ⟨j, hj, hjL⟩ := P.Lw_j l hl
  have hne : ({j : ℕ | LevelStarExponents.lA L ≤ ((l : ℝ) - 1) ^ j} : Set ℕ).Nonempty := ⟨j, hj⟩
  have hmem : LevelStarExponents.lA L ≤ ((l : ℝ) - 1) ^ depth L l := Nat.sInf_mem hne
  have hle : depth L l ≤ j := Nat.sInf_le hj
  refine ⟨hmem, by omega, fun hlt => ?_⟩
  have hl' : (11 : ℝ) ≤ l := by exact_mod_cast hl
  by_contra hc
  push_neg at hc
  interval_cases h : depth L l
  · simp at hmem
    linarith
  · simp at hmem
    linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LtPrime
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.InertPrimeLarge

theorem lt_prime : ∀ {D : D7} (L : SizeData₂ D) (l : ℕ), l.Prime → l ≠ 2 →
    jacobiSym (-(D.host.d : ℤ)) l ≠ 1 → L.sc.x ^ (L.sc.ez / 5) < l := by
  intro D L l hl h2 hj
  by_contra hlt
  push_neg at hlt
  have hle : l ≤ D.host.splitBound := le_trans (Nat.le_floor hlt) L.split_tie
  exact hj (D.host.split_small l hl h2 hle)

end GlobalTheory.InertPrimeLarge
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrderOfEqMaxTwoOfSignNegImplicit
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory

theorem orderOf_moving (fr : Formalism.HC.Frame) (φ : fr.GG) (h : φ.1.2 = -1) : orderOf φ = Nat.lcm 2 (orderOf φ.2) :=
  UpperTheory.KStar.Words.orderOf_moving φ h

theorem orderOf_moving_stmt : ∀ {fr : Formalism.HC.Frame} (φ : fr.GG), φ.1.2 = -1 → orderOf φ = Nat.lcm 2 (orderOf φ.2) :=
  fun {fr} φ h => orderOf_moving fr φ h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PadicAlgClFiniteDenseEqAdjoin
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise

theorem GlobalTheory.padicAlgCl_finite_dense_eq_adjoin : ∀ (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [NumberField E] (c : E →+* PadicAlgCl l) (K : IntermediateField ℚ_[l] (PadicAlgCl l)), (∀ x, c x ∈ K) → FiniteDimensional ℚ_[l] K → (K : Set (PadicAlgCl l)) ⊆ closure (Set.range c) → K = IntermediateField.adjoin ℚ_[l] (Set.range c) := by
  intro l _ E _ _ c K hc hfin hdense
  have hle : IntermediateField.adjoin ℚ_[l] (Set.range c) ≤ K := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨x, rfl⟩; exact hc x
  have hKfin : FiniteDimensional ℚ_[l] K.toSubalgebra.toSubmodule := hfin
  have hAfin : FiniteDimensional ℚ_[l]
      (IntermediateField.adjoin ℚ_[l] (Set.range c)).toSubalgebra.toSubmodule :=
    Submodule.finiteDimensional_of_le (S₂ := K.toSubalgebra.toSubmodule) hle
  have hclosed : IsClosed ((IntermediateField.adjoin ℚ_[l] (Set.range c)).toSubalgebra.toSubmodule
      : Set (PadicAlgCl l)) :=
    Submodule.closed_of_finiteDimensional _
  apply le_antisymm _ hle
  intro y hy
  have h1 : closure (Set.range c) ⊆
      ((IntermediateField.adjoin ℚ_[l] (Set.range c)).toSubalgebra.toSubmodule : Set (PadicAlgCl l)) := by
    apply closure_minimal _ hclosed
    rintro _ ⟨x, rfl⟩
    exact IntermediateField.subset_adjoin _ _ ⟨x, rfl⟩
  exact h1 (hdense hy)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PageWordSEtaM
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem pageWord_S_eta_m : ∀ {D : D7} (L : SizeData₂ D) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG), ((pageWord L j ε τ φ).S : ℝ) ≤ L.Sc ∧ ((pageWord L j ε τ φ).η : ℝ) ≤ L.etaSz + D.R.t + 2 ∧ (pageWord L j ε τ φ).m = D.R.m := by
  intro D L j ε τ φ
  refine ⟨?_, ?_, rfl⟩
  · exact Nat.floor_le L.Sc_pos.le
  · have h := Nat.floor_le L.etaSz_pos.le
    show ((⌊L.etaSz⌋₊ + D.R.t + 2 : ℕ) : ℝ) ≤ _
    push_cast
    linarith

end GlobalTheory.HTW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodDataDeRhamAdmissible
section
open NumberField IsDedekindDomain GlobalTheory.HTW Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.FrobeniusOrbits

open TensorProduct Module

noncomputable section

namespace GlobalTheory.CrysSub

section Alg

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {W : Type} [AddCommGroup W] [Module LL W] [Module Qp W] [IsScalarTower Qp LL W]
    {U : Type} [AddCommGroup U] [Module LL U] [Module Qp U] [IsScalarTower Qp LL U]

theorem mem_Dcris (ρ : Representation LL G V) (x : V ⊗[Qp] B) :
    x ∈ Dcris PD ρ ↔ ∀ g, actVB PD ρ g x = x := by
  simp [Dcris, Submodule.mem_iInf, sub_eq_zero]

theorem rTensor_act (ρ : Representation LL G V) (σ : Representation LL G W) (f : V →ₗ[LL] W)
    (hf : ∀ g v, f (ρ g v) = σ g (f v)) (g : G) (x : V ⊗[Qp] B) :
    AlgebraTensorModule.rTensor Qp B f (actVB PD ρ g x) =
      actVB PD σ g (AlgebraTensorModule.rTensor Qp B f x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB, hf]
  | add x y hx hy => simp only [map_add, hx, hy]

def Dmap (ρ : Representation LL G V) (σ : Representation LL G W) (f : V →ₗ[LL] W)
    (hf : ∀ g v, f (ρ g v) = σ g (f v)) : Dcris PD ρ →ₗ[LL] Dcris PD σ :=
  (AlgebraTensorModule.rTensor Qp B f).restrict (fun x hx => by
    rw [mem_Dcris] at hx ⊢
    intro g
    rw [← rTensor_act PD ρ σ f hf, hx])

theorem coe_Dmap (ρ : Representation LL G V) (σ : Representation LL G W) (f : V →ₗ[LL] W)
    (hf : ∀ g v, f (ρ g v) = σ g (f v)) (x : Dcris PD ρ) :
    (Dmap PD ρ σ f hf x : W ⊗[Qp] B) = AlgebraTensorModule.rTensor Qp B f x := rfl

theorem rTensor_eq (f : V →ₗ[LL] W) (x : V ⊗[Qp] B) :
    AlgebraTensorModule.rTensor Qp B f x = (f.restrictScalars Qp).rTensor B x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp
  | add x y hx hy => simp only [map_add, hx, hy]

theorem exact_Dmap (ρ : Representation LL G V) (σ : Representation LL G W)
    (τ : Representation LL G U) (f : V →ₗ[LL] W) (q : W →ₗ[LL] U)
    (hf : ∀ g v, f (ρ g v) = σ g (f v)) (hq : ∀ g v, q (σ g v) = τ g (q v))
    (hi : Function.Injective f) (he : Function.Exact f q) (hs : Function.Surjective q) :
    LinearMap.ker (Dmap PD σ τ q hq) ≤ LinearMap.range (Dmap PD ρ σ f hf) := by
  intro x hx
  have h0 : (q.restrictScalars Qp).rTensor B (x : W ⊗[Qp] B) = 0 := by
    rw [← rTensor_eq, ← coe_Dmap PD σ τ q hq, LinearMap.mem_ker.mp hx]
    rfl
  have hex : Function.Exact ((f.restrictScalars Qp).rTensor B) ((q.restrictScalars Qp).rTensor B) :=
    rTensor_exact B (f := f.restrictScalars Qp) (g := q.restrictScalars Qp) he hs
  have hinj : Function.Injective ((f.restrictScalars Qp).rTensor B) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ hi
  obtain ⟨y, hy⟩ := (hex _).mp h0
  rw [← rTensor_eq] at hy
  refine ⟨⟨y, ?_⟩, Subtype.ext hy⟩
  rw [mem_Dcris]
  intro g
  apply hinj
  rw [← rTensor_eq, ← rTensor_eq, rTensor_act PD ρ σ f hf, hy]
  exact (mem_Dcris PD σ _).mp x.2 g

theorem finrank_le_of_ker_le {A₁ A₂ A₃ : Type} [AddCommGroup A₁] [Module LL A₁]
    [AddCommGroup A₂] [Module LL A₂] [AddCommGroup A₃] [Module LL A₃]
    [Module.Finite LL A₁] [Module.Finite LL A₃] (f : A₁ →ₗ[LL] A₂) (q : A₂ →ₗ[LL] A₃)
    (h : LinearMap.ker q ≤ LinearMap.range f) :
    Module.Finite LL A₂ ∧ finrank LL A₂ ≤ finrank LL A₁ + finrank LL A₃ := by
  have hk : Module.Finite LL (LinearMap.ker q) := Submodule.finiteDimensional_of_le h
  have hq : Module.Finite LL (A₂ ⧸ LinearMap.ker q) :=
    Module.Finite.equiv (q.quotKerEquivRange).symm
  have h2 : Module.Finite LL A₂ := Module.Finite.of_submodule_quotient (LinearMap.ker q)
  refine ⟨h2, ?_⟩
  have h3 := q.finrank_range_add_finrank_ker
  have h4 := Submodule.finrank_mono h
  have h5 := f.finrank_range_le
  have h6 := (LinearMap.range q).finrank_le
  omega

def piRep {m : ℕ} (ρ : Fin m → Representation LL G V) : Representation LL G (Fin m → V) where
  toFun g := LinearMap.pi fun a => (ρ a g).comp (LinearMap.proj a)
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

theorem piRep_apply {m : ℕ} (ρ : Fin m → Representation LL G V) (g : G) (v : Fin m → V)
    (a : Fin m) : piRep ρ g v a = ρ a g (v a) := rfl

theorem sum_le_finrank_piRep {m : ℕ} (ρ : Fin m → Representation LL G V)
    [Module.Finite LL (Dcris PD (piRep ρ))] :
    ∑ a, finrank LL (Dcris PD (ρ a)) ≤ finrank LL (Dcris PD (piRep ρ)) := by
  have hp : ∀ a g v, (LinearMap.proj a : (Fin m → V) →ₗ[LL] V) (piRep ρ g v) =
      ρ a g ((LinearMap.proj a : (Fin m → V) →ₗ[LL] V) v) := fun a g v => rfl
  have hs : ∀ a g v, (LinearMap.single LL (fun _ : Fin m => V) a) (ρ a g v) =
      piRep ρ g (LinearMap.single LL (fun _ : Fin m => V) a v) := by
    intro a g v
    funext b
    rw [piRep_apply]
    by_cases h : b = a
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  let F : Dcris PD (piRep ρ) →ₗ[LL] (∀ a, Dcris PD (ρ a)) :=
    LinearMap.pi fun a => Dmap PD _ _ _ (hp a)
  have key : ∀ (a b : Fin m) (x : V ⊗[Qp] B),
      AlgebraTensorModule.rTensor Qp B (LinearMap.proj b : (Fin m → V) →ₗ[LL] V)
        (AlgebraTensorModule.rTensor Qp B (LinearMap.single LL (fun _ : Fin m => V) a) x) =
        if a = b then x else 0 := by
    intro a b x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v c =>
      by_cases h : a = b
      · subst h; simp
      · simp [h, Pi.single_eq_of_ne (Ne.symm h)]
    | add x y hx hy =>
      simp only [map_add, hx, hy]
      split_ifs <;> simp
  have hF : Function.Surjective F := by
    intro y
    refine ⟨∑ a, Dmap PD _ _ _ (hs a) (y a), ?_⟩
    funext b
    apply Subtype.ext
    simp only [F, LinearMap.pi_apply, coe_Dmap, Submodule.coe_sum, map_sum, key]
    simp
  have h1 : Module.Finite LL (∀ a, Dcris PD (ρ a)) := Module.Finite.of_surjective F hF
  have h2 : ∀ a, Module.Finite LL (Dcris PD (ρ a)) := fun a =>
    Module.Finite.of_surjective (LinearMap.proj a : (∀ a, Dcris PD (ρ a)) →ₗ[LL] _)
      (LinearMap.proj_surjective a)
  rw [← Module.finrank_pi_fintype]
  exact LinearMap.finrank_le_finrank_of_surjective hF

end Alg

theorem isCrys_of_isSubOfSums : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] [TopologicalSpace Qp] (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] {O : Type} [CommRing O] [Algebra O LL], Formalism.MainNotions.LocalSituation.fontCore PD → GoodO (Qp := Qp) LL O → ∀ (A : GRep G Qp LL O) {ι : Type} {k : ℕ} (Ms : ι → (G →* Matrix (Fin k) (Fin k) LL)), (∀ x, Continuous (Ms x)) → IsSubOfSums A.ρ (fun x g => Ms x g) → (∀ x, IsCrys PD (matRep (Ms x))) → IsCrys PD A.ρ := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ _ O _ _ hF hO A ι k Ms
    hc hsub hcr
  obtain ⟨m, xs, j, hj, hjg⟩ := hsub
  have htr : IsTopologicalRing LL := hO.2.2.2.1
  let σ : Representation LL G (Fin m → Fin k → LL) := piRep fun a => matRep (Ms (xs a))
  have hσ : ∀ g v a, σ g v a = (Ms (xs a) g).mulVec (v a) := by
    intro g v a
    simp [σ, piRep_apply, matRep, Matrix.toLinAlgEquiv'_apply]
  have hjσ : ∀ g v, j (A.ρ g v) = σ g (j v) := by
    intro g v
    rw [hjg]
    funext a
    rw [hσ]
  have hst : ∀ g, LinearMap.range j ≤ (LinearMap.range j).comap (σ g) := by
    rintro g _ ⟨v, rfl⟩
    exact ⟨A.ρ g v, hjσ g v⟩
  have hσc : ∀ v, Continuous fun g => σ g v := by
    intro v
    refine continuous_pi fun a => ?_
    simp only [hσ]
    exact (hc (xs a)).matrix_mulVec continuous_const
  let τ := σ.quotient (LinearMap.range j) hst
  have hτ : ∀ g v, (LinearMap.range j).mkQ (σ g v) = τ g ((LinearMap.range j).mkQ v) :=
    fun g v => rfl
  have : ContinuousSMul LL ((Fin m → Fin k → LL) ⧸ LinearMap.range j) :=
    IsModuleTopology.toContinuousSMul _ _
  let Q : GRep G Qp LL O :=
    { V := (Fin m → Fin k → LL) ⧸ LinearMap.range j
      ρ := τ
      cont := by
        intro x
        obtain ⟨v, rfl⟩ := (LinearMap.range j).mkQ_surjective x
        simp only [← hτ]
        exact continuous_quot_mk.comp (hσc v) }
  obtain ⟨⟨fA, lA⟩, -⟩ := hF LL O hO A
  obtain ⟨⟨fQ, lQ⟩, -⟩ := hF LL O hO Q
  have fQ' : Module.Finite LL (Dcris PD τ) := fQ
  have lQ' : finrank LL (Dcris PD τ) ≤
    finrank Qp K₀ * finrank LL ((Fin m → Fin k → LL) ⧸ LinearMap.range j) := lQ
  obtain ⟨fS, lS⟩ := finrank_le_of_ker_le _ _
    (exact_Dmap PD A.ρ σ τ j (LinearMap.range j).mkQ hjσ hτ hj
      (LinearMap.exact_map_mkQ_range j) (LinearMap.range j).mkQ_surjective)
  have h1 := sum_le_finrank_piRep PD (fun a => matRep (Ms (xs a)))
  have h2 : ∀ a, finrank LL (Dcris PD (matRep (Ms (xs a)))) = finrank Qp K₀ * k := by
    intro a
    have := hcr (xs a)
    rw [IsCrys] at this
    rw [this]
    simp
  simp only [h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h1
  have h3 := (LinearMap.range j).finrank_quotient_add_finrank
  rw [LinearMap.finrank_range_of_inj hj] at h3
  have h4 : finrank LL (Fin m → Fin k → LL) = m * k := by
    simp [Module.finrank_pi_fintype]
  have h5 : m * (finrank Qp K₀ * k) =
      finrank Qp K₀ * finrank LL ((Fin m → Fin k → LL) ⧸ LinearMap.range j) +
        finrank Qp K₀ * finrank LL A.V := by
    rw [← mul_add, h3, h4]; ring
  have h6 : finrank LL (Dcris PD (piRep fun a => matRep (Ms (xs a)))) = finrank LL (Dcris PD σ) := rfl
  rw [IsCrys]
  omega

end GlobalTheory.CrysSub
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodDataProperties
section
open NumberField IsDedekindDomain GlobalTheory.HTW Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.FrobeniusOrbits
open TensorProduct

namespace GlobalTheory.SubSumJumps

section
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

theorem map_mem_FilV (f : V →ₗ[LL] V') (a : ℤ) (x : V ⊗[Qp] BdR)
    (hx : x ∈ FilV PD (LL := LL) (V := V) a) :
    AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) x
      ∈ FilV PD (LL := LL) (V := V') a := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨AlgebraTensorModule.map f LinearMap.id y, ?_⟩
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp
  | add y z hy hz => simp only [map_add, hy, hz]

theorem map_mem_DdRE (ρ : Representation LL G V) (ρ' : Representation LL G V') (f : V →ₗ[LL] V')
    (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) (τ : K →ₐ[Qp] LL) (x : V ⊗[Qp] BdR)
    (hx : x ∈ DdRE PD ρ τ) :
    AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) x ∈ DdRE PD ρ' τ := by
  have h1 : ∀ (g : G) (y : V ⊗[Qp] BdR),
      actVdR PD ρ' g (AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) y)
        = AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) (actVdR PD ρ g y) := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [actVdR, hf]
    | add y z hy hz => simp only [map_add, hy, hz]
  have h2 : ∀ (c : K) (y : V ⊗[Qp] BdR),
      mulVdR (K := K) (BdR := BdR) (V := V') (LL := LL) c
        (AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) y)
        = AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR)
          (mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) c y) := by
    intro c y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [mulVdR]
    | add y z hy hz => simp only [map_add, hy, hz]
  simp only [DdRE, DdR, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply, sub_eq_zero] at hx ⊢
  refine ⟨fun g => ?_, fun c => ?_⟩
  · rw [h1, hx.1 g]
  · rw [h2, hx.2 c, map_smul]

theorem FilV_anti (a : ℤ) :
    FilV PD (LL := LL) (V := V) (a + 1) ≤ FilV PD (LL := LL) (V := V) a := by
  rintro x ⟨y, rfl⟩
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => exact ⟨v ⊗ₜ ⟨b.1, PD.Fil_anti a b.2⟩, by simp⟩
  | add y z hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz

end

theorem jumpsInV_of_isSubOfSums : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] (ρ : Representation LL G V) {ι : Type} {k : ℕ} (Ms : ι → (G →* Matrix (Fin k) (Fin k) LL)) (τ : K →ₐ[Qp] LL) (J : Set ℤ), IsSubOfSums ρ (fun x g => Ms x g) → (∀ x, JumpsInV PD (matRep (Ms x)) τ J) → JumpsInV PD ρ τ J := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ V _ _ _ _ ρ ι k Ms τ J
    hsub hJ a ha
  by_contra haJ
  apply ha
  obtain ⟨m, xs, j, hj, hje⟩ := hsub
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective j (LinearMap.ker_eq_bot.2 hj)
  have hrv : ∀ v, r (j v) = v := fun v => LinearMap.congr_fun hr v
  apply le_antisymm
  · exact inf_le_inf_left _ (FilV_anti PD a)
  intro x hx
  refine ⟨hx.1, ?_⟩
  let p : Fin m → (V →ₗ[LL] (Fin k → LL)) := fun b => (LinearMap.proj b).comp j
  let s : Fin m → ((Fin k → LL) →ₗ[LL] V) := fun b =>
    r.comp (LinearMap.single LL (fun _ : Fin m => Fin k → LL) b)
  have hdec : ∀ y : V ⊗[Qp] BdR, y = ∑ b, AlgebraTensorModule.map (s b)
      (LinearMap.id : BdR →ₗ[Qp] BdR)
      (AlgebraTensorModule.map (p b) (LinearMap.id : BdR →ₗ[Qp] BdR) y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v c =>
      simp only [AlgebraTensorModule.map_tmul, LinearMap.id_apply, ← TensorProduct.sum_tmul]
      congr 1
      simp only [s, p, LinearMap.comp_apply, ← map_sum]
      conv_lhs => rw [← hrv v]
      congr 1
      exact (Finset.univ_sum_single (j v)).symm
    | add y z hy hz =>
      simp only [map_add, Finset.sum_add_distrib]
      rw [← hy, ← hz]
  rw [hdec x]
  refine Submodule.sum_mem _ fun b _ => map_mem_FilV PD (s b) (a + 1) _ ?_
  have heq : FildR PD (matRep (Ms (xs b))) τ (a + 1) = FildR PD (matRep (Ms (xs b))) τ a := by
    by_contra h
    exact haJ (hJ (xs b) a h)
  have hm : AlgebraTensorModule.map (p b) (LinearMap.id : BdR →ₗ[Qp] BdR) x
      ∈ FildR PD (matRep (Ms (xs b))) τ a := by
    refine ⟨map_mem_DdRE PD ρ _ (p b) (fun g v => ?_) τ x hx.1, map_mem_FilV PD (p b) a x hx.2⟩
    simp [p, hje, matRep, Matrix.toLinAlgEquiv'_apply]
  rw [← heq] at hm
  exact hm.2

end GlobalTheory.SubSumJumps
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PointDeterminedBySplitComponentsOfBaseChange
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.PtOfLocSplit

theorem eventually_splitOut {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc) :
    ∀ᶠ w in Filter.cofinite, IsSplitPl H w → SplitOut N i w := by
  have hl : (N.l i).Prime := Fact.out
  have hfin : (placesOver H.E (N.l i)).Finite := by
    have h0 : Ideal.span {((N.l i : ℕ) : 𝓞 H.E)} ≠ 0 := by simpa using hl.ne_zero
    refine (Ideal.finite_factors h0).subset fun v hv => ?_
    exact Ideal.dvd_span_singleton.2 hv
  filter_upwards [hfin.eventually_cofinite_notMem, (N.S i).eventually_cofinite_notMem,
    (N.Q i).eventually_cofinite_notMem] with w h1 h2 h3 hw using ⟨hw, h1, h2, h3⟩

theorem main : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N) (i : N.Loc), GlobalTheory.RowTie.BCEx N A i → GlobalTheory.RowTie.SplitBC N A i → GlobalTheory.RowTie.RepOfLoc N A i → GlobalTheory.ThetaExh.PtOfLoc N A i := by
  intro R H what₂ N A i hBC hSp hRep P P' x hx hloc
  have hPP : P = P' := GlobalTheory.T.automorphicRep_eq_of_eq_at_almost_all_split_places R H what₂ N A i hBC hSp hRep P P' <| by
    filter_upwards [eventually_splitOut N i] with w hw hs using hloc w (hw hs)
  rw [hPP]; exact hx

end GlobalTheory.PtOfLocSplit
end

