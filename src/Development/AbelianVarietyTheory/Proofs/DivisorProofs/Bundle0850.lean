import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.LtChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0836
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0304
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.OrthSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0567
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0066
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0130
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0021
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0799
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0841

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisEquivariantPeriodFamily
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.PMC GlobalTheory.AinfK GlobalTheory.AcrisK GlobalTheory.BKReal GlobalTheory.ConjPeriod
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PMC.DdRLine

theorem exists_sep (F E : Type) [Field F] [CharZero F] [Field E] [Algebra F E] [FiniteDimensional F E] :
    ∃ e : E ⊗[F] E, (∀ a : E, (a ⊗ₜ[F] (1 : E)) * e = ((1 : E) ⊗ₜ[F] a) * e) ∧
      Algebra.TensorProduct.lmul' F e = 1 := by
  have : Algebra.FormallyUnramified F E := Algebra.FormallyUnramified.of_isSeparable F E
  obtain ⟨t, h1, h2⟩ := (Algebra.FormallyUnramified.iff_exists_tensorProduct (R := F) (S := E)).1 this
  refine ⟨t, fun a => ?_, h2⟩
  have := h1 a
  rw [sub_mul, sub_eq_zero] at this
  exact this.symm

open Classical in

theorem pair_sep {F E Ω : Type} [Field F] [Field E] [Field Ω] [Algebra F E] [Algebra F Ω]
    (e : E ⊗[F] E) (h1 : ∀ a : E, (a ⊗ₜ[F] (1 : E)) * e = ((1 : E) ⊗ₜ[F] a) * e)
    (h2 : Algebra.TensorProduct.lmul' F e = 1) (ν ν' : E →ₐ[F] Ω) :
    Algebra.TensorProduct.productMap ν ν' e = if ν = ν' then 1 else 0 := by
  split_ifs with h
  · subst h
    have : Algebra.TensorProduct.productMap ν ν = ν.comp (Algebra.TensorProduct.lmul' F) := by
      ext a <;> simp
    rw [this, AlgHom.comp_apply, h2, map_one]
  · obtain ⟨a, ha⟩ : ∃ a, ν a ≠ ν' a := by
      by_contra hc
      exact h (AlgHom.ext fun a => by_contra fun h' => hc ⟨a, h'⟩)
    have := congrArg (Algebra.TensorProduct.productMap ν ν') (h1 a)
    simp only [map_mul, Algebra.TensorProduct.productMap_apply_tmul, map_one, mul_one, one_mul] at this
    have h3 : (ν a - ν' a) * Algebra.TensorProduct.productMap ν ν' e = 0 := by
      rw [sub_mul, this, sub_self]
    exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 ha)

theorem exists_glue {G F K₀ K B D E Ω : Type} [Group G] [Field F] [CharZero F] [Field K₀] [Field K]
    [Algebra F K₀] [Algebra F K] [Algebra K₀ K] [IsScalarTower F K₀ K]
    [CommRing B] [CommRing D] [Algebra F B] [Algebra K₀ B] [IsScalarTower F K₀ B]
    [Algebra F D] [Algebra K₀ D] [Algebra K D] [IsScalarTower F K D]
    [IsScalarTower K₀ K D] [IsScalarTower F K₀ D] (PD : PeriodData G F K₀ K B D)
    [Field E] [Algebra F E] [FiniteDimensional F E] [Field Ω] [Algebra F Ω]
    (j : Ω →ₐ[F] D) (s : G → (Ω ≃ₐ[F] Ω)) (hs : ∀ g ω, PD.actdR g (j ω) = j (s g ω))
    (μ : G →* Eˣ) (ρ : Representation E G (Fin 1 → E)) (hρ : ∀ g v, ρ g v = (μ g : E) • v)
    (τ : K →ₐ[F] E) (y : (E →ₐ[F] Ω) → D) (hΩ : ∀ ω, j ω ∈ PD.Fil 0) (hy : ∀ ν, y ν ∈ PD.Fil 0)
    (hG : ∀ g (ν : E →ₐ[F] Ω), j (s g (ν (μ g : E))) * PD.actdR g (y ν) = y ((s g).toAlgHom.comp ν))
    (hK : ∀ (ν : E →ₐ[F] Ω) (c : K), j (ν (τ c)) * y ν = algebraMap K D c * y ν) :
    ∃ x ∈ DdRE PD ρ τ, x ∈ FilV PD (LL := E) (V := Fin 1 → E) 0 ∧
      ∀ (ν : E →ₐ[F] Ω) (f : (Fin 1 → E) ⊗[F] D →ₗ[F] D),
        (∀ v b, f (v ⊗ₜ b) = j (ν (v 0)) * b) → f x = y ν := by
  classical
  obtain ⟨e, h1, h2⟩ := exists_sep F E
  obtain ⟨L₁, hL₁⟩ : ∃ L₁ : E →ₗ[F] (Fin 1 → E), ∀ a, L₁ a = fun _ => a :=
    ⟨LinearMap.pi fun _ => LinearMap.id, fun _ => rfl⟩
  obtain ⟨L₂, hL₂⟩ : ∃ L₂ : E →ₗ[F] D, ∀ b, L₂ b = ∑ ν : E →ₐ[F] Ω, j (ν b) * y ν :=
    ⟨∑ ν : E →ₐ[F] Ω, LinearMap.mulRight F (y ν) ∘ₗ (j.comp ν).toLinearMap, fun b => by
      simp [LinearMap.sum_apply]⟩
  have hsm : ∀ c a : E, c • L₁ a = L₁ (c * a) := fun c a => by
    rw [hL₁, hL₁]; rfl
  have hact : ∀ g b, PD.actdR g (L₂ b) = L₂ ((((μ g)⁻¹ : Eˣ) : E) * b) := fun g b => by
    let q : (E →ₐ[F] Ω) ≃ (E →ₐ[F] Ω) :=
      { toFun := fun ν => (s g).toAlgHom.comp ν
        invFun := fun ν => (s g).symm.toAlgHom.comp ν
        left_inv := fun ν => by ext a; simp
        right_inv := fun ν => by ext a; simp }
    rw [hL₂, hL₂, map_sum]
    conv_rhs => rw [← q.sum_comp]
    refine Finset.sum_congr rfl fun ν _ => ?_
    change _ = j (s g (ν _)) * y ((s g).toAlgHom.comp ν)
    rw [← hG, ← mul_assoc, ← map_mul, ← map_mul, ← map_mul, mul_right_comm, Units.inv_mul, one_mul, map_mul, hs]
  have hmul : ∀ (c : K) b, algebraMap K D c * L₂ b = L₂ (τ c * b) := fun c b => by
    rw [hL₂, hL₂, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [mul_left_comm, ← hK, map_mul, map_mul]
    ring
  let Ψ : E ⊗[F] E →ₗ[F] (Fin 1 → E) ⊗[F] D := TensorProduct.map L₁ L₂
  have hΨ : ∀ a b, Ψ (a ⊗ₜ b) = L₁ a ⊗ₜ L₂ b := fun _ _ => rfl
  have hA : ∀ g t, actVdR PD ρ g (Ψ t) = Ψ (((μ g : E) ⊗ₜ[F] (((μ g)⁻¹ : Eˣ) : E)) * t) := fun g t => by
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero, mul_zero]
    | tmul a b =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, hΨ, hΨ, ← hsm, ← hact, ← hρ]
      rfl
    | add a b ha hb => simp only [map_add, mul_add, ha, hb]
  have hM : ∀ (c : K) t, mulVdR (Qp := F) (K := K) (BdR := D) (V := Fin 1 → E) (LL := E) c (Ψ t) =
      Ψ (((1 : E) ⊗ₜ[F] τ c) * t) := fun c t => by
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero, mul_zero]
    | tmul a b =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, hΨ, hΨ, ← hmul, one_mul]
      rfl
    | add a b ha hb => simp only [map_add, mul_add, ha, hb]
  have hS : ∀ (c : E) t, c • Ψ t = Ψ ((c ⊗ₜ[F] (1 : E)) * t) := fun c t => by
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero, mul_zero, smul_zero]
    | tmul a b => rw [Algebra.TensorProduct.tmul_mul_tmul, hΨ, hΨ, ← hsm, one_mul, TensorProduct.smul_tmul']
    | add a b ha hb => simp only [map_add, mul_add, smul_add, ha, hb]
  refine ⟨Ψ e, ⟨?_, ?_⟩, ?_, fun ν f hf => ?_⟩
  · simp only [DdR, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero]
    intro g
    have h3 : ((μ g : E) ⊗ₜ[F] (((μ g)⁻¹ : Eˣ) : E)) =
        ((1 : E) ⊗ₜ[F] (((μ g)⁻¹ : Eˣ) : E)) * ((μ g : E) ⊗ₜ[F] (1 : E)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    rw [hA, h3, mul_assoc, h1, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, Units.inv_mul, one_mul,
      ← Algebra.TensorProduct.one_def, one_mul]
  · simp only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    intro c
    rw [hM, hS, h1]
  · generalize e = t
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact zero_mem _
    | tmul a b =>
      have hb : L₂ b ∈ PD.Fil 0 := by
        rw [hL₂]
        exact Submodule.sum_mem _ fun ν _ => by simpa using PD.Fil_mul 0 0 _ _ (hΩ (ν b)) (hy ν)
      exact ⟨L₁ a ⊗ₜ ⟨L₂ b, hb⟩, rfl⟩
    | add a b ha hb => rw [map_add]; exact add_mem ha hb
  · have h4 : ∀ t, f (Ψ t) = ∑ ν' : E →ₐ[F] Ω, j (Algebra.TensorProduct.productMap ν ν' t) * y ν' := fun t => by
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul a b =>
        rw [hΨ, hf, hL₁, hL₂, Finset.mul_sum]
        refine Finset.sum_congr rfl fun ν' _ => ?_
        rw [Algebra.TensorProduct.productMap_apply_tmul, map_mul, mul_assoc]
      | add a b ha hb => simp only [map_add, ha, hb, add_mul, Finset.sum_add_distrib]
    rw [h4, Finset.sum_eq_single ν]
    · rw [pair_sep e h1 h2, if_pos rfl, map_one, one_mul]
    · intro ν' _ hne
      rw [pair_sep e h1 h2, if_neg (Ne.symm hne), map_zero, zero_mul]
    · exact fun h => absurd (Finset.mem_univ ν) h

theorem main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l)
    (μ : ↥(GK K) →* (↥LL.1)ˣ) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (y : (↥LL.1 →ₐ[ℚ_[l]] Om l) → P.R.BdR),
    (∀ ω : Om l, algebraMap (Om l) P.R.BdR ω ∈ (P.PD K).Fil 0) →
    (∀ ν, y ν ∈ (P.PD K).Fil 0) →
    (∀ (g : ↥(GK K)) (ν : ↥LL.1 →ₐ[ℚ_[l]] Om l),
      algebraMap (Om l) P.R.BdR ((g : GQ l) (ν (μ g : ↥LL.1))) * P.actQdR (g : GQ l) (y ν) =
        y ((g : GQ l).toAlgHom.comp ν)) →
    (∀ (ν : ↥LL.1 →ₐ[ℚ_[l]] Om l) (c : ↥K.1),
      algebraMap (Om l) P.R.BdR (ν (τ c)) * y ν = algebraMap ↥K.1 P.R.BdR c * y ν) →
    ∃ x ∈ DdRE (P.PD K) (lineRep (K := K) (LL := LL) μ) τ,
      x ∈ FilV (P.PD K) (LL := ↥LL.1) (V := Fin 1 → ↥LL.1) 0 ∧
      ∀ (ν : ↥LL.1 →ₐ[ℚ_[l]] Om l) (f : (Fin 1 → ↥LL.1) ⊗[ℚ_[l]] P.R.BdR →ₗ[ℚ_[l]] P.R.BdR),
        (∀ v b, f (v ⊗ₜ b) = algebraMap (Om l) P.R.BdR (ν (v 0)) * b) → f x = y ν := by
  intro l _ P K LL μ τ y hΩ hy hG hK
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  exact exists_glue (P.PD K) (IsScalarTower.toAlgHom ℚ_[l] (Om l) P.R.BdR) (fun g => (g : GQ l))
    (fun g ω => by rw [P.PD_actdR]; exact P.actQdR_Om _ _) μ _ (fun _ _ => rfl) τ y hΩ hy
    (fun g ν => by rw [P.PD_actdR]; exact hG g ν) hK

end GlobalTheory.PMC.DdRLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerRealizeEqZero
section
open NumberField IsDedekindDomain Formalism.BasicNotions GlobalTheory.AllWt GlobalTheory.FlatLine

noncomputable section

namespace GlobalTheory.OrthRankDeg

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]

theorem gram_zero [StarRing K] {n : ℕ} {b : Module.Basis (Fin n) K V}
    {X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ} {N : (K →+* ℂ) → V → ℝ}
    (hG : GlobalTheory.AllWt.IsGram b X N) (v : InfinitePlace K) : N v.embedding 0 = 0 := by
  rw [← (hG v).2 0]
  simp [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm, Formalism.HermitianLatticesTheory.fcoord_zero]

theorem inner_realize_eq_zero [StarRing K] {n : ℕ} {b : Module.Basis (Fin n) K V}
    {X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ} {N : (K →+* ℂ) → V → ℝ}
    (hG : GlobalTheory.AllWt.IsGram b X N) {x y : V}
    (h : ∀ v : InfinitePlace K, N v.embedding (x + y) ^ 2 = N v.embedding x ^ 2 + N v.embedding y ^ 2) :
    inner ℝ (Formalism.HermitianLatticesTheory.realize b X x) (Formalism.HermitianLatticesTheory.realize b X y) = 0 := by
  have hs : ∀ z, ‖Formalism.HermitianLatticesTheory.realize b X z‖ ^ 2 = ∑ v : InfinitePlace K, N v.embedding z ^ 2 := fun z => by
    rw [GlobalTheory.AllWt.norm_realize_sq]
    exact Finset.sum_congr rfl fun v _ => by rw [(hG v).2]
  have h1 := hs (x + y)
  rw [map_add, norm_add_sq_real, hs x, hs y] at h1
  rw [Finset.sum_congr rfl fun v _ => h v, Finset.sum_add_distrib] at h1
  linarith

variable [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem inner_pair [StarRing K] {n : ℕ} {b : Module.Basis (Fin n) K V}
    {X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ} {N : (K →+* ℂ) → V → ℝ}
    (hG : GlobalTheory.AllWt.IsGram b X N) {ι : Type} [Fintype ι] [DecidableEq ι] (M : ι → Submodule (𝓞 K) V)
    (hN : ∀ σ, ∀ f : ι → V, (∀ i, f i ∈ Submodule.span K (M i : Set V)) →
      N σ (∑ i, f i) ^ 2 = ∑ i, N σ (f i) ^ 2)
    {i j : ι} (hij : i ≠ j) {x y : V} (hx : x ∈ M i) (hy : y ∈ M j) :
    inner ℝ (Formalism.HermitianLatticesTheory.realize b X x) (Formalism.HermitianLatticesTheory.realize b X y) = 0 := by
  refine inner_realize_eq_zero hG fun v => ?_
  have hmem : ∀ (k : ι) (z : V) (_ : z ∈ M k) (l : ι),
      (Pi.single k z : ι → V) l ∈ Submodule.span K (M l : Set V) := by
    intro k z hz l
    by_cases hl : l = k
    · subst hl; simpa using Submodule.subset_span hz
    · simp [Pi.single_apply, hl]
  have h := hN v.embedding (Pi.single i x + Pi.single j y) fun l =>
    Submodule.add_mem _ (hmem i x hx l) (hmem j y hy l)
  have hsum : ∑ l, (Pi.single i x + Pi.single j y : ι → V) l = x + y := by
    simp [Finset.sum_add_distrib]
  have hpt : ∀ l, N v.embedding ((Pi.single i x + Pi.single j y : ι → V) l) ^ 2 =
      (Pi.single i (N v.embedding x ^ 2) : ι → ℝ) l + (Pi.single j (N v.embedding y ^ 2) : ι → ℝ) l := by
    intro l
    by_cases hli : l = i
    · subst hli; simp [Pi.single_apply, hij]
    · by_cases hlj : l = j
      · subst hlj; simp [Pi.single_apply, hli]
      · simp [Pi.single_apply, hli, hlj, gram_zero hG v]
  rw [hsum, Finset.sum_congr rfl fun l _ => hpt l, Finset.sum_add_distrib] at h
  simpa using h

theorem deg_eq [IsTotallyComplex K] [StarRing K] {n : ℕ} {b : Module.Basis (Fin n) K V}
    {X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ} {N : (K →+* ℂ) → V → ℝ}
    (hG : GlobalTheory.AllWt.IsGram b X N) (L : Submodule (𝓞 K) V) (hL : L.FG) :
    GlobalTheory.AllWt.deg N L = 1 / (Module.finrank ℚ K : ℝ) * Formalism.HN.deg (Formalism.HermitianLatticesTheory.realize b X) L +
      (Formalism.HN.rkK L : ℝ) * ((-Real.log 2 + Formalism.HN.logDisc K / (Module.finrank ℚ K : ℝ)) / 2) := by
  have hX : ∀ v, IsUnit (X v).det := fun v => (hG v).1
  rw [GlobalTheory.AllWt.deg, GlobalTheory.AllWt.slope, GlobalTheory.AllWt.slope_sq_eq hG hL]
  by_cases h0 : L = ⊥
  · subst h0
    simp [Formalism.BranchingDeterminantCap.OrthogonalSumAlt.rkK_bot, Formalism.BranchingDeterminantCap.OrthogonalSumAlt.deg_bot b X hX]
  · have hr : Formalism.HN.rkK L ≠ 0 := fun h => h0 (Formalism.BranchingDeterminantCap.OrthogonalSumAlt.eq_bot_of_rkK b h)
    have hrk := (Formalism.HN.plLat K V (Fin n) b X hX L hL).2.1
    have hs : Formalism.HN.slope (Formalism.HermitianLatticesTheory.realize b X) L =
        Formalism.HN.deg (Formalism.HermitianLatticesTheory.realize b X) L / (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) L : ℝ) := rfl
    have hn : (Module.finrank ℚ K : ℝ) ≠ 0 := by
      exact_mod_cast (Formalism.BranchingDeterminantCap.OrthogonalSumAlt.finrank_pos' (K := K)).ne'
    have hr' : (Formalism.HN.rkK L : ℝ) ≠ 0 := by exact_mod_cast hr
    rw [Formalism.HN.muDef, hs, hrk]
    push_cast
    field_simp
    ring

end GlobalTheory.OrthRankDeg

namespace GlobalTheory.OrthRankDeg

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem sum_finset [IsTotallyComplex K] [StarRing K] {n : ℕ} {b : Module.Basis (Fin n) K V}
    {X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ} {N : (K →+* ℂ) → V → ℝ}
    (hG : GlobalTheory.AllWt.IsGram b X N) {ι : Type} [Fintype ι] [DecidableEq ι] (M : ι → Submodule (𝓞 K) V)
    (hM : ∀ i, (M i).FG)
    (hN : ∀ σ, ∀ f : ι → V, (∀ i, f i ∈ Submodule.span K (M i : Set V)) →
      N σ (∑ i, f i) ^ 2 = ∑ i, N σ (f i) ^ 2) (s : Finset ι) :
    (⨆ i ∈ s, M i).FG ∧ Formalism.HN.rkK (⨆ i ∈ s, M i) = ∑ i ∈ s, Formalism.HN.rkK (M i) ∧
      Formalism.HN.deg (Formalism.HermitianLatticesTheory.realize b X) (⨆ i ∈ s, M i) =
        ∑ i ∈ s, Formalism.HN.deg (Formalism.HermitianLatticesTheory.realize b X) (M i) := by
  have hX : ∀ v, IsUnit (X v).det := fun v => (hG v).1
  induction s using Finset.induction_on with
  | empty =>
    simp [Formalism.BranchingDeterminantCap.OrthogonalSumAlt.rkK_bot, Formalism.BranchingDeterminantCap.OrthogonalSumAlt.deg_bot b X hX, Submodule.fg_bot]
  | insert a s ha ih =>
    obtain ⟨ihfg, ihrk, ihdeg⟩ := ih
    rw [Finset.iSup_insert]
    set B := ⨆ i ∈ s, M i with hB
    have ho : ∀ x ∈ M a, ∀ y ∈ B,
        inner ℝ (Formalism.HermitianLatticesTheory.realize b X x) (Formalism.HermitianLatticesTheory.realize b X y) = 0 := by
      intro x hx y hy
      obtain ⟨μ, hμ⟩ := (Submodule.mem_iSup_finset_iff_exists_sum M y).1 hy
      rw [← hμ, map_sum, inner_sum]
      refine Finset.sum_eq_zero fun i hi => ?_
      exact inner_pair hG M hN (by rintro rfl; exact ha hi) hx (μ i).2
    have hlA := (Formalism.HN.plLat K V (Fin n) b X hX (M a) (hM a)).1
    have hlB := (Formalism.HN.plLat K V (Fin n) b X hX B ihfg).1
    obtain ⟨hl, hdeg, -⟩ :=
      (Formalism.HN.hnSum.{0, 0, 0, 0} (𝓞 K) V _ (Formalism.HermitianLatticesTheory.realize b X)).2 (M a) B hlA hlB ho
    have hfg : (M a ⊔ B).FG := (hM a).sup ihfg
    have hinf : M a ⊓ B = ⊥ := by
      refine (Submodule.eq_bot_iff _).2 fun x hx => ?_
      have h1 := ho x hx.1 x hx.2
      rw [inner_self_eq_zero] at h1
      exact Formalism.HN.HeightGram.realize_injective b X hX (by rw [h1, map_zero])
    have hrk := (Formalism.HN.degSupermod (𝓞 K) V _ (Formalism.HermitianLatticesTheory.realize b X) (M a ⊔ B) (M a) B hl
      le_sup_left le_sup_right).1
    rw [hinf, (Formalism.HN.plLat K V (Fin n) b X hX _ hfg).2.1, (Formalism.HN.plLat K V (Fin n) b X hX _ (hM a)).2.1,
      (Formalism.HN.plLat K V (Fin n) b X hX _ ihfg).2.1,
      (Formalism.HN.plLat K V (Fin n) b X hX _ Submodule.fg_bot).2.1, Formalism.BranchingDeterminantCap.OrthogonalSumAlt.rkK_bot, mul_zero, add_zero,
      ← mul_add] at hrk
    have hrk' := Nat.eq_of_mul_eq_mul_left (Formalism.BranchingDeterminantCap.OrthogonalSumAlt.finrank_pos' (K := K)) hrk
    refine ⟨hfg, ?_, ?_⟩
    · rw [hrk', Finset.sum_insert ha, ihrk]
    · rw [hdeg, Finset.sum_insert ha, ihdeg]

theorem rkK_deg_iSup : ∀ (K V : Type) [Field K] [NumberField K] [IsTotallyComplex K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (ι : Type) [Fintype ι] (N : (K →+* ℂ) → V → ℝ)
    (M : ι → Submodule (𝓞 K) V), HasGram N → (∀ i, (M i).FG) →
    (∀ σ, ∀ f : ι → V, (∀ i, f i ∈ Submodule.span K (M i : Set V)) → N σ (∑ i, f i) ^ 2 = ∑ i, N σ (f i) ^ 2) →
    Formalism.HN.rkK (⨆ i, M i) = ∑ i, Formalism.HN.rkK (M i) ∧ deg N (⨆ i, M i) = ∑ i, deg N (M i) := by
  intro K V _ _ _ _ _ _ _ ι _ N M hG hM hN
  classical
  letI : StarRing K := starRingOfComm
  obtain ⟨⟨n, ⟨⟨b, X⟩, hbX⟩⟩⟩ := hG
  obtain ⟨hfg, hrk, hdeg⟩ := sum_finset hbX M hM hN Finset.univ
  have hu : (⨆ i ∈ (Finset.univ : Finset ι), M i) = ⨆ i, M i := by simp
  rw [hu] at hfg hrk hdeg
  refine ⟨hrk, ?_⟩
  rw [deg_eq hbX _ hfg, hdeg, hrk, Finset.mul_sum]
  push_cast
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => (deg_eq hbX _ (hM i)).symm

end GlobalTheory.OrthRankDeg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTanScalIffOfLeftEq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.HTPullTan

open GlobalTheory.UPel.HT

theorem isTanScal_iff_of_left_eq : ∀ {O : Type} [Ring O] {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] (f : S' ⟶ S) (φ : A'.left ⟶ A.left) (act : GlobalTheory.UPel.HT.OActN O A) (act' : GlobalTheory.UPel.HT.OActN O A'), IsGrpPullback A' A f φ → (∀ c, (act'.act c).left ≫ φ = φ ≫ (act.act c).left) → ∀ {R' : Type} [CommRing R'] (x : Sp R' ⟶ S') (b : O) (c : R') (v : GlobalTheory.UPel.HT.epsPtR x ⟶ A') (v₀ : GlobalTheory.UPel.HT.epsPtR (x ≫ f) ⟶ A), v₀.left = v.left ≫ φ → (GlobalTheory.UPel.HT.IsTanScal act' x b c v ↔ GlobalTheory.UPel.HT.IsTanScal act (x ≫ f) b c v₀) := by
  intro O _ S S' A A' _ _ f φ a a' h hact R' _ x b c v v₀ hv₀
  obtain ⟨e₀, he₀⟩ := GlobalTheory.LiePull.exists_pushEquiv h (Over.mk x) (x ≫ f) rfl
  have one : (1 : Over.mk (x ≫ f) ⟶ A).left = (1 : Over.mk x ⟶ A').left ≫ φ := by
    rw [← he₀, map_one]
  have sc : spMap (epsScaleR c) ≫ spMap (algebraMap R' (DualNumber R')) = spMap (algebraMap R' (DualNumber R')) := by
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  have fs : spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ spMap (algebraMap R' (DualNumber R')) = 𝟙 _ := by
    refine (Spec.map_comp _ _).symm.trans ((congrArg Spec.map ?_).trans (Spec.map_id _))
    ext a
    simp [TrivSqZeroExt.algebraMap_eq_inl]
  have hR : ∀ (u w : epsPtR x ⟶ A') (u₀ w₀ : epsPtR (x ≫ f) ⟶ A), u₀.left = u.left ≫ φ → w₀.left = w.left ≫ φ →
      (u.left = spMap (epsScaleR c) ≫ w.left ↔
      u₀.left = spMap (epsScaleR c) ≫ w₀.left) := fun u w u₀ w₀ hu hw => by
    rw [hu, hw]
    refine ⟨fun E => by rw [E]; exact Category.assoc _ _ _, fun E => h.1.hom_ext (E.trans (Category.assoc _ _ _).symm) ?_⟩
    refine (Over.w u).trans (Eq.symm ((Category.assoc _ _ _).trans ?_))
    refine (congrArg (spMap (epsScaleR c) ≫ ·) (Over.w w)).trans ?_
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ x) sc)
  refine and_congr ?_ ?_
  · rw [one, hv₀]
    refine ⟨fun E => by rw [← E]; exact (Category.assoc _ _ _).symm,
      fun E => h.1.hom_ext ((Category.assoc _ _ _).trans E) ?_⟩
    refine ((Category.assoc _ _ _).trans ?_).trans (Over.w (1 : Over.mk x ⟶ A')).symm
    refine (congrArg (spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ ·) (Over.w v)).trans ?_
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ x) fs).trans (Category.id_comp _))
  · refine hR _ _ _ _ ?_ hv₀
    rw [Over.comp_left, Over.comp_left, hv₀, Category.assoc, Category.assoc, hact]

end GlobalTheory.HTPullTan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTestHomMatrixOfProportionalGeneratingCombinati
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.HomFixCond

theorem unit_of_proportional {X : Scheme.{0}} {V : X.Opens} {m : ℕ} (B C : Fin m → Γ(X, V))
    (hC : ∀ x ∈ V, ∃ j, IsUnit (gs (𝟙 X) x V (C j)))
    (hB : ∀ x ∈ V, ∃ j, IsUnit (gs (𝟙 X) x V (B j)))
    (hP : ∀ x ∈ V, ∀ j j', gs (𝟙 X) x V (B j) * gs (𝟙 X) x V (C j') =
      gs (𝟙 X) x V (B j') * gs (𝟙 X) x V (C j)) :
    ∃ u : Γ(X, V)ˣ, ∀ j, B j = u.val * C j := by
  let W : Fin m → X.Opens := fun j => X.basicOpen (C j)
  have lW : ∀ j, W j ≤ V := fun j => X.basicOpen_le _
  have uC : ∀ j, ∀ y ∈ W j, IsUnit (gs (𝟙 X) y V (C j)) := fun j y hy =>
    (GlobalTheory.LBGerm.isUnit_gs_iff (𝟙 X) y V (lW j hy) (C j)).2 hy
  have uB : ∀ j, ∀ y ∈ W j, IsUnit (gs (𝟙 X) y V (B j)) := fun j y hy => by
    obtain ⟨j', hj'⟩ := hB y (lW j hy)
    have e := hP y (lW j hy) j' j
    have h2 := hj'.mul (uC j y hy)
    rw [e] at h2
    exact isUnit_of_mul_isUnit_left h2
  have hu : ∀ j, IsUnit (resG X (lW j) (C j)) := fun j =>
    X.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
      have := uC j y hy
      rw [← gs_res (𝟙 X) y (lW j) hy, gs_eq _ y _ hy] at this
      exact this
  let w : ∀ j, Γ(X, W j) := fun j => resG X (lW j) (B j) * ((hu j).unit⁻¹).val
  have hw : ∀ j, ∀ y ∈ W j, gs (𝟙 X) y (W j) (w j) * gs (𝟙 X) y V (C j) = gs (𝟙 X) y V (B j) := fun j y hy => by
    rw [← gs_res (𝟙 X) y (lW j) hy (C j), ← gs_mul _ y _ hy, _root_.mul_assoc]
    show gs (𝟙 X) y (W j) (resG X (lW j) (B j) * (((hu j).unit⁻¹).val * (hu j).unit.val)) = _
    rw [Units.inv_mul, _root_.mul_one, gs_res _ y _ hy]
  have wu : ∀ j, IsUnit (w j) := fun j => X.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
    have e := hw j y hy
    have h1 : IsUnit (gs (𝟙 X) y (W j) (w j)) := by
      have := uB j y hy
      rw [← e] at this
      exact isUnit_of_mul_isUnit_left this
    rw [gs_eq _ y _ hy] at h1
    exact h1
  obtain ⟨s, hs⟩ := glue_unit V W lW (fun y hy => by
      obtain ⟨j, hj⟩ := hC y hy
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, (GlobalTheory.LBGerm.isUnit_gs_iff (𝟙 X) y V hy (C j)).1 hj⟩)
    (fun j => (wu j).unit) (fun i j y hy => by
      apply Units.ext
      rw [← gs_unit _ y _ hy.1, ← gs_unit _ y _ hy.2]
      refine (uC i y hy.1).mul_right_cancel ?_
      refine (uC j y hy.2).mul_right_cancel ?_
      show gs (𝟙 X) y (W i) (w i) * gs (𝟙 X) y V (C i) * gs (𝟙 X) y V (C j) =
        gs (𝟙 X) y (W j) (w j) * gs (𝟙 X) y V (C i) * gs (𝟙 X) y V (C j)
      rw [hw i y hy.1, mul_right_comm, hw j y hy.2, hP y (lW i hy.1) i j])
  refine ⟨s, fun j => fn_ext fun y hy => ?_⟩
  obtain ⟨i, hi⟩ := hC y hy
  have yi : y ∈ W i := (GlobalTheory.LBGerm.isUnit_gs_iff (𝟙 X) y V hy (C i)).1 hi
  have es : gs (𝟙 X) y V s.val = gs (𝟙 X) y (W i) (w i) := by
    rw [← gs_res (𝟙 X) y (lW i) yi]
    exact congrArg (fun q : Γ(X, W i)ˣ => gs (𝟙 X) y (W i) q.val) (hs i)
  rw [gs_mul _ y _ hy, es]
  refine hi.mul_right_cancel ?_
  rw [mul_right_comm, hw i y yi, hP y hy i j]

theorem gs_finsum {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) {n : ℕ} (a : Fin n → Γ(X, U)) :
    gs f y U (∑ i, a i) = ∑ i, gs f y U (a i) := by
  simp only [gs_eq f y U h, map_sum]

theorem isMat_of_conditions : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (k mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))) (αA : Fin mA → Γ(Sp Rg, ⊤)) (βB : Fin mB → Γ(Sp Rg, ⊤)) (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B') (c : Fin mA → Fin mB → Γ(Sp R, ⊤)), L.IsLB → M.IsLB → eA.IsGen → eB.IsGen → (⨆ j, nonzeroLocus (bB j)) = ⊤ → (∀ i, GlobalTheory.HomFixUniv.IsVal (eSec A ≫ GlobalTheory.HomFixUniv.θ A) (GlobalTheory.HomFixUniv.uFr A L k eA) (bA i) (αA i)) → (∀ j, GlobalTheory.HomFixUniv.IsVal (eSec B ≫ GlobalTheory.HomFixUniv.θ B) (GlobalTheory.HomFixUniv.uFr B M k eB) (bB j) (βB j)) → IsTest A B L M t A' B' φA' φB' Φ' → GlobalTheory.HomFixUniv.Generates bA (φA' ≫ GlobalTheory.HomFixUniv.θ A) A'.hom c → GlobalTheory.HomFixUniv.Proport bA bB (φA' ≫ GlobalTheory.HomFixUniv.θ A) A'.hom (Φ'.left ≫ φB' ≫ GlobalTheory.HomFixUniv.θ B) c → GlobalTheory.HomFixUniv.Normal t c αA βB → IsMat L M k bA bB eA eB t A' B' φA' φB' Φ' c := by
  intro Rg _ A B _ _ L M k mA mB bA bB eA eB αA βB R _ t A' B' _ _ φA' φB' Φ' c hL hM heA heB hcov hvA hvB hT hgen
    hprop hnorm
  have key : ∀ p : (Fin 1 → M.ι) × (Fin 1 → L.ι),
      ∃ u : Γ(A'.left, (isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p)ˣ, ∀ j : Fin mB,
        ((Φ'.left ≫ φB' ≫ θ B).appLE (LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1)
          ((isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p)
          (inf_le_left.trans (GlobalTheory.HomFixMat.wchart_comp_le M _ _ p.1))).hom ((bB j).f p.1) =
        u.val * ∑ i, (A'.hom.appLE ⊤ ((isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p) (by simp)).hom
          (c i j) *
          ((φA' ≫ θ A).appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p.2)
            ((isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p)
            (inf_le_right.trans (GlobalTheory.HomFixMat.wchart_comp_le L _ _ p.2))).hom ((bA i).f p.2) := by
    intro p
    set V := (isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p with hV
    have mB' : ∀ z ∈ V, (Φ'.left ≫ φB' ≫ θ B) z ∈ LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1 :=
      fun z hz => GlobalTheory.HomFixMat.wchart_comp_le M _ _ p.1 hz.1
    have mA' : ∀ z ∈ V, (φA' ≫ θ A) z ∈ LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p.2 :=
      fun z hz => GlobalTheory.HomFixMat.wchart_comp_le L _ _ p.2 hz.2
    have gB : ∀ z ∈ V, ∀ j : Fin mB, gs (𝟙 A'.left) z V
        (((Φ'.left ≫ φB' ≫ θ B).appLE (LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1) V
          (inf_le_left.trans (GlobalTheory.HomFixMat.wchart_comp_le M _ _ p.1))).hom ((bB j).f p.1)) =
        gs (Φ'.left ≫ φB' ≫ θ B) z (LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1) ((bB j).f p.1) :=
      fun z hz j => (gs_appLE _ _ _ _ (𝟙 A'.left) z hz _).trans (by rw [Category.id_comp])
    have gC : ∀ z ∈ V, ∀ j : Fin mB, gs (𝟙 A'.left) z V (∑ i, (A'.hom.appLE ⊤ V (by simp)).hom (c i j) *
          ((φA' ≫ θ A).appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p.2) V
            (inf_le_right.trans (GlobalTheory.HomFixMat.wchart_comp_le L _ _ p.2))).hom ((bA i).f p.2)) =
        comb bA (φA' ≫ θ A) A'.hom c z p.2 j := fun z hz j => by
      rw [gs_finsum _ z _ hz]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [gs_mul _ z _ hz]
      refine congrArg₂ (· * ·) ((gs_appLE _ _ _ _ (𝟙 A'.left) z hz _).trans (by rw [Category.id_comp]))
        ((gs_appLE _ _ _ _ (𝟙 A'.left) z hz _).trans (by rw [Category.id_comp]; rfl))
    obtain ⟨u, hu⟩ := unit_of_proportional (V := V)
      (fun j => ((Φ'.left ≫ φB' ≫ θ B).appLE (LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1) V
          (inf_le_left.trans (GlobalTheory.HomFixMat.wchart_comp_le M _ _ p.1))).hom ((bB j).f p.1))
      (fun j => ∑ i, (A'.hom.appLE ⊤ V (by simp)).hom (c i j) *
          ((φA' ≫ θ A).appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p.2) V
            (inf_le_right.trans (GlobalTheory.HomFixMat.wchart_comp_le L _ _ p.2))).hom ((bA i).f p.2))
      (fun z hz => by
        obtain ⟨j, hj⟩ := hgen z p.2 (mA' z hz)
        exact ⟨j, by rw [gC z hz j]; exact hj⟩)
      (fun z hz => by
        obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 (hcov.ge (Set.mem_univ ((Φ'.left ≫ φB' ≫ θ B) z)))
        exact ⟨j, by rw [gB z hz j]; exact (GlobalTheory.mem_nonzeroLocus_iff_pull (bB j) _ z (mB' z hz)).1 hj⟩)
      (fun z hz j j' => by
        rw [gB z hz j, gB z hz j', gC z hz j, gC z hz j']
        exact hprop z p.2 p.1 (mA' z hz) (mB' z hz) j j')
    exact ⟨u, hu⟩
  choose u hu using key
  refine ⟨φA' ≫ θ A, φB' ≫ θ B, ⟨u⟩, by rw [Category.assoc, θ_snd, Category.comp_id],
    by rw [Category.assoc, θ_snd, Category.comp_id], ?_, ?_, fun j p => hu p j⟩
  · exact GlobalTheory.T.isGenerator_isoBundle_of_matrix_relation Rg A B L M k mA mB bA bB R A' B' Φ' (φA' ≫ θ A) (φB' ≫ θ B) c u hgen (fun j p => hu p j)
  · exact GlobalTheory.T.isoNormalisation_at_zeroSection Rg A B L M k mA mB bA bB eA eB αA βB R t A' B' φA' φB' Φ' c u hcov hvA hvB hT hnorm
      (fun j p => hu p j)

end GlobalTheory.HomFixCond
end
end

