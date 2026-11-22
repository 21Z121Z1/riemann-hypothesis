import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0009
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0010
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeSumProdNormLeOfProdNormLowerBound
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0013
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0012
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0011

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralHaarEqZeroOfFibreIntegralsEqZeroStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_haar_eq_zero_of_fibre_integrals_eq_zero_alt : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H), μ.IsHaarMeasure → ∀ (P Q : Subgroup H), IsClosed (P : Set H) → IsClosed (Q : Set H) → (∀ p ∈ P, ∀ q ∈ Q, p * q = q * p) → (∀ h, ∃ p ∈ P, ∃ q ∈ Q, h = p * q) → (∀ h, h ∈ P → h ∈ Q → h = 1) → ∀ F : H → ℂ, (∀ ν : Measure P, ν.IsHaarMeasure → ∀ q ∈ Q, ∫ p, F ((p : H) * q) ∂ν = 0) → ∫ h, F h ∂μ = 0 := by
  first | exact @GlobalTheory.integral_haar_eq_zero_of_fibre_integrals_eq_zero | exact GlobalTheory.integral_haar_eq_zero_of_fibre_integrals_eq_zero | (intros; apply GlobalTheory.integral_haar_eq_zero_of_fibre_integrals_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntertwinerMemISupRangeEqSumSmulStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eq_sum_smul_of_range_le_iSup_range : ∀ (G : Type) [Group G] (N X : Type) [AddCommGroup N] [Module ℂ N]
    [AddCommGroup X] [Module ℂ X] (π : Representation ℂ G N) (ρ : Representation ℂ G X),
    (∀ φ : π.IntertwiningMap π, ∃ c : ℂ, φ.toLinearMap = c • LinearMap.id) →
    ∀ (m : ℕ) (φ : Fin m → π.IntertwiningMap ρ), Function.Injective (fun w : Fin m → N => ∑ j, φ j (w j)) →
    ∀ ψ : π.IntertwiningMap ρ, LinearMap.range ψ.toLinearMap ≤ ⨆ j, LinearMap.range (φ j).toLinearMap →
    ∃ c : Fin m → ℂ, ∀ n, ψ n = ∑ j, c j • φ j n := by
  first | exact @GlobalTheory.intertwiner_mem_iSup_range_eq_sum_smul | exact GlobalTheory.intertwiner_mem_iSup_range_eq_sum_smul | (intros; apply GlobalTheory.intertwiner_mem_iSup_range_eq_sum_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IrreducibleUnitaryVectorDensityStatement
section
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducibleUnitary_vector_density : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (G : Type) [Group G] (π : G →* (H →L[ℂ] H)), (∀ g x, ‖π g x‖ = ‖x‖) → (∀ B : H →L[ℂ] H, (∀ g, B.comp (π g) = (π g).comp B) → ∃ c : ℂ, B = c • ContinuousLinearMap.id ℂ H) → ∀ (n : ℕ) (a : Fin n → H) (Λ : Fin n → (H →L[ℂ] ℂ)), (∀ g, ∑ j, Λ j (π g (a j)) = 0) → ∀ φ u : H, ∑ j, ⟪φ, a j⟫_ℂ * Λ j u = 0 := by
  first | exact @GlobalTheory.irreducibleUnitary_density | exact GlobalTheory.irreducibleUnitary_density | (intros; apply GlobalTheory.irreducibleUnitary_density <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAlgebraicIntegral
section
open MeasureTheory

namespace GlobalTheory.HaarAlg

variable {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (κ : Measure K) [IsProbabilityMeasure κ] {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Group K] [IsTopologicalGroup K] in
theorem integrable_of_continuous {f : K → ℂ} (hf : Continuous f) : Integrable f κ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

noncomputable def avg (F : K → Matrix ι ι ℂ) : Matrix ι ι ℂ := Matrix.of fun a b => ∫ g, F g a b ∂κ

omit [Group K] [IsTopologicalGroup K] [DecidableEq ι] in
theorem mul_avg {F : K → Matrix ι ι ℂ} (hF : Continuous F) (M : Matrix ι ι ℂ) :
    M * avg κ F = avg κ fun g => M * F g := by
  ext a b
  simp only [avg, Matrix.mul_apply, Matrix.of_apply]
  rw [integral_finset_sum]
  · exact Finset.sum_congr rfl fun c _ => (integral_const_mul _ _).symm
  · exact fun c _ => integrable_of_continuous κ (by fun_prop)

omit [Group K] [IsTopologicalGroup K] [DecidableEq ι] in
theorem avg_mul {F : K → Matrix ι ι ℂ} (hF : Continuous F) (M : Matrix ι ι ℂ) :
    avg κ F * M = avg κ fun g => F g * M := by
  ext a b
  simp only [avg, Matrix.mul_apply, Matrix.of_apply]
  rw [integral_finset_sum]
  · exact Finset.sum_congr rfl fun c _ => (integral_mul_const _ _).symm
  · exact fun c _ => integrable_of_continuous κ (by fun_prop)

omit [Group K] [IsTopologicalGroup K] [TopologicalSpace K] [CompactSpace K] [BorelSpace K] [Fintype ι] [DecidableEq ι] in
theorem avg_const (M : Matrix ι ι ℂ) : avg κ (fun _ => M) = M := by
  ext a b
  simp [avg]

variable [κ.IsMulLeftInvariant]

omit [CompactSpace K] [IsProbabilityMeasure κ] [Fintype ι] [DecidableEq ι] in
theorem avg_left (F : K → Matrix ι ι ℂ) (h : K) : (avg κ fun g => F (h * g)) = avg κ F := by
  ext a b
  exact integral_mul_left_eq_self (fun g => F g a b) h

theorem rho_mul_avg (ρ : K →* Matrix ι ι ℂ) (hρ : Continuous ρ) (h : K) : ρ h * avg κ ρ = avg κ ρ := by
  rw [mul_avg κ hρ, ← avg_left κ ρ h]
  simp only [map_mul]

theorem avg_mul_rho (ρ : K →* Matrix ι ι ℂ) (hρ : Continuous ρ) (h : K) : avg κ ρ * ρ h = avg κ ρ := by
  have hc : Continuous fun g : K => ρ g⁻¹ := hρ.comp continuous_inv
  have h1 : ∀ h, avg κ (fun g => ρ g⁻¹) * ρ h = avg κ fun g => ρ g⁻¹ := fun h => by
    rw [avg_mul κ hc, ← avg_left κ (fun g => ρ g⁻¹) h⁻¹]
    simp only [mul_inv_rev, inv_inv, map_mul]
  have h2 : avg κ (fun g => ρ g⁻¹) * avg κ ρ = avg κ ρ := by
    rw [avg_mul κ hc]
    simp only [rho_mul_avg κ ρ hρ, avg_const]
  have h3 : avg κ (fun g => ρ g⁻¹) * avg κ ρ = avg κ fun g => ρ g⁻¹ := by
    rw [mul_avg κ hρ]
    simp only [h1, avg_const]
  rw [h2.symm.trans h3, h1]

theorem isAlgebraic_integral (ρ : K →* Matrix ι ι ℂ) (hρ : Continuous ρ) (Γ : Set K) (hΓ : Dense Γ)
    (halg : ∀ γ ∈ Γ, ∀ a b, IsAlgebraic ℚ (ρ γ a b)) (a b : ι) : IsAlgebraic ℚ (∫ g, ρ g a b ∂κ) := by
  set P := avg κ ρ with hP
  let Q := algebraicClosure ℚ ℂ
  have key : ∀ s : ℂ ≃ₐ[Q] ℂ, P * P.map s = P.map s ∧ P.map s * P = P.map s := fun s => by
    have hfix : ∀ γ ∈ Γ, (ρ γ).map s = ρ γ := fun γ hγ => by
      ext a b
      exact s.commutes (⟨ρ γ a b, mem_algebraicClosure_iff.2 (halg γ hγ a b)⟩ : Q)
    have hm : ∀ M N : Matrix ι ι ℂ, (M * N).map s = M.map s * N.map s := fun M N => Matrix.map_mul
    have l : ∀ g, ρ g * P.map s = P.map s := fun g =>
      congrFun (Continuous.ext_on hΓ (f := fun g => ρ g * P.map s) (g := fun _ => P.map s) (by fun_prop) continuous_const
        fun γ hγ => by
          show ρ γ * P.map s = P.map s
          rw [← hfix γ hγ, ← hm, hP, rho_mul_avg κ ρ hρ]) g
    have r : ∀ g, P.map s * ρ g = P.map s := fun g =>
      congrFun (Continuous.ext_on hΓ (f := fun g => P.map s * ρ g) (g := fun _ => P.map s) (by fun_prop) continuous_const
        fun γ hγ => by
          show P.map s * ρ γ = P.map s
          rw [← hfix γ hγ, ← hm, hP, avg_mul_rho κ ρ hρ]) g
    constructor
    · conv_lhs => rw [hP]
      rw [avg_mul κ hρ]
      simp only [← hP, l, avg_const]
    · conv_lhs => rw [hP]
      rw [mul_avg κ hρ]
      simp only [← hP, r, avg_const]
  have fix : ∀ s : ℂ ≃ₐ[Q] ℂ, P.map s = P := fun s => by
    have h1 := congrArg (fun M : Matrix ι ι ℂ => M.map s) (key s.symm).1
    have e : (P.map s.symm).map s = P := by ext a b; simp
    have hm : ∀ M N : Matrix ι ι ℂ, (M * N).map s = M.map s * N.map s := fun M N => Matrix.map_mul
    simp only [hm, e] at h1
    rw [← (key s).2, h1]
  obtain ⟨q, hq⟩ := GlobalTheory.GaloisDescent.mem_range_algebraMap_of_forall_algEquiv (K := Q) (P a b)
    fun s => congrFun (congrFun (fix s) a) b
  have : P a b ∈ Q := hq ▸ q.2
  exact mem_algebraicClosure_iff.1 this

end GlobalTheory.HaarAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotypicFactorOfIsIrreduciblePiFiniteGroupsStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotypic_factor_of_isIrreducible_pi_finite_groups : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G : ι → Type) [∀ i, Group (G i)] [∀ i, Finite (G i)] (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (∀ i, G i) W), ρ.IsIrreducible → ∀ i, ∃ (n : ℕ) (τ : Representation ℂ (G i) (Fin n → ℂ)), τ.IsIrreducible ∧ (∃ φ : (Fin n → ℂ) →ₗ[ℂ] W, Function.Injective φ ∧ ∀ g z, φ (τ g z) = ρ (Pi.mulSingle i g) (φ z)) ∧ Submodule.span ℂ {y | ∃ φ : (Fin n → ℂ) →ₗ[ℂ] W, (∀ g z, φ (τ g z) = ρ (Pi.mulSingle i g) (φ z)) ∧ y ∈ LinearMap.range φ} = ⊤ := by
  first | exact @GlobalTheory.PiIsotypic.isotypic_factor_of_isIrreducible_pi | exact GlobalTheory.PiIsotypic.isotypic_factor_of_isIrreducible_pi | (intros; apply GlobalTheory.PiIsotypic.isotypic_factor_of_isIrreducible_pi <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeSumProdNormLeOfProdNormLowerBoundStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_sum_prod_norm_le_of_prod_norm_lower_bound : ∀ (ι : Type) [Fintype ι] [Nonempty ι] (n : ℕ) (Λ : AddSubgroup (ι → EuclideanSpace ℂ (Fin n))) (R : ℝ), 1 ≤ n → 1 < R → (∀ w ∈ Λ, w ≠ 0 → R ≤ ∏ τ, ‖w τ‖) → ∀ s : Finset (ι → EuclideanSpace ℂ (Fin n)), (∀ w ∈ s, w ∈ Λ ∧ w ≠ 0) → ∑ w ∈ s, ∏ τ, (((1 + ‖w τ‖) / 3) ^ (2 * n + 5))⁻¹ ≤ Real.exp ((6 * n + 9) * Fintype.card ι) / R := by
  first | exact @GlobalTheory.ProdNormSum.lattice_sum_le | exact GlobalTheory.ProdNormSum.lattice_sum_le | (intros; apply GlobalTheory.ProdNormSum.lattice_sum_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeKerOfLocalFiniteLengthToSimple
section
open scoped TensorProduct

namespace GlobalTheory.TensHead

section HeadKill

variable {W : Type} [AddCommGroup W] [Module ℂ W]

def MinStab (A : Set (Module.End ℂ W)) (T : Submodule ℂ W) : Prop :=
  Stab A T ∧ ∀ U : Submodule ℂ W, Stab A U → U ≤ T → U = ⊥ ∨ U = T

theorem MinStab.map {A : Set (Module.End ℂ W)} {T : Submodule ℂ W} (hT : MinStab A T)
    (b : Module.End ℂ W) (hb : ∀ a ∈ A, a * b = b * a) : MinStab A (T.map b) := by
  obtain ⟨hTs, hTmin⟩ := hT
  have hcomm' : ∀ a ∈ A, ∀ x, a (b x) = b (a x) := fun a ha x =>
    LinearMap.congr_fun (hb a ha) x
  refine ⟨?_, ?_⟩
  · intro a ha y hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
    rw [hcomm' a ha x]
    exact Submodule.mem_map_of_mem (hTs a ha x hx)
  · intro U hU hUle
    have hU' : Stab A (T ⊓ U.comap b) := by
      intro a ha x hx
      refine ⟨hTs a ha x hx.1, ?_⟩
      show b (a x) ∈ U
      rw [← hcomm' a ha x]
      exact hU a ha (b x) hx.2
    rcases hTmin _ hU' inf_le_left with h | h
    · left
      rw [eq_bot_iff]
      intro u hu
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp (hUle hu)
      have hx' : x ∈ T ⊓ U.comap b := ⟨hx, hu⟩
      rw [h] at hx'
      rw [(Submodule.mem_bot ℂ).mp hx', map_zero]
      exact Submodule.zero_mem _
    · right
      refine le_antisymm hUle ?_
      rw [Submodule.map_le_iff_le_comap]
      intro x hx
      have hx' : x ∈ T ⊓ U.comap b := by rw [h]; exact hx
      exact hx'.2

theorem exists_stab_compl {A : Set (Module.End ℂ W)}
    (htop : sSup {T | MinStab A T} = ⊤) (K : Submodule ℂ W) (hK : Stab A K) :
    ∃ C : Submodule ℂ W, Stab A C ∧ C ⊓ K = ⊥ ∧ C ⊔ K = ⊤ := by
  have hsup : ∀ N N' : Submodule ℂ W, Stab A N → Stab A N' → Stab A (N ⊔ N') := by
    intro N N' hN hN' a ha x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add]
    exact Submodule.add_mem_sup (hN a ha y hy) (hN' a ha z hz)
  let S : Set (Submodule ℂ W) := {C | Stab A C ∧ C ⊓ K = ⊥}
  obtain ⟨C, hCmax⟩ : ∃ C, Maximal (· ∈ S) C := by
    refine zorn_le₀ S ?_
    intro c hcS hc
    rcases c.eq_empty_or_nonempty with rfl | hne
    · refine ⟨⊥, ⟨?_, bot_inf_eq _⟩, by simp⟩
      intro a _ x hx
      rw [(Submodule.mem_bot ℂ).mp hx, map_zero]
      exact Submodule.zero_mem _
    · refine ⟨sSup c, ⟨?_, ?_⟩, fun z hz => le_sSup hz⟩
      · intro a ha x hx
        rw [Submodule.mem_sSup_of_directed hne hc.directedOn] at hx ⊢
        obtain ⟨y, hy, hxy⟩ := hx
        exact ⟨y, hy, (hcS hy).1 a ha x hxy⟩
      · rw [eq_bot_iff]
        intro x hx0
        obtain ⟨hx, hxK⟩ := Submodule.mem_inf.mp hx0
        rw [Submodule.mem_sSup_of_directed hne hc.directedOn] at hx
        obtain ⟨y, hy, hxy⟩ := hx
        have hx' : x ∈ y ⊓ K := ⟨hxy, hxK⟩
        rwa [(hcS hy).2] at hx'
  obtain ⟨⟨hCs, hCK⟩, hCm⟩ := hCmax
  refine ⟨C, hCs, hCK, ?_⟩
  by_contra hne
  have hex : ∃ T, MinStab A T ∧ ¬ T ≤ C ⊔ K := by
    by_contra h
    simp only [not_exists, not_and, not_not] at h
    exact hne (top_unique (by rw [← htop]; exact sSup_le fun T hT => h T hT))
  obtain ⟨T, ⟨hTs, hTmin⟩, hTn⟩ := hex
  have hI : Stab A (T ⊓ (C ⊔ K)) := fun a ha x hx =>
    ⟨hTs a ha x hx.1, hsup C K hCs hK a ha x hx.2⟩
  rcases hTmin _ hI inf_le_left with h | h
  · have hmem : C ⊔ T ∈ S := by
      refine ⟨hsup C T hCs hTs, ?_⟩
      rw [eq_bot_iff]
      intro x hx0
      obtain ⟨hx, hxK⟩ := Submodule.mem_inf.mp hx0
      obtain ⟨c, hc, t, ht, rfl⟩ := Submodule.mem_sup.mp hx
      have ht' : t ∈ T ⊓ (C ⊔ K) := by
        refine ⟨ht, ?_⟩
        simpa using Submodule.sub_mem _ (Submodule.mem_sup_right hxK : c + t ∈ C ⊔ K)
          (Submodule.mem_sup_left hc : c ∈ C ⊔ K)
      have ht0 : t = 0 := by
        rw [h] at ht'
        exact (Submodule.mem_bot ℂ).mp ht'
      subst ht0
      rw [add_zero] at hxK ⊢
      have hc' : c ∈ C ⊓ K := ⟨hc, hxK⟩
      rwa [hCK] at hc'
    have hle : C ⊔ T ≤ C := hCm hmem le_sup_left
    exact hTn ((le_sup_right.trans hle).trans le_sup_left)
  · exact hTn (inf_eq_left.mp h)

end HeadKill

theorem le_ker_of_simple_commuting {M W : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup W]
    [Module ℂ W]
    (Op : Set (Module.End ℂ M)) (Rel K : Submodule ℂ M) (φ : M →ₗ[ℂ] W)
    (act : Module.End ℂ M → Module.End ℂ W) (B : Set (Module.End ℂ W))
    (hL : ∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ M), StrictMono N →
        (∀ j, Rel ≤ N j ∧ ∀ g ∈ Op, ∀ x ∈ N j, g x ∈ N j) → m ≤ L)
    (hmax : ∀ N : Submodule ℂ M, Rel ≤ N → Stab Op N → N ≠ ⊤ → N ≤ K)
    (hKtop : K ≠ ⊤) (hK : Stab Op K) (hRel : Rel ≤ LinearMap.ker φ)
    (hφ : ∀ g ∈ Op, φ ∘ₗ g = act g ∘ₗ φ)
    (hcomm : ∀ g ∈ Op, ∀ b ∈ B, act g * b = b * act g)
    (hsimple : ∀ U : Submodule ℂ W, Stab (act '' Op ∪ B) U → U = ⊥ ∨ U = ⊤) :
    K ≤ LinearMap.ker φ := by
  classical
  have hint : ∀ g ∈ Op, ∀ x, φ (g x) = act g (φ x) := fun g hg x =>
    LinearMap.congr_fun (hφ g hg) x
  by_cases hφ0 : LinearMap.range φ = ⊥
  · intro x _
    have hx : φ x ∈ LinearMap.range φ := LinearMap.mem_range_self φ x
    rw [hφ0] at hx
    exact (Submodule.mem_bot ℂ).mp hx
  have hrange : Stab (act '' Op) (LinearMap.range φ) := by
    intro a ha y hy
    obtain ⟨g, hg, rfl⟩ := ha
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hy
    exact LinearMap.mem_range.mpr ⟨g x, hint g hg x⟩
  have hcomap : ∀ U : Submodule ℂ W, Stab (act '' Op) U → Stab Op (U.comap φ) := by
    intro U hU g hg x hx
    show φ (g x) ∈ U
    rw [hint g hg x]
    exact hU _ ⟨g, hg, rfl⟩ _ hx
  have hRelc : ∀ U : Submodule ℂ W, Rel ≤ U.comap φ := by
    intro U x hx
    show φ x ∈ U
    rw [LinearMap.mem_ker.mp (hRel hx)]
    exact U.zero_mem
  obtain ⟨L, hL⟩ := hL
  let P : Set (Submodule ℂ W) := {U | U ≤ LinearMap.range φ ∧ Stab (act '' Op) U ∧ U ≠ ⊥}
  have hwf : P.WellFoundedOn (· < ·) := by
    rw [Set.wellFoundedOn_iff_no_descending_seq]
    intro f hf
    have hlt : ∀ m n : ℕ, m < n → f n < f m := fun m n h => f.map_rel_iff.mpr h
    have hmono : StrictMono (fun i : Fin (L + 1) => (f (L - i.val)).comap φ) := by
      intro i j hij
      have hij' : (i : ℕ) < j := hij
      have hj := j.isLt
      have hlt' : f (L - i.val) < f (L - j.val) := hlt _ _ (by omega)
      show (f (L - i.val)).comap φ < (f (L - j.val)).comap φ
      refine lt_of_le_of_ne (Submodule.comap_mono hlt'.le) ?_
      intro heq
      have hmap := congrArg (Submodule.map φ) heq
      rw [Submodule.map_comap_eq_self (hf _).1, Submodule.map_comap_eq_self (hf _).1] at hmap
      exact hlt'.ne hmap
    have hbound := hL (L + 1) _ hmono (fun j => ⟨hRelc _, hcomap _ (hf _).2.1⟩)
    omega
  have hPne : LinearMap.range φ ∈ P := ⟨le_rfl, hrange, hφ0⟩
  obtain ⟨T, hTP, hTmin⟩ := (Set.wellFoundedOn_iff.mp hwf).has_min P ⟨_, hPne⟩
  have hTms : MinStab (act '' Op) T := by
    refine ⟨hTP.2.1, fun U hU hUT => ?_⟩
    by_cases hU0 : U = ⊥
    · exact Or.inl hU0
    · right
      by_contra hne
      have hUP : U ∈ P := ⟨hUT.trans hTP.1, hU, hU0⟩
      exact hTmin U hUP ⟨lt_of_le_of_ne hUT hne, hUP, hTP⟩
  have hbcomm : ∀ b ∈ B, ∀ a ∈ act '' Op, a * b = b * a := by
    rintro b hb _ ⟨g, hg, rfl⟩
    exact hcomm g hg b hb
  have hstop : sSup {T | MinStab (act '' Op) T} = ⊤ := by
    have hst : Stab (act '' Op ∪ B) (sSup {T | MinStab (act '' Op) T}) := by
      intro a ha
      rcases ha with ha | ha
      · have hle : sSup {T | MinStab (act '' Op) T} ≤ (sSup {T | MinStab (act '' Op) T}).comap a :=
          sSup_le fun T' hT' y hy => (le_sSup hT' : T' ≤ _) (hT'.1 a ha y hy)
        exact fun x hx => hle hx
      · have hle : sSup {T | MinStab (act '' Op) T} ≤ (sSup {T | MinStab (act '' Op) T}).comap a :=
          sSup_le fun T' hT' y hy =>
            (le_sSup (MinStab.map hT' a (hbcomm a ha)) : T'.map a ≤ _) (Submodule.mem_map_of_mem hy)
        exact fun x hx => hle hx
    rcases hsimple _ hst with h | h
    · exact absurd (eq_bot_iff.mpr ((le_sSup (show T ∈ {T | MinStab (act '' Op) T} from hTms)).trans h.le)) hTP.2.2
    · exact h
  have hKs : Stab (act '' Op) (K.map φ) := by
    intro a ha y hy
    obtain ⟨g, hg, rfl⟩ := ha
    obtain ⟨k, hk, rfl⟩ := Submodule.mem_map.mp hy
    rw [← hint g hg k]
    exact Submodule.mem_map_of_mem (hK g hg k hk)
  obtain ⟨C, hCs, hCK, hCtop⟩ := exists_stab_compl hstop (K.map φ) hKs
  have hNK : C.comap φ ⊔ K = ⊤ := by
    rw [eq_top_iff]
    intro m _
    have hm : φ m ∈ C ⊔ K.map φ := by rw [hCtop]; exact Submodule.mem_top
    obtain ⟨c, hc, y, hy, hcy⟩ := Submodule.mem_sup.mp hm
    obtain ⟨k, hk, rfl⟩ := Submodule.mem_map.mp hy
    have hmk : m - k ∈ C.comap φ := by
      show φ (m - k) ∈ C
      rw [map_sub, ← hcy, add_sub_cancel_right]
      exact hc
    simpa using Submodule.add_mem_sup hmk hk
  by_cases hN : C.comap φ = ⊤
  · intro k hk
    have h1 : k ∈ C.comap φ := by rw [hN]; exact Submodule.mem_top
    have h2 : φ k ∈ C ⊓ K.map φ := ⟨h1, Submodule.mem_map_of_mem hk⟩
    rw [hCK] at h2
    exact (Submodule.mem_bot ℂ).mp h2
  · exact absurd (top_unique (hNK.symm.le.trans
      (sup_le (hmax _ (hRelc C) (hcomap C hCs) hN) le_rfl))) hKtop

end GlobalTheory.TensHead
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralFundamentalDomainLeOfMeetsOrbitsStatement
section
open MeasureTheory
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_fundamentalDomain_le_of_meets_all_orbits : ∀ {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (Γ : Subgroup G) [Countable Γ] (ν : Measure G) [ν.IsMulLeftInvariant] {𝓕 S : Set G}, IsFundamentalDomain Γ 𝓕 ν → MeasurableSet S → (∀ g, ∃ γ ∈ Γ, γ * g ∈ S) → ∀ {f : G → ℝ≥0∞}, Measurable f → (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) → ∫⁻ g in 𝓕, f g ∂ν ≤ ∫⁻ g in S, f g ∂ν := by
  first | exact @GlobalTheory.lintegral_fundamentalDomain_le_of_meets_orbits | exact GlobalTheory.lintegral_fundamentalDomain_le_of_meets_orbits | (intros; apply GlobalTheory.lintegral_fundamentalDomain_le_of_meets_orbits <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralUnfoldingLeOfTranslateCoverStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_unfolding_le_of_translate_cover : ∀ (G H : Type) [Group G] [Group H] [MeasurableSpace H] [MeasurableMul H] (μ : Measure H) [μ.IsMulLeftInvariant] (ι : H →* G), Function.Injective ι → ∀ (Γ : Subgroup G) [Countable Γ] (Kc : Set H), (∀ h, ∃ δ ∈ Γ.comap ι, δ * h ∈ Kc) → ∀ F : G → ENNReal, (∀ γ : G, Measurable fun h => F (γ * ι h)) → ∑' q : Γ ⧸ ι.range.subgroupOf Γ, ∫⁻ h, F ((q.out : Γ) * ι h) ∂μ ≤ ∫⁻ h in Kc, ∑' γ : Γ, F (γ * ι h) ∂μ := by
  first | exact @GlobalTheory.unfolding_cover_bound | exact GlobalTheory.unfolding_cover_bound | (intros; apply GlobalTheory.unfolding_cover_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MapSwapShearedProductMeasureUnimodular
section
open MeasureTheory Function
open scoped Pointwise

namespace GlobalTheory.UnfoldNormal

theorem map_swap_map_shear (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H]
    [BorelSpace H] (ν : Measure H) [ν.IsHaarMeasure] (N : Subgroup H) (hNc : IsClosed (N : Set H))
    (κ : Measure N) (hκ : κ.IsHaarMeasure) (hinv : κ.map (fun n => n⁻¹) = κ) :
    ((κ.prod ν).map (GlobalTheory.UnfoldNormal.shear N)).map Prod.swap
      = (κ.prod ν).map (GlobalTheory.UnfoldNormal.shear N) := by
  haveI : LocallyCompactSpace N := hNc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology (N : Set H)
  haveI := hκ
  have hsh : Measurable (shear N) := (measurableEmbedding_shear hNc).measurable
  have hT : MeasurePreserving (fun p : N × H => (p.1⁻¹, (p.1 : H) * p.2)) (κ.prod ν) (κ.prod ν) := by
    refine MeasurePreserving.skew_product (f := fun n : N => n⁻¹) (g := fun (n : N) (h : H) => (n : H) * h)
      ⟨measurable_inv, hinv⟩ ((measurable_subtype_coe.comp measurable_fst).mul measurable_snd) ?_
    exact Filter.Eventually.of_forall fun n => (measurePreserving_mul_left ν (n : H)).map_eq
  have hcomm : Prod.swap ∘ shear N = shear N ∘ (fun p : N × H => (p.1⁻¹, (p.1 : H) * p.2)) := by
    funext p
    simp [shear]
  rw [Measure.map_map measurable_swap hsh, hcomm, ← Measure.map_map hsh hT.measurable, hT.map_eq]

end GlobalTheory.UnfoldNormal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeanFundamentalDomainOfLeStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mean_fundamentalDomain_eq_one_of_le : ∀ (g : ℕ) (Λ Λ₁ : AddSubgroup (Fin g → ℂ)) (Fd D₁ : Set (Fin g → ℂ)) (f : (Fin g → ℂ) → ℝ), Countable Λ₁ → Λ ≤ Λ₁ → IsAddFundamentalDomain Λ Fd volume → IsAddFundamentalDomain Λ₁ D₁ volume → volume Fd ≠ ⊤ → (∀ a ∈ Λ₁, ∀ z, f (z + a) = f z) → (∫ z in D₁, f z) / (volume D₁).toReal = 1 → IntegrableOn f Fd volume ∧ (∫ z in Fd, f z) / (volume Fd).toReal = 1 := by
  first | exact @GlobalTheory.mean_fundamentalDomain_of_le | exact GlobalTheory.mean_fundamentalDomain_of_le | (intros; apply GlobalTheory.mean_fundamentalDomain_of_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemClosureOfForallDualVanishStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_closure_of_forall_clm_vanish : ∀ {E : Type} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
    {p : ℕ → Seminorm ℂ E}, WithSeminorms p → ∀ (Z : Submodule ℂ E) (x : E),
    (∀ f : E →L[ℂ] ℂ, (∀ z ∈ Z, f z = 0) → f x = 0) → x ∈ closure (Z : Set E) := by
  first | exact @GlobalTheory.mem_closure_of_forall_dual_vanish | exact GlobalTheory.mem_closure_of_forall_dual_vanish | (intros; apply GlobalTheory.mem_closure_of_forall_dual_vanish <;> assumption)
end

