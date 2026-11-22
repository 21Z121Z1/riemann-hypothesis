import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0090
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0016
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.QQuasiCompact
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0091
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0015

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ReduceLatticeCoordsToResidue
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint.EvalFrame

section Comb

variable {Ω : Type} [Field Ω] {Vs : Type} [AddCommGroup Vs] [Module Ω Vs] {R' : Subring Ω} {g : ℕ}

theorem comb_add (ℓ : Fin g → Vs) (x y : Fin g → R') : comb ℓ (x + y) = comb ℓ x + comb ℓ y := by
  simp [comb, add_smul, Finset.sum_add_distrib]

theorem comb_smul (ℓ : Fin g → Vs) (r : R') (x : Fin g → R') : comb ℓ (r • x) = (r : Ω) • comb ℓ x := by
  simp [comb, Finset.smul_sum, mul_smul]

theorem comb_sum {J : Type} (ℓ : Fin g → Vs) (s : Finset J) (c : J → R') (x : J → Fin g → R') :
    comb ℓ (s.sum fun i : J => c i • x i) = Finset.sum s (fun i : J => (c i : Ω) • comb ℓ (x i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [comb]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, comb_add, comb_smul, ih]

theorem comb_single (ℓ : Fin g → Vs) (k : Fin g) : comb ℓ (Pi.single k (1 : R')) = ℓ k := by
  unfold comb
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · simp

theorem comb_inj {ℓ : Fin g → Vs} (hl : LinearIndependent Ω ℓ) {x y : Fin g → R'}
    (h : comb ℓ x = comb ℓ y) : x = y := by
  have h0 : ∑ i, ((x i : Ω) - (y i : Ω)) • ℓ i = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr h
  funext i
  exact Subtype.ext (sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hl _ h0 i))

theorem mem_span_iff {ℓ : Fin g → Vs} {v : Vs} :
    v ∈ Submodule.span R' (Set.range ℓ) ↔ ∃ x : Fin g → R', comb ℓ x = v :=
  Submodule.mem_span_range_iff_exists_fun R'

end Comb

section Comparison₂

variable {E : Type} [Field E] [NumberField E] {Ω : Type} [Field Ω] {Vs : Type} [AddCommGroup Vs] [Module Ω Vs]
  {C : Type} [Field C] {R' : Subring Ω} {g : ℕ}

theorem psi_sum {J : Type} (ψ : R' →+* C) (s : Finset J) (c : J → R') (x : J → Fin g → R') :
    (fun k => ψ ((s.sum fun i : J => c i • x i) k)) = Finset.sum s (fun i : J => ψ (c i) • fun k => ψ (x i k)) := by
  funext k
  simp [Finset.sum_apply, map_sum]

theorem rho_comb_mem {ρ : 𝓞 E →+* Module.End Ω Vs} {ℓ : Fin g → Vs}
    (hst : ∀ a i, ρ a (ℓ i) ∈ Submodule.span R' (Set.range ℓ)) (a : 𝓞 E) (x : Fin g → R') :
    ρ a (comb ℓ x) ∈ Submodule.span R' (Set.range ℓ) := by
  unfold comb
  rw [map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [map_smul]
  exact Submodule.smul_mem _ (x i) (hst a i)

theorem eigProj_comb_mem {ρ : 𝓞 E →+* Module.End Ω Vs} {σ : E →+* Ω} {ℓ : Fin g → Vs}
    (hst : ∀ a i, ρ a (ℓ i) ∈ Submodule.span R' (Set.range ℓ)) (hσ : ∀ e : E, σ e ∈ R') (x : Fin g → R') :
    HT.eigProj ρ σ (comb ℓ x) ∈ Submodule.span R' (Set.range ℓ) := by
  unfold HT.eigProj
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun k _ => ?_
  exact Submodule.smul_mem _ (⟨_, hσ (HT.dualInt E k)⟩ : R') (rho_comb_mem hst _ x)

theorem tied_eigProj {ρ : 𝓞 E →+* Module.End Ω Vs} {ρC : 𝓞 E →+* Module.End C (Fin g → C)} {σ : E →+* Ω}
    {σC : E →+* C} {ℓ : Fin g → Vs} {ψ : R' →+* C} (hl : LinearIndependent Ω ℓ)
    (hst : ∀ a i, ρ a (ℓ i) ∈ Submodule.span R' (Set.range ℓ)) (ht : Tied ℓ ψ ρ ρC)
    (hσ : ∀ e : E, ∃ h : σ e ∈ R', ψ ⟨σ e, h⟩ = σC e) {x y : Fin g → R'}
    (h : HT.eigProj ρ σ (comb ℓ x) = comb ℓ y) :
    HT.eigProj ρC σC (fun i => ψ (x i)) = fun i => ψ (y i) := by
  have h1 : ∀ k, ∃ x' : Fin g → R', comb ℓ x' = ρ (RingOfIntegers.basis E k) (comb ℓ x) :=
    fun k => mem_span_iff.mp (rho_comb_mem hst _ x)
  choose x' hx' using h1
  have hy : y = ∑ k, (⟨σ (HT.dualInt E k), (hσ _).choose⟩ : R') • x' k := by
    apply comb_inj hl
    rw [← h, comb_sum]
    unfold HT.eigProj
    rw [LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hx']
    rfl
  have ht' := fun k => ht (RingOfIntegers.basis E k) x (x' k) (hx' k).symm
  rw [hy, psi_sum]
  unfold HT.eigProj
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [(hσ (HT.dualInt E k)).choose_spec, ← ht' k]
  rfl

end Comparison₂

theorem values_basis : ∀ (E : Type) [Field E] [NumberField E] (Ω Vs C : Type) [Field Ω] [CharZero Ω] [AddCommGroup Vs] [Module Ω Vs]
    [FiniteDimensional Ω Vs] [Field C] [CharZero C] (ρ : 𝓞 E →+* Module.End Ω Vs) (R' : Subring Ω) (g n : ℕ)
    (ℓ : Fin g → Vs) (ψ : R' →+* C) (ρC : 𝓞 E →+* Module.End C (Fin g → C)) (σ : E →+* Ω) (σC : E →+* C)
    (b : Fin n → Vs) (x : Fin n → Fin g → R'),
    LinearIndependent Ω ℓ → Submodule.span Ω (Set.range ℓ) = ⊤ →
    (∀ a i, ρ a (ℓ i) ∈ Submodule.span R' (Set.range ℓ)) → Tied ℓ ψ ρ ρC →
    (∀ e : E, ∃ h : σ e ∈ R', ψ ⟨σ e, h⟩ = σC e) →
    (∀ i, b i = comb ℓ (x i)) → LinearIndependent Ω b →
    Submodule.span R' (Set.range b) = HT.eigSub ρ σ (Submodule.span R' (Set.range ℓ)) →
    Module.finrank Ω (HT.eigSp ρ σ) = n →
    LinearIndependent C (fun i k => ψ (x i k)) ∧
      Submodule.span C (Set.range fun i k => ψ (x i k)) = HT.eigSp ρC σC := by
  intro E _ _ Ω Vs C _ _ _ _ _ _ _ ρ R' g n ℓ ψ ρC σ σC b x hl hsp hst ht hσ hb _ hbs hn
  have hσ' : ∀ e : E, σ e ∈ R' := fun e => (hσ e).choose

  have hproj : ∀ k, ∃ c : Fin n → R', HT.eigProj ρ σ (ℓ k) = comb ℓ (∑ i, c i • x i) := by
    intro k
    have hm : HT.eigProj ρ σ (ℓ k) ∈ HT.eigSub ρ σ (Submodule.span R' (Set.range ℓ)) := by
      refine ⟨?_, HT.LatBasic.eigProj_mem ρ σ _⟩
      have := eigProj_comb_mem (ρ := ρ) (σ := σ) hst hσ' (Pi.single k (1 : R'))
      rwa [comb_single] at this
    rw [← hbs] at hm
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R').mp hm
    refine ⟨c, ?_⟩
    rw [comb_sum, ← hc]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hb i]
    rfl
  choose c hc using hproj

  have hC : ∀ k, HT.eigProj ρC σC (Pi.single k 1) = ∑ i, ψ (c k i) • fun j => ψ (x i j) := by
    intro k
    have h1 : HT.eigProj ρ σ (comb ℓ (Pi.single k (1 : R'))) = comb ℓ (∑ i, c k i • x i) := by
      rw [comb_single, hc]
    have h2 := tied_eigProj hl hst ht hσ h1
    have h3 : (fun i => ψ ((Pi.single k (1 : R') : Fin g → R') i)) = Pi.single k (1 : C) := by
      funext i
      by_cases h : i = k
      · subst h; simp
      · simp [Pi.single_eq_of_ne h]
    rw [h3, psi_sum] at h2
    exact h2

  have hmem : ∀ i, (fun k => ψ (x i k)) ∈ HT.eigSp ρC σC := by
    intro i
    have hbi : b i ∈ HT.eigSp ρ σ := by
      have : b i ∈ HT.eigSub ρ σ (Submodule.span R' (Set.range ℓ)) := by
        rw [← hbs]
        exact Submodule.subset_span ⟨i, rfl⟩
      exact this.2
    unfold HT.eigSp at hbi ⊢
    rw [Submodule.mem_iInf] at hbi ⊢
    intro a
    have ha := hbi a
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at ha
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    have h1 : ρ a (comb ℓ (x i)) = comb ℓ ((⟨σ (a : E), hσ' _⟩ : R') • x i) := by
      rw [comb_smul, ← hb i, ha]
      rfl
    rw [ht a (x i) _ h1]
    funext j
    have h2 : ψ ⟨σ (a : E), hσ' _⟩ = σC (a : E) := (hσ (a : E)).choose_spec
    simp [h2]
  have hspan : Submodule.span C (Set.range fun i k => ψ (x i k)) = HT.eigSp ρC σC := by
    refine le_antisymm (Submodule.span_le.mpr ?_) fun v hv => ?_
    · rintro _ ⟨i, rfl⟩
      exact hmem i
    · rw [← HT.LatBasic.eigProj_of_mem hv]
      have hv' : v = ∑ k, v k • (Pi.single k (1 : C) : Fin g → C) := by
        funext j
        simp [Finset.sum_apply, Pi.single_apply]
      rw [hv', map_sum]
      refine Submodule.sum_mem _ fun k _ => ?_
      rw [map_smul, hC]
      refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => ?_)
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

  let B : Module.Basis (Fin g) Ω Vs := Module.Basis.mk hl hsp.ge
  have hB : ∀ k, B k = ℓ k := fun k => Module.Basis.mk_apply hl hsp.ge k
  have hrepr : ∀ (y : Fin g → R') (j : Fin g), B.repr (comb ℓ y) j = (y j : Ω) := by
    intro y j
    have : comb ℓ y = ∑ i, (y i : Ω) • B i := by
      unfold comb
      exact Finset.sum_congr rfl fun i _ => by rw [hB]
    rw [this, map_sum, Finsupp.finset_sum_apply]
    simp [Finsupp.single_apply]
  have htrΩ : (∑ k, ((∑ i, c k i • x i) k : R') : R') = (n : R') := by
    apply Subtype.ext
    have h1 := HT.EigDim.trace_eigProj ρ σ
    rw [LinearMap.trace_eq_matrix_trace Ω B, Matrix.trace, hn] at h1
    push_cast
    rw [← h1]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply, hB, hc, hrepr]
  have htrC : (Module.finrank C (HT.eigSp ρC σC) : C) = (n : C) := by
    have h1 := HT.EigDim.trace_eigProj ρC σC
    rw [LinearMap.trace_eq_matrix_trace C (Pi.basisFun C (Fin g)), Matrix.trace] at h1
    rw [← h1, ← map_natCast ψ n, ← htrΩ, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply, Pi.basisFun_apply, hC]
    simp [Finset.sum_apply, map_sum]
  have hfr : Module.finrank C (HT.eigSp ρC σC) = n := by exact_mod_cast htrC
  refine ⟨?_, hspan⟩
  rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, hspan, hfr, Fintype.card_fin]

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint.EvalFrame
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SabMapIdStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sab_map_id : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S), ∃ m : SABMap t t (𝟙 S), m.φ = 𝟙 t.G.left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.exists_sabMap_id | exact GlobalTheory.CompanionTheory.Ar.exists_sabMap_id | (intros; apply GlobalTheory.CompanionTheory.Ar.exists_sabMap_id <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecializeHodgeLatticeEigenFrame
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint.EvalProj

theorem ev_eigProj : ∀ (E : Type) [Field E] [NumberField E] (Ω Vs C : Type) [Field Ω] [AddCommGroup Vs] [Module Ω Vs] [Field C]
    (R' : Subring Ω) (g : ℕ) (ℓ : Fin g → Vs) (ψ : R' →+* C)
    (ρH : 𝓞 E →+* Module.End Ω (Vs × Module.Dual Ω Vs))
    (ρHC : 𝓞 E →+* Module.End C ((Fin g → C) × Module.Dual C (Fin g → C)))
    (HL : Submodule R' (Vs × Module.Dual Ω Vs)) (ev : HL →ₛₗ[ψ] (Fin g → C) × Module.Dual C (Fin g → C))
    (σ : E →+* Ω) (σC : E →+* C) (h : HL) (hp : HT.eigProj ρH σ (h : Vs × Module.Dual Ω Vs) ∈ HL),
    IsEval ℓ ψ ρH ρHC HL ev → (∀ e : E, ∃ h : σ e ∈ R', ψ ⟨σ e, h⟩ = σC e) → (∀ a, ∀ h ∈ HL, ρH a h ∈ HL) →
    ev ⟨_, hp⟩ = HT.eigProj ρHC σC (ev h) := by
  intro E _ _ Ω Vs C _ _ _ _ R' g ℓ ψ ρH ρHC HL ev σ σC h hp hev htie hst
  choose hc hψ using htie
  have hsum : (⟨_, hp⟩ : HL) = ∑ k, (⟨σ (HT.dualInt E k), hc _⟩ : R') •
      (⟨ρH (RingOfIntegers.basis E k) (h : Vs × Module.Dual Ω Vs), hst _ _ h.2⟩ : HL) := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finset_sum]
    simp only [HT.eigProj, LinearMap.sum_apply, LinearMap.smul_apply]
    rfl
  rw [hsum, map_sum]
  simp only [HT.eigProj, LinearMap.sum_apply, LinearMap.smul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.map_smulₛₗ, hψ, hev.1 _ h]

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint.EvalProj
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecializeHodgeLatticeEigenbasis
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem isAdapted_eval : ∀ (E : Type) [Field E] [NumberField E] (Ω Vs C : Type) [Field Ω] [AddCommGroup Vs] [Module Ω Vs] [Field C]
    (R' : Subring Ω) (g p q : ℕ) (ℓ : Fin g → Vs) (ψ : R' →+* C)
    (ρH : 𝓞 E →+* Module.End Ω (Vs × Module.Dual Ω Vs))
    (ρHC : 𝓞 E →+* Module.End C ((Fin g → C) × Module.Dual C (Fin g → C)))
    (HL : Submodule R' (Vs × Module.Dual Ω Vs)) (ev : HL →ₛₗ[ψ] (Fin g → C) × Module.Dual C (Fin g → C))
    (σ : E →+* Ω) (σC : E →+* C) (b₁ : Fin p → Vs) (b₂ : Fin q → Vs) (u : Fin (p + q) → Vs × Module.Dual Ω Vs)
    (x₁ : Fin p → Fin g → R') (x₂ : Fin q → Fin g → R') (hu : ∀ i, u i ∈ HL),
    IsEval ℓ ψ ρH ρHC HL ev → (∀ e : E, ∃ h : σ e ∈ R', ψ ⟨σ e, h⟩ = σC e) → (∀ a, ∀ h ∈ HL, ρH a h ∈ HL) →
    IsAdapted ρH σ b₁ b₂ u → (∀ i, b₁ i = comb ℓ (x₁ i)) → (∀ i, b₂ i = comb ℓ (x₂ i)) →
    IsAdapted ρHC σC (fun i k => ψ (x₁ i k)) (fun i k => ψ (x₂ i k)) (fun i => ev ⟨u i, hu i⟩) := by
  intro E _ _ Ω Vs C _ _ _ _ R' g p q ℓ ψ ρH ρHC HL ev σ σC b₁ b₂ u x₁ x₂ hu hE hσ hcl hA hb₁ hb₂
  unfold GlobalTheory.CompanionTheory.Ar.Flat.CPoint.IsEval at hE
  unfold GlobalTheory.CompanionTheory.Ar.Flat.IsAdapted at hA ⊢
  obtain ⟨hE1, hE2, hE3⟩ := hE
  obtain ⟨hA1, hA2, hA3⟩ := hA
  refine ⟨?_, ?_, ?_⟩
  · intro i
    show ev ⟨u i, hu i⟩ ∈ GlobalTheory.CompanionTheory.Ar.HT.eigSp ρHC σC
    have hui := hA1 i
    rw [GlobalTheory.CompanionTheory.Ar.HT.eigSp, Submodule.mem_iInf] at hui ⊢
    intro a
    have h1 := hui a
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h1
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    change ρH a (u i) = σ (a : E) • u i at h1
    show ρHC a (ev ⟨u i, hu i⟩) = σC (a : E) • ev ⟨u i, hu i⟩
    obtain ⟨hσa, hψ⟩ := hσ (a : E)
    have hmem : ρH a (u i) ∈ HL := hcl a (u i) (hu i)
    have e1 : ev ⟨ρH a (u i), hmem⟩ = ρHC a (ev ⟨u i, hu i⟩) := hE1 a ⟨u i, hu i⟩ hmem
    have e2 : (⟨ρH a (u i), hmem⟩ : HL) = (⟨σ a, hσa⟩ : R') • (⟨u i, hu i⟩ : HL) := by
      apply Subtype.ext
      simp only [Submodule.coe_smul, Subring.smul_def]
      exact h1
    rw [← e1, e2, map_smulₛₗ, hψ]
  · intro i
    exact hE2 ⟨u (Fin.castAdd q i), hu _⟩ (x₁ i) ((hA2 i).trans (hb₁ i))
  · intro j
    obtain ⟨hj1, hj2⟩ := hA3 j
    constructor
    · have hc : (u (Fin.natAdd p j)).1 = comb ℓ (fun _ => (0 : R')) := by
        rw [hj1]
        simp [GlobalTheory.CompanionTheory.Ar.Flat.CPoint.comb]
      have h3 := hE2 ⟨u (Fin.natAdd p j), hu _⟩ (fun _ => 0) hc
      refine h3.trans ?_
      funext k
      simp
    · intro j'
      have hc : (u (Fin.natAdd p j)).2 (comb ℓ (x₂ j')) = ((if j = j' then 1 else 0 : R') : Ω) := by
        rw [← hb₂ j', hj2 j']
        split_ifs <;> simp
      have h3 := hE3 ⟨u (Fin.natAdd p j), hu _⟩ (x₂ j') (if j = j' then 1 else 0) hj1 hc
      refine h3.trans ?_
      split_ifs <;> simp

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SqMap
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.FrGauge

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Conj Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1)
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

section Values

variable {X Y F : Scheme.{0}} {L : LB X} {M : LB Y} {f : F ⟶ X} {g : F ⟶ Y}

def wv (w : LB.Iso (L.pull f) (M.pull g)) {Z : Scheme.{0}} (ψ : Z ⟶ F) (z : Z) (JL : (Z ⟶ X) → L.ι)
    (JM : (Z ⟶ Y) → M.ι) : (Z.presheaf.stalk z)ˣ :=
  gm ψ z _ (w.s (fun _ => JM (ψ ≫ g), fun _ => JL (ψ ≫ f)))

def Tr (w : LB.Iso (L.pull f) (M.pull g)) {Y' : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y' ⟶ F))
    (φL : K → (Y' ⟶ X)) (φM : K → (Y' ⟶ Y)) (ε : K → ℤ) (c : LB.Gen (LB.LinComb L φL ε))
    (b : LB.Gen (LB.LinComb M φM ε)) (u : Γ(Y', ⊤)ˣ) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (JL : (Z ⟶ X) → L.ι) (JM : (Z ⟶ Y) → M.ι), Good L z JL → Good M z JM →
    val c r z JL * ∏ k, wv w (r ≫ φ k) z JL JM ^ ε k = gm r z ⊤ u * val b r z JM

end Values

section Series

variable {R : Type} [CommRing R] {d d' : ℕ}

def linQ (Qs : Fin d' → PS R 1 d) : Matrix (Fin d') (Fin d) R :=
  fun i l => MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), l) 1) (Qs i)

def subQ (Qs : Fin d' → PS R 1 d) (f : PS R 2 d') : PS R 2 d :=
  MvPowerSeries.subst (fun p : Fin 2 × Fin d' => ev (n := 2) ![pt R d p.1] (Qs p.2)) f

def sub1 (Qs : Fin d' → PS R 1 d) (m : ℕ) : Jet R (Fin 1 × Fin d') m →ₐ[R] Jet R (Fin 1 × Fin d) m :=
  jetSubstP m fun p : Fin 1 × Fin d' => psTrunc m (Qs p.2)

def sub2 (Qs : Fin d' → PS R 1 d) (m : ℕ) : Jet R (Fin 2 × Fin d') m →ₐ[R] Jet R (Fin 2 × Fin d) m :=
  jetSubstP m fun p : Fin 2 × Fin d' => psIn d m ![p.1] (Qs p.2)

end Series

section Fibre

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)
  {k : Type} [Field k] (x : Sp k ⟶ X)

abbrev GF : Over (Sp k) := (Over.pullback x).obj t.G

def toF {T : Over (Sp k)} (a : T.left ⟶ t.G.left) (h : a ≫ t.G.hom = T.hom ≫ x) : T ⟶ GF t x :=
  Over.homMk (pullback.lift a T.hom h) (pullback.lift_snd _ _ _)

def fibPt {A : Type} [CommRing A] [Algebra k A] (y : overAt x A ⟶ t.G) : overAt (𝟙 (Sp k)) A ⟶ GF t x :=
  toF t x y.left (by simpa using Over.w y)

def cubeF {A : Type} [CommRing A] [Algebra k A] (xs : Fin 2 → (overAt x A ⟶ t.G)) (I : ULift (Finset (Fin 2))) :
    Sp A ⟶ (GF t x).left :=
  (fibPt t x (psum t.G xs I.down)).left

def sqPr (p : GF t x ⊗ GF t x ⟶ GF t x) : Over.mk ((GF t x ⊗ GF t x).hom ≫ x) ⟶ t.G :=
  Over.homMk (p.left ≫ pullback.fst t.G.hom x) (by
    have h : p.left ≫ pullback.snd t.G.hom x = (GF t x ⊗ GF t x).hom := Over.w p
    show (p.left ≫ pullback.fst t.G.hom x) ≫ t.G.hom = (GF t x ⊗ GF t x).hom ≫ x
    rw [Category.assoc, pullback.condition, ← Category.assoc, h])

def sqMap : (GF t x ⊗ GF t x).left ⟶ (t.G ⊗ t.G).left :=
  (lift (sqPr t x (fst _ _)) (sqPr t x (snd _ _))).left

def sqPt (a : t.G ⊗ t.G ⟶ t.G) : GF t x ⊗ GF t x ⟶ GF t x :=
  toF t x (sqMap t x ≫ a.left) (Over.w (lift (sqPr t x (fst _ _)) (sqPr t x (snd _ _)) ≫ a))

abbrev AdTy (t : SAB H X) (a : 𝓞 E) : Type :=
  LB.Gen (LB.LinComb t.PP.L
    (Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)])
      (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G]))
    (Sum.elim (cε 2) fun I => -cε 2 I))

def adF (a : 𝓞 E) : ULift (Finset (Fin 2)) ⊕ ULift (Finset (Fin 2)) →
    ((GF t x ⊗ GF t x).left ⟶ (GF t x).left) :=
  Sum.elim (fun I => (sqPt t x (psum t.G ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)] I.down)).left)
    (fun I => (sqPt t x (psum t.G ![fst t.G t.G ≫ t.act.act a, snd t.G t.G] I.down)).left)

def ax0 : (GF t x).left ⟶ (GF t x ⊗ GF t x).left := (lift (1 : GF t x ⟶ GF t x) (𝟙 (GF t x))).left

def ax1 : (GF t x).left ⟶ (GF t x ⊗ GF t x).left := (lift (𝟙 (GF t x)) (1 : GF t x ⟶ GF t x)).left

def qq {t : SAB H X} {x : Sp k ⟶ X} (Q : AbQuot t x) : (GF t x ⊗ GF t x).left ⟶ (Q.tB.G ⊗ Q.tB.G).left :=
  (lift (fst (GF t x) (GF t x) ≫ Q.q) (snd (GF t x) (GF t x) ≫ Q.q)).left

end Fibre

section AdRel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
  {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G)

def AdRel (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (ad : 𝓞 E → MvPowerSeries (Fin 2 × Fin d) S)
    (e : ∀ m, FrTyG t x0 d x m) (a : 𝓞 E) (wL : AdTy t a) : Prop :=
  ∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m (ad a) ∧
    LB.Gen.Corr t.PP.L _ _ _ _
      (LB.mulGen t.PP.L _ _ _ _
        (LB.pullGen t.PP.L _ _ wL (lift (jptG t x0 d x m (0 : Fin 2)) (jptG t x0 d x m (1 : Fin 2))).left)
        (peG t x0 d x e m ![fun j => psIn d m ![0] (act a j), fun j => MvPolynomial.X ((1 : Fin 2), j)]))
      (scaleGenG t _ _ (unitΓ u)
        (peG t x0 d x e m ![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)]))

end AdRel

end GlobalTheory.CompanionTheory.Ar.Flat.FrGauge
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionAlongBaseChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_along_base_change : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] (Γ : BT.QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] (x : Sp R ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ (R' : Type) [CommRing R'] [IsDomain R'] (φ : R →+* R') (Γ' : BT.QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ φ F → Γ'.IsTorsionAlong G (Spec.map (CommRingCat.ofHom φ) ≫ x) N (F ≫ i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TorBC.isTorsionAlong_baseChange | exact GlobalTheory.CompanionTheory.Ar.TorBC.isTorsionAlong_baseChange | (intros; apply GlobalTheory.CompanionTheory.Ar.TorBC.isTorsionAlong_baseChange <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionAlongGroupPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_along_group_pullback : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] (Γ : BT.QFGroup R T) (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (x' : Sp R ⟶ S') (y : Sp R ⟶ S) (N : ℕ) (i₁ : Γ.G.left ⟶ G.left), IsGrpPullback G' G f φ → x' ≫ f = y → Γ.IsTorsionAlong G y N i₁ → ∃ i' : Γ.G.left ⟶ G'.left, i' ≫ φ = i₁ ∧ Γ.IsTorsionAlong G' x' N i' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TorPull.exists_lift_isTorsionAlong | exact GlobalTheory.CompanionTheory.Ar.TorPull.exists_lift_isTorsionAlong | (intros; apply GlobalTheory.CompanionTheory.Ar.TorPull.exists_lift_isTorsionAlong <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionAlongOrderDividesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_along_order_divides : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] (Γ : BT.QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] (x : Sp R ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ t : T, t ^ N = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.TorsionKilled.pow_eq_one | exact GlobalTheory.CompanionTheory.Ar.BT.TorsionKilled.pow_eq_one | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.TorsionKilled.pow_eq_one <;> assumption)
end

