import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FactTypePrime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0991
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0220
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0147
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0167
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0155
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeLevelIdempotentProductAndCentralProduct
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevRange

theorem range_sum_eq_eig {G M : Type} [Group G] [Fintype G] [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M)
    (P : Subgroup G) (χ : P → ℂ) (E : G → ℂ) (k : ℂ) (hk : k ≠ 0) (h0 : ∀ g, g ∉ P → E g = 0)
    (h1 : ∀ g : P, E g * χ g = k) (hm : ∀ a b : P, χ (a * b) = χ a * χ b) :
    LinearMap.range (∑ g, E g • ρ g) = eig ρ P χ := by
  classical
  have hs : ∀ (p : P) (g : G), E g = χ p * E (p * g) := by
    intro p g
    by_cases hg : g ∈ P
    · have e1 := h1 ⟨g, hg⟩
      have e2 := h1 (p * ⟨g, hg⟩)
      rw [hm] at e2
      have hne : χ ⟨g, hg⟩ ≠ 0 := by
        intro h; rw [h, mul_zero] at e1; exact hk e1.symm
      apply mul_right_cancel₀ hne
      simp only [Subgroup.coe_mul] at e1 e2
      rw [e1, ← e2]; ring
    · have : (p : G) * g ∉ P := fun h => hg ((P.mul_mem_cancel_left p.2).1 h)
      rw [h0 g hg, h0 _ this, mul_zero]
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    rw [mem_eig]
    intro p
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum]
    rw [← Equiv.sum_comp (Equiv.mulLeft (p : G)) (fun g => χ p • E g • ρ g y)]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [hs p g, Equiv.coe_mulLeft, map_mul, Module.End.mul_apply, mul_smul]
  · intro x hx
    rw [mem_eig] at hx
    have hT : (∑ g, E g • ρ g) x = (∑ g : G, if g ∈ P then k else 0) • x := by
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_smul]
      refine Finset.sum_congr rfl fun g _ => ?_
      by_cases hg : g ∈ P
      · rw [if_pos hg, ← h1 ⟨g, hg⟩, mul_smul, ← hx ⟨g, hg⟩]
      · rw [if_neg hg, h0 g hg, zero_smul, zero_smul]
    have hne : (∑ g : G, if g ∈ P then k else 0) ≠ 0 := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      refine mul_ne_zero ?_ hk
      have : (Finset.univ.filter fun g : G => g ∈ P).Nonempty := ⟨1, by simp⟩
      exact_mod_cast this.card_pos.ne'
    refine ⟨(∑ g : G, if g ∈ P then k else 0)⁻¹ • x, ?_⟩
    rw [map_smul, hT, smul_smul, inv_mul_cancel₀ hne, one_smul]

theorem range_mul_eq_inf {M : Type} [AddCommGroup M] [Module ℂ M] (C T : Module.End ℂ M) (hC : C * C = C)
    (hc : C * T = T * C) : LinearMap.range (C * T) = LinearMap.range T ⊓ LinearMap.ker (C - LinearMap.id) := by
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    refine ⟨⟨C y, ?_⟩, ?_⟩
    · rw [hc]; rfl
    · have : C (C (T y)) = C (T y) := by rw [← Module.End.mul_apply, hC]
      simp [this]
  · rintro _ ⟨⟨y, rfl⟩, h⟩
    refine ⟨y, ?_⟩
    simpa [sub_eq_zero] using h

theorem op_comp {G H M : Type} [Group G] [Fintype G] [Group H] [Fintype H] [AddCommGroup M] [Module ℂ M]
    (Φ : G ≃* H) (ρ : Representation ℂ G M) (e : H → ℂ) :
    GlobalTheory.BadShare.op (M := M) (ρ.comp Φ.symm.toMonoidHom) e = ∑ g, e (Φ g) • ρ g := by
  unfold GlobalTheory.BadShare.op
  rw [← Equiv.sum_comp Φ.toEquiv]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp

theorem tens_e_mul {g N : ℕ} [Fact g.Prime] {ι : Type} [Fintype ι] (L : ι → GlobalTheory.BadShare.Lev g N)
    (γ : ι → GlobalTheory.BadShare.GG g N) (h : ∀ v, (L v).Mem (γ v)) :
    GlobalTheory.BadShare.tens (fun v => (L v).e) γ * ∏ v, (L v).chi (γ v) = ∏ v, (Nat.card {u // (L v).Mem u} : ℂ)⁻¹ := by
  unfold GlobalTheory.BadShare.tens
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  have := GlobalTheory.BadShare.Basic.chi_ne (L v) (γ v)
  simp only [GlobalTheory.BadShare.Lev.e, GlobalTheory.BadShare.eps, if_pos (h v)]
  field_simp

theorem tens_e_zero {g N : ℕ} [Fact g.Prime] {ι : Type} [Fintype ι] (L : ι → GlobalTheory.BadShare.Lev g N)
    (γ : ι → GlobalTheory.BadShare.GG g N) (h : ¬ ∀ v, (L v).Mem (γ v)) :
    GlobalTheory.BadShare.tens (fun v => (L v).e) γ = 0 := by
  obtain ⟨v, hv⟩ := not_forall.1 h
  exact Finset.prod_eq_zero (Finset.mem_univ v) (by simp only [GlobalTheory.BadShare.Lev.e, GlobalTheory.BadShare.eps, if_neg hv])

theorem prod_card_ne {g N : ℕ} [Fact g.Prime] {ι : Type} [Fintype ι] (L : ι → GlobalTheory.BadShare.Lev g N) :
    (∏ v, (Nat.card {u // (L v).Mem u} : ℂ)⁻¹) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun v _ => inv_ne_zero ?_
  haveI : Nonempty {u // (L v).Mem u} := ⟨⟨1, GlobalTheory.BadShare.Basic.mem_one (L v)⟩⟩
  exact_mod_cast Nat.card_pos.ne'

theorem ranges : ∀ (g₁ g₂ N : ℕ) [Fact g₁.Prime] [Fact g₂.Prime] (ι₁ ι₂ G M : Type) [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂] [Group G] [Fintype G] [AddCommGroup M] [Module ℂ M] (Φ : G ≃* (ι₁ → GlobalTheory.BadShare.GG g₁ N) × (ι₂ → GlobalTheory.BadShare.GG g₂ N)) (L₁ : ι₁ → GlobalTheory.BadShare.Lev g₁ N) (L₂ : ι₂ → GlobalTheory.BadShare.Lev g₂ N) (P : Subgroup G) (χ : P → ℂ) (ρ : Representation ℂ G M) [Fintype ((ι₁ → GlobalTheory.BadShare.GG g₁ N) × (ι₂ → GlobalTheory.BadShare.GG g₂ N))] (c : (ι₁ → GlobalTheory.BadShare.GG g₁ N) × (ι₂ → GlobalTheory.BadShare.GG g₂ N) → ℂ), (∀ g : G, g ∈ P ↔ (∀ v, (L₁ v).Mem ((Φ g).1 v)) ∧ ∀ v, (L₂ v).Mem ((Φ g).2 v)) → (∀ g : P, χ g = (∏ v, (L₁ v).chi ((Φ g).1 v)) * ∏ v, (L₂ v).chi ((Φ g).2 v)) → GlobalTheory.BadShare.conv c c = c → (∀ a, GlobalTheory.BadShare.conv c a = GlobalTheory.BadShare.conv a c) → LinearMap.range (GlobalTheory.BadShare.op (M := M) (ρ.comp Φ.symm.toMonoidHom) (GlobalTheory.BadShare.tens2 (GlobalTheory.BadShare.tens fun v => (L₁ v).e) (GlobalTheory.BadShare.tens fun v => (L₂ v).e))) = eig ρ P χ ∧ LinearMap.range (GlobalTheory.BadShare.op (M := M) (ρ.comp Φ.symm.toMonoidHom) (GlobalTheory.BadShare.conv c (GlobalTheory.BadShare.tens2 (GlobalTheory.BadShare.tens fun v => (L₁ v).e) (GlobalTheory.BadShare.tens fun v => (L₂ v).e)))) = eig ρ P χ ⊓ LinearMap.ker ((∑ g : G, c (Φ g) • ρ g) - LinearMap.id) := by
  intro g₁ g₂ N _ _ ι₁ ι₂ G M _ _ _ _ _ _ _ _ Φ L₁ L₂ P χ ρ _ c hP hχ hcc hc
  have key : LinearMap.range (GlobalTheory.BadShare.op (M := M) (ρ.comp Φ.symm.toMonoidHom) (GlobalTheory.BadShare.tens2 (GlobalTheory.BadShare.tens fun v => (L₁ v).e) (GlobalTheory.BadShare.tens fun v => (L₂ v).e))) = eig ρ P χ := by
    rw [op_comp]
    refine range_sum_eq_eig ρ P χ _ _ (mul_ne_zero (prod_card_ne L₁) (prod_card_ne L₂)) ?_ ?_ ?_
    · intro g hg
      rw [hP, not_and_or] at hg
      unfold GlobalTheory.BadShare.tens2
      rcases hg with h | h
      · rw [tens_e_zero _ _ h, zero_mul]
      · rw [tens_e_zero L₂ _ h, mul_zero]
    · intro g
      obtain ⟨h1, h2⟩ := (hP g).1 g.2
      rw [hχ, ← tens_e_mul L₁ _ h1, ← tens_e_mul L₂ _ h2]
      unfold GlobalTheory.BadShare.tens2
      ring
    · intro a b
      obtain ⟨a1, a2⟩ := (hP a).1 a.2
      obtain ⟨b1, b2⟩ := (hP b).1 b.2
      rw [hχ, hχ, hχ]
      simp only [Subgroup.coe_mul, map_mul, Prod.fst_mul, Prod.snd_mul, Pi.mul_apply]
      simp only [fun v => GlobalTheory.BadShare.Basic.chi_mul (L₁ v) (a1 v) (b1 v),
        fun v => GlobalTheory.BadShare.Basic.chi_mul (L₂ v) (a2 v) (b2 v), Finset.prod_mul_distrib]
      ring
  refine ⟨key, ?_⟩
  rw [GlobalTheory.BadShare.Basic.op_conv, range_mul_eq_inf, key, op_comp]
  · rw [← GlobalTheory.BadShare.Basic.op_conv, hcc]
  · rw [← GlobalTheory.BadShare.Basic.op_conv, hc, GlobalTheory.BadShare.Basic.op_conv]

end GlobalTheory.LevRange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPointActsLinearlyOnMultiplicityValuesPosDef
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RealAct

variable {D : D7} {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar}

def ActsLin (θ : InfFam D) (M : DSModel V S) (k : GA D V) : Prop :=
  ∃ φ : Module.End ℂ (MultilinearMap ℂ (fun τ : D.what₂.Tau => M.sm τ) ℂ),
    ∀ (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ T ∈ Mult θ M J χ, ∀ g : GA D V, evAt M (g * k) T = φ (evAt M g T)

theorem actsLin_one (M : DSModel V S) : ActsLin θ M 1 := by
  refine ⟨LinearMap.id, ?_⟩
  intro J χ T _ g
  rw [mul_one]
  rfl

theorem actsLin_mul {M : DSModel V S} {a b : GA D V} (ha : ActsLin θ M a) (hb : ActsLin θ M b) :
    ActsLin θ M (a * b) := by
  obtain ⟨φa, hφa⟩ := ha
  obtain ⟨φb, hφb⟩ := hb
  refine ⟨φb ∘ₗ φa, fun J χ T hT g => ?_⟩
  calc evAt M (g * (a * b)) T = evAt M ((g * a) * b) T := by rw [mul_assoc]
    _ = φb (evAt M (g * a) T) := hφb J χ T hT (g * a)
    _ = φb (φa (evAt M g T)) := by rw [hφa J χ T hT g]

theorem actsLin_atTau {M : DSModel V S} (hM : AllPlus M) (τ : D.what₂.Tau)
    {u : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hu : u ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) :
    ActsLin θ M (atTau θ V τ u) := by
  classical
  have htop : M.sm τ = ⊤ := (AllPlus.finite_smooth_irreducible _ V S M hM τ).2.1
  let A : M.sm τ →ₗ[ℂ] M.sm τ :=
    (M.rep τ u).toLinearMap.restrict (fun x _ => by rw [htop]; exact Submodule.mem_top)
  let F : ∀ i, M.sm i →ₗ[ℂ] M.sm i := Function.update (fun i => (LinearMap.id : M.sm i →ₗ[ℂ] M.sm i)) τ A
  refine ⟨MultilinearMap.compLinearMapₗ F, ?_⟩
  intro J χ T hT g
  have hmap := (GlobalTheory.MultMem.mem_mult_iff _ θ V S M J χ T).1 hT
  ext v
  have hv : (fun i => F i (v i)) = Function.update v τ (A (v τ)) := by
    funext i
    by_cases h : i = τ
    · subst h
      simp [F]
    · simp [F, h]
  have hw : ((A (v τ) : M.sm τ) : M.H τ) = M.rep τ u (v τ) := rfl
  have key := congrFun (hmap.equiv τ u hu v (A (v τ)) hw) g
  rw [evAt_apply]
  simp only [MultilinearMap.compLinearMapₗ_apply, MultilinearMap.compLinearMap_apply]
  rw [evAt_apply, hv, key]
  rfl

theorem real_acts : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S), IsInfFam θ → AllPlus M → ∀ k ∈ GinfC V, ∃ φ : Module.End ℂ (MultilinearMap ℂ (fun τ : D.what₂.Tau => M.sm τ) ℂ), ∀ (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ T ∈ Mult θ M J χ, ∀ g : GA D V, evAt M (g * k) T = φ (evAt M g T) := by
  intro D θ V S M hθ hM k hk
  classical
  obtain ⟨L, -, hLmul, -, hLarch, hLinv, hLat, -⟩ := GlobalTheory.RealLift.exists_real_lift D θ V hθ
  obtain ⟨a, hUa, hkL⟩ : ∃ a, a ∈ GlobalTheory.HolDict.UG (gramAt D V) ∧ L a = k := ⟨_, hLarch k, hLinv k hk⟩
  have haU : ∀ τ, a τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := hUa
  have h1U : ∀ τ, (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
    intro τ
    simp [Formalism.QuantumDeterminants.UH]
  have hL1 : L 1 = 1 := by
    have h := hLmul 1 (fun τ => h1U τ) 1 (fun τ => h1U τ)
    rw [mul_one] at h
    calc L 1 = (L 1)⁻¹ * (L 1 * L 1) := by group
      _ = (L 1)⁻¹ * L 1 := by rw [← h]
      _ = 1 := inv_mul_cancel _
  have hpart : ∀ s : Finset D.what₂.Tau,
      ActsLin θ M (L fun τ => if τ ∈ s then a τ else 1) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have he : (fun τ : D.what₂.Tau => if τ ∈ (∅ : Finset D.what₂.Tau) then a τ else 1) = 1 := by
        funext τ
        simp
      rw [he, hL1]
      exact actsLin_one M
    | insert x s hx ih =>
      have hs : (fun τ => if τ ∈ s then a τ else 1) ∈ GlobalTheory.HolDict.UG (gramAt D V) := by
        intro τ
        by_cases h : τ ∈ s
        · simpa [h] using haU τ
        · simpa [h] using h1U τ
      have hsing : Pi.mulSingle x (a x) ∈ GlobalTheory.HolDict.UG (gramAt D V) := by
        intro τ
        by_cases h : τ = x
        · subst h
          simpa using haU τ
        · simpa [Pi.mulSingle_apply, h] using h1U τ
      have hsplit : (fun τ => if τ ∈ insert x s then a τ else 1)
          = Pi.mulSingle x (a x) * fun τ => if τ ∈ s then a τ else 1 := by
        funext τ
        by_cases h : τ = x
        · subst h
          simp [hx]
        · simp [h, Pi.mulSingle_apply]
      rw [hsplit, hLmul _ hsing _ hs, ← hLat x (a x) (haU x)]
      exact actsLin_mul (actsLin_atTau hM x (haU x)) ih
  have hall : (fun τ => if τ ∈ (Finset.univ : Finset D.what₂.Tau) then a τ else 1) = a := by
    funext τ
    simp
  have := hpart Finset.univ
  rw [hall, hkL] at this
  exact this

end GlobalTheory.RealAct

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeParameterGLStarEqInvOfUnitarisable
section
noncomputable section

namespace GlobalTheory.LFun.UnitaryParam

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.LFun.ConjPlace

theorem esymm_map_conj (s : Multiset ℂ) (j : ℕ) :
    (s.map (starRingEnd ℂ)).esymm j = starRingEnd ℂ (s.esymm j) := by
  simp only [Multiset.esymm, Multiset.powersetCard_map, map_multiset_sum, map_multiset_prod, Multiset.map_map,
    Function.comp_def]

theorem satEig_map_star (q n : ℕ) (B : Multiset ℂˣ) (j : ℕ) :
    satEig q n (B.map star) j = starRingEnd ℂ (satEig q n B j) := by
  have h : ((q : ℂ)).arg ≠ Real.pi := by rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm
  have h2 := Complex.conj_cpow (q : ℂ) (((j : ℂ) * ((n : ℂ) - j)) / 2) h
  rw [satEig, satEig, map_mul, ← esymm_map_conj, Multiset.map_map, Multiset.map_map]
  congr 1
  rw [map_natCast, map_div₀, map_mul, map_sub, map_natCast, map_natCast, map_ofNat] at h2
  exact h2

section General

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} {K : Subgroup G}
  {h : G → ℂ} {x : V}

theorem form_heckeVec_comp (hK : IsCommensurated K) (hh : h ∈ Hecke ℂ K) (hx : x ∈ fixed ρ K)
    (β : V →ₗ[ℂ] V →ₛₗ[starRingEnd ℂ] ℂ) (hβ : ∀ v w, β w v = starRingEnd ℂ (β v w))
    (hi : ∀ g v w, β (ρ g v) (ρ g w) = β v w) (θ : G →* G) (hθ : ∀ k ∈ K, θ k ∈ K)
    (hr : ∀ g, starRingEnd ℂ (h g) = h g)
    (ht : ∀ g, h g ≠ 0 → ∃ a ∈ K, ∃ b ∈ K, ∃ t, θ t = t⁻¹ ∧ g = a * t * b) :
    β (heckeVec (ρ.comp θ) K h x) x = starRingEnd ℂ (β (heckeVec ρ K h x) x) := by
  have hf := GlobalTheory.LGrp.mem_fixed.1 hx
  have bi : ∀ a ∈ K, ∀ b ∈ K, ∀ t, β (ρ (a * t * b) x) x = β (ρ t x) x := fun a ha b hb t => by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hf b hb]
    exact (congrArg (β _) (hf a ha).symm).trans (hi a _ _)
  have inv : ∀ t, β (ρ t⁻¹ x) x = starRingEnd ℂ (β (ρ t x) x) := fun t => by
    rw [← hβ, ← hi t]; simp
  have e1 := (β.flip x).toAddMonoidHom.map_finsum (finite_heckeVec hK hh (ρ.comp θ) x)
  have e2 := ((starRingEnd ℂ).toAddMonoidHom.comp (β.flip x).toAddMonoidHom).map_finsum (finite_heckeVec hK hh ρ x)
  refine e1.trans (Eq.trans (finsum_congr fun c => ?_) e2.symm)
  change β (h c.out • ρ (θ c.out) x) x = starRingEnd ℂ (β (h c.out • ρ c.out x) x)
  rw [map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, hr]
  by_cases h0 : h c.out = 0
  · simp [h0]
  obtain ⟨a, ha, b, hb, t, htt, e⟩ := ht _ h0
  congr 1
  rw [e, map_mul θ, map_mul θ, bi _ (hθ a ha) _ (hθ b hb), bi _ ha _ hb, htt, inv]

end General

theorem map_star_eq_map_inv (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V : Type)
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (x : V)
    (B : Multiset ℂˣ) (hU : GlobalTheory.LGrp.IsUnitarisable ρ) (hx : IsSatVecGL w ρ x B) :
    B.map star = B.map (·⁻¹) := by
  classical
  obtain ⟨β, hβ, hpos, hi⟩ := hU
  let c := RingEquiv.refl (w.adicCompletion E)
  have hc : ∀ a, Valued.v (c a) = Valued.v a := fun _ => rfl
  have hx' := isSatVecGL_invT c hc rfl hx
  have hK := mem_iff_invT (n := n) c (map_mem_Ov_iff c hc)
  obtain ⟨p, hp⟩ := exists_isUnifV w
  obtain ⟨ϖ, rfl⟩ : ∃ ϖ : (w.adicCompletion E)ˣ, ϖ = p :=
    ⟨Units.mk0 p fun e => by simp [IsUnifV, e] at hp, rfl⟩
  have hne : β x x ≠ 0 := fun h0 => by simpa [h0] using hpos x hx.1
  refine eq_of_satEig_eq (qV_ne_zero w) (by simpa using hx.2.2.1) hx'.2.2.1 fun j hj => ?_
  have key := form_heckeVec_comp (Final.GLintComm E w n) (Tj_mem_hecke hp j) hx.2.1 β hβ hi
    (invT c n).symm.toMonoidHom (fun k hk => (hK _).2 (by simpa using hk))
    (fun g => by rw [Tj_apply]; split_ifs <;> simp)
    (fun g hg => by
      rw [Tj_apply] at hg
      obtain ⟨a, ha, b, hb, e⟩ : ∃ a ∈ GLint (Fin n) (Ov E w), ∃ b ∈ GLint (Fin n) (Ov E w),
          g = a * dGL n ϖ j * b := by
        by_contra hn
        exact hg (if_neg hn)
      exact ⟨a, ha, b, hb, _, (invT c n).symm_apply_eq.2 (invT_dGL c ϖ j).symm, e⟩)
  rw [hx'.2.2.2 _ hp j hj, hx.2.2.2 _ hp j hj, map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply,
    smul_eq_mul, smul_eq_mul, map_mul, ← hβ] at key
  rw [satEig_map_star]
  exact (mul_right_cancel₀ hne key).symm

end GlobalTheory.LFun.UnitaryParam

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceWeilRepLatticeVacuumCharacter
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VecInv

open GlobalTheory.SplitScalar GlobalTheory.SplitHecke in

theorem om_latVac_split : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ e, IsSplitIdem D e → ∀ g h, Formalism.L2.Theta.SuppAt e S g → Formalism.L2.Theta.SuppAt e T h → (∀ u, u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ↔ actO S T g h u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)) → ∀ x y, IsDetAt e S g x → IsDetAt e T h y → ∀ f, IsThetaFunO ψ S T f → IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f → om (g, h) f = ((splitFacO χS χT x y : Circle) : ℂ) • f := by
  intro D ψ S T ΛS ΛT χS χT om hW hS hT e he g h hg hh hlat x y hx hy f hf hv

  set Λ := (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) with hΛ

  obtain ⟨hdual, -, -⟩ := GlobalTheory.T.self_dual_lattice_pairing_dual D ψ S T ΛS ΛT hW.std hS hT
  have hdd : ∀ u ∈ Λ, ∀ u' ∈ Λ, ψ (symplO S T u u') = 1 := fun u hu u' hu' =>
    (hdual u (GlobalTheory.SplitScalar.latO_fin hu)).1 hu u' hu'
  have he' : IsSplitIdem D (cA D e) := GlobalTheory.SplitScalar.isSplitIdem_conj he
  have hst : ∀ u ∈ Λ, cA D e • u ∈ Λ := GlobalTheory.SplitScalar.idem_smul_mem he'.1
  have hst' : ∀ u ∈ Λ, cA D (cA D e) • u ∈ Λ := by
    rw [GlobalTheory.DualPairCheck.cA_cA]; exact GlobalTheory.SplitScalar.idem_smul_mem he.1

  have hd : ∀ y, IsHalf e y → y ∉ Λ → ∃ l ∈ Λ, IsHalf (cA D e) l ∧ ψ (symplO S T l y) ≠ 1 :=
    fun y hy hyn => GlobalTheory.SplitScalar.exists_dual_half he hdual hst hy hyn
  have hd' : ∀ y, IsHalf (cA D e) y → y ∉ Λ → ∃ l ∈ Λ, IsHalf e l ∧ ψ (symplO S T l y) ≠ 1 := by
    intro y hy hyn
    have hex := GlobalTheory.SplitScalar.exists_dual_half he' hdual hst' hy hyn
    rwa [GlobalTheory.DualPairCheck.cA_cA] at hex

  have hback : ∀ w, actO S T g h (actO S T g⁻¹ h⁻¹ w) = w := fun w => by
    simpa using GlobalTheory.SplitHecke.actO_inv_actO g⁻¹ h⁻¹ w
  have hmem : ∀ w, actO S T g⁻¹ h⁻¹ w ∈ Λ ↔ w ∈ Λ := fun w => by
    have hw := hlat (actO S T g⁻¹ h⁻¹ w)
    rwa [hback] at hw

  have hR : ∀ u ∈ ({0} : Finset (WO S T)), actO S T g⁻¹ h⁻¹ u ∈ Λ ∧ IsHalf e u := by
    intro u hu
    rw [Finset.mem_singleton] at hu
    subst hu
    exact ⟨(hmem 0).2 (zero_mem _), GlobalTheory.SplitScalar.isHalf_zero e⟩
  have hRu : ∀ w, actO S T g⁻¹ h⁻¹ w ∈ Λ → IsHalf e w → ∃! v, v ∈ ({0} : Finset (WO S T)) ∧ w - v ∈ Λ := by
    intro w hw _
    refine ⟨0, ⟨Finset.mem_singleton_self _, by simpa using (hmem w).1 hw⟩, ?_⟩
    rintro v ⟨hv0, -⟩
    exact Finset.mem_singleton.1 hv0
  have hle : ∀ w ∈ Λ, IsHalf e w → actO S T g⁻¹ h⁻¹ w ∈ Λ := fun w hw _ => (hmem w).2 hw
  obtain ⟨r, hr, hom⟩ := GlobalTheory.SplitHecke.om_eq_smul_sum hW he hdd hd hd' hg hh hx hy hR hRu hle
  have key : om (g, h) f = ((r : ℂ) * (splitFacO χS χT x y : ℂ)) • f := by
    have hk := hom f hf (fun u hu hue => hv.2 e he u hu hue) (fun u hu hue => hv.2 (cA D e) he' u hu hue)
    rwa [Finset.sum_singleton, GlobalTheory.WeilVacMove.heisO_zero] at hk

  by_cases hf0 : f = 0
  · subst hf0
    simp
  obtain ⟨htop, hlc, hsc, ht2, hdisc, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI := htop
  haveI := hlc
  haveI := hsc
  haveI := ht2
  haveI := hdisc
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨⟨μ, 𝓕, hμ, h𝓕, h1⟩, hN⟩ :=
    GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact _ (ratL T S) K hK hcov
  haveI := hμ
  have hper := GlobalTheory.WeilVacMove.norm_periodic hW.std hf
  obtain ⟨N, hNf⟩ := hN f hf.cont hper
  obtain ⟨-, -, hI, -⟩ := hNf μ 𝓕 hμ h𝓕
  have hu := hW.om_unit μ 𝓕 hμ h𝓕 (g, h) f hf
  rw [key] at hu
  have hpt : ∀ w, ‖(((r : ℂ) * (splitFacO χS χT x y : ℂ)) • f) w‖ₑ ^ 2 =
      ‖(r : ℂ) * (splitFacO χS χT x y : ℂ)‖ₑ ^ 2 * ‖f w‖ₑ ^ 2 := fun w => by
    rw [Pi.smul_apply, smul_eq_mul, enorm_mul (a := (r : ℂ) * (splitFacO χS χT x y : ℂ)), mul_pow]
  simp_rw [hpt] at hu
  rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top enorm_ne_top), hI, h1, one_mul] at hu
  have hN0 : (N : ENNReal) ≠ 0 := by
    intro hz
    apply hf0
    have h0 : ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ = 0 := by rw [hI, hz, mul_zero]
    rw [lintegral_eq_zero_iff' (hf.cont.measurable.enorm.pow_const 2).aemeasurable] at h0
    apply GlobalTheory.WeilVacMove.eq_zero_of_ae_fundamentalDomain (ratL T S) μ 𝓕 h𝓕 f hf.cont hper
    filter_upwards [h0] with w hw
    simpa using hw
  have hnorm : ‖(r : ℂ) * (splitFacO χS χT x y : ℂ)‖ = r := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    have hs1 : ‖(splitFacO χS χT x y : ℂ)‖ = 1 := by
      first
        | exact Circle.norm_coe _
        | exact Circle.abs_coe _
        | simp
    rw [hs1, mul_one]
  have hr1 : r = 1 := by
    have hc : ‖(r : ℂ) * (splitFacO χS χT x y : ℂ)‖₊ ^ 2 = 1 := by
      rw [enorm_eq_nnnorm] at hu
      have hN0' : N ≠ 0 := fun hz => hN0 (by rw [hz]; rfl)
      have h2 : ‖(r : ℂ) * (splitFacO χS χT x y : ℂ)‖₊ ^ 2 * N = 1 * N := by
        rw [one_mul]; exact_mod_cast hu
      exact mul_right_cancel₀ hN0' h2
    have hc' : ‖(r : ℂ) * (splitFacO χS χT x y : ℂ)‖ ^ 2 = 1 := by
      rw [← coe_nnnorm]
      exact_mod_cast hc
    rw [hnorm] at hc'
    nlinarith
  rw [key, hr1]
  simp

end GlobalTheory.VecInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoPlaceComponentsFiniteAdelicUnitaryStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_placeComponents_finiteAdelicUnitary : ∀ (D : D7) (V : HSp D) (g : GA D V), g ∈ GfC V → ∀ (ε : HeightOneSpectrum (𝓞 D.host.F) → AF D.host.F), (∀ v, IsPlaceIdem D v (ε v)) → ∀ gs : Finset (HeightOneSpectrum (𝓞 D.host.F)) → GA D V, (∀ A, Formalism.L2.Theta.mt V (gs A) = algebraMap (AF D.host.F) (AE D) (∑ v ∈ A, ε v) • Formalism.L2.Theta.mt V g + (1 - algebraMap (AF D.host.F) (AE D) (∑ v ∈ A, ε v)) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))) → Filter.Tendsto gs Filter.atTop (nhds g) := by
  first | exact @GlobalTheory.PlaceLimit.tendsto_components | exact GlobalTheory.PlaceLimit.tendsto_components | (intros; apply GlobalTheory.PlaceLimit.tendsto_components <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThPDatumEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftLevel

variable {D : D7}

def thPDatum (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ)
    (e : AE D) : WO S T → ℂ :=
  fun x => if IsHalf (cA D e) x ∧ IsIntM (frMapAdj S T βS βT x) then
    omegaK Pg (fun PP => redM PP (frMapAdj S T βS βT x)) *
      omegaQ Q T.rank ξ (-1) (fun PP => redM PP (frMapAdj S T βS βT x))
    else 0

def indL {S T : HSp D} (L : AddSubgroup (WO S T)) : WO S T → ℂ := fun x => if x ∈ L then 1 else 0

def partAt {S T : HSp D} (a : AE D) (w : WO S T) : WO S T := w.map fun z => a * z

abbrev LvCls {S T : HSp D} (C : Ctx S T) (Lv : GlobalTheory.SW.Level C.X) : Type :=
  tens (stdL D.host.E S.rank) ((Ideal.span {2} * conjI Lv.𝔪) • C.X.Λ) ⧸
    (tens (stdL D.host.E S.rank) ((Ideal.span {2} * conjI Lv.𝔪 * Lv.𝔪) • C.X.Λ)).addSubgroupOf _

end GlobalTheory.LiftLevel

end
end

