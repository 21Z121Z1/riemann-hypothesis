import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0400
import GroundTheory.AutomorphicForms.HarishChandraCentre.VermaCoordEqZeroOfMemNPlusU
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0403
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0042
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0032
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0384
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0304
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralStrictlyDominantExists
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0396
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0352
import GroundTheory.AutomorphicForms.AnisotropicHeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemEqnSetOmegaCoeff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0397
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContractingDoubleCosetVolumeBound
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
import GroundTheory.AutomorphicForms.SupercuspidalCoefficients

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActEqZeroOfMem
section
set_option maxSynthPendingDepth 1

noncomputable section

open GroundTheory.Automorphic.HarishChandra

namespace GlobalTheory.CompanionTheory.PresRho

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ}

theorem rhoVec_sub {i j : Fin n} (h : (j : ℕ) = i + 1) : rhoVec n i - rhoVec n j = 1 := by
  have : (j : ℂ) = (i : ℂ) + 1 := by exact_mod_cast h
  simp only [rhoVec, this]; ring

def sqSpan (n : ℕ) : Submodule ℂ (U n) :=
  Submodule.span ℂ {x | ∃ (u : U n) (i j : Fin n), (j : ℕ) = i + 1 ∧ u * e (j, i) ^ 2 = x}

def Jp (n : ℕ) : Submodule ℂ (U n) := vermaIdeal (rhoVec n) ⊔ sqSpan n

theorem vermaIdeal_le_Jp : vermaIdeal (rhoVec n) ≤ Jp n := le_sup_left

theorem sqSpan_le_Jp : sqSpan n ≤ Jp n := le_sup_right

theorem mul_mem_sqSpan (v : U n) {x : U n} (hx : x ∈ sqSpan n) : v * x ∈ sqSpan n := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, i, j, hij, rfl⟩ := hx
    exact Submodule.subset_span ⟨v * u, i, j, hij, mul_assoc _ _ _⟩
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hx

theorem mul_mem_Jp (v : U n) {x : U n} (hx : x ∈ Jp n) : v * x ∈ Jp n := by
  obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.1 hx
  rw [mul_add]
  exact Submodule.add_mem _ (vermaIdeal_le_Jp (mul_mem_vermaIdeal _ v hy))
    (sqSpan_le_Jp (mul_mem_sqSpan v hw))

theorem mul_sq_mem_Jp (u : U n) {i j : Fin n} (hij : (j : ℕ) = i + 1) :
    u * e (j, i) ^ 2 ∈ Jp n :=
  sqSpan_le_Jp (Submodule.subset_span ⟨u, i, j, hij, rfl⟩)

def IsAdW (μ : Fin n → ℤ) (x : U n) : Prop :=
  ∀ k, e (k, k) * x - x * e (k, k) = (μ k : ℂ) • x

def LowExp (m : Fin n × Fin n →₀ ℕ) : Prop := ∀ a ∈ m.support, IsLower a

def lowSpan (n : ℕ) : Submodule ℂ (U n) :=
  Submodule.span ℂ {x | ∃ m : Fin n × Fin n →₀ ℕ, LowExp m ∧ canon m = x}

def lowSpanW (μ : Fin n → ℤ) : Submodule ℂ (U n) :=
  Submodule.span ℂ {x | ∃ m : Fin n × Fin n →₀ ℕ, LowExp m ∧ wt m = μ ∧ canon m = x}

def casC (τ : Fin n → ℂ) : ℂ :=
  ∑ a, τ a ^ 2 + ∑ a, ∑ b, if a < b then τ a - τ b else 0

def ht (μ : Fin n → ℤ) : ℤ := ∑ k : Fin n, ((n : ℤ) - 1 - 2 * (k : ℕ)) * μ k

theorem exists_act {A : Type} [AddCommGroup A] [Module ℂ A] (G : Fin n → Fin n → Module.End ℂ A)
    (h : Formalism.REAL.GlRel G) : ∃ φ : U n →ₐ[ℂ] Module.End ℂ A, ∀ i j, φ (e (i, j)) = G i j := by
  let L : gl n →ₗ[ℂ] Module.End ℂ A :=
    { toFun := fun X => ∑ a : Fin n × Fin n, X a.1 a.2 • G a.1 a.2
      map_add' := fun X Y => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun r X => by simp [Finset.smul_sum, smul_smul] }
  have hL : ∀ a : Fin n × Fin n, L (E a) = G a.1 a.2 := by
    intro a
    show ∑ b : Fin n × Fin n, (E a) b.1 b.2 • G b.1 b.2 = _
    rw [Finset.sum_eq_single a]
    · simp [E]
    · intro b _ hb
      have : ¬ (a.1 = b.1 ∧ a.2 = b.2) := fun h => hb (Prod.ext h.1 h.2).symm
      simp [E, Matrix.single_apply, this]
    · simp
  have hE : ∀ a b : Fin n × Fin n, L ⁅E a, E b⁆ = ⁅L (E a), L (E b)⁆ := by
    intro a b
    rw [LieRing.of_associative_ring_bracket, LieRing.of_associative_ring_bracket, E_mul_sub_mul,
      hL, hL, h, map_sub, apply_ite L, apply_ite L, hL, hL, map_zero]
  let ρ : gl n →ₗ⁅ℂ⁆ Module.End ℂ A :=
    { L with
      map_lie' := fun {X Y} => by
        show L ⁅X, Y⁆ = ⁅L X, L Y⁆
        rw [eq_sum_E X, eq_sum_E Y]
        simp only [sum_lie, lie_sum, smul_lie, lie_smul, map_sum, map_smul, hE] }
  refine ⟨UniversalEnvelopingAlgebra.lift ℂ ρ, fun i j => ?_⟩
  rw [e, UniversalEnvelopingAlgebra.lift_ι_apply]
  exact hL (i, j)

theorem act_word {A : Type} [AddCommGroup A] [Module ℂ A] {G : Fin n → Fin n → Module.End ℂ A}
    (φ : U n →ₐ[ℂ] Module.End ℂ A) (hφ : ∀ i j, φ (e (i, j)) = G i j)
    (l : List (Fin n × Fin n)) : φ (word l) = (l.map fun p => G p.1 p.2).prod := by
  induction l with
  | nil => simp
  | cons a l ih => rw [word_cons, map_mul, ih, List.map_cons, List.prod_cons, hφ]

theorem glRel_e (n : ℕ) : Formalism.REAL.GlRel (fun i j : Fin n => e (i, j)) :=
  fun a b c d => e_mul_sub_mul (a, b) (c, d)

theorem IsAdW.e_mul {μ : Fin n → ℤ} {x : U n} (hx : IsAdW μ x) (a : Fin n × Fin n) :
    IsAdW (fun k => μ k + rootAt a k) (e a * x) := by
  intro k
  have h1 := e_diag_mul_sub k a
  have h2 := hx k
  have : e (k, k) * (e a * x) - e a * x * e (k, k) =
      (e (k, k) * e a - e a * e (k, k)) * x + e a * (e (k, k) * x - x * e (k, k)) := by
    noncomm_ring
  rw [this, h1, h2, smul_mul_assoc, mul_smul_comm, ← add_smul]
  push_cast; ring_nf

theorem ht_rootAt (a : Fin n × Fin n) :
    ht (rootAt a) = 2 * ((a.2 : ℕ) : ℤ) - 2 * ((a.1 : ℕ) : ℤ) := by
  simp only [ht, rootAt, mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

theorem ht_add_rootAt (μ : Fin n → ℤ) (a : Fin n × Fin n) :
    ht (fun k => μ k + rootAt a k) = ht μ + ht (rootAt a) := by
  simp only [ht, mul_add, Finset.sum_add_distrib]

theorem ht_wt (m : Fin n × Fin n →₀ ℕ) :
    ht (wt m) = m.sum fun a c => (c : ℤ) * ht (rootAt a) := by
  simp only [ht, wt, Finsupp.sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem ht_wt_nonpos {m : Fin n × Fin n →₀ ℕ} (hm : LowExp m) : ht (wt m) ≤ 0 := by
  rw [ht_wt]
  refine Finset.sum_nonpos fun a ha => ?_
  have h : (a.2 : ℕ) < a.1 := hm a ha
  show (m a : ℤ) * ht (rootAt a) ≤ 0
  rw [ht_rootAt]
  have : (0 : ℤ) ≤ (m a : ℤ) := by positivity
  nlinarith

theorem act_eq_zero_of_mem {A : Type} [AddCommGroup A] [Module ℂ A]
    (φ : U n →ₐ[ℂ] Module.End ℂ A) (t : A) (hd : ∀ k, φ (e (k, k)) t = rhoVec n k • t)
    (hu : ∀ a : Fin n × Fin n, IsUpper a → φ (e a) t = 0) {x : U n}
    (hx : x ∈ vermaIdeal (rhoVec n)) : φ x t = 0 := by
  obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.1 hx
  clear hx
  have h1 : φ y t = 0 := by
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, a, ha, rfl⟩ := hx
      simp [hu a ha]
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul r x _ hx => simp [hx]
  have h2 : φ w t = 0 := by
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, k, rfl⟩ := hx
      simp [hd k, Algebra.algebraMap_eq_smul_one]
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul r x _ hx => simp [hx]
  simp [h1, h2]

end GlobalTheory.CompanionTheory.PresRho
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AnnSubsetOfMemNhds
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier ValuativeRel
open scoped Topology

namespace GlobalTheory.CompanionTheory.MirFourier

theorem ann_subset_of_mem_nhds {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (hψ : ψ ≠ 1) (n : ℕ)
    {S : Set (Multiplicative (Fin n → k))} (hS : S ∈ 𝓝 (1 : Multiplicative (Fin n → k))) :
    ∃ t : kˣ, (ann ψ n t : Set (Multiplicative (Fin n → k))) ⊆ S := by
  obtain ⟨y, hy⟩ : ∃ y, ψ y ≠ 1 := by
    by_contra h
    push Not at h
    exact hψ (by ext a; simp [h a])
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hy (AddChar.map_zero_eq_one ψ)
  have hS' : {v : Fin n → k | Multiplicative.ofAdd v ∈ S} ∈ 𝓝 (0 : Fin n → k) := hS
  obtain ⟨s, hs⟩ := FourierPi.exists_box_subset hS'
  refine ⟨Units.mk0 y hy0 * s⁻¹, fun x hx => ?_⟩
  have hbox : x.toAdd ∈ FourierPi.box (Fin n) s := by
    intro i _
    show valuation k (x.toAdd i) ≤ valuation k (s : k)
    by_contra hlt
    have hlt' : valuation k (s : k) < valuation k (x.toAdd i) := not_le.mp hlt
    have hxi : x.toAdd i ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hlt'
      exact not_lt_zero hlt'
    have hmem : Multiplicative.ofAdd (Pi.single i (y / x.toAdd i) : Fin n → k) ∈ polyBall n
        (Units.mk0 y hy0 * s⁻¹) := by
      intro j
      by_cases hj : j = i
      · subst hj
        show valuation k ((Pi.single j (y / x.toAdd j) : Fin n → k) j) ≤
          valuation k ((Units.mk0 y hy0 * s⁻¹ : kˣ) : k)
        have hs0 : 0 < valuation k (s : k) :=
          zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr s.ne_zero)
        rw [Pi.single_eq_same, map_div₀, Units.val_mul, map_mul, Units.val_mk0,
          Units.val_inv_eq_inv_val, map_inv₀, div_eq_mul_inv]
        exact mul_le_mul_right ((inv_le_inv₀ (hs0.trans hlt') hs0).mpr hlt'.le) _
      · simp [Pi.single_eq_of_ne hj, cball]
    have h1 := hx _ hmem
    rw [toAdd_ofAdd, single_dotProduct, div_mul_cancel₀ _ hxi] at h1
    exact hy h1
  exact hs hbox

end GlobalTheory.CompanionTheory.MirFourier

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CPoly
section
noncomputable section

open Matrix Finset

namespace GlobalTheory.CompanionTheory.RealCount.Tope

variable {n : ℕ}

abbrev LP (n : ℕ) := AddMonoidAlgebra ℂ (Fin n → ℤ)

def chr (z : Fin n → ℂˣ) : Multiplicative (Fin n → ℤ) →* ℂ where
  toFun μ := ∏ a, ((z a ^ (Multiplicative.toAdd μ a) : ℂˣ) : ℂ)
  map_one' := by simp
  map_mul' μ ν := by
    simp only [toAdd_mul, Pi.add_apply, _root_.zpow_add, Units.val_mul, Finset.prod_mul_distrib]

def evL (z : Fin n → ℂˣ) : LP n →ₐ[ℂ] ℂ := AddMonoidAlgebra.lift ℂ ℂ (Fin n → ℤ) (chr z)

def altL (m : Fin n → ℤ) : LP n :=
  ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) • AddMonoidAlgebra.single (fun i => m (σ i)) (1 : ℂ)

def delZ (n : ℕ) : Fin n → ℤ := fun j => ((n - 1 - (j : ℕ) : ℕ) : ℤ)

def pPL (n : ℕ) : LP n :=
  ∏ a : Fin n, ∏ b : Fin n, (1 + AddMonoidAlgebra.single (Pi.single a 1 - Pi.single b 1 : Fin n → ℤ) (1 : ℂ))

def frL (n : ℕ) : LP n →ₐ[ℂ] LP n :=
  AddMonoidAlgebra.mapDomainAlgHom ℂ ℂ (2 • AddMonoidHom.id (Fin n → ℤ))

def cPoly (s : Finset (Fin n → ℤ)) (c : (Fin n → ℤ) → ℂ) : LP n :=
  ∑ μ ∈ s, AddMonoidAlgebra.single μ (c μ)

end GlobalTheory.CompanionTheory.RealCount.Tope
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralCharacterNormEqPow
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

namespace GlobalTheory.CompanionTheory.CentralExp

theorem continuous_scalarGL (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) :
    Continuous (Matrix.GeneralLinearGroup.scalar (Fin n) : kˣ →* GL (Fin n) k) := by
  have hs : Continuous (fun a : k => Matrix.scalar (Fin n) a) := by
    have : (fun a : k => Matrix.scalar (Fin n) a) = fun a => Matrix.diagonal (fun _ => a) := by
      funext a; rfl
    rw [this]
    exact Continuous.matrix_diagonal (continuous_pi fun _ => continuous_id)
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact hs.comp Units.continuous_val
  · exact hs.comp (Units.continuous_val.comp continuous_inv)

theorem norm_scalarBy_eq_nabs_rpow : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x : IrrGL k), 0 < x.1 → ∃ s : ℝ, ∀ (t : kˣ) (c : ℂ), Zl.ScalarBy x t c → ‖c‖ = nabs k t ^ ((x.1 : ℝ) * s) := by
  intro k _ _ _ _ x hx
  have hirr := x.2.rep.irr
  obtain ⟨v, hv⟩ : ∃ v : x.2.rep.V, v ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    haveI : Subsingleton x.2.rep.V := ⟨fun a b => by rw [hcon a, hcon b]⟩
    obtain ⟨a, b, hab⟩ := exists_pair_ne (Subrepresentation x.rep)
    exact hab (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))
  have huniq : ∀ (t : kˣ) (c c' : ℂ), Zl.ScalarBy x t c → Zl.ScalarBy x t c' → c = c' := by
    intro t c c' h h'
    exact smul_left_injective ℂ hv ((h v).symm.trans (h' v))
  choose f hf using GlobalTheory.T.central_character_exists k x
  have hmul : ∀ a b : kˣ, f (a * b) = f a * f b := by
    intro a b
    refine huniq (a * b) _ _ (hf _) fun w => ?_
    rw [map_mul, map_mul, Module.End.mul_apply, hf b w, map_smul, hf a w, smul_smul, mul_comm]
  have hone : f 1 = 1 := by
    refine huniq 1 _ _ (hf _) fun w => ?_
    simp
  let χ₀ : kˣ →* ℂ := { toFun := f, map_one' := hone, map_mul' := hmul }
  let χ : kˣ →* ℂˣ := χ₀.toHomUnits
  have hχ : ∀ t, ((χ t : ℂˣ) : ℂ) = f t := fun t => rfl
  have hsm : IsSmoothChar χ := by
    have hset : (χ.ker : Set kˣ) = (Matrix.GeneralLinearGroup.scalar (Fin x.1) : kˣ →* GL (Fin x.1) k) ⁻¹'
        {g | x.rep g v = v} := by
      ext t
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_setOf_eq]
      rw [hf t v]
      constructor
      · intro h
        have : f t = 1 := by rw [← hχ, h]; rfl
        rw [this, one_smul]
      · intro h
        have : f t = 1 := smul_left_injective ℂ hv (by simpa using h)
        exact Units.ext (by rw [hχ, this]; rfl)
    show IsOpen (χ.ker : Set kˣ)
    rw [hset]
    exact (x.2.rep.smooth v).preimage (continuous_scalarGL k x.1)
  obtain ⟨s, hs⟩ := GlobalTheory.SmoothCharNorm.norm_eq_nabs_rpow k χ hsm
  have hn : (x.1 : ℝ) ≠ 0 := by exact_mod_cast hx.ne'
  refine ⟨s / x.1, fun t c hc => ?_⟩
  rw [huniq t c (f t) hc (hf t), ← hχ, hs t, mul_div_cancel₀ _ hn]

end GlobalTheory.CompanionTheory.CentralExp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralStrictlyDominantExistsStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.central_strictly_dominant_exists : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (J : Subgroup (GL (Fin N) k)), IsOpen (J : Set (GL (Fin N) k)) → IsCompact (J : Set (GL (Fin N) k)) → HasIwahoriFact k N J d hd → (∀ a, 0 < d a) → ∃ a : Levi k (Bl d), (∀ x : Levi k (Bl d), a * x = x * a) ∧ IsStrictlyDominant k N J d hd a ∧ ∀ U : Set (GL (Fin N) k), IsOpen U → (1 : GL (Fin N) k) ∈ U → ∃ j : ℕ, ∀ y ∈ KNl k N J d hd, (leviEmb k (stdBlocks d hd) a ^ j)⁻¹ * y * leviEmb k (stdBlocks d hd) a ^ j ∈ U := by
  first | exact @GlobalTheory.CompanionTheory.CentralDom.exists_central_strictlyDominant | exact GlobalTheory.CompanionTheory.CentralDom.exists_central_strictlyDominant | (intros; apply GlobalTheory.CompanionTheory.CentralDom.exists_central_strictlyDominant <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralizerCompactReductionStatement
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralizer_compact_reduction : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (d : GL (Fin n) E) (C : Set (GA E n)), IsCompact C → ∃ C' : Set (GA E n), IsCompact C' ∧ ∀ t ∈ adCent d, t ∈ ((ratGL E n).range : Set (GA E n)) * C → t ∈ (ratCent d : Set (GA E n)) * C' := by
  first | exact @GlobalTheory.CompanionTheory.TorusCh.exists_isCompact_ratCent_mul | exact GlobalTheory.CompanionTheory.TorusCh.exists_isCompact_ratCent_mul | (intros; apply GlobalTheory.CompanionTheory.TorusCh.exists_isCompact_ratCent_mul <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChernIntegralPresentationTransfer
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open GlobalTheory GlobalTheory.Points GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.Published.ArDegreeModel GlobalTheory.ChartGlue GlobalTheory.ProjVar.Var

namespace GlobalTheory.CompanionTheory.ChernTransport

section Chart

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
  {B B' : LB X} {φ : Weight p σ B} {ψ : Weight p σ B'}

theorem hess_eq_of_unit (c : AlgChart p σ D) (h : φ.IsCInf) {y : CxPts p σ} (hy : y ∈ c.e.source)
    {i : B.ι} {j : B'.ι} (hi : y ∈ ptsIn p σ (B.U i)) (hj : y ∈ ptsIn p σ (B'.U j))
    (a : Γ(X, B.U i ⊓ B'.U j)ˣ)
    (ha : ∀ z ∈ ptsIn p σ (B.U i ⊓ B'.U j),
      ψ.φ j z = φ.φ i z + Real.log (‖ev p σ _ a.val z‖ ^ 2)) :
    c.hess ψ j y = c.hess φ i y := by
  have ho := isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (B.U i ⊓ B'.U j))
  have hm := mem_over c.e hy (mem_ptsIn_inf.2 ⟨hi, hj⟩)
  have hg := c.holo _ a.val
  have h0 : ∀ v ∈ c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ (B.U i ⊓ B'.U j),
      (ev p σ _ a.val ∘ c.e.symm) v ≠ 0 := fun v hv => ev_ne_zero hv.2 a.isUnit
  have e := ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul ho
    ((contDiffOn_chart (h i) c).mono fun v hv => ⟨hv.1, (mem_ptsIn_inf.1 hv.2).1⟩)
    (contDiffOn_log_normSq ho hg h0) 1 hm
  have e₀ : cHess D (fun w => ((Real.log (‖(ev p σ _ a.val ∘ c.e.symm) w‖ ^ 2) : ℝ) : ℂ))
      (c.e y) = 0 := by
    ext s t
    exact ReciprocityTheory.L2DbarEstimates.Y.cmpa_hess_log ho hm hg h0 s t
  rw [e₀, smul_zero, add_zero] at e
  refine Eq.trans (ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr ?_) e
  filter_upwards [ho.mem_nhds hm] with v hv
  rw [ha _ hv.2, one_mul]
  rfl

theorem chartMeas_congr_source {n : ℕ} {T : Type} [TopologicalSpace T] [MeasurableSpace T]
    (e : OpenPartialHomeomorph T (V n)) {ρ ρ' : T → ENNReal} (h : ∀ y ∈ e.source, ρ y = ρ' y) :
    chartMeas e ρ = chartMeas e ρ' := by
  have hae : (ρ ∘ e.symm) =ᵐ[volume.restrict e.target] (ρ' ∘ e.symm) :=
    (ae_restrict_iff' e.open_target.measurableSet).2
      (Filter.Eventually.of_forall fun v hv => h _ (e.map_target hv))
  show Measure.map e.symm ((volume.restrict e.target).withDensity (ρ ∘ e.symm)) =
    Measure.map e.symm ((volume.restrict e.target).withDensity (ρ' ∘ e.symm))
  rw [withDensity_congr_ae hae]

theorem chernPart_eq_of_chernDens (h : ∀ (c : AlgChart p σ D), ∀ y ∈ c.e.source,
    c.chernDens ψ y = c.chernDens φ y) (ε : ℤˣ) : ψ.chernPart D ε = φ.chernPart D ε := by
  show (⨆ c : AlgChart p σ D, chartMeas c.e fun y => ENNReal.ofReal (↑↑ε * c.chernDens ψ y)) =
    ⨆ c : AlgChart p σ D, chartMeas c.e fun y => ENNReal.ofReal (↑↑ε * c.chernDens φ y)
  exact iSup_congr fun c => chartMeas_congr_source _ fun y hy => by rw [h c y hy]

end Chart

variable {Y : Var ℂ} {Δ : Y.Dv} {L L' : LB Y.X} {r : L.ι → Y.Fnˣ} {r' : L'.ι → Y.Fnˣ}

theorem exists_unit_tv (hp : Presents Δ L r) (hp' : Presents Δ L' r') (i : L.ι) (j : L'.ι) :
    ∃ a : Γ(Y.X, L.U i ⊓ L'.U j)ˣ, ∀ z ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i ⊓ L'.U j),
      tv (σ := RingHom.id ℂ) (r i) (r' j) z = ev Y.str (RingHom.id ℂ) _ a.val z := by
  obtain ⟨a, ha⟩ := exists_unit_fnOf_eq (U := L.U i ⊓ L'.U j)
    (f := (r' j : Y.Fn) / (r i : Y.Fn))
    fun x hx => (hp.isEqn i x hx.1).iff_unitAt.1 (hp'.isEqn j x hx.2)
  refine ⟨a, fun z hz => ?_⟩
  have hb := mem_ptsIn_iff.1 hz
  rw [tv, ← ha (gen_mem hb), val_cx_fnOf hb]

theorem exists_transport (hp : Presents Δ L r) (hp' : Presents Δ L' r')
    (φ : Weight Y.str (RingHom.id ℂ) L) (hφ : φ.IsCInf) :
    ∃ ψ : Weight Y.str (RingHom.id ℂ) L', ψ.IsCInf ∧
      ψ.chernInt Y.dim Set.univ (fun _ => 1) = φ.chernInt Y.dim Set.univ (fun _ => 1) := by
  have hs : mSmooth Y (RingHom.id ℂ) Δ (ofWeight Y (RingHom.id ℂ) Δ L r hp φ) :=
    (mSmooth_ofWeight_iff hp φ).2 ((Weight.isCInf_iff_isSmooth (Y.an _)).1 hφ)
  set m := ofWeight Y (RingHom.id ℂ) Δ L r hp φ with hm
  let ψ : Weight Y.str (RingHom.id ℂ) L' := m.toWeight hs.posSet_eq hp'
  have hψ : ψ.IsCInf := (Weight.isCInf_iff_isSmooth (Y.an _)).2 (hs.isSmooth_toWeight hp')
  have key : ∀ (i : L.ι) (j : L'.ι) (a : Γ(Y.X, L.U i ⊓ L'.U j)ˣ),
      (∀ z ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i ⊓ L'.U j),
        tv (σ := RingHom.id ℂ) (r i) (r' j) z = ev Y.str (RingHom.id ℂ) _ a.val z) →
      ∀ z ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i ⊓ L'.U j),
        ψ.φ j z = φ.φ i z + Real.log (‖ev Y.str (RingHom.id ℂ) _ a.val z‖ ^ 2) := by
    intro i j a ha z hz
    obtain ⟨hi, hj⟩ := mem_ptsIn_inf.1 hz
    have hw : m.wt (r i) z = φ.φ i z := by
      rw [Met.wt, hm, ofWeight_h hp φ hi, Real.log_exp, neg_neg]
    have := Met.wt_trans (hs.posSet_eq ▸ mem_univ z) (ptsIn_subset_eqnSet hp i hi)
      (ptsIn_subset_eqnSet hp' j hj)
    rw [hw, ha z hz] at this
    exact this
  have hd : ∀ (c : AlgChart Y.str (RingHom.id ℂ) Y.dim), ∀ y ∈ c.e.source,
      c.chernDens ψ y = c.chernDens φ y := by
    intro c y hy
    have hi := mem_pick φ.isLB y
    have hj := mem_pick ψ.isLB y
    obtain ⟨a, ha⟩ := exists_unit_tv hp hp' _ _
    rw [c.chernDens_eq hψ hy hj, c.chernDens_eq hφ hy hi,
      hess_eq_of_unit c hφ hy hi hj a (key _ _ a ha)]
  refine ⟨ψ, hψ, ?_⟩
  rw [Weight.chernInt, Weight.chernInt, chernPart_eq_of_chernDens hd, chernPart_eq_of_chernDens hd]

theorem transport : ∀ (Y : Var ℂ) (Δ : Y.Dv) (L L' : LB Y.X) (r : L.ι → Y.Fnˣ) (r' : L'.ι → Y.Fnˣ),
    Presents Δ L r → Presents Δ L' r' → ∀ φ : Weight Y.str (RingHom.id ℂ) L, φ.IsCInf →
      ∃ ψ : Weight Y.str (RingHom.id ℂ) L', ψ.IsCInf ∧
        ψ.chernInt Y.dim Set.univ (fun _ => 1) = φ.chernInt Y.dim Set.univ (fun _ => 1) := by
  intro Y Δ L L' r r' hp hp' φ hφ
  exact exists_transport hp hp' φ hφ

end GlobalTheory.CompanionTheory.ChernTransport
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutePolynomialOfMemCentralizerStatement
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commute_polynomial_of_mem_centralizer : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (d : GL (Fin n) E) (t : GA E n), t ∈ adCent d → ∀ e : Matrix (Fin n) (Fin n) E, IsPol (nrm d).val e → t.val * rm e = rm e * t.val := by
  first | exact @GlobalTheory.CompanionTheory.TorusCh.CommMem.adCent_comm_rm | exact GlobalTheory.CompanionTheory.TorusCh.CommMem.adCent_comm_rm | (intros; apply GlobalTheory.CompanionTheory.TorusCh.CommMem.adCent_comm_rm <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactFixedVectorProjectionStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_fixed_vector_projection : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (J : Subgroup G), IsCompact (J : Set G) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∃ E : V →ₗ[ℂ] V, (∀ v, E v ∈ fixed π J) ∧ (∀ v ∈ fixed π J, E v = v) ∧ (∀ l : Module.Dual ℂ V, (∀ x ∈ J, l ∘ₗ π x = l) → l ∘ₗ E = l) ∧ (∀ x ∈ J, E ∘ₗ π x = E) ∧ ∀ (u : V) (H : Subgroup G), H ≤ J → (∀ h ∈ H, π h u = u) → ∀ (r : ℕ) (x : Fin r → G), 0 < r → (∀ i, x i ∈ J) → (∀ y ∈ J, ∃! i, (x i)⁻¹ * y ∈ H) → E u = ((r : ℂ)⁻¹) • ∑ i, π (x i) u := by
  first | exact @GlobalTheory.CompanionTheory.CompactAvg.exists_average | exact GlobalTheory.CompanionTheory.CompactAvg.exists_average | (intros; apply GlobalTheory.CompanionTheory.CompactAvg.exists_average <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactGroupFiniteCosetRepsStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_group_finite_coset_reps : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (J H A : Subgroup G), IsCompact (J : Set G) → IsOpen (H : Set G) → H ≤ J → A ≤ J → (∀ y ∈ J, ∃ a ∈ A, a⁻¹ * y ∈ H) → ∃ r : ℕ, 0 < r ∧ ∃ x : Fin r → G, (∀ i, x i ∈ A) ∧ ∀ y ∈ J, ∃! i, (x i)⁻¹ * y ∈ H := by
  first | exact @GlobalTheory.CompanionTheory.CosetReps.exists_fin_coset_reps | exact GlobalTheory.CompanionTheory.CosetReps.exists_fin_coset_reps | (intros; apply GlobalTheory.CompanionTheory.CosetReps.exists_fin_coset_reps <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContractingDoubleCosetVolumeBoundStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contracting_double_coset_volume_bound : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N), (∀ a, 0 < d a) → ∀ (t : kˣ), ValuativeRel.valuation k (t : k) < 1 → ∀ (j : Fin h), j.val + 1 < h → ∀ (m : ℕ), 1 ≤ m → ∀ [MeasurableSpace (AdGL k N)] [BorelSpace (AdGL k N)] (μ : MeasureTheory.Measure (AdGL k N)), μ.IsHaarMeasure → ∃ c : ℝ, 0 < c ∧ ∀ r : ℕ, ENNReal.ofReal (c * ((modulus k (fun a => Fin (d a)) (Zl.JC.zj d t j))⁻¹) ^ r) ≤ μ ((QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' {g | ∃ x ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m, ∃ y ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m, g = x * (leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j)) ^ r * y}) := by
  first | exact @GlobalTheory.CompanionTheory.ContractVolume.volume_lower_bound | exact GlobalTheory.CompanionTheory.ContractVolume.volume_lower_bound | (intros; apply GlobalTheory.CompanionTheory.ContractVolume.volume_lower_bound <;> assumption)
end

