import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0051
import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0008
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.Bundle0001
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.BetaAtAddLeftAndDiagEqTwoOrderStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.betaAt_add_left_and_diag_eq_two_order : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R] (Dg : DegData R (maximalIdeal R)) (C : Type) [NormedField C] [IsUltrametricDist C] (f : R →+* C) (p : ℕ), IsIntegrallyClosed R → (∀ a, ‖f a‖ ≤ 1) → (∀ χ r, PsiCoord Dg.toPre χ r → f r ≠ 0) → (∀ a a' b, betaAt Dg.toPre f p (a + a') b = betaAt Dg.toPre f p a b + betaAt Dg.toPre f p a' b) ∧ ∀ a, betaAt Dg.toPre f p a a = 2 * vPsiAt Dg.toPre f p a := by
  first | exact @GlobalTheory.BetaAdd.main | exact GlobalTheory.BetaAdd.main | (intros; apply GlobalTheory.BetaAdd.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DatumCommensurablePeriod
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix nonZeroDivisors
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

namespace GlobalTheory.TwoLattices

open Module

theorem natAbs_det_gram {M κ : Type} [AddCommGroup M] [Fintype κ] [DecidableEq κ] (b : Basis κ ℤ M)
    (B : LinearMap.BilinForm ℤ M) (hB : Function.Bijective B) :
    (Matrix.of fun i k => B (b i) (b k)).det.natAbs = 1 := by
  have h := LinearEquiv.isUnit_det (LinearEquiv.ofBijective B hB) b b.dualBasis
  have e : LinearMap.toMatrix b b.dualBasis (LinearEquiv.ofBijective B hB : M →ₗ[ℤ] _) =
      (Matrix.of fun i k => B (b i) (b k))ᵀ := by
    ext i k
    simp [LinearMap.toMatrix_apply]
  rw [e, Matrix.det_transpose] at h
  exact Int.isUnit_iff_natAbs_eq.mp h

theorem index_similitude {M M' : Type} [AddCommGroup M] [AddCommGroup M'] [Module.Free ℤ M] [Module.Finite ℤ M]
    [Module.Free ℤ M'] [Module.Finite ℤ M'] (B : LinearMap.BilinForm ℤ M) (B' : LinearMap.BilinForm ℤ M')
    (hB : Function.Bijective B) (hB' : Function.Bijective B') (j : M →+ M') (hj : Function.Injective j)
    (n N : ℕ) (hn : finrank ℤ M = n) (hn' : finrank ℤ M' = n)
    (h : ∀ a b, B' (j a) (j b) = (N : ℤ) ^ 2 * B a b) : j.range.index = N ^ n := by
  let b : Basis (Fin n) ℤ M := Module.finBasisOfFinrankEq ℤ M hn
  let b' : Basis (Fin n) ℤ M' := Module.finBasisOfFinrankEq ℤ M' hn'
  let bN : Basis (Fin n) ℤ j.range := b.map (AddMonoidHom.ofInjective hj).toIntLinearEquiv
  have hbN : ∀ i, (bN i : M') = j (b i) := fun i => rfl
  rw [AddSubgroup.index_eq_natAbs_det b' j.range bN, Basis.det_apply]
  set J := b'.toMatrix (fun i => (bN i : M')) with hJ
  have key : Jᵀ * (Matrix.of fun i k => B' (b' i) (b' k)) * J =
      ((N : ℤ) ^ 2) • Matrix.of fun i k => B (b i) (b k) := by
    ext i k
    have e1 : ∀ i, j (b i) = ∑ l, J l i • b' l := fun i => by
      rw [← hbN]
      exact (b'.sum_repr _).symm
    simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, ← h, e1, Matrix.mul_apply,
      Matrix.transpose_apply, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
      Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have k2 := congrArg (fun X => X.det.natAbs) key
  simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, Int.natAbs_mul, natAbs_det_gram b B hB,
    natAbs_det_gram b' B' hB', _root_.mul_one, Int.natAbs_pow, Int.natAbs_natCast, Fintype.card_fin] at k2
  have : J.det.natAbs ^ 2 = (N ^ n) ^ 2 := by
    rw [sq, k2]; ring
  exact Nat.pow_left_injective (by norm_num) this

variable {E : Type} [Field E] [NumberField E]

theorem exists_mul_mem {M' V : Type} [AddCommGroup M'] [Module (𝓞 E) M'] [AddCommGroup V] [Module E V]
    [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] (φ' : M' →ₗ[𝓞 E] V)
    (hs : Submodule.span E (Set.range φ') = ⊤) (v : V) : ∃ N : ℕ, 0 < N ∧ ∃ b, φ' b = N • v := by
  have hv : v ∈ Submodule.span E (Set.range φ') := hs ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => obtain ⟨b, rfl⟩ := hx; exact ⟨1, one_pos, b, by simp⟩
  | zero => exact ⟨1, one_pos, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨N, hN, b, hb⟩ := hx
    obtain ⟨K, hK, c, hc⟩ := hy
    refine ⟨N * K, Nat.mul_pos hN hK, K • b + N • c, ?_⟩
    rw [map_add, map_nsmul, map_nsmul, hb, hc, smul_add, smul_smul, smul_smul, mul_comm K N]
  | smul e x _ hx =>
    obtain ⟨N, hN, b, hb⟩ := hx
    have halg : IsAlgebraic ℤ e :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic e)
    obtain ⟨m, s, hm, hs⟩ := halg.exists_nsmul_eq (S := 𝓞 E)
    refine ⟨m * N, Nat.mul_pos (Nat.pos_of_ne_zero hm) hN, s • b, ?_⟩
    rw [map_smul, hb, ← IsScalarTower.algebraMap_smul E s, ← hs, smul_assoc, smul_comm e N x, mul_smul]

theorem exists_mul_le {M M' V : Type} [AddCommGroup M] [Module (𝓞 E) M] [Module.Finite (𝓞 E) M]
    [AddCommGroup M'] [Module (𝓞 E) M'] [AddCommGroup V] [Module E V]
    [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] (φ : M →ₗ[𝓞 E] V) (φ' : M' →ₗ[𝓞 E] V)
    (hs : Submodule.span E (Set.range φ') = ⊤) : ∃ N : ℕ, 0 < N ∧ ∀ a, ∃ b, φ' b = N • φ a := by
  obtain ⟨s, hS⟩ := Module.Finite.fg_top (R := 𝓞 E) (M := M)
  choose n hn c hc using exists_mul_mem φ' hs
  refine ⟨∏ x ∈ s, n (φ x), Finset.prod_pos fun x _ => hn _, fun a => ?_⟩
  have ha : a ∈ Submodule.span (𝓞 E) (s : Set M) := hS ▸ Submodule.mem_top
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun x => n (φ x)) (Finset.mem_coe.mp hx)
    exact ⟨k • c (φ x), by rw [map_nsmul, hc, smul_smul, hk, mul_comm]⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨b, hb⟩ := hx
    obtain ⟨d, hd⟩ := hy
    exact ⟨b + d, by rw [map_add, map_add, hb, hd, smul_add]⟩
  | smul e x _ hx =>
    obtain ⟨b, hb⟩ := hx
    exact ⟨e • b, by rw [map_smul, map_smul, hb, smul_comm]⟩

theorem exists_lift {R M M' V : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] [AddCommGroup V] [Module R V] (φ : M →ₗ[R] V) (φ' : M' →ₗ[R] V)
    (hi : Function.Injective φ') (N : ℕ) (h : ∀ a, ∃ b, φ' b = N • φ a) :
    ∃ j : M →ₗ[R] M', ∀ a, φ' (j a) = N • φ a := by
  choose f hf using h
  refine ⟨⟨⟨f, fun x y => hi ?_⟩, fun c x => hi ?_⟩, hf⟩
  · rw [map_add, hf, hf, hf, map_add, smul_add]
  · simp only [RingHom.id_apply]
    rw [map_smul, hf, hf, map_smul, smul_comm]

theorem rank_of_lattice {M : Type} [AddCommGroup M] {g : ℕ} (P : M →+ (Fin g → ℂ)) (hi : Function.Injective P)
    (hd : DiscreteTopology P.range) (hs : Submodule.span ℝ (Set.range P) = ⊤) :
    finrank ℤ M = 2 * g := by
  let L : Submodule ℤ (Fin g → ℂ) := P.range.toIntSubmodule
  haveI : DiscreteTopology L := hd
  haveI : IsZLattice ℝ L := ⟨hs⟩
  have h := ZLattice.rank ℝ L
  have e : M ≃ₗ[ℤ] L := (AddMonoidHom.ofInjective hi).toIntLinearEquiv
  rw [e.finrank_eq, h, Module.finrank_pi_fintype]
  simp [mul_comm]

variable [IsCMField E]

theorem herm_nsmul {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (N : ℕ) (x y : Fin r → E) :
    FD.herm G (N • x) (N • y) = (N : E) ^ 2 * FD.herm G x y := by
  simp only [FD.herm, FD.cc, Pi.smul_apply, nsmul_eq_mul, map_mul, map_natCast, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem form_lift {H : Host E} (D D' : Datum H) {r : ℕ} (ξ : E) (Gm : Matrix (Fin r) (Fin r) E)
    (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (φ' : D'.La →ₗ[𝓞 E] (Fin r → E))
    (h : ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm Gm (φ x) (φ y)))
    (h' : ∀ x y, ((D'.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm Gm (φ' x) (φ' y)))
    (N : ℕ) (j : D.La → D'.La) (hj : ∀ a, φ' (j a) = N • φ a) (a b : D.La) :
    D'.EF (j a) (j b) = (N : ℤ) ^ 2 * D.EF a b := by
  apply Int.cast_injective (α := ℚ)
  rw [h', hj, hj, herm_nsmul]
  push_cast
  rw [h, ← smul_eq_mul ((N : ℚ) ^ 2), ← map_smul]
  congr 1
  rw [Algebra.smul_def]
  simp only [map_pow, map_natCast]
  ring

theorem hermForm_real_smul {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (t : ℝ) (z w : Fin g → ℂ) :
    hermForm Hm ((t : ℂ) • z) ((t : ℂ) • w) = ((t ^ 2 : ℝ) : ℂ) * hermForm Hm z w := by
  simp only [hermForm, star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    Complex.star_def, Complex.conj_ofReal]
  push_cast
  ring

end GlobalTheory.TwoLattices

open GlobalTheory.TwoLattices in

theorem GlobalTheory.datum_commensurable_period :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D D' : Datum H) (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (φ' : D'.La →ₗ[𝓞 E] (Fin r → E)) (g : ℕ) (ty : Fin g → (E →+* ℂ)), FD.cc ξ = -ξ → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, FD.cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm Gm (φ x) (φ y))) → (Function.Injective φ' ∧ Submodule.span E (Set.range φ') = ⊤ ∧ (∀ a b, FD.cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((D'.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm Gm (φ' x) (φ' y))) → ∀ P, IsPeriod D ty P → ∃ (N : ℕ) (j : D.La →ₗ[𝓞 E] D'.La) (j' : D'.La →ₗ[𝓞 E] D.La) (P' : D'.La →+ (Fin g → ℂ)), (0 < N ∧ (∀ a, j' (j a) = (N ^ 2) • a) ∧ (∀ a, j (j' a) = (N ^ 2) • a) ∧ (∀ a b, D'.EF (j a) (j b) = (N : ℤ) ^ 2 * D.EF a b) ∧ (∀ a b, D.EF (j' a) (j' b) = (N : ℤ) ^ 2 * D'.EF a b) ∧ Nat.card (D'.La ⧸ LinearMap.range j) = N ^ (2 * g)) ∧ IsPeriod D' ty P' ∧ (∀ a, P' (j a) = (N : ℂ) • P a) ∧ ∀ a, P (j' a) = (N : ℂ) • P' a := by
  intro E _ _ _ H D D' r ξ Gm φ φ' g ty _ ⟨hi, hs, _, _, hE⟩ ⟨hi', hs', _, _, hE'⟩ P ⟨hPl, hPi, hPd, hPs, Hm, hH, hpos, hIm⟩
  haveI := D.fin
  haveI := D'.fin
  obtain ⟨N₁, hN₁, h₁⟩ := exists_mul_le φ φ' hs'
  obtain ⟨N₂, hN₂, h₂⟩ := exists_mul_le φ' φ hs
  set N := N₁ * N₂ with hNdef
  have hN : 0 < N := Nat.mul_pos hN₁ hN₂
  obtain ⟨j, hj⟩ := exists_lift φ φ' hi' N fun a => by
    obtain ⟨b, hb⟩ := h₁ a
    exact ⟨N₂ • b, by rw [map_nsmul, hb, smul_smul, mul_comm]⟩
  obtain ⟨j', hj'⟩ := exists_lift φ' φ hi N fun a => by
    obtain ⟨b, hb⟩ := h₂ a
    exact ⟨N₁ • b, by rw [map_nsmul, hb, smul_smul]⟩
  clear_value N
  have hNE : (N : E) ≠ 0 := by exact_mod_cast hN.ne'
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have c₁ : ∀ a, j' (j a) = (N ^ 2) • a := fun a => hi (by rw [hj', hj, map_nsmul, smul_smul, sq])
  have c₂ : ∀ a, j (j' a) = (N ^ 2) • a := fun a => hi' (by rw [hj, hj', map_nsmul, smul_smul, sq])
  have f₁ := form_lift D D' ξ Gm φ φ' hE hE' N j hj
  have f₂ := form_lift D' D ξ Gm φ' φ hE' hE N j' hj'
  have cancel : ∀ v w : Fin r → E, N • v = N • w → v = w := fun v w h => by
    rw [← Nat.cast_smul_eq_nsmul E, ← Nat.cast_smul_eq_nsmul E] at h
    exact smul_right_injective _ hNE h
  have ji : Function.Injective j := fun a b h => hi (cancel _ _ (by rw [← hj, ← hj, h]))
  have ji' : Function.Injective j' := fun a b h => hi' (cancel _ _ (by rw [← hj', ← hj', h]))
  let P' : D'.La →+ (Fin g → ℂ) :=
    { toFun := fun a => (N : ℂ)⁻¹ • P (j' a)
      map_zero' := by simp
      map_add' := fun a b => by simp only [map_add, smul_add] }
  have hP' : ∀ a, P' a = (N : ℂ)⁻¹ • P (j' a) := fun _ => rfl
  have p₂ : ∀ a, P (j' a) = (N : ℂ) • P' a := fun a => by
    rw [hP', smul_smul, mul_inv_cancel₀ hNC, one_smul]
  have p₁ : ∀ a, P' (j a) = (N : ℂ) • P a := fun a => by
    rw [hP', c₁, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    congr 1
    push_cast
    field_simp
  have P'i : Function.Injective P' := fun a b h => ji' (hPi (by rw [p₂, p₂, h]))
  have P'd : DiscreteTopology P'.range := by
    let f : P'.range → P.range := fun x => ⟨(N : ℂ) • (x : Fin g → ℂ), by
      obtain ⟨a, ha⟩ := x.2
      exact ⟨j' a, by rw [p₂, ha]⟩⟩
    refine DiscreteTopology.of_continuous_injective (f := f) ?_ ?_
    · exact Continuous.subtype_mk (continuous_subtype_val.const_smul (N : ℂ)) _
    · intro x y h
      exact Subtype.ext (smul_right_injective _ hNC (congrArg Subtype.val h))
  have P's : Submodule.span ℝ (Set.range P') = ⊤ := by
    rw [eq_top_iff, ← hPs, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    have : P a = (N : ℝ)⁻¹ • P' (j a) := by
      rw [p₁]
      ext i
      simp only [Pi.smul_apply, Complex.real_smul, smul_eq_mul]
      push_cast
      field_simp
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  have hper : IsPeriod D' ty P' := by
    refine ⟨fun a x i => ?_, P'i, P'd, P's, Hm, hH, hpos, fun x y => ?_⟩
    · simp only [hP', map_smul, Pi.smul_apply, hPl, smul_eq_mul]
      ring
    · have e : ((N : ℂ))⁻¹ = (((N : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
      rw [hP', hP', e, hermForm_real_smul, Complex.im_ofReal_mul, hIm, f₂]
      push_cast
      field_simp
  haveI : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) _
  haveI : Module.Finite ℤ D'.La := Module.Finite.trans (𝓞 E) _
  haveI : Module.IsTorsionFree ℤ D.La := hPi.moduleIsTorsionFree P (fun c x => map_zsmul P c x)
  haveI : Module.IsTorsionFree ℤ D'.La := P'i.moduleIsTorsionFree P' (fun c x => map_zsmul P' c x)
  refine ⟨N, j, j', P', ⟨hN, c₁, c₂, f₁, f₂, ?_⟩, hper, p₁, p₂⟩
  exact index_similitude D.EF D'.EF D.unimod D'.unimod j.toAddMonoidHom ji (2 * g) N
    (rank_of_lattice P hPi hPd hPs) (rank_of_lattice P' P'i P'd P's) f₁
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFibreSectionOtherModelSameValues
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

noncomputable section

namespace GlobalTheory.FibreSection

variable {X X' Y : Scheme.{0}}

theorem chart_le (L : LB X) {F : X' ⟶ X} {φ : Y ⟶ X} (h : Y ⟶ X') (e : h ≫ F = φ) (j : Fin 1 → L.ι) :
    LB.wchart L (fun _ : Fin 1 => φ) j ≤ h ⁻¹ᵁ (L.pull F).U (fun _ => j 0) := fun y hy =>
  mem_pull.2 ((congrArg (fun q => q y ∈ L.U (j 0)) e).mpr (LB.wchart_le L _ j 0 hy))

theorem le_chart (L : LB X) {F : X' ⟶ X} {φ : Y ⟶ X} (h : Y ⟶ X') (e : h ≫ F = φ) (j : L.ι) :
    h ⁻¹ᵁ (L.pull F).U (fun _ => j) ≤ LB.wchart L (fun _ : Fin 1 => φ) (fun _ => j) := fun y hy =>
  Set.mem_iInter.2 fun _ => (congrArg (fun q => q y ∈ L.U j) e).mp (mem_pull.1 hy)

def pullAlong (L : LB X) {F : X' ⟶ X} {φ : Y ⟶ X} (h : Y ⟶ X') (e : h ≫ F = φ) (s : LB.Sec (L.pull F)) :
    LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => 1)) where
  f := fun (j : Fin 1 → L.ι) => (h.appLE _ _ (chart_le L h e j)).hom (s.f (fun _ => j 0))
  compat := fun (j j' : Fin 1 → L.ι) => fn_ext fun y hy => by
    have h₁ : h y ∈ (L.pull F).U (fun _ => j 0) := chart_le L h e j hy.1
    have h₂ : h y ∈ (L.pull F).U (fun _ => j' 0) := chart_le L h e j' hy.2
    have g : gm (𝟙 Y) y _ ((LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => 1)).g j j') =
        gm (𝟙 Y ≫ φ) y (L.U (j 0) ⊓ L.U (j' 0)) (L.g (j 0) (j' 0)) :=
      (gm_linComb L _ _ (𝟙 Y) y j j' hy.1 hy.2).trans (by rw [Fin.prod_univ_one, zpow_one])
    have eφ : (𝟙 Y ≫ h) ≫ F = 𝟙 Y ≫ φ := by rw [Category.assoc, e]
    exact (gs_res _ y _ hy _).trans ((gs_appLE h _ _ _ (𝟙 _) y hy.1 _).trans ((gs_compat s (𝟙 Y ≫ h) y h₁ h₂).trans
      (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·)
        ((gs_unit _ y _ hy _).trans (congrArg Units.val (g.trans ((congrArg (fun q => gm q y (L.U (j 0) ⊓ L.U (j' 0))
          (L.g (j 0) (j' 0))) eφ).symm.trans (gm_pull_g L F (𝟙 Y ≫ h) y _ _ h₁ h₂).symm))))
        ((gs_res _ y _ hy _).trans (gs_appLE h _ _ _ (𝟙 _) y hy.2 _)))))))

theorem valAt'_appLE (pt : Sp ℂ ⟶ Y) (h : Y ⟶ X') (U : X'.Opens) (W : Y.Opens) (le : W ≤ h ⁻¹ᵁ U)
    (ge : h ⁻¹ᵁ U ≤ W) (f : Γ(X', U)) :
    valAt' pt W ((h.appLE U W le).hom f) = valAt' (pt ≫ h) U f := by
  unfold valAt'
  by_cases hp : ⊤ ≤ pt ⁻¹ᵁ W
  · have hp' : ⊤ ≤ (pt ≫ h) ⁻¹ᵁ U := fun z hz => le (hp hz)
    rw [dif_pos hp, dif_pos hp']
    unfold valAt
    congr 1
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  · have hp' : ¬ ⊤ ≤ (pt ≫ h) ⁻¹ᵁ U := fun k => hp fun z hz => ge (k hz)
    rw [dif_neg hp, dif_neg hp']

theorem exists_sec_same_values : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (y : Sp ℂ ⟶ Xo.X) (s : (Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom y)).Sec), ∃ s' : LB.Sec (PPx y), ∀ j (pt : Sp ℂ ⟶ Gx y) (x : Sp ℂ ⟶ pullback Xo.univ.t.G.hom y), x ≫ pullback.fst _ _ = pt ≫ gxFst y → x ≫ pullback.snd _ _ = 𝟙 _ → pt ≫ gxSnd y = 𝟙 _ → valAt' pt ((PPx y).U (fun _ => j)) (s'.f (fun _ => j)) = valAt' x ((Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom y)).U (fun _ => j)) (s.f (fun _ => j)) := by
  intro E _ _ _ H Dw l Xo y s
  have cond : gxFst y ≫ Xo.univ.t.G.hom = gxSnd y ≫ y :=
    (Over.w (CartesianMonoidalCategory.snd (Over.mk y) Xo.univ.t.G)).trans
      (Over.w (CartesianMonoidalCategory.fst (Over.mk y) Xo.univ.t.G)).symm
  let h : Gx y ⟶ pullback Xo.univ.t.G.hom y := pullback.lift _ _ cond
  have hφ : h ≫ pullback.fst _ _ = gxFst y := pullback.lift_fst _ _ cond
  have hh : h ≫ pullback.snd _ _ = gxSnd y := pullback.lift_snd _ _ cond
  refine ⟨pullAlong Xo.univ.t.PP.L h hφ s, fun j pt x e₁ e₂ e₃ => ?_⟩
  have hx : x = pt ≫ h := by
    apply pullback.hom_ext
    · rw [Category.assoc, hφ, e₁]
    · rw [Category.assoc, hh, e₂, e₃]
  subst hx
  exact valAt'_appLE pt h _ _ (chart_le Xo.univ.t.PP.L h hφ (fun _ => j)) (le_chart Xo.univ.t.PP.L h hφ j) _

end GlobalTheory.FibreSection
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFlagDomainModelsOfFamilyUniformisationStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_flagDomainModels_of_familyUniformisation : GlobalTheory.Published.HasseNormSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ' : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ' ty) (r : ℕ) (ξ₀ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : Dw.La →ₗ[𝓞 E] (Fin r → E)), cc ξ₀ = -ξ₀ → (∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → (τ ξ₀).im < 0) → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((Dw.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-ξ₀ * herm Gm (φ x) (φ y))) → ∃ M : ModelsOf F r, ModelBase M ∧ NegXi M ∧ ∀ k, (M.X k).Gm = Gm ∧ (M.X k).ξ0 = ξ₀ := by
  first | exact @GlobalTheory.ModelsExist.exists_modelsOf | exact GlobalTheory.ModelsExist.exists_modelsOf | (intros; apply GlobalTheory.ModelsExist.exists_modelsOf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIntExtension
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix nonZeroDivisors
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

namespace GlobalTheory.SatDual

theorem exists_int_extension {L V : Type} [AddCommGroup L] [AddCommGroup V] [Module.Finite ℤ L]
    [Module.IsTorsionFree ℤ V] (q : L →ₗ[ℤ] V) (f : L →ₗ[ℤ] ℚ)
    (hf : ∀ x, q x = 0 → ∃ n : ℤ, f x = n) :
    ∃ g : L →ₗ[ℤ] ℤ, ∀ x, q x = 0 → (g x : ℚ) = f x := by
  haveI : Module.Finite ℤ (LinearMap.range q) := inferInstance
  haveI : Module.Free ℤ (LinearMap.range q) := Module.free_of_finite_type_torsion_free'
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property q.rangeRestrict LinearMap.id
    q.surjective_rangeRestrict
  let p : L →ₗ[ℤ] L := LinearMap.id - σ ∘ₗ q.rangeRestrict
  have hp : ∀ x, q (p x) = 0 := by
    intro x
    have h := congrArg Subtype.val (LinearMap.congr_fun hσ (q.rangeRestrict x))
    simp only [LinearMap.comp_apply, LinearMap.id_apply, LinearMap.codRestrict_apply] at h
    simp only [p, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub]
    exact sub_eq_zero.2 h.symm
  have hp' : ∀ x, q x = 0 → p x = x := by
    intro x hx
    have : q.rangeRestrict x = 0 := Subtype.ext hx
    simp [p, this]
  choose n hn using fun x => hf (p x) (hp x)
  refine ⟨AddMonoidHom.toIntLinearMap (AddMonoidHom.mk' n ?_), ?_⟩
  · intro a b
    have : ((n (a + b) : ℤ) : ℚ) = ((n a + n b : ℤ) : ℚ) := by
      push_cast
      rw [← hn, ← hn, ← hn, map_add, map_add]
    exact_mod_cast this
  · intro x hx
    change ((n x : ℤ) : ℚ) = f x
    rw [← hn, hp' x hx]

variable {E : Type} [Field E] [NumberField E]

theorem exists_int_smul_mem {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] (Λ : Submodule (𝓞 E) V) (v : V)
    (hv : v ∈ Submodule.span E (Λ : Set V)) : ∃ N : ℤ, N ≠ 0 ∧ (N : E) • v ∈ Λ := by
  first
  | exact @_root_.GlobalTheory.IntMulMem.exists_int_mul_mem
  | exact _root_.GlobalTheory.IntMulMem.exists_int_mul_mem
  | (apply _root_.GlobalTheory.IntMulMem.exists_int_mul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntMulMem.exists_int_mul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntMulMem.exists_int_mul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntMulMem.exists_int_mul_mem ..)

variable [IsCMField E]

theorem herm_smul_snd {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) (a : E) :
    FD.herm G x (a • y) = FD.herm G x y * FD.cc a := by
  simp only [FD.herm, FD.cc, Pi.smul_apply, smul_eq_mul, map_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem pairing_pseudoBasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (s : ℕ) (e : Fin s → (Fin r → E)) (c : Fin s → FractionalIdeal (𝓞 E)⁰ E), FD.cc ξ = -ξ → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, FD.cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm Gm (φ x) (φ y))) → LinearIndependent E e → (∀ a : Fin s → E, (∑ b, a b • e b) ∈ LinearMap.range φ ↔ ∀ b, a b ∈ c b) → ∀ y : Fin s → E, (∃ x, ∀ b, ξ * FD.herm Gm (φ x) (e b) = y b) ↔ ∀ b, ∀ a ∈ c b, ∃ n : ℤ, Algebra.trace ℚ E (y b * FD.cc a) = n := by
  intro E _ _ _ H D r ξ Gm φ s e c _ hφ he hc y
  obtain ⟨hinj, hspan, -, -, hEF⟩ := hφ
  have hsingle : ∀ (b : Fin s) (a : E), ∑ b', (Pi.single b a : Fin s → E) b' • e b' = a • e b := by
    intro b a
    rw [Finset.sum_eq_single b]
    · simp
    · intro b' _ hb'
      simp [Pi.single_eq_of_ne hb']
    · simp
  have hmem : ∀ (b : Fin s) (a : E), a • e b ∈ LinearMap.range φ ↔ a ∈ c b := by
    intro b a
    rw [← hsingle, hc]
    constructor
    · intro h
      simpa using h b
    · intro h b'
      by_cases hb : b' = b
      · subst hb
        simpa using h
      · rw [Pi.single_eq_of_ne hb]
        exact FractionalIdeal.zero_mem _
  constructor
  · rintro ⟨x, hx⟩ b a ha
    obtain ⟨z, hz⟩ := (hmem b a).2 ha
    refine ⟨D.EF x z, ?_⟩
    rw [hEF, hz, herm_smul_snd, ← _root_.mul_assoc, hx]
  · intro hy
    haveI := D.fin
    haveI : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
    let j : (Fin s → E) →ₗ[E] (Fin r → E) := Fintype.linearCombination E e
    have hj : LinearMap.ker j = ⊥ :=
      LinearMap.ker_eq_bot.2 he.fintypeLinearCombination_injective
    obtain ⟨π, hπ⟩ := j.exists_leftInverse_of_injective hj
    have hπ' : ∀ a, π (j a) = a := fun a => LinearMap.congr_fun hπ a
    let q : D.La →ₗ[ℤ] (Fin r → E) := AddMonoidHom.toIntLinearMap
      (AddMonoidHom.mk' (fun x => φ x - j (π (φ x))) (by
        intro a b
        simp only [map_add]
        abel))
    let f : D.La →ₗ[ℤ] ℚ := AddMonoidHom.toIntLinearMap
      (AddMonoidHom.mk' (fun x => ∑ b, Algebra.trace ℚ E (y b * FD.cc (π (φ x) b))) (by
        intro a b
        simp only [map_add, Pi.add_apply, FD.cc, mul_add, Finset.sum_add_distrib]))
    have hq : ∀ x, q x = φ x - j (π (φ x)) := fun _ => rfl
    have hf : ∀ x, f x = ∑ b, Algebra.trace ℚ E (y b * FD.cc (π (φ x) b)) := fun _ => rfl
    obtain ⟨g, hg⟩ := exists_int_extension q f (by
      intro x hx
      rw [hq, sub_eq_zero] at hx
      have h1 : ∀ b, π (φ x) b ∈ c b := (hc _).1 ⟨x, hx⟩
      choose n hn using fun b => hy b _ (h1 b)
      refine ⟨∑ b, n b, ?_⟩
      rw [hf]
      push_cast
      exact Finset.sum_congr rfl fun b _ => hn b)
    obtain ⟨x, hx⟩ := D.unimod.2 g
    refine ⟨x, fun b => ?_⟩
    have key : ∀ a ∈ c b,
        Algebra.trace ℚ E ((ξ * FD.herm Gm (φ x) (e b) - y b) * FD.cc a) = 0 := by
      intro a ha
      obtain ⟨z, hz⟩ := (hmem b a).2 ha
      have hz' : φ z = j (Pi.single b a) := by
        rw [hz, ← hsingle]
        rfl
      have h1 := hg z (by rw [hq, hz', hπ', sub_self])
      rw [← hx, hEF, hz, herm_smul_snd, hf, hz', hπ', Finset.sum_eq_single b] at h1
      · rw [sub_mul, map_sub, _root_.mul_assoc, h1]
        simp
      · intro b' _ hb'
        simp [Pi.single_eq_of_ne hb', FD.cc]
      · simp
    rw [← sub_eq_zero]
    refine (traceForm_nondegenerate ℚ E).1 _ fun t => ?_
    obtain ⟨N, hN, hNt⟩ := exists_int_smul_mem (E := E) (LinearMap.range φ) (FD.cc t • e b)
      (by rw [LinearMap.coe_range, hspan]; trivial)
    rw [smul_smul, hmem] at hNt
    have h2 := key _ hNt
    have h3 : FD.cc ((N : E) * FD.cc t) = (N : ℚ) • t := by
      simp [FD.cc, Algebra.smul_def]
    rw [h3, mul_smul_comm, map_smul, smul_eq_zero] at h2
    rcases h2 with h2 | h2
    · exact absurd (by exact_mod_cast h2) hN
    · rw [Algebra.traceForm_apply]
      exact h2

end GlobalTheory.SatDual
end

