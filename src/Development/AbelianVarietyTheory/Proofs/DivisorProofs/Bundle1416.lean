import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1389
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1204
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
import ReciprocityTheory.SemistableReduction.Bundle0025
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1335
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1388
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1392
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1380
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1391
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0385
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1116
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0435
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0936
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralSimpleAlgebraEmbeddingsConjugate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1378
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittFrameTorusEqLeviElement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1393
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1241

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularOrbitConjCompactModCentralizerUnitaryStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_orbit_conj_compact_mod_centralizer_unitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (y : UL n w), y.1.val.charpoly.Separable → ∀ C : Set (UL n w), IsCompact C → ∃ Ω : Set (UL n w), IsCompact Ω ∧ ∀ g : UL n w, g⁻¹ * y * g ∈ C → ∃ t ∈ twCent (MonoidHom.id (UL n w)) y, ∃ ω ∈ Ω, g = t * ω := by
  first | exact @GlobalTheory.OrbitU.orbit_cpt_U | exact GlobalTheory.OrbitU.orbit_cpt_U | (intros; apply GlobalTheory.OrbitU.orbit_cpt_U <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResultantDerivativeNeZero
section
set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

namespace GlobalTheory.PencilDisc

theorem resultant_derivative_ne_zero : ∀ (σ F : Type) [Fintype σ] [Field F] [CharZero F] (p : Polynomial (MvPolynomial σ F)) (δ : ℕ), 1 ≤ δ → p.natDegree = δ → Irreducible p → Polynomial.resultant p (Polynomial.derivative p) δ (δ - 1) ≠ 0 := by
  intro σ F _ _ _ p δ hδ hp hirr
  let K := FractionRing (MvPolynomial σ F)
  have hinj : Function.Injective (algebraMap (MvPolynomial σ F) K) := IsFractionRing.injective _ _
  haveI : CharZero K := charZero_of_injective_algebraMap hinj
  have hprim : p.IsPrimitive := hirr.isPrimitive (by omega)
  have h1 : Irreducible (p.map (algebraMap _ K)) := hprim.irreducible_iff_irreducible_map_fraction_map.1 hirr
  have h2 := Polynomial.resultant_ne_zero _ _ h1.separable
  rw [Polynomial.natDegree_derivative, Polynomial.natDegree_map_eq_of_injective hinj, hp, Polynomial.derivative_map,
    Polynomial.resultant_map_map] at h2
  intro h
  exact h2 (by rw [h, map_zero])

theorem exists_specialise_ne_zero : ∀ (F S T : Type) [Field F] [Infinite F] (R : MvPolynomial (S ⊕ T) F), R ≠ 0 → ∃ v : T → F, MvPolynomial.aeval (Sum.elim (fun i => (MvPolynomial.X i : MvPolynomial S F)) fun k => MvPolynomial.C (v k)) R ≠ 0 := by
  intro F S T _ _ R hR
  have h1 : sumAlgEquiv F S T R ≠ 0 := (map_ne_zero_iff _ (sumAlgEquiv F S T).injective).2 hR
  obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.1 h1
  obtain ⟨v, hv⟩ : ∃ v : T → F, eval v (coeff m (sumAlgEquiv F S T R)) ≠ 0 := by
    by_contra! H
    exact hm (MvPolynomial.funext fun x => by simpa using H x)
  refine ⟨v, fun h => hv ?_⟩
  have key : ∀ P : MvPolynomial (S ⊕ T) F,
      aeval (Sum.elim (fun i => (X i : MvPolynomial S F)) fun k => C (v k)) P = MvPolynomial.map (eval v) (sumAlgEquiv F S T P) := by
    intro P
    induction P using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p i hp =>
      rw [map_mul, map_mul, map_mul, hp]
      cases i <;> simp
  rw [← coeff_map, ← key, h, coeff_zero]

theorem irreducible_of_map {F L : Type} [Field F] [Field L] [Algebra F L] {σ : Type} (f : MvPolynomial σ F)
    (h : Irreducible (MvPolynomial.map (algebraMap F L) f)) : Irreducible f := by
  have hinj := (algebraMap F L).injective
  haveI : IsLocalHom (MvPolynomial.map (σ := σ) (algebraMap F L)) := ⟨fun g hg => by
    obtain ⟨c, hc, e⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.1 hg
    have hc0 : algebraMap F L (coeff 0 g) = c := by
      rw [← coeff_map, e, coeff_zero_C]
    refine MvPolynomial.isUnit_iff_eq_C_of_isReduced.2 ⟨coeff 0 g, ?_, ?_⟩
    · refine isUnit_iff_ne_zero.2 fun h0 => hc.ne_zero ?_
      rw [← hc0, h0, map_zero]
    · apply MvPolynomial.map_injective _ hinj
      rw [e, map_C, hc0]⟩
  exact Irreducible.of_map h

theorem exists_poly_noSquare : ∀ (F : Type) [Field F] [CharZero F] (D N δ : ℕ) (f : MvPolynomial (Fin (D + 1) × Fin N) F), 1 ≤ δ → IsMultiHomogeneous (fun _ => δ) f → Irreducible (MvPolynomial.map (algebraMap F (AlgebraicClosure F)) f) → ∃ Q : MvPolynomial (Fin D × Fin N) F, Q ≠ 0 ∧ Q.totalDegree ≤ 2 * D * δ ^ 2 ∧ ∀ (K : Type) [Field K] [Algebra F K] (s : Fin D → Fin N → K), aeval (fun p : Fin D × Fin N => s p.1 p.2) Q ≠ 0 → NoSquare (spec s f) := by
  intro F _ _ D N δ f hδ hf hirr
  have hF : Irreducible f := irreducible_of_map f hirr
  let u : Fin D → Fin N → MvPolynomial ((Fin D × Fin N) ⊕ (Fin N ⊕ Fin N)) F := fun i j => X (Sum.inl (i, j))
  let a : Fin N → MvPolynomial ((Fin D × Fin N) ⊕ (Fin N ⊕ Fin N)) F := fun j => X (Sum.inr (Sum.inl j))
  let b : Fin N → MvPolynomial ((Fin D × Fin N) ⊕ (Fin N ⊕ Fin N)) F := fun j => X (Sum.inr (Sum.inr j))
  have hc := GlobalTheory.T.pencilLinePolynomial_natDegree_le_and_coeff F _ D N δ f hf u a b
  let g : Fin (D + 1) × Fin N → (Fin D × Fin N) ⊕ (Fin N ⊕ Fin N) := fun p =>
    Fin.lastCases (motive := fun _ => (Fin D × Fin N) ⊕ (Fin N ⊕ Fin N)) (Sum.inr (Sum.inr p.2)) (fun i => Sum.inl (i, p.2)) p.1
  have hg : Function.Injective g := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    induction i using Fin.lastCases <;> induction i' using Fin.lastCases <;> simp_all [g]
  have hjoin : join u b = fun p => X (g p) := by
    funext ⟨i, j⟩
    induction i using Fin.lastCases <;> simp [join, g, u, b]
  have hlead : (line u a b f).coeff δ ≠ 0 := by
    rw [hc.2, hjoin, show (aeval fun p => (X (g p) : MvPolynomial _ F)) f = rename g f from congrArg (fun φ : MvPolynomial _ F →ₐ[F] MvPolynomial _ F => φ f) (MvPolynomial.algHom_ext fun p => by simp)]
    exact (rename_injective g hg).ne_iff' (map_zero _) |>.mpr hF.ne_zero
  have hnat : (line u a b f).natDegree = δ := le_antisymm hc.1 (Polynomial.le_natDegree_of_ne_zero hlead)
  have hR : disc δ u a b f ≠ 0 := resultant_derivative_ne_zero _ F (line u a b f) δ hδ hnat (GlobalTheory.T.irreducible_pencilLinePolynomial_generic_line F D N f hF)
  obtain ⟨v, hv⟩ := exists_specialise_ne_zero F (Fin D × Fin N) (Fin N ⊕ Fin N) _ hR
  refine ⟨disc δ (fun i j => (X (i, j) : MvPolynomial (Fin D × Fin N) F)) (fun j => C (v (Sum.inl j))) (fun j => C (v (Sum.inr j))) f,
    ?_, GlobalTheory.T.totalDegree_pencilLineDiscriminant_le F D N δ f hf _ _, ?_⟩
  · have e := map_disc (aeval (Sum.elim (fun i => (X i : MvPolynomial (Fin D × Fin N) F)) fun k => C (v k))) δ u a b f
    rw [e] at hv
    simpa [u, a, b] using hv
  · intro K _ _ s hs
    have e := map_disc (aeval (fun p : Fin D × Fin N => s p.1 p.2)) δ (fun i j => (X (i, j) : MvPolynomial (Fin D × Fin N) F))
      (fun j => C (v (Sum.inl j))) (fun j => C (v (Sum.inr j))) f
    rw [e] at hs
    simp only [aeval_X, aeval_C] at hs
    have hc' := GlobalTheory.T.pencilLinePolynomial_natDegree_le_and_coeff F K D N δ f hf s (fun j => algebraMap F K (v (Sum.inl j))) (fun j => algebraMap F K (v (Sum.inr j)))
    exact GlobalTheory.T.not_square_linear_factor_of_pencilLineDiscriminant_ne_zero F K D N δ f s _ _ hδ hc'.1 hc'.2 hs

end GlobalTheory.PencilDisc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightDerivativeNilRadicalInvariantStatement
section
open Matrix GlobalTheory.TorFin
open scoped ContDiff

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.right_derivative_nil_radical_invariant : ∀ (n : ℕ) (G : Type) [Group G] (J : Matrix (Fin n) (Fin n) ℂ) (s : Matrix (Fin n) (Fin n) ℂ → G), Jᴴ = J → IsUnit J.det → IsMulOn J s → ∀ ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (smLoc J s), IsRightDer J s ρ → ∀ (x : Fin n → ℂ) (N : Subgroup G), (∀ u, IsUni J u → u - 1 ∈ nilRad J x → s u ∈ N) → ∀ f : smLoc J s, (∀ ν ∈ N, ∀ g, f.1 (ν * g) = f.1 g) → ∀ T ∈ leftIdl ρ (nilRad J x : Set (Matrix (Fin n) (Fin n) ℂ)), (T f).1 1 = 0 := by
  first | exact @GlobalTheory.TorFin.leftIdl_apply_one_eq_zero | exact GlobalTheory.TorFin.leftIdl_apply_one_eq_zero | (intros; apply GlobalTheory.TorFin.leftIdl_apply_one_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowsInSpanOfRankNormalForm
section
open ValuativeRel Matrix

namespace GlobalTheory

theorem rows_mem_span_of_isUnit_mul (K : Type) [Field K] (A D : Type) [Fintype A] [DecidableEq A]
    [Fintype D] [DecidableEq D] (r : ℕ) (X : Matrix A D K) (H : Matrix (Fin r) A K)
    (Q : Matrix D (Fin r) K) (hX : X.rank ≤ r) (hU : IsUnit (H * X * Q)) :
    ∀ i, ∃ s : Fin r → K, X i = s ᵥ* (H * X) := by
  intro i
  have hle : Submodule.span K (Set.range (H * X)) ≤ Submodule.span K (Set.range X) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have : (H * X) j = ∑ a, H j a • X a := by
      ext d; simp [Matrix.mul_apply, Finset.sum_apply]
    rw [this]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  have h1 : r ≤ (H * X).rank := by
    have := Matrix.rank_mul_le_left (H * X) Q
    rw [Matrix.rank_of_isUnit _ hU] at this
    simpa using this
  have heq : Submodule.span K (Set.range (H * X)) = Submodule.span K (Set.range X) := by
    apply Submodule.eq_of_le_of_finrank_le hle
    have e1 : X.rank = Module.finrank K (Submodule.span K (Set.range X)) :=
      Matrix.rank_eq_finrank_span_row X
    have e2 : (H * X).rank = Module.finrank K (Submodule.span K (Set.range (H * X))) :=
      Matrix.rank_eq_finrank_span_row (H * X)
    omega
  have hi : X i ∈ Submodule.span K (Set.range (H * X)) := heq ▸ Submodule.subset_span ⟨i, rfl⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hi
  refine ⟨c, ?_⟩
  rw [← hc]
  ext d
  simp [Matrix.vecMul, dotProduct, Finset.sum_apply, mul_comm]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurConstantsExistOnChainOfCuspRapidDecay
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.Hk3

theorem schurAll_of_cuspRapidDecay : GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), SchurAll R :=
  fun hP _ _ _ _ _ _ _ _ _ _ _ _ =>
    ⟨fun _ _ _ => GlobalTheory.MultFinite.schurMult hP _ _, GlobalTheory.MultFinite.schurMult hP _ _,
      fun _ => GlobalTheory.MultFinite.schurMult hP _ _⟩

end GlobalTheory.Hk3

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatBoxDecomposition
section
open ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.RankCoinv.Decomp
open GlobalTheory.SplitFlip GlobalTheory.RankCoinv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A D : Type}

theorem val_unif_pow_le {ϖ : kˣ} (hϖ : IsUnif ϖ) {n m : ℕ} (h : n ≤ m) :
    valuation k ((ϖ ^ m : kˣ) : k) ≤ valuation k ((ϖ ^ n : kˣ) : k) := by
  simp only [Units.val_pow_eq_pow_val, map_pow]
  exact pow_le_pow_right_of_le_one' (show valuation k (ϖ : k) ≤ 1 from hϖ ▸ uniformizer_lt_one.le) h

theorem box_mono {ϖ : kˣ} (hϖ : IsUnif ϖ) (X : Matrix A D k) {n m : ℕ} (h : n ≤ m) :
    box ϖ X (fun _ => m) ⊆ box ϖ X (fun _ => n) :=
  fun _ hY i j => (hY i j).trans (val_unif_pow_le hϖ h)

theorem mem_box_self (ϖ : kˣ) (X : Matrix A D k) (e : A → ℕ) : X ∈ box ϖ X e :=
  fun i j => by simp

theorem eq_of_forall_mem_box {ϖ : kˣ} (hϖ : IsUnif ϖ) {X Y : Matrix A D k}
    (h : ∀ n : ℕ, Y ∈ box ϖ X (fun _ => n)) : Y = X := by
  ext i j
  by_contra hne
  have h0 : valuation k (Y i j - X i j) ≠ 0 := by simpa [sub_eq_zero] using hne
  obtain ⟨n, hn⟩ := exists_pow_lt₀ (show valuation k (ϖ : k) < 1 from hϖ ▸ uniformizer_lt_one) (Units.mk0 _ h0)
  have := h n i j
  simp only [Units.val_pow_eq_pow_val, map_pow] at this
  exact absurd this (not_le.2 hn)

variable [Fintype A] [Fintype D]

theorem exists_box_subset {ϖ : kˣ} (hϖ : IsUnif ϖ) {X : Matrix A D k} {U : Set (Matrix A D k)}
    (hU : U ∈ nhds X) : ∃ n : ℕ, box ϖ X (fun _ => n) ⊆ U := by
  refine exists_subset_nhds_of_isCompact' (V := fun n : ℕ => box ϖ X (fun _ => n))
    (Antitone.directed_ge fun a b h => box_mono hϖ X h) (fun n => isCompact_box ϖ X _)
    (fun n => (isClopen_box ϖ X _).isClosed) ?_
  intro Y hY
  rw [eq_of_forall_mem_box hϖ (Set.mem_iInter.1 hY)]
  exact hU

theorem exists_sum_boxFn (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ) (hϖ : GlobalTheory.SplitFlip.IsUnif ϖ) :
    ∀ Φ ∈ GlobalTheory.WeilM.SB (Matrix A D k), ∃ m₁ : ℕ, ∀ m ≥ m₁, ∃ s : Finset (Matrix A D k),
      Φ = ∑ c ∈ s, Φ c • GlobalTheory.RankCoinv.boxFn ϖ c (fun _ => m) ∧
      ∀ c ∈ s, ∀ X ∈ GlobalTheory.RankCoinv.box ϖ c (fun _ => m), Φ X = Φ c := by
  classical
  intro Φ hΦ
  obtain ⟨hlc, hcs⟩ := hΦ
  have hrad : ∀ X, ∃ n : ℕ, box ϖ X (fun _ => n) ⊆ {Y | Φ Y = Φ X} := fun X =>
    exists_box_subset hϖ ((hlc.isOpen_fiber (Φ X)).mem_nhds rfl)
  choose n hn using hrad
  obtain ⟨t, ht⟩ := IsCompact.elim_finite_subcover hcs (fun X => box ϖ X (fun _ => n X))
    (fun X => (isClopen_box ϖ X _).isOpen) (fun Y _ => Set.mem_iUnion.2 ⟨Y, mem_box_self ϖ Y _⟩)
  refine ⟨t.sup n, fun m hm => ?_⟩
  have hconst : ∀ Y ∈ tsupport Φ, ∀ Z ∈ box ϖ Y (fun _ => m), Φ Z = Φ Y := by
    intro Y hY Z hZ
    obtain ⟨X, hXt, hYX⟩ := Set.mem_iUnion₂.1 (ht hY)
    have hsub : box ϖ Y (fun _ => m) ⊆ box ϖ X (fun _ => n X) := by
      rw [← box_eq_of_mem hYX]; exact box_mono hϖ Y ((Finset.le_sup hXt).trans hm)
    have h1 : Φ Z = Φ X := hn X (hsub hZ)
    have h2 : Φ Y = Φ X := hn X (hsub (mem_box_self ϖ Y _))
    rw [h1, h2]
  let rep : Set (Matrix A D k) → Matrix A D k := fun B =>
    if h : ∃ Z, box ϖ Z (fun _ => m) = B then h.choose else 0
  have hrep : ∀ Y, box ϖ (rep (box ϖ Y (fun _ => m))) (fun _ => m) = box ϖ Y (fun _ => m) := by
    intro Y
    have h : ∃ Z, box ϖ Z (fun _ => m) = box ϖ Y (fun _ => m) := ⟨Y, rfl⟩
    rw [show rep (box ϖ Y (fun _ => m)) = h.choose from dif_pos h]
    exact h.choose_spec
  obtain ⟨s₀, hs₀⟩ := IsCompact.elim_finite_subcover hcs
    (fun Y : tsupport Φ => box ϖ (Y : Matrix A D k) (fun _ => m))
    (fun Y => (isClopen_box ϖ _ _).isOpen) (fun Y hY => Set.mem_iUnion.2 ⟨⟨Y, hY⟩, mem_box_self ϖ Y _⟩)
  let s : Finset (Matrix A D k) := s₀.image (fun Y : tsupport Φ => rep (box ϖ (Y : Matrix A D k) (fun _ => m)))
  have hs : ∀ c ∈ s, ∃ Y ∈ tsupport Φ, c = rep (box ϖ Y (fun _ => m)) := by
    intro c hc
    obtain ⟨Y, -, rfl⟩ := Finset.mem_image.1 hc
    exact ⟨Y, Y.2, rfl⟩
  have hval : ∀ c ∈ s, ∀ Z ∈ box ϖ c (fun _ => m), Φ Z = Φ c := by
    intro c hc Z hZ
    obtain ⟨Y, hY, rfl⟩ := hs c hc
    rw [hrep] at hZ
    have hcY : rep (box ϖ Y (fun _ => m)) ∈ box ϖ Y (fun _ => m) := by
      have := mem_box_self ϖ (rep (box ϖ Y (fun _ => m))) (fun _ => m)
      rwa [hrep] at this
    rw [hconst Y hY Z hZ, hconst Y hY _ hcY]
  have huniq : ∀ c ∈ s, ∀ c' ∈ s, ∀ Z, Z ∈ box ϖ c (fun _ => m) → Z ∈ box ϖ c' (fun _ => m) → c = c' := by
    intro c hc c' hc' Z hZ hZ'
    obtain ⟨Y, -, rfl⟩ := hs c hc
    obtain ⟨Y', -, rfl⟩ := hs c' hc'
    have e1 := box_eq_of_mem hZ
    have e2 := box_eq_of_mem hZ'
    rw [hrep] at e1 e2
    rw [← e1, ← e2]
  have hcov : ∀ Z, Φ Z ≠ 0 → ∃ c ∈ s, Z ∈ box ϖ c (fun _ => m) := by
    intro Z hZ
    obtain ⟨Y, hY, hZY⟩ := Set.mem_iUnion₂.1 (hs₀ (subset_tsupport Φ hZ))
    refine ⟨rep (box ϖ (Y : Matrix A D k) (fun _ => m)), Finset.mem_image_of_mem _ hY, ?_⟩
    rw [hrep]; exact hZY
  refine ⟨s, ?_, hval⟩
  funext Z
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, boxFn]
  by_cases h : ∃ c ∈ s, Z ∈ box ϖ c (fun _ => m)
  · obtain ⟨c, hc, hZ⟩ := h
    rw [Finset.sum_eq_single c]
    · rw [Set.indicator_of_mem hZ, Pi.one_apply, mul_one, hval c hc Z hZ]
    · intro c' hc' hne
      rw [Set.indicator_of_notMem (fun hZ' => hne (huniq c' hc' c hc Z hZ' hZ)), mul_zero]
    · intro hcs'; exact absurd hc hcs'
  · push_neg at h
    rw [Finset.sum_eq_zero fun c hc => by rw [Set.indicator_of_notMem (h c hc), mul_zero]]
    by_contra hZ
    obtain ⟨c, hc, hZc⟩ := hcov Z hZ
    exact h c hc hZc

end GlobalTheory.RankCoinv.Decomp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzLocallyConstantSupport
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit GlobalTheory.GJReg
open Classical

noncomputable section
open Filter Topology

namespace GlobalTheory.SBBounds

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem tendsto_pow_zero {x : k} (h : valuation k x < 1) : Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) := by
  rw [(IsValuativeTopology.hasBasis_nhds_zero' k).tendsto_right_iff]
  intro γ hγ
  have : MulArchimedean (ValueGroupWithZero k) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨n, hn⟩ := exists_pow_lt₀ h (Units.mk0 γ hγ)
  filter_upwards [eventually_ge_atTop n] with m hm
  rw [map_pow]
  exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' h.le hm) hn

theorem sb_bounds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (t : k),
    t ≠ 0 → valuation k t < 1 → ∀ φ : Matrix (Fin n) (Fin n) k → ℂ, φ ∈ SB (Matrix (Fin n) (Fin n) k) →
    ∃ N M : ℕ, (∀ X, φ X ≠ 0 → t ^ N • X ∈ intM k (Fin n) (Fin n)) ∧
      ∀ X E, E ∈ intM k (Fin n) (Fin n) → φ (X + t ^ M • E) = φ X := by
  intro k _ _ _ _ n t _ ht φ hφ
  obtain ⟨hlc, hcs⟩ := hφ
  have hU : IsOpen (intM k (Fin n) (Fin n)) := isOpen_intMatrix
  have hUc : IsCompact (intM k (Fin n) (Fin n)) := isCompact_intMatrix
  have h0 : (0 : Matrix (Fin n) (Fin n) k) ∈ intM k (Fin n) (Fin n) := fun i j => (𝒪[k]).zero_mem
  have htO : t ∈ 𝒪[k] := (Valuation.mem_integer_iff _ _).2 ht.le
  have hT := tendsto_pow_zero ht

  have hmono : Monotone fun N : ℕ => {X : Matrix (Fin n) (Fin n) k | t ^ N • X ∈ intM k (Fin n) (Fin n)} := by
    intro N N' hNN' X hX i j
    have e : t ^ N' • X = t ^ (N' - N) • (t ^ N • X) := by
      rw [smul_smul, ← pow_add, Nat.sub_add_cancel hNN']
    rw [e]
    simp only [Matrix.smul_apply, smul_eq_mul]
    exact (𝒪[k]).mul_mem ((𝒪[k]).pow_mem htO _) (hX i j)
  obtain ⟨N, hN⟩ := hcs.isCompact.elim_directed_cover
    (fun N : ℕ => {X : Matrix (Fin n) (Fin n) k | t ^ N • X ∈ intM k (Fin n) (Fin n)})
    (fun N => hU.preimage (f := fun X : Matrix (Fin n) (Fin n) k => t ^ N • X) (continuous_const_smul _))
    (fun X _ => by
      have h1 : Tendsto (fun N : ℕ => t ^ N • X) atTop (𝓝 ((0 : k) • X)) := hT.smul_const X
      rw [zero_smul] at h1
      obtain ⟨N, hN⟩ := (h1.eventually (hU.mem_nhds h0)).exists
      exact Set.mem_iUnion.2 ⟨N, hN⟩)
    hmono.directed_le

  have hZ : IsOpen {p : k × Matrix (Fin n) (Fin n) k × Matrix (Fin n) (Fin n) k |
      φ (p.2.1 + p.1 • p.2.2) = φ p.2.1} := by
    have c1 : Continuous fun p : k × Matrix (Fin n) (Fin n) k × Matrix (Fin n) (Fin n) k =>
        p.2.1 + p.1 • p.2.2 := by fun_prop
    have c2 : Continuous fun p : k × Matrix (Fin n) (Fin n) k × Matrix (Fin n) (Fin n) k => p.2.1 := by fun_prop
    have := ((hlc.comp_continuous c1).comp₂ (hlc.comp_continuous c2) fun a b => a - b).isOpen_fiber 0
    simpa [Function.comp_def, sub_eq_zero] using this
  have hKU : IsCompact (tsupport φ ×ˢ intM k (Fin n) (Fin n)) := hcs.isCompact.prod hUc
  have hev : ∀ᶠ c in 𝓝 (0 : k), ∀ q ∈ tsupport φ ×ˢ intM k (Fin n) (Fin n), φ (q.1 + c • q.2) = φ q.1 := by
    refine hKU.eventually_forall_of_forall_eventually fun q _ => ?_
    have hm : ((0 : k), q) ∈ {p : k × Matrix (Fin n) (Fin n) k × Matrix (Fin n) (Fin n) k |
      φ (p.2.1 + p.1 • p.2.2) = φ p.2.1} := by simp
    exact hZ.mem_nhds hm
  obtain ⟨M, hM⟩ := (hT.eventually hev).exists
  refine ⟨N, M, fun X hX => hN (subset_tsupport _ hX), fun X E hE => ?_⟩
  by_cases hX : X ∈ tsupport φ
  · exact hM (X, E) ⟨hX, hE⟩
  by_cases hX' : X + t ^ M • E ∈ tsupport φ
  · have hE' : -E ∈ intM k (Fin n) (Fin n) := fun i j => (𝒪[k]).neg_mem (hE i j)
    have := hM (X + t ^ M • E, -E) ⟨hX', hE'⟩
    simp only [smul_neg, add_neg_cancel_right] at this
    exact this.symm
  · rw [image_eq_zero_of_notMem_tsupport hX, image_eq_zero_of_notMem_tsupport hX']

end GlobalTheory.SBBounds
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeedOrbKVanish
section
open MeasureTheory Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKDef
open scoped TensorProduct Classical

namespace GlobalTheory.TorusElementPower

theorem torusElt_pow_eq {k : Type} [Field k] {N : ℕ} (ϖ : kˣ) (ν : Fin N → ℤ) (m : ℕ) :
    GlobalTheory.GLDoubling.torusElt k (Fin N) ϖ ν ^ m = GlobalTheory.GLDoubling.torusElt k (Fin N) ϖ (fun a => (m : ℤ) * ν a) := by
  unfold GlobalTheory.GLDoubling.torusElt
  rw [← map_pow]
  congr 1
  funext a
  simp only [Pi.pow_apply, ← zpow_natCast, ← _root_.zpow_mul, mul_comm]

end GlobalTheory.TorusElementPower
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemSpanK
section
noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory

namespace GlobalTheory.AutGrowth

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

variable (E a) in

def spanK (φ : Sm E a) : Submodule ℂ (Sm E a) := Submodule.span ℂ (Set.range fun k => cptRep E a k φ)

theorem spanK_stable (φ : Sm E a) : ∀ k, ∀ w ∈ spanK E a φ, cptRep E a k w ∈ spanK E a φ := by
  intro k w hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k', rfl⟩ := hx
    exact Submodule.subset_span ⟨k * k', by simp only [map_mul, Module.End.mul_apply]⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem self_mem_spanK (φ : Sm E a) : φ ∈ spanK E a φ :=
  Submodule.subset_span ⟨1, by simp only [map_one, Module.End.one_apply]⟩

def mapsJ (φ : Sm E a) (L : Subgroup (GL (Fin a) (Af E))) : Submodule ℂ (spanK E a φ →ₗ[ℂ] Sm E a) where
  carrier := {T | T ∈ maps L (spanK E a φ) (spanK_stable φ) ∧ ∀ z ∈ Zalg E a, z φ = 0 → ∀ w, z (T w) = 0}
  zero_mem' := ⟨zero_mem _, fun z _ _ w => by simp⟩
  add_mem' {T T'} h h' := ⟨add_mem h.1 h'.1, fun z hz h0 w => by
    simp [h.2 z hz h0 w, h'.2 z hz h0 w]⟩
  smul_mem' c T h := ⟨Submodule.smul_mem _ c h.1, fun z hz h0 w => by simp [h.2 z hz h0 w]⟩

end GlobalTheory.AutGrowth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelTorusElementRealComponentsOfFrame
section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TorusDict

open GlobalTheory.AdelicU

theorem compAt_mt {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (a : GA D V) (τ : D.what₂.Tau) :
    Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a) =
      GlobalTheory.Orb.archMat D.sp.cm.sig V.gram (embOverOf D τ) (projArch D.sp.cm.sig V.gram (placeOf D τ) a) := by
  refine Matrix.ext fun i j => ?_
  change θ τ (infPart D (Formalism.L2.Theta.mt V a i j)) = _
  rw [eq_infProj hθ (embOverOf D τ) rfl]
  exact GlobalTheory.Doubling.infProj_fst (embOverOf D τ) _

theorem torus_dict : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (r : ℕ) (X Y : Matrix (Fin V.rank) (Fin r) D.host.E) (t : Fin r → ℝ) (a : GA D V), GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig V.gram X Y t a → (Formalism.L2.Theta.mt V a).map (finPart D) = 1 ∧ ∀ τ, Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a) * X.map (tauE D τ) = X.map (tauE D τ) * Matrix.diagonal (fun i => ((t i : ℝ) : ℂ)) ∧ Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a) * Y.map (tauE D τ) = Y.map (tauE D τ) * Matrix.diagonal (fun i => ((t i : ℝ) : ℂ)⁻¹) ∧ ∀ z : Fin V.rank → D.host.E, (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram) *ᵥ z = 0 → (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * V.gram) *ᵥ z = 0 → Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a) *ᵥ (fun i => tauE D τ (z i)) = fun i => tauE D τ (z i) := by
  intro D θ hθ V r X Y t a ha
  refine ⟨congrArg Units.val (MonoidHom.mem_ker.1 ha.1), fun τ => ?_⟩
  rw [compAt_mt hθ V a τ]
  exact ha.2 (placeOf D τ) (embOverOf D τ)

end GlobalTheory.TorusDict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralParabolicUnfoldLeviStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedOrbitalIntegral_parabolic_unfold_levi : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∀ (n a : ℕ) (ha : a ≤ n) (w : Pl E) (f : GLw n w → ℂ), (∃ K' : Subgroup (GLw n w), IsOpen (K' : Set (GLw n w)) ∧ IsHecke K' f) → ∀ m : GLw a w × GLw (n - a) w, (m.1.val.charpoly * m.2.val.charpoly).Separable → ∀ hγ : blk (Nat.add_sub_cancel' ha) w m 0 ∈ GlobalTheory.LeviDesc.parP a n w, twOrb (MonoidHom.id (GlobalTheory.LeviDesc.parP a n w)) ((GlobalTheory.LFun.KGL w n).subgroupOf (GlobalTheory.LeviDesc.parP a n w)) ⟨_, hγ⟩ (fun p => GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w n) f (p : GLw n w)) = twOrb (MonoidHom.id _) ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w (n - a))) m (GlobalTheory.LeviDesc.orbN (Nat.add_sub_cancel' ha) w f) := by
  first | exact @GlobalTheory.LeviDesc.twistedOrbitalIntegral_parabolic_unfolding | exact GlobalTheory.LeviDesc.twistedOrbitalIntegral_parabolic_unfolding | (intros; apply GlobalTheory.LeviDesc.twistedOrbitalIntegral_parabolic_unfolding <;> assumption)
end

