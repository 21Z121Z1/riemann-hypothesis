import Mathlib
import Formalism.RealPlaceAnalysis.Bundle0004
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0030
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0029
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0017
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0004
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0028
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CanonGaugeDmonOfHLIntegral
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0020
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBCorr
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.TorusExtensionPoints

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliDetMulVectorType
section
open Formalism.REAL Finset

namespace GlobalTheory

theorem qdet_mul_vector (A : Type) [Ring A] [Algebra ℂ A] (m : ℕ)
    (E : Fin (m + 1) → Fin (m + 1) → A) (x : Fin (m + 1) → A) (hE : GlRel E)
    (hx : ∀ a b j, E a b * x j = x j * E a b + if b = j then x a else 0)
    (u : ℂ) (j : Fin (m + 1)) :
    qdet E u * x j = x j * qdet E u + ∑ a : Fin (m + 1), ((-1 : ℂ) ^ ((a : ℕ) + (j : ℕ))) •
      (x a * qminor E (Fin.succAbove a) (Fin.succAbove j) (u - 1)) := by
  have h1 := GlobalTheory.T.capelli_left_comatrix_qminor_eq A m E hE u j j
  rw [if_pos rfl] at h1
  have h2 : ∀ a : Fin (m + 1), qminor E (Fin.succAbove a) (Fin.succAbove j) (u - 1) * x j
      = x j * qminor E (Fin.succAbove a) (Fin.succAbove j) (u - 1) := by
    intro a
    refine GlobalTheory.T.qminor_commute_of_commute_columns A (m + 1) m E (x j) _ _ _ ?_
    intro c i
    rw [hx, if_neg (Fin.succAbove_ne j i), add_zero]
  have h3 : ∀ a : Fin (m + 1), Tm E u a j * x j = x j * Tm E u a j + x a := by
    intro a
    have h := hx a j j
    rw [if_pos rfl] at h
    unfold Tm
    by_cases haj : a = j
    · simp only [if_pos haj, add_mul, mul_add, h, Algebra.commutes]
      abel
    · simp only [if_neg haj, zero_add, h]
  rw [← h1, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [smul_mul_assoc, mul_smul_comm, ← smul_add, mul_assoc, h2, ← mul_assoc, h3, add_mul,
    mul_assoc]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CompactCasimirLeSubspaceMonotoneStatement
section
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactCasimirLe_subspace_monotone : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M), KUnit ε E → (∀ c, CasKLe ε E c 0) ∧ (∀ c x y, CasKLe ε E c x → CasKLe ε E c y → CasKLe ε E c (x + y)) ∧ (∀ c (a : ℂ) x, CasKLe ε E c x → CasKLe ε E c (a • x)) ∧ ∀ c c' x, 0 ≤ c → c ≤ c' → CasKLe ε E c x → CasKLe ε E c' x := by
  first | exact @GlobalTheory.casKLe_subspace_mono | exact GlobalTheory.casKLe_subspace_mono | (intros; apply GlobalTheory.casKLe_subspace_mono <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CompactCasimirLeTensorOperatorRaiseStatement
section
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactCasimirLe_tensorOperator_raise : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (N ι : Type) [NormedAddCommGroup N] [InnerProductSpace ℂ N] [Fintype ι] [DecidableEq ι] (F : Fin n → Fin n → Module.End ℂ N) (φ : ι → M →ₗ[ℂ] N) (A : Fin n → Fin n → Matrix ι ι ℂ) (c s : ℝ), KUnit ε E → KUnit ε F → 0 ≤ c → 0 ≤ s → (∀ a b, ε a = ε b → (A a b).conjTranspose = A b a) → (∀ x : ι → M, ∑ a, ∑ b, (if ε a = ε b then ∑ i, ‖∑ j, A a b i j • x j‖ ^ 2 else 0) ≤ s ^ 2 * ∑ j, ‖x j‖ ^ 2) → (∀ a b, ε a = ε b → ∀ j w, F a b (φ j w) = φ j (E a b w) + ∑ i, A a b i j • φ i w) → ∀ w, CasKLe ε E c w → ∀ j, CasKLe ε F (c + s) (φ j w) := by
  first | exact @GlobalTheory.TensOp.casKLe_tensor_operator | exact GlobalTheory.TensOp.casKLe_tensor_operator | (intros; apply GlobalTheory.TensOp.casKLe_tensor_operator <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsEigenSplitOfResolventIdentityStatement
section
open Formalism.REAL Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eigenSplit_of_resolventIdentity : ∀ (N : Type) [AddCommGroup N] [Module ℂ N] (n : ℕ) (Ω : Module.End ℂ N) (X : ℂ → Module.End ℂ N) (d : ℕ) (c : ℕ → Module.End ℂ N) (ν : Fin n → ℂ), Function.Injective ν → (∀ u, X u = ∑ i ∈ Finset.range d, u ^ i • c i) → (∀ (u : ℂ) (w : N), u • X u w + Ω (X u w) = (∏ s, (u + ν s)) • w) → ∀ w : N, ∃ v : Fin n → N, w = ∑ s, v s ∧ ∀ s (u : ℂ), X u (v s) = (∏ t ∈ Finset.univ.erase s, (u + ν t)) • v s := by
  first | exact @GlobalTheory.exists_sum_eigen_split_of_resolvent | exact GlobalTheory.exists_sum_eigen_split_of_resolvent | (intros; apply GlobalTheory.exists_sum_eigen_split_of_resolvent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.GlRelNegTAndQdet
section
open Formalism.REAL Finset

namespace GlobalTheory.CapelliNegT

open Finset in

theorem _root_.GlobalTheory.CapelliNegT.glRel_negT_and_qdet :
    ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A), _root_.Formalism.REAL.GlRel E →
      _root_.Formalism.REAL.GlRel (fun a b => -E b a) ∧
        ∀ u : ℂ, _root_.Formalism.REAL.qdet (fun a b => -E b a) u = ((-1 : ℂ) ^ n) • _root_.Formalism.REAL.qdet E ((n : ℂ) - 1 - u) := by
  intro A _ _ n E hE
  refine ⟨?_, fun u => ?_⟩
  · unfold _root_.Formalism.REAL.GlRel at hE ⊢
    intro a b c d
    have h := hE b a d c
    rw [neg_mul_neg, neg_mul_neg, h]
    simp only [@eq_comm _ a d, @eq_comm _ c b]
    split_ifs <;> abel
  · have hrow : ∀ v : ℂ, _root_.Formalism.REAL.qdet E v = _root_.PI.qminorRow E id id v := by
      intro v
      have key : _root_.PI.RowForm := _root_.quantum_minor_row_form
      unfold _root_.PI.RowForm at key
      exact key A n n E hE id id v
    have hM : ∀ (x : ℂ) (a b : Fin n),
        _root_.Formalism.REAL.Tm (fun a b => -E b a) x a b = -_root_.Formalism.REAL.Tm E (-x) b a := by
      intro x a b
      unfold _root_.Formalism.REAL.Tm
      by_cases h : a = b
      · subst h
        simp only [if_true, map_neg]
        abel
      · simp only [h, Ne.symm h, if_false]
        abel
    have hneg : ∀ g : Fin n → A, (List.ofFn fun k => -g k).prod = (-1) ^ n * (List.ofFn g).prod := by
      intro g
      have hl : (List.ofFn fun k => -g k) = (List.ofFn g).map Neg.neg := by
        rw [List.map_ofFn]
        rfl
      rw [hl, List.prod_map_neg, List.length_ofFn]
    have harg : ∀ k : Fin n, -(u - ((k : ℕ) : ℂ)) = (n : ℂ) - 1 - u - n + 1 + ((k : ℕ) : ℂ) := by
      intro k
      ring
    rw [hrow]
    unfold _root_.Formalism.REAL.qdet _root_.Formalism.REAL.qminor _root_.PI.qminorRow
    rw [Algebra.smul_def, map_pow, map_neg, map_one, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [hM, hneg, harg, id]
    rw [← mul_assoc, ← mul_assoc, ((Commute.neg_one_right _).pow_right n).eq]

end GlobalTheory.CapelliNegT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvPowerSeriesEvalTsumOpenPolydiscPropertiesStatement
section
open GlobalTheory.ConvSer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mvPowerSeriesEvalTsum_openPolydisc_properties : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (σ : Type) [Fintype σ] (x : σ → K), (∀ i, ‖x i‖ < 1) → (∀ S : MvPowerSeries σ K, Bdd S → HS S x (ev S x)) ∧ (∀ S T : MvPowerSeries σ K, Bdd S → Bdd T → ev (S + T) x = ev S x + ev T x ∧ ev (S - T) x = ev S x - ev T x ∧ ev (S * T) x = ev S x * ev T x) ∧ (∀ a : K, ev (MvPowerSeries.C a : MvPowerSeries σ K) x = a) ∧ (∀ i, ev (MvPowerSeries.X i : MvPowerSeries σ K) x = x i) ∧ (∀ S : MvPowerSeries σ K, Intg S → ‖ev S x‖ ≤ 1 ∧ (Small S → ‖ev S x‖ < 1)) ∧ (∀ (ρ : Type) [Fintype ρ] (s : ρ → MvPowerSeries σ K) (S : MvPowerSeries ρ K), (∀ j, Small (s j)) → Bdd S → ev (csub s S) x = ev S (fun j => ev (s j) x)) ∧ (∀ (ρ : Type) [Fintype ρ] (a : ρ → MvPowerSeries σ K) (S : MvPowerSeries ρ K), (∀ j, Intg (a j)) → (∀ j, MvPowerSeries.constantCoeff (a j) = 0) → Bdd S → ev (MvPowerSeries.subst a S) x = ev S (fun j => ev (a j) x)) ∧ (∀ (a : MvPowerSeries σ K) (f : PowerSeries K), Intg a → MvPowerSeries.constantCoeff a = 0 → Bdd f → ev (f.subst a) x = ev1 f (ev a x)) := by
  first | exact @GlobalTheory.ConvSer.ev_algebra | exact GlobalTheory.ConvSer.ev_algebra | (intros; apply GlobalTheory.ConvSer.ev_algebra <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NabValColumnsCongr
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

namespace GlobalTheory.ColumnValue

theorem dmonOf_zero_index {k : Type} [CommRing k] {d : ℕ} (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι]
    (u : ι → Fin d → k) (g : PS k 1 d) : DmonOf F u 0 g = g := by
  unfold DmonOf
  induction (Finset.univ : Finset ι).toList with
  | nil => rfl
  | cons a L ih => rw [List.foldr_cons, ih]; rfl

theorem dmonOf_smul {k : Type} [CommRing k] {d : ℕ} (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι]
    (u : ι → Fin d → k) (mo : ι →₀ ℕ) (c : k) (g : PS k 1 d) :
    DmonOf F u mo (c • g) = C c * DmonOf F u mo g := by
  rw [smul_eq_C_mul]
  unfold DmonOf
  induction (Finset.univ : Finset ι).toList with
  | nil => rfl
  | cons a L ih => rw [List.foldr_cons, List.foldr_cons, ih, DerivEndo.iterate_dof_C_mul]

theorem column_value {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] {k : Type}
    [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d) (hh : B.IsCanonGauge k h)
    (w0 a : O) (N m : ℕ) (w : PS R 1 d)
    (hw : FB.toK k w = FB.expS k (ev (n := 1) ![B.actK k a] (B.hL k h w0) - (N : k) • B.hL k h w0))
    (I : Ideal R) {ι : Type} [Fintype ι] (u : ι → Fin d → R) (α : ι → R) (hI : ∀ l, α l ∈ I)
    (hα : ∀ l, (dAct k B a).mulVec (fun i => algebraMap R k (u l i)) =
      algebraMap R k (α l) • (fun i => algebraMap R k (u l i)))
    (hβ : ∀ l l', dotProduct (fun i => algebraMap R k (u l i)) ((bilinPart k h).mulVec
      ((dAct k B w0).mulVec (fun i => algebraMap R k (u l' i)))) ∈ (algebraMap R k).range)
    (f : PS R 1 d) (y : ι → R) (hf : ∀ l mo, coeff mo (Dof B.G.F (u l) f - C (y l) * f) ∈ I)
    (mo : ι →₀ ℕ) :
    ∃ s : R, s - (∏ l, y l ^ mo l) * constantCoeff f ∈ I ∧
      B.nabVal k h w0 (N * m) (FB.toK k (f * w ^ m)) (fun l i => algebraMap R k (u l i))
        (MvPolynomial.monomial mo 1) = algebraMap R k s := by
  have hA : ∀ b : O, GP (B.actK k b) := fun b => QuadDeriv.constantCoeff_mapP_eq_zero _ _ (B.A.const b)
  have hh0 : constantCoeff h = 0 := by
    have := congrArg constantCoeff hh.ax0
    rwa [gt_const_ev_eq _ (pair_points_zero_constant gp_zero₂ (gp_pt 0)), map_zero] at this
  have cL : constantCoeff (B.hL k h w0) = 0 :=
    gt_const_ev _ (pair_points_zero_constant (gp_pt 0) (gp_comp1 _ _ (hA w0) (gp_pt 0))) h hh0
  have cA : constantCoeff (ev (n := 1) ![B.actK k a] (B.hL k h w0)) = 0 :=
    gt_const_ev _ (single_point_zero_constant (hA a)) _ cL
  have cD : constantCoeff (ev (n := 1) ![B.actK k a] (B.hL k h w0) - (N : k) • B.hL k h w0) = 0 := by
    rw [map_sub, cA, nt_const_smul, cL, mul_zero, sub_zero]
  have hG : FB.toK k (f * w ^ m) * FB.expS k (((N * m : ℕ) : k) • B.hL k h w0) =
      FB.toK k f * FB.expS k ((m : k) • ev (n := 1) ![B.actK k a] (B.hL k h w0)) := by
    have e : FB.toK k (f * w ^ m) = FB.toK k f * FB.toK k w ^ m := by
      rw [FB.toK, map_mul, map_pow]
    rw [e, hw, PullbackColumn.expS_pow _ cD, mul_assoc,
      ← gt_expS_add _ _ (by rw [nt_const_smul, cD, mul_zero]) (by rw [nt_const_smul, cL, mul_zero]),
      smul_sub, smul_smul, Nat.cast_mul, mul_comm (N : k) (m : k), sub_add_cancel]
  have hφ : ∀ mo : ι →₀ ℕ, ∃ r ∈ I, constantCoeff (DmonOf (B.FK k) (fun l i => algebraMap R k (u l i)) mo
      ((m : k) • ev (n := 1) ![B.actK k a] (B.hL k h w0))) = algebraMap R k r := by
    intro mo
    rcases eq_or_ne mo 0 with rfl | hmo
    · exact ⟨0, I.zero_mem, by rw [dmonOf_zero_index, nt_const_smul, cA, mul_zero, map_zero]⟩
    · obtain ⟨l, hl⟩ := Finsupp.ne_iff.1 hmo
      obtain ⟨t, ht⟩ := canonGauge_dmonOf_hL_integral R d O k B h hh w0 ι u hβ mo
      refine ⟨(m : R) * ((∏ l, α l ^ mo l) * t), I.mul_mem_left _ (I.mul_mem_right _
        (Ideal.prod_mem I (Finset.mem_univ l) (I.pow_mem_of_mem (hI l) _ (Nat.pos_of_ne_zero hl)))), ?_⟩
      rw [dmonOf_smul, map_mul, constantCoeff_C,
        (invariantDeriv_along_endo R d O k B a).2 ι _ (fun l => algebraMap R k (α l)) hα mo, ← ht]
      simp only [map_mul, map_prod, map_pow, map_natCast]
  obtain ⟨r, hr, e⟩ := dmonOf_mul_expS_congr R d k B.G.F I ι u _
    (by rw [nt_const_smul, cA, mul_zero]) hφ f mo
  refine ⟨constantCoeff (DmonOf B.G.F u mo f) + r, ?_, ?_⟩
  · rw [add_sub_right_comm]
    exact I.add_mem (constantCoeff_dmonOf_sub_mem R d B.G.F I ι u y f hf mo) hr
  · unfold FB.nabVal
    rw [hG, PullbackColumn.dpolyOf_monomial_one]
    exact e

end GlobalTheory.ColumnValue

namespace GlobalTheory

open ColumnValue

theorem nabVal_columns_congr : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → ∀ (w0 a : O) (N m : ℕ) (w : PS R 1 d), FB.toK k w = FB.expS k (ev (n := 1) ![B.actK k a] (B.hL k h w0) - (N : k) • B.hL k h w0) → ∀ (I : Ideal R) (ι : Type) [Fintype ι] (u : ι → Fin d → R) (α : ι → R), (∀ l, α l ∈ I) → (∀ l, (dAct k B a).mulVec (fun i => algebraMap R k (u l i)) = algebraMap R k (α l) • (fun i => algebraMap R k (u l i))) → (∀ l l', dotProduct (fun i => algebraMap R k (u l i)) ((bilinPart k h).mulVec ((dAct k B w0).mulVec (fun i => algebraMap R k (u l' i)))) ∈ (algebraMap R k).range) → ∀ (n : ℕ) (f : Fin n → PS R 1 d) (y : ι × Fin n → R), (∀ l b mo, coeff mo (Dof B.G.F (u l) (f b) - C (y (l, b)) * f b) ∈ I) → ∀ P : MvPolynomial (ι × Fin n) R, ∃ r ∈ I, ∑ mo ∈ P.support, algebraMap R k (P.coeff mo) * ∏ b, B.nabVal k h w0 (N * m) (FB.toK k (f b * w ^ m)) (fun l i => algebraMap R k (u l i)) (MvPolynomial.monomial (colM mo b) 1) = algebraMap R k (MvPolynomial.eval y P * ∏ b, constantCoeff (f b) + r) := by
  intro R _ d O _ _ k _ _ _ B h hh w0 a N m w hw I ι _ u α hI hα hβ n f y hf P
  choose s hs he using fun (mo : ι × Fin n →₀ ℕ) (b : Fin n) =>
    column_value B h hh w0 a N m w hw I u α hI hα hβ (f b) (fun l => y (l, b)) (fun l => hf l b) (colM mo b)
  refine ⟨∑ mo ∈ P.support, P.coeff mo * ∏ b, s mo b -
    MvPolynomial.eval y P * ∏ b, constantCoeff (f b), ?_, ?_⟩
  · rw [MvPolynomial.eval_eq', Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine I.sum_mem fun mo _ => ?_
    rw [mul_assoc, ← mul_sub]
    refine I.mul_mem_left _ ?_
    rw [Fintype.prod_prod_type_right, ← Finset.prod_mul_distrib, ← Ideal.Quotient.eq, map_prod, map_prod]
    exact Finset.prod_congr rfl fun b _ => Ideal.Quotient.eq.2 (hs mo b)
  · rw [add_sub_cancel]
    simp only [he]
    simp only [map_sum, map_mul, map_prod]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.QkIsPullFLeftIff
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GtRestrictCompare

section General

variable {X Y Y' Z Z' : Scheme.{0}} {L : LB X}

theorem corr_pull_of_fac (hL : L.IsLB) {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {φ' : K' → (Y' ⟶ X)} {ε' : K' → ℤ} {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')}
    {a : Z ⟶ Y} {a' : Z ⟶ Y'} (H : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t a) (LB.pullGen L _ _ t' a'))
    (l : Z' ⟶ Z) {r : Z' ⟶ Y} {r' : Z' ⟶ Y'} (h : l ≫ a = r) (h' : l ≫ a' = r') :
    LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t r) (LB.pullGen L _ _ t' r') := by
  subst h h'
  exact corr_trans hL (corr_symm (corr_pullGen_comp t a l))
    (corr_trans hL (corr_pullGen H l) (corr_pullGen_comp t' a' l))

theorem corr_of_isEmpty [IsEmpty Y] {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε')) :
    LB.Gen.Corr L _ _ _ _ t t' := by
  intro j j' _ _ _
  have h : ∀ U : Y.Opens, Subsingleton Γ(Y, U) := fun U => by
    obtain rfl : U = ⊥ := by ext x; exact isEmptyElim x
    infer_instance
  exact Units.ext (Subsingleton.elim _ _)

theorem gen_eq_of_pull {φ : PUnit → (Y ⟶ X)} {ε : PUnit → ℤ} (t t' : LB.Gen (LB.LinComb L φ ε)) (h : Z ⟶ Y)
    (hinj : ∀ U : Y.Opens, Function.Injective (h.app U))
    (H : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t h) (LB.pullGen L _ _ t' h)) : t = t' := by
  obtain ⟨s⟩ := t
  obtain ⟨s'⟩ := t'
  congr 1
  funext j
  have e := H j j (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
  have hle : h ⁻¹ᵁ (LB.wchart L φ j) ≤
      LB.wchart L (fun k => h ≫ φ k) j ⊓ LB.wchart L (fun k => h ≫ φ k) j := fun _ hy =>
    ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k, Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k⟩
  have key : ∀ {U : Y.Opens} {A B : Z.Opens} (h₁ : h ⁻¹ᵁ U ≤ A) (h₂ : A ≤ B)
      (h₃ : B ≤ h ⁻¹ᵁ U) (s : Γ(Y, U)ˣ),
      ((res h₁ (res h₂ (res h₃ (pullU h U s))) : Γ(Z, h ⁻¹ᵁ U)ˣ) : Γ(Z, h ⁻¹ᵁ U)) = (h.app U).hom s := by
    intro U A B h₁ h₂ h₃ s
    change (h.app U ≫ Z.presheaf.map (homOfLE h₃).op ≫ Z.presheaf.map (homOfLE h₂).op ≫
      Z.presheaf.map (homOfLE h₁).op).hom s.1 = (h.app U).hom s.1
    rw [← Functor.map_comp, ← Functor.map_comp]
    erw [Z.presheaf.map_id]
    rw [Category.comp_id]
  refine Units.ext (hinj _ ?_)
  exact (key hle _ _ _).symm.trans ((congrArg (fun u => (res hle u).1) e).trans (key hle _ _ _))

end General

variable {R : Type} [CommRing R] [IsDomain R]

section Points

variable (D : DegPre R) (T : Over (Spec (CommRingCat.of R)))

def gtEquiv : GtPt D T ≃ IndefiniteRowSideFullHecke.TorusExtensionPoints.GtPt D T where
  toFun g := ⟨g.b, g.s, g.isGen, g.s_zero, g.mult⟩
  invFun g := ⟨g.b, g.s, g.isGen, g.s_zero, g.mult⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable {D T}

theorem isNsmul_iff (k : ℕ) (g h : GtPt D T) :
    GtPt.IsNsmul k g h ↔ IndefiniteRowSideFullHecke.TorusExtensionPoints.GtPt.IsNsmul k (gtEquiv D T g) (gtEquiv D T h) :=
  ⟨fun ⟨gs, a, b, c⟩ => ⟨fun i => gtEquiv D T (gs i), a, b, congrArg (gtEquiv D T) c⟩,
    fun ⟨gs, a, b, c⟩ => ⟨fun i => (gtEquiv D T).symm (gs i), a, b, congrArg (gtEquiv D T).symm c⟩⟩

variable {F : Type} [Field F] [Algebra (FractionRing R) F]

end Points

section OnOpen

variable {D : DegPre R} {W : (Spec (CommRingCat.of R)).Opens}

theorem psi_eq_iff (χ : D.X)
    (t : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (toUnit (TW W) ≫ D.c χ).left) (fun _ => -1))) :
    LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ t (jK R ∣_ W))
      (LB.pullGen D.P.L _ _ (D.psi χ) (jK R ⁻¹ᵁ W).ι) ↔
    ∀ j : TK R ⟶ IndefiniteRowSideFullHecke.TorusExtensionPoints.TU W, LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ t j.left) (D.psi χ) := by
  constructor
  · intro H j
    have h : j.left ≫ W.ι = 𝟙 _ ≫ jK R := (Over.w j).trans (Category.id_comp _).symm
    exact corr_trans D.P.isLB (corr_pull_of_fac D.P.isLB H ((isPullback_morphismRestrict (jK R) W).lift _ _ h)
      ((isPullback_morphismRestrict (jK R) W).lift_fst _ _ _)
      ((isPullback_morphismRestrict (jK R) W).lift_snd _ _ _)) (corr_pullGen_id _)
  · intro H
    rcases isEmpty_or_nonempty (jK R ⁻¹ᵁ W).toScheme with h | ⟨⟨y, hy⟩⟩
    · exact corr_of_isEmpty _ _
    · have hr : Set.range (jK R) ⊆ Set.range W.ι := by
        rintro _ ⟨z, rfl⟩
        rw [Scheme.Opens.range_ι, Subsingleton.elim z y]
        exact hy
      have hj : IsOpenImmersion.lift W.ι (jK R) hr ≫ W.ι = jK R := IsOpenImmersion.lift_fac _ _ _
      have H' := corr_trans D.P.isLB (H (Over.homMk (IsOpenImmersion.lift W.ι (jK R) hr) hj))
        (corr_symm (corr_pullGen_id _))
      refine corr_pull_of_fac D.P.isLB H' (jK R ⁻¹ᵁ W).ι ?_ (Category.comp_id _)
      change (jK R ⁻¹ᵁ W).ι ≫ IsOpenImmersion.lift W.ι (jK R) hr = _
      rw [← cancel_mono W.ι, Category.assoc, hj, morphismRestrict_ι]

variable (D W) in

def psiEquiv : PsiOn D W ≃ {ψ' : IndefiniteRowSideFullHecke.TorusExtensionPoints.PsiFam D W // IndefiniteRowSideFullHecke.TorusExtensionPoints.IsPsiExt D W ψ'} where
  toFun ψ := ⟨ψ.psi, fun χ => ⟨ψ.psi_gen χ, (psi_eq_iff χ _).1 (ψ.psi_eq χ)⟩⟩
  invFun ψ := ⟨ψ.1, fun χ => (ψ.2 χ).1, fun χ => (psi_eq_iff χ _).2 (ψ.2 χ).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem psiOn_unique (ψ ψ' : PsiOn D W) : ψ = ψ' := by
  have hd : IsDominant (jK R) := by
    refine ⟨?_⟩
    exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap R (FractionRing R))).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))]
      exact bot_le)
  have : IsSchemeTheoreticallyDominant (jK R) := .of_isDominant _
  have : IsSchemeTheoreticallyDominant (jK R ∣_ W) :=
    IsSchemeTheoreticallyDominant.of_isPullback (isPullback_morphismRestrict (jK R) W).flip
  have e : ψ.psi = ψ'.psi := funext fun χ => gen_eq_of_pull _ _ (jK R ∣_ W) (Scheme.Hom.app_injective _)
    (corr_trans D.P.isLB (ψ.psi_eq χ) (corr_symm (ψ'.psi_eq χ)))
  obtain ⟨a, _, _⟩ := ψ
  obtain ⟨b, _, _⟩ := ψ'
  obtain rfl : a = b := e
  rfl

theorem isIota_iff (ψ : PsiOn D W) {T : Over W.toScheme} (y : D.X) (g : GtPt D (overW W T)) :
    GtPt.IsIotaW ψ y g ↔ IndefiniteRowSideFullHecke.TorusExtensionPoints.GtPt.IsIota W y (gtEquiv D _ g) := by
  refine and_congr_right' ⟨fun h => ⟨Over.homMk T.hom rfl, ψ.psi, (psiEquiv D W ψ).2, h⟩, ?_⟩
  rintro ⟨u, ψ', h', h⟩
  obtain rfl : ψ = (psiEquiv D W).symm ⟨ψ', h'⟩ := psiOn_unique _ _
  have e : u.left = T.hom := (cancel_mono W.ι).1 (Over.w u)
  intro χ
  have := h χ
  rw [e] at this
  exact this

def qkEquiv (ψ : PsiOn D W) (k : ℕ) (T : Over W.toScheme) :
    QkPtW D W ψ k T ≃ IndefiniteRowSideFullHecke.TorusExtensionPoints.QkPtT D W (overW W T) k where
  toFun p := ⟨p.y, gtEquiv D _ p.g, by
    obtain ⟨h, a, b⟩ := p.eq
    exact ⟨gtEquiv D _ h, (isNsmul_iff k _ _).1 a, (isIota_iff ψ _ _).1 b⟩⟩
  invFun p := ⟨p.y, (gtEquiv D _).symm p.g, by
    obtain ⟨h, a, b⟩ := p.eq
    exact ⟨(gtEquiv D _).symm h, (isNsmul_iff k _ _).2 a, (isIota_iff ψ _ _).2 b⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable {ψ : PsiOn D W} {k : ℕ} {T : Over W.toScheme}

variable {F : Type} [Field F] [Algebra (FractionRing R) F]

end OnOpen

end GlobalTheory.GtRestrictCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightNearDiagonalOperatorsBoundsStatement
section
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightNear_diagonalOperators_bounds : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (Λ : Fin n → ℝ) (t : ℝ) (w : M), IsUnitary ε E → w ∈ WtNear E Λ t → (∀ m : ℝ, (∀ ω : Fin n → ℝ, ∑ a, |ω a - Λ a| ≤ t → m ≤ ∑ a, ω a ^ 2) → m * ‖w‖ ^ 2 ≤ ∑ a, ‖E a a w‖ ^ 2) ∧ (∀ (a : Fin n) (ζ : ℂ) (d : ℝ), 0 ≤ d → (∀ ω : Fin n → ℝ, ∑ a, |ω a - Λ a| ≤ t → d ≤ ‖ζ + (ω a : ℂ)‖) → d ^ 2 * ‖w‖ ^ 2 ≤ ‖ζ • w + E a a w‖ ^ 2) ∧ ∀ (a : Fin n) (D : ℝ), (∀ ω : Fin n → ℝ, ∑ a, |ω a - Λ a| ≤ t → |ω a| ≤ D) → ‖E a a w‖ ^ 2 ≤ D ^ 2 * ‖w‖ ^ 2 := by
  first | exact @GlobalTheory.wtNear_diag_bounds | exact GlobalTheory.wtNear_diag_bounds | (intros; apply GlobalTheory.wtNear_diag_bounds <;> assumption)
end

