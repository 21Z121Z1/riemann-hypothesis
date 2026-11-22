import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0943
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0212
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0158
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0311
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0168
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0159
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0300
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0301
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0277
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0291
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0278
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0287
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0302
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsRealThetaParameterPairThetaPartnerSignedParame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0303
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergOperatorPureTensorPlaceByPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceTensorHeis

open GlobalTheory.SplitScalar GlobalTheory.LatVac

variable {D : D7} {S T : HSp D}

theorem wAt_wAt (p : Place D) (w : WO S T) : wAt p (wAt p w) = wAt p w := by
  rw [wAt_eq_smul, wAt_eq_smul, smul_smul, (GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D).1 p]

theorem wAt_wAt_ne {p q : Place D} (h : p ≠ q) (w : WO S T) : wAt p (wAt q w) = 0 := by
  rw [wAt_eq_smul, wAt_eq_smul, smul_smul, (GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D).2.1 p q h, zero_smul]

theorem wAt_off {P : Finset (Place D)} {w r : WO S T} (h : w = ∑ q ∈ P, wAt q w + r) {p : Place D} (hp : p ∉ P) :
    wAt p w = wAt p r := by
  have e : wAt p w = wAt p (∑ q ∈ P, wAt q w + r) := by rw [← h]
  simp only [wAt_eq_smul, smul_add, Finset.smul_sum, smul_smul] at e ⊢
  rw [e, Finset.sum_eq_zero, zero_add]
  intro q hq
  rw [(GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D).2.1 p q (fun hpq => hp (hpq ▸ hq)), zero_smul]

theorem wAt_on {P : Finset (Place D)} {w r : WO S T} (h : w = ∑ q ∈ P, wAt q w + r) {p : Place D} (hp : p ∈ P) :
    wAt p r = 0 := by
  have e : wAt p w = wAt p (∑ q ∈ P, wAt q w + r) := by rw [← h]
  simp only [wAt_eq_smul, smul_add, Finset.smul_sum, smul_smul] at e ⊢
  rw [Finset.sum_eq_single p (fun q _ hqp => by rw [(GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D).2.1 p q (Ne.symm hqp), zero_smul])
    (fun hn => absurd hp hn), (GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D).1 p] at e
  exact add_left_cancel (e.symm.trans (add_zero _).symm)

theorem symplO_wAt (p : Place D) (x y : WO S T) : symplO S T (wAt p x) y = symplO S T x (wAt p y) := by
  rw [wAt_eq_smul, wAt_eq_smul, GlobalTheory.SplitScalar.symplO_smul, (GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D).2.2.1 p]

private theorem symplO_sum_wAt_left (P : Finset (Place D)) (x y : WO S T) :
    symplO S T (∑ q ∈ P, wAt q x) y = ∑ q ∈ P, symplO S T (wAt q x) (wAt q y) := by
  induction P using Finset.cons_induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, GlobalTheory.SplitScalar.symplO_zero_left]
  | cons a s ha ih =>
    rw [Finset.sum_cons, Finset.sum_cons, GlobalTheory.LatVac.symplO_add_left, ih, ← symplO_wAt, wAt_wAt]

private theorem wAt_add' (p : Place D) (x y : WO S T) : wAt p (x + y) = wAt p x + wAt p y := by
  rw [wAt_eq_smul, wAt_eq_smul, wAt_eq_smul, smul_add]

theorem symplO_split {P : Finset (Place D)} {w r w' r' : WO S T} (h : w = ∑ q ∈ P, wAt q w + r)
    (h' : w' = ∑ q ∈ P, wAt q w' + r') :
    symplO S T w w' = ∑ q ∈ P, symplO S T (wAt q w) (wAt q w') + symplO S T r r' := by
  have hr : ∀ q ∈ P, wAt q r = 0 := fun q hq => wAt_on h hq
  have hr' : ∀ q ∈ P, wAt q r' = 0 := fun q hq => wAt_on h' hq
  have hB : ∀ q ∈ P, wAt q (∑ q' ∈ P, wAt q' w') = wAt q w' := by
    intro q hq
    have e : wAt q w' = wAt q (∑ q' ∈ P, wAt q' w' + r') := by rw [← h']
    rw [wAt_add', hr' q hq, add_zero] at e
    exact e.symm
  have s1 : ∑ q ∈ P, symplO S T (wAt q w) (wAt q (∑ q' ∈ P, wAt q' w')) =
      ∑ q ∈ P, symplO S T (wAt q w) (wAt q w') :=
    Finset.sum_congr rfl fun q hq => by rw [hB q hq]
  have s2 : ∑ q ∈ P, symplO S T (wAt q w) (wAt q r') = 0 :=
    Finset.sum_eq_zero fun q hq => by rw [hr' q hq, GlobalTheory.SplitScalar.symplO_zero_right]
  have s3 : ∑ q ∈ P, symplO S T (wAt q w') (wAt q r) = 0 :=
    Finset.sum_eq_zero fun q hq => by rw [hr q hq, GlobalTheory.SplitScalar.symplO_zero_right]
  conv_lhs => rw [h, h']
  rw [GlobalTheory.LatVac.symplO_add_left, GlobalTheory.LatVac.symplO_add_right, GlobalTheory.LatVac.symplO_add_right,
    symplO_sum_wAt_left, symplO_sum_wAt_left, GlobalTheory.SplitScalar.symplO_skew S T (∑ q ∈ P, wAt q w') r,
    symplO_sum_wAt_left, s1, s2, s3, add_zero, neg_zero, zero_add]

variable {ψ : AddChar (AF D.host.F) ℂ}
  {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

theorem cocycle_two (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {u u' : WO S T}
    (hu : u ∈ latO S T ΛS ΛT fun _ => True) (hu' : u' ∈ latO S T ΛS ΛT fun _ => True) :
    ψ (symplOH S T (2 • u) (2 • u')) = 1 := by
  have hd : ψ (symplO S T u u') = 1 :=
    ((GlobalTheory.T.self_dual_lattice_pairing_dual D ψ S T ΛS ΛT hψ hS hT).1 u (GlobalTheory.SplitScalar.latO_fin hu)).mp hu u' hu'
  rw [two_nsmul, two_nsmul, GlobalTheory.SplitScalar.symplOH_add_left, GlobalTheory.SplitScalar.symplOH_add_right,
    GlobalTheory.SplitScalar.symplOH_add_self, AddChar.map_add_eq_mul, hd, one_mul]

theorem wAt_mem {u : WO S T} (hu : u ∈ latO S T ΛS ΛT fun _ => True) (p : Place D) :
    wAt p u ∈ latO S T ΛS ΛT fun _ => True :=
  latO_mono (fun _ _ => trivial) (GlobalTheory.T.weilMatrixComponentAtPlace_mem_completedLattice D S T ΛS ΛT _ u hu p).1

theorem wAt_two (p : Place D) (u : WO S T) : wAt p (2 • u) = 2 • wAt p u := by
  rw [two_nsmul, two_nsmul, wAt_eq_smul, wAt_eq_smul, smul_add]

private theorem eq_zero_of_add_self_eq_zero_AF {a : AF D.host.F} (h : a + a = 0) : a = 0 := by
  have h2 : IsUnit (2 : AF D.host.F) := by
    rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2]
    exact (IsUnit.mk0 (2 : D.host.F) two_ne_zero).map _
  rw [← two_mul] at h
  exact h2.mul_right_eq_zero.mp h

private theorem symplOH_eq_sum_wAt_add_of_decomp {P : Finset (Place D)} {w r w' r' : WO S T} (h : w = ∑ q ∈ P, wAt q w + r)
    (h' : w' = ∑ q ∈ P, wAt q w' + r') :
    symplOH S T w w' = ∑ q ∈ P, symplOH S T (wAt q w) (wAt q w') + symplOH S T r r' := by
  apply sub_eq_zero.mp
  apply eq_zero_of_add_self_eq_zero_AF
  rw [sub_add_sub_comm, GlobalTheory.SplitScalar.symplOH_add_self, add_add_add_comm, ← Finset.sum_add_distrib]
  simp only [GlobalTheory.SplitScalar.symplOH_add_self]
  rw [symplO_split h h', sub_self]

private theorem addChar_sum_eq_prod' (ψ : AddChar (AF D.host.F) ℂ) (s : Finset (Place D)) (g : Place D → AF D.host.F) :
    ψ (∑ p ∈ s, g p) = ∏ p ∈ s, ψ (g p) := by
  induction s using Finset.cons_induction with
  | empty => rw [Finset.sum_empty, Finset.prod_empty, AddChar.map_zero_eq_one]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.prod_cons, AddChar.map_add_eq_mul, ih]

theorem cocycle_prod (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (w w' : WO S T) :
    ∃ P : Finset (Place D), (∀ p ∉ P, ψ (symplOH S T (wAt p w) (wAt p w')) = 1) ∧
      ψ (symplOH S T w w') = ∏ p ∈ P, ψ (symplOH S T (wAt p w) (wAt p w')) := by
  classical
  obtain ⟨P₀, hP₀⟩ := GlobalTheory.T.exists_eq_sum_weilComponents_add_two_smul_lattice D S T ΛS ΛT hS hT w
  obtain ⟨P₁, hP₁⟩ := GlobalTheory.T.exists_eq_sum_weilComponents_add_two_smul_lattice D S T ΛS ΛT hS hT w'
  obtain ⟨u, hu, hw⟩ := hP₀ (P₀ ∪ P₁) (fun _ hx => Finset.mem_union_left _ hx)
  obtain ⟨u', hu', hw'⟩ := hP₁ (P₀ ∪ P₁) (fun _ hx => Finset.mem_union_right _ hx)
  refine ⟨P₀ ∪ P₁, fun p hp => ?_, ?_⟩
  · rw [wAt_off hw hp, wAt_off hw' hp, wAt_two, wAt_two]
    exact cocycle_two hψ hS hT (wAt_mem hu p) (wAt_mem hu' p)
  · rw [symplOH_eq_sum_wAt_add_of_decomp hw hw', AddChar.map_add_eq_mul, cocycle_two hψ hS hT hu hu', mul_one,
      addChar_sum_eq_prod']

theorem isPure_heisO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (x : Place D → WO S T → ℂ) (f : WO S T → ℂ), IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f → ∀ w : WO S T, IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ (fun p => heisO ψ S T (wAt p w) (x p)) (heisO ψ S T w f) := by
  intro D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ x f hx w
  classical
  have hψ := base_std hB
  have hθ := base_inf hB
  have hf₀ := base_theta hB
  have hB' := hB
  unfold IsBase at hB'
  have hS : IsSelfDualC S ΛS := hB'.2.2.1
  have hT : IsSelfDualC T ΛT := hB'.2.2.2.1
  have laws := GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T
  unfold IsPure IsRestricted at hx ⊢
  obtain ⟨⟨hloc, hfin⟩, hf, hprod⟩ := hx
  have hxθ : ∀ p, IsThetaFunO ψ S T (x p) := fun p => by
    have hl := hloc p
    unfold IsLocal at hl
    exact hl.1
  have hneg : ∀ (p : Place D) (a : WO S T), wAt p (-a) = -wAt p a := fun p a => by
    rw [wAt_eq_smul, wAt_eq_smul, smul_neg]
  have hadd : ∀ (p : Place D) (a b : WO S T), wAt p (a + b) = wAt p a + wAt p b := fun p a b => by
    rw [wAt_eq_smul, wAt_eq_smul, wAt_eq_smul, smul_add]

  obtain ⟨P₀, hP₀⟩ := GlobalTheory.T.exists_eq_sum_weilComponents_add_two_smul_lattice D S T ΛS ΛT hS hT w
  obtain ⟨u, hu, hwu⟩ := hP₀ P₀ (Finset.Subset.refl _)
  have hvac : ∀ p, p ∉ P₀ → (∀ τ, p ≠ .inr τ) → heisO ψ S T (wAt p w) f₀ = f₀ := by
    intro p hp hτ
    rcases p with v | τ
    · have hv : IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun u => u = v) f₀ := base_vacAt hB (.inl v)
      rw [wAt_off hwu hp, wAt_two]
      refine hv.1 _ (latO_mono ?_ (GlobalTheory.T.weilMatrixComponentAtPlace_mem_completedLattice D S T ΛS ΛT _ u hu (.inl v)).1)
      rintro v' ⟨-, hv'⟩
      exact Sum.inl_injective hv'
    · exact absurd rfl (hτ τ)
  have hfinV : {p : Place D | heisO ψ S T (wAt p w) f₀ ≠ f₀}.Finite := by
    refine ((P₀.finite_toSet).union (Set.finite_range (Sum.inr : D.what₂.Tau → Place D))).subset ?_
    intro p hp
    by_contra hc
    simp only [Set.mem_union, Finset.mem_coe, Set.mem_range, not_or, not_exists] at hc
    exact hp (hvac p hc.1 fun τ h => hc.2 τ h.symm)
  refine ⟨⟨fun p => ((GlobalTheory.T.fockVacua_localFactors_stable_heisenberg_away D ψ θ S T sS sT ΛS ΛT hψ hθ (x p) (hxθ p)).2 p (hloc p)).1 w, ?_⟩,
    laws.1 w f hf, fun w' => ?_⟩
  · refine (hfin.union hfinV).subset ?_
    intro p hp
    by_contra hc
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc
    apply hp
    show heisO ψ S T (wAt p w) (x p) = f₀
    rw [hc.1, hc.2]

  have hfac : ∀ p, ipO μ 𝓕 (heisO ψ S T (wAt p w) (x p)) (heisO ψ S T (wAt p w') f₀) =
      (starRingEnd ℂ) (ψ (symplOH S T (wAt p (-w)) (wAt p w'))) *
        ipO μ 𝓕 (x p) (heisO ψ S T (wAt p (-w + w')) f₀) := by
    intro p
    have I := GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 hψ hμ (x p) (heisO ψ S T (wAt p (-w + w')) f₀) (hxθ p) (laws.1 _ f₀ hf₀)
    have J := GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 hψ hμ (x p) (heisO ψ S T (wAt p w') f₀) (hxθ p) (laws.1 _ f₀ hf₀)
    rw [(J.2.2.2.2.2.2.1 (wAt p w)).2, laws.2.1, ← hneg, ← hadd, (I.2.2.1 _).2]
  obtain ⟨P, hP1, hP2⟩ := cocycle_prod hψ hS hT (-w) w'
  have hcfin : (Function.mulSupport fun p => (starRingEnd ℂ) (ψ (symplOH S T (wAt p (-w)) (wAt p w')))) ⊆ ↑P := by
    intro p hp
    by_contra hc
    simp only [Function.mem_mulSupport] at hp
    exact hp (by rw [hP1 p (fun h => hc (Finset.mem_coe.mpr h)), map_one])
  have hgfin := (hprod (-w + w')).1
  beta_reduce
  simp only [hfac]
  refine ⟨((P.finite_toSet.subset hcfin).union hgfin).subset (Function.mulSupport_mul _ _), ?_⟩
  have K0 := GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 hψ hμ f (heisO ψ S T w' f₀) hf (laws.1 _ _ hf₀)
  have K1 := GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 hψ hμ f (heisO ψ S T (-w + w') f₀) hf (laws.1 _ _ hf₀)
  rw [(K0.2.2.2.2.2.2.1 w).2, laws.2.1, (K1.2.2.1 _).2, (hprod (-w + w')).2, hP2, map_prod,
    finprod_mul_distrib (P.finite_toSet.subset hcfin) hgfin, finprod_eq_prod_of_mulSupport_subset _ hcfin]

end GlobalTheory.PlaceTensorHeis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableGaussianExpLinearNormTermComplexMatrixStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_gaussian_exp_linear_norm_term_complex_matrix : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (c : ι → ℝ), (∀ τ, 0 < c τ) → ∀ z₀ : VCx ι a b, Integrable fun z : VCx ι a b => Real.exp ((∑ k : DVar ι a b, ‖(c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2‖ * ‖z k.1 k.2.1 k.2.2‖) - gq c z / 2) := by
  first | exact @GlobalTheory.FockTransl.integrable_exp_lin_sub_gq | exact GlobalTheory.FockTransl.integrable_exp_lin_sub_gq | (intros; apply GlobalTheory.FockTransl.integrable_exp_lin_sub_gq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralFundamentalDomainEqIteratedDecompStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_fundamentalDomain_eq_iterated_decomp : ∀ (D : D7) (V W : HSp D) (a b k : ℕ) (f₁ f₃ : Mx D a b → WO V W) (f₂ : Mx D 1 k → WO V W), Continuous f₁ → Continuous f₂ → Continuous f₃ → (∀ s s', f₁ (s + s') = f₁ s + f₁ s') → (∀ z z', f₂ (z + z') = f₂ z + f₂ z') → (∀ y y', f₃ (y + y') = f₃ y + f₃ y') → (∀ x : WO V W, ∃ s z y, x = f₁ s + f₂ z + f₃ y) → (∀ s z y, f₁ s + f₂ z + f₃ y = 0 → s = 0 ∧ z = 0 ∧ y = 0) → (∀ s z y, f₁ s + f₂ z + f₃ y ∈ ratL W V ↔ s ∈ GlobalTheory.MixModel.ratMx D a b ∧ z ∈ GlobalTheory.MixModel.ratMx D 1 k ∧ y ∈ GlobalTheory.MixModel.ratMx D a b) → ∀ (μ : Measure (Mx D a b)) (𝓨 : Set (Mx D a b)), IsCovolOne (GlobalTheory.MixModel.ratMx D a b) μ 𝓨 → ∀ (η : Measure (Mx D 1 k)) (𝓩 : Set (Mx D 1 k)), η.IsAddHaarMeasure → IsAddFundamentalDomain (GlobalTheory.MixModel.ratMx D 1 k) 𝓩 η → ∀ (ν : Measure (WO V W)) (𝓕 : Set (WO V W)), ν.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 ν → ∃ κ : ℝ, 0 < κ ∧ ∀ T : WO V W → ℂ, Continuous T → (∀ γ ∈ ratL W V, ∀ u, T (γ + u) = T u) → ∫ u in 𝓕, T u ∂ν = κ * ∫ s in 𝓨, (∫ z in 𝓩, (∫ y in 𝓨, T (f₁ s + f₂ z + f₃ y) ∂μ) ∂η) ∂μ := by
  first | exact @GlobalTheory.CoordUnfold.integral_fundamentalDomain_eq_iterated | exact GlobalTheory.CoordUnfold.integral_fundamentalDomain_eq_iterated | (intros; apply GlobalTheory.CoordUnfold.integral_fundamentalDomain_eq_iterated <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralHomFundamentalDomainIsotropicSplitCoords
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistHaar

open scoped Pointwise

theorem isAddFundamentalDomain_prod {A B : Type*} [AddGroup A] [AddGroup B] [MeasurableSpace A]
    [MeasurableSpace B] {Γ : AddSubgroup A} {Δ : AddSubgroup B} {μ : Measure A} {ν : Measure B} [SFinite μ]
    [SFinite ν] {s : Set A} {t : Set B} (hs : IsAddFundamentalDomain Γ s μ) (ht : IsAddFundamentalDomain Δ t ν) :
    IsAddFundamentalDomain (Γ.prod Δ) (s ×ˢ t) (μ.prod ν) where
  nullMeasurableSet := hs.nullMeasurableSet.prod ht.nullMeasurableSet
  ae_covers := by
    have h1 := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae hs.ae_covers
    have h2 := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae ht.ae_covers
    filter_upwards [h1, h2] with p hp hq
    obtain ⟨g, hg⟩ := hp
    obtain ⟨h, hh⟩ := hq
    exact ⟨⟨((g : A), (h : B)), AddSubgroup.mem_prod.2 ⟨g.2, h.2⟩⟩, hg, hh⟩
  aedisjoint := by
    intro g h hgh
    change μ.prod ν ((g +ᵥ s ×ˢ t) ∩ (h +ᵥ s ×ˢ t)) = 0
    let g1 : Γ := ⟨(g : A × B).1, (AddSubgroup.mem_prod.1 g.2).1⟩
    let h1 : Γ := ⟨(h : A × B).1, (AddSubgroup.mem_prod.1 h.2).1⟩
    let g2 : Δ := ⟨(g : A × B).2, (AddSubgroup.mem_prod.1 g.2).2⟩
    let h2 : Δ := ⟨(h : A × B).2, (AddSubgroup.mem_prod.1 h.2).2⟩
    by_cases e1 : g1 = h1
    · have e2 : g2 ≠ h2 := fun e2 => hgh (Subtype.ext (Prod.ext (congrArg Subtype.val e1) (congrArg Subtype.val e2)))
      have h0 : ν ((g2 +ᵥ t) ∩ (h2 +ᵥ t)) = 0 := ht.aedisjoint e2
      refine measure_mono_null (t := Set.univ ×ˢ ((g2 +ᵥ t) ∩ (h2 +ᵥ t))) ?_ ?_
      · rintro p ⟨hp1, hp2⟩
        rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hp1 hp2
        refine ⟨Set.mem_univ _, ?_, ?_⟩
        · rw [Set.mem_vadd_set_iff_neg_vadd_mem]; exact hp1.2
        · rw [Set.mem_vadd_set_iff_neg_vadd_mem]; exact hp2.2
      · rw [Measure.prod_prod, h0, mul_zero]
    · have h0 : μ ((g1 +ᵥ s) ∩ (h1 +ᵥ s)) = 0 := hs.aedisjoint e1
      refine measure_mono_null (t := ((g1 +ᵥ s) ∩ (h1 +ᵥ s)) ×ˢ Set.univ) ?_ ?_
      · rintro p ⟨hp1, hp2⟩
        rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hp1 hp2
        refine ⟨⟨?_, ?_⟩, Set.mem_univ _⟩
        · rw [Set.mem_vadd_set_iff_neg_vadd_mem]; exact hp1.1
        · rw [Set.mem_vadd_set_iff_neg_vadd_mem]; exact hp2.1
      · rw [Measure.prod_prod, h0, zero_mul]

end GlobalTheory.TwistHaar

namespace GlobalTheory.TwistHaar

open scoped Pointwise

set_option maxHeartbeats 1000000 in

theorem integral_fundamentalDomain_eq_iterated : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ (μV : Measure (WO V W)) (𝓕V : Set (WO V W)), μV.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕V μV → ∀ (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), μ'.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V') 𝓕' μ' → ∃ κ : ℝ, 0 < κ ∧ (∀ H : WO V W → ℂ, Continuous H → (∃ b : ℝ, ∀ w, ‖H w‖ ≤ b) → (∀ γ ∈ ratL W V, ∀ w, H (γ + w) = H w) → ∫ w in 𝓕V, H w ∂μV = κ • ∫ t in 𝓨, ∫ y in 𝓨, ∫ x in 𝓕', H (isoPart V W C' t + isoPart V W C y + midPart V V' W B x) ∂μ' ∂μ ∂μ) := by
  intro D V V' W r C B hs C' h1 h2 h3 μ 𝓨 hY μV 𝓕V hμV hFV μ' 𝓕' hμ' hF'
  obtain ⟨e, he, hrat⟩ := GlobalTheory.T.exists_homSpace_dual_isotropic_middle_decomposition D V V' W r C B hs C' h1 h2 h3
  obtain ⟨a1, a2, a3, a4, a5, -⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank r
  obtain ⟨b1, b2, b3, b4, b5, -⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank V'.rank
  obtain ⟨c1, c2, c3, c4, c5, -⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank V.rank
  have : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  have : BorelSpace (WO V' W) := ⟨rfl⟩
  have : BorelSpace (WO V W) := ⟨rfl⟩
  have : DiscreteTopology (ratMx D W.rank r) := a5
  have : DiscreteTopology (ratL W V') := b5
  have : DiscreteTopology (ratL W V) := c5
  have cA : Countable (ratMx D W.rank r) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have cB : Countable (ratL W V') := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have : μ.IsAddHaarMeasure := hY.1

  set Γ' : AddSubgroup (Mx D W.rank r × Mx D W.rank r × WO V' W) :=
    (ratMx D W.rank r).prod ((ratMx D W.rank r).prod (ratL W V')) with hΓ'
  have hmem : ∀ p, e p ∈ ratL W V ↔ p ∈ Γ' := by
    rintro ⟨t, y, x⟩
    rw [hrat]
    simp [Γ', AddSubgroup.mem_prod]
  have : Countable Γ' := Function.Injective.countable
    (f := fun g : Γ' => ((⟨(g : Mx D W.rank r × Mx D W.rank r × WO V' W).1, (AddSubgroup.mem_prod.1 g.2).1⟩ :
        ratMx D W.rank r),
      (⟨(g : Mx D W.rank r × Mx D W.rank r × WO V' W).2.1, (AddSubgroup.mem_prod.1 (AddSubgroup.mem_prod.1 g.2).2).1⟩ :
        ratMx D W.rank r),
      (⟨(g : Mx D W.rank r × Mx D W.rank r × WO V' W).2.2, (AddSubgroup.mem_prod.1 (AddSubgroup.mem_prod.1 g.2).2).2⟩ :
        ratL W V')))
    fun g h hgh => by
      simp only [Prod.mk.injEq, Subtype.mk.injEq] at hgh
      exact Subtype.ext (Prod.ext hgh.1 (Prod.ext hgh.2.1 hgh.2.2))
  set P : Measure (Mx D W.rank r × Mx D W.rank r × WO V' W) := μ.prod (μ.prod μ') with hP
  have hT : IsAddFundamentalDomain Γ' (𝓨 ×ˢ (𝓨 ×ˢ 𝓕')) P :=
    isAddFundamentalDomain_prod hY.2.1 (isAddFundamentalDomain_prod hY.2.1 hF')
  set m : Measure (WO V W) := P.map e with hm
  have : (μ.prod μ').IsAddHaarMeasure := inferInstance
  have : P.IsAddHaarMeasure := inferInstance
  have : m.IsAddHaarMeasure := e.isAddHaarMeasure_map P
  have : VAddInvariantMeasure Γ' (Mx D W.rank r × Mx D W.rank r × WO V' W) P :=
    ⟨fun g s _ => measure_preimage_add P (g : Mx D W.rank r × Mx D W.rank r × WO V' W) s⟩
  set c : NNReal := μV.addHaarScalarFactor m with hcdef
  have hc : μV = c • m := Measure.isAddLeftInvariant_eq_smul μV m
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hc
    exact (NeZero.ne μV) hc
  have hac : m ≪ μV := fun s hs0 => by
    rw [hc, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at hs0
    exact (mul_eq_zero.1 hs0).resolve_left (by simpa using hc0)
  have hFm : IsAddFundamentalDomain (ratL W V) 𝓕V m := hFV.mono hac
  have hemeas : Measurable e := e.continuous.measurable
  have hpre : IsAddFundamentalDomain Γ' (e ⁻¹' 𝓕V) P := by
    refine hFm.preimage_of_equiv (f := e) (MeasurePreserving.quasiMeasurePreserving ⟨hemeas, rfl⟩)
      (e := fun g => ⟨e.symm g, (hmem _).1 (by simpa using g.2)⟩) ⟨fun g h hgh => ?_, fun g => ?_⟩ fun g x => ?_
    · exact Subtype.ext (e.symm.injective (congrArg Subtype.val hgh))
    · exact ⟨⟨e g, (hmem g).2 g.2⟩, Subtype.ext (by simp)⟩
    · change e (e.symm g + x) = (g : WO V W) + e x
      rw [map_add, ContinuousAddEquiv.apply_symm_apply]
  have hfin : μ' 𝓕' ≠ ⊤ := (GlobalTheory.Size.measure_dom hμ' hF').2
  have : IsFiniteMeasure (μ.restrict 𝓨) := ⟨by rw [Measure.restrict_apply_univ, hY.2.2]; exact ENNReal.one_lt_top⟩
  have : IsFiniteMeasure (μ'.restrict 𝓕') := ⟨by rw [Measure.restrict_apply_univ]; exact hfin.lt_top⟩
  refine ⟨(c : ℝ), NNReal.coe_pos.2 (pos_iff_ne_zero.2 hc0), fun H hH hb hper => ?_⟩
  obtain ⟨b, hb⟩ := hb
  have hmeasH : Measurable (fun p => H (e p)) := (hH.comp e.continuous).measurable
  have step1 : ∫ w in 𝓕V, H w ∂μV = (c : ℝ) • ∫ w in 𝓕V, H w ∂m := by
    have : μV = (c : ENNReal) • m := by rw [hc]; rfl
    rw [this, Measure.restrict_smul, integral_smul_measure, ENNReal.coe_toReal]
  have step2 : ∫ w in 𝓕V, H w ∂m = ∫ p in e ⁻¹' 𝓕V, H (e p) ∂P :=
    (e.toHomeomorph.toMeasurableEquiv.measurableEmbedding).setIntegral_map H 𝓕V
  have step3 : ∫ p in e ⁻¹' 𝓕V, H (e p) ∂P = ∫ p in 𝓨 ×ˢ (𝓨 ×ˢ 𝓕'), H (e p) ∂P :=
    hpre.setIntegral_eq hT (f := fun p => H (e p)) fun g p => by
      change H (e ((g : Mx D W.rank r × Mx D W.rank r × WO V' W) + p)) = H (e p)
      rw [map_add]
      exact hper _ ((hmem g).2 g.2) _
  have r1 : (μ.prod (μ.prod μ')).restrict (𝓨 ×ˢ (𝓨 ×ˢ 𝓕')) =
      (μ.restrict 𝓨).prod ((μ.restrict 𝓨).prod (μ'.restrict 𝓕')) :=
    ((congrArg (Measure.prod (μ.restrict 𝓨)) (Measure.prod_restrict 𝓨 𝓕')).trans
      (Measure.prod_restrict 𝓨 (𝓨 ×ˢ 𝓕'))).symm
  have step4 : ∫ p in 𝓨 ×ˢ (𝓨 ×ˢ 𝓕'), H (e p) ∂P = ∫ t in 𝓨, ∫ y in 𝓨, ∫ x in 𝓕',
      H (isoPart V W C' t + isoPart V W C y + midPart V V' W B x) ∂μ' ∂μ ∂μ := by
    refine (congrArg (fun ν => ∫ p, H (e p) ∂ν) r1).trans ?_
    refine (integral_prod _ (Integrable.of_bound hmeasH.aestronglyMeasurable b
      (Filter.Eventually.of_forall fun p => hb _))).trans ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    refine (integral_prod (fun q => H (e (t, q))) (Integrable.of_bound
      (hmeasH.comp measurable_prodMk_left).aestronglyMeasurable b (Filter.Eventually.of_forall fun p => hb _))).trans ?_
    simp only [he]
  exact step1.trans (congrArg (fun z : ℂ => (c : ℝ) • z) ((step2.trans step3).trans step4))

end GlobalTheory.TwistHaar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralLeviPhaseChangeOfVariables
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LeviNorm

variable {D : D7}

def sandwichHomeo {m n : ℕ} (P : GL (Fin m) (AE D)) (Q : GL (Fin n) (AE D)) : Mx D m n ≃ₜ Mx D m n where
  toFun u := HMul.hMul (HMul.hMul P.val u) Q.val
  invFun v := HMul.hMul (HMul.hMul (P⁻¹).val v) (Q⁻¹).val
  left_inv u := by
    simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  right_inv v := by
    simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
    rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

theorem phase_sandwich (ψ : AddChar (AF D.host.F) ℂ) (W : HSp D) {r : ℕ} (h : GA D W) (a : GL (Fin r) (AE D))
    (y u : Mx D W.rank r) :
    phase ψ W (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) y) (GlobalTheory.MixModel.adj (a⁻¹).val))
      (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) u) a.val) = phase ψ W y u := by
  rw [phase_apply, phase_apply]
  congr 3
  have hu := GlobalTheory.MixModel.mt_unitary W h⁻¹
  simp only [GlobalTheory.MixModel.adj_mul, GlobalTheory.MixModel.adj_adj]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (GlobalTheory.MixModel.gA W) (Formalism.L2.Theta.mt W h⁻¹),
    ← Matrix.mul_assoc (GlobalTheory.MixModel.adj (Formalism.L2.Theta.mt W h⁻¹)), hu, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

theorem absE_det_matHom_inv {W : HSp D} (h : GA D W)
    (hh : GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det (Formalism.L2.Theta.matHom W h)) = 1) :
    GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det (Formalism.L2.Theta.matHom W h⁻¹)) = 1 := by
  rw [map_inv, map_inv, map_inv, hh, inv_one]

theorem absE_det_pow_ne {r : ℕ} (a : GL (Fin r) (AE D)) (k : ℕ) :
    ((GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a) : ENNReal) ^ k) ≠ 0 ∧
      ((GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a) : ENNReal) ^ k) ≠ ⊤ :=
  ⟨pow_ne_zero _ (ENNReal.coe_ne_zero.2 ((Group.isUnit (Matrix.GeneralLinearGroup.det a)).map
    (GlobalTheory.Doubling.absE D.host.F D.host.E)).ne_zero), ENNReal.pow_ne_top ENNReal.coe_ne_top⟩

set_option maxHeartbeats 800000 in

theorem integral_phase_sandwich : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (W : HSp D) (r : ℕ) (μ : Measure (Mx D W.rank r)), μ.IsAddHaarMeasure → ∀ (h : GA D W), GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det (matHom W h)) = 1 → ∀ (a : GL (Fin r) (AE D)) (N : Mx D W.rank r → ℂ), Continuous N → Integrable N μ → Integrable (fun u : Mx D W.rank r => N (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) u) a.val)) μ ∧ ∀ y : Mx D W.rank r, ∫ u, GlobalTheory.LeviNorm.phase ψ W (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) y) (GlobalTheory.MixModel.adj (a⁻¹).val)) u * N u ∂μ = ((GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a) : ℝ) : ℂ) ^ W.rank * ∫ u, GlobalTheory.LeviNorm.phase ψ W y u * N (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) u) a.val) ∂μ := by
  intro D ψ _ W r μ hμ h hh a N _ hNi
  haveI : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  have hmod := GlobalTheory.T.addHaar_leftRightMul_adelicMatrices_module D W.rank r μ hμ (Formalism.L2.Theta.matHom W h⁻¹) a
  have h1 := absE_det_matHom_inv h hh
  rw [h1, ENNReal.coe_one, one_pow, one_mul] at hmod
  obtain ⟨hc0, hcT⟩ := absE_det_pow_ne a W.rank
  let e := (sandwichHomeo (Formalism.L2.Theta.matHom W h⁻¹) a).toMeasurableEquiv
  have he : ∀ u, e u = HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) u) a.val := fun _ => rfl
  have hmap : (Measure.map (fun u : Mx D W.rank r =>
      (HMul.hMul (HMul.hMul (Formalism.L2.Theta.matHom W h⁻¹).val (u : Matrix (Fin W.rank) (Fin r) (AE D))) a.val :
        Mx D W.rank r)) μ) = Measure.map e μ := rfl
  rw [hmap] at hmod
  refine ⟨?_, fun y => ?_⟩
  · rw [hmod, integrable_smul_measure hc0 hcT, integrable_map_equiv] at hNi
    exact hNi
  · conv_lhs => rw [hmod]
    rw [integral_smul_measure, integral_map_equiv]
    simp only [he, phase_sandwich]
    rw [ENNReal.toReal_pow, ENNReal.coe_toReal, Complex.real_smul]
    push_cast
    rfl

end GlobalTheory.LeviNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsDiscreteSeriesNegSignatureOfIsDiscreteSeriesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDiscreteSeries_neg_signature_of_isDiscreteSeries : ∀ (n : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsDS ε lam σ → Formalism.MainNotions.S.IsDS (fun a => !ε a) lam σ := by
  first | exact @GlobalTheory.PairLift.isDS_flip | exact GlobalTheory.PairLift.isDS_flip | (intros; apply GlobalTheory.PairLift.isDS_flip <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsRealThetaParameterPairThetaPartnerSignedParameStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRealThetaParameterPair_thetaPartnerSignedParameter : ∀ (t : ℕ) (b : Bool) (c c' : ℚ) (P : SPar) (N : ℕ), 1 ≤ t → P.Nonempty → GlobalTheory.SignedHC.IsRegular P → GlobalTheory.SignedHC.InCoset (c + ((t : ℚ) + 1) / 2) (GlobalTheory.SignedHC.entries P) → GlobalTheory.SignedHC.FarFrom c (((t : ℚ) + 1) / 2) P → P.card + t ≤ N → 1800 < N → GapOver P (2 * (N : ℚ) ^ 3) → GapOver (partner t b c c' P) (2 * (N : ℚ) ^ 3) → ThetaPar t P (partner t b c c' P) c c' := by
  first | exact @GlobalTheory.PairLift.FromSigned.thetaPar_partner | exact GlobalTheory.PairLift.FromSigned.thetaPar_partner | (intros; apply GlobalTheory.PairLift.FromSigned.thetaPar_partner <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedIntegralDecompContinuousPeriodicStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iteratedIntegral_decomp_continuous_periodic : ∀ (D : D7) (V W : HSp D) (a b k : ℕ) (f₁ f₃ : Mx D a b → WO V W) (f₂ : Mx D 1 k → WO V W), Continuous f₁ → Continuous f₂ → Continuous f₃ → (∀ s s', f₁ (s + s') = f₁ s + f₁ s') → (∀ r ∈ GlobalTheory.MixModel.ratMx D a b, f₁ r ∈ ratL W V) → ∀ (μ : Measure (Mx D a b)) (𝓨 : Set (Mx D a b)), IsCovolOne (GlobalTheory.MixModel.ratMx D a b) μ 𝓨 → ∀ (η : Measure (Mx D 1 k)) (𝓩 : Set (Mx D 1 k)), η.IsAddHaarMeasure → IsAddFundamentalDomain (GlobalTheory.MixModel.ratMx D 1 k) 𝓩 η → ∀ T : WO V W → ℂ, Continuous T → (∀ γ ∈ ratL W V, ∀ u, T (γ + u) = T u) → Continuous (fun s => ∫ z in 𝓩, (∫ y in 𝓨, T (f₁ s + f₂ z + f₃ y) ∂μ) ∂η) ∧ ∀ r ∈ GlobalTheory.MixModel.ratMx D a b, ∀ s, ∫ z in 𝓩, (∫ y in 𝓨, T (f₁ (r + s) + f₂ z + f₃ y) ∂μ) ∂η = ∫ z in 𝓩, (∫ y in 𝓨, T (f₁ s + f₂ z + f₃ y) ∂μ) ∂η := by
  first | exact @GlobalTheory.IsoMean.iterInt_continuous_periodic | exact GlobalTheory.IsoMean.iterInt_continuous_periodic | (intros; apply GlobalTheory.IsoMean.iterInt_continuous_periodic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralThetaLiftTermSumNeTopStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_thetaLift_termSum_ne_top : ∀ (D : D7) (V W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C → ∀ (κ : Measure (NI V C)) (𝓝 : Set (NI V C)), κ.IsHaarMeasure → IsFundamentalDomain (NIQ V C) 𝓝 κ → ∀ (ν : Measure (GA D W)) (𝓕 : Set (GA D W)), ν.IsHaarMeasure → IsFundamentalDomain (GQ W) 𝓕 ν → ∀ F : GA D W → ℂ, GlobalTheory.Grow.RapidDec W F → ∀ (Sg : GA D V × GA D W → ℝ≥0∞), (∀ n ∈ NI V C, n ∈ GQ V → ∀ a b, Sg (n * a, b) = Sg (a, b)) → (∀ γ ∈ GQ W, ∀ a b, Sg (a, γ * b) = Sg (a, b)) → ∀ (A : ℕ) (c : ℝ), (∀ a b, Sg (a, b) ≤ ENNReal.ofReal (c * (GlobalTheory.Grow.height V a * GlobalTheory.Grow.height W b) ^ A)) → ∀ g : GA D V, ∫⁻ n in 𝓝, ∫⁻ h in 𝓕, Sg ((n : GA D V) * g, h) * ‖F h‖ₑ ∂ν ∂κ ≠ ⊤ := by
  first | exact @GlobalTheory.ThetaLiftBound.lintegral_ne_top | exact GlobalTheory.ThetaLiftBound.lintegral_ne_top | (intros; apply GlobalTheory.ThetaLiftBound.lintegral_ne_top <;> assumption)
end

