import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0113
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0111
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0019
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0115
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0116
import Development.AbelianVarietyTheory.Definitions.Foundations.CyclotomicDvdExpandOfCoprime
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0118
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0073
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0112
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraicElementApproximation
section
open GlobalTheory.K5 Polynomial
open scoped NNReal

namespace GlobalTheory.K5.Dense

theorem exists_near_root {Ωl : Type} [Field Ωl] [CharZero Ωl] (v : Valuation Ωl ℝ≥0)
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] (j : Ω →+* Ωl) (e : Ωl) (t : ℝ≥0) (Q : ℤ[X])
    (h : v (Q.eval₂ (Int.castRingHom Ωl) e) < v (Q.leadingCoeff : Ωl) * t ^ Q.natDegree) :
    ∃ a : Ω, v (e - j a) < t := by
  haveI : CharZero Ω := j.charZero
  by_contra hcon
  push_neg at hcon
  set R : Polynomial Ω := Q.map (Int.castRingHom Ω) with hR
  have hinj : Function.Injective (Int.castRingHom Ω) := Int.cast_injective
  have hdeg : R.natDegree = Q.natDegree := natDegree_map_eq_of_injective hinj Q
  have hlc : R.leadingCoeff = (Q.leadingCoeff : Ω) := leadingCoeff_map_of_injective hinj Q
  have hcard : Multiset.card R.roots = R.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hprod := C_leadingCoeff_mul_prod_multiset_X_sub_C hcard
  have h1 : Q.eval₂ (Int.castRingHom Ωl) e = R.eval₂ j e := by
    rw [hR, eval₂_map]
    congr 1
    exact RingHom.ext_int _ _
  have h2 : R.eval₂ j e = (Q.leadingCoeff : Ωl) * (R.roots.map fun a => e - j a).prod := by
    conv_lhs => rw [← hprod]
    rw [eval₂_mul, eval₂_C, eval₂_multiset_prod, Multiset.map_map, hlc, map_intCast]
    simp
  rw [h1, h2, map_mul, map_multiset_prod, Multiset.map_map] at h
  have h3 : t ^ Q.natDegree ≤ (R.roots.map (v ∘ fun a => e - j a)).prod := by
    have := Multiset.pow_card_le_prod (s := R.roots.map (v ∘ fun a => e - j a)) (a := t) (by
      intro x hx
      obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 hx
      exact hcon a)
    rwa [Multiset.card_map, hcard, hdeg] at this
  exact absurd h (not_lt.2 (by gcongr))

theorem exists_approx {p : ℕ} [Fact p.Prime] (P : ℤ_[p][X]) (N : ℕ) :
    ∃ (Q : ℤ[X]) (R : ℤ_[p][X]), Q.natDegree ≤ P.natDegree ∧
      P = Q.map (Int.castRingHom ℤ_[p]) + C ((p : ℤ_[p]) ^ N) * R := by
  have h : ∀ x : ℤ_[p], ∃ (m : ℤ) (r : ℤ_[p]), x = m + (p : ℤ_[p]) ^ N * r := by
    intro x
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.1 (PadicInt.appr_spec N x)
    exact ⟨PadicInt.appr x N, r, by push_cast; linear_combination hr⟩
  choose m r hmr using h
  refine ⟨∑ i ∈ Finset.range (P.natDegree + 1), monomial i (m (P.coeff i)),
    ∑ i ∈ Finset.range (P.natDegree + 1), monomial i (r (P.coeff i)), ?_, ?_⟩
  · refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
    exact (natDegree_monomial_le _).trans (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
  · rw [Polynomial.map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    conv_lhs => rw [P.as_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_monomial, C_mul_monomial, ← map_add, eq_intCast, ← hmr]

theorem exists_cong : ∀ (p : ℕ) [Fact p.Prime] (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl], IsClo p Ωl → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (j : Ω →+* Ωl) (k : ℕ) (e : Ωl), IsInt p e → IsAlgZp p e → ∃ a : Ω, IsInt p (j a) ∧ Cong p k e (j a) := by
  intro p hp Ωl _ _ hclo Ω _ _ j k e he ⟨P, hP0, hP⟩
  obtain ⟨v, hv, -, hp0, hp1⟩ := exists_valuation_isInt p Ωl hclo
  haveI : CharZero Ωl := Basic.charZero_of_isClo hclo
  have hpne : (p : Ωl) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  set φ : ℤ_[p] →+* Ωl := (algebraMap (O0 p) Ωl).comp (algebraMap ℤ_[p] (O0 p)) with hφ
  have hPe : P.eval₂ φ e = 0 := by rwa [aeval_def, eval₂_map] at hP
  have hφint : ∀ x, v (φ x) ≤ 1 := fun x => (hv _).2 isIntegral_algebraMap
  have hc0 : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hP0
  have hc : φ P.leadingCoeff ≠ 0 := by
    rw [PadicInt.unitCoeff_spec hc0, map_mul, map_pow, map_natCast]
    exact mul_ne_zero ((Units.isUnit _).map φ).ne_zero (pow_ne_zero _ hpne)
  have hvc : 0 < v (φ P.leadingCoeff) := (Valuation.pos_iff v).2 hc
  obtain ⟨N, hN⟩ := NNReal.exists_pow_lt_of_lt_one
    (a := v (φ P.leadingCoeff) * (v (p : Ωl) ^ k) ^ P.natDegree) (by positivity) hp1
  have hpk : v (p : Ωl) ^ k ≤ 1 := pow_le_one₀ zero_le hp1.le
  have hN' : v (p : Ωl) ^ N < v (φ P.leadingCoeff) :=
    hN.trans_le (mul_le_of_le_one_right zero_le (pow_le_one₀ zero_le hpk))
  obtain ⟨Q, R, hdeg, hQR⟩ := exists_approx P N
  have hsmall : ∀ y : Ωl, v y ≤ 1 → v ((p : Ωl) ^ N * y) ≤ v (p : Ωl) ^ N := by
    intro y hy
    rw [map_mul, map_pow]
    exact mul_le_of_le_one_right zero_le hy
  have hco : φ P.leadingCoeff = (Q.coeff P.natDegree : Ωl) + (p : Ωl) ^ N * φ (R.coeff P.natDegree) := by
    have := congrArg (fun S => φ (coeff S P.natDegree)) hQR
    simp only [coeff_add, coeff_C_mul, coeff_map, map_add, map_mul, eq_intCast, map_intCast] at this
    rw [map_pow, map_natCast] at this
    exact this
  have hvQ : v (Q.coeff P.natDegree : Ωl) = v (φ P.leadingCoeff) := by
    rw [eq_sub_of_add_eq hco.symm]
    exact Valuation.map_sub_eq_of_lt_left v ((hsmall _ (hφint _)).trans_lt hN')
  have hQ0 : Q.coeff P.natDegree ≠ 0 := by
    intro h0
    rw [h0, Int.cast_zero, map_zero] at hvQ
    exact hvc.ne hvQ
  have hdeg' : Q.natDegree = P.natDegree := natDegree_eq_of_le_of_coeff_ne_zero hdeg hQ0
  have hRe : v (R.eval₂ φ e) ≤ 1 := by
    rw [eval₂_eq_sum_range]
    refine Valuation.map_sum_le v fun i _ => ?_
    rw [map_mul, map_pow]
    exact mul_le_one₀ (hφint _) zero_le (pow_le_one₀ zero_le ((hv _).2 he))
  have hQe : Q.eval₂ (Int.castRingHom Ωl) e = -((p : Ωl) ^ N * R.eval₂ φ e) := by
    rw [hQR, eval₂_add, eval₂_mul, eval₂_C, eval₂_map, map_pow, map_natCast,
      RingHom.ext_int (φ.comp _) (Int.castRingHom Ωl)] at hPe
    exact eq_neg_of_add_eq_zero_left hPe
  obtain ⟨a, ha⟩ := exists_near_root v j e (v (p : Ωl) ^ k) Q (by
    rw [hQe, Valuation.map_neg, leadingCoeff, hdeg', hvQ]
    exact (hsmall _ hRe).trans_lt hN)
  refine ⟨a, (hv _).1 ?_, (e - j a) / (p : Ωl) ^ k, (hv _).1 ?_, ?_⟩
  · rw [show j a = e - (e - j a) by ring]
    exact Valuation.map_sub_le v ((hv _).2 he) (ha.le.trans hpk)
  · rw [map_div₀, map_pow]
    exact div_le_one_of_le₀ ha.le zero_le
  · field_simp

end GlobalTheory.K5.Dense
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraicTowerKhatPadicSmulTorsionFreeStatement
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicTowerKhat_padic_smul_torsionFree : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], [IsAlgClosed Ω] → ∀ (c : ℤ_[l]) (x : X.Khat l), c ≠ 0 → c • x = 0 → x = 0 := by
  first | exact @GlobalTheory.KZ.H3.khat_torsionFree | exact GlobalTheory.KZ.H3.khat_torsionFree | (intros; apply GlobalTheory.KZ.H3.khat_torsionFree <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardDualZmodModuleEqCardStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_dual_zmod_module_eq_card : ∀ (n : ℕ) [NeZero n] (A : Type) [AddCommGroup A] [Module (ZMod n) A] [Finite A], Nat.card (Module.Dual (ZMod n) A) = Nat.card A := by
  first | exact @GlobalTheory.ZModDual.card_dual_eq | exact GlobalTheory.ZModDual.card_dual_eq | (intros; apply GlobalTheory.ZModDual.card_dual_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterEigenspaceIsComplPrincipalSeriesTwistedStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.characterEigenspace_isCompl_principalSeriesTwistedSpan : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∀ (H : Set G) (θ : G → ℂ), Datum H θ → (∀ u ∈ aug π H θ, IsEig π H θ u → u = 0) ∧ ∀ w : V, ∃ w' : V, IsEig π H θ w' ∧ w - w' ∈ aug π H θ := by
  first | exact @GlobalTheory.PsType.eig_compl_aug | exact GlobalTheory.PsType.eig_compl_aug | (intros; apply GlobalTheory.PsType.eig_compl_aug <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmpProps
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem cmp_props :
    (∀ f : ℍ → ℂ, GlobalTheory.FN.cmp 1 f = f) ∧ (∀ (g h : GQ) (f : ℍ → ℂ), GlobalTheory.FN.cmp (g * h) f = GlobalTheory.FN.cmp h (GlobalTheory.FN.cmp g f)) ∧
      (∀ (γ : SL(2, ℤ)) (f : ℍ → ℂ), GlobalTheory.FN.cmp (ofSL γ) f = fun τ => f (γ • τ)) ∧
        ∀ (g : GQ) (f : ℍ → ℂ), ∀ z ∈ Hs, up (GlobalTheory.FN.cmp g f) z = up f (mob g z) := by
  obtain ⟨hH, hmul, hone, hsl, -, -⟩ := GlobalTheory.T.glTwoPosRatMobius_upperHalfPlane_properties
  have hup : ∀ (f : ℍ → ℂ) (z : ℂ) (hz : 0 < z.im), up f z = f ⟨z, hz⟩ := by
    intro f z hz
    simp only [up, UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  have hupH : ∀ (f : ℍ → ℂ) (τ : ℍ), up f τ = f τ := by
    intro f τ
    simp only [up, UpperHalfPlane.ofComplex_apply]
  have h4 : ∀ (g : GQ) (f : ℍ → ℂ), ∀ z ∈ Hs, up (GlobalTheory.FN.cmp g f) z = up f (mob g z) := by
    intro g f z hz
    rw [hup _ z hz]
    rfl
  refine ⟨?_, ?_, ?_, h4⟩
  · intro f
    funext τ
    simp only [cmp, hone, hupH]
  · intro g h f
    funext τ
    have hτ : (τ : ℂ) ∈ Hs := τ.im_pos
    show up f (mob (g * h) τ) = up (cmp g f) (mob h τ)
    rw [h4 g f _ (hH h _ hτ), hmul g h _ hτ]
  · intro γ f
    funext τ
    simp only [cmp, hsl, hupH]

end GlobalTheory.FN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffMemRangeOfIsRoot
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.PsRoot

theorem mem_of_isAlgebraic_of_isAlgClosed (E : Subfield ℂ) [IsAlgClosed E] {x : ℂ}
    (hx : IsAlgebraic E x) : x ∈ E := by
  have hi : IsIntegral E x := hx.isIntegral
  have h1 : (minpoly E x).natDegree = 1 := by
    have := IsAlgClosed.degree_eq_one_of_irreducible E (minpoly.irreducible hi)
    exact Polynomial.natDegree_eq_of_degree_eq_some this
  obtain ⟨y, hy⟩ := (minpoly.natDegree_eq_one_iff).1 h1
  rw [← hy]
  exact y.2

theorem coeff_mem_range_of_isRoot : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ)
    (b : PowerSeries ℂ) (Q : Polynomial (PowerSeries ℂ)), Q ≠ 0 →
    (∀ i k, PowerSeries.coeff k (Q.coeff i) ∈ ε.range) → Q.eval b = 0 →
    ∀ k, PowerSeries.coeff k b ∈ ε.range := by
  intro Ω _ _ ε b Q hQ hcoef hb k
  let E : Subfield ℂ := ε.fieldRange
  haveI : IsAlgClosed E := IsAlgClosed.of_ringEquiv Ω E ε.rangeRestrictFieldEquiv
  have hE : ∀ z : ℂ, z ∈ ε.range → z ∈ E := fun z hz => by
    obtain ⟨y, rfl⟩ := hz
    exact ⟨y, rfl⟩

  have hroot : ∀ g : ℂ ≃ₐ[E] ℂ, Q.IsRoot (PowerSeries.map (g : ℂ →+* ℂ) b) := by
    intro g
    have hfix : Q.map (PowerSeries.map (g : ℂ →+* ℂ)) = Q := by
      ext i j
      rw [Polynomial.coeff_map, PowerSeries.coeff_map]
      obtain ⟨y, hy⟩ := hE _ (hcoef i j)
      rw [← hy]
      exact g.commutes ⟨_, ⟨y, rfl⟩⟩
    have h2 := Polynomial.eval_map_apply (PowerSeries.map (g : ℂ →+* ℂ)) (p := Q) b
    show Q.eval _ = 0
    rw [hfix, hb, map_zero] at h2
    exact h2
  have hfin : (Set.range fun g : ℂ ≃ₐ[E] ℂ => g (PowerSeries.coeff k b)).Finite := by
    refine ((Polynomial.finite_setOf_isRoot hQ).image (PowerSeries.coeff k)).subset ?_
    rintro _ ⟨g, rfl⟩
    refine ⟨PowerSeries.map (g : ℂ →+* ℂ) b, hroot g, ?_⟩
    simp [PowerSeries.coeff_map]
  obtain ⟨y, hy⟩ := mem_of_isAlgebraic_of_isAlgClosed E (GlobalTheory.T.isAlgebraic_of_finite_complex_automorphism_orbit E _ hfin)
  exact ⟨y, hy⟩

end GlobalTheory.PsRoot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ColemanNormOperatorIterateSuccCongrFrobenius
section
open GlobalTheory.Col PowerSeries

namespace GlobalTheory

theorem normOp_isUnit {R : Type} [CommRing R] (p : ℕ) [Fact p.Prime] {h : PowerSeries R} (hu : IsUnit h) :
    IsUnit (normOp p h) := by
  unfold normOp
  exact hu.map _

theorem normOp_iterate_isUnit {R : Type} [CommRing R] (p : ℕ) [Fact p.Prime] {h : PowerSeries R} (hu : IsUnit h)
    (j : ℕ) : IsUnit ((normOp p)^[j] h) := by
  induction j with
  | zero => simpa using hu
  | succ j ih => rw [Function.iterate_succ_apply']; exact normOp_isUnit p ih

theorem normOp_iterate_congr : ∀ (R : Type) [CommRing R] (p : ℕ) [hp : Fact p.Prime] (σ : R ≃+* R), FrobLift R p σ →
    ∀ (h : PowerSeries R), IsUnit h → ∀ j : ℕ, ∃ r : PowerSeries R,
      (normOp p)^[j + 1] h = smap σ ((normOp p)^[j] h) + (p : PowerSeries R) ^ (j + 1) * r := by
  intro R _ p hp σ hσ h hu j
  induction j with
  | zero =>
    obtain ⟨r, hr⟩ := GlobalTheory.T.normOp_eq_smap_add_mul R p σ hσ h
    exact ⟨r, by simpa using hr⟩
  | succ j ih =>
    obtain ⟨r, hr⟩ := ih
    have hu2 : IsUnit (smap σ ((normOp p)^[j] h)) := (normOp_iterate_isUnit p hu j).map _
    obtain ⟨r', hr'⟩ := GlobalTheory.T.normOp_congr_mod_pow_succ R p σ hσ _ _ r (j + 1) (by omega) hu2 hr
    refine ⟨r', ?_⟩
    rw [Function.iterate_succ_apply' (normOp p) (j + 1), hr', GlobalTheory.T.colemanNormOperator_powerSeriesCoeffAutMap_comm R p σ, ← Function.iterate_succ_apply' (normOp p) j]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContCohomologyTransportMulEquiv
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

namespace GlobalTheory

theorem dn_comp_monoidHom {R Γ Γ' M : Type*} [CommRing R] [Group Γ] [Group Γ'] [AddCommGroup M]
    [Module R M] (φ : Γ' →* Γ) (ρ : Representation R Γ M) (ρ' : Representation R Γ' M)
    (h : ∀ g m, ρ' g m = ρ (φ g) m) (n : ℕ) (f : (Fin n → Γ) → M) (g : Fin (n + 1) → Γ') :
    dn ρ' n (fun x => f (fun i => φ (x i))) g = dn ρ n f (fun i => φ (g i)) := by
  show ρ' (g 0) (f fun i => φ (g i.succ)) + (Finset.univ.sum fun j : Fin (n + 1) =>
      (-1 : R) ^ ((j : ℕ) + 1) • f (fun i => φ (Fin.contractNth j (· * ·) g i))) =
    ρ (φ (g 0)) (f fun i => φ (g i.succ)) + Finset.univ.sum fun j : Fin (n + 1) =>
      (-1 : R) ^ ((j : ℕ) + 1) • f (Fin.contractNth j (· * ·) fun i => φ (g i))
  rw [h]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 2
  funext i
  simp only [Fin.contractNth]
  split_ifs <;> simp

theorem contCohomology_transport_mulEquiv :
    ∀ (R : Type) [CommRing R] (Γ Γ' : Type) [Group Γ] [TopologicalSpace Γ] [Group Γ'] [TopologicalSpace Γ'] (M : Type) [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (e : Γ' ≃* Γ), Continuous e → Continuous e.symm → ∀ (ρ : Representation R Γ M) (ρ' : Representation R Γ' M), (∀ g m, ρ' g m = ρ (e g) m) → Nonempty (H1 ρ ≃ H1 ρ') ∧ Nonempty (H2 ρ ≃ H2 ρ') ∧ (Subsingleton (Hn ρ 3) → Subsingleton (Hn ρ' 3)) := by
  intro R _ Γ Γ' _ _ _ _ M _ _ _ _ e he he' ρ ρ' h
  have h' : ∀ g m, ρ g m = ρ' (e.symm g) m := fun g m => by rw [h, e.apply_symm_apply]
  refine ⟨⟨⟨pairH1DecompositionMap ρ ρ' e.toMonoidHom he LinearMap.id continuous_id (fun g m => (h g m).symm),
      pairH1DecompositionMap ρ' ρ e.symm.toMonoidHom he' LinearMap.id continuous_id (fun g m => (h' g m).symm),
      ?_, ?_⟩⟩,
    ⟨⟨compatiblePairH2 ρ ρ' e.toMonoidHom he LinearMap.id continuous_id (fun g m => (h g m).symm),
      compatiblePairH2 ρ' ρ e.symm.toMonoidHom he' LinearMap.id continuous_id (fun g m => (h' g m).symm),
      ?_, ?_⟩⟩, ?_⟩
  · intro x
    induction x using Submodule.Quotient.induction_on with
    | H f =>
      refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun g => ?_))
      exact congrArg f.1 (e.apply_symm_apply g)
  · intro x
    induction x using Submodule.Quotient.induction_on with
    | H f =>
      refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun g => ?_))
      exact congrArg f.1 (e.symm_apply_apply g)
  · intro x
    induction x using Submodule.Quotient.induction_on with
    | H f =>
      refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun g => ?_))
      exact congrArg f.1 (Prod.ext (e.apply_symm_apply g.1) (e.apply_symm_apply g.2))
  · intro x
    induction x using Submodule.Quotient.induction_on with
    | H f =>
      refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun g => ?_))
      exact congrArg f.1 (Prod.ext (e.symm_apply_apply g.1) (e.symm_apply_apply g.2))
  · intro hs
    rw [GlobalTheory.Published.subsingleton_Hn_succ_iff] at hs ⊢
    intro f hf hd
    obtain ⟨c, hc, hcf⟩ := hs (fun x => f (fun i => e.symm (x i)))
      (hf.comp (continuous_pi fun i => he'.comp (continuous_apply i))) (by
        funext g
        have := dn_comp_monoidHom e.symm.toMonoidHom ρ' ρ h' 3 f g
        rw [hd] at this
        exact this)
    refine ⟨fun x => c (fun i => e (x i)),
      hc.comp (continuous_pi fun i => he.comp (continuous_apply i)), ?_⟩
    funext g
    have := dn_comp_monoidHom e.toMonoidHom ρ ρ' h 2 c g
    rw [hcf] at this
    refine this.trans ?_
    exact congrArg f (funext fun i => e.symm_apply_apply _)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqOrEqNegOfWeierstrassPTorsionEqStatement
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_or_eq_neg_of_weierstrassP_torsion_eq : ∀ (N : ℕ) [NeZero N] (τ : ℍ) (x y : Fin 2 → ZMod N), x ≠ 0 → y ≠ 0 → wp N x τ = wp N y τ → x = y ∨ x = -y := by
  first | exact @GlobalTheory.FN.WpSep.main | exact GlobalTheory.FN.WpSep.main | (intros; apply GlobalTheory.FN.WpSep.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoboundaryOfSubsingletonContCohomologyThre
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

namespace GlobalTheory

theorem exists_coboundary_of_subsingleton_Hn_three :
    ∀ (R : Type) [CommRing R] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (M : Type) [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R Γ M), Subsingleton (Hn ρ 3) → ∀ c : Γ × Γ × Γ → M, Continuous c → (∀ g h k m, ρ g (c (h, k, m)) - c (g * h, k, m) + c (g, h * k, m) - c (g, h, k * m) + c (g, h, k) = 0) → ∃ u : Γ × Γ → M, Continuous u ∧ ∀ g h k, ρ g (u (h, k)) - u (g * h, k) + u (g, h * k) - u (g, h) = c (g, h, k) := by
  intro R _ Γ _ _ M _ _ _ _ ρ hs c hc hcoc
  let f : (Fin 3 → Γ) → M := fun x => c (x 0, x 1, x 2)
  have hf : Continuous f := hc.comp (by fun_prop)
  have hd : dn ρ 3 f = 0 := by
    funext g
    rw [dn_apply, Fin.sum_univ_four]
    have e := hcoc (g 0) (g 1) (g 2) (g 3)
    have e0 : (f fun i => g i.succ) = c (g 1, g 2, g 3) := rfl
    have e1 : f (Fin.contractNth 0 (· * ·) g) = c (g 0 * g 1, g 2, g 3) := rfl
    have e2 : f (Fin.contractNth 1 (· * ·) g) = c (g 0, g 1 * g 2, g 3) := rfl
    have e3 : f (Fin.contractNth 2 (· * ·) g) = c (g 0, g 1, g 2 * g 3) := rfl
    have e4 : f (Fin.contractNth 3 (· * ·) g) = c (g 0, g 1, g 2) := rfl
    rw [e0, e1, e2, e3, e4, Pi.zero_apply, ← e]
    norm_num [pow_succ]
    abel
  rw [Submodule.Quotient.subsingleton_iff, eq_top_iff] at hs
  obtain ⟨w, hw, hwf⟩ : ∃ w : (Fin 2 → Γ) → M, Continuous w ∧ dn ρ 2 w = f :=
    hs (x := ⟨f, hf, hd⟩) trivial
  refine ⟨fun p => w ![p.1, p.2], hw.comp (by fun_prop), fun g h k => ?_⟩
  have e := congrFun hwf ![g, h, k]
  rw [dn_apply, Fin.sum_univ_three] at e
  have e0 : (fun i : Fin 2 => (![g, h, k] : Fin 3 → Γ) i.succ) = ![h, k] := by
    funext i; fin_cases i <;> rfl
  have e1 : Fin.contractNth 0 (· * ·) (![g, h, k] : Fin 3 → Γ) = ![g * h, k] := by
    funext i; fin_cases i <;> rfl
  have e2 : Fin.contractNth 1 (· * ·) (![g, h, k] : Fin 3 → Γ) = ![g, h * k] := by
    funext i; fin_cases i <;> rfl
  have e3 : Fin.contractNth 2 (· * ·) (![g, h, k] : Fin 3 → Γ) = ![g, h] := by
    funext i; fin_cases i <;> rfl
  have e4 : f ![g, h, k] = c (g, h, k) := rfl
  rw [e0, e1, e2, e3, e4] at e
  rw [← e]
  norm_num [pow_succ]
  abel

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCombinationMulEqReparametrizationImage
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois GlobalTheory.GeoFix

namespace GlobalTheory.GeoFix

theorem inR_algebraMap {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]
    {T : Tower p Ω} {n : ℕ} {ψ : O0 p →+* Ω} (h : IsReb T n ψ) (c : O0 p) :
    ∃ c' : O0 p, ψ c' = algebraMap (O0 p) Ω c := by
  have hmem : algebraMap (O0 p) Ω c ∈ ψ.range := by
    rw [h.rng]
    exact Subalgebra.algebraMap_mem _ c
  exact hmem

theorem inR_pow {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]
    {ψ : O0 p →+* Ω} {x : Ω} (hx : InR ψ x) (k : ℕ) : InR ψ (x ^ k) := by
  induction k with
  | zero => simpa using inR_psi ψ 1
  | succ k ih => rw [pow_succ]; exact inR_mul ih hx

theorem exists_inR_mul_eq_psi : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ (T : Tower p Ω) (n : ℕ) (ψ : O0 p →+* Ω), IsReb T n ψ → ∀ N : Ω, GlobalTheory.GeoFix.InR ψ N → N ≠ 0 →
    ∃ (N' : Ω) (D : O0 p), GlobalTheory.GeoFix.InR ψ N' ∧ D ≠ 0 ∧ N * N' = ψ D := by
  intro p _ Ω _ _ hc T n ψ h N hN hN0
  obtain ⟨f, hfm, hf⟩ : IsIntegral (O0 p) N := hN.isInt h
  have key : ∀ k : ℕ, ∀ f : Polynomial (O0 p), f.natDegree = k → f.Monic → Polynomial.eval₂ (algebraMap (O0 p) Ω) N f = 0 →
      ∃ (N' : Ω) (D : O0 p), InR ψ N' ∧ D ≠ 0 ∧ N * N' = ψ D := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro f hk hfm hf
      by_cases h0 : f.coeff 0 = 0
      · obtain ⟨g, rfl⟩ := Polynomial.X_dvd_iff.2 h0
        have hgm : g.Monic := Polynomial.Monic.of_mul_monic_left Polynomial.monic_X hfm
        have hgdeg : g.natDegree < k := by
          rw [← hk, Polynomial.natDegree_X_mul hgm.ne_zero]; omega
        refine ih _ hgdeg g rfl hgm ?_
        rw [Polynomial.eval₂_mul, Polynomial.eval₂_X] at hf
        exact (mul_eq_zero.1 hf).resolve_left hN0
      · obtain ⟨g, hg⟩ := Polynomial.X_dvd_iff.2 (show (f - Polynomial.C (f.coeff 0)).coeff 0 = 0 by simp)
        obtain ⟨D, hD⟩ := inR_algebraMap h (-f.coeff 0)
        refine ⟨Polynomial.eval₂ (algebraMap (O0 p) Ω) N g, D, ?_, ?_, ?_⟩
        · rw [Polynomial.eval₂_eq_sum_range]
          refine inR_sum _ _ fun i _ => ?_
          obtain ⟨c', hc'⟩ := inR_algebraMap h (g.coeff i)
          rw [← hc']
          exact inR_mul (inR_psi ψ c') (inR_pow hN i)
        · rintro rfl
          rw [map_zero, map_neg] at hD
          exact h0 (hc.inj (by rw [map_zero]; exact neg_eq_zero.1 hD.symm))
        · have hf' : f = Polynomial.X * g + Polynomial.C (f.coeff 0) := by
            rw [← hg]; ring
          rw [hf', Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_C] at hf
          rw [hD, map_neg]
          linear_combination hf
  exact key _ f rfl hfm hf

end GlobalTheory.GeoFix
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsConjOverPrimeStatement
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algEquiv_map_valuationSubring_over_prime : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (p : ℕ) [Fact p.Prime] (A B : ValuationSubring Ω), ((p : ℕ) : Ω) ∈ A.nonunits → ((p : ℕ) : Ω) ∈ B.nonunits → ∃ σ : Ω ≃ₐ[ℚ] Ω, ∀ x, σ x ∈ B ↔ x ∈ A := by
  first | exact @GlobalTheory.ValConjClosure.exists_conj_over_prime | exact GlobalTheory.ValConjClosure.exists_conj_over_prime | (intros; apply GlobalTheory.ValConjClosure.exists_conj_over_prime <;> assumption)
end

