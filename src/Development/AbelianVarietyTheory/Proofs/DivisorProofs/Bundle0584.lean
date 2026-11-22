import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0560
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0487
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0414
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0407
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0457
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0573
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FinalD
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0409
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0382
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0571

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSeriesTermSmulAddDecomposition
section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem theta_term_smul_add (O : Type) [CommRing O] (N : GlobalTheory.Ex.NumD O) (S : Subring O) (m : ℕ) (h : N.Gt)
    (y : N.X) (hy : h ^ m = N.io y)
    (hθ : ∀ x ∈ Subgroup.closure (Set.range N.c ∪ {h.b}), ∀ x' ∈ Subgroup.closure (Set.range N.c ∪ {h.b}),
      ∀ x'' ∈ Subgroup.closure (Set.range N.c ∪ {h.b}),
        (N.θ x x' x'' : O) ∈ S ∧ (((N.θ x x' x'')⁻¹ : Oˣ) : O) ∈ S)
    (hσ : ∀ x ∈ Subgroup.closure (Set.range N.c ∪ {h.b}), (N.σ x : O) ∈ S ∧ (((N.σ x)⁻¹ : Oˣ) : O) ∈ S)
    (a b : N.X) : ∃ w : Oˣ, (w : O) ∈ S ∧
      N.ψ (m • a + b) * h.s (m • a + b) = w * N.ψ a ^ (m ^ 2) * N.τ a (m • b + y) * (N.ψ b * h.s b) := by
  set H := Subgroup.closure (Set.range N.c ∪ {h.b}) with hH
  set T := S.toSubmonoid.units with hT
  set π : Oˣ →* Oˣ ⧸ T := QuotientGroup.mk' T with hπ
  have Hc : ∀ a, N.c a ∈ H := fun a => Subgroup.subset_closure (Or.inl ⟨a, rfl⟩)
  have Hb : h.b ∈ H := Subgroup.subset_closure (Or.inr rfl)
  have θ1 : ∀ x ∈ H, ∀ x' ∈ H, ∀ x'' ∈ H, π (N.θ x x' x'') = 1 := fun x hx x' hx' x'' hx'' =>
    (QuotientGroup.eq_one_iff _).2 ((Submonoid.mem_units_iff _ _).2 (hθ x hx x' hx' x'' hx''))
  have σ1 : ∀ a, π (N.σ (N.c a)) = 1 := fun a =>
    (QuotientGroup.eq_one_iff _).2 ((Submonoid.mem_units_iff _ _).2 (hσ _ (Hc a)))
  have Bl : ∀ a a' b, π (N.τ (a + a') b) = π (N.τ a b) * π (N.τ a' b) := by
    intro a a' b
    have := congrArg π (N.τ_add_left a a' b)
    rwa [map_mul, map_mul, θ1 _ (Hc a) _ (Hc a') _ (Hc b), mul_one] at this
  have Br : ∀ a b b', π (N.τ a (b + b')) = π (N.τ a b) * π (N.τ a b') := by
    intro a b b'
    have := congrArg π (N.τ_add_right a b b')
    rwa [map_mul, map_mul, θ1 _ (Hc b) _ (Hc b') _ (Hc a), mul_one] at this
  have fadd : ∀ a b, π (N.ψ (a + b)) = π (N.τ a b) * π (N.ψ a) * π (N.ψ b) := by
    intro a b
    rw [N.ψ_add, map_mul, map_mul]
  have fneg : ∀ a, π (N.ψ (-a)) = π (N.ψ a) := by
    intro a
    have := congrArg π (N.even a)
    rwa [map_mul, σ1, mul_one] at this
  have Bnegr : ∀ a b, π (N.τ a (-b)) = (π (N.τ a b))⁻¹ := by
    intro a b
    have := Br a b (-b)
    rw [add_neg_cancel, N.τ_zero_right, map_one] at this
    exact eq_inv_of_mul_eq_one_right this.symm
  have Bself : ∀ a, π (N.τ a a) = π (N.ψ a) ^ 2 := by
    intro a
    have := fadd a (-a)
    rw [add_neg_cancel, N.ψ_zero, map_one, fneg, Bnegr, mul_assoc, eq_comm, inv_mul_eq_one] at this
    rw [sq]
    exact this
  have Bsmul : ∀ (k : ℕ) a b, π (N.τ (k • a) b) = π (N.τ a b) ^ k := by
    intro k a b
    induction k with
    | zero => simp
    | succ k ih => rw [succ_nsmul, Bl, ih, pow_succ]
  have Bsmulr : ∀ (k : ℕ) a b, π (N.τ a (k • b)) = π (N.τ a b) ^ k := by
    intro k a b
    rw [N.τ_symm, Bsmul, N.τ_symm]
  have fsmul : ∀ (k : ℕ) a, π (N.ψ (k • a)) = π (N.ψ a) ^ (k ^ 2) := by
    intro k a
    induction k with
    | zero => simp
    | succ k ih =>
      rw [succ_nsmul, fadd, ih, Bsmul, Bself, ← pow_mul, ← pow_add, ← pow_succ]
      congr 1
      ring
  have Sadd : ∀ χ χ', π (h.s (χ + χ')) = π (h.s χ) * π (h.s χ') := by
    intro χ χ'
    have := congrArg π (h.mult χ χ')
    rwa [map_mul, map_mul, θ1 _ (Hc χ) _ (Hc χ') _ Hb, mul_one] at this
  have Ssmul : ∀ (k : ℕ) a, π (h.s (k • a)) = π (h.s a) ^ k := by
    intro k a
    induction k with
    | zero => simp
    | succ k ih => rw [succ_nsmul, Sadd, ih, pow_succ]
  have Spow : π (h.s a) ^ m = π (N.τ a y) := by
    have := congrArg π (h.pow_s m a)
    rw [map_mul, map_pow, hy, GlobalTheory.Ex.NumD.io_s, N.τ_symm] at this
    have hc : π (cubN N.θ m 1 h.b (N.c a)) = 1 := by
      unfold cubN
      rw [map_prod]
      exact Finset.prod_eq_one fun i _ => θ1 _ (by rw [one_mul]; exact pow_mem Hb i) _ Hb _ (Hc a)
    rw [hc, mul_one] at this
    exact this.symm
  refine ⟨N.ψ (m • a + b) * h.s (m • a + b) / (N.ψ a ^ (m ^ 2) * N.τ a (m • b + y) * (N.ψ b * h.s b)), ?_, ?_⟩
  · have e : π (N.ψ (m • a + b) * h.s (m • a + b) / (N.ψ a ^ (m ^ 2) * N.τ a (m • b + y) * (N.ψ b * h.s b))) = 1 := by
      rw [map_div, div_eq_one, map_mul, map_mul, map_mul, map_mul, map_pow, fadd, Sadd, fsmul, Bsmul, Br, Bsmulr,
        Ssmul, Spow]
      ac_rfl
    exact ((Submonoid.mem_units_iff _ _).1 ((QuotientGroup.eq_one_iff _).1 e)).1
  · exact (fun (L X Y Z : Oˣ) => show L = L / (X * Y * Z) * X * Y * Z by
      rw [mul_assoc (L / (X * Y * Z)) X Y, mul_assoc (L / (X * Y * Z)) (X * Y) Z, div_mul_cancel]) _ _ _ _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TiltUntiltDividesPow
section
open Ideal WittVector

namespace GlobalTheory

private lemma perfection_isUnit_of_coeff_zero {p : ℕ} [hp : Fact p.Prime] {R : Type*}
    [CommRing R] [CharP R p]
    (x : Perfection R p) (h : IsUnit (Perfection.coeff R p 0 x)) : IsUnit x := by
  have hn : ∀ n, IsUnit (Perfection.coeff R p n x) := fun n => by
    have e : Perfection.coeff R p n x ^ p ^ n = Perfection.coeff R p 0 x :=
      Perfection.coeffMonoidHom_pow_p_pow_self x n
    rw [← e] at h
    exact (isUnit_pow_iff (pow_ne_zero _ hp.out.ne_zero)).1 h
  let y : Perfection R p := ⟨fun n => ((hn n).unit⁻¹ : Rˣ), fun n => by
    have e : (hn (n + 1)).unit ^ p = (hn n).unit :=
      Units.ext (by simp [Perfection.coeff_pow_p' x n])
    rw [← Units.val_pow_eq_pow_val, inv_pow, e]⟩
  have hy : ∀ n, Perfection.coeff R p n x * Perfection.coeff R p n y = 1 := fun n => by
    rw [Perfection.coeff_mk]
    exact (hn n).mul_val_inv
  refine ⟨⟨x, y, ?_, ?_⟩, rfl⟩
  · ext n; rw [map_mul, hy, map_one]
  · ext n; rw [map_mul, mul_comm, hy, map_one]

private lemma untilt_sub_one_congr {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O]
    [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O] (x : PreTilt O p) :
    ∃ t : O, (x - 1).untilt = x.untilt - 1 + p * t := by
  have h : Ideal.Quotient.mk (span {(p : O)}) (x - 1).untilt =
      Ideal.Quotient.mk (span {(p : O)}) (x.untilt - 1) := by
    rw [PreTilt.mk_untilt_eq_coeff_zero, map_sub, map_sub, PreTilt.mk_untilt_eq_coeff_zero,
      map_one, map_one]
  obtain ⟨t, ht⟩ := mem_span_singleton'.1 (Ideal.Quotient.eq.1 h)
  exact ⟨t, by linear_combination -ht⟩

theorem preTilt_pow_sub_one_pow_dvd_of_associated (p : ℕ) [hp : Fact p.Prime] (R : Type)
    [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (Ideal.span {(p : R)}) R]
    (hreg : IsSMulRegular R (p : R)) (pflat f : PreTilt R p)
    (hpf : PreTilt.untilt pflat = (p : R))
    (hker : ∀ c : PreTilt R p, PreTilt.coeff 0 c = 0 → pflat ∣ c)
    (hass : Associated ((PreTilt.untilt f - 1) ^ (p * (p - 1))) (p : R))
    (c : PreTilt R p) (hc : PreTilt.coeff 0 c = 0) : (f ^ p - 1) ^ (p - 1) ∣ c := by
  obtain ⟨w, hw⟩ := hass
  obtain ⟨t, ht⟩ := untilt_sub_one_congr f
  set a : R := PreTilt.untilt f - 1 with ha
  have h2 := hp.out.two_le
  obtain ⟨M, hM⟩ : ∃ M, p * (p - 1) = M + 2 := by
    refine ⟨p * (p - 1) - 2, ?_⟩
    have : 2 * 1 ≤ p * (p - 1) := Nat.mul_le_mul h2 (by omega)
    omega
  have hpJ : (p : R) ∈ jacobson (⊥ : Ideal R) :=
    IsAdicComplete.le_jacobson_bot (span {(p : R)}) (mem_span_singleton_self _)
  have haJ : a ∈ jacobson (⊥ : Ideal R) := by
    refine Ideal.isRadical_jacobson ⊥ ⟨p * (p - 1), ?_⟩
    have : a ^ (p * (p - 1)) = (p : R) * ((w⁻¹ : Rˣ) : R) := by
      rw [← hw, mul_assoc, Units.mul_inv, mul_one]
    rw [this]
    exact Ideal.mul_mem_right _ _ hpJ
  have hu : IsUnit (a * (a ^ M * w * t) + 1) := mem_jacobson_bot.1 haJ _
  have h1 : (f - 1).untilt = a * (a * (a ^ M * w * t) + 1) := by
    rw [ht, ← hw, hM]; ring
  have hg : (f ^ p - 1) ^ (p - 1) = (f - 1) ^ (p * (p - 1)) := by
    rw [pow_mul, sub_pow_char (p := p) f 1, one_pow]
  have hu' : IsUnit (((w⁻¹ : Rˣ) : R) * (a * (a ^ M * w * t) + 1) ^ (p * (p - 1))) :=
    (Units.isUnit _).mul (hu.pow _)
  set u : R := ((w⁻¹ : Rˣ) : R) * (a * (a ^ M * w * t) + 1) ^ (p * (p - 1)) with hudef
  have hunt : ((f ^ p - 1) ^ (p - 1)).untilt = (p : R) * u := by
    rw [hg, PreTilt.untilt.map_pow, h1, mul_pow, hudef, ← hw, mul_assoc (a ^ (p * (p - 1))) (w : R),
      Units.mul_inv_cancel_left]
  have h0 : PreTilt.coeff 0 ((f ^ p - 1) ^ (p - 1)) = 0 := by
    rw [← PreTilt.mk_untilt_eq_coeff_zero, hunt]
    exact Ideal.Quotient.eq_zero_iff_mem.2
      (Ideal.mul_mem_right _ _ (mem_span_singleton_self _))
  obtain ⟨d, hd⟩ := hker _ h0
  have hdu : d.untilt = u := by
    apply hreg
    have := hunt
    rw [hd, map_mul, hpf] at this
    simpa [smul_eq_mul] using this
  have hdunit : IsUnit d := by
    apply perfection_isUnit_of_coeff_zero d
    have : IsUnit (PreTilt.coeff 0 d) := by
      rw [← PreTilt.mk_untilt_eq_coeff_zero, hdu]
      exact hu'.map _
    exact this
  rw [hd, hdunit.mul_right_dvd]
  exact hker c hc

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedDualRegularFormsFiniteCover
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.PD

theorem twistedDual_omB : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ (τ : DR k K →ₗ[K] K), IsTop k K x τ → ∀ I : Finset (Fin (d + 1)), I.Nonempty → ∀ p q : ℕ, p + q = d → ∀ y ∈ ⋀[K]^q Ω[K⁄k], (∀ a ∈ omB k K (rB k K x I) p, Algebra.trace F K (τ (a * y)) ∈ omA k x I) ↔ y ∈ omB k K (rB k K x I) q := by
  intro k _ _ F K _ _ _ _ _ _ d x hc τ hτ I hI p q hpq y hy
  obtain ⟨-, hfr, hsm⟩ := GlobalTheory.T.finite_cover_chart_smooth_normal k F K d x hc I hI
  have hrk : Module.finrank K Ω[K⁄k] = d := by
    obtain ⟨b, -⟩ := hc.exists_basis
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  have htop := (GlobalTheory.T.exists_topDegreeCoefficientForm_and_eq_on_top_forms k F K d x hc).2 τ hτ
  constructor
  · intro h
    refine GlobalTheory.T.mem_regularForms_of_wedge_pairing_perfect k K (rB k K x I) d p q hrk hpq y hy fun a ha => ?_
    have haG : a ∈ ⋀[K]^p Ω[K⁄k] := ((GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties k K (rB k K x I) p q).2.1 a ha).2.2.1
    have hay : a * y ∈ ⋀[K]^d Ω[K⁄k] := hpq ▸ SetLike.mul_mem_graded haG hy
    have hz : ∀ b ∈ rB k K x I, Algebra.trace F K (τ (a * y) * b) ∈ omA k x I := by
      intro b hb
      have hba : b • a ∈ omB k K (rB k K x I) p := ((GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties k K (rB k K x I) p q).2.1 a ha).2.2.2 b hb
      have e : τ (a * y) * b = τ ((b • a) * y) := by
        rw [smul_mul_assoc, map_smul, smul_eq_mul, mul_comm]
      rw [e]
      exact h _ hba
    obtain ⟨y', hy', e'⟩ := (GlobalTheory.T.complementaryModule_standardOpens_iff k F K d x hc τ hτ I hI (τ (a * y))).1 hz
    have hy'G : y' ∈ ⋀[K]^d Ω[K⁄k] := ((GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties k K (rB k K x I) d q).2.1 y' hy').2.2.1
    rw [htop _ hay, ← e', ← htop _ hy'G]
    exact hy'
  · intro h a ha
    have hay : a * y ∈ omB k K (rB k K x I) d := hpq ▸ (GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties k K (rB k K x I) p q).1 a ha y h
    have := (GlobalTheory.T.complementaryModule_standardOpens_iff k F K d x hc τ hτ I hI (τ (a * y))).2 ⟨a * y, hay, rfl⟩ 1 (Subalgebra.one_mem _)
    rwa [mul_one] at this

end GlobalTheory.PD

example : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ (τ : DR k K →ₗ[K] K), IsTop k K x τ → ∀ I : Finset (Fin (d + 1)), I.Nonempty → ∀ p q : ℕ, p + q = d → ∀ y ∈ ⋀[K]^q Ω[K⁄k], (∀ a ∈ omB k K (rB k K x I) p, Algebra.trace F K (τ (a * y)) ∈ omA k x I) ↔ y ∈ omB k K (rB k K x I) q := GlobalTheory.PD.twistedDual_omB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylTensorCoefSpaceLeSpanPureTensorsStatement
section
set_option autoImplicit false
noncomputable section
open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weylTensorCoefSpace_le_span_pure_tensors : ∀ (K : Type) [Field K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (S : ι → Set (MvPolynomial (Fin n × Fin n) K)), (∀ τ, nablaSq K n (lam τ) ≤ Submodule.span K (S τ)) → VV K lam ≤ Submodule.span K {P | ∃ f : ι → MvPolynomial (Fin n × Fin n) K, (∀ τ, f τ ∈ S τ) ∧ P = ten f} := by
  first | exact @GlobalTheory.coefSpace_le_span_pure_tensors | exact GlobalTheory.coefSpace_le_span_pure_tensors | (intros; apply GlobalTheory.coefSpace_le_span_pure_tensors <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.XiMuAssociatedOfPrimitiveRoots
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem frobenius_nu {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (ε : PreTilt O p) :
    WittVector.frobenius (nu ε) = mu ε := by
  unfold nu mu root
  rw [map_sub, map_one, WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller,
    frobenius_apply_frobeniusEquiv_symm]

theorem xi_mu_associated : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p),
    IsPrimitiveRoot (root ε).untilt p → ∀ ε' : PreTilt O p, IsPrimitiveRoot (root ε').untilt p →
    Associated (xi ε) (xi ε') ∧ Associated (mu ε) (mu ε') := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε ε' hε'
  obtain ⟨hdom, -, hker, -⟩ := GlobalTheory.AinfXi.ainf_local_xi_order p C v O hv ε hε
  obtain ⟨-, -, hker', -⟩ := GlobalTheory.AinfXi.ainf_local_xi_order p C v O hv ε' hε'
  have hA : Associated (xi ε) (xi ε') := by
    rw [← Ideal.span_singleton_eq_span_singleton, ← hker, ← hker']
  refine ⟨hA, ?_⟩
  obtain ⟨hS, hVR⟩ := GlobalTheory.TiltValuation.tilt_isDomain_valuationRing p C v O hv

  have key : ∀ e e' : PreTilt O p, IsPrimitiveRoot (root e).untilt p →
      Associated (xi e) (xi e') → mu e ∣ mu e' := by
    intro e e' he hee'
    obtain ⟨u, hu⟩ := hee'
    have h0 := (GlobalTheory.DetInv.mu_coeff_zero_ne_zero p C v O hv e he).1
    have hrel : ∀ i : Fin 1, mu e * WittVector.frobenius ((fun _ : Fin 1 => mu e') i) =
        WittVector.frobenius (mu e) *
          ((fun _ _ => WittVector.frobenius (u : WittVector p (PreTilt O p))) *ᵥ
            (fun _ : Fin 1 => mu e')) i := by
      intro i
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_one]
      have hφ : ∀ x : PreTilt O p, WittVector.frobenius (mu x) =
          WittVector.frobenius (xi x) * mu x := fun x => by
        conv_lhs => rw [← xi_mul_nu x, map_mul, frobenius_nu]
      rw [hφ e, hφ e', ← hu, map_mul]
      ring
    exact GlobalTheory.LemY.dvd_of_frobenius_eq p (PreTilt O p) 1 (mu e) _ _ h0 hrel 0
  exact associated_of_dvd_dvd (key ε ε' hε hA) (key ε' ε hε' hA.symm)

end GlobalTheory.DetInv
end

