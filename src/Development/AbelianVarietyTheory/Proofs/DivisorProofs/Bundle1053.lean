import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1012
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0998
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1013
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothVectorsSubspaceStableSobolevFormDeriv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0978
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0904
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0931
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1014
import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateLocalEpsilonFactorMulTameChar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import Development.AbelianVarietyTheory.Definitions.Foundations.TupleConstantsNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudeFactorFormGroupBoundedOfTestSupport
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
namespace GlobalTheory.SimBound

theorem eq_one_of_forall_prime {r : ℚ} (hr : 0 < r)
    (h : ∀ q : ℕ, q.Prime → ¬ (q : ℤ) ∣ r.num ∧ ¬ (q : ℤ) ∣ (r.den : ℤ)) : r = 1 := by
  have hn : r.num.natAbs = 1 := by
    by_contra hne
    obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hne
    exact (h q hq).1 (Int.natCast_dvd.2 hqd)
  have hd : r.den = 1 := by
    by_contra hne
    obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hne
    exact (h q hq).2 (Int.natCast_dvd_natCast.2 hqd)
  have hpos : 0 < r.num := Rat.num_pos.2 hr
  have hn1 : r.num = 1 := by omega
  rw [← Rat.num_div_den r, hn1, hd]; simp

theorem not_dvd_of_iff {r : ℚ} {q : ℕ} (hq : q.Prime) (h : (q : ℤ) ∣ r.num ↔ (q : ℤ) ∣ (r.den : ℤ)) :
    ¬ (q : ℤ) ∣ r.num ∧ ¬ (q : ℤ) ∣ (r.den : ℤ) := by
  have key : ¬ ((q : ℤ) ∣ r.num ∧ (q : ℤ) ∣ (r.den : ℤ)) := by
    rintro ⟨h1, h2⟩
    have h1' : q ∣ r.num.natAbs := Int.natCast_dvd.1 h1
    have h2' : q ∣ r.den := Int.natCast_dvd_natCast.1 h2
    have h3 : q ∣ Nat.gcd r.num.natAbs r.den := Nat.dvd_gcd h1' h2'
    rw [r.reduced.gcd_eq_one] at h3
    exact hq.one_lt.ne' (Nat.dvd_one.1 h3)
  exact ⟨fun h1 => key ⟨h1, h.1 h1⟩, fun h2 => key ⟨h.2 h2, h2⟩⟩

theorem not_dvd_of_padicNorm (p : ℕ) [Fact p.Prime] {r : ℚ} (hr : padicNorm p r = 1) :
    ¬ (p : ℤ) ∣ r.num ∧ ¬ (p : ℤ) ∣ (r.den : ℤ) := by
  have e : padicNorm p (r.num : ℚ) = padicNorm p ((r.den : ℤ) : ℚ) := by
    rw [← Rat.mul_den_eq_num, padicNorm.mul, hr, one_mul, Int.cast_natCast]
  refine not_dvd_of_iff (Fact.out : p.Prime) ?_
  rw [← padicNorm.int_lt_one_iff, ← padicNorm.int_lt_one_iff, e]

theorem not_dvd_of_valuation {q : ℕ} (hq : q.Prime) (v : HeightOneSpectrum ℤ)
    (hv : v.asIdeal = Ideal.span {(q : ℤ)}) {r : ℚ} (hr : v.valuation ℚ r = 1) :
    ¬ (q : ℤ) ∣ r.num ∧ ¬ (q : ℤ) ∣ (r.den : ℤ) := by
  have e : v.valuation ℚ (algebraMap ℤ ℚ r.num) = v.valuation ℚ (algebraMap ℤ ℚ (r.den : ℤ)) := by
    rw [algebraMap_int_eq, eq_intCast, eq_intCast, ← Rat.mul_den_eq_num, map_mul, hr, one_mul,
      Int.cast_natCast]
  refine not_dvd_of_iff hq ?_
  rw [← Ideal.mem_span_singleton, ← Ideal.mem_span_singleton, ← hv, ← valuation_lt_one_iff_mem (K := ℚ),
    ← valuation_lt_one_iff_mem (K := ℚ), e]

def placeOf (p : ℕ) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) : AwayP p :=
  ⟨⟨Ideal.span {(q : ℤ)}, (Ideal.span_singleton_prime (by exact_mod_cast hq.ne_zero)).2
      (Nat.prime_iff_prime_int.1 hq), by simpa using hq.ne_zero⟩, fun h => hqp (by
    have h1 := Ideal.span_singleton_eq_span_singleton.1 h
    have h2 := Int.natAbs_eq_natAbs_iff.2 (Int.associated_iff.1 h1)
    simpa using h2)⟩

theorem eq_one_of_units (p : ℕ) [Fact p.Prime] {r : ℚ} (hr : 0 < r)
    (hw : ∀ w : AwayP p, Valued.v (algebraMap ℚ (w.1.adicCompletion ℚ) r) = 1) (hp : padicNorm p r = 1) :
    r = 1 := by
  refine eq_one_of_forall_prime hr fun q hq => ?_
  by_cases hqp : q = p
  · subst hqp; exact not_dvd_of_padicNorm q hp
  · refine not_dvd_of_valuation hq (placeOf p hq hqp).1 rfl ?_
    rw [← valuedAdicCompletion_eq_valuation']
    exact hw (placeOf p hq hqp)

theorem valued_snd_eq_one {p : ℕ} [Fact p.Prime] (G : HTGroup p) (K : Subgroup G.GAf)
    (hK : IsCompact (K : Set G.GAf)) (w : AwayP p) {k : G.GAf} (hk : k ∈ K) :
    Valued.v (AfP.eval w (((k : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : (AfP p)ˣ) : AfP p)) = 1 := by
  letI : NontriviallyNormedField (w.1.adicCompletion ℚ) := Valued.toNontriviallyNormedField _ _
  let F : G.GAf → ℝ := fun g => ‖AfP.eval w (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : (AfP p)ˣ) : AfP p)‖
  have hev : Continuous (fun x : AfP p => AfP.eval w x) :=
    RestrictedProduct.continuous_eval (R := fun v : AwayP p => v.1.adicCompletion ℚ)
      (A := fun v : AwayP p => (v.1.adicCompletionIntegers ℚ : Set (v.1.adicCompletion ℚ))) w
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  have hF : Continuous F :=
    continuous_norm.comp (hev.comp (Units.continuous_val.comp (continuous_snd.comp continuous_subtype_val)))
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF.continuousOn
  have hmul : ∀ a b : G.GAf, F (a * b) = F a * F b := fun a b => by
    simp only [F, Subgroup.coe_mul, Prod.snd_mul, Units.val_mul, map_mul, norm_mul]
  have hone : F 1 = 1 := by simp [F]
  have hpow : ∀ (a : G.GAf) (n : ℕ), F (a ^ n) = F a ^ n := fun a n => by
    induction n with
    | zero => simpa using hone
    | succ n ih => rw [pow_succ, hmul, ih, pow_succ]
  have hle : ∀ a ∈ K, F a ≤ 1 := by
    intro a ha
    by_contra hlt
    push_neg at hlt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C hlt
    have h1 := hC (a ^ n) (K.pow_mem ha n)
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at h1
    have : F (a ^ n) = F a ^ n := hpow a n
    linarith
  have h1 := hle k hk
  have h2 := hle k⁻¹ (K.inv_mem hk)
  have h3 : F k⁻¹ * F k = 1 := by rw [← hmul, inv_mul_cancel, hone]
  have h0 : 0 ≤ F k⁻¹ := norm_nonneg _
  have h0' : 0 ≤ F k := norm_nonneg _
  have hk1 : F k = 1 := by nlinarith
  have hle1 : Valued.v (AfP.eval w (((k : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : (AfP p)ˣ) : AfP p)) ≤ 1 :=
    Valued.toNormedField.norm_le_one_iff.1 hk1.le
  have hnlt : ¬ Valued.v (AfP.eval w (((k : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : (AfP p)ˣ) : AfP p)) < 1 :=
    fun h => by
      have := Valued.toNormedField.norm_lt_one_iff.2 h
      exact absurd hk1 (ne_of_lt this)
  exact le_antisymm hle1 (not_lt.1 hnlt)

noncomputable def nu1 (p : ℕ) [Fact p.Prime] (g : GL (Fin 1) (Qr p 1)) : ℝ :=
  ‖(((g : Matrix (Fin 1) (Fin 1) (Qr p 1)) 0 0 : Qr p 1) : PadicAlgCl p)‖

theorem glOneUnramifiedEntryNorm_mul (p : ℕ) [Fact p.Prime] (a b : GL (Fin 1) (Qr p 1)) : nu1 p (a * b) = nu1 p a * nu1 p b := by
  simp only [nu1, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_one, IntermediateField.coe_mul, norm_mul]

theorem glOneUnramifiedEntryNorm_one (p : ℕ) [Fact p.Prime] : nu1 p 1 = 1 := by simp [nu1]

theorem glOneUnramifiedEntryNorm_le_one_of_integral (p : ℕ) [Fact p.Prime] {k : GL (Fin 1) (Qr p 1)} (hk : k ∈ GlobalTheory.LKLoc.Kint p (Q0 p) 1 1) :
    nu1 p k ≤ 1 := by
  obtain ⟨u, rfl⟩ := hk
  have h := ((u : Matrix (Fin 1) (Fin 1) (GlobalTheory.LKLoc.intR p (Q0 p) 1)) 0 0).2
  exact ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Obar_iff.1 h

theorem glOneUnramifiedEntryNorm_eq_one_of_integral (p : ℕ) [Fact p.Prime] {k : GL (Fin 1) (Qr p 1)}
    (hk : k ∈ GlobalTheory.LKLoc.Kint p (Q0 p) 1 1) : nu1 p k = 1 := by
  have h1 := glOneUnramifiedEntryNorm_le_one_of_integral p hk
  have h2 := glOneUnramifiedEntryNorm_le_one_of_integral p ((GlobalTheory.LKLoc.Kint p (Q0 p) 1 1).inv_mem hk)
  have h3 : nu1 p k⁻¹ * nu1 p k = 1 := by rw [← glOneUnramifiedEntryNorm_mul, inv_mul_cancel, glOneUnramifiedEntryNorm_one]
  have h0 : 0 ≤ nu1 p k⁻¹ := norm_nonneg _
  have h0' : 0 ≤ nu1 p k := norm_nonneg _
  nlinarith

theorem glOneUnramifiedEntryNorm_rat_scalar_eq_padicNorm (p : ℕ) [Fact p.Prime] (s : ℚˣ) :
    nu1 p (GeneralLinearGroup.scalar (Fin 1) (Units.map (algebraMap ℚ_[p] (Qr p 1)).toMonoidHom
      (Units.map (algebraMap ℚ ℚ_[p]).toMonoidHom s))) = ((padicNorm p (s : ℚ) : ℚ) : ℝ) := by
  have e : nu1 p (GeneralLinearGroup.scalar (Fin 1) (Units.map (algebraMap ℚ_[p] (Qr p 1)).toMonoidHom
      (Units.map (algebraMap ℚ ℚ_[p]).toMonoidHom s))) = ‖(((s : ℚ) : ℚ_[p]) : PadicAlgCl p)‖ := by
    simp [nu1, GeneralLinearGroup.scalar]
  rw [e, PadicAlgCl.norm_extends, Padic.eq_padicNorm]

noncomputable def lam {p : ℕ} [Fact p.Prime] (G : HTGroup p) (w : AwayP p) (g : G.GAf) : WithZero (Multiplicative ℤ) :=
  Valued.v (AfP.eval w (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : (AfP p)ˣ) : AfP p))

theorem lam_mul {p : ℕ} [Fact p.Prime] (G : HTGroup p) (w : AwayP p) (a b : G.GAf) :
    lam G w (a * b) = lam G w a * lam G w b := by
  simp only [lam, Subgroup.coe_mul, Prod.snd_mul, Units.val_mul, map_mul]

theorem lam_one {p : ℕ} [Fact p.Prime] (G : HTGroup p) (w : AwayP p) : lam G w 1 = 1 := by
  simp [lam]

theorem away {p : ℕ} [Fact p.Prime] (G : HTGroup p) (L : G.Level) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ)
    (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t) (y : grp G β) (h σ k₁ k₂ : G.GAf) (hk₁ : k₁ ∈ L.K.toSubgroup)
    (hk₂ : k₂ ∈ L.K.toSubgroup) (e : h⁻¹ * toAfF G β x t hx y * h = k₁ * σ * k₂) (w : AwayP p) :
    Valued.v (algebraMap ℚ (w.1.adicCompletion ℚ) (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ)) = lam G w σ := by
  have hc : IsCompact (L.K.toSubgroup : Set G.GAf) := L.compact
  have e1 : lam G w k₁ = 1 := valued_snd_eq_one G _ hc w hk₁
  have e2 : lam G w k₂ = 1 := valued_snd_eq_one G _ hc w hk₂
  have e3 := congrArg (lam G w) e
  rw [lam_mul, lam_mul, lam_mul, lam_mul, e1, e2, one_mul, mul_one] at e3
  have e4 : lam G w (toAfF G β x t hx y) = lam G w σ := by
    rw [← e3, mul_right_comm, ← lam_mul, inv_mul_cancel, lam_one, one_mul]
  rw [← e4]
  show _ = Valued.v (AfP.eval w (algebraMap ℚ (AfP p) (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ)))
  rw [AlgHom.commutes]

theorem atp {p : ℕ} [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ) (y : grp G β) (h σ k₁ k₂ : Gr G 1)
    (hk₁ : k₁ ∈ KHT p G.m G.n 1 G.Fw) (hk₂ : k₂ ∈ KHT p G.m G.n 1 G.Fw)
    (e : h⁻¹ * toP1 G β y * h = k₁ * σ * k₂) :
    ((padicNorm p (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℚ) : ℝ) = nu1 p σ.1 := by
  have e1 : nu1 p k₁.1 = 1 := glOneUnramifiedEntryNorm_eq_one_of_integral p hk₁.1
  have e2 : nu1 p k₂.1 = 1 := glOneUnramifiedEntryNorm_eq_one_of_integral p hk₂.1
  have e3 := congrArg (fun g : Gr G 1 => nu1 p g.1) e
  simp only [Prod.fst_mul, Prod.fst_inv, glOneUnramifiedEntryNorm_mul, e1, e2, one_mul, mul_one] at e3
  have e4 : nu1 p (toP1 G β y).1 = nu1 p σ.1 := by
    rw [← e3, mul_right_comm, ← glOneUnramifiedEntryNorm_mul, inv_mul_cancel, glOneUnramifiedEntryNorm_one, one_mul]
  rw [← e4]
  exact (glOneUnramifiedEntryNorm_rat_scalar_eq_padicNorm p _).symm

theorem eq_of_valuations {p : ℕ} [Fact p.Prime] {s s₀ : ℚ} (hs : 0 < s) (hs₀ : 0 < s₀)
    (hw : ∀ w : AwayP p, Valued.v (algebraMap ℚ (w.1.adicCompletion ℚ) s) =
      Valued.v (algebraMap ℚ (w.1.adicCompletion ℚ) s₀))
    (hp : padicNorm p s = padicNorm p s₀) : s = s₀ := by
  have h := eq_one_of_units p (r := s * s₀⁻¹) (mul_pos hs (inv_pos.2 hs₀)) (fun w => by
      have h0 : Valued.v (algebraMap ℚ (w.1.adicCompletion ℚ) s₀) ≠ 0 :=
        (Valuation.ne_zero_iff _).2 ((map_ne_zero _).2 hs₀.ne')
      rw [map_mul, map_mul, map_inv₀, map_inv₀, hw w, mul_inv_cancel₀ h0])
    (by
      have h0 : padicNorm p s₀ ≠ 0 := fun h => hs₀.ne' (padicNorm.zero_of_padicNorm_eq_zero h)
      rw [← div_eq_mul_inv, padicNorm.div, hp, div_self h0])
  exact (mul_inv_eq_one₀ hs₀.ne').1 h

theorem main : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ),
    IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ),
    IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t), ∃ S : ℝ, ∀ (y : grp G β) (h₁ : G.GAf) (h₂ : Gr G 1),
      f (h₁⁻¹ * toAfF G β x t hx y * h₁) ≠ 0 → f' (h₂⁻¹ * toP1 G β y * h₂) ≠ 0 →
      (((y : G.Cˣ × ℚˣ).2 : ℚ) : ℝ) ≤ S := by
  intro p _ G L f hf K' f' hf' β x t hx
  obtain ⟨T, hT⟩ := hf.2.2.2
  obtain ⟨T', hT'⟩ := hf'.2.2.2
  let M : G.GAf → Gr G 1 → ℚ → Prop := fun σ σ' s => 0 < s ∧
    (∀ w : AwayP p, Valued.v (algebraMap ℚ (w.1.adicCompletion ℚ) s) = lam G w σ) ∧
    ((padicNorm p s : ℚ) : ℝ) = nu1 p σ'.1
  let g : G.GAf → Gr G 1 → ℝ := fun σ σ' => if h : ∃ s, M σ σ' s then ((h.choose : ℚ) : ℝ) else 0
  have g_nonneg : ∀ σ σ', 0 ≤ g σ σ' := by
    intro σ σ'
    simp only [g]
    split_ifs with h
    · exact_mod_cast h.choose_spec.1.le
    · exact le_rfl
  refine ⟨∑ σ ∈ T, ∑ σ' ∈ T', g σ σ', ?_⟩
  intro y h₁ h₂ h1 h2
  obtain ⟨σ, hσ, k₁, hk₁, k₂, hk₂, e⟩ := hT _ h1
  obtain ⟨σ', hσ', k₁', hk₁', k₂', hk₂', e'⟩ := hT' _ h2
  have hM : M σ σ' (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) :=
    ⟨y.2.2, fun w => away G L β x t hx y h₁ σ k₁ k₂ hk₁ hk₂ e w, atp G β y h₂ σ' k₁' k₂' hk₁' hk₂' e'⟩
  have hex : ∃ s, M σ σ' s := ⟨_, hM⟩
  have heq : (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) = hex.choose :=
    eq_of_valuations hM.1 hex.choose_spec.1 (fun w => by rw [hM.2.1 w, hex.choose_spec.2.1 w])
      (by exact_mod_cast hM.2.2.trans hex.choose_spec.2.2.symm)
  have hg : ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) = g σ σ' := by
    simp only [g, dif_pos hex, heq]
  rw [hg]
  calc g σ σ' ≤ ∑ σ'' ∈ T', g σ σ'' :=
        Finset.single_le_sum (f := fun σ'' => g σ σ'') (fun i _ => g_nonneg σ i) hσ'
    _ ≤ ∑ σ₀ ∈ T, ∑ σ'' ∈ T', g σ₀ σ'' :=
        Finset.single_le_sum (f := fun σ₀ => ∑ σ'' ∈ T', g σ₀ σ'')
          (fun i _ => Finset.sum_nonneg fun j _ => g_nonneg i j) hσ

end GlobalTheory.SimBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudePairHermitianFormInvertibleSimilitudeStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.similitudePair_hermitianForm_invertible_similitude : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (v : InfinitePlace G.F), (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)).IsHermitian ∧ (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)).det ≠ 0 ∧ (G.psi v P.γ)ᴴ * (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) * G.psi v P.γ = ((P.c : ℚ) : ℂ) • (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) := by
  first | (exact @GlobalTheory.LKMid.pair_form_laws) | (exact GlobalTheory.LKMid.pair_form_laws) | (intros; apply GlobalTheory.LKMid.pair_form_laws  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudePairRegularImageAtPStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.similitudePair_regular_image_at_p : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G), (∀ w, (P.atP.2 w).val.charpoly = P.pol.map (G.embW w)) ∧ regular₂ G P.atP ∧ ∀ y : P.cent, locC G y.1 ∈ Subgroup.centralizer {P.atP} := by
  first | (exact @GlobalTheory.LKMid.atP_regular) | (exact GlobalTheory.LKMid.atP_regular) | (intros; apply GlobalTheory.LKMid.atP_regular  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudeSignatureOnePreservesPosDefForm
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical ComplexOrder

namespace GlobalTheory.PositiveDefiniteFormIdentities

theorem form_pull {n : ℕ} (h Z : Matrix (Fin n) (Fin n) ℂ) (v v' : Fin n → ℂ) :
    star (Z *ᵥ v) ⬝ᵥ h *ᵥ (Z *ᵥ v') = star v ⬝ᵥ (Zᴴ * h * Z) *ᵥ v' := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]

theorem form_swap {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℂ} (hQ : Q.IsHermitian) (x y : Fin n → ℂ) :
    star y ⬝ᵥ Q *ᵥ x = star (star x ⬝ᵥ Q *ᵥ y) := by
  rw [star_dotProduct, star_mulVec, hQ.eq, ← dotProduct_mulVec]

theorem form_expand {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℂ} (hQ : Q.IsHermitian) (w z : Fin n → ℂ) (a : ℂ)
    (hwz : star z ⬝ᵥ Q *ᵥ w = 0) :
    star (w + a • z) ⬝ᵥ Q *ᵥ (w + a • z) =
      star w ⬝ᵥ Q *ᵥ w + (Complex.normSq a : ℂ) * (star z ⬝ᵥ Q *ᵥ z) := by
  have hzw : star w ⬝ᵥ Q *ᵥ z = 0 := by rw [form_swap hQ, hwz, star_zero]
  simp only [star_add, star_smul, mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add,
    smul_dotProduct, dotProduct_smul, hwz, hzw, smul_eq_mul, Complex.normSq_eq_conj_mul_self, RCLike.star_def]
  ring

theorem form_self_ofReal {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℂ} (hQ : Q.IsHermitian) (x : Fin n → ℂ) :
    ((star x ⬝ᵥ Q *ᵥ x).re : ℂ) = star x ⬝ᵥ Q *ᵥ x := by
  have h := form_swap hQ x x
  exact Complex.conj_eq_iff_re.mp h.symm

end GlobalTheory.PositiveDefiniteFormIdentities

namespace GlobalTheory

open GlobalTheory.PositiveDefiniteFormIdentities in

theorem similitude_preserves_posDef : ∀ (n : ℕ) (h Q M : Matrix (Fin n) (Fin n) ℂ) (hh : h.IsHermitian) (Z : GL (Fin n) ℂ) (s : ℝ), h.det ≠ 0 → sigPosH hh = 1 → Q = (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ * h * (Z : Matrix (Fin n) (Fin n) ℂ) → 0 < s → Mᴴ * Q * M = (s : ℂ) • Q → ∀ (z : Fin n → ℂ) (c : ℂ), 0 < (star z ⬝ᵥ Q *ᵥ z).re → M *ᵥ z = c • z → ∃ H : Matrix (Fin n) (Fin n) ℂ, H.PosDef ∧ Mᴴ * H * M = (s : ℂ) • H := by
  intro n h Q M hh Z s hdet hsig hQZ hs hsim z c hz hMz
  set Zm : Matrix (Fin n) (Fin n) ℂ := (Z : Matrix (Fin n) (Fin n) ℂ) with hZm
  have hQ : Q.IsHermitian := by
    rw [hQZ]
    simp [IsHermitian, conjTranspose_mul, hh.eq, Matrix.mul_assoc]
  set q0 : ℝ := (star z ⬝ᵥ Q *ᵥ z).re with hq0
  have hq : star z ⬝ᵥ Q *ᵥ z = (q0 : ℂ) := (form_self_ofReal hQ z).symm
  have hq0ne : (q0 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz.ne'
  set u : Fin n → ℂ := Q *ᵥ z with hu
  set H : Matrix (Fin n) (Fin n) ℂ := ((2 / q0 : ℝ) : ℂ) • vecMulVec u (star u) - Q with hH
  have hsu : ∀ x : Fin n → ℂ, star u ⬝ᵥ x = star z ⬝ᵥ Q *ᵥ x := by
    intro x
    rw [hu, star_mulVec, ← dotProduct_mulVec, hQ.eq]
  have hus : ∀ x : Fin n → ℂ, star x ⬝ᵥ u = star (star z ⬝ᵥ Q *ᵥ x) := by
    intro x
    rw [hu, ← form_swap hQ]

  have hval : ∀ x : Fin n → ℂ, star x ⬝ᵥ H *ᵥ x =
      ((2 / q0 * Complex.normSq (star z ⬝ᵥ Q *ᵥ x) - (star x ⬝ᵥ Q *ᵥ x).re : ℝ) : ℂ) := by
    intro x
    rw [hH, sub_mulVec, Matrix.smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul, dotProduct_sub,
      dotProduct_smul, dotProduct_smul, hsu, hus, smul_eq_mul, smul_eq_mul]
    have e := form_self_ofReal hQ x
    push_cast
    rw [e, Complex.normSq_eq_conj_mul_self, Complex.star_def]
    ring
  have hHh : H.IsHermitian := by
    rw [hH]
    refine IsHermitian.sub ?_ hQ
    ext i j
    simp [vecMulVec_apply, mul_comm]
  have hpos : H.PosDef := by
    refine PosDef.of_dotProduct_mulVec_pos hHh fun x hx => ?_
    rw [hval x]
    refine Complex.zero_lt_real.mpr ?_
    set p := star z ⬝ᵥ Q *ᵥ x with hp
    set a : ℂ := p / (q0 : ℂ) with ha
    have hpa : p = a * q0 := by rw [ha]; field_simp
    set w := x - a • z with hw
    have hxw : x = w + a • z := by rw [hw]; abel
    have hwz : star z ⬝ᵥ Q *ᵥ w = 0 := by
      rw [hw, mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, smul_eq_mul, hq, ← hp, hpa, sub_self]
    have hexp : star x ⬝ᵥ Q *ᵥ x = star w ⬝ᵥ Q *ᵥ w + (Complex.normSq a : ℂ) * q0 := by
      conv_lhs => rw [hxw]
      rw [form_expand hQ w z a hwz, hq]
    have hre : (star x ⬝ᵥ Q *ᵥ x).re = (star w ⬝ᵥ Q *ᵥ w).re + Complex.normSq a * q0 := by
      rw [hexp, Complex.add_re, ← Complex.ofReal_mul, Complex.ofReal_re]
    have hnp : Complex.normSq p = Complex.normSq a * q0 ^ 2 := by
      rw [hpa, Complex.normSq_mul, Complex.normSq_ofReal]; ring
    have h2 : 2 / q0 * (Complex.normSq a * q0 ^ 2) = 2 * Complex.normSq a * q0 := by
      field_simp
    rw [hre, hnp, h2]
    by_cases hw0 : w = 0
    · have ha0 : a ≠ 0 := by
        intro ha0
        apply hx
        rw [hxw, hw0, ha0, zero_smul, add_zero]
      have e : (star w ⬝ᵥ Q *ᵥ w).re = 0 := by simp [hw0]
      rw [e]
      nlinarith [Complex.normSq_pos.mpr ha0]
    · have hZw : Zm *ᵥ w ≠ 0 := by
        intro h0
        apply hw0
        have hinv : ((Z⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) * Zm = 1 := Units.inv_mul Z
        calc w = (((Z⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) * Zm) *ᵥ w := by rw [hinv, one_mulVec]
          _ = 0 := by rw [← mulVec_mulVec, h0, mulVec_zero]
      have hneg := re_form_neg_of_orth_of_sigPosH_eq_one h hh hdet hsig (Zm *ᵥ z) (Zm *ᵥ w)
        (by rw [form_pull, ← hQZ]; exact hz) (by rw [form_pull, ← hQZ]; exact hwz) hZw
      rw [form_pull, ← hQZ] at hneg
      nlinarith [Complex.normSq_nonneg a]
  have hs0 : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  have hc : star c * c = (s : ℂ) := by
    have e1 := congrArg (fun A => star z ⬝ᵥ A *ᵥ z) hsim
    rw [← form_pull Q M z z, hMz] at e1
    simp only [star_smul, mulVec_smul, smul_mulVec, smul_dotProduct, dotProduct_smul, smul_eq_mul] at e1
    rw [← hu, hq] at e1
    have e3 : (star c * c - s) * (q0 : ℂ) = 0 := by linear_combination e1
    exact sub_eq_zero.mp ((mul_eq_zero.mp e3).resolve_right hq0ne)
  have hMu : Mᴴ *ᵥ u = star c • u := by
    have e2 := congrArg (fun A => A *ᵥ z) hsim
    rw [← mulVec_mulVec, ← mulVec_mulVec, hMz, mulVec_smul, mulVec_smul, smul_mulVec, ← hu] at e2
    apply smul_right_injective _ hs0
    change (s : ℂ) • (Mᴴ *ᵥ u) = (s : ℂ) • (star c • u)
    calc (s : ℂ) • (Mᴴ *ᵥ u) = star c • (c • Mᴴ *ᵥ u) := by rw [smul_smul, hc]
      _ = star c • ((s : ℂ) • u) := by rw [e2]
      _ = (s : ℂ) • (star c • u) := smul_comm _ _ _
  have hstar : star u ᵥ* M = c • star u := by
    have e : star (Mᴴ *ᵥ u) = star u ᵥ* M := by rw [star_mulVec, conjTranspose_conjTranspose]
    rw [← e, hMu, star_smul, star_star]
  have hM1 : Mᴴ * vecMulVec u (star u) * M = (s : ℂ) • vecMulVec u (star u) := by
    rw [mul_vecMulVec, vecMulVec_mul, hMu, hstar, ← hc]
    ext i j
    simp [vecMulVec_apply]
    ring
  refine ⟨H, hpos, ?_⟩
  rw [hH, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, hM1, hsim, smul_sub,
    smul_comm ((2 / q0 : ℝ) : ℂ) (s : ℂ)]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothGramSchmidtIndefiniteHermitianFramesStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_gram_schmidt_indefinite_hermitian_frames : ∀ (n : ℕ) (Hm : Mt n) (q : ℕ) (x₀ : Mt n), OrthFr Hm q x₀ → ∃ β : (Fin n → Fin n → ℂ) → (Fin n → Fin n → ℂ), ContDiffOn ℝ ∞ β {x | Matrix.of x ∈ frDom Hm q} ∧ ∀ x : Fin n → Fin n → ℂ, Matrix.of x ∈ frDom Hm q → UpT (Matrix.of (β x)) ∧ Matrix.of x * (Matrix.of (β x))⁻¹ * x₀⁻¹ ∈ Formalism.QuantumDeterminants.UH Hm := by
  first | exact @GlobalTheory.HolDict.GS.smooth_gramSchmidt | exact GlobalTheory.HolDict.GS.smooth_gramSchmidt | (intros; apply GlobalTheory.HolDict.GS.smooth_gramSchmidt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothVectorsSubspaceStableSobolevFormDerivStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothVectors_subspace_stable_sobolevForm_deriv : ∀ (n : ℕ) (Hm : Mt n) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mt n → (H →L[ℂ] H)), Hm.IsHermitian → Hm.det ≠ 0 → IsURepOn (Formalism.QuantumDeterminants.UH Hm) σ → (∀ v ∈ Submodule.span ℂ {w | SmoothVec (lieH Hm) σ w}, SmoothVec (lieH Hm) σ v) ∧ ∀ v, SmoothVec (lieH Hm) σ v → (∀ g ∈ Formalism.QuantumDeterminants.UH Hm, SmoothVec (lieH Hm) σ (σ g v)) ∧ (∀ X ∈ lieH Hm, SmoothVec (lieH Hm) σ (dRep σ X v) ∧ HasDerivAt (fun t : ℝ => σ (NormedSpace.exp (t • X)) v) (dRep σ X v) 0) ∧ (∀ Z, SmoothVec (lieH Hm) σ (dRepC Hm σ Z v)) ∧ ∀ ℓ : H →ₗ[ℂ] ℂ, Sobolev₂ (lieH Hm) σ ℓ → ∀ X ∈ lieH Hm, HasDerivAt (fun t : ℝ => ℓ (σ (NormedSpace.exp (t • X)) v)) (ℓ (dRep σ X v)) 0 := by
  first | exact @GlobalTheory.UnitarySmVec.smoothVec_basic | exact GlobalTheory.UnitarySmVec.smoothVec_basic | (intros; apply GlobalTheory.UnitarySmVec.smoothVec_basic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothVectorsUnitaryRepStableConjSkewAdjointStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothVectors_unitaryRep_stable_conj_skewAdjoint : ∀ (n : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (J : Matrix (Fin n) (Fin n) ℂ) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Jᴴ = J → IsUnit J.det → IsURepOn (Formalism.QuantumDeterminants.UH J) π → ∀ v, SmoothVec {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0} π v → (∀ g ∈ Formalism.QuantumDeterminants.UH J, SmoothVec {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0} π (π g v)) ∧ (∀ w, SmoothVec {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0} π w → ∀ c : ℂ, SmoothVec {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0} π (v + c • w)) ∧ ∀ X ∈ {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0}, SmoothVec {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0} π (dRep π X v) ∧ HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) v) (dRep π X v) 0 ∧ (∀ g ∈ Formalism.QuantumDeterminants.UH J, π g (dRep π X v) = dRep π (g * X * g⁻¹) (π g v)) ∧ (∀ c : ℝ, dRep π (c • X) v = (c : ℂ) • dRep π X v) ∧ ∀ w, SmoothVec {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0} π w → ⟪dRep π X v, w⟫_ℂ = -⟪v, dRep π X w⟫_ℂ ∧ ∀ c : ℂ, dRep π X (v + c • w) = dRep π X v + c • dRep π X w := by
  first | exact @GlobalTheory.SmVecCalc.smooth_calculus | exact GlobalTheory.SmVecCalc.smooth_calculus | (intros; apply GlobalTheory.SmVecCalc.smooth_calculus <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothingAffineFamilyEqIntegralKernelStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothing_affine_family_eq_integral_kernel : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] (σ₀ : Fin n → Fin n → Cinf E) (L : Z →L[ℝ] (Fin n → Fin n → Cinf E)) (χ : Z → ℂ) (α : (Fin n → Fin n → Cinf E) → ℂ), HasCompactSupport χ → (∀ z ∈ tsupport χ, IsUnit (Matrix.of (σ₀ + L z))) → HasCompactSupport α → tsupport α ⊆ {x | IsUnit (Matrix.of x)} → ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (κ : X → ℂ) (τ : X → (Z × (Fin n → Fin n → Cinf E)) →L[ℝ] ℝ), Measurable κ → (∀ z, Measurable fun x => τ x z) → (∀ N : ℕ, Integrable (fun x => ‖κ x‖ * (1 + ‖τ x‖) ^ N) ν) → (∀ z a, χ z * ((jacInf (Matrix.of (σ₀ + L z)) : ℝ) : ℂ) * α a = ∫ x, κ x * (𝐞 (τ x (z, a)) : ℂ) ∂ν) → ∃ R : ℝ, ∀ W : GL (Fin n) (Cinf E) → ℂ, IsModGrowthInf W → ∀ q z g, χ z * smoothMatInf α W (g * (toGLInf (Matrix.of (σ₀ + L z)))⁻¹ * q) = ∫ p, secKInf R σ₀ κ τ q p * (𝐞 (secEtaInf L τ q p z) : ℂ) * W (g * toGLInf (Matrix.of p.1)) ∂((volume : Measure (Fin n → Fin n → Cinf E)).prod ν) := by
  first | exact @GlobalTheory.JSW.MirCinf.smoothMatInf_affine_eq_integral_secKInf | exact GlobalTheory.JSW.MirCinf.smoothMatInf_affine_eq_integral_secKInf | (intros; apply GlobalTheory.JSW.MirCinf.smoothMatInf_affine_eq_integral_secKInf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncChartEquationsDifferUnit
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LogPair

theorem sncChart_germ_eqn_unit : ∀ {R : Type} [CommRing R] {Y : Scheme.{0}} (g : Y ⟶ Sp R) {n s : ℕ} (L : Fin s → LB Y) (σ : ∀ i, (L i).Sec), (∀ i, (L i).IsLB) → ∀ (C C' : SncChart g n L σ) (y : Y) (hy : y ∈ C.U) (hy' : y ∈ C'.U) (c : Fin s), ∃ v : (Y.presheaf.stalk y)ˣ, (Y.presheaf.germ C.U y hy).hom ((C.e c).elim 1 C.t) = v * (Y.presheaf.germ C'.U y hy').hom ((C'.e c).elim 1 C'.t) := by
  intro R _ Y g n s L σ hL C C' y hy hy' c
  have hyi : y ∈ (L c).U (C.c c) := C.le c hy
  have hyj : y ∈ (L c).U (C'.c c) := C'.le c hy'
  have hyij : y ∈ (L c).U (C.c c) ⊓ (L c).U (C'.c c) := ⟨hyi, hyj⟩
  have e1 := congrArg (Y.presheaf.germ C.U y hy).hom (C.eq c)
  have e2 := congrArg (Y.presheaf.germ C'.U y hy').hom (C'.eq c)
  have e3 := congrArg (Y.presheaf.germ _ y hyij).hom ((σ c).2 (C.c c) (C'.c c))
  simp only [resG, map_mul, TopCat.Presheaf.germ_res_apply] at e1 e2 e3
  let w0 := Units.map (Y.presheaf.germ C.U y hy).hom.toMonoidHom (C.u c)
  let w1 := Units.map (Y.presheaf.germ C'.U y hy').hom.toMonoidHom (C'.u c)
  let wg := Units.map (Y.presheaf.germ _ y hyij).hom.toMonoidHom ((L c).g (C.c c) (C'.c c))
  refine ⟨w0⁻¹ * wg * w1, ?_⟩
  have key : (w0 : Y.presheaf.stalk y) * (Y.presheaf.germ C.U y hy).hom ((C.e c).elim 1 C.t) =
      (wg : Y.presheaf.stalk y) * ((w1 : Y.presheaf.stalk y) * (Y.presheaf.germ C'.U y hy').hom ((C'.e c).elim 1 C'.t)) := by
    exact e1.symm.trans (e3.trans (congrArg (fun z => _ * z) e2))
  calc (Y.presheaf.germ C.U y hy).hom ((C.e c).elim 1 C.t)
      = ((w0⁻¹ : (Y.presheaf.stalk y)ˣ) : Y.presheaf.stalk y) * ((w0 : Y.presheaf.stalk y) * (Y.presheaf.germ C.U y hy).hom ((C.e c).elim 1 C.t)) := by
        rw [← mul_assoc, Units.inv_mul, one_mul]
    _ = _ := by rw [key]; simp only [Units.val_mul, mul_assoc]

end GlobalTheory.LogPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrongApproximationNormOneDivisionQuaternionStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_closure_normOne_of_strongApproximation : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → (∀ x : ℍ[F, a, b], nrm x = 0 → x = 0) → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → (∀ t : AF F, ∃ h : DA F a b, nrm h = 1 ∧ ε * h.re = ε * t) → ∀ g : DA F a b, nrm g = 1 → g ∈ closure (H0 (a := a) (b := b) ε) := by
  first | exact @GlobalTheory.QSA.DivAssembly.strongApproximation_normOne_divisionQuaternion | exact GlobalTheory.QSA.DivAssembly.strongApproximation_normOne_divisionQuaternion | (intros; apply GlobalTheory.QSA.DivAssembly.strongApproximation_normOne_divisionQuaternion <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateLocalEpsilonFactorMulTameCharStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.HeckeEps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateLocalEpsilonFactor_mul_tameChar : ∀ (E : Type) [Field E] [NumberField E] (χ ξ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (q : ℕ) (s : ℂ), q.Prime → Nat.card (𝓞 E ⧸ w.asIdeal) = q → (q : 𝓞 E) ∉ w.asIdeal ^ 2 → ExpAt χ w 2 → ξ.TameAt w → ExpAt (χ * ξ) w 2 ∧ ∃ y : Eˣ, locEps (χ * ξ) w 2 s = ((ξ.locK w y : ℂˣ) : ℂ) * locEps χ w 2 s := by
  first | exact @GlobalTheory.TameTwist.locEps_mul_tame | exact GlobalTheory.TameTwist.locEps_mul_tame | (intros; apply GlobalTheory.TameTwist.locEps_mul_tame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistLocalToGlobalStrictlyHenselianStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etC_b3 : GlobalTheory.EtC.B3 := by
  first | (exact @GlobalTheory.EtC.tateTwist_local_to_global_strictlyHenselian) | (exact GlobalTheory.EtC.tateTwist_local_to_global_strictlyHenselian) | (intros; apply GlobalTheory.EtC.tateTwist_local_to_global_strictlyHenselian  <;> assumption)
end

