import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0016
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle0003
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0003
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TorsionLiftPairingInOrthogonalFrame
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.Bundle0001
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0019

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsSmallInPrimePow
section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne

theorem thue_normSq (d e : ℕ) (he : d + 1 = 4 * e) (u v : ℤ) :
    Complex.normSq ((u : ℂ) + (v : ℂ) * wK d) = ((u ^ 2 + u * v + e * v ^ 2 : ℤ) : ℝ) := by
  have hs : Real.sqrt d * Real.sqrt d = d := Real.mul_self_sqrt (Nat.cast_nonneg d)
  have he' : (d : ℝ) + 1 = 4 * e := by exact_mod_cast he
  have h1 : ((u : ℂ) + (v : ℂ) * wK d).re = u + v / 2 := by
    simp [wK]; ring
  have h2 : ((u : ℂ) + (v : ℂ) * wK d).im = v * Real.sqrt d / 2 := by
    simp [wK]; ring
  rw [Complex.normSq_apply, h1, h2]
  push_cast
  linear_combination ((v : ℝ) ^ 2 / 4) * hs + ((v : ℝ) ^ 2 / 4) * he'

theorem thue_norm_zc {q : ℕ} [Fact q.Prime] (a : ℤ_[q]) : ‖zc a‖ = ‖a‖ := by
  unfold zc
  rw [norm_algebraMap', PadicInt.padic_norm_e_of_padicInt]

theorem thue_pigeon {q : ℕ} [Fact q.Prime] (a : ℤ_[q]) (k : ℕ) :
    ∃ u v : ℤ, (u ≠ 0 ∨ v ≠ 0) ∧ u ^ 2 ≤ (q : ℤ) ^ k ∧ v ^ 2 ≤ (q : ℤ) ^ k ∧
      ‖(u : ℤ_[q]) + (v : ℤ_[q]) * a‖ ≤ (q : ℝ) ^ (-(k : ℤ)) := by
  have hq : q.Prime := Fact.out
  haveI : NeZero (q ^ k) := ⟨pow_ne_zero _ hq.ne_zero⟩
  set m := Nat.sqrt (q ^ k) with hm
  let f : Fin (m + 1) × Fin (m + 1) → ZMod (q ^ k) := fun p =>
    PadicInt.toZModPow k (((p.1 : ℕ) : ℤ_[q]) + ((p.2 : ℕ) : ℤ_[q]) * a)
  have hcard : Fintype.card (ZMod (q ^ k)) < Fintype.card (Fin (m + 1) × Fin (m + 1)) := by
    rw [ZMod.card, Fintype.card_prod, Fintype.card_fin]
    exact Nat.lt_succ_sqrt _
  obtain ⟨x, y, hxy, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  have hm2 : ((m : ℤ)) ^ 2 ≤ (q : ℤ) ^ k := by
    have := Nat.sqrt_le' (q ^ k)
    exact_mod_cast this
  have hb : ∀ i j : Fin (m + 1), (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) ^ 2 ≤ (q : ℤ) ^ k := by
    intro i j
    have hi := i.2
    have hj := j.2
    refine le_trans ?_ hm2
    apply sq_le_sq' <;> omega
  refine ⟨((x.1 : ℕ) : ℤ) - ((y.1 : ℕ) : ℤ), ((x.2 : ℕ) : ℤ) - ((y.2 : ℕ) : ℤ), ?_, hb _ _, hb _ _, ?_⟩
  · by_contra h
    push_neg at h
    apply hxy
    ext
    · have := h.1; omega
    · have := h.2; omega
  · rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker]
    have : PadicInt.toZModPow k ((((x.1 : ℕ) : ℤ_[q]) + ((x.2 : ℕ) : ℤ_[q]) * a) -
        (((y.1 : ℕ) : ℤ_[q]) + ((y.2 : ℕ) : ℤ_[q]) * a)) = 0 := by
      rw [map_sub, sub_eq_zero]; exact hf
    rw [← this]
    congr 1
    push_cast
    ring

theorem exists_small_in_prime_pow : ∀ (d q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]), d.Prime → d % 16 = 7 → Split d q → ∀ k : ℕ, ∃ (β : ℂ) (N : ℕ), InOK d β ∧ β ≠ 0 ∧ ‖ι β‖ ≤ (q : ℝ) ^ (-(k : ℤ)) ∧ (N : ℂ) = β * conj β ∧ N ≤ (d + 3) * q ^ k := by
  intro d q _ ι hd h16 hs k
  obtain ⟨⟨-, hw, -⟩, h2, -⟩ := GlobalTheory.T.imagQuadraticMaximalOrder_arithmetic_at_split_prime d q ι hd h16 hs
  obtain ⟨⟨a, ha⟩, -⟩ := h2 _ hw
  obtain ⟨u, v, huv, hu, hv, hn⟩ := thue_pigeon a k
  obtain ⟨e, he⟩ : ∃ e : ℕ, d + 1 = 4 * e := ⟨(d + 1) / 4, by omega⟩
  have he1 : (1 : ℤ) ≤ e := by omega
  have hed : (e : ℤ) ≤ d := by omega
  have hpos : 0 < u ^ 2 + u * v + e * v ^ 2 := by
    have h3 : v ^ 2 ≤ e * v ^ 2 := by nlinarith [sq_nonneg v]
    have h4 : 0 < u ^ 2 + v ^ 2 := by
      rcases huv with h | h
      · have := sq_pos_of_ne_zero h; nlinarith [sq_nonneg v]
      · have := sq_pos_of_ne_zero h; nlinarith [sq_nonneg u]
    nlinarith [sq_nonneg (u + v)]
  have hN := thue_normSq d e he u v
  obtain ⟨N, hNe⟩ := Int.eq_ofNat_of_zero_le hpos.le
  refine ⟨(u : ℂ) + (v : ℂ) * wK d, N, ⟨u, v, rfl⟩, ?_, ?_, ?_, ?_⟩
  · intro h
    rw [h, map_zero] at hN
    have : u ^ 2 + u * v + e * v ^ 2 = 0 := by exact_mod_cast hN.symm
    omega
  · have : ι ((u : ℂ) + (v : ℂ) * wK d) = zc ((u : ℤ_[q]) + (v : ℤ_[q]) * a) := by
      rw [map_add, map_mul, ha]
      simp [zc]
    rw [this, thue_norm_zc]
    exact hn
  · rw [Complex.mul_conj, hN, hNe]
    simp
  · have h5 : (e : ℤ) * v ^ 2 ≤ d * (q : ℤ) ^ k :=
      mul_le_mul hed hv (sq_nonneg v) (by positivity)
    have h6 : (N : ℤ) ≤ (d + 3) * (q : ℤ) ^ k := by
      rw [← hNe]
      nlinarith [sq_nonneg (u - v), sq_nonneg u, sq_nonneg v]
    exact_mod_cast h6

end GlobalTheory.MomOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HarmonicFixedCard
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.IndefiniteRowSideFullHecke.HarmonicEigenCriterion

section Exp

variable {k : Type} [CommRing k] [Algebra ℚ k] {d n : ℕ}

omit [Algebra ℚ k] in
theorem cc_ev {m : ℕ} {a : Fin m → Pt k n d} (ha : ∀ j i, constantCoeff (a j i) = 0)
    (f : PS k m d) : constantCoeff (ev a f) = constantCoeff f := by
  have hs : HasSubst (fun p : Fin m × Fin d => a p.1 p.2) :=
    hasSubst_of_constantCoeff_zero fun p => ha p.1 p.2
  have e : f = (f - C (constantCoeff f)) + C (constantCoeff f) := by ring
  have h0 : constantCoeff (ev a (f - C (constantCoeff f))) = 0 :=
    constantCoeff_subst_eq_zero hs (fun p => ha p.1 p.2) (by simp)
  have hadd : ∀ f g : PS k m d, ev a (f + g) = ev a f + ev a g := fun f g => subst_add hs f g
  conv_lhs => rw [e, hadd, map_add, h0]
  simp [ev]

theorem expS_sum {ι : Type} (s : Finset ι) (g : ι → PS k n d) (hg : ∀ i, constantCoeff (g i) = 0) :
    FB.expS k (∑ i ∈ s, g i) = ∏ i ∈ s, FB.expS k (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [BalancedFrameGauge.expS_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha,
      WickVanishing.gt_expS_add _ _ (hg a) (by simp [map_sum, hg]), ih]

theorem expS_smul_sum {ι : Type} [Fintype ι] (g : ι → PS k n d) (hg : ∀ i, constantCoeff (g i) = 0)
    (N : ℕ) : FB.expS k ((N : k) • ∑ i, g i) = ∏ i, FB.expS k (g i) ^ N := by
  have h : (N : k) • ∑ i, g i = ∑ _j : Fin N, ∑ i, g i := by
    rw [Nat.cast_smul_eq_nsmul]; simp
  rw [h, expS_sum _ _ (fun _ => by simp [map_sum, hg]), expS_sum _ _ hg, Finset.prod_pow]
  simp

end Exp

section Frames

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k]

theorem gauge_iff (B : FB R d O) (h : PS k 2 d) :
    BalancedFrameGauge.IsBalancedGauge k B h ↔ BiadditiveBalancedSeries.IsBiaddBalanced B k h :=
  ⟨fun H => ⟨H.ax0, H.ax1, H.ph1, H.ph2, H.ad⟩, fun H => ⟨H.ax0, H.ax1, H.add1, H.add2, H.bal⟩⟩

omit [Algebra ℚ k] in
theorem cc_of_ax {h : PS k 2 d} (h0 : ev (n := 1) ![0, pt k d 0] h = 0) : constantCoeff h = 0 := by
  have := cc_ev (a := (![0, pt k d 0] : Fin 2 → Pt k 1 d))
    (fun j i => by fin_cases j <;> simp [pt]) h
  rw [← this, h0, map_zero]

omit [Algebra ℚ k] in
theorem cc_col (B : FB R d O) {h : PS k 2 d} (h0 : ev (n := 1) ![0, pt k d 0] h = 0) (w0 : O) {n : ℕ}
    (b : Fin n) : constantCoeff (ev (n := n) ![pt k d b, comp1 (B.actK k w0) (pt k d b)] h) = 0 := by
  have hc : ∀ i, constantCoeff (comp1 (B.actK k w0) (pt k d b) i) = 0 := fun i => by
    have := cc_ev (a := (![pt k d b] : Fin 1 → Pt k n d))
      (fun j i => by fin_cases j; simp [pt]) (B.actK k w0 i)
    rw [comp1, this, FB.actK, constantCoeff_map, B.A.const, map_zero]
  have := cc_ev (a := (![pt k d b, comp1 (B.actK k w0) (pt k d b)] : Fin 2 → Pt k n d))
    (fun j i => by
      fin_cases j
      · simp [pt]
      · exact hc i) h
  rw [this, cc_of_ax k h0]

theorem val_eq (B : FB R d O) {h : PS k 2 d} (h0 : ev (n := 1) ![0, pt k d 0] h = 0) (w0 : O)
    (N : ℕ) {n : ℕ} (f : PS k n d) {ι : Type} [Fintype ι] (u : ι → Fin d → k)
    (P : MvPolynomial (ι × Fin n) k) :
    BalancedFrameGauge.valCols k B h w0 N f u P = BiadditiveBalancedSeries.frameVal B k h w0 N f u P := by
  unfold BalancedFrameGauge.valCols BiadditiveBalancedSeries.frameVal BalancedFrameGauge.quotCols BiadditiveBalancedSeries.colSum
  rw [expS_smul_sum _ (cc_col k B h0 w0)]
  rfl

end Frames

section Letters

variable {E : Type} [Field E] [NumberField E] {k : Type} [Field k]

theorem conj_eq [IsCMField E] (τ : E →+* k) : BalancedFrameGauge.conjType E τ = BiadditiveBalancedSeries.conjEmb τ := rfl

theorem harmonic_iff [IsCMField E] (r : (E →+* k) → ℕ) {n : ℕ}
    (P : MvPolynomial ((Σ τ : E →+* k, Fin (r τ)) × Fin n) k) :
    BalancedFrameGauge.IsHarmonic r P ↔ BiadditiveBalancedSeries.IsHarmonic r P := Iff.rfl

theorem eigen_eq [StarRing (𝓞 E)] {R : Type} [CommRing R] [Algebra R k] {d : ℕ} (B : FB R d (𝓞 E))
    (τ : E →+* k) : BalancedFrameGauge.lieEigen k B τ = BiadditiveBalancedSeries.lieEig B τ := rfl

theorem card_iff [CharZero k] :
    Fintype.card (E →+* k) = Module.finrank ℚ E ↔ Nat.card (E →+* k) = Module.finrank ℚ E := by
  rw [Nat.card_eq_fintype_card]

end Letters

section Bases

variable {k V ι : Type} [Field k] [AddCommGroup V] [Module k V]

theorem indep_span_iff (W : Submodule k V) (v : ι → V) :
    (LinearIndependent k v ∧ Submodule.span k (Set.range v) = W) ↔
      ∃ b : Module.Basis ι k W, ∀ i, (b i : V) = v i := by
  constructor
  · rintro ⟨hv, rfl⟩
    exact ⟨Module.Basis.span hv, fun i => by simp⟩
  · rintro ⟨b, hb⟩
    have e : v = W.subtype ∘ b := funext fun i => (hb i).symm
    subst e
    refine ⟨b.linearIndependent.map' _ (Submodule.ker_subtype W), ?_⟩
    rw [Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]

end Bases

theorem fixed_iff (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)]
    (k : Type) [Field k] [CharZero k] (R : Type) [CommRing R] [Algebra R k] (d : ℕ) (B : FB R d (𝓞 E))
    (w0 : 𝓞 E) (r : (E →+* k) → ℕ) :
    (∀ (u : (Σ τ : E →+* k, Fin (r τ)) → Fin d → k),
      (∀ τ : E →+* k, LinearIndependent k (fun i : Fin (r τ) => u ⟨τ, i⟩) ∧
        Submodule.span k (Set.range fun i : Fin (r τ) => u ⟨τ, i⟩) = BalancedFrameGauge.lieEigen k B τ) →
      ∀ (n N : ℕ) (P : MvPolynomial ((Σ τ : E →+* k, Fin (r τ)) × Fin n) k), BalancedFrameGauge.IsHarmonic r P →
      ∀ (h h' : PS k 2 d), B.IsCanonGauge k h → BalancedFrameGauge.IsBalancedGauge k B h' →
      ∀ f : PS k n d, BalancedFrameGauge.valCols k B h w0 N f u P = BalancedFrameGauge.valCols k B h' w0 N f u P) ↔
    (∀ (u : ∀ τ : E →+* k, Module.Basis (Fin (r τ)) k (BiadditiveBalancedSeries.lieEig B τ))
      (n N : ℕ) (P : MvPolynomial ((Σ τ : E →+* k, Fin (r τ)) × Fin n) k),
      BiadditiveBalancedSeries.IsHarmonic r P →
      ∀ (f : PS k n d) (hc g : PS k 2 d), B.IsCanonGauge k hc → BiadditiveBalancedSeries.IsBiaddBalanced B k g →
        BiadditiveBalancedSeries.frameVal B k g w0 N f (fun l : Σ τ : E →+* k, Fin (r τ) => (u l.1 l.2 : Fin d → k)) P =
          BiadditiveBalancedSeries.frameVal B k hc w0 N f
            (fun l : Σ τ : E →+* k, Fin (r τ) => (u l.1 l.2 : Fin d → k)) P) := by
  constructor
  · intro H u n N P hP f hc g hhc hg
    rw [← val_eq k B hg.ax0, ← val_eq k B hhc.ax0]
    refine (H _ (fun τ => ?_) n N P ((harmonic_iff r P).2 hP) hc g hhc ((gauge_iff k B g).2 hg) f).symm
    rw [eigen_eq]
    exact (indep_span_iff _ _).2 ⟨u τ, fun _ => rfl⟩
  · intro H u hu n N P hP h h' hh hh' f
    choose b hb using fun τ : E →+* k =>
      (indep_span_iff (BiadditiveBalancedSeries.lieEig B τ) (fun i : Fin (r τ) => u ⟨τ, i⟩)).1 (hu τ)
    have e : u = fun l : Σ τ : E →+* k, Fin (r τ) => (b l.1 l.2 : Fin d → k) :=
      funext fun l => (hb l.1 l.2).symm
    rw [val_eq k B hh.ax0, val_eq k B hh'.ax0, e]
    exact (H b n N P ((harmonic_iff r P).1 hP) f h h' hh ((gauge_iff k B h').1 hh')).symm

theorem balancedFrameValue_iff : BalancedFrameGauge.BalancedFrameValue ↔ BiadditiveBalancedSeries.BiaddBalancedValue := by
  constructor
  · intro H E _ _ _ _ hs k _ _ hk R _ _ d B w0 hw r
    exact (fixed_iff E k R d B w0 r).1 (H E hs k (card_iff.2 hk) R d B w0 hw r)
  · intro H E _ _ _ _ hs k _ _ hk R _ _ d B w0 hw r
    exact (fixed_iff E k R d B w0 r).2 (H E hs k (card_iff.1 hk) R d B w0 hw r)

end GlobalTheory.IndefiniteRowSideFullHecke.HarmonicEigenCriterion
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HasSubstAddSqZero
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.Jets

theorem hasSubst_add_sqZero {σ τ S : Type} [Fintype σ] [CommRing S]
    (a b : σ → MvPowerSeries τ S) (e : MvPowerSeries τ S) (he : e * e = 0)
    (ha : ∀ s, IsNilpotent (constantCoeff (a s))) : HasSubst (fun s => a s + e * b s) := by
  apply hasSubst_of_constantCoeff_nilpotent
  intro s
  rw [map_add, map_mul]
  have h1 : IsNilpotent (constantCoeff e) := ⟨2, by rw [pow_two, ← map_mul, he, map_zero]⟩
  exact (Commute.all _ _).isNilpotent_add (ha s) ((Commute.all _ _).isNilpotent_mul_right h1)

open scoped MvPowerSeries.WithPiTopology in

theorem subst_add_sqZero {σ τ S : Type} [Fintype σ] [CommRing S]
    (a b : σ → MvPowerSeries τ S) (e : MvPowerSeries τ S) (he : e * e = 0)
    (ha0 : ∀ s, IsNilpotent (constantCoeff (a s))) (g : MvPowerSeries σ S) :
    subst (fun s => a s + e * b s) g = subst a g + e * ∑ s, b s * subst a (pderiv S s g) := by
  classical
  letI : UniformSpace S := ⊥
  haveI : DiscreteUniformity S := ⟨rfl⟩
  have ha : HasSubst a := hasSubst_of_constantCoeff_nilpotent ha0
  have hb : HasSubst (fun s => a s + e * b s) := hasSubst_add_sqZero a b e he ha0
  have hca : Continuous (subst a : MvPowerSeries σ S → MvPowerSeries τ S) := continuous_subst ha
  have hcb : Continuous (subst (fun s => a s + e * b s) :
      MvPowerSeries σ S → MvPowerSeries τ S) := continuous_subst hb
  have hs0 : subst a (0 : MvPowerSeries σ S) = 0 := by rw [← coe_substAlgHom ha, map_zero]
  have hs1 : subst a (1 : MvPowerSeries σ S) = 1 := by rw [← coe_substAlgHom ha, map_one]
  let D2 : MvPowerSeries σ S → MvPowerSeries τ S := fun g =>
    subst a g + e * ∑ s, b s * subst a (pderiv S s g)
  have c2 : Continuous D2 :=
    hca.add (continuous_const.mul (continuous_finsetSum _ fun i _ =>
      continuous_const.mul (hca.comp (continuous_pderiv_disc _))))
  have hpoly : ∀ p : MvPolynomial σ S,
      subst (fun s => a s + e * b s) (p : MvPowerSeries σ S) = D2 (p : MvPowerSeries σ S) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C r => simp [D2, subst_C, hs0]
    | add p q hp hq =>
      simp only [D2, MvPolynomial.coe_add, subst_add ha, subst_add hb, map_add] at hp hq ⊢
      rw [hp, hq]
      simp only [mul_add, Finset.sum_add_distrib]
      ring
    | mul_X p s hp =>
      simp only [D2, MvPolynomial.coe_mul, MvPolynomial.coe_X] at hp ⊢
      rw [subst_mul ha, subst_X ha, subst_mul hb, subst_X hb, hp]
      have hX : ∀ i : σ, pderiv S i (X s : MvPowerSeries σ S) = if i = s then 1 else 0 := by
        intro i
        by_cases h : i = s
        · subst h; simp
        · rw [if_neg h, pderiv_X_of_ne]
          intro h'
          exact h h'.symm
      have hterm : ∀ i : σ, b i * subst a (pderiv S i ((p : MvPowerSeries σ S) * X s)) =
          (if i = s then b i * subst a (p : MvPowerSeries σ S) else 0) +
            a s * (b i * subst a (pderiv S i (p : MvPowerSeries σ S))) := by
        intro i
        rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, hX i, subst_add ha, subst_mul ha,
          subst_mul ha, subst_X ha]
        split_ifs with h
        · rw [hs1]; ring
        · rw [hs0]; ring
      rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib, Finset.sum_ite_eq',
        if_pos (Finset.mem_univ _), ← Finset.mul_sum]
      linear_combination (b s * ∑ i, b i * subst a (pderiv S i (p : MvPowerSeries σ S))) * he
  have := (MvPowerSeries.WithPiTopology.denseRange_toMvPowerSeries).equalizer hcb c2 (funext hpoly)
  exact congrFun this g

theorem map_pderiv' {σ R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (i : σ)
    (f : MvPowerSeries σ R) :
    MvPowerSeries.map φ (pderiv R i f) = pderiv S i (MvPowerSeries.map φ f) := by
  classical
  ext n
  simp [coeff_pderiv]

theorem hasSubst_pt_zero (R : Type) [CommRing R] (d : ℕ) :
    ∀ p : Fin 2 × Fin d,
      constantCoeff ((![pt R d 0, 0] : Fin 2 → Pt R 1 d) p.1 p.2) = 0 := by
  rintro ⟨j, i⟩
  fin_cases j <;> simp [pt]

theorem law_right_unit {R : Type} [CommRing R] {d : ℕ} (G : FGLaw R d) (i : Fin d) :
    ev (n := 1) ![pt R d 0, 0] (G.F i) = (X ((0 : Fin 1), i) : PS R 1 d) := by
  have hb : HasSubst (fun p : Fin 2 × Fin d => (![pt R d 0, 0] : Fin 2 → Pt R 1 d) p.1 p.2) :=
    hasSubst_of_constantCoeff_zero (hasSubst_pt_zero R d)
  have ha : HasSubst
      (fun p : Fin 2 × Fin d => (![pt R d 1, pt R d 0] : Fin 2 → Pt R 2 d) p.1 p.2) :=
    hasSubst_of_constantCoeff_zero (by
      rintro ⟨j, i⟩
      fin_cases j <;> simp [pt])
  rw [← G.comm i, ← G.unit i]
  unfold ev
  rw [subst_comp_subst_apply ha hb]
  congr 1
  funext p
  obtain ⟨j, l⟩ := p
  fin_cases j
  · exact subst_X hb ((1 : Fin 2), l)
  · exact subst_X hb ((0 : Fin 2), l)

theorem map_ev_pt_zero {R S : Type} [CommRing R] [CommRing S] {d : ℕ} (φ : R →+* S)
    (g : PS R 2 d) :
    MvPowerSeries.map φ (ev (n := 1) ![pt R d 0, 0] g) =
      ev (n := 1) ![pt S d 0, 0] (MvPowerSeries.map φ g) := by
  unfold ev
  rw [MvPowerSeries.map_subst (hasSubst_of_constantCoeff_zero (hasSubst_pt_zero R d))]
  congr 1
  funext p
  obtain ⟨j, l⟩ := p
  fin_cases j <;> simp [pt]

theorem C_eps_mul_self (R : Type) [CommRing R] (τ : Type) :
    (C (DualNumber.eps : DualNumber R) : MvPowerSeries τ (DualNumber R)) * C DualNumber.eps = 0 := by
  rw [← map_mul, DualNumber.eps_mul_eps, map_zero]

theorem addOf_eps {R : Type} [CommRing R] {d : ℕ} (G : FGLaw R d) (v : Fin d → R) (j : Fin d) :
    addOf (n := 1) (G.mapF (algebraMap R (DualNumber R))) (pt (DualNumber R) d 0)
        (fun i => C (TrivSqZeroExt.inr (v i) : DualNumber R)) j =
      X ((0 : Fin 1), j) + C (DualNumber.eps : DualNumber R) *
        MvPowerSeries.map (algebraMap R (DualNumber R))
          (∑ i : Fin d, C (v i) *
            ev (n := 1) ![pt R d 0, 0] (pderiv R ((1 : Fin 2), i) (G.F j))) := by
  have h := subst_add_sqZero
    (fun p : Fin 2 × Fin d => (![pt (DualNumber R) d 0, 0] : Fin 2 → Pt (DualNumber R) 1 d) p.1 p.2)
    (fun p : Fin 2 × Fin d => (![0, fun i => C (algebraMap R (DualNumber R) (v i))] :
      Fin 2 → Pt (DualNumber R) 1 d) p.1 p.2)
    (C DualNumber.eps) (C_eps_mul_self R _)
    (fun p => by rw [hasSubst_pt_zero]; exact IsNilpotent.zero)
    (MvPowerSeries.map (algebraMap R (DualNumber R)) (G.F j))
  have h1 := map_ev_pt_zero (algebraMap R (DualNumber R)) (G.F j)
  rw [law_right_unit, map_X] at h1
  rw [h1, map_sum]
  simp only [map_mul, map_C, map_ev_pt_zero, map_pderiv']
  rw [Fintype.sum_prod_type, Fin.sum_univ_two] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply, zero_mul,
    Finset.sum_const_zero, zero_add] at h
  refine Eq.trans ?_ h
  unfold addOf ev FGLaw.mapF
  congr 1
  funext p
  obtain ⟨l, i⟩ := p
  fin_cases l
  · simp
  · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero, Pi.zero_apply,
      zero_add]
    rw [← map_mul]
    congr 1
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem ev_addOf_eps :
    ∀ (R : Type) [CommRing R] (d : ℕ) (G : FGLaw R d) (v : Fin d → R) (f : PS R 1 d),
      ev (n := 1) ![addOf (G.mapF (algebraMap R (DualNumber R))) (pt (DualNumber R) d 0)
          (fun i => C (TrivSqZeroExt.inr (v i) : DualNumber R))]
        (MvPowerSeries.map (algebraMap R (DualNumber R)) f) =
      MvPowerSeries.map (algebraMap R (DualNumber R)) f +
        C (DualNumber.eps : DualNumber R) *
          MvPowerSeries.map (algebraMap R (DualNumber R)) (Dof G.F v f) := by
  intro R _ d G v f
  have h := subst_add_sqZero
    (X : Fin 1 × Fin d → PS (DualNumber R) 1 d)
    (fun p : Fin 1 × Fin d => MvPowerSeries.map (algebraMap R (DualNumber R))
          (∑ i : Fin d, C (v i) *
            ev (n := 1) ![pt R d 0, 0] (pderiv R ((1 : Fin 2), i) (G.F p.2))))
    (C DualNumber.eps) (C_eps_mul_self R _)
    (fun p => by rw [constantCoeff_X]; exact IsNilpotent.zero)
    (MvPowerSeries.map (algebraMap R (DualNumber R)) f)
  rw [subst_self, Fintype.sum_prod_type, Fin.sum_univ_one] at h
  unfold Dof
  rw [map_sum]
  simp only [map_mul (MvPowerSeries.map (algebraMap R (DualNumber R)))
    (∑ i : Fin d, _) (pderiv R _ f), map_pderiv' (algebraMap R (DualNumber R)) _ f]
  refine Eq.trans ?_ h
  unfold ev
  congr 1
  funext p
  obtain ⟨l, j⟩ := p
  obtain rfl : l = 0 := Subsingleton.elim _ _
  exact addOf_eps G v j

end GlobalTheory.Jets
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TorsionLiftPairingInOrthogonalFrameStatement
section
open GlobalTheory.MomOne Formalism.L2.Ker.JMB
open scoped ComplexConjugate BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_lift_pairing_in_orthogonal_frame : ∀ (q : ℕ) [Fact q.Prime] (lam : Qbar →+* ℂ_[q]) (ι : ℂ ≃+* ℂ_[q]) (g : ℕ) (S : Setup g) (x : Fin g → Fin g → ℂ) (a : Fin g → ℕ) (r : ℕ) (b : Fin r → Fin g → ℂ) (n m s s₀ : ℕ) (eps : ℂ) (y : Fin r → Fin (q ^ n)), (∀ z : Qbar, ι (z : ℂ) = lam z) → S.Ok → Split S.d q → (∀ i, x i ∈ S.La) → (∀ i j, beta S.d S.Hm (x i) (x j) = if i = j then (a i : ℂ) else 0) → (∀ i, 0 < a i ∧ Nat.Coprime (a i) q) → (∀ i, b i ∈ S.La) → IsIdem lam S.d m eps → 2 * n ≤ m → (s₀ * ∏ i, a i) ∣ s → let y' : Fin g → ℂ := fun i => beta S.d S.Hm ((s : ℂ) • liftY q n eps b y) (x i) / (a i : ℂ); (∀ i, Good ι S.d n s₀ (y' i)) ∧ ∀ (A : Fin r → ℤ_[q]) (A' : Fin g → ℤ_[q]), (∀ i, GlobalTheory.MomOne.zc (A' i) = ∑ j, GlobalTheory.MomOne.zc (A j) * ι (beta S.d S.Hm (x i) (b j))) → kap S.Hm (vecA n b A) ((s : ℂ) • liftY q n eps b y) ∈ Qbar ∧ ι (kap S.Hm (vecA n b A) ((s : ℂ) • liftY q n eps b y)) = ∏ i, ι (kap1 S.d 1 (y' i)) ^ (PadicInt.toZModPow n (A' i)).val := by
  first | exact @GlobalTheory.MomOne.kapFrame | exact GlobalTheory.MomOne.kapFrame | (intros; apply GlobalTheory.MomOne.kapFrame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TwistedMeasureMomentsEqShiftedSeriesJetsStatement
section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_measure_moments_eq_shifted_series_jets : ∀ (q : ℕ) [Fact q.Prime] (S : ℂ_[q]⟦X⟧) (ζ : ℂ_[q]) (n k : ℕ), Bdd S → ζ ^ (q ^ n) = 1 → ∃ f : C(ℤ_[q], ℂ_[q]), (∀ a, f a = ζ ^ (PadicInt.toZModPow n a).val * zc a ^ k) ∧ HasSum (fun m : ℕ => coeff m S * (fwdDiff (1 : ℤ_[q]))^[m] f 0) (constantCoeff (DT^[k] (shiftS ζ S))) := by
  first | exact @GlobalTheory.MomOne.TwistMom.twisted_moments | exact GlobalTheory.MomOne.TwistMom.twisted_moments | (intros; apply GlobalTheory.MomOne.TwistMom.twisted_moments <;> assumption)
end

