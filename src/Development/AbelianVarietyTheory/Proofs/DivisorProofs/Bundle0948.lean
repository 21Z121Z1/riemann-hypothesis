import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartDirectionsAreEigenvectors
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0074
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.BiextCoeffSecondLinear
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PtCoeffSingleSubst
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0923
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0125
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0070
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MulMemIntA
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LimitActionLieAlgebraOfPrimeIdempotentApprox
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv.LimAct

open NumberField MvPowerSeries
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.LawLog GlobalTheory.IsoTriv
open ReciprocityTheory.ChartRestriction.G.TB (dAct)
open ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA (dActH)

theorem exists_lim {O : Type} [CommRing O] (q : O) [IsAdicComplete (Ideal.span {q}) O] (g : ℕ → O)
    (hg : ∀ m n, m ≤ n → ∃ w, g n - g m = q ^ m * w) : ∃ L : O, ∀ n, ∃ w, L - g n = q ^ n * w := by
  have key : ∀ m n, m ≤ n → g m ≡ g n [SMOD (Ideal.span {q} ^ m • ⊤ : Submodule O O)] := by
    intro m n hmn
    obtain ⟨w, hw⟩ := hg m n hmn
    rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
    exact ⟨-w, by rw [← neg_sub, hw]; ring⟩
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {q}) g (fun {m n} h => key m n h)
  refine ⟨L, fun n => ?_⟩
  have h := hL n
  rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h
  obtain ⟨a, ha⟩ := h
  exact ⟨-a, by rw [← neg_sub, ← ha]; ring⟩

section Val

variable {T : CDVR} {p : ℕ} [Fact p.Prime] (X : ValExt T p)

theorem isIntV_alg (o : X.O) : IsIntV (vX_vp X) (algebraMap X.O X.C o) := by
  rw [GlobalTheory.FactorDepth.isIntV_iff]; exact X.ints.map_le_one o

theorem le_v_pow_mul (N : ℕ) (o : X.O) :
    ((N : ℝ) : WithTop ℝ) ≤ vX_vp X ((p : X.C) ^ N * algebraMap X.O X.C o) := by
  rw [AddValuation.map_mul, AddValuation.map_pow, vX_vp_p, nsmul_one]
  have h := isIntV_alg X o
  unfold IsIntV at h
  calc ((N : ℝ) : WithTop ℝ) = (N : WithTop ℝ) := by norm_cast
    _ ≤ (N : WithTop ℝ) + vX_vp X (algebraMap X.O X.C o) := le_add_of_nonneg_right h

theorem eq_zero_of_le_v (x : X.C) (h : ∀ N : ℕ, ((N : ℝ) : WithTop ℝ) ≤ vX_vp X x) : x = 0 := by
  by_contra hx
  obtain ⟨N, hN⟩ := exists_nat_gt ((Real.log (X.v (p : X.C) : ℝ))⁻¹ * Real.log (X.v x : ℝ))
  have := h N
  rw [vX_vp_apply X hx, WithTop.coe_le_coe] at this
  linarith

end Val

section Chart

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [inst : StarRing (𝓞 E)] {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}
  (Ch : IntegralChartA3 Xo c T io y) {p : ℕ} [Fact p.Prime] (X : ValExt T p)

def dActXH : 𝓞 E →+* Matrix (Fin (chD Ch.ch)) (Fin (chD Ch.ch)) X.C :=
  letI := io.toAlgebra
  letI : Algebra T.Fr X.C := X.ιF.toAlgebra
  dActH X.C Ch.ch.B

theorem dActX_eq (a : 𝓞 E) : dActX Ch X a = dActXH Ch X a := rfl

def entO (a : 𝓞 E) (e e' : Fin (chD Ch.ch)) : X.O :=
  X.ι (coeff (Finsupp.single ((0 : Fin 1), e') 1) (Ch.actT a e))

theorem alg_entO (a : 𝓞 E) (e e' : Fin (chD Ch.ch)) :
    algebraMap X.O X.C (entO Ch X a e e') = dActX Ch X a e e' := by
  letI := io.toAlgebra
  letI : Algebra T.Fr X.C := X.ιF.toAlgebra
  rw [entO, ← X.comp]
  show _ = coeff _ (Ch.ch.B.actK X.C a e)
  unfold FB.actK
  rw [Ch.gen.1.2.1 a e, coeff_map, coeff_map]
  rfl

theorem dActX_apply (a : 𝓞 E) (e e' : Fin (chD Ch.ch)) :
    dActX Ch X a e e' = X.ιF (letI := io.toAlgebra; dAct T.Fr Ch.ch.B a e e') := by
  letI := io.toAlgebra
  letI : Algebra T.Fr X.C := X.ιF.toAlgebra
  show coeff _ (Ch.ch.B.actK X.C a e) = X.ιF (coeff _ (Ch.ch.B.actK T.Fr a e))
  unfold FB.actK
  rw [coeff_map, coeff_map]
  rfl

theorem dActX_mulVec_lieVec (hst : ∀ a : 𝓞 E, star a = H.bar a) (φ : 𝓞 E →+* T.V) (τ : E →+* ℂ)
    (hφ : ∀ a : 𝓞 E, algebraMap T.V T.Fr (φ a) = io (embK c τ a)) (a : 𝓞 E) (i : Fin (Dw.mult τ)) :
    (dActX Ch X a).mulVec (lieVec Ch X ⟨τ, i⟩) = jX X (φ a) • lieVec Ch X ⟨τ, i⟩ := by
  obtain rfl := GlobalTheory.PowGerm.starSt E H inst hst
  letI := H.starRing
  letI := io.toAlgebra
  have h := GlobalTheory.PowGerm.eigDirSt E H Dw l Xo c T io y Ch a ⟨τ, i⟩
  funext e
  have h3 := congrArg X.ιF (congrFun h e)
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, map_sum, map_mul] at h3 ⊢
  simp only [dActX_apply, lieVec, jX, RingHom.comp_apply, hφ, ← Ch.gen.1.2.2.2.2.2.2]
  exact h3

end Chart

theorem cauchy_eps_mul {R V : Type} [CommRing R] [CommRing V] (φ : R →+* V) (q : R) (ε x : ℕ → R) (t : V)
    (hε : ∀ N : ℕ, (∃ z, φ (ε N) = 1 + φ q ^ N * z) ∧
      ∀ M ≤ N, ∀ a : R, (∃ z, φ a = φ q ^ M * z) → ε N * a ∈ Ideal.span {q ^ M})
    (hx : ∀ N : ℕ, ∃ z, φ (x N) = t + φ q ^ N * z) (m n : ℕ) (hmn : m ≤ n) :
    ∃ w, ε n * x n - ε m * x m = q ^ m * w := by
  have hstep : ∀ N, ε (N + 1) * x (N + 1) - ε N * x N ∈ Ideal.span {q ^ N} := by
    intro N
    obtain ⟨z0, hz0⟩ := hx N
    obtain ⟨z1, hz1⟩ := hx (N + 1)
    obtain ⟨u0, hu0⟩ := (hε N).1
    obtain ⟨u1, hu1⟩ := (hε (N + 1)).1
    have ha : ε N * (x (N + 1) - x N) ∈ Ideal.span {q ^ N} :=
      (hε N).2 N le_rfl _ ⟨φ q * z1 - z0, by rw [map_sub, hz0, hz1]; ring⟩
    have hb : ε (N + 1) * (1 - ε N) ∈ Ideal.span {q ^ N} :=
      (hε (N + 1)).2 N (Nat.le_succ N) _ ⟨-u0, by rw [map_sub, map_one, hu0]; ring⟩
    have hc : ε N * (1 - ε (N + 1)) ∈ Ideal.span {q ^ N} :=
      (hε N).2 N le_rfl _ ⟨-(φ q * u1), by rw [map_sub, map_one, hu1]; ring⟩
    have e : ε (N + 1) * x (N + 1) - ε N * x N =
        ε N * (x (N + 1) - x N) + (ε (N + 1) * (1 - ε N) - ε N * (1 - ε (N + 1))) * x (N + 1) := by ring
    rw [e]
    exact Ideal.add_mem _ ha (Ideal.mul_mem_right _ _ (Ideal.sub_mem _ hb hc))
  induction n, hmn using Nat.le_induction with
  | base => exact ⟨0, by ring⟩
  | succ n hmn ih =>
    obtain ⟨w, hw⟩ := ih
    obtain ⟨w', hw'⟩ := Ideal.mem_span_singleton'.1 (hstep n)
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    exact ⟨w + q ^ k * w', by linear_combination hw - hw'⟩

end GlobalTheory.IsoTriv.LimAct

namespace GlobalTheory.IsoTriv

open NumberField MvPowerSeries
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.LawLog GlobalTheory.IsoTriv.LimAct

theorem limActSt_of_epsSt (hε : EpsSt) : LimActSt := by
  intro E _ _ _ H Dw l Xo c inst hst T io y Ch p _ X τ
  obtain ⟨φ, hφ⟩ := GlobalTheory.IsoCols.exists_lift T (io.comp (embK c τ))
  have hP : φ (p : 𝓞 E) = (p : T.V) := map_natCast φ p
  have hp0 : φ (p : 𝓞 E) ≠ 0 := by rw [hP]; exact Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hpu : ¬ IsUnit (φ (p : 𝓞 E)) := by rw [hP]; exact not_isUnit_p X
  obtain ⟨ε, hεN⟩ := hε (𝓞 E) T.V φ (p : 𝓞 E) hp0 hpu
  refine ⟨ε, fun t x hx => ?_⟩
  have hxN : ∀ N : ℕ, ∃ z, φ (x N) = t + φ (p : 𝓞 E) ^ N * z := fun N => by
    obtain ⟨z, hz⟩ := hx N
    exact ⟨z, by rw [hP]; exact IsFractionRing.injective T.V T.Fr ((hφ (x N)).trans hz)⟩
  have hcau := cauchy_eps_mul φ (p : 𝓞 E) ε x t hεN hxN
  have hent : ∀ e e', ∃ L : X.O, ∀ N, ∃ w, L - entO Ch X (ε N * x N) e e' = (p : X.O) ^ N * w := by
    intro e e'
    refine exists_lim (p : X.O) (fun N => entO Ch X (ε N * x N) e e') fun m n hmn => ?_
    obtain ⟨w, hw⟩ := hcau m n hmn
    refine ⟨entO Ch X w e e', X.ints.hom_inj ?_⟩
    rw [map_sub, map_mul, map_pow, map_natCast, alg_entO, alg_entO, alg_entO, dActX_eq, dActX_eq, dActX_eq,
      ← Matrix.sub_apply, ← map_sub, hw, ← Nat.cast_pow, ← nsmul_eq_mul, map_nsmul, Matrix.smul_apply, nsmul_eq_mul,
      Nat.cast_pow]
  choose L W hW using hent
  have hA : ∀ N e e', algebraMap X.O X.C (L e e') =
      dActX Ch X (ε N * x N) e e' + (p : X.C) ^ N * algebraMap X.O X.C (W e e' N) := by
    intro N e e'
    have h := congrArg (algebraMap X.O X.C) (hW e e' N)
    rw [map_sub, map_mul, map_pow, map_natCast, alg_entO] at h
    linear_combination h
  refine ⟨Matrix.of fun e e' => algebraMap X.O X.C (L e e'), fun N e e' => ?_, fun i => ?_⟩
  · rw [Matrix.of_apply, hA N, add_sub_cancel_left]
    exact le_v_pow_mul X N _
  · funext e
    rw [← sub_eq_zero]
    refine eq_zero_of_le_v X _ fun N => ?_
    obtain ⟨z0, hz0⟩ := hxN N
    obtain ⟨u, hu⟩ := (hεN N).1
    obtain ⟨z, hz⟩ : ∃ z, φ (ε N * x N) = t + (p : T.V) ^ N * z :=
      ⟨z0 + u * t + (p : T.V) ^ N * u * z0, by rw [map_mul, hu, hz0, hP]; ring⟩
    have hj : ∀ r : T.V, jX X r = algebraMap X.O X.C (X.ι r) := fun r => X.comp r
    have he := congrFun (dActX_mulVec_lieVec Ch X hst φ τ (fun a => hφ a) (ε N * x N) i) e
    rw [hz, map_add, map_mul, map_pow, map_natCast] at he
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Matrix.of_apply] at he ⊢
    have key : ∑ e', algebraMap X.O X.C (L e e') * lieVec Ch X ⟨τ, i⟩ e' - jX X t * lieVec Ch X ⟨τ, i⟩ e =
        (p : X.C) ^ N * algebraMap X.O X.C
          (∑ e', W e e' N * X.ι (Ch.uvecT ⟨τ, i⟩ e') + X.ι z * X.ι (Ch.uvecT ⟨τ, i⟩ e)) := by
      simp only [hA N, add_mul, Finset.sum_add_distrib, he, map_add, map_sum, map_mul, ← hj, mul_add, Finset.mul_sum,
        mul_assoc]
      simp only [lieVec]
      ring
    rw [key]
    exact le_v_pow_mul X N _

end GlobalTheory.IsoTriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LimitEntriesMatrixInverseClosedProof
section
open GlobalTheory.IsoTriv

namespace GlobalTheory.LimInv

variable {R V : Type} [CommRing R] [CommRing V]

def limSub (φ : R →+* V) (q : R) : Subring V where
  carrier := {t | ∀ N : ℕ, ∃ a z, φ a = t + φ q ^ N * z}
  mul_mem' := by
    intro s t hs ht N
    obtain ⟨a, z, ha⟩ := hs N
    obtain ⟨b, w, hb⟩ := ht N
    refine ⟨a * b, z * t + s * w + φ q ^ N * z * w, ?_⟩
    rw [map_mul, ha, hb]; ring
  one_mem' := fun N => ⟨1, 0, by simp⟩
  add_mem' := by
    intro s t hs ht N
    obtain ⟨a, z, ha⟩ := hs N
    obtain ⟨b, w, hb⟩ := ht N
    exact ⟨a + b, z + w, by rw [map_add, ha, hb]; ring⟩
  zero_mem' := fun N => ⟨0, 0, by simp⟩
  neg_mem' := by
    intro s hs N
    obtain ⟨a, z, ha⟩ := hs N
    exact ⟨-a, -z, by rw [map_neg, ha]; ring⟩

theorem inv_mem_limSub [IsDedekindDomain R] [IsDomain V] [IsDiscreteValuationRing V]
    (φ : R →+* V) (q : R) (hq0 : φ q ≠ 0) (hqu : ¬ IsUnit (φ q)) (u : Vˣ)
    (hu : (u : V) ∈ limSub φ q) : ((u⁻¹ : Vˣ) : V) ∈ limSub φ q := by
  intro N
  obtain ⟨a, z, ha⟩ := hu (N + 1)
  have hqm : φ q ∈ IsLocalRing.maximalIdeal V := (IsLocalRing.mem_maximalIdeal _).2 hqu
  have haU : IsUnit (φ a) := by
    by_contra h
    have h1 : φ a ∈ IsLocalRing.maximalIdeal V := (IsLocalRing.mem_maximalIdeal _).2 h
    have h2 : φ q ^ (N + 1) * z ∈ IsLocalRing.maximalIdeal V :=
      Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hqm _ (Nat.succ_pos N))
    have h3 : (u : V) ∈ IsLocalRing.maximalIdeal V := by
      have : (u : V) = φ a - φ q ^ (N + 1) * z := by rw [ha]; ring
      rw [this]; exact Ideal.sub_mem _ h1 h2
    exact ((IsLocalRing.mem_maximalIdeal _).1 h3) u.isUnit
  set w : Ideal R := (IsLocalRing.maximalIdeal V).comap φ with hw
  have hwp : w.IsPrime := Ideal.comap_isPrime φ _
  have hqw : q ∈ w := hqm
  have hwne : w ≠ ⊥ := by
    intro h
    have : q = 0 := by rw [h] at hqw; exact (Submodule.mem_bot R).1 hqw
    exact hq0 (by rw [this, map_zero])
  have hwm : w.IsMaximal := hwp.isMaximal hwne
  have haw : a ∉ w := fun h => ((IsLocalRing.mem_maximalIdeal _).1 h) haU
  obtain ⟨y, i, hiw, hyi⟩ := hwm.exists_inv haw
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨n, e, he⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (pow_ne_zero N hq0) hϖ
  have hiV : φ i ∈ Ideal.span {ϖ} := by rw [← hϖ.maximalIdeal_eq]; exact hiw
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hiV
  let b : R := y * ∑ j ∈ Finset.range n, i ^ j
  have hab : φ a * φ b = 1 - φ q ^ N * ((e⁻¹ : Vˣ) * c ^ n) := by
    have h1 : a * b = 1 - i ^ n := by
      have : a * y = 1 - i := by linear_combination hyi
      calc a * b = (a * y) * ∑ j ∈ Finset.range n, i ^ j := by ring
        _ = 1 - i ^ n := by rw [this, mul_neg_geom_sum]
    have h2 : φ a * φ b = 1 - φ i ^ n := by rw [← map_mul, h1, map_sub, map_one, map_pow]
    rw [h2, he, ← hc, mul_pow]
    have : ((e : V) * (e⁻¹ : Vˣ)) = 1 := Units.mul_inv e
    linear_combination (c ^ n * ϖ ^ n) * this
  refine ⟨b, -((u⁻¹ : Vˣ) : V) * ((e⁻¹ : Vˣ) * c ^ n) - ((u⁻¹ : Vˣ) : V) * φ q * z * φ b, ?_⟩
  have hu1 : (u : V) * ((u⁻¹ : Vˣ) : V) = 1 := Units.mul_inv u
  linear_combination ((u⁻¹ : Vˣ) : V) * hab - (((u⁻¹ : Vˣ) : V) * φ b) * ha - φ b * hu1

end GlobalTheory.LimInv

open GlobalTheory.LimInv in
theorem GlobalTheory.IsoTriv.limitEntriesMatrixInverseClosed_proof : InvSt := by
  intro R V _ _ _ _ _ φ q hq0 hqu n M hdet hM
  classical
  let S := limSub φ q
  let M₀ : Matrix (Fin n) (Fin n) S := fun b b' => ⟨M b b', fun N => hM b b' N⟩
  have hMM : S.subtype.mapMatrix M₀ = M := by ext b b'; rfl
  have hadj : ∀ b b', M.adjugate b b' ∈ S := by
    intro b b'
    rw [← hMM, ← RingHom.map_adjugate]
    exact (M₀.adjugate b b').2
  have hdetS : M.det ∈ S := by
    rw [← hMM, ← RingHom.map_det]; exact (M₀.det).2
  set u := hdet.unit with hu
  have huS : (u : V) ∈ S := by rw [hu, IsUnit.unit_spec]; exact hdetS
  have hinv := inv_mem_limSub φ q hq0 hqu u huS
  refine ⟨((u⁻¹ : Vˣ) : V) • M.adjugate, ?_, ?_⟩
  · rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul]
    have : ((u⁻¹ : Vˣ) : V) * M.det = 1 := by
      rw [show M.det = (u : V) by rw [hu, IsUnit.unit_spec]]; exact Units.inv_mul u
    rw [this, one_smul]
  · intro b b' N
    have : (((u⁻¹ : Vˣ) : V) • M.adjugate) b b' ∈ S := by
      rw [Matrix.smul_apply, smul_eq_mul]; exact S.mul_mem hinv (hadj b b')
    exact this N
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LimitIsotropicFrameIntegralOfSteps
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv

open MvPowerSeries
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dAct)

theorem subst_comb_expPt {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d n : ℕ} {σ κ : Type} [Fintype κ]
    (G : LogFGL v d) (w : κ → Fin d → MvPowerSeries σ C) (hw : ∀ b i, constantCoeff (w b i) = 0)
    (F : MvPowerSeries (Fin n × Fin d) C) (M : κ → Fin n → Matrix (Fin d) (Fin d) C) :
    (subst (fun q : Fin n × Fin d => ∑ i : κ × Fin d, M i.1 q.1 q.2 i.2 • w i.1 i.2)
      (subst (fun q : Fin n × Fin d => expPt G (fun e => (X (q.1, e) : MvPowerSeries (Fin n × Fin d) C)) q.2) F :
        MvPowerSeries (Fin n × Fin d) C) : MvPowerSeries σ C) =
      subst (fun q : Fin n × Fin d => expPt G (∑ b, mv (M b q.1) (w b)) q.2) F := by
  have ht : HasSubst (fun q : Fin n × Fin d => ∑ i : κ × Fin d, M i.1 q.1 q.2 i.2 • w i.1 i.2) :=
    hasSubst_of_constantCoeff_zero (by intro q; simp [hw])
  have hs : HasSubst (fun q : Fin n × Fin d =>
      expPt G (fun e => (X (q.1, e) : MvPowerSeries (Fin n × Fin d) C)) q.2) :=
    hasSubst_of_constantCoeff_zero (fun q => cc_expPt G (by simp) q.2)
  refine (subst_comp_subst_apply hs ht F).trans ?_
  congr 1
  funext q
  refine (subst_expPt G ht (by simp) q.2).trans ?_
  congr 1
  funext e
  refine (subst_X ht _).trans ?_
  simp [mv, Fintype.sum_prod_type, Finset.sum_apply]

theorem le_v_pow_mul_int {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {p : ℕ} (hp : v (p : C) = 1)
    (N : ℕ) (z : ℤ) : ((N : ℝ) : WithTop ℝ) ≤ v ((((p : ℤ) ^ N * z : ℤ)) : C) := by
  have hz : 0 ≤ v (z : C) := intCast_mem (ReciprocityTheory.ChartRestriction.G.Sh.ptIntSub v) z
  push_cast
  rw [v.map_mul, v.map_pow, hp]
  calc ((N : ℕ) : WithTop ℝ) = N • (1 : WithTop ℝ) := by simp
    _ ≤ _ := le_add_of_nonneg_right hz

theorem limFrame : AddSt → ActSt → UnitSt → BiaddSt → FrameSt → FinSt → ContSt → LimFrameSt := by
  classical
  intro _ hAct hUnit hBi hFr hFin hCont C _ _ v p hp d R _ _ O _ _ _ B hB h hh σ _ κ _ w hw w0 n A a hA hiso α
  have hw0 : ∀ b i, constantCoeff (w b i) = 0 := fun b => (hw b).1
  have mono : ∀ {M N : ℕ} {x : WithTop ℝ}, M ≤ N → ((N : ℝ) : WithTop ℝ) ≤ x → ((M : ℝ) : WithTop ℝ) ≤ x :=
    fun hMN hx => le_trans (WithTop.coe_le_coe.2 (Nat.cast_le.2 hMN)) hx
  have zle : ∀ {N : ℕ} {x : C}, ((N : ℝ) : WithTop ℝ) ≤ v x → IsIntV v x := fun hx => by
    have := mono (Nat.zero_le _) hx
    simpa [IsIntV] using this
  have hD : ∀ (x : O) i j, IsIntV v (dAct C B x i j) := fun x i j => hB.2.1 x i _
  have hAi : ∀ b j e e', IsIntV v (A b j e e') := fun b j e e' => by
    have := (ReciprocityTheory.ChartRestriction.G.Sh.ptIntSub v).add_mem (zle (hA 0 b j e e')) (hD (a 0 b j) e e')
    rw [sub_add_cancel] at this
    exact this
  obtain ⟨m, e, he⟩ := Module.Finite.exists_fin (R := ℤ) (M := O)
  let g : κ × κ × Fin m → MvPowerSeries σ C := fun i =>
    pairSer (fglOf hB) h (w i.1) (mv (dAct C B (e i.2.2)) (w i.2.1))
  have hg0 : ∀ i, constantCoeff (g i) = 0 := fun i =>
    (hBi C v d R O B hB h hh σ (w i.1) (w i.1) _ (hw _) (hw _)
      ((hAct C v d R O B hB σ (e i.2.2)).2 _ (hw i.2.1))).1
  obtain ⟨N₀, hN₀⟩ := hCont C v (Fin n × Fin d) σ (κ × Fin d)
    (subst (fun q : Fin n × Fin d => expPt (fglOf hB) (fun e => (X (q.1, e) : MvPowerSeries (Fin n × Fin d) C)) q.2)
      (frameSer B h w0 n)) (fun i => w i.1 i.2) (fun i => hw0 _ _) α
  choose N₁ hN₁ using fun γ => hCont C v Unit σ (κ × κ × Fin m) (PowerSeries.exp C) g hg0 γ
  obtain ⟨N, hN0, hN1⟩ : ∃ N : ℕ, N₀ ≤ N ∧ ∀ x ∈ Finset.HasAntidiagonal.antidiagonal α, N₁ x.2 ≤ N :=
    ⟨max N₀ ((Finset.HasAntidiagonal.antidiagonal α).sup fun x => N₁ x.2), le_max_left _ _,
      fun x hx => le_trans (Finset.le_sup (f := fun x => N₁ x.2) hx) (le_max_right _ _)⟩
  have hdec : ∀ b b', ∃ nn : Fin m → ℤ,
      (∑ j, star (a N b j) * a N b' j) * w0 = ∑ i, ((p : ℤ) ^ N * nn i) • e i := fun b b' => by
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 (hiso N b b')
    obtain ⟨nn, hnn⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ (v := e) (x := c * w0)).1
      (by rw [he]; exact Submodule.mem_top)
    refine ⟨nn, ?_⟩
    rw [hc, mul_assoc, ← hnn, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [zsmul_eq_mul, mul_assoc]
  choose nn hnn using hdec
  have hU := hFin C v d R O B hB h hh σ κ w hw w0 n (a N) (Fin m) e (fun b b' i => (p : ℤ) ^ N * nn b b' i) hnn
  have hF := (hFr C v d R O B hB h hh w0 n).2.2 σ (fun j => ∑ b, mv (dAct C B (a N b j)) (w b))
    (fun j i => by simp [Finset.sum_apply, mv, hw0])
  let s : κ × κ × Fin m → C := fun i => (((p : ℤ) ^ N * nn i.1 i.2.1 i.2.2 : ℤ) : C)
  have hT : ∑ b, ∑ b', ∑ i, (((p : ℤ) ^ N * nn b b' i : ℤ) : C) •
      pairSer (fglOf hB) h (w b) (mv (dAct C B (e i)) (w b')) = ∑ i, s i • g i := by
    simp only [Fintype.sum_prod_type, s, g]
  rw [hT] at hU
  have hT0 : constantCoeff (∑ i, s i • g i) = 0 := by simp [hg0]
  obtain ⟨hz, -, -, hmul, -⟩ := hUnit C v σ
  have hprod := hmul _ _ hU.1 hT0
  rw [sub_add_cancel, ← hF] at hprod
  have h1 := hN₀ (fun q i => A i.1 q.1 q.2 i.2) (fun q i => dAct C B (a N i.1 q.1) q.2 i.2)
    (fun q i => hAi _ _ _ _) (fun q i => hD _ _ _) (fun q i => mono hN0 (hA N _ _ _ _))
  rw [subst_comb_expPt (fglOf hB) w hw0 _ A,
    subst_comb_expPt (fglOf hB) w hw0 _ (fun b j => dAct C B (a N b j)), hprod] at h1
  have h2 : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal α,
      IsIntV v (coeff x.2 (PowerSeries.subst (∑ i, s i • g i) (PowerSeries.exp C))) := fun x hx => by
    have h3 := hN₁ x.2 (fun _ => s) (fun _ _ => 0) (fun _ i => zle (le_v_pow_mul_int hp N _))
      (fun _ _ => by simp [IsIntV]) (fun _ i => by
        rw [sub_zero]; exact mono (hN1 x hx) (le_v_pow_mul_int hp N _))
    simp only [zero_smul, Finset.sum_const_zero] at h3
    have h4 := (ReciprocityTheory.ChartRestriction.G.Sh.ptIntSub v).add_mem h3 (hz.2 x.2)
    have h5 : ∀ y z : C, y - z + z ∈ ReciprocityTheory.ChartRestriction.G.Sh.ptIntSub v → IsIntV v y := fun y z hyz => by
      rw [sub_add_cancel] at hyz
      exact hyz
    exact h5 _ _ h4
  rw [coeff_mul] at h1
  have h6 := (ReciprocityTheory.ChartRestriction.G.Sh.ptIntSub v).add_mem h1
    ((ReciprocityTheory.ChartRestriction.G.Sh.ptIntSub v).sum_mem fun x hx =>
      (ReciprocityTheory.ChartRestriction.G.Sh.ptIntSub v).mul_mem (hU.2 x.1) (h2 x hx))
  rw [sub_add_cancel] at h6
  exact h6

end GlobalTheory.IsoTriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleOnOpenPullCompIso
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue

theorem isOn_pull_comp : ∀ (X Z Z' : Scheme.{0}) (W : X.Opens) (L : LB X) (r : Z ⟶ X) (s : Z' ⟶ Z),
    IsOn W L → (∀ z, r z ∈ W) → LBIso ((L.pull r).pull s) (L.pull (s ≫ r)) := by
  intro X Z Z' W L r s hL hr
  have h : (L.pull (s ≫ r)).IsLB := GlobalTheory.T.isLineBundle_pull_of_isLineBundleOnOpen X Z' W L (s ≫ r) hL fun z ↦ by
    simpa using hr (s z)
  exact iso_of_chart h (chartPullLinComb L r (fun _ : PUnit => s) (fun _ => s ≫ r) (fun _ => 1) (𝟙 _)
    fun _ => (Category.id_comp _).symm)

end GlobalTheory.PicGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOrderCompletionSurjectiveFromIntegralAdeles
section
open IsDedekindDomain NumberField
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.OrdLift

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem one_mem_intAf : (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) ∈ Formalism.MainNotions.StandardLattice.intAf F := fun v => by
  rw [map_one]; exact one_mem _

theorem mul_mem_intA {x y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E} (hx : x ∈ GlobalTheory.PlaceComp.intA F E)
    (hy : y ∈ GlobalTheory.PlaceComp.intA F E) : x * y ∈ GlobalTheory.PlaceComp.intA F E :=
  by apply _root_.UpperTheory.Reformulated.B.Uc13.mul_mem_intA <;> assumption

end GlobalTheory.OrdLift

theorem GlobalTheory.OrdLift.ordAt_lift : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v ⊗[F] E),
    a ∈ GlobalTheory.PlaceComp.ordAt E v → ∃ t ∈ GlobalTheory.PlaceComp.intA F E, GlobalTheory.PlaceComp.evF E v t = a := by
  intro F E _ _ _ _ _ v a ha
  induction ha using Subring.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, x, rfl⟩ := hy
    refine ⟨Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.singleV F v b ⊗ₜ[F] (x : E),
      AddSubgroup.subset_closure ⟨_, GlobalTheory.SplitIdem.singleV_mem_intAf F v ⟨b, hb⟩, x, rfl⟩, ?_⟩
    show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.singleV F v b) ⊗ₜ[F] (x : E) = _
    rw [GlobalTheory.SplitIdem.evalV_singleV_same]
  | zero => exact ⟨0, zero_mem _, map_zero _⟩
  | one =>
    refine ⟨1, AddSubgroup.subset_closure ⟨1, GlobalTheory.OrdLift.one_mem_intAf F, 1, ?_⟩, map_one _⟩
    simp [Algebra.TensorProduct.one_def]
  | add x y _ _ hx hy =>
    obtain ⟨s, hs, rfl⟩ := hx
    obtain ⟨t, ht, rfl⟩ := hy
    exact ⟨s + t, add_mem hs ht, map_add _ _ _⟩
  | neg x _ hx =>
    obtain ⟨s, hs, rfl⟩ := hx
    exact ⟨-s, neg_mem hs, map_neg _ _⟩
  | mul x y _ _ hx hy =>
    obtain ⟨s, hs, rfl⟩ := hx
    obtain ⟨t, ht, rfl⟩ := hy
    exact ⟨s * t, GlobalTheory.OrdLift.mul_mem_intA F E hs ht, map_mul _ _ _⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemInterConjIff
section
namespace GlobalTheory.ConjugateIntersectionMembership

theorem mem_inter_conj_iff {H : Type} [Group H] {T L : Subgroup H} {x g : H} :
    g ∈ GlobalTheory.LKLoc.locPart T L x ↔ g ∈ T ∧ x⁻¹ * g * x ∈ L := by
  rw [GlobalTheory.LKLoc.locPart, Subgroup.mem_inf, Subgroup.mem_map]
  refine and_congr_right fun _ => ⟨?_, fun h => ⟨x⁻¹ * g * x, h, ?_⟩⟩
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · simp [MulAut.conj_apply, mul_assoc]

end GlobalTheory.ConjugateIntersectionMembership
end

