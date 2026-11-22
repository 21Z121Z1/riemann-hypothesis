import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0012
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA

-- bundled from Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.NotOverAndTriv
section
noncomputable section

namespace GlobalTheory.Height.OrderTieGuards

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0 Formalism.L2.Pj

section Unit

variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  {v : AddValuation Ω (WithTop ℤ)} {la : HeightOneSpectrum (𝓞 K)}

omit [NumberField K] in

theorem nonneg_int (v : AddValuation Ω (WithTop ℤ)) (a : 𝓞 K) : 0 ≤ v (algebraMap K Ω (a : K)) := by
  have h : IsIntegral ℤ (algebraMap K Ω (a : K)) := map_isIntegral_int (algebraMap K Ω) a.isIntegral_coe
  have h2 : IsIntegral (vRing v) (algebraMap K Ω (a : K)) := h.tower_top
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := vRing v) (K := Ω)).1 h2
  rw [← hy]
  exact y.2

theorem zero_of_notMem (ho : IsOver (K := K) v la) {a : 𝓞 K} (ha : a ∉ la.asIdeal) :
    v (algebraMap K Ω (a : K)) = 0 :=
  le_antisymm (not_lt.1 fun h => ha ((ho a).1 h)) (nonneg_int v a)

theorem zero_of_unit (ho : IsOver (K := K) v la) {u : K} (hu : la.valuation K u = 1) :
    v (algebraMap K Ω u) = 0 := by
  obtain ⟨n, d, hnd⟩ := la.exists_primeCompl_mul_eq_of_integer u hu.le
  have hd : la.valuation K (algebraMap (𝓞 K) K d) = 1 := (la.valuation_eq_one_iff_notMem).2 d.2
  have hn : la.valuation K (algebraMap (𝓞 K) K n) = 1 := by rw [← hnd, map_mul, hu, hd, one_mul]
  have h1 := zero_of_notMem ho ((la.valuation_eq_one_iff_notMem).1 hn)
  have h2 := zero_of_notMem ho (a := d) d.2
  have h3 : algebraMap K Ω u * algebraMap K Ω ((d : 𝓞 K) : K) = algebraMap K Ω ((n : 𝓞 K) : K) := by
    rw [← map_mul]; exact congrArg _ hnd
  have h4 := congrArg v h3
  rwa [AddValuation.map_mul, h1, h2, add_zero] at h4

theorem v_zpow (hv : IsNormDiscrete v) {x : Ω} (hx : x ≠ 0) {m : ℤ} (hm : v x = m) (k : ℤ) :
    v (x ^ k) = ((k * m : ℤ) : WithTop ℤ) := by
  induction k using Int.induction_on with
  | zero => simp
  | succ k ih =>
    rw [zpow_add_one₀ hx, AddValuation.map_mul, ih, hm, ← WithTop.coe_add]; congr 1; ring
  | pred k ih =>
    obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 (hv.1 _ (zpow_ne_zero (-(k : ℤ) - 1) hx))
    have e : x ^ (-(k : ℤ) - 1) * x = x ^ (-(k : ℤ)) := by rw [← zpow_add_one₀ hx]; congr 1; ring
    have h := congrArg v e
    rw [AddValuation.map_mul, ih, hm, ← hs, ← WithTop.coe_add, WithTop.coe_inj] at h
    rw [← hs, WithTop.coe_inj]; linarith

theorem exists_mul (hv : IsNormDiscrete v) (ho : IsOver (K := K) v la) :
    ∃ m : ℤ, 0 < m ∧ (∃ p ∈ la.asIdeal, p ≠ 0 ∧ vLa la (p : K) = 1) ∧
      ∀ a : K, a ≠ 0 → v (algebraMap K Ω a) = ((m * vLa la a : ℤ) : WithTop ℤ) := by
  obtain ⟨p, hp⟩ := la.intValuation_exists_uniformizer
  have hpK : la.valuation K (p : K) = WithZero.exp (-1 : ℤ) := by
    rw [← hp]; exact HeightOneSpectrum.valuation_of_algebraMap la p
  have hp0 : (p : K) ≠ 0 := by
    intro h; rw [h, map_zero] at hpK; exact WithZero.exp_ne_zero hpK.symm
  have hpm : p ∈ la.asIdeal := by
    rw [← la.intValuation_lt_one_iff_mem, hp, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have hx : algebraMap K Ω (p : K) ≠ 0 := (map_ne_zero _).2 hp0
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 (hv.1 _ hx)
  have hm0 : 0 < m := by
    have := (ho p).2 hpm
    rw [← hm] at this; exact_mod_cast this
  refine ⟨m, hm0, ⟨p, hpm, fun h => hp0 (by simp [h]), by simp [vLa, hpK]⟩, fun a ha => ?_⟩
  have hva : la.valuation K a ≠ 0 := by simpa using ha
  have hu : la.valuation K (a / (p : K) ^ vLa la a) = 1 := by
    rw [map_div₀, map_zpow₀, hpK, ← WithZero.exp_zsmul, div_eq_one_iff_eq WithZero.exp_ne_zero]
    simp [vLa, WithZero.exp_log hva]
  have e : algebraMap K Ω a = algebraMap K Ω (a / (p : K) ^ vLa la a) * algebraMap K Ω (p : K) ^ vLa la a := by
    rw [← map_zpow₀ (algebraMap K Ω), ← map_mul, div_mul_cancel₀ _ (zpow_ne_zero _ hp0)]
  rw [congrArg v e, AddValuation.map_mul, zero_of_unit ho hu, zero_add, v_zpow hv hx hm.symm, mul_comm]

theorem restrict_eq (hv : IsNormDiscrete v) (ho : IsOver (K := K) v la) :
    0 < ramIdx (K := K) v la ∧
      ∀ a : K, a ≠ 0 → v (algebraMap K Ω a) = ((ramIdx (K := K) v la * vLa la a : ℤ) : WithTop ℤ) := by
  obtain ⟨m, hm, ⟨p, hp, hp0, hp1⟩, h⟩ := exists_mul hv ho
  have : ramIdx (K := K) v la = m := by
    refine IsLeast.csInf_eq ⟨⟨p, hp, hp0, ?_⟩, ?_⟩
    · rw [h _ (by exact_mod_cast hp0), hp1, mul_one]
    · rintro n ⟨a, ha, ha0, hn⟩
      have h1 := (ho a).2 ha
      rw [h _ (by exact_mod_cast ha0)] at hn h1
      have h2 : m * vLa la (a : K) = n := by exact_mod_cast hn
      have h3 : 0 < m * vLa la (a : K) := by exact_mod_cast h1
      have h4 : 0 < vLa la (a : K) := (mul_pos_iff_of_pos_left hm).1 h3
      nlinarith
  rw [this]; exact ⟨hm, h⟩

end Unit

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def Clause (h : GenFrEx Xo c) (Z : Comp Xo c) (δ : Ix Dw → ℤ) (v : AddValuation (Om Z) (WithTop ℤ)) (e : ℤ)
    (val : Rul Xo c → EReal) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n → evC h Z f ≠ 0 →
    (((ordC δ v (wtZ a n) (valC h a n f Z) : ℤ) : ℝ) : EReal) = ((e : ℝ) : EReal) * val f

variable {h : GenFrEx Xo c} {Z : Comp Xo c} {δ δ' : Ix Dw → ℤ} {v : AddValuation (Om Z) (WithTop ℤ)} {e : ℤ}
  {val : Rul Xo c → EReal}

end GlobalTheory.Height.OrderTieGuards
end
end

-- bundled from Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.RegularityFirstClauseBot
section
noncomputable section

namespace GlobalTheory.TrivialValuationTest

open Formalism.L2.Pj Formalism.L2.PjFree NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Ring

variable {V F : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field F] [Algebra V F]
  [IsFractionRing V F]

theorem vV_unit (u : Vˣ) : vV V (algebraMap V F (u : V)) = 0 := by
  have h : valV V (algebraMap V F (u : V)) = 1 := by
    unfold valV
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    intro hm
    exact (IsLocalRing.mem_maximalIdeal _).1 hm u.isUnit
  simp [vV, h]

end Ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem vV_eq_zero_of_triv {T : CDVR} {ι : c.F →+* T.Fr} {y : IntFr Xo c T ι} (h : trivCls Xo c T ι y)
    {a : c.F} (ha : a ≠ 0) : vV T.V (ι a) = 0 := by
  obtain ⟨u, hu⟩ := h a ha
  rw [← hu]; exact vV_unit u

theorem not_overLa_of_triv {T : CDVR} {ι : c.F →+* T.Fr} {y : IntFr Xo c T ι} (h : trivCls Xo c T ι y)
    (la : HeightOneSpectrum (𝓞 c.F)) (e : ℕ) : ¬ OverLa la T.V ι e := by
  rintro ⟨he, hv⟩
  obtain ⟨π, hπ⟩ := la.valuation_exists_uniformizer c.F
  have hπ0 : π ≠ 0 := by rintro rfl; simp at hπ; exact absurd hπ.symm WithZero.exp_ne_zero
  have h1 := hv π
  rw [vV_eq_zero_of_triv h hπ0, vLa, hπ] at h1
  simp at h1
  omega

theorem ordQ_smul (q : QPt Xo c) {a : c.F} (ha : a ≠ 0) (f : Rul Xo c) :
    ordQ Xo c q (a • f) = ordQ Xo c q f := by
  unfold ordQ
  rw [evI_smul]
  exact nval_mul_unit 1 ((map_ne_zero q.ι).2 ha) (vV_eq_zero_of_triv q.triv ha) _

theorem ord_nonneg_of_bddBelow {C : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c)} (h : RegularityR1Quotient Xo c C)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hf : f ∈ C a n) (la : HeightOneSpectrum (𝓞 c.F)) (N : ℕ)
    (hb : ∀ v ∈ valSet Xo c (algCls Xo c) la, ((-(N : ℝ) : ℝ) : EReal) ≤ v f) (q : QPt Xo c) :
    0 ≤ ordQ Xo c q f := by
  obtain ⟨π, hπ⟩ := la.valuation_exists_uniformizer c.F
  have hπ0 : π ≠ 0 := by rintro rfl; simp at hπ; exact absurd hπ.symm WithZero.exp_ne_zero
  have hN : vLa la (π ^ N) = N := by
    simp [vLa, map_pow, hπ, ← WithZero.exp_nsmul]
  rw [← ordQ_smul q (pow_ne_zero N hπ0) f]
  refine h a n _ ((C a n).smul_mem _ hf) ⟨la, fun v hv => ?_⟩ q
  rw [(isVal_valSet la v hv).smul _ _ (pow_ne_zero N hπ0), hN]
  calc (0 : EReal) = ((((N : ℤ) : ℝ)) : EReal) + ((-(N : ℝ) : ℝ) : EReal) := by
        rw [← EReal.coe_add]; simp
    _ ≤ _ := add_le_add le_rfl (hb v hv)

theorem ord_eq_top_of_no_point {C : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c)} (h : RegularityR2Quotient Xo c C)
    (la : HeightOneSpectrum (𝓞 c.F)) (h0 : valSet Xo c (algCls Xo c) la = ∅)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hf : f ∈ C a n) (q : QPt Xo c) : ordQ Xo c q f = ⊤ := by
  by_contra hne
  have := (h a n a n 0 Fin.elim0 f 0 le_rfl (fun i => i.elim0) hf ⟨la, 0, by simp [h0]⟩ q).2 hne
  rw [iInf_of_empty] at this
  simp at this

theorem premise_fails_of_empty (hne : IntFrNe Xo c (algCls Xo c)) (ws : Fin 0 → Rul Xo c)
    (la : HeightOneSpectrum (𝓞 c.F)) : ¬ ∀ v ∈ valSet Xo c (algCls Xo c) la, ∃ i, v (ws i) ≠ ⊤ := by
  intro h
  obtain ⟨T, io, e, ho, y, hy⟩ := hne la
  obtain ⟨i, -⟩ := h _ ⟨PtV.mk la ho y hy () trivial, rfl⟩
  exact i.elim0

theorem powerSeries_const_unit (K : Type) [Field K] (a : K) (ha : a ≠ 0) :
    ∃ u : (PowerSeries K)ˣ, algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) u =
      ((algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).comp PowerSeries.C) a :=
  ⟨Units.map (PowerSeries.C : K →+* PowerSeries K).toMonoidHom (Units.mk0 a ha), rfl⟩

def powerSeriesCDVR (K : Type) [Field K] [CharZero K] : CDVR where
  V := PowerSeries K
  cpl := by rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance
  ch0 := algebraRat.charZero _

theorem trivCls_powerSeries
    (y : IntFr Xo c (powerSeriesCDVR c.F)
      ((algebraMap (PowerSeries c.F) (FractionRing (PowerSeries c.F))).comp PowerSeries.C)) :
    trivCls Xo c _ _ y := fun a ha => powerSeries_const_unit c.F a ha

theorem regularity_first_clause_bot : RegularityR1Quotient Xo c (fun _ _ => ⊥) := by
  intro a n f hf _ q
  rw [(Submodule.mem_bot c.F).1 hf, ordQ, (isEval_evI q.y).zero (), nval_zero]
  exact le_top

end GlobalTheory.TrivialValuationTest
end
end

