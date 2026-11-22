import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0012

-- bundled from Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.BetaIsPrincipal
section
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.BetaCounterexample
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (c : Coeff l)

omit [NumberField E] [IsCMField E] in
theorem ln_std (n : ℕ) : (⟨stdLat E n⟩ : GenLat E n).Ln = stdLat E n := inf_idem _

theorem std_one (n : ℕ) (β : c.F) (hβ : β = 1 ∨ β = -1) :
    β ≠ 0 ∧ BetaIs (Dw := Dw) c (⟨stdLat E n⟩ : GenLat E n) β ∧ BetaAbs (Dw := Dw) c (⟨stdLat E n⟩ : GenLat E n) β := by
  have h1 : Submodule.span (𝓞 c.F) {β} = 1 := by
    rcases hβ with rfl | rfl
    · exact (Submodule.one_eq_span).symm
    · rw [Submodule.one_eq_span, ← Set.neg_singleton, Submodule.span_neg]
  refine ⟨by rcases hβ with rfl | rfl <;> simp, ?_, ?_⟩
  · unfold BetaIs
    rw [h1, one_mul, ln_std]
  · intro σ
    rw [ln_std]
    rcases hβ with rfl | rfl <;> simp

theorem betaH_congr {n m : ℕ} (Λ : GenLat E n) (Λ' : GenLat E m)
    (h : ∀ β : c.F, (β ≠ 0 ∧ BetaIs (Dw := Dw) c Λ β ∧ BetaAbs (Dw := Dw) c Λ β) ↔
      (β ≠ 0 ∧ BetaIs (Dw := Dw) c Λ' β ∧ BetaAbs (Dw := Dw) c Λ' β)) :
    betaH (Dw := Dw) c Λ = betaH (Dw := Dw) c Λ' := by
  unfold betaH
  have e := funext fun β => propext (h β)
  generalize (fun β : c.F => β ≠ 0 ∧ BetaIs (Dw := Dw) c Λ β ∧ BetaAbs (Dw := Dw) c Λ β) = p at e ⊢
  subst e
  rfl

theorem betaH_ne_zero {n : ℕ} (Λ : GenLat E n) : betaH (Dw := Dw) c Λ ≠ 0 := by
  unfold betaH
  split_ifs with h
  · exact h.choose_spec.1
  · exact one_ne_zero

omit [NumberField E] [IsCMField E] in

theorem detSet_scale {n : ℕ} (M M' : Submodule (𝓞 E) (Fin n → E)) (a : E)
    (h : ∀ v, v ∈ M' ↔ ∃ w ∈ M, v = a • w) : detSet M' = (fun d => a ^ n * d) '' detSet M := by
  have key : ∀ w : Fin n → Fin n → E, Matrix.det (Matrix.of fun i j => (a • w j) i) =
      a ^ n * Matrix.det (Matrix.of fun i j => w j i) := by
    intro w
    have : (Matrix.of fun i j => (a • w j) i) = a • (Matrix.of fun i j => w j i) := by
      ext i j; simp
    rw [this, Matrix.det_smul, Fintype.card_fin]
  ext d
  constructor
  · rintro ⟨v, hv, rfl⟩
    choose w hw hw' using fun i => (h (v i)).1 (hv i)
    refine ⟨_, ⟨w, hw, rfl⟩, ?_⟩
    have : v = fun j => a • w j := funext hw'
    subst this
    exact (key w).symm
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨fun j => a • w j, fun i => (h _).2 ⟨w i, hw i, rfl⟩, (key w).symm⟩

theorem betaIs_principal {n : ℕ} (Λ : GenLat E n) (a : E) (h : ∀ v, v ∈ Λ.Ln ↔ ∃ w ∈ Λ.La, v = a • w) :
    BetaIs (Dw := Dw) c Λ (∏ τ : E →+* ℂ, embF c τ (a ^ n) ^ Dw.mult τ) := by
  have h1 : ∀ τ, idealAt c Λ.Ln τ = Submodule.span (𝓞 c.F) {embF c τ (a ^ n)} * idealAt c Λ.La τ := by
    intro τ
    unfold idealAt
    rw [detSet_scale Λ.La Λ.Ln a h, Submodule.span_mul_span, Set.singleton_mul, Set.image_image, Set.image_image]
    simp only [map_mul]
  unfold BetaIs
  simp only [h1, mul_pow, Finset.prod_mul_distrib, Submodule.span_pow, Set.singleton_pow]
  rw [Submodule.prod_span_singleton]

theorem betaIs_bot {n : ℕ} (hn : 0 < n) (τ₀ : E →+* ℂ) (h0 : Dw.mult τ₀ ≠ 0) (β : c.F) :
    BetaIs (Dw := Dw) c (⟨⊥⟩ : GenLat E n) β := by
  have hd : ∀ τ, idealAt c (⊥ : Submodule (𝓞 E) (Fin n → E)) τ = 0 := by
    intro τ
    unfold idealAt
    rw [Submodule.zero_eq_bot, Submodule.span_eq_bot]
    rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    have : (Matrix.of fun i j => v j i) = 0 := by
      ext i j; simp [(Submodule.mem_bot _).1 (hv j)]
    have hne : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    rw [this, Matrix.det_zero, map_zero]
  have hL : (⟨⊥⟩ : GenLat E n).Ln = ⊥ := bot_inf_eq _
  unfold BetaIs
  rw [hL]
  have hz : ∏ τ : E →+* ℂ, idealAt c (⊥ : Submodule (𝓞 E) (Fin n → E)) τ ^ Dw.mult τ = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ τ₀) (by rw [hd, zero_pow h0])
  rw [hz, mul_zero]

theorem not_unimod_bot {n : ℕ} (hn : 0 < n) : ¬ (⟨⊥⟩ : GenLat E n).Unimod := by
  intro h
  have := (h (fun _ => 1)).2 (by
    intro w hw
    rw [(Submodule.mem_bot _).1 hw]
    simp)
  have h1 := congrFun ((Submodule.mem_bot _).1 this) ⟨0, hn⟩
  simp at h1

end GlobalTheory.BetaCounterexample
end
end

-- bundled from Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.FullIffBijective
section
noncomputable section

namespace GlobalTheory.CoeffRingTest

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

section Ring

variable {O L : Type} [CommRing O] [Field L] (ι : O →+* L) (σ : L →+* ℂ)

def gen : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ (Set.range (σ.comp ι))

def Full : Prop := Function.Injective ι ∧ ∀ z ∈ gen ι σ, IsIntegral ℤ z → z ∈ Set.range (σ.comp ι)

theorem zeta_prim {n : ℕ} (hn : n ≠ 0) : IsPrimitiveRoot (zeta n) n := Complex.isPrimitiveRoot_exp n hn

end Ring

theorem zeta_mem_of_dvd {F : IntermediateField ℚ ℂ} {m n : ℕ} (hn : n ≠ 0) (hmn : m ∣ n) (h : zeta n ∈ F) :
    zeta m ∈ F := by
  obtain ⟨k, rfl⟩ := hmn
  have hm : m ≠ 0 := left_ne_zero_of_mul hn
  have hk : k ≠ 0 := right_ne_zero_of_mul hn
  have : zeta m = zeta (m * k) ^ k := by
    rw [zeta, zeta, ← Complex.exp_nat_mul]
    congr 1
    have : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk
    have : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hm
    push_cast
    field_simp
  rw [this]
  exact pow_mem h k

theorem zeta_pd_mem {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n) (h : d.IsLev) : zeta d.pd ∈ c.F := by
  have hM : d.l₂.M' ≠ 0 := Nat.lcm_ne_zero (by have := d.l₂.three_le; omega) d.l₂.A_pos.ne'
  have hd : d.pd ∣ d.l₂.M' := (h.2.1 ▸ dvd_mul_left d.pd l.M).trans (Nat.dvd_lcm_left _ _)
  exact d.hF ▸ zeta_mem_of_dvd hM hd d.c₂.zeta_mem

end GlobalTheory.CoeffRingTest
end
end

-- bundled from Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.InducedEqOne
section
noncomputable section

namespace GlobalTheory.DeltaPinTest

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ}

theorem noDelta_phiPin (nab : NabV Xo c) (m : SABMap Xo.univ.t Xo.univ.t (𝟙 Xo.X)) :
    (noDelta Xo c nab m n).PhiPin (fun _ => 1) 1 (fun _ => 0) := by
  haveI hs : Subsingleton (LaJ Xo c (noDelta Xo c nab m n)) := by
    apply Submodule.Quotient.subsingleton_iff.2
    show Ideal.map _ ⊤ • ⊤ = ⊤
    rw [Ideal.map_top, Submodule.top_smul]
  refine ⟨fun _ _ _ => rfl, fun _ _ => Subsingleton.elim _ _, fun _ _ _ _ => by simp, rfl,
    Subsingleton.elim _ _, fun q => ?_⟩
  haveI : Unique (Fin n → LaJ Xo c (noDelta Xo c nab m n)) := uniqueOfSubsingleton (fun _ => 0)
  rw [finsum_unique]
  have hz : ((⟨zeta l.M', c.zeta_mem⟩ : c.F) ^ (l.M' / 1)) = 1 := by
    have h0 : l.M' ≠ 0 := Nat.lcm_ne_zero (by have := l.three_le; omega) l.A_pos.ne'
    apply Subtype.ext
    rw [Nat.div_one]
    exact (Complex.isPrimitiveRoot_exp _ h0).pow_eq_one
  show (noDelta Xo c nab m n).eF 1 = (noDelta Xo c nab m n).eF 1 * ((⟨zeta l.M', c.zeta_mem⟩ : c.F) ^ (l.M' / 1)) ^ _
  rw [hz]
  exact ((congrArg _ (one_zpow _)).trans (mul_one _)).symm

end GlobalTheory.DeltaPinTest
end
end

-- bundled from Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.LevelGroupEqTopOfCoprime
section
noncomputable section

namespace GlobalTheory.LevelGroupTest

open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}

theorem natCast_mem_half (l : Level H) : (l.M : 𝓞 E) ∈ l.Mb := by
  have h : Ideal.span {(l.M : 𝓞 E)} ≤ l.Mb := by
    rw [← l.prod]; exact Ideal.mul_le_left
  exact h (Ideal.subset_span rfl)

attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

end GlobalTheory.LevelGroupTest
end
end

-- bundled from Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.TransformIndicator
section
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ClassSumProbe
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj MvPolynomial
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

set_option autoImplicit false in
open NumberField MvPolynomial in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H}
  {l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} in
private theorem mfr_ne_bot : _root_.Formalism.L2.Pj.Mfr l ≠ ⊥ := by
  intro h
  have hM := l.prod
  have h3 := l.three_le
  unfold _root_.Formalism.L2.Pj.Mfr at h
  rw [h, Ideal.mul_bot, eq_comm, Ideal.span_singleton_eq_bot] at hM
  exact absurd (Nat.cast_eq_zero.mp hM) (by omega)

set_option autoImplicit false in
open NumberField MvPolynomial in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H}
  {l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} in

theorem _root_.GlobalTheory.ClassSumProbe.finite_conj_half :
    Finite (Dw.La ⧸ (_root_.Formalism.L2.Pj.Mfr l • ⊤ : Submodule (𝓞 E) Dw.La)) := by
  haveI := Dw.fin
  haveI : Finite (𝓞 E ⧸ _root_.Formalism.L2.Pj.Mfr l) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ mfr_ne_bot
  exact Module.finite_of_finite (𝓞 E ⧸ _root_.Formalism.L2.Pj.Mfr l)

end GlobalTheory.ClassSumProbe
end
end

-- bundled from Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.VVAlgebraMapNonneg
section
noncomputable section

namespace GlobalTheory.IntegralFrameCheck

open Formalism.L2.Pj NumberField IsDedekindDomain
open scoped WithZero

section Dvr

variable {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K'] [Algebra V K']
  [IsFractionRing V K']

theorem vV_algebraMap_nonneg (a : V) : 0 ≤ vV V (algebraMap V K' a) := by
  by_cases ha : algebraMap V K' a = 0
  · rw [ha]; simp [vV]
  · have hv : valV V (algebraMap V K' a) ≤ 1 :=
      (IsDiscreteValuationRing.maximalIdeal V).valuation_le_one a
    have := (WithZero.log_le_log (valV_ne_zero (V := V) ha) one_ne_zero).2 hv
    simp only [WithZero.log_one] at this
    simp only [vV]; omega

theorem vV_one : vV V (1 : K') = 0 := by simp [vV]

theorem vV_pow {x : K'} (hx : x ≠ 0) (n : ℕ) : vV V (x ^ n) = n * vV V x := by
  induction n with
  | zero => simp [vV]
  | succ n ih => rw [pow_succ, vV_mul (pow_ne_zero n hx) hx, ih]; push_cast; ring

variable {V' K'' : Type} [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'] [Field K''] [Algebra V' K'']
  [IsFractionRing V' K'']

theorem vV_map_unit (i : K' →+* K'') (hi : ∀ a : V, i (algebraMap V K' a) ∈ Set.range (algebraMap V' K''))
    (u : Vˣ) : vV V' (i (algebraMap V K' u)) = 0 := by
  have hne : ∀ w : Vˣ, i (algebraMap V K' w) ≠ 0 := fun w =>
    ((w.isUnit.map (algebraMap V K')).map i).ne_zero
  have h0 : ∀ w : Vˣ, 0 ≤ vV V' (i (algebraMap V K' w)) := fun w => by
    obtain ⟨b, hb⟩ := hi w
    rw [← hb]; exact vV_algebraMap_nonneg b
  have h1 := vV_mul (V := V') (hne u) (hne u⁻¹)
  rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, vV_one] at h1
  have := h0 u
  have := h0 u⁻¹
  omega

theorem exists_vV_map (i : K' →+* K'') (hi : ∀ a : V, i (algebraMap V K' a) ∈ Set.range (algebraMap V' K'')) :
    ∃ r : ℕ, ∀ x, vV V' (i x) = (r : ℤ) * vV V x := by
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hp0 : algebraMap V K' p ≠ 0 := by
    simpa using hp.ne_zero
  have hr : 0 ≤ vV V' (i (algebraMap V K' p)) := by
    obtain ⟨b, hb⟩ := hi p
    rw [← hb]; exact vV_algebraMap_nonneg b
  have hp1 : vV V (algebraMap V K' p) = 1 := by
    have h : valV V (algebraMap V K' p) = WithZero.exp (-1 : ℤ) := by
      unfold valV
      rw [HeightOneSpectrum.valuation_of_algebraMap]
      refine HeightOneSpectrum.intValuation_singleton _ hp.ne_zero ?_
      exact hp.maximalIdeal_eq
    simp [vV, h]
  refine ⟨(vV V' (i (algebraMap V K' p))).toNat, ?_⟩
  rw [Int.toNat_of_nonneg hr]
  have key : ∀ a : V, a ≠ 0 → vV V' (i (algebraMap V K' a)) =
      vV V' (i (algebraMap V K' p)) * vV V (algebraMap V K' a) := by
    intro a ha
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hp
    have hu : algebraMap V K' u ≠ 0 := (u.isUnit.map (algebraMap V K')).ne_zero
    have hu0 : vV V (algebraMap V K' u) = 0 :=
      vV_map_unit (V' := V) (RingHom.id K') (fun a => ⟨a, rfl⟩) u
    rw [map_mul, map_pow, map_mul, map_pow,
      vV_mul ((map_ne_zero i).2 hu) (pow_ne_zero n ((map_ne_zero i).2 hp0)),
      vV_mul hu (pow_ne_zero n hp0), vV_pow ((map_ne_zero i).2 hp0), vV_pow hp0, vV_map_unit i hi u, hu0, hp1]
    ring
  intro x
  by_cases hx : x = 0
  · subst hx; simp [vV]
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := V) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hb' : algebraMap V K' b ≠ 0 := by simpa using hb0
  have ha0 : a ≠ 0 := by rintro rfl; simp at hx
  have e : algebraMap V K' a / algebraMap V K' b * algebraMap V K' b = algebraMap V K' a :=
    div_mul_cancel₀ _ hb'
  have h1 := vV_mul (V := V) hx hb'
  have h2 := vV_mul (V := V') ((map_ne_zero i).2 hx) ((map_ne_zero i).2 hb')
  rw [← map_mul, e, key a ha0, key b hb0] at h2
  rw [e] at h1
  rw [h1] at h2
  linarith

end Dvr

theorem nval_map_of_overLa {K : Type} [Field K] [NumberField K] {la : HeightOneSpectrum (𝓞 K)}
    {T T' : CDVR} {io : K →+* T.Fr} {io' : K →+* T'.Fr} {e e' : ℕ}
    (ho : OverLa la T.V io e) (ho' : OverLa la T'.V io' e') (i : T.Fr →+* T'.Fr)
    (hc : ∀ a, i (io a) = io' a)
    (hi : ∀ a : T.V, i (algebraMap T.V T.Fr a) ∈ Set.range (algebraMap T'.V T'.Fr)) :
    ∃ r : ℕ, 0 < r ∧ e' = r * e ∧ (∀ x, vV T'.V (i x) = (r : ℤ) * vV T.V x) ∧
      ∀ x, nval T'.V e' (i x) = nval T.V e x := by
  obtain ⟨r, hr⟩ := exists_vV_map i hi
  obtain ⟨a, ha⟩ := la.valuation_exists_uniformizer K
  have h1 : vLa la a = 1 := by simp [vLa, ha]
  have h2 := hr (io a)
  rw [hc, ho'.2, ho.2, h1] at h2
  have he : e' = r * e := by
    have : (e' : ℤ) = (r * e : ℕ) := by push_cast; linarith
    exact_mod_cast this
  have hr0 : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · have := ho'.1; rw [he, h] at this; simp at this
    · exact h
  exact ⟨r, hr0, he, hr, fun x => he ▸ nval_bc i hr0 hr e x⟩

open ReciprocityTheory.ChartRestriction.G.Geo.Tor in

theorem intAll_ramified {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (h : Formalism.L2.PjFree.IntAll Xo c)
    (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (ho : OverLa la T.V io e)
    (hf : T.FinRes) (y : letI := io.toAlgebra; FrPt Xo c T.Fr) :
    ∃ (T' : CDVR) (io' : c.F →+* T'.Fr) (r : ℕ) (y' : IntFr Xo c T' io'), 0 < r ∧ OverLa la T'.V io' (r * e) ∧
      T'.FinRes ∧
      letI := io.toAlgebra; letI := io'.toAlgebra
      ∃ (φ : T.Fr →ₐ[c.F] T'.Fr) (z : FrPt Xo c T'.Fr) (t : Ix Dw → T'.Frˣ),
        (∀ x, vV T'.V (φ x) = (r : ℤ) * vV T.V x) ∧ (∀ x, nval T'.V (r * e) (φ x) = nval T.V e x) ∧
        FrMap φ y z ∧ FrBor t z y'.1 := by
  obtain ⟨T', io', e', y', ho', hf', φ, z, t, hφ, hz, hb⟩ := h la T io e ho hf y
  let _ := io.toAlgebra
  let _ := io'.toAlgebra
  obtain ⟨r, hr, rfl, h1, h2⟩ := nval_map_of_overLa ho ho' φ.toRingHom (fun a => φ.commutes a) hφ
  exact ⟨T', io', r, y', hr, ho', hf', φ, z, t, h1, h2, hz, hb⟩

end GlobalTheory.IntegralFrameCheck
end
end

