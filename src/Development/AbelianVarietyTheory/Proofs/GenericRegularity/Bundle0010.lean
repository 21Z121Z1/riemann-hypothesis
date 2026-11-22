import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFinsetOfMemNhds
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0009
import Development.AbelianVarietyTheory.Definitions.RegularCharts.SCharts
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0019
import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0001
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.RigFrame
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0031
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0033
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TriangularFrameMovesPeriodBlockTriangular
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0032
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0036
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemIffConjugateNotMem
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFrameOfIsPeriod
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.SpanEvalEqTopOfNoCommonZeroReduced

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.DimAddCardFlagVar
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.FlagDim

open NumberField in

theorem _root_.GlobalTheory.FlagDim.card_pairs_lt (n : ℕ) : Nat.card {p : Fin n × Fin n // p.1 < p.2} = n * (n - 1) / 2 := by
  have e : {p : Fin n × Fin n // p.1 < p.2} ≃ (j : Fin n) × Fin j :=
    { toFun := fun p => ⟨p.1.2, ⟨p.1.1, p.2⟩⟩
      invFun := fun q => ⟨(⟨q.2, q.2.2.trans q.1.2⟩, q.1), q.2.2⟩
      left_inv := fun p => rfl
      right_inv := fun q => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) n, Finset.sum_range_id]

open NumberField in

theorem _root_.GlobalTheory.FlagDim.dim_add_card_flagVar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H), Dw.dim + Nat.card (_root_.Formalism.L2.Pj.FlagVar Dw) = Module.finrank ℚ E / 2 * (Dw.p * Dw.q + Dw.p * (Dw.p - 1) / 2 + Dw.q * (Dw.q - 1) / 2) := by
  intro E _ _ _ H Dw
  classical
  have hcard : Nat.card (_root_.Formalism.L2.Pj.FlagVar Dw) = ∑ τ : E →+* ℂ, Dw.mult τ * (Dw.mult τ - 1) / 2 := by
    show Nat.card ((τ : E →+* ℂ) × {p : Fin (Dw.mult τ) × Fin (Dw.mult τ) // p.1 < p.2}) = _
    rw [Nat.card_sigma]
    simp only [_root_.GlobalTheory.FlagDim.card_pairs_lt]
  have hdim : Dw.dim = Module.finrank ℚ E / 2 * Dw.p * Dw.q := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.dim; rfl
  have hall : Fintype.card (E →+* ℂ) = Module.finrank ℚ E := Embeddings.card E ℂ
  have hcm : (Finset.univ.filter fun τ : E →+* ℂ => τ H.rt = H.rt0).card = Module.finrank ℚ E / 2 := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card, _root_.GlobalTheory.PeriodCoord.card_cmType]
  have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (E →+* ℂ)))
    (fun τ : E →+* ℂ => τ H.rt = H.rt0)
  obtain ⟨k, hk⟩ : Even (Module.finrank ℚ E) := by
    rw [IsTotallyComplex.finrank]; exact even_two_mul _
  rw [Finset.card_univ, hall] at hsplit
  have hk2 : Module.finrank ℚ E / 2 = k := by omega
  have hnot : (Finset.univ.filter fun τ : E →+* ℂ => ¬ τ H.rt = H.rt0).card = k := by omega
  have hterm : ∀ τ : E →+* ℂ, Dw.mult τ * (Dw.mult τ - 1) / 2 =
      if τ H.rt = H.rt0 then Dw.p * (Dw.p - 1) / 2 else Dw.q * (Dw.q - 1) / 2 := by
    intro τ; unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.mult; split_ifs <;> rfl
  rw [hcard, hdim, Finset.sum_congr rfl (fun τ _ => hterm τ), Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul, hcm, hnot, hk2]
  ring

end GlobalTheory.FlagDim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.IntegralityTrivialValuationsOfNormalAffineCharts
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

noncomputable section

namespace GlobalTheory.Reg.ChartInt

open IsLocalRing Formalism.L2.PjFree

section Values
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

theorem vV_nonneg (w : V) (hw : w ≠ 0) : 0 ≤ vV V (algebraMap V (FractionRing V) w) := by
  have hw' : algebraMap V (FractionRing V) w ≠ 0 := by
    intro h; apply hw; exact IsFractionRing.injective V (FractionRing V) (by rw [h, map_zero])
  have h1 := IsDedekindDomain.HeightOneSpectrum.valuation_le_one
    (IsDiscreteValuationRing.maximalIdeal V) (K := FractionRing V) w
  have h0 : valV V (algebraMap V (FractionRing V) w) ≠ 0 := valV_ne_zero hw'
  have h2 : WithZero.log (valV V (algebraMap V (FractionRing V) w)) ≤ WithZero.log (1 : WithZero (Multiplicative ℤ)) :=
    (WithZero.log_le_log h0 one_ne_zero).2 h1
  rw [WithZero.log_one] at h2
  unfold vV
  omega

theorem vV_unit (u : V) (hu : u ∉ maximalIdeal V) : vV V (algebraMap V (FractionRing V) u) = 0 := by
  have h1 : (IsDiscreteValuationRing.maximalIdeal V).valuation (FractionRing V) (algebraMap V _ u) = 1 :=
    (IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem (K := FractionRing V)
      (IsDiscreteValuationRing.maximalIdeal V)).2 hu
  unfold vV valV
  rw [h1, WithZero.log_one, neg_zero]

theorem mem_of_vV_nonneg (y : FractionRing V) (hy : y ≠ 0) (h : 0 ≤ vV V y) :
    ∃ w : V, algebraMap V (FractionRing V) w = y := by
  have h0 : valV V y ≠ 0 := valV_ne_zero hy
  have hle : valV V y ≤ 1 := by
    rw [← WithZero.log_le_log h0 one_ne_zero, WithZero.log_one]
    unfold vV at h
    omega
  obtain ⟨w, hw⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one (R := V)
    (K := FractionRing V) y (fun v => by
      have hv : v = IsDiscreteValuationRing.maximalIdeal V := by
        have hm : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
        ext1
        exact IsLocalRing.eq_maximalIdeal hm
      rw [hv]
      exact hle)
  exact ⟨w, hw⟩

theorem nval_nonneg (e : ℕ) (w : V) : 0 ≤ nval V e (algebraMap V (FractionRing V) w) := by
  by_cases hw : w = 0
  · rw [hw, map_zero, nval_zero]
    exact le_top
  · have hw' : algebraMap V (FractionRing V) w ≠ 0 := by
      intro h; apply hw; exact IsFractionRing.injective V (FractionRing V) (by rw [h, map_zero])
    rw [nval_of_ne hw']
    exact EReal.coe_nonneg.2 (div_nonneg (by exact_mod_cast vV_nonneg w hw) (Nat.cast_nonneg e))

theorem nval_unit (e : ℕ) (u : V) (hu : u ∉ maximalIdeal V) : nval V e (algebraMap V (FractionRing V) u) = 0 := by
  have hu0 : u ≠ 0 := fun h => hu (h ▸ (maximalIdeal V).zero_mem)
  have hu' : algebraMap V (FractionRing V) u ≠ 0 := by
    intro h; apply hu0; exact IsFractionRing.injective V (FractionRing V) (by rw [h, map_zero])
  rw [nval_of_ne hu', vV_unit u hu]
  simp

theorem ne_zero_map {x : V} (hx : x ≠ 0) : algebraMap V (FractionRing V) x ≠ 0 := by
  intro h; apply hx; exact IsFractionRing.injective V (FractionRing V) (by rw [h, map_zero])

variable {A : Type} [CommRing A] [IsDomain A]

theorem chval_eq (φ : A →+* V) (e : ℕ) (f : FractionRing A) (r : EReal) (h : ChV φ e f r) (a b : A)
    (hab : f * algebraMap A (FractionRing A) b = algebraMap A (FractionRing A) a) (hb : φ b ≠ 0) :
    r = nval V e (algebraMap V (FractionRing V) (φ a)) - nval V e (algebraMap V (FractionRing V) (φ b)) := by
  obtain ⟨x, s, hs, hfs, rfl⟩ := h
  have has : a * s = x * b := by
    apply IsFractionRing.injective A (FractionRing A)
    rw [map_mul, map_mul, ← hab, ← hfs]
    ring
  have hφ : φ a * φ s = φ x * φ b := by rw [← map_mul, ← map_mul, has]
  by_cases ha : φ a = 0
  · have hx : φ x = 0 := by
      rw [ha, zero_mul] at hφ
      exact (mul_eq_zero.1 hφ.symm).resolve_right hb
    rw [ha, hx, map_zero, nval_zero, nval_of_ne (ne_zero_map hs), nval_of_ne (ne_zero_map hb),
      EReal.top_sub_coe, EReal.top_sub_coe]
  · have hx : φ x ≠ 0 := by
      intro hx
      rw [hx, zero_mul] at hφ
      exact mul_ne_zero ha hs hφ
    have hv := congrArg (vV V) (congrArg (algebraMap V (FractionRing V)) hφ)
    rw [map_mul, map_mul, vV_mul (ne_zero_map ha) (ne_zero_map hs),
      vV_mul (ne_zero_map hx) (ne_zero_map hb)] at hv
    rw [nval_of_ne (ne_zero_map ha), nval_of_ne (ne_zero_map hb), nval_of_ne (ne_zero_map hx),
      nval_of_ne (ne_zero_map hs), ← EReal.coe_sub, ← EReal.coe_sub, div_sub_div_same, div_sub_div_same]
    congr 2
    have : ((vV V (algebraMap V (FractionRing V) (φ x)) : ℤ) : ℝ) -
        (vV V (algebraMap V (FractionRing V) (φ s)) : ℤ) =
        ((vV V (algebraMap V (FractionRing V) (φ a)) : ℤ) : ℝ) - (vV V (algebraMap V (FractionRing V) (φ b)) : ℤ) := by
      have : (vV V (algebraMap V (FractionRing V) (φ x)) : ℤ) - vV V (algebraMap V (FractionRing V) (φ s)) =
          vV V (algebraMap V (FractionRing V) (φ a)) - vV V (algebraMap V (FractionRing V) (φ b)) := by omega
      exact_mod_cast this
    exact this

theorem chval_div (φ : A →+* V) (e : ℕ) (he : 0 < e) (f : FractionRing A) (r : EReal) (h : ChV φ e f r)
    (hr : 0 ≤ r) (a b : A) (hab : f * algebraMap A (FractionRing A) b = algebraMap A (FractionRing A) a)
    (hb : φ b ≠ 0) : ∃ w : V, φ a = w * φ b := by
  by_cases ha : φ a = 0
  · exact ⟨0, by rw [ha, zero_mul]⟩
  rw [chval_eq φ e f r h a b hab hb, nval_of_ne (ne_zero_map ha), nval_of_ne (ne_zero_map hb),
    ← EReal.coe_sub, EReal.coe_nonneg, div_sub_div_same] at hr
  have he' : (0 : ℝ) < e := by exact_mod_cast he
  have hle : (vV V (algebraMap V (FractionRing V) (φ b)) : ℝ) ≤ vV V (algebraMap V (FractionRing V) (φ a)) := by
    have := (div_nonneg_iff.1 hr)
    rcases this with ⟨h1, -⟩ | ⟨-, h2⟩
    · linarith
    · linarith
  have hle' : vV V (algebraMap V (FractionRing V) (φ b)) ≤ vV V (algebraMap V (FractionRing V) (φ a)) := by
    exact_mod_cast hle
  set y := algebraMap V (FractionRing V) (φ a) / algebraMap V (FractionRing V) (φ b)
  have hy0 : y ≠ 0 := div_ne_zero (ne_zero_map ha) (ne_zero_map hb)
  have hyv : vV V y + vV V (algebraMap V (FractionRing V) (φ b)) = vV V (algebraMap V (FractionRing V) (φ a)) := by
    rw [← vV_mul hy0 (ne_zero_map hb), div_mul_cancel₀ _ (ne_zero_map hb)]
  obtain ⟨w, hw⟩ := mem_of_vV_nonneg y hy0 (by omega)
  refine ⟨w, IsFractionRing.injective V (FractionRing V) ?_⟩
  rw [map_mul, hw, div_mul_cancel₀ _ (ne_zero_map hb)]

theorem chval_nonneg (φ : A →+* V) (e : ℕ) (f : FractionRing A) (r : EReal) (h : ChV φ e f r) (a s : A)
    (hfs : f * algebraMap A (FractionRing A) s = algebraMap A (FractionRing A) a) (hs : φ s ∉ maximalIdeal V) :
    0 ≤ r := by
  have hs0 : φ s ≠ 0 := fun h0 => hs (h0 ▸ (maximalIdeal V).zero_mem)
  rw [chval_eq φ e f r h a s hfs hs0, nval_unit e _ hs, sub_zero]
  exact nval_nonneg e _

end Values

section Charts
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem transfer {la : HeightOneSpectrum (𝓞 c.F)}
    (S : SCharts Xo c la) (j : S.J) (g : FractionRing (S.A j)) (x : S.A j) (hx0 : x ≠ 0)
    (hpts : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra S.O V]
      [Module.Finite S.O V] (φ : S.A j →ₐ[S.O] V), φ x ≠ 0 →
        ∃ (e : ℕ) (r : EReal), 0 < e ∧ ChV φ.toRingHom e g r ∧ 0 ≤ r)
    (qq : Ideal (S.A j)) [qq.IsPrime]
    (hqq : qq ⊔ Ideal.map (algebraMap S.O (S.A j)) (maximalIdeal S.O) ≠ ⊤) :
    ∃ a s : S.A j, s ∉ qq ∧ g * algebraMap (S.A j) (FractionRing (S.A j)) s =
      algebraMap (S.A j) (FractionRing (S.A j)) a := by
  refine Formalism.L2.Pj.RegC.key_centre g x hx0 (fun V _ _ _ _ _ φ a b hab hb hφx => ?_) qq hqq
  obtain ⟨e, r, he, hr, hr0⟩ := hpts V φ hφx
  exact chval_div φ.toRingHom e he g r hr hr0 a b hab hb

theorem nonneg_at {la : HeightOneSpectrum (𝓞 c.F)}
    (S : SCharts Xo c la) {a n} {F : Rul Xo c} (hF : F ∈ sec Xo c a n)
    (h0 : ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v F) (j : S.J) (x : S.A j) (hxE : x ∈ S.Eb j)
    (hx0 : x ≠ 0) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra S.O V]
    (φ : S.A j →ₐ[S.O] V) (e : ℕ) (rr : EReal) (hch : ChV φ.toRingHom e (S.ch j F) rr)
    (hqq : (maximalIdeal V).comap φ.toRingHom ⊔ Ideal.map (algebraMap S.O (S.A j)) (maximalIdeal S.O) ≠ ⊤) :
    0 ≤ rr := by
  obtain ⟨a', s', hs', hfs'⟩ := transfer S j (S.ch j F) x hx0 (fun V _ _ _ _ _ φ hφx => by
    obtain ⟨ioV, e', hov, -, v, hv, hChV⟩ := S.pts j V φ ⟨x, hxE, hφx⟩
    exact ⟨e', v F, hov.1, hChV a n F hF, h0 v hv⟩) ((maximalIdeal V).comap φ.toRingHom) hqq
  exact chval_nonneg φ.toRingHom e (S.ch j F) rr hch a' s' hfs' hs'

theorem nonneg_at_all_points {la : HeightOneSpectrum (𝓞 c.F)}
    (S : SCharts Xo c la) {a n} {F : Rul Xo c} (hF : F ∈ sec Xo c a n)
    (h0 : ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v F) : ∀ v ∈ valSet Xo c (trivialClassCondition Xo c) la, 0 ≤ v F := by
  intro v hv
  obtain ⟨j, V, _, _, _, _, φ, ioV, e, hov, ⟨x, hxE, hφx⟩, -, hmap, hChV⟩ := S.cover v hv
  have hx0 : x ≠ 0 := fun h => hφx (by rw [h, map_zero])
  refine nonneg_at S hF h0 j x hxE hx0 V φ e (v F) (hChV a n F hF) ?_
  rw [sup_eq_left.2 hmap]
  exact (Ideal.IsPrime.ne_top inferInstance)

theorem nonneg_at_trivial {la : HeightOneSpectrum (𝓞 c.F)}
    (S : SCharts Xo c la) (hQ : S.CovQ) {a n} {F : Rul Xo c} (hF : F ∈ sec Xo c a n)
    (h0 : ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v F) : ∀ q ∈ trivSet Xo c, 0 ≤ q F := by
  intro q hq
  obtain ⟨j, V, _, _, _, _, φ, hcen, -, ⟨x, hxE, hφx⟩, hChV⟩ := hQ q hq
  have hx0 : x ≠ 0 := fun h => hφx (by rw [h, map_zero])
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S.O
  refine nonneg_at S hF h0 j x hxE hx0 V φ 1 (q F) (hChV a n F hF) ?_
  have hm : maximalIdeal S.O = Ideal.span {ϖ} := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  rw [hm, Ideal.map_span, Set.image_singleton, sup_comm]
  exact hcen ϖ hϖ

theorem qpt_mem_trivSet (q : QPt Xo c) : (fun f => ordQ Xo c q f) ∈ trivSet Xo c := by
  refine ⟨q.T, q.ι, q.y, fun a ha => ?_, rfl⟩
  obtain ⟨u, hu⟩ := q.triv a ha
  rw [← hu]
  exact vV_unit (u : q.T.V) (fun h => h u.isUnit)

end Charts

end GlobalTheory.Reg.ChartInt

namespace GlobalTheory

theorem integrality_at_trivial_valuations_of_charts :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), (∀ la : HeightOneSpectrum (𝓞 c.F), (∃ S : SCharts Xo c la, S.CovQ) ∧ ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n m : ℕ) (ws : Fin m → Rul Xo c), (∀ i, ws i ∈ sec Xo c a n) → Formalism.L2.PjFree.NoCommonZero Xo c ws → ∃ S : SCharts Xo c la, S.FamW ws ∧ S.CovQ) → ∀ C : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c), (∀ a n, C a n ≤ sec Xo c a n) → Formalism.L2.PjFree.RegularityR1Quotient Xo c C ∧ ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ C a n, ∀ la, (∀ v ∈ Formalism.L2.PjFree.valSet Xo c (Formalism.L2.PjFree.algCls Xo c) la, 0 ≤ v f) → ∀ v ∈ Formalism.L2.PjFree.valSet Xo c (Formalism.L2.PjFree.trivialClassCondition Xo c) la, 0 ≤ v f := by
  intro E _ _ _ H Dw l Xo c hS C hC
  refine ⟨?_, ?_⟩
  · rintro a n f hf ⟨la, h0⟩ q
    obtain ⟨S, hQ⟩ := (hS la).1
    exact GlobalTheory.Reg.ChartInt.nonneg_at_trivial S hQ (hC a n hf) h0 _ (GlobalTheory.Reg.ChartInt.qpt_mem_trivSet q)
  · intro a n f hf la h0
    obtain ⟨S, -⟩ := (hS la).1
    exact GlobalTheory.Reg.ChartInt.nonneg_at_all_points S (hC a n hf) h0

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.KapFgTrdeg
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg

theorem kap_fg_trdeg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), KapFG Xo c ∧ KapTrdeg Xo c Dw.dim := by
  intro E _ _ _ H Dw l Xo c
  have hs : SmoothOfRelativeDimension Dw.dim (strK (Xo := Xo) (c := c)) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) Xo.smooth
  have h := fun Z : Comp Xo c =>
    GlobalTheory.residueField_genericPoint_fg_trdeg_of_smoothOfRelativeDimension c.F (Xo.XF c) strK Dw.dim hs Z.1 Z.2
  exact ⟨fun Z => (h Z).1, fun Z => (h Z).2⟩

end GlobalTheory.Reg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.PeriodEqTriangularOrthonormal
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif GlobalTheory.FrameNorm
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.FrameNorm

theorem period_eq_triangular_orthonormal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (D : Datum H) (r : ℕ) (X : Data E r) (φ : D.La ≃ₗ[𝓞 E] X.Λ), GoodEmb c σ → D.p = Dw.p → D.q = Dw.q → r = Dw.p + Dw.q → X.p0 = Dw.q → (∀ τ : E →+* ℂ, τ ∈ X.Ψ ↔ τ (H.rt : E) = H.rt0) → (∀ a b, ((D.EF a b : ℤ) : ℚ) = Algebra.trace ℚ E (-X.ξ0 * herm X.Gm (φ a : Fin r → E) (φ b))) → (r ≠ 0 → ∀ τ ∈ X.Ψ, (τ X.ξ0).im < 0) → ∃ d : Fin g → ℝ, (∀ j, 0 < d j) ∧ ∀ P : D.La →+ (Fin g → ℂ), IsPeriod D (fun j => relab c σ (e j).1) P → ∃ x₀ ∈ X.dom, IsUnitFr X x₀ ∧ ∃ h₀ : Matrix (Fin g) (Fin g) ℂ, IsUnit h₀.det ∧ (∀ j j', h₀ j j' ≠ 0 → (e j).1 = (e j').1 ∧ ((e j).2 : ℕ) ≤ (e j').2) ∧ (∀ a j, (h₀ *ᵥ P a) j = perFr X x₀ (φ a : Fin r → E) (relab c σ (e j).1) (e j).2) ∧ ∀ a b, (hermForm (Matrix.diagonal fun j => ((d j : ℝ) : ℂ)) (h₀ *ᵥ P a) (h₀ *ᵥ P b)).im = D.EF a b := by
  intro E _ _ _ H Dw l c σ g e D r X φ hσ hp hq hr hp0 hty hef hneg
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  have hcc : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := fun τ =>
    ComplexEmbedding.involutive_conjugate E τ
  obtain ⟨f, hf⟩ := exists_letter_equiv X.Ψ X.cmType Dw.p Dw.q r hr (relab c σ) hbij Dw.mult
    (fun τ h => by unfold Datum.mult; rw [if_pos ((hrt τ).1 ((hty _).1 h))])
    (fun τ h => by unfold Datum.mult; rw [if_neg (fun h' => h ((hty _).2 ((hrt τ).2 h')))])
  obtain ⟨idx, hi⟩ : ∃ idx : Fin g ≃ X.Ψ × Fin r, ∀ j,
      (relab c σ (e j).1 ∈ X.Ψ ∧ (idx j).1.1 = relab c σ (e j).1 ∧ ((idx j).2 : ℕ) = Dw.q + (e j).2) ∨
      (relab c σ (e j).1 ∉ X.Ψ ∧ (idx j).1.1 = ComplexEmbedding.conjugate (relab c σ (e j).1) ∧
        ((idx j).2 : ℕ) = Dw.q - 1 - (e j).2 ∧ ((e j).2 : ℕ) < Dw.q) := ⟨e.trans f, fun j => hf (e j)⟩
  rcases eq_or_ne r 0 with hr0 | hr0
  · subst hr0
    haveI : IsEmpty (Fin g) := idx.isEmpty
    refine ⟨fun _ => 1, fun _ => one_pos, fun P hP => ?_⟩
    obtain ⟨hx, hu⟩ := (GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular E 0 X.p0 X.Ψ X.Gm
      X.Gm_herm).2.1 (fun _ a => a.elim0) (fun τ => Subsingleton.elim _ _)
    refine ⟨_, hx, hu, 1, by simp, fun j => isEmptyElim j, fun _ j => isEmptyElim j, fun a b => ?_⟩
    obtain ⟨-, -, -, -, Hm, -, -, hIm⟩ := hP
    rw [← hIm]
    simp [hermForm, dotProduct]
  have hpos : ∀ τ ∈ X.Ψ, 0 < (τ (-X.ξ0)).im := by
    intro τ hτ
    have := hneg hr0 τ hτ
    rw [map_neg, Complex.neg_im]
    linarith
  have hξ : cc (-X.ξ0) = -(-X.ξ0) := by
    have h := X.ξ0_im
    unfold cc at h ⊢
    rw [map_neg, h]
  have hty' : ∀ j, relab c σ (e j).1 = if ((idx j).2 : ℕ) < D.q then
      ComplexEmbedding.conjugate (idx j).1.1 else (idx j).1.1 := by
    intro j
    rw [hq]
    rcases hi j with ⟨a, b, c'⟩ | ⟨a, b, c', d⟩
    · rw [if_neg (by omega), b]
    · rw [if_pos (by omega), b, hcc]
  have hper : ∀ (x : Frame X.Ψ r) (v : Fin r → E) j, perFr X x v (relab c σ (e j).1) (e j).2 =
      if ((idx j).2 : ℕ) < D.q then
        hermC (idx j).1.1 X.Gm (col (mat x (idx j).1) (idx j).2) (Data.emb (idx j).1.1 v)
      else ((mat x (idx j).1)⁻¹ *ᵥ Data.emb (idx j).1.1 v) (idx j).2 := by
    intro x v j
    have h := hi j
    rw [hq]
    generalize idx j = t at h ⊢
    obtain ⟨⟨τ, hτ⟩, ⟨n, hn⟩⟩ := t
    dsimp only at h ⊢
    rw [← hp0] at h ⊢
    rcases h with ⟨a, rfl, rfl⟩ | ⟨a, rfl, rfl, d⟩
    · rw [if_neg (by omega)]
      unfold perFr
      rw [dif_pos a, dif_pos hn]
    · rw [if_pos (by omega)]
      unfold perFr
      rw [dif_neg a, dif_pos (show conjEmb (relab c σ (e j).1) ∈ X.Ψ from hτ), dif_pos hn]
      rfl
  let φ' : D.La →ₗ[𝓞 E] (Fin r → E) := X.Λ.subtype.comp φ.toLinearMap
  have hφ' : Function.Injective φ' ∧ Submodule.span E (Set.range φ') = ⊤ ∧
      (∀ a b, cc (X.Gm a b) = X.Gm b a) ∧ X.Gm.det ≠ 0 ∧
      ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-X.ξ0 * herm X.Gm (φ' x) (φ' y)) := by
    refine ⟨fun a b hab => φ.injective (Subtype.ext hab), ?_, X.Gm_herm, X.Gm_det, hef⟩
    have hrange : Set.range φ' = X.Λ := by
      ext y
      constructor
      · rintro ⟨a, rfl⟩
        exact (φ a).2
      · intro hy
        exact ⟨φ.symm ⟨y, hy⟩, by simp [φ']⟩
    rw [hrange]
    exact X.Λ_span
  have hinj : ∀ j j', (e j).1 = (e j').1 → ((e j).2 : ℕ) = (e j').2 → j = j' := by
    intro j j' h1 h2
    apply e.injective
    refine Sigma.ext h1 ((Fin.heq_ext_iff (by rw [h1])).2 h2)
  refine ⟨fun j => 2 * ‖(idx j).1.1 (-X.ξ0)‖, fun j => ?_, fun P hP => ?_⟩
  · have h1 := hpos _ (idx j).1.2
    have h2 : (idx j).1.1 (-X.ξ0) ≠ 0 := by
      intro h0
      rw [h0] at h1
      simp at h1
    have := norm_pos_iff.2 h2
    positivity
  obtain ⟨x, hx, hPx⟩ := GlobalTheory.exists_frame_of_isPeriod E H D r (-X.ξ0) X.Gm φ' X.Ψ hty g idx _ hty' hξ hpos hφ'
    (by rw [hp, hq, hr]) P hP
  obtain ⟨x₀, b, hb, horth, rfl⟩ :=
    (GlobalTheory.UnitFrames.frame_mul_triangular_orthonormal E r D.q X.Ψ X.Gm X.Gm_herm).1 x hx
  have hs : ∀ j j', PerBor.moveMat D.q idx b j j' ≠ 0 →
      (e j).1 = (e j').1 ∧ ((e j).2 : ℕ) ≤ (e j').2 := by
    intro j j' hne
    obtain ⟨h1, h2⟩ := PerBor.moveMat_support _ idx hb j j' hne
    have t1 := hty' j
    have t2 := hty' j'
    have c1 := hi j
    have c2 := hi j'
    by_cases hj : ((idx j).2 : ℕ) < D.q
    · rw [if_pos hj] at h2 t1
      have hj' : ((idx j').2 : ℕ) < D.q := by omega
      rw [if_pos hj'] at t2
      refine ⟨hbij.1 (by rw [t1, t2, h1]), ?_⟩
      rcases c1 with ⟨-, -, c1⟩ | ⟨-, -, c1, d1⟩ <;> rcases c2 with ⟨-, -, c2⟩ | ⟨-, -, c2, d2⟩ <;> omega
    · rw [if_neg hj] at h2 t1
      have hj' : ¬ ((idx j').2 : ℕ) < D.q := by omega
      rw [if_neg hj'] at t2
      refine ⟨hbij.1 (by rw [t1, t2, h1]), ?_⟩
      rcases c1 with ⟨-, -, c1⟩ | ⟨-, -, c1, d1⟩ <;> rcases c2 with ⟨-, -, c2⟩ | ⟨-, -, c2, d2⟩ <;> omega
  have hbne : ∀ τ i, b τ i i ≠ 0 := fun τ i => PerMove.bor_diag_ne hb τ i
  have hu : IsUnit (PerBor.moveMat D.q idx b).det := by
    rw [PerBor.det_of_support _ _ hinj _ hs, isUnit_iff_ne_zero]
    refine Finset.prod_ne_zero_iff.2 fun j _ => ?_
    rw [PerBor.moveMat_diag D.q idx hb]
    split_ifs
    · exact hbne _ _
    · exact inv_ne_zero (hbne _ _)
  have hmove : ∀ a j, (PerBor.moveMat D.q idx b *ᵥ P a) j = if ((idx j).2 : ℕ) < D.q then
      hermC (idx j).1.1 X.Gm (col (mat (rmul x b) (idx j).1) (idx j).2) (Data.emb (idx j).1.1 (φ' a))
      else ((mat (rmul x b) (idx j).1)⁻¹ *ᵥ Data.emb (idx j).1.1 (φ' a)) (idx j).2 := fun a j =>
    (congrFun (PerBor.moveMat_mulVec D.q idx hb X.Gm x (φ' a) (P a) _ (hPx a) (fun _ => rfl)) j).symm
  have hqq : D.q = X.p0 := hq.trans hp0.symm
  obtain ⟨hx₀, hu₀⟩ := (GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular E r X.p0 X.Ψ X.Gm
    X.Gm_herm).2.1 (rmul x b) (hqq ▸ horth)
  refine ⟨rmul x b, hx₀, hu₀, PerBor.moveMat D.q idx b, hu, hs, fun a j => ?_, fun a a' => ?_⟩
  · rw [hper, hmove]
    rfl
  · exact GlobalTheory.UnitFrame.im_hermForm_eq E H D r (-X.ξ0) X.Gm φ' X.Ψ hty g idx _ hty' hξ hpos hφ' (rmul x b)
      ((Matrix.mulVecLin (PerBor.moveMat D.q idx b)).toAddMonoidHom.comp P) hmove horth a a'

end GlobalTheory.FrameNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.SpanEvalEqTopOfNoCommonZeroReducedStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_eval_eq_top_of_noCommonZero_reduced : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n m : ℕ) (ws : Fin m → Rul Xo c), (∀ i, ws i ∈ sec Xo c a n) → Formalism.L2.PjFree.NoCommonZero Xo c ws → ∀ (S : Type) [CommRing S] [IsReduced S] [Algebra c.F S] (y : FrPt Xo c S), Ideal.span (Set.range fun i => evR Xo c (ws i) y) = ⊤ := by
  first | exact @GlobalTheory.Reg.span_evR_eq_top_of_noCommonZero | exact GlobalTheory.Reg.span_evR_eq_top_of_noCommonZero | (intros; apply GlobalTheory.Reg.span_evR_eq_top_of_noCommonZero <;> assumption)
end

