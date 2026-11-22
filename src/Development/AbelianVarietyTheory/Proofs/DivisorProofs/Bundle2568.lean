import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1522
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0359
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2493
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2549
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2545
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2523
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2455

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CarryingSectionIntegralFrame
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt

namespace GlobalTheory.CovMult

open GlobalTheory.SlopeRec GlobalTheory.FlatLine GlobalTheory.RefSum

section Places

variable {K : Type} [Field K] [NumberField K]

theorem exists_prime_mem (la : HeightOneSpectrum (𝓞 K)) : ∃ q : ℕ, q.Prime ∧ (q : 𝓞 K) ∈ la.asIdeal := by
  have h0 : Ideal.absNorm la.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact la.ne_bot
  have key : ∀ n : ℕ, n ≠ 0 → (n : 𝓞 K) ∈ la.asIdeal → ∃ q : ℕ, q.Prime ∧ (q : 𝓞 K) ∈ la.asIdeal := by
    intro n
    induction n using Nat.recOnMul with
    | zero => exact fun h => absurd rfl h
    | one => exact fun _ h => absurd ((Ideal.eq_top_iff_one _).2 (by simpa using h)) la.isPrime.ne_top
    | prime p hp => exact fun _ h => ⟨p, hp, h⟩
    | mul a b ha hb =>
      intro h hm
      rw [Nat.cast_mul] at hm
      exact (la.isPrime.mem_or_mem hm).elim (ha (left_ne_zero_of_mul h)) (hb (right_ne_zero_of_mul h))
  exact key _ h0 (Ideal.absNorm_mem _)

theorem vLa_nat_nonneg (la : HeightOneSpectrum (𝓞 K)) {n : ℕ} (hn : n ≠ 0) : 0 ≤ vLa la (n : K) := by
  have := vAdd_int_nonneg la (a := (n : 𝓞 K)) (by simpa using hn)
  simpa [vLa, Formalism.BasicNotions.vAdd] using this

theorem vLa_pos {la : HeightOneSpectrum (𝓞 K)} {q : ℕ} (hq : q ≠ 0) (h : (q : 𝓞 K) ∈ la.asIdeal) :
    0 < vLa la (q : K) := by
  have h1 : la.valuation K (q : K) < 1 := by
    have := (la.valuation_lt_one_iff_mem (K := K) (q : 𝓞 K)).2 h
    simpa using this
  have h0 : la.valuation K (q : K) ≠ 0 := (Valuation.ne_zero_iff _).2 (Nat.cast_ne_zero.2 hq)
  unfold vLa
  rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
  omega

theorem exists_spread {S : Finset ℕ} {a : ℕ → ℝ} {s : ℝ} (h : PrimeSum S a s) (e : HeightOneSpectrum (𝓞 K) →₀ ℝ)
    (t : (K →+* ℂ) → ℝ) : ∃ e' : HeightOneSpectrum (𝓞 K) →₀ ℝ, cost e' t ≤ cost e t + s ∧
      ∀ (la : HeightOneSpectrum (𝓞 K)) (q : ℕ), e la + (vLa la (q : K) : ℝ) * a q ≤ e' la := by
  classical
  obtain ⟨hp, h0, hS, hs⟩ := h
  have one : ∀ (q : ℕ), q ≠ 0 → ∀ (b : ℝ) (e : HeightOneSpectrum (𝓞 K) →₀ ℝ), ∃ e' : HeightOneSpectrum (𝓞 K) →₀ ℝ,
      cost e' t = cost e t + b * Real.log q ∧ ∀ la, e' la = e la + (vLa la (q : K) : ℝ) * b := by
    intro q hq b e
    have hf := fin_mul (finite_vAdd (K := K) (a := q) (Nat.cast_ne_zero.2 hq)) fun _ => b
    refine ⟨e + Finsupp.ofSupportFinite _ hf, ?_, fun la => rfl⟩
    have h1 := sum_vAdd_nat (K := K) hq
    have h2 : ((Finsupp.ofSupportFinite _ hf).sum fun la a => a * Real.log (Ideal.absNorm la.asIdeal : ℝ)) /
        (Module.finrank ℚ K : ℝ) = b * Real.log q := by
      rw [← h1, mul_finsum, Finsupp.sum, Finset.sum_div, finsum_eq_sum_of_support_subset (s := (Finsupp.ofSupportFinite _ hf).support)]
      · refine Finset.sum_congr rfl fun la _ => ?_
        simp only [Finsupp.ofSupportFinite_coe, lw]; ring
      · intro la hla
        simp only [Finset.mem_coe, Finsupp.mem_support_iff, Finsupp.ofSupportFinite_coe]
        intro h
        apply hla
        simp only
        rw [← mul_assoc, mul_comm b, h, zero_mul]
    rw [cost, cost, Finsupp.sum_add_index' (by simp) (fun _ _ _ => add_mul _ _ _), ← h2]
    ring
  have all : ∀ T : Finset ℕ, (∀ q ∈ T, q ≠ 0) → ∃ e' : HeightOneSpectrum (𝓞 K) →₀ ℝ,
      cost e' t = cost e t + ∑ q ∈ T, a q * Real.log q ∧ ∀ la, e' la = e la + ∑ q ∈ T, (vLa la (q : K) : ℝ) * a q := by
    intro T
    induction T using Finset.induction_on with
    | empty => exact fun _ => ⟨e, by simp, by simp⟩
    | insert q T hq ih =>
      intro hT
      obtain ⟨e₁, h1, h2⟩ := ih fun r hr => hT r (Finset.mem_insert_of_mem hr)
      obtain ⟨e₂, h3, h4⟩ := one q (hT q (Finset.mem_insert_self _ _)) (a q) e₁
      exact ⟨e₂, by rw [h3, h1, Finset.sum_insert hq]; ring, fun la => by rw [h4, h2, Finset.sum_insert hq]; ring⟩
  obtain ⟨e', h1, h2⟩ := all S fun q hq => (hp q hq).ne_zero
  have hn : ∀ la, ∀ q ∈ S, 0 ≤ (vLa la (q : K) : ℝ) * a q := fun la q hq =>
    mul_nonneg (by exact_mod_cast vLa_nat_nonneg la (hp q hq).ne_zero) (h0 q)
  refine ⟨e', by linarith, fun la q => ?_⟩
  rw [h2]
  by_cases hq : q ∈ S
  · exact add_le_add_right (Finset.single_le_sum (hn la) hq) _
  · rw [hS q hq, mul_zero]
    exact add_le_add_right (Finset.sum_nonneg (hn la)) _

end Places

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r}

theorem depthOn_le (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) {cst a : ℝ} {G : WTZ E} {q : ℕ} (hq : q ≠ 0)
    (ha : refExp_vp U cst G q ≤ (a : EReal)) {la : HeightOneSpectrum (𝓞 c.F)} (hla : (q : 𝓞 c.F) ∈ la.asIdeal)
    {T : CDVR} {io : c.F →+* T.Fr} {e : ℕ} (ho : OverLa la T.V io e) {y : IntFr Xo c T io} (hy : y.IsAlg)
    {φ : ℝ} (hφ : HasPhi y φ) {Z : Comp Xo c} (hZ : letI := io.toAlgebra; LiesOn Z y.1) :
    depthOn U Z G (fun f => nval T.V e (evI y f)) ≤ (((vLa la (q : c.F) : ℝ) * a + cst * φ / e : ℝ) : EReal) := by
  letI := io.toAlgebra
  have hb := (refExp_vp_le_iff U).1 ha ⟨la, hla⟩ T io e ho y hy φ hφ
  rw [← EReal.coe_add] at hb
  have hm := vLa_pos hq hla
  have hv : vV T.V (q : T.Fr) = e * vLa la (q : c.F) := by rw [← ho.2, map_natCast]
  have hm' : (0 : ℝ) < vLa la (q : c.F) := by exact_mod_cast hm
  have he : (0 : ℝ) < e := by exact_mod_cast ho.1
  have hn : (((vV T.V (q : T.Fr)).toNat : ℕ) : ℝ) = e * vLa la (q : c.F) := by
    have : (((vV T.V (q : T.Fr)).toNat : ℕ) : ℤ) = e * vLa la (q : c.F) := by
      rw [← hv, Int.toNat_of_nonneg (hv ▸ mul_nonneg (Nat.cast_nonneg _) hm.le)]
    exact_mod_cast this
  refine le_of_forall_gt_imp_ge_of_dense fun b hb' => ?_
  induction b using EReal.rec with
  | bot => exact absurd hb' not_lt_bot
  | top => exact le_top
  | coe b =>
    have hb1 := EReal.coe_lt_coe_iff.1 hb'
    have hlt : depthAt_vp U G q y < ((b / vLa la (q : c.F) : ℝ) : EReal) := by
      refine hb.trans_lt (EReal.coe_lt_coe_iff.2 ?_)
      rw [lt_div_iff₀ hm', hv]
      refine lt_of_eq_of_lt ?_ hb1
      push_cast; field_simp
    unfold depthAt_vp depth_vw at hlt
    obtain ⟨w, hw⟩ := iInf_lt_iff.1 hlt
    obtain ⟨hwl, hw⟩ := iInf_lt_iff.1 hw
    have hne : evI y (w : Rul Xo c) ≠ 0 := fun h0 => by
      simp only [h0, nval_zero] at hw
      exact not_top_lt hw
    obtain ⟨g, hg, hgl⟩ := GlobalTheory.CompRestr.exists_cuspOn_restrict E H Dw l Xo c r U hU Z _ w
    have hev : evI y (g : Rul Xo c) = evI y (w : Rul Xo c) := hg T.Fr y.1 hZ
    refine (iInf₂_le g (hgl hwl)).trans ?_
    simp only [nval_of_ne hne] at hw
    beta_reduce
    rw [hev, nval_of_ne hne, EReal.coe_le_coe_iff]
    have h2 := EReal.coe_lt_coe_iff.1 hw
    rw [hn, ← div_div, div_lt_div_iff_of_pos_right hm'] at h2
    exact h2.le

theorem exists_bound (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) {a : ℕ → ℝ} {G : WTZ E}
    (ha : ∀ q : ℕ, q.Prime → refExp_vp U (1 / 2500) G q ≤ (a q : EReal)) {Z : Comp Xo c} {θ : Rul Xo c} {w : Ix Dw → ℤ}
    (hθ : θ ∈ secZ Xo c w) {e e' : HeightOneSpectrum (𝓞 c.F) →₀ ℝ}
    (he : ∀ (la : HeightOneSpectrum (𝓞 c.F)) (q : ℕ), e la + (vLa la (q : c.F) : ℝ) * a q ≤ e' la)
    (hk : ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e₀ : ℕ), OverLa la T.V io e₀ →
      ∀ y : IntFr Xo c T io, y.IsAlg → (∃ (G' : WTZ E), ∃ f ∈ cuspOn U Z G', evI y f ≠ 0) → ∀ φ : ℝ, HasPhi y φ →
        ((8 / 2500 * φ / e₀ - 8 * e la : ℝ) : EReal) ≤ nval T.V e₀ (evI y θ))
    {la : HeightOneSpectrum (𝓞 c.F)} {v : Rul Xo c → EReal} (hv : v ∈ (recVals Xo c).1 la) {G' : WTZ E} {f : Rul Xo c}
    (hf : f ∈ cuspOn U Z G') (hf0 : v f ≠ ⊤) :
    ∃ B : ℝ, depthOn U Z G v ≤ (B : EReal) ∧ ((8 * B - 8 * e' la : ℝ) : EReal) ≤ v θ := by
  obtain ⟨⟨_, T, io, e₀, ho, y, hy, η, hη, rfl⟩, rfl⟩ := hv
  obtain ⟨T', i, e₁, y', φ, -, ho', hy', hφ, -, hv⟩ := exists_ext_hasPhi ho y hy
  obtain ⟨q, hq, hla⟩ := exists_prime_mem la
  have hf1 : evI y' f ≠ 0 := fun h => hf0 (by
    show nval T.V e₀ (evI y f) = ⊤
    rw [← (hv f hf.1.1.1).2, h, nval_zero])
  letI := (i.comp io).toAlgebra
  have hZ : LiesOn Z y'.1 := by
    by_contra h
    exact hf1 (hf.2 _ _ ((liesOff_iff Z y'.1).2 h))
  refine ⟨_, le_trans (le_of_eq ?_) (depthOn_le hU hq.ne_zero (ha q hq) hla ho' hy' hφ hZ), ?_⟩
  · exact iInf_congr fun g => iInf_congr fun _ => (hv g g.2.1.1.1).2.symm
  · refine le_trans (EReal.coe_le_coe_iff.2 ?_) ((hk la T' _ e₁ ho' y' hy' ⟨G', f, hf, hf1⟩ φ hφ).trans_eq (hv θ hθ.1).2)
    have := he la q
    have e2 : 8 / 2500 * φ / e₁ = 8 * (1 / 2500 * φ / e₁) := by ring
    linarith

theorem mult_of (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) {x : ℝ} {D : D7} {V : (c.F →+* ℂ) → HSp D}
    {dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r} {u u' : AllWt.Weight Dw} {S : Finset ℕ} {a : ℕ → ℝ} {s cc : ℝ}
    (hS : PrimeSum S a s) (ha : ∀ q : ℕ, q.Prime → refExp_vp U (1 / 2500) (wtOf Dw u 0) q ≤ (a q : EReal)) {Z : Comp Xo c}
    (hZ : ∃ (θ : Rul Xo c) (e : HeightOneSpectrum (𝓞 c.F) →₀ ℝ) (t : (c.F →+* ℂ) → ℝ), Carries U Z u u' θ ∧
      (∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e₀ : ℕ), OverLa la T.V io e₀ →
        ∀ y : IntFr Xo c T io, y.IsAlg → (∃ (G' : WTZ E), ∃ f ∈ cuspOn U Z G', evI y f ≠ 0) → ∀ φ : ℝ, HasPhi y φ →
          ((8 / 2500 * φ / e₀ - 8 * e la : ℝ) : EReal) ≤ nval T.V e₀ (evI y θ)) ∧
      InfBd U x V dict Z (wtOf Dw u 0) (wtOf Dw ((8 : ℤ) • (u - u')) 0) 8 θ t ∧ cost e t ≤ cc) :
    Mult U x V dict Z u u' (cc + s) := by
  obtain ⟨θ, e, t, hC, hk, hI, hco⟩ := hZ
  obtain ⟨e', he', he⟩ := exists_spread hS e t
  have key := fun la v hv G' f hf hf0 => exists_bound hU ha hC.1 he hk (la := la) (v := v) hv (G' := G') (f := f) hf hf0
  refine ⟨fun la v hv G' f hf hf0 => ?_, θ, e', t, hC, fun la v hv ⟨w, _, hw⟩ => ?_, hI, by linarith⟩
  · obtain ⟨B, hB, -⟩ := key la v hv G' f hf hf0
    by_contra hn
    push Not at hn
    exact EReal.coe_ne_top B (top_le_iff.1 ((le_iInf₂ fun w hw => (hn w hw).ge).trans hB))
  · obtain ⟨B, hB, hB'⟩ := key la v hv _ w w.2 hw
    calc _ ≤ ((8 : ℕ) : EReal) * (B : EReal) := mul_le_mul_of_nonneg_left hB (by exact_mod_cast Nat.zero_le 8)
      _ = ((8 * B - 8 * e' la : ℝ) : EReal) + ((((8 : ℕ) : ℝ) * e' la : ℝ) : EReal) := by
        rw [← EReal.coe_add, ← EReal.coe_natCast, ← EReal.coe_mul]; congr 1; push_cast; ring
      _ ≤ _ := add_le_add_left hB' _

theorem budget_add {T a b C₁ C₂ u : ℝ} (h₁ : T * b ≤ C₁ * u) (h₂ : T * a ≤ C₂ * u) : T * (a + b) ≤ (C₁ + C₂) * u := by
  linarith

theorem multC_of_refW : GlobalTheory.RefSum.RefW → (Covers fun Fm x _ ι p i Y PP C => ∀ u1, Quo p i PP u1 → ∃ cc : ℝ, 0 ≤ cc ∧ lenT p i PP * cc ≤ C * unitE p ∧ ∀ Z : Comp Y.d.Xo₂ Y.d.c₂, ∃ (θ : Rul Y.d.Xo₂ Y.d.c₂) (e : HeightOneSpectrum (𝓞 Y.d.c₂.F) →₀ ℝ) (t : (Y.d.c₂.F →+* ℂ) → ℝ), Carries Y.U Z u1 (uPrime (dat p i) u1) θ ∧ (∀ (la : HeightOneSpectrum (𝓞 Y.d.c₂.F)) (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (e₀ : ℕ), OverLa la T.V io e₀ → ∀ y : IntFr Y.d.Xo₂ Y.d.c₂ T io, y.IsAlg → (∃ (G' : WTZ (Fm.D x ι).host.E), ∃ f ∈ cuspOn Y.U Z G', evI y f ≠ 0) → ∀ φ : ℝ, GlobalTheory.SlopeRec.HasPhi y φ → ((8 / 2500 * φ / e₀ - 8 * e la : ℝ) : EReal) ≤ nval T.V e₀ (evI y θ)) ∧ InfBd Y.U (xiR (Fm.D x ι)) (fun _ => (Fm.D x ι).sp.W ((i : ℕ) + 1)) Y.dict Z (wtOf (dat p i) u1 0) (wtOf (dat p i) ((8 : ℤ) • (u1 - uPrime (dat p i) u1)) 0) 8 θ t ∧ cost e t ≤ cc) → MultC := by
  intro hR hK
  refine Closed.imp (Closed.and hR hK) fun _ _ _ ⟨⟨C₁, h₁, hR⟩, C₂, h₂, hK⟩ => ⟨C₁ + C₂, add_nonneg h₁ h₂, ?_⟩
  refine (hR.and hK).imp fun _ h x hx hle ι p hp i hi Y hY u1 hu => ?_
  obtain ⟨hR, hK⟩ := h x hx hle ι p hp
  obtain ⟨S, a, s, hS, hs, ha⟩ := hR i hi Y hY u1 hu
  obtain ⟨cc, hc0, hc, hZ⟩ := hK i hi Y hY u1 hu
  have hs0 : 0 ≤ s := (Finset.sum_nonneg fun q _ => mul_nonneg (hS.2.1 q) (Real.log_natCast_nonneg q)).trans hS.2.2.2
  exact ⟨cc + s, add_nonneg hc0 hs0, budget_add hs hc, fun Z => mult_of hY.1.unf hS ha (hZ Z)⟩

end GlobalTheory.CovMult

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierSectionsFlatBaseChangeLinearlyDisjoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
open TensorProduct

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.SecFlatBC

section Helpers

variable {R₁ F₁ : Type} [CommRing R₁] [CommRing F₁]

theorem zero_mem_spanBy (c : R₁ →+* F₁) (T : Set F₁) : (0 : F₁) ∈ spanBy c T :=
  ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, by simp⟩

theorem add_mem_spanBy (c : R₁ →+* F₁) (T : Set F₁) {a b : F₁} (ha : a ∈ spanBy c T) (hb : b ∈ spanBy c T) :
    a + b ∈ spanBy c T := by
  obtain ⟨n, r, t, ht, rfl⟩ := ha
  obtain ⟨m, r', t', ht', rfl⟩ := hb
  refine ⟨n + m, Fin.append r r', Fin.append t t', fun i => ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa using ht i
    · simpa using ht' i
  · rw [Fin.sum_univ_add]; simp

theorem spanBy_mul (c : R₁ →+* F₁) (T : Set F₁) (w : F₁) :
    spanBy c ((w * ·) '' T) = (w * ·) '' spanBy c T := by
  ext v; constructor
  · rintro ⟨n, r, t, ht, rfl⟩
    choose s hs e using ht
    refine ⟨∑ i, c (r i) * s i, ⟨n, r, s, hs, rfl⟩, ?_⟩
    dsimp only
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [← e i]; ring
  · rintro ⟨_, ⟨n, r, t, ht, rfl⟩, rfl⟩
    refine ⟨n, r, fun i => w * t i, fun i => ⟨_, ht i, rfl⟩, ?_⟩
    dsimp only
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

end Helpers

theorem fnOf_algX {R : Type} [CommRing R] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp R) (U : X.Opens)
    (hg : genericPoint X ∈ U) (a : R) :
    GlobalTheory.Cartier.fnOf U hg (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U a) = GlobalTheory.Desc.cst p a := by
  simp only [ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX, GlobalTheory.Desc.cst, RingHom.comp_apply]
  have := X.presheaf.germ_res_apply (homOfLE (show U ≤ p ⁻¹ᵁ ⊤ from le_top)) (genericPoint X) hg
    ((p.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
  exact this

theorem span_chart {R R₁ : Type} [CommRing R] [CommRing R₁] {ρ : R →+* R₁} {X Y V : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] {p : X ⟶ Sp R} {q : Y ⟶ Sp R₁} {i : V ⟶ Y} [IsOpenImmersion i] {φ : V ⟶ X}
    {θ : X.functionField →+* Y.functionField} (H : IsPullback φ (i ≫ q) p (spMap ρ)) (hP : PFF i φ θ)
    {U : X.Opens} (hU : IsAffineOpen U) (hg : genericPoint X ∈ U) :
    spanBy (GlobalTheory.Desc.cst q) (θ '' Set.range (GlobalTheory.Cartier.fnOf U hg)) =
      {v | ∀ z : V, φ z ∈ U → GlobalTheory.Cartier.RegAt (i z) v} := by
  letI := (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U).toAlgebra
  letI := ρ.toAlgebra
  obtain ⟨β, -, hβ, hr⟩ := GlobalTheory.T.exists_tensor_sections_embed_functionField_regular R R₁ ρ X Y V p q i φ θ H hP U hU hg
  rw [← hr]
  ext v; constructor
  · rintro ⟨n, r, t, ht, rfl⟩
    choose a ha e using ht
    choose b hb using ha
    refine ⟨∑ j, b j ⊗ₜ[R] r j, ?_⟩
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [hβ, hb, e, _root_.mul_comm]
  · rintro ⟨x, rfl⟩
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact zero_mem_spanBy _ _
    | tmul b r =>
      refine ⟨1, fun _ => r, fun _ => θ (GlobalTheory.Cartier.fnOf U hg b), fun _ => ⟨_, ⟨b, rfl⟩, rfl⟩, ?_⟩
      rw [hβ, Fin.sum_univ_one, _root_.mul_comm]
    | add x y hx hy => rw [map_add]; exact add_mem_spanBy _ _ hx hy

theorem sections_linDisj_flatBaseChange : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] (ρ : R →+* R₁), ρ.Flat → ∀ (X Y V : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp R) (q : Y ⟶ Sp R₁) (i : V ⟶ Y) [IsOpenImmersion i] (φ : V ⟶ X) (θ : X.functionField →+* Y.functionField), QuasiCompact p → QuasiSeparated p → IsPullback φ (i ≫ q) p (spMap ρ) → PFF i φ θ → ∀ (D : CartierDiv X) (D₁ : CartierDiv Y), PPull i φ θ D D₁ → LinDisj (GlobalTheory.Desc.cst p) (GlobalTheory.Desc.cst q) θ ∧ ∀ k : ℕ, {v | ∀ z : V, (k • D₁).RegularAt (i z) v} = spanBy (GlobalTheory.Desc.cst q) (θ '' Sec D k) := by
  intro R R₁ _ _ ρ hρ X Y V _ _ p q i _ φ θ _ _ H hP D D₁ hD
  letI : Algebra R X.functionField := (GlobalTheory.Desc.cst p).toAlgebra
  letI : Algebra R R₁ := ρ.toAlgebra
  haveI : Module.Flat R R₁ := hρ
  obtain ⟨U₀, hU₀, hg₀, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
    (show genericPoint X ∈ (⊤ : X.Opens) from trivial)
  have hc : ∀ a : R, θ (algebraMap R X.functionField a) = GlobalTheory.Desc.cst q (algebraMap R R₁ a) := by
    intro a
    letI := (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U₀).toAlgebra
    obtain ⟨β, -, hβ, -⟩ := GlobalTheory.T.exists_tensor_sections_embed_functionField_regular R R₁ ρ X Y V p q i φ θ H hP U₀ hU₀ hg₀
    have e : (algebraMap R Γ(X, U₀) a) ⊗ₜ[R] (1 : R₁) = (1 : Γ(X, U₀)) ⊗ₜ[R] (algebraMap R R₁ a) := by
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one a, TensorProduct.smul_tmul]
    have e' := congrArg β e
    simp only [hβ, _root_.map_one, _root_.mul_one, _root_.one_mul] at e'
    rw [← e']
    exact congrArg θ (fnOf_algX p U₀ hg₀ a).symm
  have hinj : ∀ (n : ℕ) (u : Fin n → X.functionField) (r : Fin n → R₁),
      ∑ j, GlobalTheory.Desc.cst q (r j) * θ (u j) = 0 → ∑ j, u j ⊗ₜ[R] r j = 0 := by
    letI := (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U₀).toAlgebra
    haveI : Nonempty U₀ := ⟨⟨_, hg₀⟩⟩
    haveI : IsFractionRing Γ(X, U₀) X.functionField := functionField_isFractionRing_of_isAffineOpen X U₀ hU₀
    have hal : ∀ b, algebraMap Γ(X, U₀) X.functionField b = GlobalTheory.Cartier.fnOf U₀ hg₀ b := fun b => rfl
    haveI : IsScalarTower R Γ(X, U₀) X.functionField :=
      IsScalarTower.of_algebraMap_eq fun a => ((hal _).trans (fnOf_algX p U₀ hg₀ a)).symm
    obtain ⟨β, hβi, hβ, -⟩ := GlobalTheory.T.exists_tensor_sections_embed_functionField_regular R R₁ ρ X Y V p q i φ θ H hP U₀ hU₀ hg₀
    exact GlobalTheory.T.tensor_fraction_injective_of_tensor_injective R R₁ Γ(X, U₀) X.functionField Y.functionField θ (GlobalTheory.Desc.cst q) β hβi
      (fun b r => (hβ b r).trans (by rw [hal]))
  refine ⟨GlobalTheory.T.linearlyDisjoint_of_flat_baseChange_embeds R R₁ X.functionField Y.functionField θ (GlobalTheory.Desc.cst q) hinj, fun k => ?_⟩
  have hloc : ∀ x : X, ∃ (U : X.Opens) (g : X.functionFieldˣ), IsAffineOpen U ∧ x ∈ U ∧ ∀ y ∈ U, D.IsEqn y g := by
    intro x
    obtain ⟨W, hxW, g, hg⟩ := D.exists_isEqn_nhds x
    obtain ⟨U, hU, hxU, hUW⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens hxW
    exact ⟨U, g, hU, hxU, fun y hy => hg y (hUW hy)⟩
  choose U g hUa hxU hUg using hloc
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (U x : Set X)) (fun x => (U x).isOpen)
    (fun x _ => Set.mem_iUnion.2 ⟨x, hxU x⟩)
  have cov : ∀ y : X, ∃ j : t, y ∈ U j.1 := fun y => by
    obtain ⟨a, ha, h⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
    exact ⟨⟨a, ha⟩, h⟩
  haveI : Nonempty t := ⟨(cov (genericPoint X)).choose⟩
  have hgen : ∀ j : t, genericPoint X ∈ U j.1 := fun j => GlobalTheory.Cartier.gen_mem (hxU j.1)
  let N : t → Submodule R X.functionField := fun j =>
    { carrier := {u | ∀ y ∈ U j.1, (k • D).RegularAt y u}
      add_mem' := fun ha hb y hy => (ha y hy).add (hb y hy)
      zero_mem' := fun y _ => ((k • D).vanishesAt_zero y).regularAt
      smul_mem' := fun a u hu y hy => by
        rw [Algebra.smul_def]
        exact (hu y hy).regAt_mul (GlobalTheory.Cartier.regAt_fnOf (U := ⊤) trivial trivial _) }
  have hSec : Sec D k = ⋂ j, (N j : Set X.functionField) := by
    ext u; rw [Set.mem_iInter]
    exact ⟨fun h j y _ => h y, fun h y => let ⟨j, hj⟩ := cov y; h j y hj⟩
  have hG : ∀ j : t, ∀ z : V, φ z ∈ U j.1 →
      (k • D₁).IsEqn (i z) (Units.map θ.toMonoidHom (g j.1 ^ k)) := by
    intro j z hz
    rw [map_pow]
    exact (hD z _ (hUg j.1 _ hz)).nsmul k
  have hN : ∀ j : t, (N j : Set X.functionField) =
      ((((g j.1 ^ k : X.functionFieldˣ) : X.functionField)⁻¹ * ·) '' Set.range (GlobalTheory.Cartier.fnOf (U j.1) (hgen j))) := by
    intro j; ext u; constructor
    · intro hu
      have hreg : ∀ y ∈ U j.1, GlobalTheory.Cartier.RegAt y (u * ((g j.1 ^ k : X.functionFieldˣ) : X.functionField)) :=
        fun y hy => ((hUg j.1 y hy).nsmul k).regularAt_iff.1 (hu y hy)
      obtain ⟨b, hb⟩ := GlobalTheory.Cartier.exists_fnOf_eq (hgen j) hreg
      exact ⟨_, ⟨b, rfl⟩, by dsimp only; rw [hb, _root_.mul_comm u, ← _root_.mul_assoc, inv_mul_cancel₀ (Units.ne_zero _), _root_.one_mul]⟩
    · rintro ⟨_, ⟨b, rfl⟩, rfl⟩ y hy
      dsimp only
      rw [((hUg j.1 y hy).nsmul k).regularAt_iff, _root_.mul_comm _ ((g j.1 ^ k : X.functionFieldˣ) : X.functionField),
        ← _root_.mul_assoc, mul_inv_cancel₀ (Units.ne_zero _), _root_.one_mul]
      exact GlobalTheory.Cartier.regAt_fnOf hy (hgen j) b
  have hspan : ∀ j : t, spanBy (GlobalTheory.Desc.cst q) (θ '' (N j : Set X.functionField)) =
      {v | ∀ z : V, φ z ∈ U j.1 → (k • D₁).RegularAt (i z) v} := by
    intro j
    set G : X.functionField := ((g j.1 ^ k : X.functionFieldˣ) : X.functionField) with hGdef
    have himg : θ '' ((G⁻¹ * ·) '' Set.range (GlobalTheory.Cartier.fnOf (U j.1) (hgen j))) =
        (θ G⁻¹ * ·) '' (θ '' Set.range (GlobalTheory.Cartier.fnOf (U j.1) (hgen j))) := by
      rw [Set.image_image, Set.image_image]; simp only [map_mul]
    rw [hN j, himg, spanBy_mul, span_chart H hP (hUa j.1) (hgen j)]
    have hGne : G ≠ 0 := Units.ne_zero _
    have hθG : θ G ≠ 0 := (map_ne_zero θ).2 hGne
    have hval : ∀ z : V, (((Units.map θ.toMonoidHom (g j.1 ^ k)) : Y.functionFieldˣ) : Y.functionField) = θ G :=
      fun _ => rfl
    ext v; constructor
    · rintro ⟨w, hw, rfl⟩ z hz
      rw [(hG j z hz).regularAt_iff, hval z, map_inv₀, _root_.mul_comm, ← _root_.mul_assoc, mul_inv_cancel₀ hθG, _root_.one_mul]
      exact hw z hz
    · intro hv
      refine ⟨v * θ G, fun z hz => ?_, ?_⟩
      · have := (hG j z hz).regularAt_iff.1 (hv z hz)
        rwa [hval z] at this
      · show θ G⁻¹ * (v * θ G) = v
        rw [map_inv₀, _root_.mul_comm, _root_.mul_assoc, mul_inv_cancel₀ hθG, _root_.mul_one]
  have hT : {v | ∀ z : V, (k • D₁).RegularAt (i z) v} =
      ⋂ j : t, {v | ∀ z : V, φ z ∈ U j.1 → (k • D₁).RegularAt (i z) v} := by
    ext v; rw [Set.mem_iInter]
    exact ⟨fun h j z _ => h z, fun h z => let ⟨j, hj⟩ := cov (φ z); h j z hj⟩
  rw [hT, hSec, GlobalTheory.T.span_iInter_submodules_of_flat_baseChange R R₁ X.functionField Y.functionField θ (GlobalTheory.Desc.cst q) hc hinj t N]
  exact Set.iInter_congr fun j => (hspan j).symm

end GlobalTheory.SecFlatBC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPairRestrictBaseChangeBijective
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs.PairExt

variable {X X' Y : Scheme.{0}}

theorem pair_point (φ : X' ⟶ X) (x : X') (U : X'.Opens) (hx : x ∈ U) :
    ∃ t : (Pair φ)ᵒᵖ, x ∈ ((pairFst φ).obj t).unop.1 ∧ ((pairFst φ).obj t).unop.1 ≤ U := by
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (x := φ.base x) (U := (⊤ : X.Opens)) trivial
  obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := U ⊓ φ ⁻¹ᵁ V) ⟨hx, hxV⟩
  exact ⟨Opposite.op ⟨(⟨W, hW⟩, ⟨V, hV⟩), fun y hy ↦ (hWU hy).2⟩, hxW, fun y hy ↦ (hWU hy).1⟩

theorem pair_point_two (φ : X' ⟶ X) (t₁ t₂ : (Pair φ)ᵒᵖ) (x : X') (U : X'.Opens) (hx : x ∈ U)
    (h₁ : x ∈ ((pairFst φ).obj t₁).unop.1) (h₂ : x ∈ ((pairFst φ).obj t₂).unop.1) :
    ∃ t₃ : (Pair φ)ᵒᵖ, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ x ∈ ((pairFst φ).obj t₃).unop.1 ∧
      ((pairFst φ).obj t₃).unop.1 ≤ U := by
  have h₁' : x ∈ t₁.unop.1.1.1 := h₁
  have h₂' : x ∈ t₂.unop.1.1.1 := h₂
  obtain ⟨V, hV, hxV, hVV⟩ := exists_isAffineOpen_mem_and_subset (x := φ.base x)
    (U := t₁.unop.1.2.1 ⊓ t₂.unop.1.2.1) ⟨t₁.unop.2 h₁', t₂.unop.2 h₂'⟩
  obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset (x := x)
    (U := U ⊓ φ ⁻¹ᵁ V ⊓ (t₁.unop.1.1.1 ⊓ t₂.unop.1.1.1)) ⟨⟨hx, hxV⟩, h₁', h₂'⟩
  let t₃ : Pair φ := ⟨(⟨W, hW⟩, ⟨V, hV⟩), fun y hy ↦ (hWU hy).1.2⟩
  refine ⟨Opposite.op t₃, ⟨(homOfLE ?_).op⟩, ⟨(homOfLE ?_).op⟩, hxW, fun y hy ↦ (hWU hy).1.1⟩
  · exact ⟨fun y hy ↦ (hWU hy).2.1, fun y hy ↦ (hVV hy).1⟩
  · exact ⟨fun y hy ↦ (hWU hy).2.2, fun y hy ↦ (hVV hy).2⟩

theorem triple_point (φ : X' ⟶ X) (ψ : X ⟶ Y) (x : X') (U : X'.Opens) (hx : x ∈ U) :
    ∃ t : (Triple φ ψ)ᵒᵖ, x ∈ ((cechTripleProjFirstThird φ ψ ⋙ pairFst (φ ≫ ψ)).obj t).unop.1 ∧
      ((cechTripleProjFirstThird φ ψ ⋙ pairFst (φ ≫ ψ)).obj t).unop.1 ≤ U := by
  obtain ⟨Z, hZ, hxZ, -⟩ := exists_isAffineOpen_mem_and_subset (x := ψ.base (φ.base x)) (U := (⊤ : Y.Opens)) trivial
  obtain ⟨V, hV, hxV, hVZ⟩ := exists_isAffineOpen_mem_and_subset (x := φ.base x) (U := ψ ⁻¹ᵁ Z) hxZ
  obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := U ⊓ φ ⁻¹ᵁ V) ⟨hx, hxV⟩
  exact ⟨Opposite.op ⟨(⟨W, hW⟩, ⟨V, hV⟩, ⟨Z, hZ⟩), fun y hy ↦ (hWU hy).2, fun y hy ↦ hVZ hy⟩, hxW,
    fun y hy ↦ (hWU hy).1⟩

theorem triple_point_two (φ : X' ⟶ X) (ψ : X ⟶ Y) (t₁ t₂ : (Triple φ ψ)ᵒᵖ) (x : X') (U : X'.Opens) (hx : x ∈ U)
    (h₁ : x ∈ ((cechTripleProjFirstThird φ ψ ⋙ pairFst (φ ≫ ψ)).obj t₁).unop.1)
    (h₂ : x ∈ ((cechTripleProjFirstThird φ ψ ⋙ pairFst (φ ≫ ψ)).obj t₂).unop.1) :
    ∃ t₃ : (Triple φ ψ)ᵒᵖ, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧
      x ∈ ((cechTripleProjFirstThird φ ψ ⋙ pairFst (φ ≫ ψ)).obj t₃).unop.1 ∧
      ((cechTripleProjFirstThird φ ψ ⋙ pairFst (φ ≫ ψ)).obj t₃).unop.1 ≤ U := by
  have h₁' : x ∈ t₁.unop.1.1.1 := h₁
  have h₂' : x ∈ t₂.unop.1.1.1 := h₂
  have hy₁ : φ.base x ∈ t₁.unop.1.2.1.1 := t₁.unop.2.1 h₁'
  have hy₂ : φ.base x ∈ t₂.unop.1.2.1.1 := t₂.unop.2.1 h₂'
  obtain ⟨Z, hZ, hxZ, hZZ⟩ := exists_isAffineOpen_mem_and_subset (x := ψ.base (φ.base x))
    (U := t₁.unop.1.2.2.1 ⊓ t₂.unop.1.2.2.1) ⟨t₁.unop.2.2 hy₁, t₂.unop.2.2 hy₂⟩
  obtain ⟨V, hV, hxV, hVV⟩ := exists_isAffineOpen_mem_and_subset (x := φ.base x)
    (U := t₁.unop.1.2.1.1 ⊓ t₂.unop.1.2.1.1 ⊓ ψ ⁻¹ᵁ Z) ⟨⟨hy₁, hy₂⟩, hxZ⟩
  obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset (x := x)
    (U := U ⊓ φ ⁻¹ᵁ V ⊓ (t₁.unop.1.1.1 ⊓ t₂.unop.1.1.1)) ⟨⟨hx, hxV⟩, h₁', h₂'⟩
  let t₃ : Triple φ ψ := ⟨(⟨W, hW⟩, ⟨V, hV⟩, ⟨Z, hZ⟩), fun y hy ↦ (hWU hy).1.2, fun y hy ↦ (hVV hy).2⟩
  refine ⟨Opposite.op t₃, ⟨(homOfLE ?_).op⟩, ⟨(homOfLE ?_).op⟩, hxW, fun y hy ↦ (hWU hy).1.1⟩
  · exact ⟨fun y hy ↦ (hWU hy).2.1, fun y hy ↦ (hVV hy).1.1, fun y hy ↦ (hZZ hy).1⟩
  · exact ⟨fun y hy ↦ (hWU hy).2.2, fun y hy ↦ (hVV hy).1.2, fun y hy ↦ (hZZ hy).2⟩

theorem extHom_of_id {R₀ : Type} [CommRing R₀] (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] {B : Type} [CommRing B]
    [Algebra R₀ B] (f : B →ₐ[R₀] B) (hf : ∀ b, f b = b) (y : R₁ ⊗[R₀] B) : extHom R₁ f y = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [hf]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem cechTripleRestrict_comp_pairRestrict {R₀ : Type} [CommRing R₀] (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (s' : X' ⟶ Sp R₀)
    (φ : X' ⟶ X) (ψ : X ⟶ Y) (c : CatCoh.H1 (ext R₁ (OAff s'))) :
    (extMap R₁ (cechTripleRestrictFirst φ ψ s')).pull1 ((extMap R₁ (pairRes φ s')).pull1 c) =
      (extMap R₁ (CoefMap.restrict (OAff s') (cechTripleProjFirstThird φ ψ ⋙ pairFst (φ ≫ ψ)))).pull1 c := by
  obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
  rw [CoefMap.pullCohomologyOne_class, CoefMap.pullCohomologyOne_class, CoefMap.pullCohomologyOne_class]
  refine congrArg _ (Subtype.ext ?_)
  funext T T' a
  exact extHom_of_id R₁ (coefHom (cechTripleRestrictFirst φ ψ s') T') (fun _ ↦ rfl) _

theorem pairRes_ext_bijective : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (X X' : Scheme.{0}) (s' : X' ⟶ Sp R₀) (φ : X' ⟶ X), (Function.Bijective (extMap R₁ (pairRes φ s')).pull1 ∧ Function.Bijective (extMap R₁ (pairRes φ s')).pull2) ∧ ∀ (Y : Scheme.{0}) (ψ : X ⟶ Y), Function.Injective (extMap R₁ (cechTripleRestrictFirst φ ψ s')).pull1 := by
  intro R₀ R₁ _ _ _ X X' s' φ
  have hp : Function.Bijective (extMap R₁ (pairRes φ s')).pull1 ∧ Function.Bijective (extMap R₁ (pairRes φ s')).pull2 :=
    GlobalTheory.T.cohomology_restrict_basis_extended_bijective R₀ R₁ X' s' _ (pairFst φ) (pair_point φ) (pair_point_two φ)
  refine ⟨hp, fun Y ψ x y e ↦ ?_⟩
  obtain ⟨x0, rfl⟩ := hp.1.2 x
  obtain ⟨y0, rfl⟩ := hp.1.2 y
  rw [cechTripleRestrict_comp_pairRestrict, cechTripleRestrict_comp_pairRestrict] at e
  rw [(GlobalTheory.T.cohomology_restrict_basis_extended_bijective R₀ R₁ X' s' _ _ (triple_point φ ψ) (triple_point_two φ ψ)).1.1 e]

end GlobalTheory.Obs.PairExt
end
end

