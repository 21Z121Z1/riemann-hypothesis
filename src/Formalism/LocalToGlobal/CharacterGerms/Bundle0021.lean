import Formalism.LocalToGlobal.CharacterGerms.Bundle0012
import Formalism.LocalToGlobal.CharacterGerms.Bundle0017
import Formalism.LocalToGlobal.CharacterGerms.RowTiePLogSt

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePNabMapSt
section
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.FormalSeriesBounds.MapFB

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

variable {K C : Type} [Field K] [Field C] (φ : K →+* C) {d : ℕ}

theorem constantCoeff_eval_single {n : ℕ} (a : Pt K n d) (ha : ∀ i, constantCoeff (a i) = 0) (f : PS K 1 d) :
    constantCoeff (ev ![a] f) = constantCoeff f :=
  cc_ev_eq _ (by intro j i; fin_cases j; simp [ha]) f

theorem map_pderiv {σ : Type} (x : σ) (f : MvPowerSeries σ K) :
    MvPowerSeries.map φ (pderiv K x f) = pderiv C x (MvPowerSeries.map φ f) := by
  ext n
  simp [coeff_pderiv, coeff_map]

theorem map_DofN (F : Fin d → PS K 2 d) {n : ℕ} (b : Fin n) (u : Fin d → K) (f : PS K n d) :
    MvPowerSeries.map φ (DofN F b u f) =
      DofN (fun j => MvPowerSeries.map φ (F j)) b (fun i => φ (u i)) (MvPowerSeries.map φ f) := by
  unfold DofN
  simp only [map_sum, map_mul, MvPowerSeries.map_C,
    map_ev2 φ (pt K d b) 0 (fun i => cc_pt b i) zc_zero, mpt_pt, mpt_zero, map_pderiv]

theorem map_iter_DofN (F : Fin d → PS K 2 d) {n : ℕ} (b : Fin n) (u : Fin d → K) (m : ℕ) (f : PS K n d) :
    MvPowerSeries.map φ ((DofN F b u)^[m] f) =
      (DofN (fun j => MvPowerSeries.map φ (F j)) b (fun i => φ (u i)))^[m] (MvPowerSeries.map φ f) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', map_DofN, ih]

theorem map_DmonN (F : Fin d → PS K 2 d) {n : ℕ} {ι : Type} [Fintype ι] (cp : ι → Fin n)
    (u : ι → Fin d → K) (m : ι →₀ ℕ) (f : PS K n d) :
    MvPowerSeries.map φ (DmonN F cp u m f) =
      DmonN (fun j => MvPowerSeries.map φ (F j)) cp (fun l i => φ (u l i)) m (MvPowerSeries.map φ f) := by
  unfold DmonN
  induction (Finset.univ : Finset ι).toList with
  | nil => rfl
  | cons l L ih => rw [List.foldr_cons, List.foldr_cons, map_iter_DofN, ih]

theorem map_DpolyN (F : Fin d → PS K 2 d) {n : ℕ} {ι : Type} [Fintype ι] (cp : ι → Fin n)
    (u : ι → Fin d → K) (P : MvPolynomial ι K) (f : PS K n d) :
    MvPowerSeries.map φ (DpolyN F cp u P f) =
      DpolyN (fun j => MvPowerSeries.map φ (F j)) cp (fun l i => φ (u l i)) (MvPolynomial.map φ P)
        (MvPowerSeries.map φ f) := by
  unfold DpolyN
  rw [map_sum, MvPolynomial.support_map_of_injective P φ.injective]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, MvPowerSeries.map_C, MvPolynomial.coeff_map, map_DmonN]

theorem map_expS' [Algebra ℚ K] [Algebra ℚ C] {n : ℕ} (f : PS K n d) (hf : constantCoeff f = 0) :
    MvPowerSeries.map φ (FB.expS K f) = FB.expS C (MvPowerSeries.map φ f) := by
  unfold FB.expS
  rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero hf), PowerSeries.map_exp]

theorem map_nabValN [Algebra ℚ K] [Algebra ℚ C] {O : Type} [CommRing O] [StarRing O]
    (B : FB K d O) (B' : FB C d O) (hF : ∀ j, B'.G.F j = MvPowerSeries.map φ (B.G.F j))
    (hA : ∀ a j, B'.A.act a j = MvPowerSeries.map φ (B.A.act a j)) (h : PS K 2 d)
    (hh : constantCoeff h = 0) (w0 : O) (m : ℕ) {n : ℕ} (f : PS K n d) {ι : Type} [Fintype ι]
    (cp : ι → Fin n) (u : ι → Fin d → K) (P : MvPolynomial ι K) :
    nabValN B' C (MvPowerSeries.map φ h) w0 m (MvPowerSeries.map φ f) cp (fun l i => φ (u l i))
        (MvPolynomial.map φ P) = φ (nabValN B K h w0 m f cp u P) := by
  unfold nabValN
  rw [← constantCoeff_map]
  congr 1
  have e1 : B.FK K = B.G.F := rfl
  have e2 : B'.FK C = fun j => MvPowerSeries.map φ (B.G.F j) := funext hF
  have eA : mpt φ (B.A.act w0) = B'.actK C w0 := by
    funext j; exact (hA w0 j).symm
  have eK : B.actK K w0 = B.A.act w0 := rfl
  have p0 : ∀ i, constantCoeff (pt K d (0 : Fin 1) i) = 0 := cc_pt (R := K) (d := d) 0
  have q0 : ∀ i, constantCoeff (comp1 (B.A.act w0) (pt K d (0 : Fin 1)) i) = 0 :=
    cc_comp1 (B.A.act w0) (B.A.const w0) (pt K d (0 : Fin 1)) p0
  have hL : MvPowerSeries.map φ (B.hL K h w0) = B'.hL C (MvPowerSeries.map φ h) w0 := by
    unfold FB.hL
    rw [eK, map_ev2 φ (pt K d 0) (comp1 (B.A.act w0) (pt K d 0)) p0 q0, mpt_pt,
      mpt_comp1 φ (B.A.act w0) (pt K d 0) p0, mpt_pt, eA]
  have hcL : constantCoeff (B.hL K h w0) = 0 := by
    unfold FB.hL
    rw [eK, constantCoeff_eval_pair (pt K d 0) (comp1 (B.A.act w0) (pt K d 0)) p0 q0, hh]
  have hcb : ∀ b : Fin n, constantCoeff (ev (n := n) ![pt K d b] (B.hL K h w0)) = 0 := fun b => by
    rw [constantCoeff_eval_single (pt K d b) (cc_pt (R := K) (d := d) b), hcL]
  have hcs : constantCoeff ((m : K) • ∑ b : Fin n, ev (n := n) ![pt K d b] (B.hL K h w0)) = 0 := by
    rw [Nat.cast_smul_eq_nsmul, map_nsmul, map_sum, Finset.sum_eq_zero fun b _ => hcb b, smul_zero]
  have hsum : ∑ b : Fin n, MvPowerSeries.map φ (ev (n := n) ![pt K d b] (B.hL K h w0)) =
      ∑ b : Fin n, ev (n := n) ![pt C d b] (B'.hL C (MvPowerSeries.map φ h) w0) :=
    Finset.sum_congr rfl fun b _ => by
      rw [map_ev1 φ (pt K d b) (cc_pt (R := K) (d := d) b), mpt_pt, hL]
  rw [e1, e2, map_DpolyN, map_mul, map_expS' φ _ hcs, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul,
    map_nsmul, map_sum, hsum]

end Formalism.L2.FormalSeriesBounds.MapFB

namespace Formalism.L2.FormalSeriesBounds

open MvPowerSeries MapFB Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]

theorem nabMapSt_holds : NabMapSt Xo c := by
  intro T io y C3 C _ _ V ι k Y hY a n f P
  have hga : (a3B C3).IsCanonGauge T.Fr (a3h C3) := by
    let := io.toAlgebra
    exact C3.ch.gauge
  have hcc : constantCoeff (a3h C3) = 0 := by
    have e := congrArg constantCoeff hga.ax0
    rwa [constantCoeff_eval_pair _ _ zc_zero (by simp), map_zero] at e
  unfold FBChart.nab chartDerivativeCoefficient
  rw [hY.h, hY.w0, hY.k]
  exact map_nabValN ι (a3B C3) Y.B hY.F hY.act (a3h C3) hcc H.w0 k f _ _ P

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePOActLog
section
noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Formalism.L2.FormalSeriesBounds

namespace OActLog

open PartialDerivEval LogEx

variable {C : Type} [Field C] [CharZero C] {d : ℕ}

theorem ev_zero_pt {n : ℕ} (g : PS C 1 d) : ev (n := n) ![(0 : Pt C n d)] g = MvPowerSeries.C (constantCoeff g) := by
  have h0 : ∀ j, constantCoeff ((0 : Pt C n d) j) = 0 := fun j => by simp
  apply pderiv.ext
  · intro q
    rw [pderiv_eval_single (0 : Pt C n d) h0 g q, pderiv_C]
    exact Finset.sum_eq_zero fun b _ => by simp
  · rw [constantCoeff_ev (z0_1 _ h0), constantCoeff_C]

theorem cc_pderiv {σ : Type} (i : σ) (f : MvPowerSeries σ C) :
    constantCoeff (pderiv C i f) = coeff (Finsupp.single i 1) f := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv]
  simp

theorem add_zero_of (G : FGLaw C d) (Q : PS C 1 d)
    (hQ : ev (n := 2) ![G.F] Q = ev (n := 2) ![pt C d 0] Q + ev (n := 2) ![pt C d 1] Q)
    (hlin : ∀ k, coeff (Finsupp.single ((0 : Fin 1), k) 1) Q = 0) (hc : constantCoeff Q = 0) : Q = 0 := by
  have hrow : ∀ k, ∑ b, Mm G b k * pderiv C ((0 : Fin 1), b) Q = 0 := by
    intro k
    have D := congrArg (fun g => ev (n := 1) ![pt C d 0, 0] (pderiv C ((1 : Fin 2), k) g)) hQ
    simp only [map_add, pderiv_eval_single G.F G.const, pderiv_eval_single (pt C d 0) (coordinate_point_constantCoeff 0), pderiv_eval_single (pt C d 1) (coordinate_point_constantCoeff 1),
      sum_d_pt_other (0 : Fin 2) 1 (by decide), sum_d_pt_self, zero_add] at D
    rw [ev_sum constant_zero_first_zero] at D
    simp only [ev_mul constant_zero_first_zero, eval_group_law_at_zero G, log_jacobian_at_zero G] at D
    rw [eval_eval_single (z0_1 (pt C d 1) (coordinate_point_constantCoeff 1)) constant_zero_first_zero (a' := (0 : Pt C 1 d)) (fun j => ev_X constant_zero_first_zero 1 j), ev_zero_pt,
      cc_pderiv, hlin k, map_zero] at D
    rw [← D]
    exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  have hd : ∀ b, pderiv C ((0 : Fin 1), b) Q = 0 := by
    intro b
    rw [← vec_cancel G (fun c => pderiv C ((0 : Fin 1), c) Q) b]
    exact Finset.sum_eq_zero fun k _ => by rw [hrow k, zero_mul]
  apply pderiv.ext
  · intro q
    obtain ⟨q1, q2⟩ := q
    fin_cases q1
    rw [map_zero]
    exact hd q2
  · rw [hc, map_zero]

def linM (φ : Pt C 1 d) (i j : Fin d) : C := coeff (Finsupp.single ((0 : Fin 1), j) 1) (φ i)

theorem linN_coeff {lg : Pt C 1 d} (hlin : LinN lg) (j b : Fin d) :
    coeff (Finsupp.single ((0 : Fin 1), b) 1) (lg j) = if b = j then 1 else 0 := by
  rw [hlin j _ (by rw [Finsupp.degree_single]), coeff_X]
  by_cases h : b = j
  · subst h; simp
  · rw [if_neg h, if_neg]
    intro e
    exact h (congrArg Prod.snd ((Finsupp.single_left_inj one_ne_zero).mp e))

theorem log_endo (G : FGLaw C d) (lg : Pt C 1 d) (hlin : LinN lg)
    (hadd : ∀ i, ev (n := 2) ![addOf G.F (pt C d 0) (pt C d 1)] (lg i) =
      ev (n := 2) ![pt C d 0] (lg i) + ev (n := 2) ![pt C d 1] (lg i))
    (φ : Pt C 1 d) (hφ0 : ∀ i, constantCoeff (φ i) = 0)
    (hφ : comp1 φ (addOf G.F (pt C (n := 2) d 0) (pt C (n := 2) d 1)) =
      addOf G.F (comp1 φ (pt C (n := 2) d 0)) (comp1 φ (pt C (n := 2) d 1)))
    (i : Fin d) : comp1 lg φ i = ∑ j, MvPowerSeries.C (linM φ i j) * lg j := by
  have haddF : addOf G.F (pt C d 0) (pt C d 1) = (G.F : Pt C 2 d) := funext fun j => eval_points_two (G.F j)
  have hF : ∀ j, ev (n := 2) ![G.F] (lg j) = ev (n := 2) ![pt C d 0] (lg j) + ev (n := 2) ![pt C d 1] (lg j) := by
    intro j; rw [← haddF]; exact hadd j
  have hφ1 : Z0 (![φ] : Fin 1 → Pt C 1 d) := z0_1 φ hφ0
  have hFz : Z0 (![G.F] : Fin 1 → Pt C 2 d) := z0_1 G.F G.const
  have hP0 : Z0 (![pt C d 0] : Fin 1 → Pt C 2 d) := z0_1 _ (coordinate_point_constantCoeff 0)
  have hP1 : Z0 (![pt C d 1] : Fin 1 → Pt C 2 d) := z0_1 _ (coordinate_point_constantCoeff 1)
  set A : Pt C 2 d := comp1 φ (pt C (n := 2) d 0) with hA
  set B : Pt C 2 d := comp1 φ (pt C (n := 2) d 1) with hB
  have hA0 : ∀ j, constantCoeff (A j) = 0 := fun j => const_ev hP0 (hφ0 j)
  have hB0 : ∀ j, constantCoeff (B j) = 0 := fun j => const_ev hP1 (hφ0 j)
  have hAB : Z0 (![A, B] : Fin 2 → Pt C 2 d) := by
    intro k j; fin_cases k
    · exact hA0 j
    · exact hB0 j

  have hlgAB : ∀ j, ev (n := 2) ![addOf G.F A B] (lg j) = ev (n := 2) ![A] (lg j) + ev (n := 2) ![B] (lg j) := by
    intro j
    have h := congrArg (ev (n := 2) ![A, B]) (hF j)
    have hFc : ∀ k, constantCoeff (G.F k) = 0 := G.const
    rw [ev_add hAB, eval_eval_single hFz hAB (a' := addOf G.F A B) (fun k => rfl),
      eval_eval_single hP0 hAB (a' := A) (fun k => ev_X hAB 0 k),
      eval_eval_single hP1 hAB (a' := B) (fun k => ev_X hAB 1 k)] at h
    exact h

  have hcomp : ev (n := 2) ![G.F] (comp1 lg φ i) =
      ev (n := 2) ![pt C d 0] (comp1 lg φ i) + ev (n := 2) ![pt C d 1] (comp1 lg φ i) := by
    have e1 : ev (n := 2) ![G.F] (comp1 lg φ i) = ev (n := 2) ![comp1 φ G.F] (lg i) :=
      eval_eval_single hφ1 hFz (a' := comp1 φ G.F) (fun k => rfl) (lg i)
    have e2 : comp1 φ G.F = addOf G.F A B :=
      calc comp1 φ G.F = comp1 φ (addOf G.F (pt C d 0) (pt C d 1)) := by rw [haddF]
        _ = addOf G.F A B := hφ
    have e3 : ev (n := 2) ![pt C d 0] (comp1 lg φ i) = ev (n := 2) ![A] (lg i) :=
      eval_eval_single hφ1 hP0 (a' := A) (fun k => rfl) (lg i)
    have e4 : ev (n := 2) ![pt C d 1] (comp1 lg φ i) = ev (n := 2) ![B] (lg i) :=
      eval_eval_single hφ1 hP1 (a' := B) (fun k => rfl) (lg i)
    rw [e1, e2, e3, e4, hlgAB]
  have hQ := add_zero_of G (comp1 lg φ i - ∑ j, MvPowerSeries.C (linM φ i j) * lg j) (by
      rw [ev_sub hFz, ev_sub hP0, ev_sub hP1, ev_sum hFz, ev_sum hP0, ev_sum hP1, hcomp]
      simp only [ev_mul hFz, ev_mul hP0, ev_mul hP1, ev_C, hF, mul_add, Finset.sum_add_distrib]
      ring)
    (by
      intro k
      rw [map_sub, map_sum]
      simp only [coeff_C_mul, linN_coeff hlin, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
      rw [← cc_pderiv, show comp1 lg φ i = ev ![φ] (lg i) from rfl, pderiv_eval_single φ hφ0, map_sum]
      simp only [map_mul, constantCoeff_ev hφ1, cc_pderiv, linN_coeff hlin, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      unfold linM
      ring)
    (by
      rw [map_sub, map_sum, show comp1 lg φ i = ev ![φ] (lg i) from rfl, constantCoeff_ev hφ1, linN_const hlin]
      simp [linN_const hlin])
  exact sub_eq_zero.mp hQ

end OActLog

end Formalism.L2.FormalSeriesBounds
end
end

