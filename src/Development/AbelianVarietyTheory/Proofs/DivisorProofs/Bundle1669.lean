import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0409
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0571
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1583
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1639
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1644
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulMemRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1640
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0823
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1631
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0829
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1050
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0923
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0885
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0887
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import CompanionTheory.EightfoldTheory.ZeroLevelTheory.LocalLanglands.Imports
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0253
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0702
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0794
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0730
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0802
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0729
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0750
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0793
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0809
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0723
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0349
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0327
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0780
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1641

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MuDvdOfDvdIterates
section
open GlobalTheory GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv GlobalTheory.HTLat Matrix TensorProduct

noncomputable section

namespace GlobalTheory.MuDivides

private theorem mem_span_pow_smul_univ_iff_dvd {R : Type} [CommRing R] (q x : R) (n : ℕ) :
    x ∈ (Ideal.span {q} ^ n • ⊤ : Submodule R R) ↔ q ^ n ∣ x := by
  rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

theorem dvd_of_step {R : Type} [CommRing R] (q a : R) [IsAdicComplete (Ideal.span {q}) R]
    (P : R → Prop) (h : ∀ z, P z → ∃ y z₁, z = a * y + q * z₁ ∧ P z₁) (z : R) (hz : P z) :
    a ∣ z := by
  choose Y Z hYZ using h

  let s : ℕ → {w : R // P w} := fun n =>
    Nat.rec ⟨z, hz⟩ (fun _ w => ⟨Z w.1 w.2, (hYZ w.1 w.2).2⟩) n
  obtain ⟨w, y, hw0, hw⟩ : ∃ w y : ℕ → R, w 0 = z ∧ ∀ n, w n = a * y n + q * w (n + 1) :=
    ⟨fun n => (s n).1, fun n => Y (s n).1 (s n).2, rfl, fun n => (hYZ _ _).1⟩

  have key : ∀ n, z = a * (∑ k ∈ Finset.range n, q ^ k * y k) + q ^ n * w n := by
    intro n
    induction n with
    | zero => simp [hw0]
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, hw n]
      ring
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := Ideal.span {q}) (M := R) inferInstance
    (f := fun n => ∑ k ∈ Finset.range n, q ^ k * y k) (by
      intro m n hmn
      rw [SModEq.sub_mem, mem_span_pow_smul_univ_iff_dvd]
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
      refine ⟨-∑ j ∈ Finset.range d, q ^ j * y (m + j), ?_⟩
      rw [Finset.sum_range_add, mul_neg, Finset.mul_sum]
      simp only [pow_add, mul_assoc, sub_add_cancel_left])
  refine ⟨L, ?_⟩
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (I := Ideal.span {q}) (M := R) inferInstance _ fun n => ?_
  rw [SModEq.sub_mem, sub_zero, mem_span_pow_smul_univ_iff_dvd]
  have hn := hL n
  rw [SModEq.sub_mem, mem_span_pow_smul_univ_iff_dvd] at hn
  obtain ⟨c, hc⟩ := hn
  exact ⟨a * c + w n, by linear_combination key n + a * hc⟩

variable {p : ℕ} [hp : Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C]
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]

omit [IsAlgClosed C] [IsAdicComplete (Ideal.span {(p : O)}) O] in

theorem modP_isNilpotent_of_not_isUnit (hv : v.Integers O) (x : ModP O p) (hx : ¬IsUnit x) : IsNilpotent x := by
  obtain ⟨o, rfl⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {(p : O)}) x

  have hlt : v (algebraMap O C o) < 1 := by
    refine lt_of_le_of_ne (hv.map_le_one o) fun h1 => hx ?_
    exact (hv.isUnit_of_one' h1).map _

  have hp0 : 0 < v (algebraMap O C (p : O)) := by
    rw [map_natCast]
    exact (Valuation.pos_iff v).2 (Nat.cast_ne_zero.2 hp.out.ne_zero)
  obtain ⟨n, hn⟩ := NNReal.exists_pow_lt_of_lt_one hp0 hlt
  refine ⟨n, ?_⟩
  have hdvd : (p : O) ∣ o ^ n := hv.dvd_of_le (by rw [map_pow, map_pow]; exact hn.le)
  rw [← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton.2 hdvd)

omit [IsAlgClosed C] [IsAdicComplete (Ideal.span {(p : O)}) O] in

theorem eq_zero_of_forall_pow_dvd (hv : v.Integers O) (c m : PreTilt O p) (hc : ¬IsUnit c)
    (h : ∀ n, c ^ p ^ n ∣ m) : m = 0 := by
  have h0 : ¬IsUnit (PreTilt.coeff 0 c) := fun hu => hc (GlobalTheory.AinfXi.isUnit_of_coeff_zero hu)
  obtain ⟨N, hN⟩ := modP_isNilpotent_of_not_isUnit hv _ h0
  refine Perfection.ext (R := ModP O p) (p := p) fun k => ?_
  rw [← PreTilt.coeff_def, ← PreTilt.coeff_def, map_zero]
  obtain ⟨d, hd⟩ := h (k + N)

  rw [hd, map_mul, map_pow, pow_add, pow_mul, GlobalTheory.AinfXi.coeff_pow_pow_zero,
    pow_eq_zero_of_le (Nat.lt_pow_self hp.out.one_lt).le hN, zero_mul]

omit [IsAdicComplete (Ideal.span {(p : O)}) O] in
theorem root_iterate_pow (n : ℕ) (ε : PreTilt O p) : (root^[n] ε) ^ p ^ n = ε :=
  iterate_frobeniusEquiv_symm_pow_p_pow (PreTilt O p) p ε n

theorem tilt_dvd (hv : v.Integers O) (ε : PreTilt O p) (hm : ε - 1 ≠ 0) (w : PreTilt O p)
    (h : ∀ n : ℕ, ε - 1 ∣ (root^[n] ε - 1) * w) : ε - 1 ∣ w := by
  obtain ⟨hD, hV⟩ := GlobalTheory.TiltValuation.tilt_isDomain_valuationRing p C v O hv

  have ht : ∀ n : ℕ, (root^[n] ε - 1) ^ p ^ n = ε - 1 := fun n => by
    rw [sub_pow_char_pow, one_pow, root_iterate_pow]
  rcases ValuationRing.dvd_total (ε - 1) w with hw | ⟨u, hu⟩
  · exact hw
  by_cases hu' : IsUnit u
  · exact hu'.dvd_mul_right.1 (by rw [← hu])

  exfalso
  refine hm (eq_zero_of_forall_pow_dvd hv u (ε - 1) hu' fun n => ?_)
  have h1 : (ε - 1) * u ∣ (ε - 1) * (root^[n] ε - 1) := by
    have := mul_dvd_mul_right (h n) u
    rwa [mul_assoc, ← hu, mul_comm (root^[n] ε - 1)] at this
  have hut : u ∣ root^[n] ε - 1 := (mul_dvd_mul_iff_left hm).1 h1
  simpa only [ht n] using pow_dvd_pow_of_dvd hut (p ^ n)

omit [IsAdicComplete (Ideal.span {(p : O)}) O] in
theorem constantCoeff_mu (ε : PreTilt O p) : WittVector.constantCoeff (mu ε) = ε - 1 := by
  rw [mu, map_sub, map_one,
    show WittVector.constantCoeff (WittVector.teichmuller p ε) = ε from
      WittVector.teichmuller_coeff_zero p ε]

omit [IsAdicComplete (Ideal.span {(p : O)}) O] in
theorem exists_eq_p_mul (x : Ainf p O) (hx : WittVector.constantCoeff x = 0) :
    ∃ y, x = (p : Ainf p O) * y :=
  Ideal.mem_span_singleton.1 ((WittVector.mem_span_p_iff_coeff_zero_eq_zero x).2 hx)

theorem dvd_of_dvd_p_mul (hv : v.Integers O) (ε : PreTilt O p) (hm : ε - 1 ≠ 0) (w : Ainf p O)
    (h : mu ε ∣ (p : Ainf p O) * w) : mu ε ∣ w := by
  obtain ⟨hD, -⟩ := GlobalTheory.TiltValuation.tilt_isDomain_valuationRing p C v O hv
  obtain ⟨c, hc⟩ := h

  have hc0 : WittVector.constantCoeff c = 0 := by
    have h0 := congrArg WittVector.constantCoeff hc
    rw [map_mul, map_mul, map_natCast, CharP.cast_eq_zero, zero_mul, constantCoeff_mu] at h0
    exact (mul_eq_zero.1 h0.symm).resolve_left hm
  obtain ⟨c', rfl⟩ := exists_eq_p_mul c hc0
  refine ⟨c', sub_eq_zero.1 (WittVector.eq_zero_of_p_mul_eq_zero _ ?_)⟩
  linear_combination hc

theorem mu_dvd_of_forall_dvd : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ z : Ainf p O, (∀ n : ℕ, mu ε ∣ mu (root^[n] ε) * z) → mu ε ∣ z := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε z hz
  have hm : ε - 1 ≠ 0 := by
    rw [← constantCoeff_mu]
    exact (GlobalTheory.DetInv.mu_coeff_zero_ne_zero p C v O hv ε hε).1
  refine dvd_of_step (p : Ainf p O) (mu ε) (fun x => ∀ n : ℕ, mu ε ∣ mu (root^[n] ε) * x) ?_ z hz
  intro x hx

  obtain ⟨b, hb⟩ : ε - 1 ∣ WittVector.constantCoeff x := by
    refine tilt_dvd hv ε hm _ fun n => ?_
    have h1 := map_dvd WittVector.constantCoeff (hx n)
    rwa [map_mul, constantCoeff_mu, constantCoeff_mu] at h1

  obtain ⟨z₁, hz₁⟩ := exists_eq_p_mul (x - mu ε * WittVector.teichmuller p b) (by
    rw [map_sub, map_mul, constantCoeff_mu, hb, sub_eq_zero,
      show WittVector.constantCoeff (WittVector.teichmuller p b) = b from
        WittVector.teichmuller_coeff_zero p b])
  refine ⟨WittVector.teichmuller p b, z₁, by rw [← hz₁]; ring, fun n => ?_⟩

  apply dvd_of_dvd_p_mul hv ε hm
  have h1 : mu ε ∣ mu (root^[n] ε) * (x - mu ε * WittVector.teichmuller p b) := by
    rw [mul_sub]
    exact dvd_sub (hx n) (dvd_mul_of_dvd_right (dvd_mul_right _ _) _)
  rwa [hz₁, mul_left_comm] at h1

end GlobalTheory.MuDivides
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormDbarQuotientFormBound
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CurveDens

open GlobalTheory.VBExt (AdaptedChart)
open GlobalTheory.Twist (resM app_resM)

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
  {S : ShortComplex X.Modules}

theorem form_eq_gram_frame {r s : ℕ} (h : Met p σ S.X₂ (r + s)) (hS : S.ShortExact)
    (a : AdaptedChart S r s) {V : X.Opens} (u w : Γ(S.X₂, V)) {x : CxPts p σ}
    (hx : x ∈ ptsIn p σ a.U) (hV : x ∈ ptsIn p σ V) :
    h.form u w x = HermFrame.form (h.gram a.frame x)
      (fun i => (a.mid hS).crd p σ u x (finSumFinEquiv i))
      (fun i => (a.mid hS).crd p σ w x (finSumFinEquiv i)) := by
  rw [h.form_eq (a.mid hS) hx u w hV, Met.gram_frame h hS a hx, form_eq_sum, form_eq_sum,
    ← finSumFinEquiv.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← finSumFinEquiv.sum_comp]
  rfl

def adaptedOf (a : AdaptedChart S 1 1) {U : X.Opens} (t : Γ(S.X₁, U))
    (ht : IsFrame fun _ : Fin 1 => t) : AdaptedChart S 1 1 where
  U := U ⊓ a.U
  e := fun _ => resM S.X₁ inf_le_left t
  t := fun i => resM S.X₂ inf_le_right (a.t i)
  he := ht.res inf_le_left
  ht := by
    simp only [app_resM]
    exact a.ht.res inf_le_right

theorem crd_adaptedOf (hS : S.ShortExact) (a : AdaptedChart S 1 1) {U : X.Opens} (t : Γ(S.X₁, U))
    (ht : IsFrame fun _ : Fin 1 => t) {x : CxPts p σ} (hx : x ∈ ptsIn p σ (adaptedOf a t ht).U) :
    (fun i => ((adaptedOf a t ht).mid hS).crd p σ (S.f.app U t) x (finSumFinEquiv i)) =
      Pi.single (Sum.inl 0) 1 := by
  have e : (adaptedOf a t ht).frame (.inl 0) = resM S.X₂ inf_le_left (S.f.app U t) :=
    app_resM _ _ _
  funext i
  rw [← Chart.crd_resM _ (S.f.app U t) (inf_le_left : (adaptedOf a t ht).U ≤ U) hx, ← e]
  refine (AdaptedChart.crd_frame hS (adaptedOf a t ht) hx i (.inl 0)).trans ?_
  rw [Matrix.one_apply, Pi.single_apply]

theorem norm_dbar_projection_sq (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ)
    (S : ShortComplex X.Modules) (h : Met p σ S.X₂ (1 + 1)) (hS : S.ShortExact) (h₁ : IsVB S.X₁ 1)
    (h₃ : IsVB S.X₃ 1) (H : h.IsCInf) (U : X.Opens) (t : Γ(S.X₁, U)) (w : Γ(S.X₂, U))
    (ht : IsFrame (fun _ : Fin 1 => t)) (c : AlgChart p σ 1) (y : CxPts p σ) (hy : y ∈ c.e.source)
    (hU : y ∈ ptsIn p σ U) :
    ‖dbar (fun v => h.form w (S.f.app U t) (c.e.symm v)) (c.e y) (EuclideanSpace.single 0 1) -
        h.form w (S.f.app U t) y *
          dbar (fun v => (Real.log (h.form (S.f.app U t) (S.f.app U t) (c.e.symm v)).re : ℂ)) (c.e y)
            (EuclideanSpace.single 0 1)‖ ^ 2 =
      ((h.form (S.f.app U t) (S.f.app U t) y).re * (h.form w w y).re -
        ‖h.form w (S.f.app U t) y‖ ^ 2) * (Real.pi * h.bcDens hS h₁ h₃ c y) := by
  obtain ⟨a', ha'⟩ := Met.exists_adapted (p := p) (σ := σ) hS h₁ h₃ y
  set a := adaptedOf a' t ht with a_def
  have ha : y ∈ ptsIn p σ a.U := mem_ptsIn_inf.2 ⟨hU, ha'⟩
  set G : ReciprocityTheory.L2DbarEstimates.V 1 → Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ :=
    fun v => h.gram a.frame (c.e.symm v) with G_def
  set s : ReciprocityTheory.L2DbarEstimates.V 1 → Fin 1 ⊕ Fin 1 → ℂ :=
    fun v i => (a.mid hS).crd p σ w (c.e.symm v) (finSumFinEquiv i) with s_def
  have hs : ∀ i, DifferentiableAt ℂ (fun x => s x i) (c.e y) := fun i =>
    c.differentiableAt_ev _ hy (mem_ptsIn_inf.2 ⟨hU, ha⟩)
  have hG : MContDiffAt 1 G (c.e y) :=
    ((H.gram a.frame ha).mContDiffAt c hy).of_le (by norm_cast)
  have hp := h.eventually_posDef hS a c hy ha
  have hn : ∀ᶠ v in 𝓝 (c.e y), c.e.symm v ∈ ptsIn p σ (U ⊓ a'.U) :=
    eventually_of_mem ((ChartGlue.isOpen_over c.e (isOpen_ptsIn (U ⊓ a'.U))).mem_nhds
      (ChartGlue.mem_over c.e hy ha)) fun _ hv => hv.2
  have e₀ : c.e.symm (c.e y) = y := c.e.left_inv hy
  have key (v : ReciprocityTheory.L2DbarEstimates.V 1) (hv : c.e.symm v ∈ ptsIn p σ (U ⊓ a'.U)) :
      h.form w (S.f.app U t) (c.e.symm v) = form (G v) (s v) (Pi.single (Sum.inl 0) 1) ∧
      h.form (S.f.app U t) (S.f.app U t) (c.e.symm v) = G v (Sum.inl 0) (Sum.inl 0) ∧
      h.form w w (c.e.symm v) = form (G v) (s v) (s v) := by
    have hv' : c.e.symm v ∈ ptsIn p σ U := (mem_ptsIn_inf.1 hv).1
    have hc := crd_adaptedOf hS a' t ht hv
    refine ⟨?_, ?_, form_eq_gram_frame h hS a w w hv hv'⟩
    · rw [form_eq_gram_frame h hS a w _ hv hv', hc]
    · rw [form_eq_gram_frame h hS a _ _ hv hv', hc, form_single]
  have k₀ := key _ (e₀.symm ▸ ha)
  rw [e₀] at k₀
  have e₁ : dbar (fun v => h.form w (S.f.app U t) (c.e.symm v)) (c.e y) =
      dbar (fun v => form (G v) (s v) (Pi.single (Sum.inl 0) 1)) (c.e y) :=
    dbar_congr (hn.mono fun v hv => (key v hv).1)
  have e₂ : dbar (fun v => (Real.log (h.form (S.f.app U t) (S.f.app U t) (c.e.symm v)).re : ℂ))
        (c.e y) = dbar (fun v => (Real.log (G v (Sum.inl 0) (Sum.inl 0)).re : ℂ)) (c.e y) :=
    dbar_congr (hn.mono fun v hv => by simp only [(key v hv).2.1])
  have e₃ : G (c.e y) = h.gram a.frame y := by rw [G_def]; simp only [e₀]
  have main := GlobalTheory.T.norm_dbar_form_sub_log_metric_le _ G s (EuclideanSpace.single 0 1) (c.e y) hG hp hs
  rw [e₁, e₂, k₀.1, k₀.2.1, k₀.2.2, Met.bcDens_eq hS h₁ h₃ a c H hy ha]
  exact main

end GlobalTheory.CurveDens
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupOmegaFiniteFreeAndPSqMemDlogSpan
section
noncomputable section

open GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta CategoryTheory

namespace GlobalTheory.DlogSpan

theorem ker_finite_free {O : Type} [CommRing O] [IsDomain O] [ValuationRing O] {h : ℕ}
    (b : (Fin h → O) →ₗ[O] (Fin h → O)) :
    Module.Finite O (LinearMap.ker b) ∧ Module.Free O (LinearMap.ker b) := by
  have flat : ∀ S : Submodule O (Fin h → O), Module.Flat O S := fun S => by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
    rintro x ⟨a, ha⟩
    have h1 : (a : O) • (x : Fin h → O) = 0 := congrArg Subtype.val ha
    rw [Submodule.mem_bot]
    apply Subtype.ext
    exact (smul_eq_zero.1 h1).resolve_left (nonZeroDivisors.ne_zero a.2)
  haveI := flat (LinearMap.range b)
  haveI : Module.Free O (LinearMap.range b) := Module.free_of_flat_of_isLocalRing
  obtain ⟨s, hs⟩ := Module.projective_lifting_property b.rangeRestrict LinearMap.id
    b.surjective_rangeRestrict
  have hs' : ∀ y, b (s y) = y := fun y => congrArg Subtype.val (LinearMap.congr_fun hs y)
  let π : (Fin h → O) →ₗ[O] LinearMap.ker b :=
    (LinearMap.id - s ∘ₗ b.rangeRestrict).codRestrict _ fun x => by
      simp [LinearMap.mem_ker, hs']
  have hπ : Function.Surjective π := fun x => ⟨x, by
    apply Subtype.ext
    have h0 : b.rangeRestrict x = 0 := Subtype.ext x.2
    simp [π, h0]⟩
  haveI hfin : Module.Finite O (LinearMap.ker b) := Module.Finite.of_surjective π hπ
  haveI := flat (LinearMap.ker b)
  exact ⟨hfin, Module.free_of_flat_of_isLocalRing⟩

theorem sub_one_dvd {O : Type} [CommRing O] [IsDomain O] {ζ : O} {k : ℕ}
    (hζ : IsPrimitiveRoot ζ k) (hk : 1 < k) : ζ - 1 ∣ (k : O) := by
  have h0 := hζ.geom_sum_eq_zero hk
  have h1 : (k : O) = -∑ i ∈ Finset.range k, (ζ ^ i - 1) := by
    rw [Finset.sum_sub_distrib, h0]; simp
  rw [h1, dvd_neg]
  exact Finset.dvd_sum fun i _ => sub_one_dvd_pow_sub_one ζ i

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O]

def pDivGroupOmegaBidualEquiv (G : PDivGroup p O) : G.omega ≃ₗ[O] G.dual.dual.omega :=
  LinearEquiv.ofLinear (omegaMap _ _ G.bidual.inv) (omegaMap _ _ G.bidual.hom)
    (by rw [← omegaMap_comp, Iso.inv_hom_id, omegaMap_id])
    (by rw [← omegaMap_comp, Iso.hom_inv_id, omegaMap_id])

theorem pDivGroupOmegaBidual_dlog_eq_dual_hodgeTate (G : PDivGroup p O) (χ : G.dual.Tate) :
    pDivGroupOmegaBidualEquiv G (dlog G χ) = hodgeTate G.dual χ := by
  rw [hodgeTate_apply, ← dualHom_bidual_inv, dlog_tateMap]
  rfl

theorem finite_free_and_sq_smul_mem_span : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] (ε : PreTilt O p) (hε : GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.IsPrimitiveSystem ε), v.Integers O → GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.HodgeTateSandwichAt hε → ∀ G : PDivGroup p O, Module.Finite O G.omega ∧ Module.Free O G.omega ∧ ∀ w : G.omega, (p : O) ^ 2 • w ∈ Submodule.span O (Set.range (dlog (G := G))) := by
  intro p hp C _ _ _ v O _ _ _ _ _ ε hε hv hS G
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  obtain ⟨u₁, u₂, hS⟩ := hS
  obtain ⟨D, e, fil, lie, hR⟩ := hS G.dual ℤ_[p] (padicAction _)
  let Ψ : G.omega ≃ₗ[O] D.Fil := pDivGroupOmegaBidualEquiv G ≪≫ₗ fil
  obtain ⟨hfin, hfree⟩ := ker_finite_free D.bb
  haveI : Module.Finite O D.Fil := hfin
  haveI : Module.Free O D.Fil := hfree
  refine ⟨Module.Finite.equiv Ψ.symm, Module.Free.of_equiv Ψ.symm, fun w => ?_⟩
  have hζ : IsPrimitiveRoot (root ε).untilt p := by
    have h := hε 1
    rw [pow_one] at h
    exact h
  obtain ⟨-, -, -, hb, -⟩ := HodgeTateBound.bound p C v O hv ε hζ ℤ_[p] _ D
  have hθ : WittVector.fontaineTheta O p (nu ε) = (root ε).untilt - 1 := by
    rw [nu, map_sub, WittVector.fontaineTheta_teichmuller, map_one]
  have hal : ∀ χ : G.dual.Tate, D.al (toO e χ) = (Ψ ((u₁ : O) • dlog G χ) : Fin _ → O) := by
    intro χ
    rw [hR.al_eq, ← hodgeTate_eq_omegaMap, ← pDivGroupOmegaBidual_dlog_eq_dual_hodgeTate, map_smul]
    rfl
  have key : ∀ y, ∃ s ∈ Submodule.span O (Set.range (dlog G)),
      D.al y = (Ψ s : Fin _ → O) := by
    intro y
    refine ⟨∑ i, y i • (u₁ : O) • dlog G (e.symm (Pi.single i 1)), ?_, ?_⟩
    · exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
    · have hy : y = ∑ i, y i • toO e (e.symm (Pi.single i 1)) := by
        ext j
        simp [toO, Finset.sum_apply, Pi.single_apply, apply_ite]
      conv_lhs => rw [hy]
      rw [map_sum, map_sum, Submodule.coe_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, hal, map_smul Ψ (y i), Submodule.coe_smul]
  obtain ⟨y, hy⟩ := hb (Ψ w) (Ψ w).2
  obtain ⟨s, hs, hys⟩ := key y
  have h1 : WittVector.fontaineTheta O p (nu ε) • w = s := by
    apply Ψ.injective
    apply Subtype.ext
    rw [map_smul, Submodule.coe_smul, ← hy, hys]
  obtain ⟨c, hc⟩ := sub_one_dvd hζ hp.out.one_lt
  have h2 : (p : O) ^ 2 • w = ((p : O) * c) • s := by
    rw [← h1, hθ, smul_smul, pow_two]
    congr 1
    rw [mul_assoc, mul_comm c, ← hc]
  rw [h2]
  exact Submodule.smul_mem _ _ hs

end GlobalTheory.DlogSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParsevalFundamentalDomainThetaStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parseval_fundamental_domain_theta : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (𝓕₁ : Set (κ → AF F)), @IsAddFundamentalDomain (GlobalTheory.ThetaParseval.ratVec F κ) _ _ _ (borel _) 𝓕₁ μ → ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
      ∫⁻ x in 𝓕₁, ∑' ξ : κ → F, ‖Φ ((fun i => algebraMap F (AF F) (ξ i)) + x)‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ := by
  first | exact @GlobalTheory.ThetaUnfold.unfold | exact GlobalTheory.ThetaUnfold.unfold | (intros; apply GlobalTheory.ThetaUnfold.unfold <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PassIn3OfRows
section
open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Cx NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem passIn3_of_rows : ∀ (D : D7) [IsTotallyComplex D.what₂.LL] (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (C CH : ℝ), R.WeakCharacterisation F → A3.fam3.Ok3 1 → PrimRows3 R F → (∀ k : Fin 2, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; ∃ (C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv (ZMod (D.host.g k))) (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod (D.host.g k)) C), ∀ f, D.ntypes.eSer k f = Formalism.L2.NT.eSerO O D.R.r f) → Formalism.MainNotions.PrimeDegreeVariant.LevelRatioBound D → (R.num F C CH).de = 8 * (D.R.f : ℝ) * (D.R.r : ℝ) / ((min (D.host.g 0) (D.host.g 1) : ℕ) : ℝ) → (R.num F C CH).la = Real.log (Fintype.card G) → PassIn3 R F C CH := by
  intro D _ G _ _ Pl0 I0 T A3 Ks _ _ _ R F C CH hC hOk hP hser hadm hde hla
  classical
  have hlev : R.toRealDat.grp_levels F.lv2 := hC.base.grp.levels
  have hrec : R.toRealDat.grp_record := hC.base.grp.record
  have hirr : ∀ χ ∈ A3.A.X, IsAbsIrrChar χ := hOk.ok2.irr
  have hind := GlobalTheory.T.goodCharacter_placewise_cuspidal_parabolic_product D G Pl0 T A3.A Ks R.toRealDat hrec hser hirr
  letI i0 : Fintype F.P0 := Fintype.ofFinite _
  letI i1 : Fintype F.P1 := Fintype.ofFinite _
  have hone : ∀ χ ∈ A3.A.X, ∑ h : F.P0, χ (h : G) * (((F.ψ0 h)⁻¹ : D.what₂.LLˣ) : D.what₂.LL) = (Fintype.card F.P0 : D.what₂.LL) :=
    @GlobalTheory.RealOneVector.typeSum_base_eq_card D G _ _ Pl0 T A3.A Ks _ _ _ R.toRealDat F.lv2 hlev hind i0
  obtain ⟨S, iS, Ws, iA, iM, iF, τ, hgood, hchars, hm1⟩ :=
    GlobalTheory.T.exists_goodFamily_given_characters_multiplicityOne D.what₂.LL G A3.A.X hirr F.P0 F.ψ0 hone
  obtain ⟨hcard, hres⟩ := GlobalTheory.typePlaces_card_and_residue_le D G Pl0 T A3.A Ks R.toRealDat hrec
  have hcol := @GlobalTheory.ColumnMultSum.columnMult D G _ _ Pl0 T A3.A Ks _ _ _ R.toRealDat F.lv2 hlev hcard hres hadm hirr hind i1
  refine ⟨S, iS, Ws, iA, iM, iF, τ, (GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.nbar R.Pg D.R.k : ℝ), ?_⟩
  refine ⟨GlobalTheory.ratMuP_of_rowTest D G Pl0 I0 T A3 Ks R F hP.rowTest hP.h2P, hgood, hchars, hm1, ?_, ?_, ?_⟩
  · exact_mod_cast GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.nbar_pos R.Pg D.R.k
  · intro s
    obtain ⟨n, hn, hb⟩ := hcol (Formalism.IndefR.TransferLatticeStatement.charOf (τ s)) ((hchars _).2 ⟨s, rfl⟩)
    have hnOf := GlobalTheory.T.multiplicity_linearCharacter_eq_characterSum D.what₂.LL G (Ws s) (τ s) F.P1 F.ψ1
    have heq : Formalism.IndefR.IndefiniteEpsilonOperator.nOf (τ s) ⟨F.P1, F.ψ1⟩ = n := by
      apply Nat.cast_injective (R := D.what₂.LL)
      rw [hnOf]
      exact hn
    rw [heq]
    have hde' : ((faceOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc (R.toCx3 F).zs).Z.num C CH).de = _ := hde
    rw [hde']
    have := abs_le.1 hb
    constructor <;> nlinarith [this.1, this.2]
  · exact hla

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceIsoCompatibleLocalLanglandsFourStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.place_iso_compatible_local_langlands_four : ∀ (E E' Ω : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω] [Algebra E Ω] [Algebra E' Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (w' : HeightOneSpectrum (𝓞 E')) (h : IsPlaceOver A w) (h' : IsPlaceOver A w') (j : E →+* E') (i : w.adicCompletion E ≃+* w'.adicCompletion E'), GlobalTheory.LocLanglands.PlaceIso A w A w' (RingEquiv.refl Ω) j i → ∀ (rc : IrrGL (w.adicCompletion E) → WD h) (rc' : IrrGL (w'.adicCompletion E') → WD h'), (∀ x x', RepRel i x x' → WDRel (RingEquiv.refl Ω) (rc x) (rc' x')) → (∀ x x', RepRel i x x' → (UpperTheory.Zero.LLC.Good x ↔ UpperTheory.Zero.LLC.Good x')) → ∀ (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a), UpperTheory.Zero.LLC.LawsT a ha rc → ∀ (a' : Weil h' →* (w'.adicCompletion E')ˣ) (ha' : IsLocalArtin h' a'), (∀ (x : IrrGL (w'.adicCompletion E')) ω, HasCentralChar x.rep ω → ∀ σ, ‖((rc' x).eig σ).prod‖ = ‖(ω (a' σ) : ℂ)‖) ∧ (∀ x χ hχ, UpperTheory.Zero.LLC.Good x → rc' (x.tw χ hχ) = (rc' x).lpChar (rc' (.ofChar χ hχ))) ∧ (∀ (x : IrrGL (w'.adicCompletion E')) ω, UpperTheory.Zero.LLC.Good x → HasCentralChar x.rep ω → ∀ σ, ((rc' x).eig σ).prod = (ω (a' σ) : ℂ)) ∧ (∀ (n : ℕ) (π π' : IrrRep (GL (Fin n) (w'.adicCompletion E'))), UpperTheory.Zero.LLC.Good (cls π) → Nonempty (π'.ρ.Equiv (contra π.ρ)) → rc' (cls π') = (rc' (cls π)).lpDual) ∧ (∀ x y, UpperTheory.Zero.LLC.Good y → rc' x = rc' y → x = y) := by
  first | (exact @GlobalTheory.LawsTTransport.lawsT_transport) | (exact GlobalTheory.LawsTTransport.lawsT_transport) | (intros; apply GlobalTheory.LawsTTransport.lawsT_transport  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceIsoCompatibleLocalLanglandsThreeStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.place_iso_compatible_local_langlands_three : ∀ (E E' Ω : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω] [Algebra E Ω] [Algebra E' Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (w' : HeightOneSpectrum (𝓞 E')) (h : IsPlaceOver A w) (h' : IsPlaceOver A w') (j : E →+* E') (i : w.adicCompletion E ≃+* w'.adicCompletion E'), GlobalTheory.LocLanglands.PlaceIso A w A w' (RingEquiv.refl Ω) j i → ∀ (rc : IrrGL (w.adicCompletion E) → WD h) (rc' : IrrGL (w'.adicCompletion E') → WD h'), (∀ x x', RepRel i x x' → WDRel (RingEquiv.refl Ω) (rc x) (rc' x')) → ∀ (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a), UpperTheory.Zero.LLC.LawsT a ha rc → ∀ (a' : Weil h' →* (w'.adicCompletion E')ˣ) (ha' : IsLocalArtin h' a'), (∀ x, (rc' x).lpDim = x.1) ∧ (∀ χ hχ, rc' (.ofChar χ hχ) = WD.lpOfChar h' (χ.comp a') (ha'.smooth hχ)) ∧ (∀ (l : List (Segment (w'.adicCompletion E'))) (x : IrrGL (w'.adicCompletion E')), IsL (l : Multiset (Segment (w'.adicCompletion E'))) x.rep → rc' x = segSum rc' l) ∧ (∀ x, x.IsCusp → IsIrrWD (rc' x)) ∧ (∀ x (s : ℝ), rc' (x.nu s) = (rc' x).lpTw s) := by
  first | (exact @GlobalTheory.LawsTTransport.lawsA_transport) | (exact GlobalTheory.LawsTTransport.lawsA_transport) | (intros; apply GlobalTheory.LawsTTransport.lawsA_transport  <;> assumption)
end

