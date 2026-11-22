import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0017
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0007
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsMvPolynomialOfPolyBoundOffHypersurface
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IntegralAndRationalOfPolynomialGrowth
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0116
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0148
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0002
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0014
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1170
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1182
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1173
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1181
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1183
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1167
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0239
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0081
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1185
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulEqOfPolynomialGrowth
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.CxPts

namespace GlobalTheory.SerreSections

theorem exists_ringHom_of_denominator {P A : Type*} [CommRing P] [CommRing A] (α : P →+* A) (e : P →+* ℂ) (q : P)
    (hq : e q ≠ 0) (hk : ∀ s, α s = 0 → e s = 0) (r : A → P) (hr : ∀ b, α q * b = α (r b)) :
    ∃ χ : A →+* ℂ, (∀ b, χ b = e (r b) / e q) ∧ ∀ s, χ (α s) = e s := by
  have hk' (s s' : P) (h : α s = α s') : e s = e s' :=
    sub_eq_zero.1 ((map_sub e s s').symm.trans (hk _ (by rw [map_sub, h, sub_self])))
  have h1 (s : P) : e (r (α s)) / e q = e s := by
    rw [div_eq_iff hq, ← map_mul]
    exact hk' _ _ (by rw [← hr, map_mul, mul_comm])
  refine ⟨{ toFun := fun b => e (r b) / e q, map_one' := ?_, map_mul' := fun a b => ?_,
            map_zero' := ?_, map_add' := fun a b => ?_ }, fun _ => rfl, h1⟩
  · simpa using h1 1
  · have := hk' (q * r (a * b)) (r a * r b) (by simp only [map_mul, ← hr]; ring)
    simp only [map_mul] at this
    field_simp
    linear_combination this
  · simpa using h1 0
  · rw [← add_div, ← map_add]
    congr 1
    exact hk' _ _ (by simp only [map_add, ← hr]; ring)

section Along

variable {Y : Scheme.{0}} {p : Y ⟶ Sp ℂ} {σ : ℂ →+* ℂ} {D : ℕ} {E : Type} [NormedAddCommGroup E]
  [NormedSpace ℂ E] {U : Y.Opens} {Z : Set E} {z : E} {s : E → CxPts p σ}

theorem exists_analyticAt_ev (hU : IsAffineOpen U) (hz : z ∈ Z) (hs : ∀ w ∈ Z, s w ∈ ptsIn p σ U)
    (hc : ContinuousWithinAt s Z z)
    (hd : ∀ a : Γ(Y, U), ∃ F : E → ℂ, AnalyticAt ℂ F z ∧ ∀ w ∈ Z, ev p σ U a (s w) = F w)
    {W : Y.Opens} (hW : s z ∈ ptsIn p σ W) (f : Γ(Y, W)) :
    ∃ F : E → ℂ, AnalyticAt ℂ F z ∧ ∀ᶠ w in 𝓝[Z] z, ev p σ W f (s w) = F w := by
  obtain ⟨h, hhW, hh⟩ := hU.exists_basicOpen_le (V := W) ⟨_, mem_ptsIn.1 hW⟩ (mem_ptsIn.1 (hs z hz))
  have hB : s z ∈ ptsIn p σ (Y.basicOpen h) := mem_ptsIn.2 hh
  have := hU.isLocalization_basicOpen h
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj h (resG Y hhW f)
  obtain ⟨Fa, hFa, ea⟩ := hd a
  obtain ⟨Fh, hFh, eh⟩ := hd h
  refine ⟨fun w => Fa w * (Fh w ^ n)⁻¹, hFa.mul ((hFh.pow n).inv (pow_ne_zero n
    (eh z hz ▸ (mem_ptsIn_basicOpen (hs z hz) h).1 hB))), ?_⟩
  filter_upwards [hc.preimage_mem_nhdsWithin ((isOpen_ptsIn _).mem_nhds hB), self_mem_nhdsWithin] with w hw hwZ
  have ha' : resG Y hhW f * resG Y (Y.basicOpen_le h) h ^ n = resG Y (Y.basicOpen_le h) a := ha
  have e := congrArg (evHom hw) ha'
  rw [map_mul, map_pow, ← ev_eq, ← ev_eq, ← ev_eq, ev_res _ hw, ev_res _ hw, ev_res _ hw] at e
  rw [← ea w hwZ, ← eh w hwZ]
  exact (eq_mul_inv_iff_mul_eq₀
    (pow_ne_zero n ((mem_ptsIn_basicOpen (ptsIn_mono (Y.basicOpen_le h) hw) h).1 hw))).2 e

theorem exists_analyticAt_holo (R : AnRead p σ D) (hU : IsAffineOpen U) (hz : z ∈ Z)
    (hs : ∀ w ∈ Z, s w ∈ ptsIn p σ U)
    (hd : ∀ a : Γ(Y, U), ∃ F : E → ℂ, AnalyticAt ℂ F z ∧ ∀ w ∈ Z, ev p σ U a (s w) = F w)
    {φ : CxPts p σ → ℂ} (hφ : R.HoloOn (ptsIn p σ U) φ) :
    ∃ F : E → ℂ, AnalyticAt ℂ F z ∧ ∀ᶠ w in 𝓝[Z] z, φ (s w) = F w := by
  have hc : ContinuousWithinAt s Z z := tendsto_subtype_rng.2
    (Points.tendsto_of_isAffineOpen hU (hs z hz) (eventually_of_mem self_mem_nhdsWithin hs) fun a => by
      obtain ⟨F, hF, e⟩ := hd a
      exact hF.continuousAt.continuousWithinAt.congr e (e z hz))
  obtain ⟨i, hi⟩ := R.cover (s z)
  set c := R.chart i
  choose F hF e using fun a => exists_analyticAt_ev hU hz hs hc hd (c.source_subset hi) (c.x a)
  let X : E → ReciprocityTheory.L2DbarEstimates.V D := fun w => (EuclideanSpace.equiv (Fin D) ℂ).symm fun a => F a w
  have hX : AnalyticAt ℂ X z :=
    ((EuclideanSpace.equiv (Fin D) ℂ).symm.analyticAt _).comp (analyticAt_pi_iff.2 hF)
  have hev : ∀ᶠ w in 𝓝[Z] z, s w ∈ c.e.source ∧ X w = c.e (s w) := by
    filter_upwards [eventually_all.2 e, hc.preimage_mem_nhdsWithin (c.e.open_source.mem_nhds hi)] with w h₁ h₂
    refine ⟨h₂, ?_⟩
    ext a
    exact (h₁ a).symm.trans (c.apply_eq _ h₂ a).symm
  have hG : AnalyticAt ℂ (φ ∘ c.e.symm) (X z) := by
    rw [(hev.self_of_nhdsWithin hz).2]
    exact SCV.analyticAt_of_differentiableOn (hφ i)
      ((ChartGlue.isOpen_over _ (isOpen_ptsIn U)).mem_nhds (ChartGlue.mem_over _ hi (hs z hz)))
  refine ⟨(φ ∘ c.e.symm) ∘ X, hG.comp hX, hev.mono fun w hw => ?_⟩
  simp only [Function.comp_apply, hw.2, c.e.left_inv hw.1]

end Along

theorem analyticAt_eval_map {d : ℕ} (r : Polynomial (MvPolynomial (Fin d) ℂ)) (z : (Fin d → ℂ) × ℂ) :
    AnalyticAt ℂ (fun w : (Fin d → ℂ) × ℂ => (r.map (MvPolynomial.eval w.1)).eval w.2) z :=
  SCV.analyticOnNhd_of_differentiable ((FiniteCoverGrowth.contDiff_eval_map r).differentiable one_ne_zero)
    univ z trivial

theorem exists_sum_norm_le {A : Type*} [CommRing A] {d n : ℕ} (j : MvPolynomial (Fin d) ℂ →+* A)
    (hj : j.IsIntegral) (u : Fin n → A) : ∃ (K : ℝ) (M : ℕ), ∀ (x : Fin d → ℂ) (χ : A →+* ℂ),
      χ.comp j = MvPolynomial.eval x → 1 + ∑ l, ‖χ (u l)‖ ≤ K * (1 + ‖x‖) ^ M := by
  choose s hs hs' using fun l => hj (u l)
  choose K M hK h using fun l => FiniteCoverGrowth.exists_norm_root_le (s l) (hs l)
  refine ⟨1 + ∑ l, K l, ∑ l, M l, fun x χ hχ => ?_⟩
  have h0 : (1 : ℝ) ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
  rw [add_mul, one_mul, Finset.sum_mul]
  refine add_le_add (one_le_pow₀ h0) (Finset.sum_le_sum fun l _ => (h l x _ ?_).trans ?_)
  · rw [Polynomial.eval_map, ← hχ, ← Polynomial.hom_eval₂, hs', map_zero]
  · exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h0
      (Finset.single_le_sum (f := M) (fun _ _ => Nat.zero_le _) (Finset.mem_univ l))) (hK l)

theorem exists_mul_eq_of_polynomial_growth : ∀ (Y : Scheme.{0}) (p : Y ⟶ Sp ℂ) (D : ℕ), SmoothOfRelativeDimension D p → ∀ (R : AnRead p (RingHom.id ℂ) D) (V : Y.Opens), IsAffineOpen V → IsDomain Γ(Y, V) → ∀ φ : CxPts p (RingHom.id ℂ) → ℂ, R.HoloOn (ptsIn p (RingHom.id ℂ) V) φ → ∀ (n : ℕ) (u : Fin n → Γ(Y, V)) (C : ℝ) (m : ℕ), (∀ y ∈ ptsIn p (RingHom.id ℂ) V, ‖φ y‖ ≤ C * (1 + ∑ l, ‖ev p (RingHom.id ℂ) V (u l) y‖) ^ m) → ∃ a b : Γ(Y, V), b ≠ 0 ∧ ∀ y ∈ ptsIn p (RingHom.id ℂ) V, ev p (RingHom.id ℂ) V b y * φ y = ev p (RingHom.id ℂ) V a y := by
  intro Y p D hs R V hV hd φ hφ n u C m hb
  classical
  have hsm : Smooth p := SmoothOfRelativeDimension.smooth D p
  have hc : (algX p V).FiniteType :=
    (HasRingHomProperty.appLE @LocallyOfFiniteType p inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ _).comp
      (RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).2)
  letI : Algebra ℂ Γ(Y, V) := (algX p V).toAlgebra
  haveI : Algebra.FiniteType ℂ Γ(Y, V) := hc
  obtain ⟨d, j, a, P, q, -, hinj, hfin, hP, -, hdvd, hq, hqP, hr⟩ := noetherNormalization_primitive Γ(Y, V)
  choose r hr using hr
  let α := Polynomial.eval₂RingHom j.toRingHom a
  let e (z : (Fin d → ℂ) × ℂ) := Polynomial.eval₂RingHom (MvPolynomial.eval z.1) z.2
  have he (z) (s) : e z s = (s.map (MvPolynomial.eval z.1)).eval z.2 := (Polynomial.eval_map _ _).symm
  have hα (f) : α (Polynomial.C f) = j f := Polynomial.eval₂_C _ _
  have heC (z) (f) : e z (Polynomial.C f) = MvPolynomial.eval z.1 f := Polynomial.eval₂_C _ _
  set Z : Set ((Fin d → ℂ) × ℂ) := {z | MvPolynomial.eval z.1 q ≠ 0 ∧
    (P.map (MvPolynomial.eval z.1)).eval z.2 = 0}
  have hχ (z) (hz : z ∈ Z) := exists_ringHom_of_denominator α (e z) (Polynomial.C q) (heC z q ▸ hz.1)
    (fun s h => by
      obtain ⟨t, rfl⟩ := (hdvd s).1 h
      rw [map_mul, he, hz.2, zero_mul]) r fun b => by rw [hα]; exact hr b
  choose χ hχ hχ' using hχ
  have hχj (z) (hz : z ∈ Z) (f) : χ z hz (j f) = MvPolynomial.eval z.1 f := by rw [← hα, hχ', heC]
  have hχc (z) (hz : z ∈ Z) (c : ℂ) : χ z hz (algX p V c) = RingHom.id ℂ c :=
    (congrArg _ (j.commutes c).symm).trans ((hχj z hz _).trans (MvPolynomial.eval_C _))
  have hb0 : j q * α P.derivative ≠ 0 := by
    have h0 : j q ≠ 0 := (map_ne_zero_iff _ hinj).2 hq
    refine mul_ne_zero h0 fun h => h0 ?_
    obtain ⟨v, w, hvw⟩ := Ideal.mem_span_pair.1 hqP
    rw [← hα, ← hvw, map_add, map_mul, map_mul, h, show α P = 0 from (hdvd P).2 dvd_rfl]
    simp
  rcases (ptsIn p (RingHom.id ℂ) V).eq_empty_or_nonempty with hE | ⟨y₀, -⟩
  · exact ⟨0, 1, one_ne_zero, by simp [hE]⟩
  let s (z : (Fin d → ℂ) × ℂ) : CxPts p (RingHom.id ℂ) :=
    if hz : z ∈ Z then ofHom hV (χ z hz) (hχc z hz) else y₀
  have hsV (z) (hz : z ∈ Z) : s z ∈ ptsIn p (RingHom.id ℂ) V := by
    simp only [s, dif_pos hz]; exact ofHom_mem _ _ _
  have hsv (z) (hz : z ∈ Z) (b) : ev p (RingHom.id ℂ) V b (s z) = χ z hz b := by
    simp only [s, dif_pos hz]; exact ev_ofHom _ _ _ b
  obtain ⟨K, M, hK⟩ := exists_sum_norm_le j.toRingHom hfin.to_isIntegral u
  obtain ⟨-, t, ht⟩ := FiniteCoverGrowth.integral_and_rational_of_polynomial_growth
    isConnected_and_dense_compl_hypersurface exists_mvPolynomial_of_poly_bound_off_hypersurface
    d (M * m) P q (fun z => φ (s z)) (|C| * K ^ m) hP hq hqP
    (fun z hz => exists_analyticAt_holo R hV hz hsV (fun b => ⟨fun w => e w (r b) / e w (Polynomial.C q), by
      simp only [he]
      exact (analyticAt_eval_map _ z).div (analyticAt_eval_map _ z) (by rw [← he, heC]; exact hz.1),
      fun w hw => (hsv w hw b).trans (hχ w hw b)⟩) hφ)
    fun z hz => by
      refine (hb _ (hsV z hz)).trans ?_
      simp only [hsv z hz]
      rw [mul_assoc, pow_mul, ← mul_pow]
      exact mul_le_mul (le_abs_self C) (pow_le_pow_left₀ (by positivity)
        (hK z.1 _ (RingHom.ext (hχj z hz))) m) (by positivity) (abs_nonneg C)
  refine ⟨j q * α t, j q * α P.derivative, hb0, fun y hy => ?_⟩
  simp only [ev_eq hy, map_mul]
  by_cases h0 : evHom hy (j q) = 0
  · simp [h0]
  let z : (Fin d → ℂ) × ℂ := (fun k => evHom hy (j (MvPolynomial.X k)), evHom hy a)
  have hj : (evHom hy).comp j.toRingHom = MvPolynomial.eval z.1 :=
    MvPolynomial.ringHom_ext (fun c => by
      rw [MvPolynomial.eval_C]
      exact (congrArg _ (j.commutes c)).trans ((ev_eq hy _).symm.trans (ev_algX hy c))) fun k => by simp [z]
  have hez (f) : evHom hy (α f) = e z f := by
    change _ = Polynomial.eval₂ _ _ _
    rw [← hj]
    exact Polynomial.hom_eval₂ _ _ _ _
  have hz : z ∈ Z := ⟨by rwa [← heC, ← hez, hα], by
    rw [← he, ← hez, show α P = 0 from (hdvd P).2 dvd_rfl, map_zero]⟩
  have hsz : s z = y := Subtype.ext (Points.ext_of_valR hV (hsV z hz) hy fun b => by
    refine (hsv z hz b).trans (Eq.trans ?_ (ev_eq hy b).symm)
    rw [hχ, ← hez, ← hez, hα, div_eq_iff h0, ← map_mul, mul_comm, hr]
    rfl)
  rw [mul_assoc, hez, hez, he, he, ← ht z hz, hsz]

end GlobalTheory.SerreSections
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormOfEqualGramTraceForms
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.UnitLemma.IsometryUnit

theorem isometry_unit : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K), B.P.Separable → ∀ (ε : B.A), (ε = 1 ∨ ε = -1) → ∀ (a : ℕ) (β β' : B.Aˣ), B.σ (β : B.A) = β * (ε * B.g) → B.σ (β' : B.A) = β' * (ε * B.g) → ∀ b b' : Module.Basis (Fin a) K.E B.A, (∀ i j, B.herm β (b i) (b j) = B.herm β' (b' i) (b' j)) → ∃ t : B.Aˣ, (β' : B.A) = β * (t * B.σ t) := by
  intro K B hs ε hε a β β' hβ hβ' b b' hgram
  have hs' : (LinearMap.mulLeft K.E B.g).charpoly.Separable := hs
  have σsm : ∀ (r : K.E) (y : B.A), B.σ (r • y) = K.c r • B.σ y := by
    intro r y; rw [Algebra.smul_def, map_mul, B.σ_alg, Algebra.smul_def]
  have trσ := GlobalTheory.UnitLemma.PairClass.trace_σ K B
  have addL : ∀ (x u u' v : B.A), B.herm x (u + u') v = B.herm x u v + B.herm x u' v := by
    intro x u u' v; unfold InvAlg.herm; rw [mul_add, add_mul, map_add]
  have subL : ∀ (x u u' v : B.A), B.herm x (u - u') v = B.herm x u v - B.herm x u' v := by
    intro x u u' v; unfold InvAlg.herm; rw [mul_sub, sub_mul, map_sub]
  have smulL : ∀ (x : B.A) (r : K.E) (u v : B.A), B.herm x (r • u) v = r * B.herm x u v := by
    intro x r u v; unfold InvAlg.herm; rw [mul_smul_comm, smul_mul_assoc, map_smul, smul_eq_mul]
  have addR : ∀ (x u v v' : B.A), B.herm x u (v + v') = B.herm x u v + B.herm x u v' := by
    intro x u v v'; unfold InvAlg.herm; rw [map_add, mul_add, map_add]
  have smulR : ∀ (x : B.A) (r : K.E) (u v : B.A), B.herm x u (r • v) = K.c r * B.herm x u v := by
    intro x r u v; unfold InvAlg.herm; rw [σsm, mul_smul_comm, map_smul, smul_eq_mul]

  have asym : ∀ (x : B.A), B.σ x = x * (ε * B.g) → ∀ z y, K.c (B.herm x z y) = B.herm x (ε * B.g * y) z := by
    intro x hx z y; unfold InvAlg.herm
    rw [← trσ]; congr 1; simp only [map_mul, B.σ_σ, hx]; ring

  have nd : ∀ x : B.A, (∀ y, Algebra.trace K.E B.A (x * y) = 0) → x = 0 :=
    fun x hx => GlobalTheory.UnitLemma.PairClass.trace_nondeg K.E B.A B.g hs' x hx
  have ndh : ∀ w : B.A, (∀ z, B.herm β w z = 0) → w = 0 := by
    intro w hw
    have h0 : (β : B.A) * w = 0 := nd _ (fun y => by
      have := hw (B.σ y); unfold InvAlg.herm at this; rwa [B.σ_σ] at this)
    have := congrArg (fun z => ((β⁻¹ : B.Aˣ) : B.A) * z) h0
    simpa [← mul_assoc] using this

  let φ : B.A ≃ₗ[K.E] B.A := b'.equiv b (Equiv.refl _)
  have hφb : ∀ i, φ (b' i) = b i := fun i => by simp [φ, Module.Basis.equiv_apply]
  have hφ : ∀ u v, B.herm β (φ u) (φ v) = B.herm β' u v := by
    let F₁ : B.A →ₗ[K.E] B.A →ₛₗ[(K.c : K.E →+* K.E)] K.E :=
      LinearMap.mk₂'ₛₗ (RingHom.id K.E) (K.c : K.E →+* K.E) (fun u v => B.herm β (φ u) (φ v))
        (fun u u' v => by rw [map_add, addL]) (fun r u v => by rw [map_smul, smulL]; rfl)
        (fun u v v' => by rw [map_add, addR]) (fun r u v => by rw [map_smul, smulR]; rfl)
    let F₂ : B.A →ₗ[K.E] B.A →ₛₗ[(K.c : K.E →+* K.E)] K.E :=
      LinearMap.mk₂'ₛₗ (RingHom.id K.E) (K.c : K.E →+* K.E) (fun u v => B.herm β' u v)
        (fun u u' v => addL _ _ _ _) (fun r u v => smulL _ _ _ _)
        (fun u v v' => addR _ _ _ _) (fun r u v => smulR _ _ _ _)
    have hF : F₁ = F₂ := LinearMap.ext_basis b' b' (fun i j => by
      simp only [F₁, F₂, LinearMap.mk₂'ₛₗ_apply, hφb]; exact hgram i j)
    intro u v
    have := LinearMap.congr_fun₂ hF u v
    simp only [F₁, F₂, LinearMap.mk₂'ₛₗ_apply] at this
    exact this
  have hcomm : ∀ u, φ (ε * B.g * u) = ε * B.g * φ u := by
    intro u
    rw [← sub_eq_zero]
    apply ndh
    intro z
    obtain ⟨v, rfl⟩ : ∃ v, φ v = z := ⟨φ.symm z, by simp⟩
    rw [subL, hφ, ← asym _ hβ', ← hφ, asym _ hβ, sub_self]
  have hg : ∀ u, φ (B.g * u) = B.g * φ u := by
    intro u
    rcases hε with rfl | rfl
    · simpa using hcomm u
    · have := hcomm u
      simp only [neg_mul, one_mul, map_neg, neg_inj] at this
      exact this
  have hpoly : ∀ q : K.E[X], ∀ u, φ (aeval B.g q * u) = aeval B.g q * φ u := by
    intro q
    induction q using Polynomial.induction_on with
    | C r => intro u; rw [aeval_C, ← Algebra.smul_def, ← Algebra.smul_def, map_smul]
    | add p q hp hq => intro u; rw [map_add, add_mul, add_mul, map_add, hp, hq]
    | monomial n r h =>
      intro u
      have e : aeval B.g (C r * X ^ (n + 1)) = aeval B.g (C r * X ^ n) * B.g := by
        simp [pow_succ, mul_assoc]
      rw [e, mul_assoc, h, hg, mul_assoc]
  have hmul : ∀ y, φ y = y * φ 1 := by
    intro y
    obtain ⟨q, rfl⟩ := GlobalTheory.UnitLemma.PairClass.exists_aeval_eq_of_separable B.g hs' y
    simpa using hpoly q 1
  have ht : IsUnit (φ 1) := by
    have := hmul (φ.symm 1)
    rw [LinearEquiv.apply_symm_apply] at this
    exact ⟨⟨φ 1, φ.symm 1, by rw [mul_comm]; exact this.symm, this.symm⟩, rfl⟩
  refine ⟨ht.unit, ?_⟩
  rw [IsUnit.unit_spec]
  rw [← sub_eq_zero]
  apply nd
  intro y
  have h1 := hφ y 1
  rw [hmul y] at h1
  unfold InvAlg.herm at h1
  rw [map_one B.σ, mul_one] at h1
  have h2 : ((β' : B.A) - β * (φ 1 * B.σ (φ 1))) * y = (β' : B.A) * y - β * (y * φ 1) * B.σ (φ 1) := by ring
  rw [h2, map_sub, h1, sub_self]

end GlobalTheory.UnitLemma.IsometryUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenIsDomainOfSmoothComplex
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts

namespace GlobalTheory

theorem exists_open_isDomain_of_smooth_complex :
    ∀ (Y : Scheme.{0}) (p : Y ⟶ Sp ℂ) (D : ℕ), SmoothOfRelativeDimension D p → ∀ x : Y,
      ∃ U : Y.Opens, x ∈ U ∧ ∀ V : Y.Opens, V ≤ U → x ∈ V → IsDomain Γ(Y, V) := by
  intro Y p D hp x
  have hs : Smooth p := SmoothOfRelativeDimension.smooth D p
  obtain ⟨-, hn, hl⟩ := isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field ℂ Y p hs
  have := IsNormalScheme.of_pred hn
  obtain ⟨U, hx, hU⟩ := GlobalTheory.ModelChart.exists_open_isDomain Y x
  exact ⟨U, hx, fun V hV hxV => hU V hxV hV⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPoincareGoodPatchOutsideOpen
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

set_option autoImplicit false

namespace GlobalTheory.GoodTop

theorem exists_goodPatch : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ}
    (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens)
    (H : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ),
    IsGood E O H → ∀ y ∉ ptsIn X.str σ O, ∃ e S A W c, y ∈ W ∧ GoodPatch E O H e S A W c := by
  intro F _ σ X m E O H hG y hy
  obtain ⟨e, S, hholo, hys, hy0, hcomp, A, hA, c, N, hev⟩ := hG y hy
  have h1 : ∀ᶠ z in 𝓝 y, z ∈ ptsIn X.str σ O → GoodBound S c N (fun v => H A (e.symm v) ()) (e z) :=
    (eventually_nhdsWithin_iff.1 hev).mono fun z hz hzO => hz hzO ()
  have h2 : ∀ᶠ z in 𝓝 y, A ∈ E.S (under z) := GlobalTheory.T.adaptedFrame_eventually_near_complexPoint E hA
  have h3 : ∀ᶠ z in 𝓝 y, z ∈ e.source := e.open_source.mem_nhds hys
  have h4 : ∀ᶠ z in 𝓝 y, ∀ a ∈ S, ‖e z a‖ ≤ 1 / 2 := by
    refine (Filter.eventually_all_finset S).2 fun a ha => ?_
    have hc : ContinuousAt (fun z => e z a) y :=
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin X.dim => ℂ) a).continuous.comp
        (PiLp.continuous_ofLp 2 _)).continuousAt.comp (e.continuousAt hys)
    have h0 : e y a = 0 := hy0 a ha
    have : ∀ᶠ z in 𝓝 y, e z a ∈ Metric.ball (0 : ℂ) (1 / 2) :=
      hc.preimage_mem_nhds (by rw [h0]; exact Metric.ball_mem_nhds _ (by norm_num))
    exact this.mono fun z hz => le_of_lt (by simpa using hz)
  obtain ⟨W, hW, hWo, hyW⟩ := eventually_nhds_iff.1 (h1.and (h2.and (h3.and h4)))
  refine ⟨e, S, A, W, c, hyW, ?_⟩
  exact
  { holo := hholo
    isOpen := hWo
    sub := fun z hz => (hW z hz).2.2.1
    frame := fun z hz => (hW z hz).2.1
    small := fun z hz => (hW z hz).2.2.2
    mem := fun z hz => by
      have := hcomp z (hW z hz).2.2.1
      constructor
      · intro hzO a ha h
        exact (this.2 ⟨a, ha, h⟩) hzO
      · intro hne
        by_contra hzO
        obtain ⟨a, ha, h⟩ := this.1 hzO
        exact hne a ha h
    form := fun z hz hzO a i j => ((hW z hz).1 hzO).form a i j
    dbar := fun z hz hzO a b i j => ((hW z hz).1 hzO).dbar a b i j }

end GlobalTheory.GoodTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointLocalRingClosedPointCentreOfPlaceStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pointLocalRing_closedPoint_centre_of_place : ∀ {κ' : Type} [Field κ'] [Algebra ℂ κ'] (F : Place (algebraMap ℂ κ')) (A : Subalgebra ℂ κ'),
    Algebra.Smooth ℂ A → A.toSubring ≤ F.ring.toSubring →
    (∀ f : κ', ∃ a ∈ A, ∃ b ∈ A, b ≠ 0 ∧ f * b = a) →
    ∃ (B : Subring κ') (hB : IsLocModel (algebraMap ℂ κ') B), RatRes (algebraMap ℂ κ') B ∧
      A.toSubring ≤ B ∧ B ≤ F.ring.toSubring ∧
      ((algebraMap ℂ κ').codRestrict B hB.const_mem).FormallySmooth := by
  first | exact @GlobalTheory.FieldPair.exists_locRing_closedPoint_centre | exact GlobalTheory.FieldPair.exists_locRing_closedPoint_centre | (intros; apply GlobalTheory.FieldPair.exists_locRing_closedPoint_centre <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolynomialChernIntegralTensPow
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory.ChernPoly

theorem chernInt_tens_pow_poly : ∀ (Y : Var ℂ) (L H : LB Y.X) (φ : Weight Y.str (RingHom.id ℂ) L)
    (ψ : Weight Y.str (RingHom.id ℂ) H), φ.IsCInf → ψ.IsCInf → ∃ P : Polynomial ℝ,
      P.eval 0 = Weight.chernInt φ Y.dim Set.univ (fun _ => 1) ∧ ∀ m : ℕ,
        Weight.chernInt (φ.tens (ψ.pow m)) Y.dim Set.univ (fun _ => 1) = P.eval (m : ℝ) := by
  intro Y L H φ ψ hφ hψ
  obtain ⟨hc, ht, _, A, hA⟩ := GlobalTheory.T.complexPoints_smoothProjVariety_compact_manifold Y
  have := hc
  have := ht

  have hφs : φ.IsSmooth (AnRead.all Y.str (RingHom.id ℂ) Y.dim) :=
    (Weight.isCInf_iff_isSmooth _).1 hφ
  have hψs : ψ.IsSmooth (AnRead.all Y.str (RingHom.id ℂ) Y.dim) :=
    (Weight.isCInf_iff_isSmooth _).1 hψ
  have hΦ : IsPotential A φ.locPot := hφs.isPotential hA
  have hΨ : IsPotential A ψ.locPot := hψs.isPotential hA

  obtain ⟨P, hP⟩ := GlobalTheory.T.exists_polynomial_mongeAmpereMass_add_zsmul Y.dim _ A (fun _ => φ.locPot) (fun _ => ψ.locPot)
    (fun _ => hΦ) (fun _ => hΨ)

  refine ⟨P, ?_, fun m => ?_⟩
  · rw [(GlobalTheory.T.chernIntegral_one_eq_mongeAmpereIntegral Y L φ hφ).2 A hA, ← (by simpa using hP 0 :
      mInt A (fun _ => φ.locPot + ψ.locPot.zsmul 0) (fun _ => 1) = P.eval 0)]
    refine SameForm.mInt_eq (fun _ => ?_) _
    refine (Weight.sameForm_of_eq φ hA (isPotentialAdd A _ _ hΦ (isPotentialZsmul A 0 _ hΨ))
      (fun x => ⟨pick φ.isLB x, mem_pick φ.isLB x, fun z => ?_⟩)).symm
    show φ.φ (pick φ.isLB x) z / 2 = φ.locPot.φ x z + ((0 : ℤ) : ℝ) * ψ.locPot.φ x z
    rw [Weight.locPot_φ]
    simp
  · have hT : (φ.tens (ψ.pow m)).IsCInf := hφ.tens (hψ.zpow m)
    rw [(GlobalTheory.T.chernIntegral_one_eq_mongeAmpereIntegral Y _ _ hT).2 A hA, show ((m : ℕ) : ℝ) = (((m : ℕ) : ℤ) : ℝ) by push_cast; rfl,
      ← hP m]
    refine SameForm.mInt_eq (fun _ => ?_) _
    refine Weight.sameForm_of_eq _ hA (isPotentialAdd A _ _ hΦ (isPotentialZsmul A m _ hΨ))
      (fun x => ⟨(pick φ.isLB x, fun _ => pick ψ.isLB x),
        mem_ptsIn_inf.2 ⟨mem_pick φ.isLB x, mem_pow_iff.2 (mem_pick ψ.isLB x)⟩, fun z => ?_⟩)
    show (φ.φ (pick φ.isLB x) z + (ψ.zpow m).φ (fun _ => pick ψ.isLB x) z) / 2 =
      φ.locPot.φ x z + ((m : ℤ) : ℝ) * ψ.locPot.φ x z
    rw [Weight.zpow_φ, Weight.locPot_φ, Weight.locPot_φ]
    ring

end GlobalTheory.ChernPoly
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalBudgetsTwoPointInductionStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_budgets_twoPointInduction : ∀ (n r : ℕ) (c : ℕ → ℝ), 0 < r → (∀ e ∈ Finset.Icc 1 n, 0 < c e) → ∑ e ∈ Finset.Icc 1 n, (2 : ℝ) ^ (1 / (e : ℝ)) * e / c e ≤ 1 → ∃ (h : ℕ → ℚ), (∀ e, 0 < h e) ∧ ∑ e ∈ Finset.Icc 1 n, h e < 1 / (r : ℚ) ∧ ∀ e ∈ Finset.Icc 1 n, ∀ t : ℤ, c e ^ e < (t : ℝ) / (r : ℝ) ^ e → 2 * (e : ℚ) ^ e < h e ^ e * t := by
  first | exact @GlobalTheory.PairStep.exists_rat_budgets | exact GlobalTheory.PairStep.exists_rat_budgets | (intros; apply GlobalTheory.PairStep.exists_rat_budgets <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalFrameCoordsOfMemTorusLatticeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_frameCoords_of_mem_torusLattice : ∀ {D : D7} (S T : HSp D) (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1 → ∀ δ : ℂ, ∀ x ∈ Formalism.MainNotions.TaylorLogMetric.La D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (Formalism.MainNotions.StandardLatticesGL3.stdL D S.rank) (Formalism.MainNotions.StandardLatticesGL3.stdL D T.rank), ∃ v : Matrix (Fin T.rank) (Fin S.rank) D.host.E, GlobalTheory.VacUnique.finRat S T v ∈ latO S T (colLat frS : Set (Fin S.rank → D.host.E)) (colLat frT : Set (Fin T.rank → D.host.E)) (fun _ => True) ∧ x = δ • (fun τ a b => ((GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (GlobalTheory.VacUnique.infRat S T v τ) * GlobalTheory.FockPos.frAt frS τ) a b) := by
  first | exact @GlobalTheory.ThetaLawLat.mem_La_frame | exact GlobalTheory.ThetaLawLat.mem_La_frame | (intros; apply GlobalTheory.ThetaLawLat.mem_La_frame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealChartAdeleTensorAdmissibleCMBaseStatement
section
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_realChart_adeleTensor_admissibleCMBase : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ),
      IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ → ∃ ι : (InfinitePlace F → ℂ) →+ AEF F E, IsChartF θ ι := by
  first | exact @GlobalTheory.RealWeilF.CMChart.exists_chartF | exact GlobalTheory.RealWeilF.CMChart.exists_chartF | (intros; apply GlobalTheory.RealWeilF.CMChart.exists_chartF <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitRootCyclotomicExpExpansionsStatement
section
open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_root_cyclotomicExpExpansions : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l), l ≠ 2 → (∃ ζ : ↥LL.1, IsPrimitiveRoot ζ l) → ∃ (u : ℤ_[l]ˣ) (c : ℤ_[l]) (ζ : ↥(OL LL)) (jj : ℕ → PowerSeries ↥(OL LL) →+* PowerSeries ↥LL.1), (u : ℤ_[l]) = 1 + (l : ℤ_[l]) * c ∧ IsUnit c ∧ IsPrimitiveRoot ζ l ∧ ζ - 1 ∈ maximalIdeal ↥(OL LL) ∧ ∀ b ∈ Finset.Ioo 0 l, IsLocExp l ↥(OL LL) ↥LL.1 (OL LL).val.toRingHom (ζ ^ b - 1) (u : ℤ_[l]) (jj b) ∧ IsExpAt (OL LL).val.toRingHom (ζ ^ b) (jj b) := by
  first | exact @GlobalTheory.WachExp.exists_locExp_expAt | exact GlobalTheory.WachExp.exists_locExp_expAt | (intros; apply GlobalTheory.WachExp.exists_locExp_expAt <;> assumption)
end

