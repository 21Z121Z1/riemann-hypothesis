import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.ArithDegreeExact
import GroundTheory.HeightsAndTheta.Heights.Slopes
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0055
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0054
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0042
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0035
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0038
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0053
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0050
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0044

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HermitianBundleQuotientDegreeBound
section
open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PtBoundary

variable {K : Type} [Field K] [NumberField K]

theorem finrank_submodule_of_torsion {R M : Type*} [CommRing R] [IsDomain R] [AddCommGroup M]
    [Module R M] (N : Submodule R M) (h : ∀ x : M, ∃ a : R, a ≠ 0 ∧ a • x ∈ N) :
    Module.finrank R N = Module.finrank R M := by
  have h0 : Module.rank R (M ⧸ N) = 0 := by
    rw [rank_eq_zero_iff]
    intro x
    obtain ⟨x, rfl⟩ := N.mkQ_surjective x
    obtain ⟨a, ha, hax⟩ := h x
    refine ⟨a, ha, ?_⟩
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hax
  have h1 := rank_quotient_add_rank_of_isDomain N
  rw [h0, zero_add] at h1
  simp only [Module.finrank, h1]

theorem saturated_ker (E E' : HermitianBundle.{0} K) (q : E.carrier →ₗ[𝓞 K] E'.carrier) :
    E.Saturated (LinearMap.ker q) := by
  intro a x ha hx
  rw [LinearMap.mem_ker, map_smul] at hx
  rw [LinearMap.mem_ker]
  have : Module.IsTorsionFree (𝓞 K) E'.carrier := inferInstance
  exact (smul_eq_zero.mp hx).resolve_left ha

def barMap (E E' : HermitianBundle.{0} K) (P : Submodule (𝓞 K) E.carrier) (hP : E.Saturated P)
    (q : E.carrier →ₗ[𝓞 K] E'.carrier) (hq : P ≤ LinearMap.ker q) :
    (E.quot P hP).carrier →ₗ[𝓞 K] E'.carrier :=
  P.liftQ q hq

theorem sqAt_barMap_le (E E' : HermitianBundle.{0} K) (P : Submodule (𝓞 K) E.carrier)
    (hP : E.Saturated P) (q : E.carrier →ₗ[𝓞 K] E'.carrier) (hq : P ≤ LinearMap.ker q) (c : ℝ)
    (h : ∀ (σ : K →+* ℂ) (x : Fibre σ E.carrier),
      sqAt E' σ (q.lTensor (ComplexAt σ) x) ≤ c * sqAt E σ x)
    (σ : K →+* ℂ) (y : Fibre σ (E.quot P hP).carrier) :
    sqAt E' σ ((barMap E E' P hP q hq).lTensor (ComplexAt σ) y) ≤
      c * sqAt (E.quot P hP) σ y := by
  letI := HermitianBundle.quot_projective hP
  let V := subFibre E.metric σ P
  let y' : Fibre σ (E.carrier ⧸ P) := y
  let s : Fibre σ E.carrier := fibreMap σ (HermitianBundle.quotSection E P hP) y'
  let v : FibreSpace E.metric σ := HermitianBundle.quotFibreMap E P hP σ y
  let x : Fibre σ E.carrier := (FibreSpace.equiv E.metric σ).symm v
  have hvx : FibreSpace.equiv E.metric σ x = v := by simp [x]
  have hdiff : FibreSpace.equiv E.metric σ s - v ∈ V := by
    have hv : v = Vᗮ.starProjection (FibreSpace.equiv E.metric σ s) := rfl
    have e : Vᗮ.starProjection (FibreSpace.equiv E.metric σ s) =
        FibreSpace.equiv E.metric σ s - V.starProjection (FibreSpace.equiv E.metric σ s) := by
      rw [Submodule.starProjection_orthogonal']
      rfl
    rw [hv, e, sub_sub_cancel]
    exact V.starProjection_apply_mem _
  obtain ⟨w, hw⟩ := hdiff
  have hw' : fibreMap σ P.subtype w = s - x := by
    apply (FibreSpace.equiv E.metric σ).injective
    rw [map_sub, hvx]
    exact hw
  have hsub : q ∘ₗ P.subtype = 0 := by
    ext z
    exact hq z.2
  have hsec : q ∘ₗ HermitianBundle.quotSection E P hP = P.liftQ q hq := by
    have h1 : P.liftQ q hq ∘ₗ P.mkQ = q := Submodule.liftQ_mkQ P q hq
    calc q ∘ₗ HermitianBundle.quotSection E P hP
        = P.liftQ q hq ∘ₗ (P.mkQ ∘ₗ HermitianBundle.quotSection E P hP) := by
          rw [← LinearMap.comp_assoc, h1]
      _ = P.liftQ q hq := by
          rw [HermitianBundle.mkQ_comp_quotSection, LinearMap.comp_id]
  have hqx : (barMap E E' P hP q hq).lTensor (ComplexAt σ) y = q.lTensor (ComplexAt σ) x := by
    have h1 : fibreMap σ q s = (barMap E E' P hP q hq).lTensor (ComplexAt σ) y := by
      have h0 : fibreMap σ q s = fibreMap σ (P.liftQ q hq) y' :=
        (fibreMap_fibreMap σ q (HermitianBundle.quotSection E P hP) y').trans
          (congrArg (fun f => fibreMap σ f y') hsec)
      exact h0
    have h2 : fibreMap σ q (s - x) = 0 := by
      rw [← hw', fibreMap_fibreMap, hsub]
      simp [fibreMap]
    rw [map_sub, h1] at h2
    exact sub_eq_zero.mp h2
  have hnorm : sqAt (E.quot P hP) σ y = sqAt E σ x := by
    have h1 : sqAt E σ x = (inner ℂ (FibreSpace.equiv E.metric σ x) (FibreSpace.equiv E.metric σ x)).re := rfl
    rw [h1, hvx]
    rfl
  rw [hqx, hnorm]
  exact h σ x

theorem normDegree_top_eq (E : HermitianBundle.{0} K) :
    E.normDegree ⊤ = E.arithDegree / Module.finrank ℚ K := by
  rw [HermitianBundle.normDegree, HermitianBundle.degree_top_eq_arithDegree]

theorem final_real (C L ρ m x g : ℝ) (hC : 1 ≤ C) (hL : 0 ≤ L) (hρ : 0 ≤ ρ) (hm : 0 ≤ m) (hx : 0 ≤ x) (hg : 0 ≤ g)
    (hρg : ρ ≤ g) (hmx : m ≤ x + g * L) :
    C * Real.log (2 + ρ + m) + L / 2 ≤
      (C + g + g * L + L) * Real.log (2 + (C + g + g * L + L) + x) + (C + g + g * L + L) := by
  have hgL : 0 ≤ g * L := mul_nonneg hg hL
  set C' := C + g + g * L + L with hC'
  have h1 : 2 + ρ + m ≤ 2 + C' + x := by rw [hC']; linarith
  have h0 : 0 < 2 + ρ + m := by linarith
  have h2 : Real.log (2 + ρ + m) ≤ Real.log (2 + C' + x) := Real.log_le_log h0 h1
  have h3 : 0 ≤ Real.log (2 + ρ + m) := Real.log_nonneg (by linarith)
  have h4 : C ≤ C' := by rw [hC']; linarith
  have h5 : C * Real.log (2 + ρ + m) ≤ C' * Real.log (2 + C' + x) :=
    mul_le_mul h4 h2 h3 (by linarith)
  have h6 : L / 2 ≤ C' := by rw [hC']; linarith
  linarith

theorem slopeMax_le_log : ∀ (g : ℕ) (C : ℝ), 1 ≤ C → ∃ C' : ℝ, 0 ≤ C' ∧ ∀ (K : Type) [Field K] [NumberField K] (E E' : HermitianBundle.{0} K) (r : ℕ) (ε : Fin r → E.carrier) (q : E.carrier →ₗ[𝓞 K] E'.carrier), Module.finrank (𝓞 K) E.carrier = g → LinearIndependent (𝓞 K) ε → LinearMap.ker q = Submodule.span (𝓞 K) (Set.range ε) → (∀ e' : E'.carrier, ∃ (a : 𝓞 K) (e : E.carrier), a ≠ 0 ∧ q e = a • e') → (∀ (σ : K →+* ℂ) (w : Fin r → ℂ), C⁻¹ * ∑ a, ‖w a‖ ^ 2 ≤ sqAt E σ (∑ a, ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 K] ε a) ∧ sqAt E σ (∑ a, ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 K] ε a) ≤ C * ∑ a, ‖w a‖ ^ 2) → (∀ (σ : K →+* ℂ) (x : Fibre σ E.carrier), sqAt E' σ (q.lTensor (ComplexAt σ) x) ≤ C * sqAt E σ x) → E'.slopeMax ≤ ((C * Real.log (2 + Module.finrank (𝓞 K) E'.carrier + max (-E'.normDegree ⊤) 0) : ℝ) : EReal) → E.slopeMax ≤ ((C' * Real.log (2 + C' + max (-E.normDegree ⊤) 0) + C' : ℝ) : EReal) := by
  intro g C hC
  have hC0 : 0 < C := by linarith
  have hL : 0 ≤ Real.log C := Real.log_nonneg hC
  refine ⟨C + g + g * Real.log C + Real.log C, by positivity, ?_⟩
  intro K _ _ E E' r ε q hg hli hker hfull hgram hexp hslope
  set L := Real.log C with hLdef
  set P : Submodule (𝓞 K) E.carrier := Submodule.span (𝓞 K) (Set.range ε) with hPdef
  have hP : E.Saturated P := hker ▸ saturated_ker E E' q
  have hPq : P ≤ LinearMap.ker q := hker.ge
  set X := HermitianBundle.subQuotExtension E P hP with hX
  set φ := barMap E E' P hP q hPq with hφ
  have hφinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ hker.le
  have hφq : ∀ e, φ (P.mkQ e) = q e := fun e => rfl

  let b : Module.Basis (Fin r) (𝓞 K) (E.sub P).carrier := Module.Basis.span hli
  have hb : ∀ (σ : K →+* ℂ) (w : Fin r → ℂ),
      sqAt (E.sub P) σ (∑ a, ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 K] b a) =
        sqAt E σ (∑ a, ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 K] ε a) := by
    intro σ w
    have h1 : X.incl.lTensor (ComplexAt σ) (∑ a, ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 K] b a) =
        ∑ a, ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 K] ε a := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [LinearMap.lTensor_tmul]
      congr 1
      exact congrArg Subtype.val (Module.Basis.span_apply hli a)
    rw [← h1]
    simp only [sqAt]
    rw [X.incl_isometric]
  obtain ⟨hP1, hP2⟩ := GlobalTheory.T.slope_bound_comparable_metric K (E.sub P) r b C hC (fun σ w => by rw [hb]; exact hgram σ w)

  obtain ⟨hQ1, hQ2⟩ := GlobalTheory.T.normalized_degree_bounded_map K (E.quot P hP) E' φ C hφinj hC0
    (fun σ y => sqAt_barMap_le E E' P hP q hPq C hexp σ y)

  have hrP : Module.finrank (𝓞 K) (E.sub P).carrier = r := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  have hrk := X.finrank_eq
  have hrange : Module.finrank (𝓞 K) ((⊤ : Submodule (𝓞 K) (E.quot P hP).carrier).map φ) =
      Module.finrank (𝓞 K) E'.carrier := by
    apply finrank_submodule_of_torsion
    intro e'
    obtain ⟨a, e, ha, he⟩ := hfull e'
    exact ⟨a, ha, he ▸ ⟨P.mkQ e, trivial, hφq e⟩⟩
  have hrQ : Module.finrank (𝓞 K) (E.quot P hP).carrier = Module.finrank (𝓞 K) E'.carrier := by
    rw [← hrange, Submodule.map_top]
    exact (LinearMap.finrank_range_of_inj hφinj).symm
  have hsum : r + Module.finrank (𝓞 K) E'.carrier = g := by
    rw [← hg, hrk, hrP, hrQ]
  obtain ⟨hI1, -⟩ := GlobalTheory.T.normalized_degree_full_rank_sublattice K E' ((⊤ : Submodule (𝓞 K) (E.quot P hP).carrier).map φ) hrange

  have hdeg : E.normDegree ⊤ = (E.sub P).normDegree ⊤ + (E.quot P hP).normDegree ⊤ := by
    rw [normDegree_top_eq, normDegree_top_eq, normDegree_top_eq, X.arithDegree_eq_add, add_div]
  have hQd := hQ1 ⊤
  have hrkTop : (E.quot P hP).rank ⊤ = Module.finrank (𝓞 K) E'.carrier := by
    rw [HermitianBundle.rank, finrank_top, hrQ]
  rw [hrkTop] at hQd
  set ρ : ℕ := Module.finrank (𝓞 K) E'.carrier with hρ
  have hsumR : (r : ℝ) + ρ = g := by exact_mod_cast hsum
  have hP2' := (abs_le.mp hP2).2
  have hgL : (g : ℝ) * L = r * L + ρ * L := by rw [← hsumR]; ring
  have hrL : 0 ≤ (r : ℝ) * L := by positivity
  have hρL : 0 ≤ (ρ : ℝ) * L := by positivity
  have hm : max (-E'.normDegree ⊤) 0 ≤ max (-E.normDegree ⊤) 0 + g * L := by
    apply max_le
    · have := le_max_left (-E.normDegree ⊤) 0
      nlinarith
    · have := le_max_right (-E.normDegree ⊤) 0
      nlinarith
  have hreal := final_real C L ρ (max (-E'.normDegree ⊤) 0) (max (-E.normDegree ⊤) 0) g hC hL
    (by positivity) (le_max_right _ _) (le_max_right _ _) (by positivity)
    (by have : (0 : ℝ) ≤ r := by positivity
        linarith) hm
  have hfirst : L / 2 ≤ (C + g + g * L + L) * Real.log (2 + (C + g + g * L + L) + max (-E.normDegree ⊤) 0) + (C + g + g * L + L) := by
    have h0 : (0 : ℝ) ≤ g := by positivity
    have h1 : 0 ≤ (C + g + g * L + L) := by positivity
    have h2 : 0 ≤ Real.log (2 + (C + g + g * L + L) + max (-E.normDegree ⊤) 0) :=
      Real.log_nonneg (by have := le_max_right (-E.normDegree ⊤) 0; linarith)
    have h3 := mul_nonneg h1 h2
    nlinarith
  refine (SlopeMaxExtension.main K _ _ _ X).trans (max_le ?_ ?_)
  · exact hP1.trans (by exact_mod_cast hfirst)
  · refine hQ2.trans ((add_le_add_left hslope _).trans ?_)
    rw [← EReal.coe_add]
    exact_mod_cast hreal

end GlobalTheory.CompanionTheory.Ar.PtBoundary

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsotropicQuotientStructure
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Univ.QuotLat

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]

theorem orth_of_set {m : ℕ} {T : Set (Fin m → ℂ)} {H : Matrix (Fin m) (Fin m) ℂ} {z : Fin m → ℂ}
    (h : ∀ t ∈ T, z ⬝ᵥ H *ᵥ star t = 0) : ∀ s ∈ Submodule.span ℂ T, z ⬝ᵥ H *ᵥ star s = 0 := by
  intro s hs
  induction hs using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simp
  | add x y _ _ hx hy => simp [star_add, mulVec_add, dotProduct_add, hx, hy]
  | smul a x _ hx => simp [star_smul, mulVec_smul, dotProduct_smul, hx]

theorem span_period (R : RiemLat E g Λ) {I : Submodule (𝓞 E) Λ} {k : ℕ} {e : Fin k → Λ}
    (hI : ∀ v, v ∈ I ↔ v ∈ Submodule.span ℤ (Set.range e)) :
    Submodule.span ℂ (R.P '' I) = Submodule.span ℂ (Set.range fun i => R.P (e i)) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨v, hv, rfl⟩
    have hv' := (hI v).1 hv
    show R.P v ∈ Submodule.span ℂ (Set.range fun i => R.P (e i))
    induction hv' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact Submodule.subset_span ⟨i, rfl⟩
    | zero => simp
    | add x y hx' hy' hx hy =>
      rw [map_add]
      exact Submodule.add_mem _ (hx ((hI x).2 hx')) (hy ((hI y).2 hy'))
    | smul a x hx' hx =>
      rw [map_zsmul]
      exact Submodule.smul_of_tower_mem _ a (hx ((hI x).2 hx'))
  · refine Submodule.span_mono ?_
    rintro _ ⟨i, rfl⟩
    exact ⟨e i, (hI _).2 (Submodule.subset_span ⟨i, rfl⟩), rfl⟩

theorem im_quot (R : RiemLat E g Λ) {I : Submodule (𝓞 E) Λ} {k : ℕ} {e : Fin k → Λ}
    (hI : ∀ v, v ∈ I ↔ v ∈ Submodule.span ℤ (Set.range e)) (hiso : IsIsoSub R.form I)
    (hLI : LinearIndependent ℂ fun i => R.P (e i)) {g' : ℕ} (q : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ))
    (hk : LinearMap.ker q = Submodule.span ℂ (R.P '' I)) (H' : Matrix (Fin g') (Fin g') ℂ)
    (hm : ∀ a b, (∀ v ∈ I, R.ip (R.P v) a = 0) → q b ⬝ᵥ H' *ᵥ star (q a) = b ⬝ᵥ R.Hm *ᵥ star a)
    {x y : Λ} (hx : ∀ v ∈ I, R.form x v = 0) (hy : ∀ v ∈ I, R.form y v = 0) :
    (q (R.P x) ⬝ᵥ H' *ᵥ star (q (R.P y))).im = R.form x y := by
  have heI : ∀ i, e i ∈ I := fun i => (hI _).2 (Submodule.subset_span ⟨i, rfl⟩)
  have hui : ∀ i j, (R.P (e i) ⬝ᵥ R.Hm *ᵥ star (R.P (e j))).im = 0 := fun i j => by
    rw [R.im, hiso _ (heI i) _ (heI j)]; simp
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_real_orthogonal_projection_of_real_gram g k R.Hm R.pos _ hLI (GlobalTheory.T.exists_hermitian_orthogonal_projection g k R.Hm R.pos _ hLI) hui (R.P y) (fun j => by
    rw [R.im, hy _ (heI j)]; simp)
  set s : Fin g → ℂ := ∑ i, (c i : ℂ) • R.P (e i) with hs
  have hsk : q s = 0 := by
    have : s ∈ LinearMap.ker q := by
      rw [hk, span_period R hI]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    exact this
  have hqy : q (R.P y - s) = q (R.P y) := by rw [map_sub, hsk, sub_zero]
  have horth : ∀ v ∈ I, R.ip (R.P v) (R.P y - s) = 0 := by
    intro v hv
    have hv' : R.P v ∈ Submodule.span ℂ (Set.range fun i => R.P (e i)) := by
      rw [← span_period R hI]; exact Submodule.subset_span ⟨v, hv, rfl⟩
    refine orth_of_set (T := Set.range fun i => R.P (e i)) ?_ _ hv'
    rintro _ ⟨j, rfl⟩
    exact hc j
  rw [← hqy, hm _ _ horth]
  have hxs : (R.P x ⬝ᵥ R.Hm *ᵥ star s).im = 0 := by
    simp only [hs, star_sum, star_smul, mulVec_sum, mulVec_smul, dotProduct_sum, dotProduct_smul,
      smul_eq_mul, Complex.im_sum, Complex.star_def, Complex.conj_ofReal, Complex.im_ofReal_mul, R.im,
      hx _ (heI _)]
    simp
  rw [star_sub, mulVec_sub, dotProduct_sub, Complex.sub_im, hxs, sub_zero, R.im]

theorem period_facts (R : RiemLat E g Λ) {I : Submodule (𝓞 E) Λ} {k n : ℕ} (b : Module.Basis (Fin n) ℤ Λ)
    (f : Fin k → Fin n) (hf : Function.Injective f)
    (hI : ∀ v, v ∈ I ↔ v ∈ Submodule.span ℤ (Set.range fun i => b (f i))) (hiso : IsIsoSub R.form I) :
    LinearIndependent ℂ fun i => R.P (b (f i)) := by
  have heI : ∀ i, b (f i) ∈ I := fun i => (hI _).2 (Submodule.subset_span ⟨i, rfl⟩)
  refine GlobalTheory.T.linearIndependent_complex_of_real_hermitian g k R.Hm R.pos _ ((GlobalTheory.T.linearIndependent_real_periods_basis E g Λ R n b).comp f hf) fun i j => ?_
  rw [R.im, hiso _ (heI i) _ (heI j)]; simp

theorem exists_orth (R : RiemLat E g Λ) {I : Submodule (𝓞 E) Λ} {k : ℕ} {e : Fin k → Λ}
    (hI : ∀ v, v ∈ I ↔ v ∈ Submodule.span ℤ (Set.range e))
    (hLI : LinearIndependent ℂ fun i => R.P (e i)) (z : Fin g → ℂ) :
    ∃ s ∈ Submodule.span ℂ (R.P '' I), ∀ v ∈ Submodule.span ℂ (R.P '' I), (z - s) ⬝ᵥ R.Hm *ᵥ star v = 0 := by
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_hermitian_orthogonal_projection g k R.Hm R.pos _ hLI z
  rw [span_period R hI]
  refine ⟨∑ i, c i • R.P (e i), Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ (c i) (Submodule.subset_span ⟨i, rfl⟩), ?_⟩
  refine orth_of_set ?_
  rintro _ ⟨j, rfl⟩
  exact hc j

theorem mem_of_mem_span (R : RiemLat E g Λ) {I : Submodule (𝓞 E) Λ} {k n : ℕ} (b : Module.Basis (Fin n) ℤ Λ)
    (f : Fin k → Fin n) (hf : Function.Injective f)
    (hI : ∀ v, v ∈ I ↔ v ∈ Submodule.span ℤ (Set.range fun i => b (f i))) (hiso : IsIsoSub R.form I)
    {x : Λ} (hx : ∀ v ∈ I, R.form x v = 0) (hs : R.P x ∈ Submodule.span ℂ (R.P '' I)) : x ∈ I := by
  have heI : ∀ i, b (f i) ∈ I := fun i => (hI _).2 (Submodule.subset_span ⟨i, rfl⟩)
  have hLI := period_facts R b f hf hI hiso
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_real_orthogonal_projection_of_real_gram g k R.Hm R.pos _ hLI (GlobalTheory.T.exists_hermitian_orthogonal_projection g k R.Hm R.pos _ hLI) (fun i j => by
    rw [R.im, hiso _ (heI i) _ (heI j)]; simp) (R.P x) (fun j => by rw [R.im, hx _ (heI j)]; simp)
  rw [span_period R hI] at hs
  set s : Fin g → ℂ := ∑ i, (c i : ℂ) • R.P (b (f i)) with hsdef
  have hsm : s ∈ Submodule.span ℂ (Set.range fun i => R.P (b (f i))) :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hw : R.P x - s = 0 := by
    by_contra hne
    have h0 : (R.P x - s) ⬝ᵥ R.Hm *ᵥ star (R.P x - s) = 0 :=
      orth_of_set (by rintro _ ⟨j, rfl⟩; exact hc j) _ (Submodule.sub_mem _ hs hsm)
    have := R.pos _ hne
    rw [h0] at this
    simp at this
  exact (hI x).2 (GlobalTheory.T.mem_span_of_real_combination_periods g k n Λ R.P b f (GlobalTheory.T.linearIndependent_real_periods_basis E g Λ R n b) hf x c (sub_eq_zero.1 hw))

end

theorem exists_univ_quot : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R₀ : RiemLat E g Λ) (I : Submodule (𝓞 E) Λ), IsSaturated I → IsIsoSub R₀.form I → ∃ (g' k : ℕ) (Λ' : Type) (_ : AddCommGroup Λ') (_ : Module (𝓞 E) Λ') (e : Fin k → Λ) (form' : Λ' →ₗ[ℤ] Λ' →ₗ[ℤ] ℤ) (π : Λ → Λ'), k + g' = g ∧ (∀ x', ∃ x, (∀ y ∈ I, R₀.form x y = 0) ∧ π x = x') ∧ ∀ R : RiemLat E g Λ, R.form = R₀.form → LinearIndependent ℂ (fun i => R.P (e i)) ∧ Submodule.span ℂ (R.P '' I) = Submodule.span ℂ (Set.range fun i => R.P (e i)) ∧ ∀ q : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ), Function.Surjective q → LinearMap.ker q = Submodule.span ℂ (R.P '' I) → ∃ R' : RiemLat E g' Λ', R'.form = form' ∧ (∀ x, (∀ y ∈ I, R.form x y = 0) → R'.P (π x) = q (R.P x)) ∧ ∀ x y, (∀ v ∈ I, R.ip (R.P v) x = 0) → R'.ip (q x) (q y) = R.ip x y := by
  intro E _ _ _ g Λ _ _ R₀ I hsat hiso
  classical
  haveI := R₀.free
  haveI := R₀.fin
  obtain ⟨g', Λ', i1, i2, R₀', q₀, hq₀s, hq₀k, hq₀B, hq₀r, hq₀m⟩ := GlobalTheory.T.quotient_lattice_by_isotropic_submodule E g Λ Unit R₀ I hsat hiso
  obtain ⟨k, n, b, f, hf, hN⟩ := GlobalTheory.T.exists_basis_subset_of_saturated_submodule Λ (AddSubgroup.toIntSubmodule I.toAddSubgroup) (fun v m hm h => hsat v m hm h)
  have hI : ∀ v, v ∈ I ↔ v ∈ Submodule.span ℤ (Set.range fun i => b (f i)) := fun v => by
    rw [hN]; rfl
  have hLI₀ := period_facts R₀ b f hf hI hiso

  let D : AddSubgroup Λ :=
    { carrier := {x | ∀ y ∈ I, R₀.form x y = 0}
      add_mem' := fun {a c} ha hc y hy => by simp [ha y hy, hc y hy]
      zero_mem' := fun y _ => by simp
      neg_mem' := fun {a} ha y hy => by simp [ha y hy] }
  have hDmem : ∀ x, x ∈ D ↔ ∀ y ∈ I, R₀.form x y = 0 := fun x => Iff.rfl
  have hDsmul : ∀ (a : 𝓞 E), ∀ x ∈ D, a • x ∈ D := by
    intro a x hx y hy
    rw [R₀.adj a (IsCMField.ringOfIntegersComplexConj E a) (by simp [IsCMField.coe_ringOfIntegersComplexConj])]
    exact hx _ (I.smul_mem _ hy)
  have hex : ∀ x ∈ D, ∃ x', R₀'.P x' = q₀ (R₀.P x) := by
    intro x hx
    have : q₀ (R₀.P x) ∈ Set.range R₀'.P := by
      rw [hq₀r]; exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact this
  let π : Λ → Λ' := fun x => if h : x ∈ D then (hex x h).choose else 0
  have hπ : ∀ x ∈ D, R₀'.P (π x) = q₀ (R₀.P x) := by
    intro x h
    simp only [π, dif_pos h]
    exact (hex x h).choose_spec
  have hinj : Function.Injective R₀'.P := (GlobalTheory.T.riemann_lattice_eigen_projection E g' Λ' Unit R₀').1
  have hπs : ∀ x', ∃ x ∈ D, π x = x' := by
    intro x'
    have : R₀'.P x' ∈ Set.range R₀'.P := ⟨x', rfl⟩
    rw [hq₀r] at this
    obtain ⟨_, ⟨x, hx, rfl⟩, h⟩ := this
    exact ⟨x, hx, hinj ((hπ x hx).trans h)⟩
  have hπadd : ∀ x ∈ D, ∀ y ∈ D, π (x + y) = π x + π y := by
    intro x hx y hy
    apply hinj
    rw [hπ _ (D.add_mem hx hy), map_add, map_add, map_add, hπ x hx, hπ y hy]
  have hπsmul : ∀ (a : 𝓞 E), ∀ x ∈ D, a • x ∈ D ∧ π (a • x) = a • π x := by
    intro a x hx
    refine ⟨hDsmul a x hx, hinj ?_⟩
    rw [hπ _ (hDsmul a x hx), R₀'.act, hπ x hx, R₀.act, hq₀B]
  have hπI : ∀ x ∈ D, π x = 0 → x ∈ I := by
    intro x hx h0
    have h1 : q₀ (R₀.P x) = 0 := by rw [← hπ x hx, h0, map_zero]
    have h2 : R₀.P x ∈ LinearMap.ker q₀ := h1
    rw [hq₀k] at h2
    exact mem_of_mem_span R₀ b f hf hI hiso hx h2
  have hπform : ∀ x ∈ D, ∀ y ∈ D, R₀'.form (π x) (π y) = R₀.form x y := by
    intro x hx y hy
    have h := im_quot R₀ hI hiso hLI₀ q₀ hq₀k R₀'.Hm (fun a c ha => hq₀m a c ha) hx hy
    rw [← hπ x hx, ← hπ y hy, R₀'.im] at h
    exact_mod_cast h
  have hk : k + g' = g := by
    have h1 := LinearMap.finrank_range_add_finrank_ker q₀
    rw [LinearMap.range_eq_top.2 hq₀s, hq₀k, span_period R₀ hI, finrank_span_eq_card hLI₀] at h1
    simp at h1
    omega
  refine ⟨g', k, Λ', i1, i2, fun i => b (f i), R₀'.form, π, hk, hπs, fun R hR => ?_⟩
  have hiso' : IsIsoSub R.form I := hR ▸ hiso
  have hLI := period_facts R b f hf hI hiso'
  refine ⟨hLI, span_period R hI, fun q hqs hqk => ?_⟩
  obtain ⟨Hm', hherm, hpos, hmet⟩ := GlobalTheory.T.exists_posDef_form_on_quotient g g' R.Hm R.herm R.pos _ q hqs hqk (exists_orth R hI hLI)
  have hD' : ∀ x, (∀ y ∈ I, R.form x y = 0) → x ∈ D := fun x h => by rw [hDmem, ← hR]; exact h
  have hDR : ∀ x ∈ D, ∀ y ∈ I, R.form x y = 0 := fun x h => by rw [hR]; exact h
  have hmet' : ∀ a c, (∀ v ∈ I, R.ip (R.P v) a = 0) → q c ⬝ᵥ Hm' *ᵥ star (q a) = c ⬝ᵥ R.Hm *ᵥ star a := by
    intro a c ha
    refine hmet a c (orth_of_set ?_)
    rintro _ ⟨v, hv, rfl⟩
    exact ha v hv
  have hqB : ∀ (a : 𝓞 E) z, q z = 0 → q (R.B a z) = 0 := by
    intro a z hz
    have hz' : z ∈ Submodule.span ℂ (R.P '' I) := by rw [← hqk]; exact hz
    clear hz
    have : R.B a z ∈ Submodule.span ℂ (R.P '' I) := by
      induction hz' using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨v, hv, rfl⟩ := hw
        rw [← R.act]
        exact Submodule.subset_span ⟨_, I.smul_mem _ hv, rfl⟩
      | zero => simp
      | add w w' _ _ h h' =>
        rw [map_add]
        exact Submodule.add_mem _ h h'
      | smul c w _ h =>
        rw [map_smul]
        exact Submodule.smul_mem _ c h
    rw [← hqk] at this
    exact this
  have hker : ∀ x ∈ D, π x = 0 → q (R.P x) = 0 := by
    intro x hx h0
    have : R.P x ∈ LinearMap.ker q := by
      rw [hqk]; exact Submodule.subset_span ⟨x, hπI x hx h0, rfl⟩
    exact this
  have him : ∀ x ∈ D, ∀ y ∈ D, (q (R.P x) ⬝ᵥ Hm' *ᵥ star (q (R.P y))).im = R₀'.form (π x) (π y) := by
    intro x hx y hy
    rw [im_quot R hI hiso' hLI q hqk Hm' hmet' (hDR x hx) (hDR y hy), hπform x hx y hy, hR]
  obtain ⟨B', hB'⟩ := GlobalTheory.T.exists_descended_ringHom_on_quotient (𝓞 E) g g' R.B q hqs hqB
  obtain ⟨R', h1, h2, h3⟩ := GlobalTheory.T.riemannLattice_quotient_compat E g g' Λ Λ' R R₀' D π q Hm' B' hπs hπadd hπsmul hker hB' hherm hpos him
  refine ⟨R', h1, fun x hx => h3 x (hD' x hx), fun x y hx => ?_⟩
  show q y ⬝ᵥ R'.Hm *ᵥ star (q x) = y ⬝ᵥ R.Hm *ᵥ star x
  rw [h2]
  exact hmet' x y hx

end GlobalTheory.CompanionTheory.Ar.Cusp.Univ.QuotLat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogBlockMetricOffBoundaryStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_block_metric_off_boundary : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (l : Fin BM.q) (x₀ : BM.Rb.X) (z : (Σ k, ι k) → ℂ), M.blk p = none → x₀ ∈ BM.O l \ bdry BM.s → z ∈ mcPts (mCoordIdeal y) → SameOrbit (basePart M.blk z) (BM.Rb.lift x₀ x₀) → Real.log ((BM.hom p).h z) = blockPot j p.2 (BM.G l p.1 x₀) 1 + Real.log ‖baseMono M (BM.F l) p z * valAt M.x ((BM.F l).υ p)⁻¹ (basePart M.blk z)‖ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.StepW.BaseLine.main | exact GlobalTheory.CompanionTheory.Ar.PB.StepW.BaseLine.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.StepW.BaseLine.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogNormNonvanishingAnalyticHarmonicStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_norm_nonvanishing_analytic_harmonic : ∀ (e : ℕ) (f : (Fin e → ℂ) → ℂ) (z : Fin e → ℂ), AnalyticAt ℂ f z → f z ≠ 0 → ∃ Hh : (Fin e → ℂ) → ℂ, AnalyticAt ℂ Hh z ∧ ∀ᶠ z' in 𝓝 z, Real.log ‖f z'‖ = (Hh z').re := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.log_norm_eventually_eq_re_analyticAt | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.log_norm_eventually_eq_re_analyticAt | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.log_norm_eventually_eq_re_analyticAt <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogNormProductFormulaStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_norm_product_formula : ∀ (N : ℕ) (P : Fin N → Prop) (t : ℂ) (v f : Fin N → ℂ) (e : Fin N → ℤ), t ≠ 0 → (∀ i, ¬ P i → v i ≠ 0 ∧ f i ≠ 0) → Real.log ‖t * ∏ i : Fin N, (if P i then 1 else v i * f i) ^ e i‖ = Real.log ‖t‖ + ∑ i : Fin N, (e i : ℝ) * (if P i then 0 else Real.log ‖v i‖ + Real.log ‖f i‖) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.log_norm_mul_prod_ite_zpow | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.log_norm_mul_prod_ite_zpow | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.log_norm_mul_prod_ite_zpow <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogSineFormulaStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_sine_formula : ∀ (G : Matrix (Fin 2) (Fin 2) ℂ) (a₀ a₁ : ℂ), G.PosDef → a₀ ≠ a₁ → logSin G a₀ a₁ = Real.log ‖a₁ - a₀‖ + (1 / 2) * (xiPot G a₀ + xiPot G a₁) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.LogSin.logSin_eq_log_add_xiPot | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.LogSin.logSin_eq_log_add_xiPot | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.LogSin.logSin_eq_log_add_xiPot <;> assumption)
end

