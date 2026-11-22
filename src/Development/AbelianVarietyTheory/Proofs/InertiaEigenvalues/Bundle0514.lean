import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0018
import Formalism.SharpRestriction.Bundle0002
import Formalism.SharpRestriction.LevelLetterCocycles.NEqRZeroMulXPow
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0005
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0426
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0415
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0467
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0405
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0408
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0410
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisPrescribedUnramifiedKummer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0480
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0303
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0481

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonPlacePartLocalBoundLeMiddleRange
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

noncomputable section

namespace GlobalTheory.NLink.BBSize

variable {D : D7}

theorem sum_locDeg_le (i : D.nd.Loc) (S : Finset (HeightOneSpectrum (𝓞 D.host.E)))
    (hS : ∀ v ∈ S, v ∈ placesOver D.host.E (D.nd.l i)) :
    ∑ w ∈ S, (locDeg D.host.E w : ℝ) ≤ 2 * D.R.f := by
  have hl := (D.nd.lPrime i).out
  refine le_trans ?_ (TwistedPlaces.sum_nLam_le D hl)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro v hv
    exact (Set.Finite.mem_toFinset _).2 (hS v hv)
  · intro v _ _
    positivity

theorem card_le_sum_locDeg (S : Finset (HeightOneSpectrum (𝓞 D.host.E))) :
    (S.card : ℝ) ≤ ∑ w ∈ S, (locDeg D.host.E w : ℝ) := by
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  apply Finset.sum_le_sum
  intro v _
  exact_mod_cast TwistedPlaces.nLam_pos D v

theorem vdel_nonneg (i : D.nd.Loc) : (0 : ℝ) ≤ (D.nd.vdel i : ℝ) := by
  have : (0 : ℚ) ≤ D.nd.vdel i := by
    unfold NData.vdel
    positivity
  exact_mod_cast this

theorem vdel_le_two_t (i : D.nd.Loc) (h2 : D.nd.l i ∉ D.host.small) : (D.nd.vdel i : ℝ) ≤ 2 * D.R.t := by
  have := D.nd.lPrime i
  have h := LargeLevelLemmas.vdel_le i
  have hs : D.nd.s0 i = 1 := UpperTheory.Small.localLevel_eq_one_of_not_mem_smallPrimes D.nd i h2
  have hv : (padicValNat (D.nd.l i) D.R.t.factorial : ℚ) ≤ D.R.t := by
    exact_mod_cast padicValNat_factorial_le (D.nd.l i) D.R.t
  rw [hs] at h
  have : D.nd.vdel i ≤ 2 * (D.R.t : ℚ) := by
    push_cast at h
    linarith
  exact_mod_cast this

theorem blk_arith {f t n V large₂ c A k b v h : ℝ} (hf : 1 ≤ f) (ht : 1 ≤ t) (hn : 1 ≤ n) (hV : 1 ≤ V)
    (hL : 1 ≤ large₂) (hc : 1 ≤ c) (hA : A ≤ 6 * f) (hk0 : 0 ≤ k) (hk : k ≤ 2 * f) (hb0 : 0 ≤ b)
    (hb : b ≤ c * t * n * V * large₂) (hv0 : 0 ≤ v) (hv : v ≤ 2 * t) (hh : h ≤ c * t) :
    t * (A * b) + 4 * V * (k + 1) * v + t * k * h ≤ 32 * (c * f * n * t ^ 2 * V * large₂) := by
  have h1 : t * (A * b) ≤ 6 * (c * f * n * t ^ 2 * V * large₂) := by
    calc t * (A * b) ≤ t * ((6 * f) * (c * t * n * V * large₂)) := by gcongr
      _ = _ := by ring
  have h2 : 4 * V * (k + 1) * v ≤ 24 * (c * f * n * t ^ 2 * V * large₂) := by
    calc 4 * V * (k + 1) * v ≤ 4 * V * (3 * f) * (2 * t) := by gcongr; linarith
      _ = 24 * (1 * f * 1 * (t * 1) * V * 1) := by ring
      _ ≤ 24 * (c * f * n * (t * t) * V * large₂) := by gcongr
      _ = _ := by ring
  have h3 : t * k * h ≤ 2 * (c * f * n * t ^ 2 * V * large₂) := by
    calc t * k * h ≤ t * k * (c * t) := by gcongr
      _ ≤ t * (2 * f) * (c * t) := by gcongr
      _ = 2 * (c * f * 1 * t ^ 2 * 1 * 1) := by ring
      _ ≤ _ := by gcongr
  linarith

theorem col_arith {f t n V large₂ c A k m r v : ℝ} (hf : 1 ≤ f) (ht : 1 ≤ t) (hn : 1 ≤ n) (hV : 1 ≤ V)
    (hL : 1 ≤ large₂) (hc : 1 ≤ c) (hA : A ≤ 2 * f) (hk0 : 0 ≤ k) (hk : k ≤ 2 * f) (hm0 : 0 ≤ m) (hm : m ≤ t)
    (hr0 : 0 ≤ r) (hr : r ≤ t) (hv0 : 0 ≤ v) (hv : v ≤ 2 * t) :
    A * (m * v) + k * (2 * v + 2 * (c * r * n * V * large₂)) ≤ 16 * (c * f * n * t ^ 2 * V * large₂) := by
  have h1 : A * (m * v) ≤ 4 * (c * f * n * t ^ 2 * V * large₂) := by
    calc A * (m * v) ≤ (2 * f) * (t * (2 * t)) := by gcongr
      _ = 4 * (1 * f * 1 * t ^ 2 * 1 * 1) := by ring
      _ ≤ _ := by gcongr
  have h2 : k * (2 * v) ≤ 8 * (c * f * n * t ^ 2 * V * large₂) := by
    calc k * (2 * v) ≤ (2 * f) * (2 * (2 * t)) := by gcongr
      _ = 8 * (1 * f * 1 * (t * 1) * 1 * 1) := by ring
      _ ≤ 8 * (c * f * n * (t * t) * V * large₂) := by gcongr
      _ = _ := by ring
  have h3 : k * (2 * (c * r * n * V * large₂)) ≤ 4 * (c * f * n * t ^ 2 * V * large₂) := by
    calc k * (2 * (c * r * n * V * large₂)) ≤ (2 * f) * (2 * (c * t * n * V * large₂)) := by gcongr
      _ = 4 * (c * f * n * (t * 1) * V * large₂) := by ring
      _ ≤ 4 * (c * f * n * (t * t) * V * large₂) := by gcongr
      _ = _ := by ring
  rw [mul_add]
  linarith

theorem f_ge_one (D : D7) : (1 : ℝ) ≤ D.R.f := (TwistedPlaces.m_ge_one D).trans (TwistedPlaces.m_le_f D)

theorem nV_ge_one (D : D7) : (1 : ℝ) ≤ D.R.nV := by
  have := TwistedPlaces.t_ge_one D
  have h0 : (0 : ℝ) ≤ D.R.r := by positivity
  unfold Ranks.nV
  push_cast
  linarith

theorem blockBoundDeclaration_le_middleRange (L : SizeData₂ D) (i : D.nd.Loc) (h2 : D.nd.l i ∉ D.host.small) (dc : TruncatedSeriesCountingIdentities.Decl D i) (cB : ℕ) {c : ℝ}
    (hc : 1 ≤ c) (hB : (cB : ℝ) ≤ c * D.R.t * D.R.n * D.R.nV * TwistedPlaces.large₂ L)
    (hh : (h0 D.nd i dc.col : ℝ) ≤ c * D.R.t) :
    (KillingConditions.localErrorBoundDecomposition i dc cB : ℝ) ≤ 32 * (c * D.R.f * D.R.n * (D.R.t : ℝ) ^ 2 * D.R.nV * TwistedPlaces.large₂ L) := by
  have hrow := sum_locDeg_le i dc.row (fun v hv => (dc.cover v).1 (Or.inl hv))
  have hcol := sum_locDeg_le i dc.col (fun v hv => (dc.cover v).1 (Or.inr hv))
  have hr := card_le_sum_locDeg dc.row
  have hk := card_le_sum_locDeg dc.col
  have hA : ∑ w ∈ dc.row, ((locDeg D.host.E w : ℝ) + 2) ≤ 6 * D.R.f := by
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    linarith
  have := blk_arith (f_ge_one D) (TwistedPlaces.t_ge_one D) (TwistedPlaces.n_ge_one D) (nV_ge_one D) (TwistedPlaces.L_ge_one L) hc hA
    (Nat.cast_nonneg dc.col.card) (hk.trans hcol) (Nat.cast_nonneg cB) hB (vdel_nonneg i)
    (vdel_le_two_t i h2) hh
  unfold KillingConditions.localErrorBoundDecomposition
  push_cast
  rw [← Finset.sum_mul]
  exact this

theorem blockBoundAtZero_le_middleRange (L : SizeData₂ D) (i : D.nd.Loc) (h2 : D.nd.l i ∉ D.host.small)
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i)
    (c0 : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ) {c : ℝ}
    (hc : 1 ≤ c) (hB : (cB : ℝ) ≤ c * D.R.t * D.R.n * D.R.nV * TwistedPlaces.large₂ L)
    (hh : (h0 D.nd i dc.col : ℝ) ≤ c * D.R.t)
    (hu : ∀ u ∈ dc.col, (c0 u : ℝ) ≤ c * D.R.n * D.R.nV * TwistedPlaces.large₂ L ∧
      (Br.h0W i u ρ π : ℝ) ≤ c * D.R.r * D.R.n * D.R.nV * TwistedPlaces.large₂ L) :
    (localErrorBoundPlaces i ρ π dc c0 cB : ℝ) ≤ 48 * (c * D.R.f * D.R.n * (D.R.t : ℝ) ^ 2 * D.R.nV * TwistedPlaces.large₂ L) := by
  have hb := blockBoundDeclaration_le_middleRange L i h2 dc cB hc hB hh
  have hcol := sum_locDeg_le i dc.col (fun v hv => (dc.cover v).1 (Or.inr hv))
  have hk := card_le_sum_locDeg dc.col
  have hrt : (D.R.r : ℝ) ≤ D.R.t := by linarith [TwistedPlaces.t_ge D]
  have hmt : (D.R.m : ℝ) ≤ D.R.t := by linarith [TwistedPlaces.m_le_k D, TwistedPlaces.k_le_r D]
  have hc' := col_arith (f_ge_one D) (TwistedPlaces.t_ge_one D) (TwistedPlaces.n_ge_one D) (nV_ge_one D) (TwistedPlaces.L_ge_one L) hc hcol
    (Nat.cast_nonneg dc.col.card) (hk.trans hcol) (Nat.cast_nonneg D.R.m) hmt (Nat.cast_nonneg D.R.r) hrt
    (vdel_nonneg i) (vdel_le_two_t i h2)
  have hs : ∑ u ∈ dc.col, ((locDeg D.host.E u : ℝ) * (D.R.m : ℝ) * (D.nd.vdel i : ℝ) + 2 * (D.nd.vdel i : ℝ) +
        (Br.h0W i u ρ π : ℝ) + (D.R.r : ℝ) * (c0 u : ℝ)) ≤
      ∑ u ∈ dc.col, ((locDeg D.host.E u : ℝ) * ((D.R.m : ℝ) * (D.nd.vdel i : ℝ)) +
        (2 * (D.nd.vdel i : ℝ) + 2 * (c * D.R.r * D.R.n * D.R.nV * TwistedPlaces.large₂ L))) := by
    apply Finset.sum_le_sum
    intro u hu'
    obtain ⟨h1, h3⟩ := hu u hu'
    have h4 := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg (α := ℝ) D.R.r)
    linarith
  rw [Finset.sum_add_distrib (f := fun u => (locDeg D.host.E u : ℝ) * ((D.R.m : ℝ) * (D.nd.vdel i : ℝ))),
    ← Finset.sum_mul, Finset.sum_const, nsmul_eq_mul] at hs
  unfold KillingConditions.localErrorBoundDecomposition at hb
  unfold localErrorBoundPlaces
  push_cast at hb ⊢
  linarith

theorem main : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (X : KillingConditions.HubData D) (R : KillingConditions.RowK) (c : ℝ), 1 ≤ c → KillingConditions.DataAD L HW X R → KillingConditions.InvariantsBoundsWithCoarseColumnConstant L X c → KillingConditions.BBLe L X (60 * c) := by
  intro D L _ HW X R c hc hD hJ i hi hg hR π hπ
  obtain ⟨hB, hh, hS⟩ := hJ i hi hg hR
  have h2 : D.nd.l i ∉ D.host.small := fun h => hR.1 (Or.inl h)
  have hq : D.nd.l i ≠ D.host.q := fun h => hR.2.1 (Or.inl h)
  have hd : D.nd.l i ≠ D.host.d := fun h => hR.2.1 (Or.inr h)
  have hL := TwistedPlaces.L_ge_one L
  have hM0 : 0 ≤ c * D.R.f * D.R.n * (D.R.t : ℝ) ^ 2 * D.R.nV * TwistedPlaces.large₂ L := by
    have : 0 ≤ c := by linarith
    have : 0 ≤ TwistedPlaces.large₂ L := by linarith
    positivity
  have hM := le_mul_of_one_le_right hM0 hL
  have hE : 60 * c * D.R.f * D.R.n * (D.R.t : ℝ) ^ 2 * D.R.nV * (TwistedPlaces.large₂ L) ^ 2 =
      60 * (c * D.R.f * D.R.n * (D.R.t : ℝ) ^ 2 * D.R.nV * TwistedPlaces.large₂ L * TwistedPlaces.large₂ L) := by ring
  rw [hE]
  rcases TwistedPlaces.split_or_inert D h2 hq hd with hs | hin
  · rw [hD.error_bound_split_eq i hs π]
    have := blockBoundAtZero_le_middleRange L i h2 (X.ρ i) π (X.dc i) (X.c0 i) (X.cB i) hc hB hh
      (fun u hu => ⟨(hS hs u hu).1, (hS hs u hu).2 π hπ⟩)
    linarith
  · rw [hD.error_bound_inert_eq i hin π]
    have := blockBoundDeclaration_le_middleRange L i h2 (X.dc i) (X.cB i) hc hB hh
    linarith

end GlobalTheory.NLink.BBSize

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyBreuilKisinDatum
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem wq_map_injective {l : ℕ} [Fact l.Prime] {a : ℕ} [NeZero a] {O : Type} [CommRing O] [IsDomain O]
    [CharZero O] (w : Wq l a →+* O) : Function.Injective w := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra h0
  obtain ⟨n, u, rfl⟩ := WittVector.exists_eq_pow_p_mul' x h0
  rw [map_mul, map_pow, map_natCast] at hx
  rcases mul_eq_zero.1 hx with h | h
  · exact pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h
  · exact (u.isUnit.map w).ne_zero h

theorem nonempty_bk_of_finExt : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l), Nonempty (BK K) := by
  intro l hl K
  obtain ⟨hdvr, hfin, hunit⟩ := GlobalTheory.T.ringOfIntegers_finiteExt_isDVR_finite_unit_iff l K
  obtain ⟨a, ha, w, hK, hw, hres⟩ := GlobalTheory.T.exists_witt_residueField_in_ringOfIntegers l K
  letI : Algebra (Wq l a) ↥(OL K) := w.toRingHom.toAlgebra
  have halg : ∀ c, algebraMap (Wq l a) ↥(OL K) c = w c := fun _ => rfl
  haveI : IsScalarTower ℤ_[l] (Wq l a) ↥(OL K) :=
    IsScalarTower.of_algebraMap_eq fun z => (w.commutes z).symm
  haveI : Module.Finite (Wq l a) ↥(OL K) := Module.Finite.of_restrictScalars_finite ℤ_[l] _ _
  obtain ⟨π, Ep, hπ, hE, hne, hmin⟩ :=
    GlobalTheory.T.exists_uniformiser_eisenstein_not_in_X_pow l a ↥(OL K) (wq_map_injective _) hres
  obtain ⟨str, hstr⟩ := GlobalTheory.T.breuilKisin_quotient_eisenstein_equiv l a ↥(OL K) π Ep hE hmin
  obtain ⟨hδ, hc⟩ := GlobalTheory.T.eisenstein_distinguished_powerSeries_adicComplete l a Ep hE
  obtain ⟨fl, ev, hfl, hX, hC, hφ⟩ :=
    GlobalTheory.T.exists_breuilKisin_eval_teichmuller_tilt l a (intToOC K π) (fun h => hπ.not_isUnit ((hunit π).2 h))
  have hpoly : ∀ f : Polynomial (Wq l a),
      Per.θ l (ev (f : (Wq l a)⟦X⟧)) = intToOC K (Polynomial.aeval π f) := by
    intro f
    have : ((Per.θ l).comp ev).comp Polynomial.coeToPowerSeries.ringHom =
        (intToOC K).comp (Polynomial.aeval π : Polynomial (Wq l a) →ₐ[Wq l a] ↥(OL K)).toRingHom := by
      refine Polynomial.ringHom_ext (fun c => ?_) ?_
      · change Per.θ l (ev ((Polynomial.C c : Polynomial (Wq l a)) : (Wq l a)⟦X⟧)) =
          intToOC K (Polynomial.aeval π (Polynomial.C c))
        rw [Polynomial.coe_C, hC, Polynomial.aeval_C, halg, hw]
      · change Per.θ l (ev ((Polynomial.X : Polynomial (Wq l a)) : (Wq l a)⟦X⟧)) =
          intToOC K (Polynomial.aeval π (Polynomial.X : Polynomial (Wq l a)))
        rw [Polynomial.coe_X, hX, Polynomial.aeval_X, hfl]
    exact congrArg (fun φ : Polynomial (Wq l a) →+* OC l => φ f) this
  have hE0 : Per.θ l (ev (Ep : (Wq l a)⟦X⟧)) = 0 := by rw [hpoly, hmin.1, map_zero]
  refine ⟨{
    a := a, Ep := Ep, monic := hE.1, deg_pos := hE.2.1, dvd_coeff := hE.2.2.1, coeff_zero := hE.2.2.2
    not_expand := hne, str := str, isUnit_δ := hδ, complete := hc, flat := fl, ev := ev, ev_X := hX
    ev_C := hC, ev_frob := hφ
    span_ev := GlobalTheory.T.span_eq_ker_theta_of_distinguished_ainf l _ hE0 ?_
    θ_ev := fun r x h => ?_
    gal_w := fun g c => gal_wA l a
      (fun x hx => (IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 x (hK hx)) c }⟩
  · rw [← (deltaS l a).map_δ_of_map_φ (ainfDelta l) ainf_torsionFree ev hφ]
    exact hδ.map ev
  · obtain ⟨f, rfl⟩ := hmin.2.1 r
    rw [hstr, Ideal.Quotient.eq, Ideal.mem_span_singleton'] at h
    obtain ⟨y, hy⟩ := h
    rw [← hpoly, ← sub_eq_zero, ← map_sub, ← map_sub, ← hy, map_mul, map_mul, hE0, mul_zero]

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormEqOfIsRootMinpolyUnramifiedRootsOfUnityField
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory

theorem conj_norm_eq_of_minpoly_root :
    ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (z z' : Om l),
    Polynomial.aeval z' (minpoly (↥(Kunr l a)) z) = 0 → ‖z'‖ = ‖z‖ := by
  intro l _ a _ z z' h
  have hint : IsIntegral (↥(Kunr l a)) z := Algebra.IsIntegral.isIntegral z
  have hm : minpoly (↥(Kunr l a)) z' = minpoly (↥(Kunr l a)) z :=
    (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hint) h (minpoly.monic hint)).symm
  obtain ⟨τ, hτ⟩ := ((Normal.minpoly_eq_iff_mem_orbit (Om l)).1 hm)
  have hτ' : τ • z = z' := hτ
  rw [← hτ']
  exact (spectralNorm_eq_of_equiv (τ.restrictScalars ℚ_[l]) z).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormInertiaPartialTraceGeometricLe
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.PartialTraceGain

theorem sum_range_mul_eq {M : Type*} [AddCommMonoid M] (f : ℕ → M) (a b : ℕ) :
    ∑ i ∈ Finset.range (a * b), f i = ∑ i ∈ Finset.range a, ∑ j ∈ Finset.range b, f (i + a * j) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_range_succ, add_comm (a * b) i]

theorem norm_natCast_lt_one (l : ℕ) [Fact l.Prime] : ‖((l : ℕ) : Om l)‖ < 1 := by
  have h : ((l : ℕ) : Om l) = algebraMap ℚ_[l] (Om l) (l : ℚ_[l]) := by simp
  rw [h, norm_algebraMap']
  exact Padic.norm_p_lt_one

def fixedAdd {l : ℕ} [Fact l.Prime] (H : Subgroup (GQ l)) : AddSubgroup (Om l) where
  carrier := {x | ∀ g ∈ H, g x = x}
  add_mem' := fun {a b} ha hb g hg => by rw [map_add, ha g hg, hb g hg]
  zero_mem' := fun g _ => map_zero g
  neg_mem' := fun {a} ha g hg => by rw [map_neg, ha g hg]

theorem apply_mem_fixedAdd {l : ℕ} [Fact l.Prime] {H : Subgroup (GQ l)} (hH : H.Normal)
    (σ : GQ l) {x : Om l} (hx : x ∈ fixedAdd H) : σ x ∈ fixedAdd H := by
  intro g hg
  have h1 := hx _ (hH.conj_mem' g hg σ)
  have h2 : g * σ = σ * (σ⁻¹ * g * σ) := by group
  calc g (σ x) = (g * σ) x := rfl
    _ = σ ((σ⁻¹ * g * σ) x) := by rw [h2]; rfl
    _ = σ x := by rw [h1]

theorem apply_sum_pow {l : ℕ} [Fact l.Prime] (σ : GQ l) (m : ℕ) {x : Om l}
    (hx : (σ ^ m) x = x) :
    σ (∑ j ∈ Finset.range m, (σ ^ j) x) = ∑ j ∈ Finset.range m, (σ ^ j) x := by
  have h1 : σ (∑ j ∈ Finset.range m, (σ ^ j) x) = ∑ j ∈ Finset.range m, (σ ^ (j + 1)) x := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_succ']; rfl
  have h2 := Finset.sum_range_succ' (fun j => (σ ^ j) x) m
  rw [Finset.sum_range_succ, hx] at h2
  rw [h1]
  simpa using h2.symm

theorem pow_apply_of_fixed {l : ℕ} [Fact l.Prime] (σ : GQ l) {y : Om l} (hy : σ y = y) (i : ℕ) :
    (σ ^ i) y = y := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [pow_succ]
    change (σ ^ i) (σ y) = y
    rw [hy, ih]

theorem norm_sum_pow_le : ∀ (l : ℕ) [Fact l.Prime] (γ : GQ l), γ ∈ (MaximalUnramifiedExtension l).fixingSubgroup → ∀ (H : ℕ → Subgroup (GQ l)) (k : ℕ), (∀ n, (H n).Normal) → (∀ n, (H n).index ≠ 0) → (∀ n, (H n).index ≤ l ^ (k + n)) → (∀ n, γ ^ l ^ n ∈ H n) → (∀ n, ∀ h ∈ H n, ∃ i : ℕ, ((γ ^ l ^ n) ^ i)⁻¹ * h ∈ H (n + 1)) → ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ (n : ℕ) (x : Om l), (∀ g ∈ H n, g x = x) → ‖∑ i ∈ Finset.range (l ^ n), (γ ^ i) x‖ ≤ ρ ^ n * ‖x‖ := by
  intro l hl γ hγ H k hN hI hIle hpow hgen
  have hp : l.Prime := hl.out
  have hl1 : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hp.one_le
  have ha0 : 0 ≤ ‖((l : ℕ) : Om l)‖ := norm_nonneg _
  have ha1 := norm_natCast_lt_one l
  have hpk : (1 : ℝ) ≤ (l : ℝ) ^ (k + 1) := one_le_pow₀ hl1
  have he0 : (0 : ℝ) < (1 : ℝ) / (l : ℝ) ^ (k + 1) := by positivity
  have he1 : (1 : ℝ) / (l : ℝ) ^ (k + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; exact hpk
  set ρ : ℝ := ‖((l : ℕ) : Om l)‖ ^ ((1 : ℝ) / (l : ℝ) ^ (k + 1)) with hρ
  have hρ0 : 0 ≤ ρ := Real.rpow_nonneg ha0 _
  have hρ1 : ρ < 1 := Real.rpow_lt_one ha0 ha1 he0
  have haρ : ‖((l : ℕ) : Om l)‖ ≤ ρ := by
    have := Real.rpow_le_rpow_of_exponent_ge' ha0 ha1.le he0.le he1
    rwa [Real.rpow_one] at this
  have hmax : max (ρ ^ (l - 1)) ‖((l : ℕ) : Om l)‖ ≤ ρ := by
    refine max_le ?_ haρ
    have h2 := hp.two_le
    exact pow_le_of_le_one hρ0 hρ1.le (by omega)
  refine ⟨ρ, hρ0, hρ1, fun n => ?_⟩
  induction n with
  | zero => intro x _; simp
  | succ n ih =>
    intro x hx
    set σ : GQ l := γ ^ l ^ n with hσ
    have hσl : σ ^ l = γ ^ l ^ (n + 1) := by rw [hσ, ← pow_mul, ← pow_succ]
    have hxS : x ∈ fixedAdd (H (n + 1)) := hx
    set y : Om l := ∑ j ∈ Finset.range l, (σ ^ j) x with hy
    have hyS : y ∈ fixedAdd (H (n + 1)) :=
      sum_mem fun j _ => apply_mem_fixedAdd (hN _) _ hxS
    have hσy : σ y = y := apply_sum_pow σ l (by rw [hσl]; exact hx _ (hpow _))
    have hyH : ∀ g ∈ H n, g y = y := by
      intro g hg
      obtain ⟨i, hi⟩ := hgen n g hg
      have h1 := hyS _ hi
      have h2 : g = σ ^ i * ((σ ^ i)⁻¹ * g) := by group
      calc g y = (σ ^ i) (((σ ^ i)⁻¹ * g) y) := by
            conv_lhs => rw [h2]
            rfl
        _ = y := by rw [h1, pow_apply_of_fixed σ hσy]
    have hmove : ∀ z ∈ fixedAdd (H (n + 1)), ‖σ z - z‖ ≤ ρ * ‖z‖ := by
      intro z hz
      have := GlobalTheory.T.norm_inertia_pow_prime_pow_sub_le l γ hγ (H (n + 1)) (hN _) (hI _) (k + (n + 1)) (n + 1) (hIle _)
        (hpow _) n (by omega) z hz
      rwa [show k + (n + 1) - n = k + 1 by omega] at this
    have hyn : ‖y‖ ≤ ρ * ‖x‖ :=
      (GlobalTheory.T.norm_sum_pow_apply_le_and_norm_pow_prime_sub_le l σ (fixedAdd (H (n + 1))) ρ hρ0 hρ1.le
        (fun z hz => apply_mem_fixedAdd (hN _) σ hz) hmove x hxS).1.trans
        (mul_le_mul_of_nonneg_right hmax (norm_nonneg _))
    have hsum : ∑ i ∈ Finset.range (l ^ (n + 1)), (γ ^ i) x
        = ∑ i ∈ Finset.range (l ^ n), (γ ^ i) y := by
      rw [pow_succ, sum_range_mul_eq]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hy, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [pow_add, pow_mul]; rfl
    rw [hsum]
    calc _ ≤ ρ ^ n * ‖y‖ := ih y hyH
      _ ≤ ρ ^ n * (ρ * ‖x‖) := mul_le_mul_of_nonneg_left hyn (pow_nonneg hρ0 _)
      _ = ρ ^ (n + 1) * ‖x‖ := by ring

end GlobalTheory.PartialTraceGain
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLtOneOfIsRootDistinguishedWittPolynomial
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

noncomputable section

namespace GlobalTheory.RootLt

open Polynomial

theorem norm_iotaO_le_one (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (w : Wq l a) :
    ‖GlobalTheory.TameFrob.iotaO l a w‖ ≤ 1 := by
  have hw : w ∈ Submodule.span ℤ_[l] (Set.range (WittVector.teichmuller l : Fq l a → Wq l a)) := by
    rw [span_teich]; trivial
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z, rfl⟩ := hx
    set ω := GlobalTheory.TameFrob.iotaO l a (WittVector.teichmuller l z)
    have hω : ω ^ l ^ a = ω := by
      simp only [ω]
      rw [← map_pow, ← map_pow, Fq.pow_card]
    by_contra h
    push_neg at h
    have h2 : 1 < l ^ a := Nat.one_lt_pow (NeZero.ne a) (Fact.out : l.Prime).one_lt
    have h3 : ‖ω‖ ^ 1 < ‖ω‖ ^ l ^ a := pow_lt_pow_right₀ h h2
    rw [pow_one, ← norm_pow, hω] at h3
    exact lt_irrefl _ h3
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
  | smul c x _ hx =>
    rw [Algebra.smul_def, map_mul, GlobalTheory.TameFrob.iotaO_algebraMap, norm_mul]
    have hc : ‖algebraMap ℚ_[l] (Om l) (c : ℚ_[l])‖ ≤ 1 :=
      (PadicAlgCl.norm_extends l (c : ℚ_[l])).le.trans c.2
    calc _ ≤ 1 * 1 := mul_le_mul hc hx (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1

theorem norm_lt_one_of_isRoot : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (P : Polynomial (Wq l a)), P.Monic →
    (∀ i < P.natDegree, (l : Wq l a) ∣ P.coeff i) → ∀ x : Om l, (P.map (GlobalTheory.TameFrob.iotaO l a)).IsRoot x → ‖x‖ < 1 := by
  intro l _ a _ P hP hdiv x hx
  set d := P.natDegree with hd
  rcases Nat.eq_zero_or_pos d with h0 | hpos
  · have : P = 1 := Polynomial.eq_one_of_monic_natDegree_zero hP h0
    rw [this, Polynomial.map_one] at hx
    simp [Polynomial.IsRoot] at hx
  by_contra hge
  push_neg at hge
  have hlpos : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt

  have hnl : ‖GlobalTheory.TameFrob.iotaO l a (l : Wq l a)‖ = (l : ℝ)⁻¹ := by
    rw [map_natCast, ← map_natCast (algebraMap ℚ_[l] (Om l)), PadicAlgCl.norm_extends, Padic.norm_p]
  have hcoef : ∀ i < d, ‖GlobalTheory.TameFrob.iotaO l a (P.coeff i)‖ ≤ (l : ℝ)⁻¹ := by
    intro i hi
    obtain ⟨c, hc⟩ := hdiv i hi
    rw [hc, map_mul, norm_mul, hnl]
    calc _ ≤ (l : ℝ)⁻¹ * 1 := mul_le_mul_of_nonneg_left (norm_iotaO_le_one l a c) (by positivity)
      _ = _ := mul_one _
  have hxd : (1 : ℝ) ≤ ‖x‖ ^ d := one_le_pow₀ hge

  have heq : x ^ d + ∑ i ∈ Finset.range d, GlobalTheory.TameFrob.iotaO l a (P.coeff i) * x ^ i = 0 := by
    have h := hx
    rw [Polynomial.IsRoot, hP.as_sum] at h
    simpa [Polynomial.eval_finset_sum, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_sum,
      Polynomial.map_mul] using h
  have hsum : ‖∑ i ∈ Finset.range d, GlobalTheory.TameFrob.iotaO l a (P.coeff i) * x ^ i‖ ≤ (l : ℝ)⁻¹ * ‖x‖ ^ d := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    rw [norm_mul, norm_pow]
    exact mul_le_mul (hcoef i hi') (pow_le_pow_right₀ hge hi'.le) (by positivity) (by positivity)
  have hxeq : x ^ d = -∑ i ∈ Finset.range d, GlobalTheory.TameFrob.iotaO l a (P.coeff i) * x ^ i :=
    eq_neg_of_add_eq_zero_left heq
  have h1 : ‖x‖ ^ d ≤ (l : ℝ)⁻¹ * ‖x‖ ^ d := by
    calc ‖x‖ ^ d = ‖x ^ d‖ := (norm_pow _ _).symm
      _ = ‖∑ i ∈ Finset.range d, GlobalTheory.TameFrob.iotaO l a (P.coeff i) * x ^ i‖ := by rw [hxeq, norm_neg]
      _ ≤ _ := hsum
  have h2 : (l : ℝ)⁻¹ * ‖x‖ ^ d < ‖x‖ ^ d := by
    have : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
    nlinarith
  exact lt_irrefl _ (h1.trans_lt h2)

end GlobalTheory.RootLt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormTeichmullerTiltMinusOneLeStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_teichmullerTiltMinusOne_le : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (e : OCb l), IsEps e → ‖bk.iA (mu e)‖ ≤ (l : ℝ)⁻¹ ∧ (l = 2 → ‖bk.iA (mu e)‖ ≤ (4 : ℝ)⁻¹) := by
  first | exact @GlobalTheory.BSP.BK.norm_iA_mu_le | exact GlobalTheory.BSP.BK.norm_iA_mu_le | (intros; apply GlobalTheory.BSP.BK.norm_iA_mu_le <;> assumption)
end

