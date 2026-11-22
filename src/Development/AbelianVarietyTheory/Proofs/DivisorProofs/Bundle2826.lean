import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2289
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2430
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2734
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2250
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0653
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2421
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2442
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2403
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPointExtensionSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2668
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2735
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CrossRelationGivesConvolutionRelation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTangentPresentationPrime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2633
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2684
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2736
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2566

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelLevelPPowerTangent
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace GlobalTheory.FlatModel

theorem norm_int_le_one {p : ℕ} [Fact p.Prime] (x : 𝓞_ℂ_[p]) : ‖(x : ℂ_[p])‖ ≤ 1 := by
  rw [← coe_valued]
  exact_mod_cast (Valuation.mem_valuationSubring_iff _ _).1 x.2

theorem norm_eq_of_norm_sub_lt {p : ℕ} [Fact p.Prime] {X A : ℂ_[p]} (h : ‖X - A‖ < ‖X‖) : ‖A‖ = ‖X‖ := by
  have h1 : ‖A‖ ≤ max ‖X‖ ‖X - A‖ := by
    have := IsUltrametricDist.norm_add_le_max X (-(X - A))
    rwa [norm_neg, show X + -(X - A) = A by ring] at this
  have h2 : ‖X‖ ≤ max ‖A‖ ‖X - A‖ := by
    have := IsUltrametricDist.norm_add_le_max A (X - A)
    simpa using this
  rcases le_max_iff.1 h2 with h2 | h2
  · exact le_antisymm (h1.trans (max_le le_rfl h.le)) h2
  · exact absurd h (not_lt.2 h2)

theorem norm_quot_sub_lt {p : ℕ} [Fact p.Prime] (n : ℕ) (x y : 𝓞_ℂ_[p]) (A B κ q : ℂ_[p])
    (hbig : (p : ℝ)⁻¹ ^ n < ‖((x * y : 𝓞_ℂ_[p]) : ℂ_[p])‖)
    (hA : ‖(x : ℂ_[p]) - A‖ ≤ (p : ℝ)⁻¹ ^ n) (hB : ‖(y : ℂ_[p]) - B‖ ≤ (p : ℝ)⁻¹ ^ n)
    (hq : q * A = κ * B) (hκ : κ ≠ 0) :
    ‖q * (x : ℂ_[p]) / (y : ℂ_[p]) - κ‖ < ‖κ‖ := by
  have hX1 := norm_int_le_one x
  have hY1 := norm_int_le_one y
  have hbig' : (p : ℝ)⁻¹ ^ n < ‖(x : ℂ_[p])‖ * ‖(y : ℂ_[p])‖ := by
    rw [← norm_mul]; exact_mod_cast hbig
  have hXb : (p : ℝ)⁻¹ ^ n < ‖(x : ℂ_[p])‖ :=
    hbig'.trans_le (mul_le_of_le_one_right (norm_nonneg _) hY1)
  have hYb : (p : ℝ)⁻¹ ^ n < ‖(y : ℂ_[p])‖ :=
    hbig'.trans_le (mul_le_of_le_one_left (norm_nonneg _) hX1)
  have hXA : ‖(x : ℂ_[p]) - A‖ < ‖(x : ℂ_[p])‖ := hA.trans_lt hXb
  have hYB : ‖(y : ℂ_[p]) - B‖ < ‖(y : ℂ_[p])‖ := hB.trans_lt hYb
  have nA := norm_eq_of_norm_sub_lt hXA
  have nB := norm_eq_of_norm_sub_lt hYB
  have hpos : (0 : ℝ) < (p : ℝ)⁻¹ ^ n := by
    have : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    positivity
  have hA0 : A ≠ 0 := fun h0 => by rw [h0, norm_zero] at nA; linarith
  have hB0 : B ≠ 0 := fun h0 => by rw [h0, norm_zero] at nB; linarith
  have hY0 : (y : ℂ_[p]) ≠ 0 := fun h0 => by rw [h0, norm_zero] at hYb; linarith
  have hq' : q = κ * B / A := by rw [eq_div_iff hA0, hq]
  have key : q * (x : ℂ_[p]) / (y : ℂ_[p]) - κ =
      κ * ((((x : ℂ_[p]) - A) * B - A * ((y : ℂ_[p]) - B)) / (A * (y : ℂ_[p]))) := by
    rw [hq']; field_simp; ring
  rw [key, norm_mul]
  have hk : 0 < ‖κ‖ := norm_pos_iff.2 hκ
  refine mul_lt_of_lt_one_right hk ?_
  have hden : 0 < ‖A * (y : ℂ_[p])‖ := norm_pos_iff.2 (mul_ne_zero hA0 hY0)
  rw [norm_div, div_lt_one hden]
  have e1 : ‖((x : ℂ_[p]) - A) * B‖ < ‖A * (y : ℂ_[p])‖ := by
    rw [norm_mul, norm_mul, nA, nB]
    exact mul_lt_mul_of_pos_right hXA (by linarith)
  have e2 : ‖A * ((y : ℂ_[p]) - B)‖ < ‖A * (y : ℂ_[p])‖ := by
    rw [norm_mul, norm_mul]
    exact mul_lt_mul_of_pos_left hYB (by rw [nA]; linarith)
  calc ‖((x : ℂ_[p]) - A) * B - A * ((y : ℂ_[p]) - B)‖
      ≤ max ‖((x : ℂ_[p]) - A) * B‖ ‖A * ((y : ℂ_[p]) - B)‖ := by
        have := IsUltrametricDist.norm_add_le_max (((x : ℂ_[p]) - A) * B) (-(A * ((y : ℂ_[p]) - B)))
        rwa [norm_neg, ← sub_eq_add_neg] at this
    _ < ‖A * (y : ℂ_[p])‖ := max_lt e1 e2

end GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel

theorem norm_minor_sub_le {p : ℕ} [Fact p.Prime] {E : Type} [Field E] [NumberField E] [StarRing (𝓞 E)] (P : PtP E p)
    (n : ℕ) {V J : Type} [CommRing V] (β : V →+* 𝓞_ℂ_[p]) {N g m : ℕ} (T : J → Fin N → V)
    (h : Fin N → Fin g → 𝓞_ℂ_[p]) (ta : Fin N → P.T) (xb : Fin g → LieG P.Gt)
    (hh : ∀ a b, h a b - (P.al₀ (ta a)).1 (xb b) ∈ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n})
    (I : Fin m → J) (U : Fin m → Fin g → 𝓞_ℂ_[p]) :
    ‖((pairDet (covec β T h I) U : 𝓞_ℂ_[p]) : ℂ_[p]) -
      (Matrix.of fun k k' => P.pairV (∑ b, (U k b : ℂ_[p]) • P.bLie (xb b))
        (∑ a, (β (T (I k') a) : ℂ_[p]) ⊗ₜ[ℤ_[p]] ta a)).det‖ ≤ (p : ℝ)⁻¹ ^ n := by
  classical
  set Mex : Matrix (Fin m) (Fin m) 𝓞_ℂ_[p] :=
    Matrix.of fun k k' => ∑ b, (∑ a, β (T (I k') a) * (P.al₀ (ta a)).1 (xb b)) * U k b with hMex
  have h1 : pairDet (covec β T h I) U - Mex.det ∈ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n} := by
    rw [← Ideal.Quotient.eq, pairDet, RingHom.map_det, RingHom.map_det]
    congr 1
    ext k k'
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, hMex, covec]
    rw [Ideal.Quotient.eq, ← Finset.sum_sub_distrib]
    refine Ideal.sum_mem _ fun b _ => ?_
    rw [← sub_mul, ← Finset.sum_sub_distrib]
    refine Ideal.mul_mem_right _ _ (Ideal.sum_mem _ fun a _ => ?_)
    rw [← mul_sub]
    exact Ideal.mul_mem_left _ _ (hh a b)
  have e : ∀ (x : LieG P.Gt) (c : ℂ_[p]) (t : P.T),
      P.pairV (P.bLie x) (c ⊗ₜ[ℤ_[p]] t) = c * algebraMap 𝓞_ℂ_[p] ℂ_[p] ((P.al₀ t).1 x) := fun x c t => by
    rw [show (c ⊗ₜ[ℤ_[p]] t : P.V) = c • ((1 : ℂ_[p]) ⊗ₜ[ℤ_[p]] t) by
      rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one], map_smul, P.pairV_bLie, smul_eq_mul]
  have h2 : ((Mex.det : 𝓞_ℂ_[p]) : ℂ_[p]) = (Matrix.of fun k k' => P.pairV (∑ b, (U k b : ℂ_[p]) • P.bLie (xb b))
        (∑ a, (β (T (I k') a) : ℂ_[p]) ⊗ₜ[ℤ_[p]] ta a)).det := by
    change algebraMap 𝓞_ℂ_[p] ℂ_[p] Mex.det = _
    rw [RingHom.map_det]
    congr 1
    ext k k'
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, hMex, map_sum, map_mul, map_smul,
      LinearMap.sum_apply, LinearMap.smul_apply, e, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    change ((β (T (I k') a) : ℂ_[p]) * ((P.al₀ (ta a)).1 (xb b) : ℂ_[p])) * (U k b : ℂ_[p]) =
      (U k b : ℂ_[p]) * ((β (T (I k') a) : ℂ_[p]) * ((P.al₀ (ta a)).1 (xb b) : ℂ_[p]))
    ring
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h1
  rw [← h2]
  have h3 : ((pairDet (covec β T h I) U : 𝓞_ℂ_[p]) : ℂ_[p]) - ((Mex.det : 𝓞_ℂ_[p]) : ℂ_[p]) =
      (c : ℂ_[p]) * (p : ℂ_[p]) ^ n := by
    have := congrArg (algebraMap 𝓞_ℂ_[p] ℂ_[p]) hc
    rw [map_mul, map_pow, map_natCast, map_sub] at this
    exact this.symm
  rw [h3, norm_mul, norm_pow, GlobalTheory.PadicComplexHost.norm_p]
  exact mul_le_of_le_one_left (by positivity) (norm_int_le_one c)

end GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel

theorem kap_close : GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.HodgeTateKernelAtPoint → TateSt → ValueSt → BoundSt →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (τ : Psi H) (p : ℕ) [Fact p.Prime]
    [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ n : ℕ,
    ∀ (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F), OverIncl r hle → l'.A = p ^ n →
    ∀ (N : ℕ) (a : Fin N → Dw.La) (T S : Ind Dw τ.1 → Fin N → c'.V W), LatData Dw (embV c' W (conjEmb τ.1)) a T S →
    ∀ [Algebra c.F ℂ_[p]] (f : Rul Xo c) (yb : Sp 𝓞_ℂ_[p] ⟶ Y.X) (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p)
      (π : P.G.left ⟶ Y.t.G.left) (ψ : P.A.A.left ⟶ Y.oF.t.G.left) (y : FrPt Xo c ℂ_[p]), HTAt Y r ν yb yy P π ψ y →
      evR Xo c f y ≠ 0 → ∃ κ : ℂ_[p], ‖κ‖ = ‖evR Xo c f y‖ ∧
      ∀ (β : c'.V W →+* 𝓞_ℂ_[p]), yb ≫ Y.s = spMap β →
      ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber 𝓞_ℂ_[p]) ⟶ Y.t.G.left)) (U₁ U₂ : Fin g → Fin g → 𝓞_ℂ_[p])
        (h : Fin N → Fin g → 𝓞_ℂ_[p]), IsTanBasis Y.t yb e → EigAt Y.t yb (β.comp (embV c' W τ.1)) e U₁ →
        EigAt Y.t yb (β.comp (embV c' W (conjEmb τ.1))) e U₂ → HTApprox Y n yy P π ψ a e h →
        ∀ (σ : Equiv.Perm (Ind Dw τ.1)) (K₁ : Fin (Dw.mult τ.1) → Fin g) (K₂ : Fin (Dw.mult (conjEmb τ.1)) → Fin g),
          ((p : ℝ)⁻¹ ^ n < ‖((pairDet (covec β T h (σ ∘ Sum.inl)) (U₁ ∘ K₁) *
        pairDet (covec β S h (σ ∘ Sum.inr)) (U₂ ∘ K₂) : 𝓞_ℂ_[p]) : ℂ_[p])‖) →
          ∀ fv : ℂ_[p], GVal Y r ν τ.1 f yy (bcV Y.t (algebraMap 𝓞_ℂ_[p] ℂ_[p]) e) (fun k b => (U₁ (K₁ k) b : ℂ_[p]))
            (fun k b => (U₂ (K₂ k) b : ℂ_[p])) fv →
          ‖fv * ((Equiv.Perm.sign σ : ℤ) : ℂ_[p]) * (pairDet (covec β T h (σ ∘ Sum.inl)) (U₁ ∘ K₁) : 𝓞_ℂ_[p]) /
            (pairDet (covec β S h (σ ∘ Sum.inr)) (U₂ ∘ K₂) : 𝓞_ℂ_[p]) - κ‖ < ‖κ‖ := by
  classical
  intro hK hT hV _ E _ _ _ H Dw τ p _ _ hs n l l' Xo Xo' c c' W Y r ν hle hov hA N a T S hLD _ f yb yy P π ψ y hHT hev
  have inj : ∀ {A B : Type} [CommRing A] [CommRing B] (f f' : A →+* B), spMap f = spMap f' → f = f' := by
    intro A B _ _ f f' h
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  obtain ⟨β₀, hβ₀⟩ : ∃ β₀ : c'.V W →+* 𝓞_ℂ_[p], yb ≫ Y.s = spMap β₀ :=
    ⟨(Spec.preimage (yb ≫ Y.s)).hom, by simp [spMap]⟩
  have hHT' := hHT
  obtain ⟨hPt, hTe, hF, z, gm, am, x, hFC, -, -, htie, hlat⟩ := hHT'
  obtain ⟨ta, u0, hlev, hDF⟩ :=
    hT E H Dw l' Xo' c' W Y p n hs hA yb yy P π ψ hPt β₀ (conjEmb τ.1) (Ind Dw τ.1) N a T S hLD
  rw [GlobalTheory.T.integral_model_p_adic_comparison E H Dw l l' Xo Xo' c c' W Y r ν hle hov p yb yy P π ψ y hHT β₀ hβ₀] at hDF
  have heig : ∀ σ j, AvDefs.IsEig P.Gt P.oGt (embInt c P.integers σ) (x σ j) := fun σ j =>
    GlobalTheory.T.p_adic_point_complete_field E H Dw l l' Xo Xo' c c' W Y r ν p yb yy P π ψ hPt σ (x σ j) (z.u σ j) (htie σ j) (z.eig σ j)
  have hmemE : ∀ σ k, ∑ j, gm σ k j • P.bLie (x σ j) ∈ P.eigV (embInt c P.integers σ) := fun σ k =>
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (bLie_mem_eigV (heig σ j))
  have hKS := (hK p ℂ_[p] _ 𝓞_ℂ_[p] (𝓞 E) P).2.2.2
  have hmemW : ∀ σ k, ∑ j, gm σ k j • P.bLie (x σ j) ∈ P.W := fun σ k => by
    rw [hKS.2.2.2.2.2.2]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  set w₁ : Fin (Dw.mult τ.1) → P.V := fun k => ∑ j, gm τ.1 k j • P.bLie (x τ.1 j) with hw₁
  set w₂ : Fin (Dw.mult (conjEmb τ.1)) → P.V := fun k => ∑ j, gm (conjEmb τ.1) k j • P.bLie (x (conjEmb τ.1) j)
    with hw₂
  have horth : ∀ k k', P.pairV (w₁ k) (w₂ k') = 0 := fun k k' =>
    (hKS.2.2.2.2.1 _).1 (hmemW _ k) _ (hmemW _ k')
  obtain ⟨lam, hlam, hlamσ, -⟩ :=
    hV E H Dw l c p hs P τ _ _ u0 hDF w₁ w₂ (hmemE _) (hmemE _) horth (hlat _) (hlat _)
  refine ⟨lam * evR Xo c f y, by rw [norm_mul, hlam, _root_.one_mul], ?_⟩
  intro β hβ g e U₁ U₂ h htb hE1 hE2 happ σ K₁ K₂ hbig fv hGV
  have hββ : β = β₀ := inj _ _ (hβ.symm.trans hβ₀)
  subst hββ
  choose xb hxb using fun b => GlobalTheory.T.p_adic_point_frame_map E H Dw l' Xo' c' W Y p yb yy P π ψ hPt (e b) (htb.1 b)
  have hh : ∀ m b, h m b - (P.al₀ (ta m)).1 (xb b) ∈ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n} := fun m b =>
    happ m (ta m) (hlev m) b (xb b) (hxb b)
  have G1 := fun k => GlobalTheory.T.integral_model_p_adic_over_inclusion E H Dw l l' Xo Xo' c c' W Y r ν hle hov p yb yy P π ψ y hHT z gm am x hFC
    htie β hβ g e htb xb hxb τ.1 (U₁ (K₁ k)) (fun u hu => hE1.1 (K₁ k) u hu)
  have G2 := fun k => GlobalTheory.T.integral_model_p_adic_over_inclusion E H Dw l l' Xo Xo' c c' W Y r ν hle hov p yb yy P π ψ y hHT z gm am x hFC
    htie β hβ g e htb xb hxb (conjEmb τ.1) (U₂ (K₂ k)) (fun u hu => hE2.1 (K₂ k) u hu)
  choose v₁ cf₁ hv₁ hcf₁ hid₁ using G1
  choose v₂ cf₂ hv₂ hcf₂ hid₂ using G2
  have hfv := hGV y hTe hF v₁ v₂ (Matrix.of cf₁) (Matrix.of cf₂) hv₁ hv₂ hcf₁ hcf₂
  have fac : ∀ {m : ℕ} (cf : Fin m → Fin m → ℂ_[p]) (w : Fin m → P.V) (tt : Fin m → P.V)
      (L : Fin m → Fin g → 𝓞_ℂ_[p]), (∀ k, ∑ b, (L k b : ℂ_[p]) • P.bLie (xb b) = ∑ j, cf k j • w j) →
      (Matrix.of fun k k' => P.pairV (∑ b, (L k b : ℂ_[p]) • P.bLie (xb b)) (tt k')).det =
        (Matrix.of cf).det * (Matrix.of fun k k' => P.pairV (w k) (tt k')).det := by
    intro m cf w tt L hL
    rw [← Matrix.det_mul]
    congr 1
    ext k k'
    simp only [Matrix.of_apply, Matrix.mul_apply, hL, map_sum, map_smul, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul]
  set M₁ := (Matrix.of fun k k' => P.pairV (w₁ k)
    ((fun i => ∑ m, (β (T i m) : ℂ_[p]) ⊗ₜ[ℤ_[p]] ta m) (σ (Sum.inl k')))).det with hM₁
  set M₂ := (Matrix.of fun k k' => P.pairV (w₂ k)
    ((fun i => ∑ m, (β (S i m) : ℂ_[p]) ⊗ₜ[ℤ_[p]] ta m) (σ (Sum.inr k')))).det with hM₂
  have hl : ((Equiv.Perm.sign σ : ℤ) : ℂ_[p]) * M₁ = lam * M₂ := hlamσ σ
  have hA₁ : ‖((pairDet (covec β T h (σ ∘ Sum.inl)) (U₁ ∘ K₁) : 𝓞_ℂ_[p]) : ℂ_[p]) - (Matrix.of cf₁).det * M₁‖ ≤
      (p : ℝ)⁻¹ ^ n :=
    (congrArg (fun d => ‖((pairDet (covec β T h (σ ∘ Sum.inl)) (U₁ ∘ K₁) : 𝓞_ℂ_[p]) : ℂ_[p]) - d‖)
      (fac cf₁ w₁ (fun k' => ∑ m, (β (T (σ (Sum.inl k')) m) : ℂ_[p]) ⊗ₜ[ℤ_[p]] ta m) (U₁ ∘ K₁) hid₁).symm).trans_le
      (norm_minor_sub_le P n β T h ta xb hh (σ ∘ Sum.inl) (U₁ ∘ K₁))
  have hB₁ : ‖((pairDet (covec β S h (σ ∘ Sum.inr)) (U₂ ∘ K₂) : 𝓞_ℂ_[p]) : ℂ_[p]) - (Matrix.of cf₂).det * M₂‖ ≤
      (p : ℝ)⁻¹ ^ n :=
    (congrArg (fun d => ‖((pairDet (covec β S h (σ ∘ Sum.inr)) (U₂ ∘ K₂) : 𝓞_ℂ_[p]) : ℂ_[p]) - d‖)
      (fac cf₂ w₂ (fun k' => ∑ m, (β (S (σ (Sum.inr k')) m) : ℂ_[p]) ⊗ₜ[ℤ_[p]] ta m) (U₂ ∘ K₂) hid₂).symm).trans_le
      (norm_minor_sub_le P n β S h ta xb hh (σ ∘ Sum.inr) (U₂ ∘ K₂))
  have hlam0 : lam ≠ 0 := fun h0 => by rw [h0, norm_zero] at hlam; exact zero_ne_one hlam
  refine norm_quot_sub_lt n _ _ _ _ _ _ hbig hA₁ hB₁ ?_ (mul_ne_zero hlam0 hev)
  linear_combination (((Equiv.Perm.sign σ : ℤ) : ℂ_[p]) * M₁) * hfv + ((Matrix.of cf₂).det * evR Xo c f y) * hl

end GlobalTheory.FlatModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelMapExtension
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModelOpen

theorem unit_loc : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.CanonicalExtensionRankOne → GlobalTheory.Published.DeRhamCanonicalExtension →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F)
    (r₀ : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r₀) (x : ℝ), Laws U x →
    ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ)
      (Xw : Y.X.Opens), p.Prime → IsCover Y r hle Z la p Xw →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] (ξ : Sp A ⟶ Y.X) (β : c'.V W →+* A),
      IsOpenImmersion ξ → ξ ≫ Y.s = spMap β → IsUnit (p : A) → ξ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ∈ Xw →
    ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber A) ⟶ Y.t.G.left)) (U₁ h₁ : Fin (Dw.mult τ.1) → Fin g → A)
      (U₂ h₂ : Fin (Dw.mult (conjEmb τ.1)) → Fin g → A), IsTanBasis Y.t ξ e →
      (∀ (S : Type) [CommRing S] (φ : A →+* S),
        EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W τ.1))) (bcV Y.t φ e) (fun k b => φ (U₁ k b)) ∧
        EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W (conjEmb τ.1)))) (bcV Y.t φ e) fun k b => φ (U₂ k b)) →
      IsUnit (pairDet h₁ U₁) → IsUnit (pairDet h₂ U₂) →
    ∀ 𝔭 : PrimeSpectrum A, ξ 𝔭 ∈ Set.range Y.j → ∃ u : (Localization.AtPrime 𝔭.asIdeal)ˣ,
      ∀ (k : Type) [Field k] (φ : Localization.AtPrime 𝔭.asIdeal →+* k), SecValAt Y r ν τ.1 s.sig ξ e U₁ U₂ k (φ.comp (algebraMap A _)) (φ u) := by
  intro _ _ _ E _ _ _ H Dw l l' Xo Xo' c c' W Y r ν hle r₀ U x _ Z τ s la p Xw _ hcov A _ _ _ ξ β _ hβ _ hgen
    g e U₁ h₁ U₂ h₂ he heig hu₁ hu₂ 𝔭 h𝔭
  haveI := GlobalTheory.TriplesAlong.isOpenImmersion_j W Y
  obtain ⟨yL, hyL⟩ := GlobalTheory.T.lift_to_local_ring_open_immersion Y.j ξ 𝔭 h𝔭
  have hinj : Function.Injective (algebraMap A (Localization.AtPrime 𝔭.asIdeal)) :=
    IsLocalization.injective _ 𝔭.asIdeal.primeCompl_le_nonZeroDivisors
  obtain ⟨alg, z, w₁, w₂, hz, hc₁, hc₂, hz₁, hz₂⟩ := GlobalTheory.T.integral_model_tangent_over_inclusion E H Dw l l' Xo Xo' c c' W Y r ν hle hcov.1 τ A ξ β
    hβ g e U₁ h₁ U₂ h₂ he heig hu₁ hu₂ (Localization.AtPrime 𝔭.asIdeal) (algebraMap A _) yL hyL
  have hlies : LiesOn Z z := by
    intro q
    have hZc : IsClosed (Z : Set (Xo.XF c)) := isClosed_of_mem_irreducibleComponents _ Z.2
    have h1 : Y.j (yL (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Localization.AtPrime 𝔭.asIdeal))) ∈ Xw := by
      have e : (yL ≫ Y.j) (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Localization.AtPrime 𝔭.asIdeal)) =
          Y.j (yL (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Localization.AtPrime 𝔭.asIdeal))) := Scheme.Hom.comp_apply _ _ _
      rw [← e, hyL, bot_map hinj]; exact hgen
    have h0 : ptF z (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Localization.AtPrime 𝔭.asIdeal)) ∈ (Z : Set (Xo.XF c)) := by
      have e : (yL ≫ r) (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Localization.AtPrime 𝔭.asIdeal)) =
          r (yL (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Localization.AtPrime 𝔭.asIdeal))) := Scheme.Hom.comp_apply _ _ _
      rw [hz, e]; exact hcov.2.2.2.2.2.2.1 _ h1
    have hs : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Localization.AtPrime 𝔭.asIdeal)) ⤳ q :=
      (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
    exact (hs.map (ptF z).continuous).mem_closed hZc h0
  have hT : Tested z := GlobalTheory.FlagTan.fromTest_of_isLocalRing z
  have hone : evR Xo c s.sig z * evR Xo c s.inv z = 1 := by
    rw [← evR_idem hlies hT, ← s.mul_inv]
    exact (Formalism.L2.Pj.evalAt_mul _ _ _ _ _).symm
  have hU : IsUnit (evR Xo c s.sig z) := IsUnit.of_mul_eq_one _ hone
  refine ⟨hU.unit, fun k _ φ => ?_⟩
  intro alg' yy hyy y _ hy w₁' w₂' g₁ g₂ hw₁ hw₂ hg₁ hg₂
  have hyy' : yy = spMap φ ≫ yL := by
    apply (cancel_mono Y.j).1
    rw [hyy, Category.assoc, hyL, sp_sp]
  have hcomp : algebraMap c.F k = φ.comp (algebraMap c.F (Localization.AtPrime 𝔭.asIdeal)) := by
    have e1 : ptF y ≫ pullback.snd _ _ = spMap (algebraMap c.F k) := pullback.lift_snd _ _ _
    have e2 : ptF z ≫ pullback.snd _ _ = spMap (algebraMap c.F (Localization.AtPrime 𝔭.asIdeal)) :=
      pullback.lift_snd _ _ _
    have e3 : spMap (algebraMap c.F k) = spMap (φ.comp (algebraMap c.F (Localization.AtPrime 𝔭.asIdeal))) := by
      rw [← e1, hy, hyy', Category.assoc, Category.assoc, ← Category.assoc yL, ← hz, e2, spMap_spMap]
    have e4 := Spec.map_injective e3
    exact congrArg CommRingCat.Hom.hom e4
  let φA : Localization.AtPrime 𝔭.asIdeal →ₐ[c.F] k :=
    { φ with commutes' := fun a => (RingHom.congr_fun hcomp a).symm }
  obtain ⟨zk, hzk⟩ := GlobalTheory.FlagTan.exists_frMap φA z
  have hev : evR Xo c s.sig zk = φ (evR Xo c s.sig z) := GlobalTheory.FlagTan.evR_frMap s.sig_mem.1 hzk
  have hx : zk.x = y.x := by
    have e1 : y.x = ptF y ≫ pullback.fst _ _ := (pullback.lift_fst _ _ _).symm
    have e2 : z.x = ptF z ≫ pullback.fst _ _ := (pullback.lift_fst _ _ _).symm
    rw [hzk.1, e1, e2, hy, hz, hyy']
    simp only [Category.assoc]
  have hv₁ : ∀ i, zk.u τ.1 i = w₁' i ≫ ν.φ := by
    intro i
    have h2 := hw₁ i
    rw [hyy', Category.assoc, ← bcV_bcV] at h2
    have hw := GlobalTheory.T.tangent_frame_base_change Y φ yL _ _ (w₁ i) (w₁' i) (hc₁ i) h2
    rw [hzk.2.1 τ.1 i, hz₁ i, hw, Category.assoc]
  have hv₂ : ∀ i, zk.u (conjEmb τ.1) i = w₂' i ≫ ν.φ := by
    intro i
    have h2 := hw₂ i
    rw [hyy', Category.assoc, ← bcV_bcV] at h2
    have hw := GlobalTheory.T.tangent_frame_base_change Y φ yL _ _ (w₂ i) (w₂' i) (hc₂ i) h2
    rw [hzk.2.1 (conjEmb τ.1) i, hz₂ i, hw, Category.assoc]
  have key := GlobalTheory.T.flat_section_frame_invariance τ s.sig_mem zk y hx g₁ g₂ (fun i => by rw [hv₁ i]; exact hg₁ i)
    (fun i => by rw [hv₂ i]; exact hg₂ i)
  rw [hev] at key
  rw [IsUnit.unit_spec]
  exact key

end GlobalTheory.FlatModelOpen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPointExtensionSplitStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_point_extension_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X) (K : Type) [Field K] [CharZero K] (ξ : Sp K ⟶ X) (q : ℕ), q ≠ 0 → (∃ ζ : K, IsPrimitiveRoot ζ q) → SplitK t ξ q → ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsLocalRing R] [Algebra R K] [IsFractionRing R K] (x : Sp R ⟶ X), spMap (algebraMap R K) ≫ x = ξ → Finite (TorsK t ξ q →* Kˣ) ∧ ∀ (p : ℕ) [Fact p.Prime] (ψ : R →+* ↥(intO ℂ_[p])) (z : Sp ↥(intO ℂ_[p]) ⟶ X), IsLocalHom ψ → spMap ψ ≫ x = z → (∀ χ : TorsK t ξ q →* Kˣ, ∃ c : TorsChar t z q, InducedBy χ x (algebraMap R K) ψ c) ∧ (∀ c : TorsChar t z q, ∃ χ : TorsK t ξ q →* Kˣ, InducedBy χ x (algebraMap R K) ψ c) ∧ ∀ (χ : TorsK t ξ q →* Kˣ) (c c' : TorsChar t z q), InducedBy χ x (algebraMap R K) ψ c → InducedBy χ x (algebraMap R K) ψ c' → Agree c c' := by
  first | exact @GlobalTheory.HtChar.induced_chars | exact GlobalTheory.HtChar.induced_chars | (intros; apply GlobalTheory.HtChar.induced_chars <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPointPlaceConditionStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_point_place_condition : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (l : ℕ) (U : V.X.Opens) (g : V.X.functionField), (∀ z : V.G, V.j z ∈ U → RegAt (V.j z) g) → (∀ (v : HeightOneSpectrum (𝓞 F)) (e : TrueGeo.Ext v) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X), (l : 𝓞 F) ∈ v.asIdeal → z ≫ V.π ≫ Y.str = spMap (algebraMap F (AlgebraicClosure F)) → spMap e.O.subtype ≫ yt = z ≫ V.j → ⊤ ≤ yt ⁻¹ᵁ U → e.w (TrueGeo.valAt (z ≫ V.j) g) ≤ 1) → ∀ x ∈ U, (l : 𝓞 F) ∈ (V.p x).asIdeal → RegAt x g := by
  first | exact @GlobalTheory.HtGen.RegOver.regAt_of_integral_values_over | exact GlobalTheory.HtGen.RegOver.regAt_of_integral_values_over | (intros; apply GlobalTheory.HtGen.RegOver.regAt_of_integral_values_over <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPointTorsionSplitStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_point_torsion_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X) (K : Type) [Field K] [CharZero K] (ξ : Sp K ⟶ X) (p : ℕ) [Fact p.Prime] (n : ℕ), SplitK t ξ (p ^ n) → ∀ (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Algebra A K] [IsFractionRing A K] (x₀ : Sp A ⟶ X), spMap (algebraMap A K) ≫ x₀ = ξ → ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber A) ⟶ t.G.left)), (∀ i, IsTanAtG t x₀ (e i)) → ∀ χ : TorsK t ξ (p ^ n) →* Kˣ, ∃ h : Fin g → A, ∀ (R : Type) [CommRing R] (φ : A →+* R) (u : R →+* K) (x : Sp R ⟶ X) (ψ : R →+* ↥(intO ℂ_[p])) (z : Sp ↥(intO ℂ_[p]) ⟶ X) (c : TorsChar t z (p ^ n)), u.comp φ = algebraMap A K → spMap φ ≫ x₀ = x → IsLocalHom ψ → spMap ψ ≫ x = z → InducedBy χ x u ψ c → DlogIs t p n c (fun i => spMap (dualMap (ψ.comp φ)) ≫ e i) (fun i => ψ (φ (h i))) := by
  first | exact @GlobalTheory.HtGen.dlog_regular_of_chart | exact GlobalTheory.HtGen.dlog_regular_of_chart | (intros; apply GlobalTheory.HtGen.dlog_regular_of_chart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralRelationUniformisedHomConvolutionExpansiAlt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section
namespace GlobalTheory.Mum.Two.Mix

def mixφ {R : Type} [CommRing R] [IsDomain R] (D₁ D₂ : DegPre R) (b : D₁.P.A ⟶ D₂.P.A) (α : D₁.X) :
    PUnit.{1} ⊕ Fin 4 → (D₁.P.A.left ⟶ D₁.P.A.left ⨿ D₂.P.A.left) :=
  Sum.elim (fun _ => b.left ≫ coprod.inr) (fun k => D₁.famφB α k ≫ coprod.inl)

end GlobalTheory.Mum.Two.Mix
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrallyClosedGenericExtensionStatement
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrally_closed_generic_extension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l' : Level H)
    (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (p : ℕ)
    [Fact p.Prime] (n : ℕ), l'.A = p ^ n →
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (ξ : Sp R ⟶ Y.X)
      (y : Sp (FractionRing R) ⟶ Xo'.XF c'), spMap (algebraMap R (FractionRing R)) ≫ ξ = y ≫ Y.j → ∀ a : Dw.La,
    ∃ κ : (Sp (FractionRing R) ⟶ Y.t.G.left) → Rˣ, GlobalTheory.HTMap.Mult Y.t ξ (p ^ n) κ ∧
      ∀ (e σ : Over.mk y ⟶ Y.oF.t.G), e.left = y ≫ (Y.oF.etaA a).left → σ ^ (p ^ n) = 1 →
        Out.WeilIs Y.oF.t.G Y.oF.t.PP.L ((p ^ n : ℕ) : ℤ) e σ
          (unitOn (Units.map (algebraMap R (FractionRing R)).toMonoidHom (κ (σ.left ≫ Y.m.φ)))) := by
  first | exact @GlobalTheory.HTLocWeil.weil_kappa | exact GlobalTheory.HTLocWeil.weil_kappa | (intros; apply GlobalTheory.HTLocWeil.weil_kappa <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleSpaceFibreSemiAbelianFieldPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducibleSpace_fibre_semiAbelian_fieldPoint : ∀ (T : Scheme.{0}) (G : Over T) [GrpObj G], IsSemiAbelian G → ∀ (Ω : Type) [Field Ω] (x : Sp Ω ⟶ T), IrreducibleSpace (pullback G.hom x : Scheme.{0}) := by
  first | exact @GlobalTheory.SemiAbFibre.irreducibleSpace_fibre | exact GlobalTheory.SemiAbFibre.irreducibleSpace_fibre | (intros; apply GlobalTheory.SemiAbFibre.irreducibleSpace_fibre <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageGenericBaseChangeModificatio
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem isAffineOpen_preimage_genericBaseChange : ∀ (R : Type) [CommRing R] [IsDomain R] (M : Modif R) (G : Over M.S) (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)), IsPullback α t G.hom M.gp → ∀ W : G.left.Opens, IsAffineOpen W → IsAffineOpen (α ⁻¹ᵁ W) := by
  intro R _ _ M G Y α t h W hW
  haveI := M.proper
  haveI : M.S.IsSeparated := by
    constructor
    rw [← terminal.comp_from M.π]
    infer_instance
  haveI : IsAffineHom M.gp := by
    haveI : IsAffineHom (M.gp ≫ terminal.from M.S) := inferInstance
    exact IsAffineHom.of_comp M.gp (terminal.from M.S)
  haveI : IsAffineHom α := MorphismProperty.of_isPullback (P := @IsAffineHom) h.flip inferInstance
  exact hW.preimage α

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleTensorNefAmpleFiniteFieldFibreStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAmple_tensor_nef_ample_finiteFieldFibre : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ L A : HermLB p, NefFib L → IsAmpleLB A.B → ∀ (l : ℕ) [Fact l.Prime], IsAmpleLB ((L.tens A).B.pull (Limits.pullback.fst (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod l))))) := by
  first | exact @GlobalTheory.AmpleFibre.isAmpleLB_fibre | exact GlobalTheory.AmpleFibre.isAmpleLB_fibre | (intros; apply GlobalTheory.AmpleFibre.isAmpleLB_fibre <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArithVarOfIntStatement
section
open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CovTest GlobalTheory.Published
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_regular_integral_cover_same_dimension : RegularAlteration → ∀ (k : Type) [CommRing k] (Z : Scheme.{0}) [IsIntegral Z] (r : Z ⟶ Sp k) (d : ℕ),
    IsArithVar r d → ∃ (B' : Scheme.{0}) (_ : IsIntegral B') (ρ : B' ⟶ Z), IsArithVar (ρ ≫ r) d ∧
      (∀ b : B', IsRegularLocalRing (B'.presheaf.stalk b)) ∧ ρ (genericPoint B') = genericPoint Z ∧
      ρ.residueDegree (genericPoint B') ≠ 0 := by
  first | exact @GlobalTheory.AlterationOrder.regularAlteration_order | exact GlobalTheory.AlterationOrder.regularAlteration_order | (intros; apply GlobalTheory.AlterationOrder.regularAlteration_order <;> assumption)
end

