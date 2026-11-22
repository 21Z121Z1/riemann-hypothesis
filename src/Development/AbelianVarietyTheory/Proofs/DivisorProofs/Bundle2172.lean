import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsGenericComponentPointsOffMeagre
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0041
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0579
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0568
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1584
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1581
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0363
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEqMulOfContinuousOnQuotient
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0003
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0084
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0033
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2155
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2116

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionQuotientOfContinuousReading
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SecDivision

open NumberField Topology Filter
open scoped Matrix

theorem dvd_of_locally_bounded {K A : Type} [Field K] [NumberField K] [CommRing A] [IsDomain A] [Algebra K A]
    [Algebra.Smooth K A] (σ : K →+* ℂ) {a b : A} (ha : a ≠ 0)
    (H : ∀ (m : ℕ) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → (A →+* ℂ)), IsOpen B →
      (∀ z ∈ B, (φ z).comp (algebraMap K A) = σ) → (∀ u : A, DifferentiableOn ℂ (fun z => φ z u) B) →
      ∀ z₀ ∈ B, ∃ n : ℕ, n ≠ 0 ∧ ∃ M : ℝ, ∀ᶠ z in 𝓝 z₀, ‖φ z b‖ ^ n ≤ M * ‖φ z a‖ ^ n) : a ∣ b := by
  haveI : IsIntegrallyClosed A := isIntegrallyClosed_of_smooth K A
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  by_contra hn
  obtain ⟨p, hp, s, r, hs, hr, h⟩ := GlobalTheory.ContinuousQuotient.exists_prime_of_not_dvd ha hn
  letI : Algebra K ℂ := σ.toAlgebra
  have h0 : Ideal.Quotient.mkₐ K p s ≠ 0 := fun h => hs (Ideal.Quotient.eq_zero_iff_mem.mp h)
  obtain ⟨e, he⟩ := not_forall.mp fun h => h0 (GlobalTheory.FiniteOrderRule.eq_zero_of_forall_algHom (K := K) (Ω := ℂ) _ h)
  obtain ⟨ι, -, m, B, φ, hB, hφσ, hd, hcov, hne⟩ := GlobalTheory.T.exists_countable_holomorphic_families_smooth K A σ
  let ψ : A →ₐ[K] ℂ := e.comp (Ideal.Quotient.mkₐ K p)
  obtain ⟨i, z₀, hz₀, hψ⟩ := hcov ψ.toRingHom (RingHom.ext fun k => ψ.commutes k)
  obtain ⟨n, hn0, M, hM⟩ := H _ _ _ (hB i) (hφσ i) (hd i) z₀ hz₀
  have hc : ∀ u, ContinuousAt (fun z => φ i z u) z₀ := fun u =>
    (hd i u).continuousOn.continuousAt ((hB i).mem_nhds hz₀)
  have hr0 : φ i z₀ r = 0 := by
    rw [hψ]
    change e (Ideal.Quotient.mk p r) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr, map_zero]
  have hs0 : φ i z₀ s ≠ 0 := by rw [hψ]; exact he
  have hlt : ∀ᶠ z in 𝓝 z₀, M * ‖φ i z r‖ ^ n < ‖φ i z s‖ ^ n := by
    refine ContinuousAt.eventually_lt (continuousAt_const.mul ((hc r).norm.pow n)) ((hc s).norm.pow n) ?_
    simp only [hr0, norm_zero, zero_pow hn0, mul_zero]
    exact pow_pos (norm_pos_iff.2 hs0) n
  obtain ⟨z, hz, h1, h2⟩ := ((hne i z₀ hz₀ a ha).and_eventually (hM.and hlt)).exists
  have h3 : ‖φ i z a‖ ^ n * ‖φ i z s‖ ^ n = ‖φ i z b‖ ^ n * ‖φ i z r‖ ^ n := by
    rw [← mul_pow, ← mul_pow, ← norm_mul, ← norm_mul, ← map_mul, ← map_mul, h]
  have h4 : 0 < ‖φ i z a‖ ^ n := pow_pos (norm_pos_iff.2 hz) n
  have h5 := mul_le_mul_of_nonneg_right h1 (pow_nonneg (norm_nonneg (φ i z r)) n)
  have h6 := mul_lt_mul_of_pos_left h2 h4
  nlinarith

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.GenericFrames GlobalTheory.AllWt GlobalTheory.FlatLine
  GlobalTheory.CompHt GlobalTheory.FlagTan

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem exists_near_frames (U : Unf Xo c σ r) (hσ : GoodEmb c σ) (hU : IsUnf U) {A : Type} [CommRing A]
    [Algebra c.F A] (yA : FrPt Xo c A) {m : ℕ} {B : Set (Fin m → ℂ)} (φ : (Fin m → ℂ) → (A →ₐ[c.F] CAt σ))
    (y : (Fin m → ℂ) → FrPt Xo c (CAt σ)) (hB : IsOpen B) (hφ : ∀ a, DifferentiableOn ℂ (fun b => toC (φ b a)) B)
    (hy : ∀ b ∈ B, FrMap (φ b) yA (y b)) {b₀ : Fin m → ℂ} (hb₀ : b₀ ∈ B) :
    ∃ (k : U.Comp) (x₀ : (U.X k).dom), (∃ t, FrBor t (U.un k x₀) (y b₀)) ∧ ∀ V ∈ 𝓝 x₀.1, ∀ᶠ b in 𝓝 b₀,
      ∃ x : (U.X k).dom, x.1 ∈ V ∧ ∃ t, FrBor t (U.un k x) (y b) ∧ ∀ i, t (some i) = 1 := by
  obtain ⟨hr, hty, hsur, -, -, g, e, F, ik, ψ, hef, hun⟩ := hU
  obtain ⟨B', k', P, hB', hb', hs, hP, hyP⟩ :=
    GlobalTheory.AdaptedPeriods.exists_holPeriods_adapted E H Dw l Xo c σ g e F A yA m B φ y hB hφ hy b₀ hb₀
  obtain ⟨k, ⟨x₁, hx₁⟩, t₁, ht₁⟩ := hsur (y b₀)
  obtain ⟨P₁, hP₁, hP₁', hu₁, -⟩ := hun k ⟨x₁, hx₁⟩
  obtain rfl : ik k = k' := F.disj _ _ _ _ hP₁' (hP.1 b₀ hb') (hu₁.symm.trans (ht₁.1.symm.trans (hyP b₀ hb').1))
  obtain ⟨idx, hper, -, honto⟩ := dictionary c σ e _ (U.X k) (ψ k) hσ (F.sig _).1 (F.sig _).2 hr
    (hty k).1 (hty k).2 (hef k) (GlobalTheory.FrameSign.im_neg_of_isPeriod E H Dw l c σ g e _ r (U.X k) (ψ k) hσ hr
      (hty k).1 (hty k).2 (hef k) x₁ hx₁ P₁ hP₁ hP₁')
  have hbor : ∀ x (hx : x ∈ (U.X k).dom), ∀ b ∈ B',
      (∀ a j, pc (U.X k) x (ψ k a : Fin r → E) (idx j).1 (idx j).2 = P b a j) →
      ∃ t, FrBor t (U.un k ⟨x, hx⟩) (y b) ∧ ∀ i, t (some i) = 1 := by
    intro x hx b hb hh
    obtain ⟨P₀, hP₀, hP₀', hux, hud, -⟩ := hun k ⟨x, hx⟩
    have hPS : ∀ v, P₀ v = (1 : Matrix (Fin g) (Fin g) ℂ) *ᵥ P b v := fun v => funext fun j => by
      rw [Matrix.one_mulVec]
      exact (hP₀ v j).trans ((hper _ _ j).trans (hh v j))
    obtain ⟨t, ht, ht1⟩ := GlobalTheory.FrameNorm.frBor_of_triangular_period E H Dw l Xo c σ g e F _ (P b) P₀ 1 (y b)
      (U.un k ⟨x, hx⟩) (hP.1 b hb) hP₀' hPS (fun j j' hj => by
        obtain rfl : j = j' := by
          by_contra hjj
          exact hj (Matrix.one_apply_ne hjj)
        exact ⟨rfl, le_rfl⟩) (hyP b hb).1 hux (hyP b hb).2 hud
    refine ⟨t, ht, fun i => Units.ext ?_⟩
    have := ht1 (e.symm i)
    rw [Equiv.apply_symm_apply, Matrix.one_apply_eq] at this
    exact this
  choose! x₂ hx₂ hr₂ using fun b (hb : b ∈ B') => honto (P b) (hP.1 b hb)
  have hBn : ∀ᶠ b in 𝓝 b₀, b ∈ B' := hB'.mem_nhds hb'
  refine ⟨k, ⟨x₂ b₀, hx₂ b₀ hb'⟩, (hbor _ _ b₀ hb' (hr₂ b₀ hb')).imp fun _ h => h.1, fun V hV => ?_⟩
  have key := GlobalTheory.T.period_coordinates_frames_lift_tendsto E r (U.X k) _ (𝓝 b₀) (x₂ b₀) x₂ (hx₂ b₀ hb') (hBn.mono hx₂) (fun v hv τ i => by
    obtain ⟨a, rfl⟩ : ∃ a, (ψ k a : Fin r → E) = v := ⟨(ψ k).symm ⟨v, hv⟩, by simp⟩
    obtain ⟨j, hj⟩ := idx.surjective (τ, i)
    obtain ⟨rfl, rfl⟩ : τ = (idx j).1 ∧ i = (idx j).2 := by rw [hj]; exact ⟨rfl, rfl⟩
    change Tendsto (fun b => pc (U.X k) (x₂ b) (ψ k a) _ _) _ (𝓝 (pc (U.X k) (x₂ b₀) (ψ k a) _ _))
    rw [hr₂ b₀ hb']
    have hc : ContinuousAt (fun b => P b a j) b₀ :=
      (continuous_apply j).continuousAt.comp ((hP.2 a).continuousOn.continuousAt hBn)
    exact hc.tendsto.congr' (hBn.mono fun b hb => (hr₂ b hb a j).symm)) _
    (inter_mem hV ((FourierCoefficientDomain.isOpen_dom _).mem_nhds (hx₂ b₀ hb')))
  filter_upwards [hBn, key] with b hb ⟨x, ⟨hxV, hx⟩, hxx⟩
  exact ⟨⟨x, hx⟩, hxV, hbor x hx b hb fun a j => (hxx _ _ _).trans (hr₂ b hb a j)⟩

theorem toC_evR_frBor {e : Ix Dw → ℤ} {f : Rul Xo c} (hf : f ∈ secZ Xo c e) {t : Ix Dw → (CAt σ)ˣ}
    {y y' : FrPt Xo c (CAt σ)} (h : FrBor t y y') (ht : ∀ i, t (some i) = 1) :
    toC (evR Xo c f y') = toC (t none : CAt σ) ^ e none * toC (evR Xo c f y) := by
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  rw [evR_frBor hf h, Finset.prod_eq_single none (fun i _ hi => by
    obtain ⟨j, rfl⟩ := Option.ne_none_iff_exists'.1 hi
    rw [ht, one_zpow]) (fun h => absurd (Finset.mem_univ _) h), Units.val_zpow_eq_zpow_val]
  rfl

theorem rdU_apply (U : Unf Xo c σ r) (f : Rul Xo c) (k : U.Comp) (x : (U.X k).dom) :
    rdU U f k x.1 = toC (evR Xo c f (U.un k x)) := dif_pos x.2

theorem chart_dvd (U : Unf Xo c σ r) (hσ : GoodEmb c σ) (hU : IsUnf U) {h : GenFrEx Xo c} (C : FChart h)
    {e e' : Ix Dw → ℤ} {f g : Rul Xo c} (hf : f ∈ secZ Xo c e) (hg : g ∈ secZ Xo c e') (q : FDSec U.X)
    (hq : ∀ k, ContinuousOn (q k) (U.X k).dom)
    (hfg : ∀ z ∈ framesOn U C.Z, rdU U g z.1 z.2 = q z.1 z.2 * rdU U f z.1 z.2) {a b : C.R} (ha0 : a ≠ 0)
    (ha : ∀ (ψ : C.R →ₐ[c.F] CAt σ) (z : FrPt Xo c (CAt σ)), FrMap ψ C.y z → evR Xo c f z = ψ a)
    (hb : ∀ (ψ : C.R →ₐ[c.F] CAt σ) (z : FrPt Xo c (CAt σ)), FrMap ψ C.y z → evR Xo c g z = ψ b) : a ∣ b := by
  classical
  haveI := C.sm
  refine dvd_of_locally_bounded σ ha0 fun m B φ hB hφσ hd z₀ hz₀ => ?_
  let mk : ∀ z ∈ B, C.R →ₐ[c.F] CAt σ := fun z hz =>
    { (show C.R →+* CAt σ from φ z) with commutes' := fun a => RingHom.congr_fun (hφσ z hz) a }
  let φ' : (Fin m → ℂ) → (C.R →ₐ[c.F] CAt σ) := fun z => if hz : z ∈ B then mk z hz else mk z₀ hz₀
  have hφ' : ∀ z ∈ B, ∀ u, toC (φ' z u) = φ z u := by
    intro z hz u
    simp only [φ', dif_pos hz]
    rfl
  choose y hy using fun z => exists_frMap (φ' z) C.y
  obtain ⟨k, x₀, ⟨t₀, ht₀⟩, hnear⟩ := exists_near_frames U hσ hU C.y φ' y hB
    (fun u => (hd u).congr fun z hz => hφ' z hz u) (fun z _ => hy z) hz₀
  obtain ⟨n, hn, hev, η, hη, hη0⟩ := exists_even_sec_evR_ne_zero E H Dw l Xo c σ (y z₀)
  have hηc : ContinuousOn (rdU U η k) (U.X k).dom :=
    (hU.2.2.2.2.1 0 n ⟨fun _ _ _ _ => le_rfl, hev⟩ η hη k).1.continuousOn
  rw [← secZ_nat] at hη
  obtain ⟨w, -, hw⟩ := GlobalTheory.DegCmp.fChart_exists_val C hη
  have hBn : ∀ᶠ z in 𝓝 z₀, z ∈ B := hB.mem_nhds hz₀
  have hdn : (U.X k).dom ∈ 𝓝 x₀.1 := (FourierCoefficientDomain.isOpen_dom _).mem_nhds x₀.2
  have hw0 : φ z₀ w ≠ 0 := by
    rw [← hφ' z₀ hz₀, ← hw _ _ _ (hy z₀)]; exact hη0
  have hx0 : rdU U η k x₀.1 ≠ 0 := by
    letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
    rw [rdU_apply]
    intro h0
    apply hη0
    rw [evR_frBor hη ht₀, show evR Xo c η (U.un k x₀) = 0 from h0, mul_zero]
  let G : (Fin m → ℂ) × Frame (U.X k).Ψ r → ℝ := fun p =>
    ‖(φ p.1 w / rdU U η k p.2) ^ (e' none - e none) * q k p.2 ^ n‖
  have hG : ContinuousAt G (z₀, x₀.1) := by
    have c1 : ContinuousAt (fun p : (Fin m → ℂ) × Frame (U.X k).Ψ r => φ p.1 w) (z₀, x₀.1) :=
      ContinuousAt.comp (g := fun z => φ z w) ((hd w).continuousOn.continuousAt hBn) continuousAt_fst
    have c2 : ContinuousAt (fun p : (Fin m → ℂ) × Frame (U.X k).Ψ r => rdU U η k p.2) (z₀, x₀.1) :=
      ContinuousAt.comp (g := rdU U η k) (hηc.continuousAt hdn) continuousAt_snd
    have c3 : ContinuousAt (fun p : (Fin m → ℂ) × Frame (U.X k).Ψ r => q k p.2) (z₀, x₀.1) :=
      ContinuousAt.comp (g := q k) ((hq k).continuousAt hdn) continuousAt_snd
    exact (((c1.div c2 hx0).zpow₀ _ (Or.inl (div_ne_zero hw0 hx0))).mul (c3.pow n)).norm
  have hlt : ∀ᶠ p in 𝓝 (z₀, x₀.1), G p < G (z₀, x₀.1) + 1 := hG.eventually_lt continuousAt_const (lt_add_one _)
  rw [nhds_prod_eq, eventually_prod_iff] at hlt
  obtain ⟨pa, hpa, pb, hpb, hlt⟩ := hlt
  have hV : ∀ᶠ x in 𝓝 x₀.1, pb x ∧ rdU U η k x ≠ 0 := hpb.and ((hηc.continuousAt hdn).eventually_ne hx0)
  refine ⟨n, hn.ne', G (z₀, x₀.1) + 1, ?_⟩
  filter_upwards [hBn, hpa, hnear _ hV] with z hz hza ⟨x, ⟨hx1, hx2⟩, t, ht, ht1⟩
  have hon : LiesOn C.Z (U.un k x) := fun s => by
    rw [← GlobalTheory.UnifComp.ptF_frBor ht, GlobalTheory.UnifComp.ptF_frMap (hy z), AlgebraicGeometry.Scheme.Hom.comp_apply]
    exact GlobalTheory.UnifComp.liesOn_chart C _
  have e0 : rdU U g k x.1 = q k x.1 * rdU U f k x.1 := hfg ⟨k, x.1⟩ ⟨x.2, hon⟩
  have e1 := toC_evR_frBor hf ht ht1
  have e2 := toC_evR_frBor hg ht ht1
  have e3 := toC_evR_frBor hη ht ht1
  rw [ha _ _ (hy z), hφ' z hz, ← rdU_apply] at e1
  rw [hb _ _ (hy z), hφ' z hz, ← rdU_apply] at e2
  rw [hw _ _ _ (hy z), hφ' z hz, ← rdU_apply] at e3
  have hT : toC (t none : CAt σ) ≠ 0 := (show ℂˣ from t none).ne_zero
  generalize toC (t none : CAt σ) = T at e1 e2 e3 hT
  have e4 : φ z w / rdU U η k x.1 = T ^ n := by
    rw [div_eq_iff hx2, e3, ← zpow_natCast]; rfl
  have e5 : φ z b = T ^ (e' none - e none) * q k x.1 * φ z a := by
    rw [e1, e2, e0, zpow_sub₀ hT]
    field_simp
  have e6 : ‖φ z b‖ ^ n = G (z, x.1) * ‖φ z a‖ ^ n := by
    simp only [G]
    rw [e4, e5, ← norm_pow, ← norm_pow, ← norm_mul, mul_pow, mul_pow, ← zpow_natCast T, ← zpow_mul,
      ← zpow_natCast (T ^ _), ← zpow_mul, mul_comm (n : ℤ)]
  rw [e6]
  exact mul_le_mul_of_nonneg_right (hlt hza hx1).le (pow_nonneg (norm_nonneg _) _)

open IsDedekindDomain Module Formalism.BasicNotions GlobalTheory.FlatCore in

theorem exists_quotient : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (e e' : Ix Dw → ℤ) (f g : Rul Xo c), f ∈ secZ Xo c e → f ∈ suppOn Z → g ∈ secZ Xo c e' → g ∈ suppOn Z → f ≠ 0 → ∀ σ, GoodEmb c σ → ∀ q : FDSec (U σ).X, (∀ k, ContinuousOn (q k) ((U σ).X k).dom) → (∀ z ∈ framesOn (U σ) Z, rdU (U σ) g z.1 z.2 = q z.1 z.2 * rdU (U σ) f z.1 z.2) → ∃ s ∈ secZ Xo c (e' - e), idem Z * s = s ∧ s * f = g := by
  intro E _ _ _ H Dw l Xo c r U x hL Z e e' f g hf hfZ hg hgZ hf0 σ hσ q hq hfg
  obtain ⟨-, -, h, -⟩ := evLaws_genFr_atlas E H Dw l Xo c
  have off : ∀ {u : Rul Xo c}, u ∈ suppOn Z → ∀ Z', Z' ≠ Z → genVal Z' u = 0 := fun hu Z' hZ => by
    rw [genVal_apply h]; exact evC_eq_zero h hZ hu
  have hfz : genVal Z f ≠ 0 := fun h0 => hf0 (secZ_eq_zero_of_genVal hf fun Z' => by
    by_cases hZ : Z' = Z
    · rw [hZ, h0]
    · exact off hfZ Z' hZ)
  obtain ⟨s, hs, hsv⟩ := GlobalTheory.SecGlueInt.exists_secZ_of_regular E H Dw l Xo c h (e' - e)
    (fun Z' => genVal Z' g / genVal Z' f) fun C => by
      by_cases hZ : C.Z = Z
      swap
      · rw [off hgZ _ hZ, zero_div, mul_zero]; exact zero_mem _
      subst hZ
      obtain ⟨a, ha1, ha2⟩ := GlobalTheory.DegCmp.fChart_exists_val C hf
      obtain ⟨b, hb1, hb2⟩ := GlobalTheory.DegCmp.fChart_exists_val C hg
      have ha0 : (a : Om C.Z) ≠ 0 := by rw [ha1]; exact mul_ne_zero (Units.ne_zero _) hfz
      obtain ⟨u, hu⟩ := chart_dvd (U σ) hσ (hL.unf σ hσ) C hf hg q hq hfg (fun h0 => ha0 (by rw [h0]; rfl))
        (ha2 _) (hb2 _)
      have hu' : (b : Om C.Z) = a * u := by rw [hu]; rfl
      have hp : (∏ i, C.t i ^ e' i) = (∏ i, C.t i ^ (e' - e) i) * ∏ i, C.t i ^ e i := by
        rw [← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun i _ => by rw [← zpow_add, Pi.sub_apply, sub_add_cancel]
      have : ((∏ i, C.t i ^ (e' - e) i : (Om C.Z)ˣ) : Om C.Z) * (genVal C.Z g / genVal C.Z f) = u := by
        refine mul_left_cancel₀ ha0 ?_
        rw [← hu', ha1, hb1, hp, Units.val_mul]
        field_simp
      rw [this]
      exact u.2
  have hsv' : ∀ Z' : Comp Xo c, genVal Z' s = genVal Z' g / genVal Z' f := fun Z' => (genVal_apply h Z' s).trans (hsv Z')
  refine ⟨s, hs, sub_eq_zero.1 (secZ_eq_zero_of_genVal (sub_mem (idem_mul_mem Z hs).1 hs) fun Z' => ?_),
    sub_eq_zero.1 (secZ_eq_zero_of_genVal (sub_mem (sub_add_cancel e' e ▸ mul_mem_secZ hs hf) hg) fun Z' => ?_)⟩
  · rw [map_sub, map_mul]
    by_cases hZ : Z' = Z
    · rw [hZ, GlobalTheory.DegCmp.genVal_idem_self, one_mul, sub_self]
    · rw [hsv', off hgZ _ hZ, zero_div, mul_zero, sub_self]
  · rw [map_sub, map_mul, hsv']
    by_cases hZ : Z' = Z
    · rw [hZ, div_mul_cancel₀ _ hfz, sub_self]
    · rw [off hgZ _ hZ, zero_div, zero_mul, sub_self]

end GlobalTheory.SecDivision
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulMemOfMemSpan
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn HasGram IsGram cuspW cuspOn_le latW suppOn
  normW petW petAt petE muOn muPart classesOver ptN rdU_eq_zero mem_latOn modelWt)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

namespace GlobalTheory.HSApp

section Gram

open Matrix Module
open scoped MatrixOrder ComplexOrder

theorem sum_norm_sq_eq {n : ℕ} (u : Fin n → ℂ) : ((∑ i, ‖u i‖ ^ 2 : ℝ) : ℂ) = star u ⬝ᵥ u := by
  simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul']

theorem cnorm_mulVec_eq {n n' m : ℕ} {A : Matrix (Fin n) (Fin m) ℂ} {Y : Matrix (Fin n') (Fin m) ℂ} (h : Aᴴ * A = Yᴴ * Y)
    (u : Fin m → ℂ) : Formalism.HermitianLatticesTheory.cnorm (Y *ᵥ u) = Formalism.HermitianLatticesTheory.cnorm (A *ᵥ u) := by
  have key : ∀ {k : ℕ} (B : Matrix (Fin k) (Fin m) ℂ), star (B *ᵥ u) ⬝ᵥ (B *ᵥ u) = star u ⬝ᵥ ((Bᴴ * B) *ᵥ u) := fun B => by
    have e0 : star u ⬝ᵥ (Bᴴ *ᵥ (B *ᵥ u)) = (star u ᵥ* Bᴴ) ⬝ᵥ (B *ᵥ u) := dotProduct_mulVec _ _ _
    rw [← mulVec_mulVec, e0, star_mulVec]
  have e : ∑ i, ‖(Y *ᵥ u) i‖ ^ 2 = ∑ i, ‖(A *ᵥ u) i‖ ^ 2 := by
    apply Complex.ofReal_injective
    rw [sum_norm_sq_eq, sum_norm_sq_eq, key, key, h]
  simp only [Formalism.HermitianLatticesTheory.cnorm, e]

theorem cnorm_smul {n : ℕ} {t : ℝ} (ht : 0 < t) (u : Fin n → ℂ) :
    Formalism.HermitianLatticesTheory.cnorm ((t : ℂ) • u) = t * Formalism.HermitianLatticesTheory.cnorm u := by
  simp only [Formalism.HermitianLatticesTheory.cnorm, Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht, mul_pow,
    ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht.le]

variable {K V W : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

theorem exists_unit_factor {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosDef) :
    ∃ B : Matrix (Fin n) (Fin n) ℂ, IsUnit B.det ∧ A = Bᴴ * B := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.posSemidef.nonneg
  refine ⟨B, ?_, by simpa [star_eq_conjTranspose] using hB⟩
  have h1 : A.det ≠ 0 := hA.det_pos.ne'
  rw [hB, star_eq_conjTranspose, det_mul] at h1
  exact isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul h1)

theorem hasGram_of_injective {N : (K →+* ℂ) → V → ℝ} (h : HasGram N) (φ : W →ₗ[K] V) (hφ : Function.Injective φ)
    {N' : (K →+* ℂ) → W → ℝ} (t : InfinitePlace K → ℝ) (ht : ∀ v, 0 < t v)
    (hN : ∀ (v : InfinitePlace K) (x : W), N' v.embedding x = t v * N v.embedding (φ x)) : HasGram N' := by
  classical
  obtain ⟨n, ⟨b, X⟩, hX⟩ := h
  dsimp only at hX
  haveI : FiniteDimensional K V := Module.Finite.of_basis b
  haveI : FiniteDimensional K W := FiniteDimensional.of_injective φ hφ
  let b' := Module.finBasis K W
  let B : Matrix (Fin n) (Fin (finrank K W)) K := LinearMap.toMatrix b' b φ
  obtain ⟨g, hg⟩ := φ.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hφ)
  let C : Matrix (Fin (finrank K W)) (Fin n) K := LinearMap.toMatrix b b' g
  have hCB : C * B = 1 := by
    rw [← LinearMap.toMatrix_comp, hg, LinearMap.toMatrix_id]
  have key : ∀ v : InfinitePlace K, ∃ Y : Matrix (Fin (finrank K W)) (Fin (finrank K W)) ℂ, IsUnit Y.det ∧
      ((X v)⁻¹ * B.map v.embedding)ᴴ * ((X v)⁻¹ * B.map v.embedding) = Yᴴ * Y := fun v => by
    have hu := (hX v).1
    have hL : (C.map v.embedding * X v) * ((X v)⁻¹ * B.map v.embedding) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (X v), Matrix.mul_nonsing_inv _ hu, Matrix.one_mul, ← Matrix.map_mul, hCB,
        Matrix.map_one _ (map_zero _) (map_one _)]
    have hinj : Function.Injective ((X v)⁻¹ * B.map v.embedding).mulVec := fun y z hyz => by
      have := congrArg (C.map v.embedding * X v).mulVec hyz
      simpa only [mulVec_mulVec, hL, one_mulVec] using this
    exact exists_unit_factor (PosDef.conjTranspose_mul_self _ hinj)
  choose Y hY hYG using key
  have hu : ∀ v, IsUnit (((t v : ℂ)) • Y v).det := fun v => by
    rw [det_smul]
    exact (IsUnit.pow _ (isUnit_iff_ne_zero.2 (by exact_mod_cast (ht v).ne'))).mul (hY v)
  refine IsGram.hasGram (b := b') (X := fun v => ((t v : ℂ) • Y v)⁻¹) fun v => ⟨?_, fun x => ?_⟩
  · exact Matrix.isUnit_nonsing_inv_det _ (hu v)
  · have e1 : Formalism.HermitianLatticesTheory.vecAt b v (φ x) = B.map v.embedding *ᵥ Formalism.HermitianLatticesTheory.vecAt b' v x := by
      funext i
      have e := congrFun (LinearMap.toMatrix_mulVec_repr b' b φ x) i
      show v.embedding (b.repr (φ x) i) = _
      rw [← e]
      exact RingHom.map_mulVec v.embedding _ _ i
    rw [hN v x, ← (hX v).2 (φ x)]
    simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.fcoord]
    rw [Matrix.nonsing_inv_nonsing_inv _ (hu v), smul_mulVec, cnorm_smul (ht v), e1, mulVec_mulVec,
      cnorm_mulVec_eq (hYG v)]

theorem HasGram_eq_zero {N : (K →+* ℂ) → V → ℝ} (h : HasGram N) (v : InfinitePlace K) {x : V} (hx : N v.embedding x = 0) :
    x = 0 := by
  obtain ⟨n, ⟨b, X⟩, hX⟩ := h
  dsimp only at hX
  have h0 := (hX v).2 x
  rw [hx] at h0
  have h1 : ∑ i, ‖Formalism.HermitianLatticesTheory.fcoord b X v x i‖ ^ 2 = 0 :=
    (Real.sqrt_eq_zero (Finset.sum_nonneg fun _ _ => sq_nonneg _)).1 h0
  have h2 : Formalism.HermitianLatticesTheory.fcoord b X v x = 0 := by
    funext i
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).1 h1 i (Finset.mem_univ i)
    simpa using this
  have h3 : Formalism.HermitianLatticesTheory.vecAt b v x = 0 := by
    have := congrArg (X v).mulVec h2
    simpa only [Formalism.HermitianLatticesTheory.fcoord, mulVec_mulVec, Matrix.mul_nonsing_inv _ (hX v).1, one_mulVec, mulVec_zero] using this
  apply b.repr.map_eq_zero_iff.1
  ext i
  have := congrFun h3 i
  simpa [Formalism.HermitianLatticesTheory.vecAt] using this

theorem exists_smul_mem_of_mem_span [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {L : Submodule (𝓞 K) V} {x : V}
    (hx : x ∈ Submodule.span K (L : Set V)) : ∃ a : 𝓞 K, a ≠ 0 ∧ a • x ∈ L := by
  first
  | exact @_root_.GlobalTheory.NonzeroScalarMultipleMembership.exists_ne_zero_smul_mem
  | exact _root_.GlobalTheory.NonzeroScalarMultipleMembership.exists_ne_zero_smul_mem
  | (apply _root_.GlobalTheory.NonzeroScalarMultipleMembership.exists_ne_zero_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.NonzeroScalarMultipleMembership.exists_ne_zero_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NonzeroScalarMultipleMembership.exists_ne_zero_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NonzeroScalarMultipleMembership.exists_ne_zero_smul_mem ..)

theorem fg_of_injective [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    (φ : W →ₗ[K] V) (hφ : Function.Injective φ) {L : Submodule (𝓞 K) V} {L' : Submodule (𝓞 K) W}
    (hL : ∀ f ∈ L', φ f ∈ L) (hfg : L.FG) : L'.FG := by
  have hN : IsNoetherian (𝓞 K) L := isNoetherian_of_fg_of_noetherian _ hfg
  let ψ : W →ₗ[𝓞 K] V := φ.restrictScalars (𝓞 K)
  have hle : L'.map ψ ≤ L := by
    rintro _ ⟨f, hf, rfl⟩
    exact hL f hf
  exact Submodule.fg_of_fg_map_injective ψ hφ (isNoetherian_submodule.1 hN _ hle)

theorem span_eq_top_of_injective [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    (φ : W →ₗ[K] V) {L : Submodule (𝓞 K) V} {L' : Submodule (𝓞 K) W} (hL : ∀ f, φ f ∈ L → f ∈ L')
    (hsp : Submodule.span K (L : Set V) = ⊤) : Submodule.span K (L' : Set W) = ⊤ := by
  rw [eq_top_iff]
  intro f _
  have hf : φ f ∈ Submodule.span K (L : Set V) := hsp ▸ Submodule.mem_top
  obtain ⟨a, ha, hm⟩ := exists_smul_mem_of_mem_span hf
  have h1 : a • f ∈ L' := hL _ (by rwa [LinearMap.map_smul_of_tower])
  have hA : algebraMap (𝓞 K) K a ≠ 0 := fun h => ha (IsFractionRing.injective (𝓞 K) K (h.trans (map_zero _).symm))
  have e : f = (algebraMap (𝓞 K) K a)⁻¹ • (a • f) := by
    rw [← algebraMap_smul K a f, smul_smul, inv_mul_cancel₀ hA, one_smul]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span h1)

end Gram

section Norms

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {D : D7}

section One

variable {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (x : ℝ) (V : TH.HSp D)
  (dict : Formalism.L2.Theta.GA D V → Σ k, FD.Frame (U.X k).Ψ r) (Z : Comp Xo c) (G : WTZ E)

theorem support_ptN_subset {f : Rul Xo c} (hf : f ∈ suppOn Z) :
    Function.support (fun q : AutQ V => ptN (modelWt U G) (rdU U f) (dict q.out)) ⊆
      classesOver V dict (framesOn U Z) := fun q hq => by
  by_contra h
  apply hq
  have h0 := rdU_eq_zero U hf (z := dict q.out) h
  show ‖rdU U f (dict q.out).1 (dict q.out).2‖ * _ = 0
  rw [h0, norm_zero, zero_mul]

theorem petAt_muOn {f : Rul Xo c} (hf : f ∈ suppOn Z) :
    petAt U x V dict (muOn U V dict Z) G f =
      (((muQ1 V (classesOver V dict (framesOn U Z)))⁻¹ ^ (1 / (2 : ENNReal)).toReal).toReal) *
        petAt U x V dict (muQ1 V) G f := by
  unfold petAt petE muOn muPart
  rw [ProbabilityTheory.cond, MeasureTheory.eLpNorm_smul_measure_of_ne_top (by simp),
    MeasureTheory.eLpNorm_restrict_eq_of_support_subset (support_ptN_subset U V dict Z G hf), smul_eq_mul, ENNReal.toReal_mul]
  ring

theorem petAt_eq_zero {f : Rul Xo c} (hf : f ∈ suppOn Z) (h0 : muQ1 V (classesOver V dict (framesOn U Z)) = 0) :
    petAt U x V dict (muQ1 V) G f = 0 := by
  unfold petAt petE
  rw [← MeasureTheory.eLpNorm_restrict_eq_of_support_subset (support_ptN_subset U V dict Z G hf),
    MeasureTheory.Measure.restrict_eq_zero.2 h0, MeasureTheory.eLpNorm_measure_zero]
  simp

end One

variable (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (V : (c.F →+* ℂ) → TH.HSp D)
  (dict : ∀ σ, Formalism.L2.Theta.GA D (V σ) → Σ k, FD.Frame ((U σ).X k).Ψ r) (Z : Comp Xo c) (G : WTZ E)

theorem goodOn_of_goodW (h : GoodW U x V dict G) : GoodOn U x V dict Z G := by
  obtain ⟨hg, hfg, hsp⟩ := h
  let φ : cuspOn U Z G →ₗ[c.F] cuspW Xo c U G := Submodule.inclusion (cuspOn_le U Z G)
  have hφ : Function.Injective φ := Submodule.inclusion_injective _
  refine ⟨?_, ?_, ?_⟩
  · by_cases h0 : ∃ v : InfinitePlace c.F, muQ1 (V (goodOf c v.embedding))
        (classesOver (V (goodOf c v.embedding)) (dict (goodOf c v.embedding)) (framesOn (U (goodOf c v.embedding)) Z)) = 0
    · obtain ⟨v, hv⟩ := h0
      have hz : ∀ f : cuspOn U Z G, f = 0 := fun f => hφ (by
        rw [map_zero]
        exact HasGram_eq_zero hg v (petAt_eq_zero _ x _ _ Z G f.2.2 hv))
      refine hasGram_of_injective hg φ hφ (fun _ => 1) (fun _ => one_pos) fun w f => ?_
      obtain rfl := hz f
      rw [map_zero, one_mul]
      have a1 := GlobalTheory.AllWt.petOn_smul U x V dict Z G w.embedding 0 0
      have a2 := GlobalTheory.AllWt.petW_smul U x V dict G w.embedding 0 0
      simp only [zero_smul, map_zero, norm_zero, zero_mul] at a1 a2
      exact a1.trans a2.symm
    · push_neg at h0
      refine hasGram_of_injective hg φ hφ (fun v => (((muQ1 (V (goodOf c v.embedding))
        (classesOver (V (goodOf c v.embedding)) (dict (goodOf c v.embedding)) (framesOn (U (goodOf c v.embedding)) Z)))⁻¹ ^
          (1 / (2 : ENNReal)).toReal).toReal)) (fun v => ?_) fun v f => ?_
      · rw [← ENNReal.toReal_rpow]
        refine Real.rpow_pos_of_pos (ENNReal.toReal_pos (ENNReal.inv_ne_zero.2 (MeasureTheory.measure_ne_top _ _))
          (ENNReal.inv_ne_top.2 (h0 v))) _
      · exact petAt_muOn _ x _ _ Z G f.2.2
  · exact fg_of_injective φ hφ (fun _ h => h) hfg
  · exact span_eq_top_of_injective φ (fun _ h => h) hsp

end Norms

theorem goodOn_of_goodAt : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o →
    2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (G : WTZ D.host.E), Y.GoodAt G →
      GoodOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z G :=
  fun _ _ _ Y _ _ _ _ Z G hG => goodOn_of_goodW Y.U _ _ Y.dict Z G hG

end GlobalTheory.HSApp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdentityTransportsComponentToItselfStatement
section
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.identity_transports_component_to_itself : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (ψ : ∀ k : (uAt r v i).Comp, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] latQ p r i v k) (k : (uAt r v i).Comp), IsTransp p r i v ψ 1 k k 1 := by
  first | exact @GlobalTheory.ShareOn.isTransp_one | exact GlobalTheory.ShareOn.isTransp_one | (intros; apply GlobalTheory.ShareOn.isTransp_one <;> assumption)
end

