import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0022
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0041
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0083
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0059
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0074
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0081
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0001
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0078
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0027
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0068

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PCurvePointsFinite
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

namespace CurvePointsFinite

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem aeval_eq_eval₂ {F : Type*} [CommRing F] {inst : Algebra ℤ F} (y : (Σ k, ι k) → F) (f : MRing ι) :
    @aeval ℤ F _ _ _ inst y f = eval₂ (Int.castRingHom F) y f := by
  rw [aeval_def]
  congr 1
  exact RingHom.ext_int _ _

def genericPt (W : Ideal (MRing ι)) [W.IsPrime] : (Σ k, ι k) → FractionRing (MRing ι ⧸ W) :=
  fun p ↦ algebraMap (MRing ι ⧸ W) _ (Ideal.Quotient.mk W (X p))

theorem aeval_genericPt (W : Ideal (MRing ι)) [W.IsPrime] (f : MRing ι) :
    aeval (genericPt W) f = algebraMap (MRing ι ⧸ W) _ (Ideal.Quotient.mk W f) := by
  have h : (aeval (genericPt W) : MRing ι →ₐ[ℤ] _).toRingHom =
      (algebraMap (MRing ι ⧸ W) (FractionRing (MRing ι ⧸ W))).comp (Ideal.Quotient.mk W) :=
    ringHom_ext (fun n ↦ by simp) (fun p ↦ by simp [genericPt])
  exact RingHom.congr_fun h f

theorem aeval_genericPt_eq_zero_iff (W : Ideal (MRing ι)) [W.IsPrime] (f : MRing ι) :
    aeval (genericPt W) f = 0 ↔ f ∈ W := by
  rw [aeval_genericPt, ← Ideal.Quotient.eq_zero_iff_mem]
  exact (IsFractionRing.injective (MRing ι ⧸ W) (FractionRing (MRing ι ⧸ W))).eq_iff' (map_zero _)

theorem mCoordIdeal_genericPt (W : Ideal (MRing ι)) [W.IsPrime] (hW : IsMultiHomogIdeal W) :
    mCoordIdeal (genericPt W) = W := by
  apply le_antisymm
  · intro f hf
    rw [ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.eq_sum_multihomogeneous_components f]
    refine Ideal.sum_mem _ fun b _ ↦ ?_
    have h1 := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.i2comp_mem (CoordinateConeArithVar.isMultiHomogIdeal _) b hf
    rw [mCoordIdeal, RingHom.mem_ker,
      ProjLine.mConeMap_eq_of_isMultiHomog _ (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_i2comp b f)] at h1
    rcases mul_eq_zero.1 h1 with h | h
    · exact (aeval_genericPt_eq_zero_iff W _).1 (by
        have h' := MvPolynomial.C_eq_zero.1 h
        rw [aeval_eq_eval₂] at h' ⊢
        exact h')
    · exact absurd h (Finset.prod_ne_zero_iff.2 fun k _ ↦ pow_ne_zero _ (MvPolynomial.X_ne_zero k))
  · obtain ⟨S, hS, hWS⟩ := hW
    calc W = Ideal.span S := hWS
      _ ≤ mCoordIdeal (genericPt W) := Ideal.span_le.2 fun f hf ↦ by
        obtain ⟨a, ha⟩ := hS f hf
        have hfW : f ∈ W := hWS ▸ Ideal.subset_span hf
        show f ∈ RingHom.ker (mConeMap (genericPt W))
        have h0 := (aeval_genericPt_eq_zero_iff W f).2 hfW
        rw [RingHom.mem_ker, ProjLine.mConeMap_eq_of_isMultiHomog _ ha]
        exact mul_eq_zero_of_left (MvPolynomial.C_eq_zero.2 (by
          rw [aeval_eq_eval₂] at h0 ⊢
          exact h0)) _

theorem charZero_fractionRing (W : Ideal (MRing ι)) [W.IsPrime] (hH : IsHorizontal W) :
    CharZero (FractionRing (MRing ι ⧸ W)) := by
  have hinj : Function.Injective (algebraMap ℤ (FractionRing (MRing ι ⧸ W))) := by
    have e : algebraMap ℤ (FractionRing (MRing ι ⧸ W)) =
        (algebraMap (MRing ι ⧸ W) (FractionRing (MRing ι ⧸ W))).comp (algebraMap ℤ (MRing ι ⧸ W)) :=
      RingHom.ext_int _ _
    rw [e]
    exact (IsFractionRing.injective (MRing ι ⧸ W) (FractionRing (MRing ι ⧸ W))).comp (CoordinateConeArithVar.algebraMap_injective W hH)
  exact charZero_of_injective_algebraMap hinj

end CurvePointsFinite

open CurvePointsFinite in

theorem CurvePointsFinite.proof : CurvePointsFinite.Statement := by
  intro K _ ι _ W hW
  have : W.IsPrime := hW.2.1.1
  have := charZero_fractionRing W hW.2.2.1
  have hEq := mCoordIdeal_genericPt W hW.2.1.2.1
  have hP : IsArithVar (mCoordIdeal (genericPt W)) 1 := by rw [hEq]; exact hW
  have hdeg := IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.degC_eq hP
  rw [hEq, GroundTheory.Heights₂.Heights.degC_eq_card_projPts] at hdeg
  have := IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.isAlgebraic_blockFnField hP
  set L := ReciprocityTheory.ChartRestriction.G.AI.I4.blockFnField (genericPt W)
  set S : Set (FractionRing (MRing ι ⧸ W)) :=
    {t | ∃ p q : Σ k, ι k, p.1 = q.1 ∧ t = genericPt W p / genericPt W q}
  have hSfin : S.Finite := (Set.finite_range fun pq : (Σ k, ι k) × (Σ k, ι k) ↦
      genericPt W pq.1 / genericPt W pq.2).subset fun t ⟨p, q, _, ht⟩ ↦ ⟨(p, q), ht.symm⟩
  have : Finite S := hSfin.to_subtype
  have hint : ∀ t ∈ S, IsIntegral ℚ t := fun t ht ↦
    ((Algebra.IsAlgebraic.isAlgebraic (⟨t, IntermediateField.subset_adjoin ℚ S ht⟩ : L)).isIntegral).map
      L.val
  have : FiniteDimensional ℚ L := IntermediateField.finiteDimensional_adjoin hint
  have hpos : 0 < Nat.card (L →ₐ[ℚ] ℂ) := Nat.card_pos_iff.2 ⟨⟨IsAlgClosed.lift⟩, inferInstance⟩
  exact (Nat.card_pos_iff.1 (hdeg ▸ hpos)).2

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreNormPullback
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

namespace FibreNormPullback

theorem charZero_of_isArithVar {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    {y : (Σ k, ι k) → Ω} {d : ℕ} (hV : IsArithVar (mCoordIdeal y) d) : CharZero Ω := by
  refine charZero_of_inj_zero fun m hm => ?_
  have hmem : (m : ℤ) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := by
    show mConeMap y (C (m : ℤ)) = 0
    simp only [mConeMap, eq_intCast, Int.cast_natCast]
    rw [map_natCast, ← map_natCast (MvPolynomial.C : Ω →+* MvPolynomial K Ω), hm, map_zero]
  rw [hV.2.2.1, Ideal.mem_bot] at hmem
  exact_mod_cast hmem

theorem isHomogeneous_of_map {σ : Type} {F : MvPolynomial σ ℤ} {m : ℕ}
    (h : (map (Int.castRingHom ℚ) F).IsHomogeneous m) : F.IsHomogeneous m := fun {d} hd =>
  h (by rw [coeff_map, eq_intCast, ne_eq, Int.cast_eq_zero]; exact hd)

theorem norm_prod_le_pow {B : ℝ} (hB : 0 ≤ B) (m : Multiset ℂ) (h : ∀ x ∈ m, ‖x‖ ≤ B) :
    ‖m.prod‖ ≤ B ^ Multiset.card m := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    rw [Multiset.prod_cons, norm_mul, Multiset.card_cons, pow_succ']
    exact mul_le_mul (h a (Multiset.mem_cons_self a m)) (ih fun x hx => h x (Multiset.mem_cons_of_mem hx))
      (norm_nonneg _) hB

theorem norm_last_le {n : ℕ} (a : ℕ → ℂ) (ha : a 0 = 1) {B : ℝ} (hB : 0 ≤ B)
    (hroot : ∀ w : ℂ, ∑ i ∈ Finset.range (n + 1), a i * w ^ (n - i) = 0 → ‖w‖ ≤ B) :
    ‖a n‖ ≤ B ^ n := by
  classical
  set p : Polynomial ℂ := ∑ i ∈ Finset.range (n + 1), Polynomial.C (a i) * Polynomial.X ^ (n - i) with hp
  have hcoeff : ∀ k, p.coeff k = ∑ i ∈ Finset.range (n + 1), if k = n - i then a i else 0 := by
    intro k
    rw [hp, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul_X_pow]
  have hdeg : p.natDegree ≤ n :=
    Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ =>
      (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.sub_le n i)
  have hlead : p.coeff n = 1 := by
    rw [hcoeff, Finset.sum_eq_single 0]
    · simp [ha]
    · intro i hi hi0
      rw [Finset.mem_range] at hi
      rw [if_neg]
      omega
    · intro h; exact absurd (Finset.mem_range.mpr (Nat.succ_pos n)) h
  have hmon : p.Monic := Polynomial.monic_of_degree_le n (Polynomial.degree_le_of_natDegree_le hdeg) hlead
  have hnat : p.natDegree = n :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hdeg (by rw [hlead]; exact one_ne_zero)
  have hzero : p.coeff 0 = a n := by
    rw [hcoeff, Finset.sum_eq_single n]
    · simp
    · intro i hi hin
      rw [Finset.mem_range] at hi
      rw [if_neg]
      omega
    · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self n)) h
  have hsplit : p.Splits := IsAlgClosed.splits p
  have hcard : Multiset.card p.roots = n := by rw [Polynomial.splits_iff_card_roots.mp hsplit, hnat]
  have hprod := hsplit.coeff_zero_eq_prod_roots_of_monic hmon
  rw [hzero, hnat] at hprod
  rw [hprod, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, ← hcard]
  refine norm_prod_le_pow hB _ fun w hw => hroot w ?_
  have hw' := (Polynomial.mem_roots hmon.ne_zero).mp hw
  rw [Polynomial.IsRoot.def, hp, Polynomial.eval_finsetSum] at hw'
  simpa using hw'

theorem proof (hA : FibreNormCharpoly.Statement) (hI : FibreNormIntegral.Statement)
    (hR : FibreNormRoots.Statement) : FibreNormPullback.Statement := by
  intro K _ ι _ Ω _ y D e L q hV hBir he hL hL0
  classical
  have : CharZero Ω := charZero_of_isArithVar hV
  obtain ⟨hfin, hA'⟩ := hA K ι Ω y D e L q hV hBir he hL hL0
  obtain ⟨M₀, hM₀, hI'⟩ := hI K ι Ω y D e L q hV hBir he hL hL0
  have hR' := hR K ι Ω y D e L q hV hBir he hL hL0
  have hP : IsMultiHomogIdeal (mCoordIdeal y) := hV.2.1.2.1
  set n := Module.finrank (pullField y L) Ω
  have hn1 : 1 ≤ n := Module.finrank_pos
  refine ⟨n, M₀, hn1, by exact_mod_cast hM₀, fun τ s hs hs0 => ?_⟩
  obtain ⟨c, hc, hcn⟩ := hA' τ s hs
  obtain ⟨F, hF⟩ := hI' τ s hs c hc
  have hRc := hR' τ s hs c hc
  obtain ⟨_, hc0, hch, -⟩ := hc
  have hM₀q : ((M₀ : ℚ) ^ τ) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (show M₀ ≠ 0 by omega))
  refine ⟨F, ?_, ?_, fun ζ hζ S hS M hM hrep => ?_⟩
  · rintro rfl
    rw [map_zero, eq_comm, smul_eq_zero] at hF
    exact hF.elim hM₀q (hcn hs0)
  · apply isHomogeneous_of_map
    rw [hF, smul_eq_C_mul, show n * q * τ = 0 + n * (q * τ) by ring]
    exact (isHomogeneous_C _ _).mul (hch n le_rfl)

  have hmapF : eval ζ (map (Int.castRingHom ℂ) F) = (M₀ : ℂ) ^ τ * eval ζ (map (algebraMap ℚ ℂ) (c n)) := by
    have h1 : map (Int.castRingHom ℂ) F = map (algebraMap ℚ ℂ) (map (Int.castRingHom ℚ) F) := by
      rw [map_map]
      congr 1
    rw [h1, hF, smul_eq_C_mul, map_mul, map_C, eval_mul, eval_C]
    simp
  set B := M * ‖ζ‖ ^ (q * τ) with hBdef
  have hB0 : 0 ≤ B := mul_nonneg hM (pow_nonneg (norm_nonneg _) _)
  have hroot : ∀ w : ℂ, ∑ i ∈ Finset.range (n + 1), eval ζ (map (algebraMap ℚ ℂ) (c i)) * w ^ (n - i) = 0 →
      ‖w‖ ≤ B := by
    intro w hw
    obtain ⟨z, hz, t, ht0, hLz, hval⟩ := hRc ζ hζ w hw
    obtain ⟨z', hz'S, r, hr0, rfl⟩ := hS z hz ⟨t, hLz⟩
    have hz'm : z' ∈ mcPts (mCoordIdeal y) := by
      have h1 := mcPts_smul hP (fun k => (r k)⁻¹) (fun k => inv_ne_zero (hr0 k)) hz
      convert h1 using 1
      funext p
      simp [hr0 p.1]
    obtain ⟨dg, dh, g, h, hg, hh, hd, hgh, hz'0, hle⟩ := hrep z' hz'S hz'm
    have hgz := eval_smul_homog g dg hg r z'
    have hhz := eval_smul_homog h dh hh r z'
    have hhz0 : eval (fun p => r p.1 * z' p) (map (Int.castRingHom ℂ) h) ≠ 0 := by
      rw [hhz]
      exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hr0 k)) hz'0
    have hv := hval dg dh g h hg hh hd hgh hhz0
    have hRg : (∏ k, r k ^ dg k) = (∏ k, r k ^ dh k) * (∏ k, r k ^ e k) ^ (q * τ) := by
      rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [hd k, ← pow_mul, ← pow_add]
      ring
    have hnormL : ‖∏ k, r k ^ e k‖ * ‖fun j => eval z' (map (Int.castRingHom ℂ) (L j))‖ = ‖t‖ * ‖ζ‖ := by
      have h1 : (∏ k, r k ^ e k) • (fun j => eval z' (map (Int.castRingHom ℂ) (L j))) = t • ζ := by
        funext j
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [← eval_smul_homog (L j) e (hL j) r z', hLz j]
      rw [← norm_smul, h1, norm_smul]
    have hpos : 0 < ‖t‖ ^ (q * τ) * ‖eval (fun p => r p.1 * z' p) (map (Int.castRingHom ℂ) h)‖ :=
      mul_pos (pow_pos (norm_pos_iff.mpr ht0) _) (norm_pos_iff.mpr hhz0)
    refine le_of_mul_le_mul_right ?_ hpos
    calc ‖w‖ * (‖t‖ ^ (q * τ) * ‖eval (fun p => r p.1 * z' p) (map (Int.castRingHom ℂ) h)‖)
        = ‖eval (fun p => r p.1 * z' p) (map (Int.castRingHom ℂ) g)‖ := by
          rw [hv, norm_mul, norm_mul, norm_pow]; ring
      _ = ‖∏ k, r k ^ dg k‖ * ‖eval z' (map (Int.castRingHom ℂ) g)‖ := by rw [hgz, norm_mul]
      _ ≤ ‖∏ k, r k ^ dg k‖ * (M * ‖fun j => eval z' (map (Int.castRingHom ℂ) (L j))‖ ^ (q * τ) *
            ‖eval z' (map (Int.castRingHom ℂ) h)‖) := mul_le_mul_of_nonneg_left hle (norm_nonneg _)
      _ = M * (‖∏ k, r k ^ e k‖ * ‖fun j => eval z' (map (Int.castRingHom ℂ) (L j))‖) ^ (q * τ) *
            (‖∏ k, r k ^ dh k‖ * ‖eval z' (map (Int.castRingHom ℂ) h)‖) := by
          rw [hRg, norm_mul, norm_pow]; ring
      _ = B * (‖t‖ ^ (q * τ) * ‖eval (fun p => r p.1 * z' p) (map (Int.castRingHom ℂ) h)‖) := by
          rw [hnormL, hhz, norm_mul, hBdef]; ring
  have key := norm_last_le (fun i => eval ζ (map (algebraMap ℚ ℂ) (c i))) (by simp [hc0]) hB0 hroot
  rw [hmapF, norm_mul, norm_pow, Complex.norm_natCast]
  calc (M₀ : ℝ) ^ τ * ‖eval ζ (map (algebraMap ℚ ℂ) (c n))‖ ≤ (M₀ : ℝ) ^ τ * B ^ n :=
        mul_le_mul_of_nonneg_left key (pow_nonneg (Nat.cast_nonneg _) _)
    _ = (M₀ : ℝ) ^ τ * ‖ζ‖ ^ (n * q * τ) * M ^ n := by
        rw [hBdef, mul_pow, ← pow_mul, show q * τ * n = n * q * τ by ring]
        ring

end FibreNormPullback

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenKoszulStep
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KoszulCech

noncomputable section

namespace GenKoszulStep

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)]
  [∀ k, LinearOrder (ι k)]

theorem subsingleton_cechHc_iff {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
    [IsScalarTower S (MRingOver S ι) M] (𝓜 : (K → ℤ) → Submodule S M) (c : K → ℤ) (n : ℕ) :
    Subsingleton (KH.cechHc ι 𝓜 c (n + 1)) ↔
      ∀ x ∈ KH.cechCc ι 𝓜 c (n + 1), KH.cechD S ι M (n + 1) x = 0 →
        ∃ y ∈ KH.cechCc ι 𝓜 c n, KH.cechD S ι M n y = x := by
  rw [KH.cechHc, Submodule.Quotient.subsingleton_iff, eq_top_iff]
  constructor
  · intro h x hx hdx
    have hZ : x ∈ KH.cechZc ι 𝓜 c (n + 1) := ⟨hx, hdx⟩
    obtain ⟨y, hy, hyx⟩ := h (Submodule.mem_top (x := ⟨x, hZ⟩))
    exact ⟨y, hy, hyx⟩
  · rintro h ⟨x, hx, hdx⟩ -
    obtain ⟨y, hy, hyx⟩ := h x hx hdx
    exact ⟨y, hy, hyx⟩

theorem gather {V : Ideal (MRingOver S ι)} {α : K → ℤ} (h : KH.GeneratedV S V α) :
    ∃ (R : ℕ) (z : Fin R → KH.CechC S ι (MRingOver S ι ⧸ V) 0),
      (∀ j, z j ∈ KH.cechZc ι (KH.quotPart S V) α 0) ∧
      ∀ I : KH.Cell K ι 0, ∃ u : Fin R → LocalizedModule (KH.cellMon S I.1) (MRingOver S ι ⧸ V),
        (∀ j, u j ∈ KH.locPart ι (KH.quotPart S V) (KH.cellMon S I.1) (-α)) ∧ ∑ j, u j * z j I = 1 := by
  classical
  choose r zz uu hz hu hs using h
  have : Finite (KH.Cell K ι 0) := by unfold KH.Cell; infer_instance
  let _ : Fintype (KH.Cell K ι 0) := Fintype.ofFinite _
  set e := Fintype.equivFin (Σ I : KH.Cell K ι 0, Fin (r I))
  let v : ∀ I : KH.Cell K ι 0, (Σ I' : KH.Cell K ι 0, Fin (r I')) →
      LocalizedModule (KH.cellMon S I.1) (MRingOver S ι ⧸ V) :=
    fun I σ => if h : σ.1 = I then h ▸ uu σ.1 σ.2 else 0
  refine ⟨Fintype.card (Σ I : KH.Cell K ι 0, Fin (r I)), fun j => zz (e.symm j).1 (e.symm j).2,
    fun j => hz _ _, fun I => ⟨fun j => v I (e.symm j), fun j => ?_, ?_⟩⟩
  · have hv : ∀ σ, v I σ ∈ KH.locPart ι (KH.quotPart S V) (KH.cellMon S I.1) (-α) := by
      rintro ⟨I', i⟩
      simp only [v]
      split_ifs with hI
      · subst hI
        exact hu _ i
      · exact Submodule.zero_mem _
    exact hv (e.symm j)
  · rw [Equiv.sum_comp e.symm (fun σ => v I σ * zz σ.1 σ.2 I), Fintype.sum_sigma,
      Finset.sum_eq_single I]
    · simp only [v, dif_pos rfl]
      exact hs I
    · intro I' _ hI'
      refine Finset.sum_eq_zero fun i _ => ?_
      simp only [v, dif_neg hI']
      exact zero_mul (zz I' i I)
    · simp

end GenKoszulStep

open GenKoszulStep

theorem GenKoszulStep.proof (hB : KoszulCechComplex.Statement) (hC : KoszulCechExact.Statement)
    (hD : DoubleComplexVanish.Statement) (hSq : KH.CechDSqStatement) (hDeg : KH.CechDDegStatement) :
    GenKoszulStep.Statement := by
  intro S _ K _ _ ι _ _ V α _ hα
  obtain ⟨R, z, hz, hu⟩ := gather hα
  refine ⟨R, fun c hc => ?_⟩
  have hB' := hB S K ι V α R z hz c
  have hC' := hC S K ι V α R z hu c
  have key := hD (fun p n => KosC S ι V R p n) (fun p n => kosPart S ι V R α c p n)
    (fun p n => kosCech S ι V R p n) (fun p n => kosD z p n) R
    (fun p n x hx J _ => hDeg S K ι _ _ _ n (x J) (hx J trivial))
    (fun p n x hx => (hB' p n).1 x hx)
    (fun p n x _ => funext fun J => LinearMap.congr_fun (hSq S K ι (MRingOver S ι ⧸ V) n) (x J))
    (fun p n x _ => (hB' p n).2.1 x)
    (fun p n x _ => (hB' p n).2.2 x)
    (fun n x hx => (hC' n).1 x hx)
    (fun p n x hx h0 => (hC' n).2 p x hx h0)
    (fun p n hp x _ => funext fun J => absurd ((J.2.symm.trans_le (J.1.card_le_univ)).trans_eq
      (Fintype.card_fin R)) (by omega))
    (fun p hp1 hpR n x hx h0 => by
      have hJ := fun J => (subsingleton_cechHc_iff _ _ n).mp (hc p hp1 hpR (n + 1) (by omega))
        (x J) (hx J trivial) (congrFun h0 J)
      choose y hy hdy using hJ
      exact ⟨y, fun J _ => hy J, funext hdy⟩)
  intro i hi
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  rw [subsingleton_cechHc_iff]
  intro x hx hdx
  obtain ⟨y, hy, hdy⟩ := key n (fun _ => x) (fun J _ => by simpa using hx) (funext fun _ => hdx)
  exact ⟨y ⟨∅, Finset.card_empty⟩, by simpa using hy _ trivial, congrFun hdy _⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGeneratedNefGeneric
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1

noncomputable section

theorem GeneratedNefGeneric.eq_natCast_of_add_one_eq (d : ℕ) (x : WithBot ℕ∞)
    (hform : x + 1 = ((d : ℕ) : WithBot ℕ∞) + 1) : x = d := by
  induction x using WithBot.recBotCoe with
  | bot => exact absurd hform (by simp; rw [← Nat.cast_succ]; exact (WithBot.natCast_ne_bot _).symm)
  | coe y =>
    induction y using ENat.recTopCoe with
    | top =>
      exfalso
      have h1 : (((⊤ : ℕ∞) + 1 : ℕ∞) : WithBot ℕ∞) = (((d + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
        rw [WithBot.coe_add]; exact_mod_cast hform
      have h2 : ((⊤ : ℕ∞) + 1 : ℕ∞) = ((d + 1 : ℕ) : ℕ∞) := WithBot.coe_injective h1
      rw [top_add] at h2
      exact ENat.top_ne_natCast _ h2
    | coe y =>
      have h1 : ((y + 1 : ℕ) : WithBot ℕ∞) = ((d + 1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast hform
      have : y = d := by exact_mod_cast (by exact_mod_cast h1 : y + 1 = d + 1) |> Nat.succ_injective
      subst this; rfl

theorem GeneratedNefGeneric.isProjVarF_map {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {W : Ideal (MRing ι)} {d : ℕ} (hW : IsArithVar W (d + 1)) :
    IsProjVarF (W.map (MvPolynomial.map (Int.castRingHom ℚ))) d := by
  obtain ⟨-, ⟨hWp, ⟨S, hS, hWS⟩, hrel⟩, hhor, hdim⟩ := hW
  have : W.IsPrime := hWp
  have hchar : ∀ m : ℤ, (C m : MvPolynomial (Σ k, ι k) ℤ) ∈ W → m = 0 := by
    intro m hm
    have h1 : m ∈ W.comap (C : ℤ →+* MRing ι) := hm
    rw [show W.comap (C : ℤ →+* MRing ι) = ⊥ from hhor, Ideal.mem_bot] at h1
    exact h1
  obtain ⟨hqp, hcomap, hform⟩ := ReciprocityTheory.AnForm.R.extQ_spec W hchar
  have hq : ReciprocityTheory.AnForm.R.extQ W = W.map (MvPolynomial.map (Int.castRingHom ℚ)) := rfl
  rw [← hq]
  refine ⟨⟨hqp, ?_, ?_⟩, ?_⟩
  · refine ⟨MvPolynomial.map (Int.castRingHom ℚ) '' S, ?_, ?_⟩
    · rintro _ ⟨f, hf, rfl⟩
      obtain ⟨b, hb⟩ := hS f hf
      exact ⟨b, fun m hm k => hb m (MvPolynomial.support_map_subset _ _ hm) k⟩
    · show W.map (MvPolynomial.map (Int.castRingHom ℚ)) = _
      rw [hWS, Ideal.map_span]
  · intro k
    obtain ⟨i, hi⟩ := hrel k
    refine ⟨i, fun hX => hi ?_⟩
    rw [← hcomap, Ideal.mem_comap, map_X]
    exact hX
  · refine GeneratedNefGeneric.eq_natCast_of_add_one_eq (d + Fintype.card K) _ ?_
    rw [hform, hdim, show d + 1 + Fintype.card K = (d + Fintype.card K) + 1 by omega]
    push_cast
    rfl

theorem GeneratedNefGeneric.proof (hG : GenOnFibres.Statement) (hR : GeneratedRestrict.Statement)
    (hN : GeneratedProductNonneg.Statement) : GeneratedNefGeneric.Statement := by
  intro K _ ι _ Ω _ _ y D a q w _ hw hgen W hW hPW
  classical
  let _ : LinearOrder K := LinearOrder.lift' (Fintype.equivFin K) (Fintype.equivFin K).injective
  let _ : ∀ k, LinearOrder (ι k) := fun k =>
    LinearOrder.lift' (Fintype.equivFin (ι k)) (Fintype.equivFin (ι k)).injective
  have hQ : KH.GeneratedV ℚ (KH.genIdeal y) a := (hG K ι Ω y a q w hw hgen).1
  have hWQ : KH.GeneratedV ℚ (W.map (MvPolynomial.map (Int.castRingHom ℚ))) a :=
    hR ℚ K ι _ _ a (Ideal.map_mono hPW) hQ
  have hV : IsProjVarF (W.map (MvPolynomial.map (Int.castRingHom ℚ))) 1 :=
    GeneratedNefGeneric.isProjVarF_map (d := 1) hW
  have h := hN ℚ K ι (fun V _ L => NumbersDVR.intNum ℚ V L) _ 1 (fun _ => a)
    (NumbersDVR.IntNumIsFieldIntersection.full ℚ K ι) hV (fun _ => hWQ)
  unfold genDeg
  convert h

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSecCochReduce
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

theorem SecCochReduce.map_map_int {K : Type} {ι : K → Type} (p : ℕ) (f : MRing ι) :
    MvPolynomial.map (Int.castRingHom (ZMod p)) (MvPolynomial.map (Int.castRingHom ℤ) f) =
      MvPolynomial.map (Int.castRingHom (ZMod p)) f := by
  rw [MvPolynomial.map_map]
  congr 1

theorem SecCochReduce.proof : SecCochReduce.Statement := by
  intro K _ _ ι _ _ Ω _ y p a s hs
  funext J
  rw [FibreReduction.redCoch_apply]
  by_cases hz : ∃ k, y ⟨k, GenOnFibres.cellChart J k⟩ = 0
  · obtain ⟨k, h0⟩ := hz
    have := GenOnFibres.subsingleton_loc (S := ZMod p) (GenOnFibres.cellChart_mem J k) h0
    exact Subsingleton.elim _ _
  · push Not at hz
    obtain ⟨e, F, hF, _, heq⟩ := GenOnFibres.secCoch_spec (S := ℤ) hs J hz
    have hrep : GenOnFibres.IsRep y (ZMod p) (KH.cellMon (ZMod p) J.1)
        (FibreReduction.redLoc y p J.1 (GenOnFibres.secCoch y ℤ s a J)) (GenOnFibres.cellChart J) s a := by
      refine ⟨e, F, hF, GenOnFibres.cmon_mem (ZMod p) (GenOnFibres.cellChart_mem J) e, ?_⟩
      rw [heq, FibreReduction.redLoc_mk, FibreReduction.redRing_mk, SecCochReduce.map_map_int]
      congr 1
      exact Subtype.ext (SecCochReduce.map_map_int p _)
    exact hrep.unique (GenOnFibres.secCoch_spec hs J hz)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

