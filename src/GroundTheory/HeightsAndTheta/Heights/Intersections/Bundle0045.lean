import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.Intersections.AnalyticResolutionHypothesesProjectiveLine
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0014
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0042
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0037
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0039
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0040
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsSemilocRing

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.IsSmoothMetricOfIsSmoothHerm
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing)

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in

theorem map_rat_complex (f : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι) :
    MvPolynomial.map (algebraMap ℚ ℂ) (MvPolynomial.map (Int.castRingHom ℚ) f) =
      MvPolynomial.map (Int.castRingHom ℂ) f := by
  rw [MvPolynomial.map_map]
  congr 1

omit [DecidableEq K] [∀ k, Fintype (ι k)] in

theorem isOpen_blockNonzero : IsOpen {w : MCone ι | ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0} := by
  have h : {w : MCone ι | ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {w : MCone ι | w ⟨k, i⟩ ≠ 0} := by
    ext w
    simp
  rw [h]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

omit [DecidableEq K] in

theorem isSmoothMetric_of_isSmoothHerm (P : Ideal (MRing ι ℂ)) (L : HLine ι)
    (h : ReciprocityTheory.ChartRestriction.G.Geo.IsSmoothHerm L) : IsSmoothMetric P L := by
  intro z hz
  refine ⟨_, isOpen_blockNonzero.mem_nhds hz.1, logH L, ?_, fun w _ => rfl⟩
  exact h.log fun w hw => (L.pos w hw).ne'

theorem isProjVarQ_of_isArithVar {P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)} {e : ℕ}
    (hP : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar P (e + 1)) :
    IsProjVarQ (P.map (MvPolynomial.map (Int.castRingHom ℚ))) e := by
  obtain ⟨-, ⟨hprime, ⟨S, hS, hPS⟩, hrel⟩, hhor, hdim⟩ := hP
  have := hprime
  have hch : ∀ m : ℤ, (C m : MvPolynomial (Σ k, ι k) ℤ) ∈ P → m = 0 := by
    intro m hm
    have hm' : m ∈ P.comap (C : ℤ →+* ReciprocityTheory.ChartRestriction.G.Geo.MRing ι) := Ideal.mem_comap.mpr hm
    rw [show P.comap (C : ℤ →+* ReciprocityTheory.ChartRestriction.G.Geo.MRing ι) = ⊥ from hhor, Ideal.mem_bot] at hm'
    exact hm'
  obtain ⟨hQ, hcomap, hd⟩ := ReciprocityTheory.AnForm.R.extQ_spec P hch
  refine ⟨(GroundTheory.Heights₂.Heights.NumbersDVR.Objects.isMultiProjPrime_iff _).mpr
    ⟨hQ, ⟨MvPolynomial.map (Int.castRingHom ℚ) '' S, ?_, ?_⟩, ?_⟩, ?_⟩
  · rintro _ ⟨f, hf, rfl⟩
    obtain ⟨a, ha⟩ := hS f hf
    exact ⟨a, fun m hm k => ha m (MvPolynomial.support_map_subset _ _ hm) k⟩
  · rw [hPS, Ideal.map_span]
  · intro k
    obtain ⟨i, hi⟩ := hrel k
    refine ⟨i, fun h => hi ?_⟩
    rw [← hcomap, Ideal.mem_comap, MvPolynomial.map_X]
    exact h
  · have hd' : ringKrullDim (MvPolynomial (Σ k, ι k) ℚ ⧸
        P.map (MvPolynomial.map (Int.castRingHom ℚ))) + 1 =
        ((e + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
      rw [← hdim]
      exact hd
    show ringKrullDim (MvPolynomial (Σ k, ι k) ℚ ⧸ P.map (MvPolynomial.map (Int.castRingHom ℚ))) =
      ((e + Fintype.card K : ℕ) : WithBot ℕ∞)
    generalize ringKrullDim (MvPolynomial (Σ k, ι k) ℚ ⧸
      P.map (MvPolynomial.map (Int.castRingHom ℚ))) = d at hd'
    induction d using WithBot.recBotCoe with
    | bot =>
      rw [WithBot.bot_add] at hd'
      exact absurd hd' (WithBot.bot_ne_coe)
    | coe d =>
      induction d using ENat.recTopCoe with
      | top =>
        have h3 : (⊤ : ℕ∞) + 1 = ((e + 1 + Fintype.card K : ℕ) : ℕ∞) := by exact_mod_cast hd'
        rw [top_add] at h3
        exact absurd h3.symm (ENat.natCast_ne_top _)
      | coe n =>
        have h1 : n + 1 = e + 1 + Fintype.card K := by exact_mod_cast hd'
        have h2 : n = e + Fintype.card K := by omega
        rw [h2]
        rfl

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PBlockGenFinite
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace BlockGenFinite

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

theorem eval_smul_of_isMultiHomog {s : MRing ι} {a : K → ℕ} (hs : IsMultiHomog s a) (c : K → ℂ)
    (u : (Σ k, ι k) → ℂ) :
    eval (fun p ↦ c p.1 * u p) (map (Int.castRingHom ℂ) s) =
      (∏ k, c k ^ a k) * eval u (map (Int.castRingHom ℂ) s) := by
  rw [eval_map, eval_map, eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  have hprod : ∏ p, (c p.1 * u p) ^ d p = (∏ k, c k ^ a k) * ∏ p, u p ^ d p := by
    simp only [mul_pow, Finset.prod_mul_distrib]
    congr 1
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    show ∏ i, c k ^ d ⟨k, i⟩ = c k ^ a k
    rw [Finset.prod_pow_eq_pow_sum, hs d hd k]
  rw [hprod]
  ring

omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in

theorem eval_map_rename (v : (Σ k, ι k) → (Σ k', ι' k')) (s : MRing ι) (z' : (Σ k', ι' k') → ℂ) :
    eval z' (map (Int.castRingHom ℂ) (rename v s)) = eval (fun p ↦ z' (v p)) (map (Int.castRingHom ℂ) s) := by
  rw [map_rename, eval_rename]
  rfl

end BlockGenFinite

open BlockGenFinite in

theorem BlockGenFinite.proof (hR : BlockRatioAlg.Statement) : BlockGenFinite.Statement := by
  classical
  intro K _ ι _ K' _ ι' _ κ v P' n hv hP' hP
  have hrel := hP'.2.1.2.2
  have hpr := hP'.2.1.1
  have hrel' : ∀ k : FibreBlock κ, ∃ i : ι' k.1, (X (⟨k.1, i⟩ : Σ k', ι' k') : MRing ι') ∉ P' := fun k ↦ hrel k.1
  choose c hc using hrel'
  have hA := fun q : (Σ k : FibreBlock κ, ι' k.1) ↦
    hR K ι K' ι' κ v P' n hv hP' hP ⟨q.1.1, q.2⟩ ⟨q.1.1, c q.1⟩ rfl (hc q.1)
  choose m A a hAh hAl hAP using hA
  refine ⟨(∏ q, rename v (A q (Fin.last (m q)))) * ∏ k : FibreBlock κ, X ⟨k.1, c k⟩,
    (∑ q, Function.extend κ (a q) 0) + ∑ k : FibreBlock κ, Pi.single k.1 1, ?_, ?_, ?_⟩
  · exact AvoidRing.isMultiHomog_mul
      (AvoidRing.isMultiHomog_prod _ _ _ fun q _ ↦ ArithmeticIntersectionHorizontal.isMultiHomog_rename hv (hAh q _))
      (AvoidRing.isMultiHomog_prod _ _ _ fun k _ ↦ AvoidRing.isMultiHomog_X _ _)
  · intro h
    rcases hpr.mul_mem_iff_mem_or_mem.mp h with h | h
    · obtain ⟨q, -, hq⟩ := hpr.prod_mem_iff.mp h
      exact hAl q hq
    · obtain ⟨k, -, hk⟩ := hpr.prod_mem_iff.mp h
      exact hc k hk
  intro u

  obtain ⟨pol, hpol⟩ : ∃ pol : (Σ k : FibreBlock κ, ι' k.1) → Polynomial ℂ, ∀ q, pol q =
      ∑ j : Fin (m q + 1), Polynomial.C (eval u (map (Int.castRingHom ℂ) (A q j))) * Polynomial.X ^ (j : ℕ) :=
    ⟨_, fun _ ↦ rfl⟩

  obtain ⟨build, hbuild⟩ : ∃ build : ((Σ k : FibreBlock κ, ι' k.1) → ℂ) → (Σ k', ι' k') → ℂ, ∀ ρ p',
      build ρ p' = if h : p'.1 ∈ Set.range κ then u (hv.2.2.2 p' h).choose else ρ ⟨⟨p'.1, h⟩, p'.2⟩ :=
    ⟨_, fun _ _ ↦ rfl⟩
  refine ⟨(Fintype.piFinset fun q ↦ (pol q).roots.toFinset).image build, ?_⟩
  rintro z' hz' hf0 ⟨d, hd, hzd⟩
  have hzd' : ∀ p, z' (v p) = d p.1 * u p := fun p ↦ congrFun hzd p
  simp only [map_mul, map_prod, map_X, eval_X] at hf0
  have hcz : ∀ k : FibreBlock κ, z' ⟨k.1, c k⟩ ≠ 0 := fun k ↦
    Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hf0) k (Finset.mem_univ _)
  have hlead : ∀ q, eval u (map (Int.castRingHom ℂ) (A q (Fin.last (m q)))) ≠ 0 := by
    intro q h
    have := Finset.prod_ne_zero_iff.mp (left_ne_zero_of_mul hf0) q (Finset.mem_univ _)
    rw [eval_map_rename, show (fun p ↦ z' (v p)) = fun p ↦ d p.1 * u p from hzd,
      eval_smul_of_isMultiHomog (hAh q _), h, mul_zero] at this
    exact this rfl

  have hroot : ∀ q, z' ⟨q.1.1, q.2⟩ / z' ⟨q.1.1, c q.1⟩ ∈ (pol q).roots.toFinset := by
    intro q
    have hne : pol q ≠ 0 := by
      intro h0
      have h1 := congrArg (fun f ↦ Polynomial.coeff f (m q)) h0
      simp only [hpol, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
        Polynomial.coeff_zero] at h1
      rw [Finset.sum_eq_single (Fin.last (m q))] at h1
      · simp only [Fin.val_last, if_true] at h1
        exact hlead q h1
      · intro j _ hj
        rw [if_neg]
        intro e
        exact hj (Fin.ext (by simp [e]))
      · simp
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hne, Polynomial.IsRoot.def]
    have hrel0 := hz'.2 _ (hAP q)
    simp only [map_sum, map_mul, map_pow, map_X, eval_X, eval_map_rename,
      show (fun p ↦ z' (v p)) = fun p ↦ d p.1 * u p from hzd, eval_smul_of_isMultiHomog (hAh q _)] at hrel0
    have hD : (∏ k, d k ^ a q k) * z' ⟨q.1.1, c q.1⟩ ^ m q ≠ 0 :=
      mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hd k)) (pow_ne_zero _ (hcz q.1))
    refine (mul_eq_zero.mp ?_).resolve_left hD
    rw [hpol, Polynomial.eval_finsetSum, Finset.mul_sum, ← hrel0]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have hj : (j : ℕ) ≤ m q := Nat.lt_succ_iff.mp j.2
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    rw [← pow_sub_mul_pow (z' ⟨q.1.1, c q.1⟩) hj, div_pow]
    field_simp [pow_ne_zero _ (hcz q.1)]

  refine ⟨build fun q ↦ z' ⟨q.1.1, q.2⟩ / z' ⟨q.1.1, c q.1⟩,
    Finset.mem_image_of_mem _ (Fintype.mem_piFinset.mpr hroot), ?_⟩
  refine ⟨fun k' ↦ if h : k' ∈ Set.range κ then d h.choose else z' ⟨k', c ⟨k', h⟩⟩,
    fun k' ↦ ?_, funext fun p' ↦ ?_⟩
  · dsimp only
    split_ifs with h
    · exact hd _
    · exact hcz ⟨k', h⟩
  · rw [hbuild]
    by_cases h : p'.1 ∈ Set.range κ
    · rw [dif_pos h]
      dsimp only
      rw [dif_pos h]
      obtain ⟨p, rfl⟩ := hv.2.2.2 p' h
      rw [show h.choose = p.1 from hv.1 (h.choose_spec.trans (hv.2.2.1 p)),
        show (hv.2.2.2 (v p) h).choose = p from hv.2.1 (hv.2.2.2 (v p) h).choose_spec]
      exact hzd' p
    · rw [dif_neg h]
      dsimp only
      rw [dif_neg h]
      have hc' := hcz ⟨p'.1, h⟩
      dsimp only at hc'
      field_simp [hc']

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PPFFibreSum
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

section Homog

variable {R : Type*} [CommRing R] {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem weight_blockSingle (d : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (fun q : Σ k, ι k => (Pi.single q.1 1 : K → ℕ)) d = fun k => ∑ i, d ⟨k, i⟩ := by
  funext k
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_sigma]
  simp [Pi.single_apply]

theorem isMultiHomog_iff_weighted (f : MRingOver R ι) (a : K → ℕ) :
    IsMultiHomog f a ↔ IsWeightedHomogeneous (fun q : Σ k, ι k => (Pi.single q.1 1 : K → ℕ)) f a := by
  constructor
  · intro h d hd
    rw [weight_blockSingle]
    funext k
    exact h d (mem_support_iff.mpr hd) k
  · intro h m hm k
    have := h (mem_support_iff.mp hm)
    rw [weight_blockSingle] at this
    exact congrFun this k

end Homog

section Subst

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')}

omit [Fintype K'] [∀ k, Fintype (ι' k)] in

theorem aeval_baseSubst (hv : IsBlockMap κ v) (G : GenFibre v P') (f : MRing ι') :
    aeval (fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩) (baseSubst κ G f) = aeval G.x' f := by
  have h : ((aeval (fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩) :
      MRingOver G.Φ (fibreIdx ι' κ) →ₐ[G.Φ] G.Φ').toRingHom.comp (baseSubst κ G)) =
      (aeval G.x' : MRing ι' →ₐ[ℤ] G.Φ').toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [show (C r : MRing ι') = (r : MRing ι') from eq_intCast C r, map_intCast]
    · intro q
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
      unfold baseSubst
      rw [eval₂Hom_X']
      split_ifs with h h'
      · rw [aeval_C, ← G.compat, h'.choose_spec]
      · exact absurd (hv.2.2.2 q h) h'
      · rw [aeval_X]
  exact DFunLike.congr_fun h f

theorem baseSubst_isMultiHomog (G : GenFibre v P') {s : MRing ι'} {a : K' → ℕ} (hs : IsMultiHomog s a) :
    IsMultiHomog (baseSubst κ G s) (fun k : FibreBlock κ => a k.1) := by
  classical
  rw [isMultiHomog_iff_weighted] at hs ⊢
  have hg : ∀ q : Σ k', ι' k', IsWeightedHomogeneous
      (fun q : Σ k : FibreBlock κ, ι' k.1 => (Pi.single q.1 1 : FibreBlock κ → ℕ))
      (if h : q.1 ∈ Set.range κ then (if h' : q ∈ Set.range v then C (G.x h'.choose) else 0)
        else X ⟨⟨q.1, h⟩, q.2⟩ : MRingOver G.Φ (fibreIdx ι' κ))
      (fun k : FibreBlock κ => (Pi.single q.1 1 : K' → ℕ) k.1) := by
    intro q
    by_cases h : q.1 ∈ Set.range κ
    · have h0 : (fun k : FibreBlock κ => (Pi.single q.1 1 : K' → ℕ) k.1) = 0 := by
        funext k
        have : k.1 ≠ q.1 := fun e => k.2 (e ▸ h)
        simp [this]
      rw [dif_pos h, h0]
      split_ifs
      · exact isWeightedHomogeneous_C _ _
      · exact isWeightedHomogeneous_zero _ _ _
    · rw [dif_neg h]
      have e : (fun k : FibreBlock κ => (Pi.single q.1 1 : K' → ℕ) k.1) =
          (Pi.single (⟨q.1, h⟩ : FibreBlock κ) 1 : FibreBlock κ → ℕ) := by
        funext k
        simp [Pi.single_apply, Subtype.ext_iff]
      rw [e]
      exact isWeightedHomogeneous_X G.Φ _ (⟨⟨q.1, h⟩, q.2⟩ : Σ k : FibreBlock κ, ι' k.1)
  induction hs using IsWeightedHomogeneous.induction_on with
  | zero => rw [map_zero]; exact isWeightedHomogeneous_zero _ _ _
  | add p q hp hq ihp ihq => rw [map_add]; exact ihp.add ihq
  | monomial d r hr =>
    unfold baseSubst
    rw [coe_eval₂Hom, eval₂_monomial, MvPolynomial.algebraMap_apply, Finsupp.prod]
    convert ((IsWeightedHomogeneous.prod d.support _ _ fun q _ => (hg q).pow (d q)).C_mul _) using 1
    funext k
    rw [← hr]
    simp [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]

end Subst

theorem PFFibreSum.proof (hFD : FibreDimStatement) (hBij : PFFibreBij.Statement) (hMult : PFFibreMult.Statement) :
    PFFibreSum.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' d r G J N s a hv hP' hP hJ hNa hs hsP
  classical
  have hV : IsProjVarF (fibreIdeal κ G) (r + 1) := hFD K ι K' ι' κ v P' d (r + 1) G hv hP' hP
  have hmem : ∀ g : MRing ι', baseSubst κ G g ∈ fibreIdeal κ G ↔ g ∈ P' := by
    intro g
    rw [fibreIdeal, RingHom.mem_ker, aeval_baseSubst hv, ← RingHom.mem_ker, G.genericFibre_ker_target]
  have hsec : IsRatSection (fibreIdeal κ G) (fibreDeg κ (N (Fin.last r)).a) (baseSubst κ G s) 1 := by
    refine ⟨fun k => a k.1, 0, baseSubst_isMultiHomog G hs,
      (isMultiHomog_iff_weighted _ _).mpr (isWeightedHomogeneous_one _ _), fun h => hsP ((hmem s).mp h),
      fun h1 => hV.1.1.ne_top ((Ideal.eq_top_iff_one _).mpr h1), fun k => ?_⟩
    simp [fibreDeg, hNa]
  have hb' : J (fibreIdeal κ G) (r + 1) (fun j => fibreDeg κ (N j).a) =
      cycEval (fun W => J W r (fun j => fibreDeg κ (N (Fin.castSucc j)).a))
        (ratDiv (fibreIdeal κ G) (baseSubst κ G s) 1) := by
    rw [← hJ.2 _ r _ _ _ _ hV hsec]
    exact congrArg _ (Fin.snoc_init_self (α := fun _ => FibreBlock κ → ℤ) (fun j => fibreDeg κ (N j).a)).symm
  have hdiv1 : divCycle (fibreIdeal κ G) 1 = 0 := by
    ext W
    simp only [divCycle, Finsupp.ofSupportFinite_coe, Finsupp.coe_zero, Pi.zero_apply]
    rw [if_neg]
    simp [divSupp, Ideal.span_singleton_one, Ideal.minimalPrimes_top]
  set L := fun j : Fin r => fibreDeg κ (N (Fin.castSucc j)).a
  set V := fibreIdeal κ G
  set f := baseSubst κ G s
  have hD : ∀ Q, (divCycle V f Q : ℝ) = if Q ∈ divSupp V f then (multAt (V ⊔ Ideal.span {f}) Q : ℝ) else 0 := by
    intro Q
    simp only [divCycle, Finsupp.ofSupportFinite_coe]
    split_ifs <;> simp

  have hR : ((cycEval (fun W => J W r L) (ratDiv V f 1) : ℤ) : ℝ) =
      ∑ᶠ Q ∈ divSupp V f, (multAt (V ⊔ Ideal.span {f}) Q : ℝ) * (J Q r L : ℝ) := by
    rw [ratDiv, hdiv1, Finsupp.mapRange_zero, sub_zero, cycEval,
      Finsupp.sum_mapRange_index (fun _ => zero_mul _), Finsupp.sum, Int.cast_sum,
      finsum_mem_def]
    simp only [Int.cast_mul, Int.cast_natCast]
    have hsupp : Function.support (fun Q => (divCycle V f Q : ℝ) * (J Q r L : ℝ)) ⊆ ↑(divCycle V f).support := by
      intro Q hQ
      rw [Function.mem_support] at hQ
      rw [Finset.mem_coe, Finsupp.mem_support_iff]
      intro h0
      exact hQ (by rw [h0]; simp)
    rw [← finsum_eq_sum_of_support_subset _ hsupp]
    congr 1
    funext Q
    rw [hD]
    by_cases hQ : Q ∈ divSupp V f <;> simp [hQ, Set.indicator]

  have hL : ∑ᶠ W ∈ divSupp P' s, (multAt (P' ⊔ Ideal.span {s}) W : ℝ) *
        (if IsHorizontal W ∧ imageZ v W = imageZ v P' then (J (fibreOf κ G W) r L : ℝ) else 0) =
      ∑ᶠ W ∈ {W | W ∈ divSupp P' s ∧ IsHorizontal W ∧ imageZ v W = imageZ v P'},
        (multAt (P' ⊔ Ideal.span {s}) W : ℝ) * (J (fibreOf κ G W) r L : ℝ) := by
    rw [finsum_mem_def, finsum_mem_def]
    congr 1
    funext W
    by_cases hW : W ∈ divSupp P' s <;> by_cases hH : IsHorizontal W ∧ imageZ v W = imageZ v P' <;>
      simp [Set.indicator, hW, hH]
  rw [hb', hR, hL]
  refine finsum_mem_eq_of_bijOn (fibreOf κ G) (hBij K ι K' ι' κ v P' d (d + r + 1) G s hv hP' hP) ?_
  rintro W ⟨hW, hH, hI⟩
  rw [hMult K ι K' ι' κ v P' d (d + r + 1) G s W hv hP' hP hW hH hI]

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StLocRingInj
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def LocRingInj.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P W W' : Ideal (MRing ι)),
    P.IsPrime → IsMultiProjPrime W → IsMultiProjPrime W' → P ≤ W → P ≤ W' →
    locRing P W = locRing P W' → W = W'

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StZIntAdd
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open GroundTheory.Heights₂.Heights.NumbersDVR (MRing)

def ZIntAdd.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι ℂ)) (e : ℕ) (L : Fin e → HLine ι) (A B : HLine ι),
    IsProjVar P (e + 1) → Nonempty (Res ι P (e + 1)) → (∀ j, IsSmoothMetric P (L j)) →
    IsSmoothMetric P A → IsSmoothMetric P B →
    zInt P (e + 1) (Fin.cons (logH (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor A B)) fun j => logH (L j))
        (fun _ => 1) =
      zInt P (e + 1) (Fin.cons (logH A) fun j => logH (L j)) (fun _ => 1) +
        zInt P (e + 1) (Fin.cons (logH B) fun j => logH (L j)) (fun _ => 1)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsLocRingDimOne
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

def LocRingDimOne.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (s : MRing ι) (a : K → ℕ)
    (W : Ideal (MRing ι)),
    IsMultiProjPrime P → IsMultiHomog s a → s ∉ P → W ∈ divSupp P s →
    IsNoetherianRing (locRing P W) ∧ IsLocalRing (locRing P W) ∧ ringKrullDim (locRing P W) = 1

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsLocRingIntClosure
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

def LocRingIntClosureFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ) (s : MRing ι) (α : K → ℕ)
    (W : Ideal (MRing ι)) (_hv : IsBlockMap κ v) (hP' : IsArithVar P' (n + 1)),
    IsArithVar (imageZ v P') (n + 1) → IsMultiHomog s α → s ∉ imageZ v P' → W ∈ divSupp (imageZ v P') s →
    haveI := hP'.2.1.1
    letI := ((fracMapZ v P').comp (locRing (imageZ v P') W).subtype).toAlgebra
    letI : Module (locRing (imageZ v P') W) (FractionRing (MRing ι' ⧸ P')) := Algebra.toModule
    ∃ t : Finset (FractionRing (MRing ι' ⧸ P')), ∀ x ∈ semiLocRing P' ∅,
      IsIntegral (locRing (imageZ v P') W) x → x ∈ Submodule.span (locRing (imageZ v P') W) (t : Set _)

end GroundTheory.Heights₂.Heights.Inter
end
end

