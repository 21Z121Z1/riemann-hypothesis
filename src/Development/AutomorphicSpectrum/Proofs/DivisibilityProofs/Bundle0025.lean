import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0016
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0061
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0008
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0024
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0011
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0041
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0015
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0001
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0014
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0018

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.DivisorCycleSubstitution
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem divCycle_support_finite {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι O)) (f : MRing ι O) : (Function.support (divCycle P f)).Finite := by
  haveI : IsNoetherianRing (MRing ι O) := by
    unfold MRing
    infer_instance
  refine (Ideal.finite_minimalPrimes_of_isNoetherianRing (MRing ι O) (P ⊔ Ideal.span {f})).subset ?_
  intro W hW
  by_contra hn
  apply hW
  unfold divCycle
  rw [dif_neg]
  exact fun h => hn h.1

theorem cycList_ratDiv {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι O)) (f g : MRing ι O) (l : List (K → ℤ)) :
    cycList (ratDiv P f g) l = cycList (divCycle P f) l - cycList (divCycle P g) l := by
  have e : ratDiv P f g = divCycle P f - divCycle P g := rfl
  unfold cycList
  rw [e]
  exact (cycEval_sub_cycle _ _ _ (divCycle_support_finite P f) (divCycle_support_finite P g)).symm

theorem cycNum_subst_of_add {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (Z : Ideal (MRing ι O) → ℤ) (d : ℕ)
    (hadd : ∀ (b b' : K → ℤ) (l : List (K → ℤ)), l.length + 1 = d →
      cycList Z ((b + b') :: l) = cycList Z (b :: l) + cycList Z (b' :: l))
    {σ σ' : Type} [Fintype σ] (cls : σ → K → ℤ) (M : σ' → σ → ℤ) (H : MvPolynomial σ' ℝ) (m : ℕ)
    (hH : H.IsHomogeneous m) (Q : List (K → ℤ)) (hQ : m + Q.length = d) :
    cycNum Z (fun t => ∑ i, M t i • cls i) H Q =
      cycNum Z cls (aeval (fun t => ∑ i, (C (M t i : ℝ) * X i : MvPolynomial σ ℝ)) H) Q :=
  GlobalTheory.T.homogeneous_class_substitution (K → ℤ) d (fun l => (cycList Z l : ℝ))
    (fun l l' h => by rw [GlobalTheory.T.cycle_list_perm_invariant.2 O K ι Z l l' h])
    (fun b b' l h => by rw [hadd b b' l h]; push_cast; rfl)
    σ σ' cls M H m hH Q hQ

theorem cycNum_linear_subst : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d → ∀ (a a' : K → ℕ) (f g : MRing ι O), IsMultiHomog f a → IsMultiHomog g a' → f ∉ P → g ∉ P → ∀ (σ σ' : Type) [Fintype σ] (cls : σ → K → ℤ) (M : σ' → σ → ℤ) (H : MvPolynomial σ' ℝ) (m : ℕ), H.IsHomogeneous m → ∀ Q : List (K → ℤ), m + Q.length = d → cycNum (ratDiv P f g) (fun t => ∑ i, M t i • cls i) H Q = cycNum (ratDiv P f g) cls (aeval (fun t => ∑ i, (C (M t i : ℝ) * X i : MvPolynomial σ ℝ)) H) Q ∧ cycNum (divCycle P f) (fun t => ∑ i, M t i • cls i) H Q = cycNum (divCycle P f) cls (aeval (fun t => ∑ i, (C (M t i : ℝ) * X i : MvPolynomial σ ℝ)) H) Q := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP a a' f g hf hg hfP hgP σ σ' _ cls M H m hH Q hQ
  have af := GlobalTheory.T.divisor_cycle_list_additive O ϖ hϖ K ι P d hP a f hf hfP
  have ag := GlobalTheory.T.divisor_cycle_list_additive O ϖ hϖ K ι P d hP a' g hg hgP
  refine ⟨cycNum_subst_of_add _ d (fun b b' l h => ?_) cls M H m hH Q hQ,
    cycNum_subst_of_add _ d (af · · · ·) cls M H m hH Q hQ⟩
  rw [cycList_ratDiv, cycList_ratDiv, cycList_ratDiv, af b b' l h, ag b b' l h]
  ring

end GlobalTheory.CompanionTheory.Ar.Num
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagFramePointDimension
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.flag_frame_point_dimension : NumericalSegre.Statement → ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (e : ℕ), IsMultiProjPrime (pointIdeal F y) → ringKrullDim (MRing ι F ⧸ pointIdeal F y) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) → ∀ (N : ℕ) (w : Module.Basis (Fin N) Ω (Fin N → Ω)) (b : Fin N → K → ℤ), IsFlagFrame y (scaledTrivBundle F (segreVec y) N (one_ne_zero (α := Ω))) w b → ∀ k : ℕ, 1 ≤ k → ∀ Q : List (K → ℤ), Q.length + k = e → genNum F (pointIdeal F y) b (∑ i, X i ^ k) Q = 0 := by
  intro hS F _ Ω _ _ K _ _ ι _ y e hP hdim N w b hb k hk Q hQ
  obtain ⟨R, hR, hsum⟩ := psum_eq_sum_hsymm_neg N k hk
  rw [hsum, (genNum_linear F K ι (Fin N) (pointIdeal F y) b Q).2.2.1]
  refine Finset.sum_eq_zero fun a ha => ?_
  obtain ⟨ha1, hak⟩ := Finset.mem_Icc.mp ha
  rw [genNum_mul_expand]
  refine Finset.sum_eq_zero fun μ hμ => ?_
  have hlen : (classList b μ).length = k - a :=
    PositivityTheory.HtPt.Pflag.length_classList_of_hom b (hR a) hμ
  have hl : a + (classList b μ ++ Q).length = e := by
    rw [List.length_append, hlen]
    omega
  rw [PositivityTheory.HtPt.Pflag.genNum_neg F K ι (pointIdeal F y) e hP hdim b _ a
      (PositivityTheory.HtPt.Pflag.isHomogeneous_hsymm_real N a) _ hl,
    PositivityTheory.HtPt.Pflag.genNum_hsymm,
    hsymm_dualRoots_triv_numZero hS F Ω K ι y e hP hdim N w b hb a ha1 _ hl]
  simp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FractionRingRingEquiv
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num

noncomputable def fractionRingRingEquiv (A L : Type) [CommRing A] [IsDomain A] [Field L] [Algebra A L]
    [IsFractionRing A L] : L ≃+* FractionRing A :=
  (FractionRing.algEquiv A L).toRingEquiv.symm

noncomputable def ratEquivFractionZP (p : Nat.Primes) : ℚ ≃+* FractionRing (ZP p) :=
  letI : Algebra (ZP p) ℚ :=
    (IsLocalization.lift (M := (Ideal.span {((p : ℕ) : ℤ)}).primeCompl) (S := ZP p)
      (g := algebraMap ℤ ℚ) (fun y => isUnit_iff_ne_zero.2 (by
        have hy : (y : ℤ) ≠ 0 := fun h => y.2 (h ▸ Ideal.zero_mem _)
        simpa using hy))).toAlgebra
  haveI : @IsScalarTower ℤ (ZP p) ℚ Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)
  haveI : IsFractionRing (ZP p) ℚ :=
    IsFractionRing.isFractionRing_of_isLocalization
      (Ideal.span {((p : ℕ) : ℤ)}).primeCompl (ZP p) ℚ (Ideal.primeCompl_le_nonZeroDivisors _)
  fractionRingRingEquiv (ZP p) ℚ

theorem genFib_extTo_zp {K : Type} {ι : K → Type} (P : Ideal (MRing ι ℤ)) (p : Nat.Primes) :
    genFib (extTo (ZP p) P) =
      (extTo ℚ P).map (MvPolynomial.map ((ratEquivFractionZP p : ℚ ≃+* FractionRing (ZP p)) :
        ℚ →+* FractionRing (ZP p))) := by
  unfold genFib extTo
  rw [Ideal.map_map, Ideal.map_map]
  congr 1
  refine RingHom.ext fun f => ?_
  simp only [RingHom.comp_apply, MvPolynomial.map_map]
  exact congrArg (fun φ : ℤ →+* FractionRing (ZP p) => MvPolynomial.map φ f) (RingHom.ext_int _ _)

theorem genNum_zp_eq_rat (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι ℤ)) (p : Nat.Primes) (σ : Type) (cls : σ → K → ℤ) (H : MvPolynomial σ ℝ)
    (Q : List (K → ℤ)) :
    genNum (FractionRing (ZP p)) (genFib (extTo (ZP p) P)) cls H Q = genNum ℚ (extTo ℚ P) cls H Q := by
  unfold genNum
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [genFib_extTo_zp, GlobalTheory.T.intersection_number_field_equiv K ι ℚ (FractionRing (ZP p)) (ratEquivFractionZP p)]

end GlobalTheory.CompanionTheory.Ar.Num
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HodgeComponentFactorPointStatement
section
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_component_factor_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S y), Mono (spMap β) → ∃ x : Sp A.Ω₀ ⟶ Xo.XF c, A.ξ₀ = x ≫ Y.j := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GenOpen.gen_open | exact GlobalTheory.CompanionTheory.Ar.GenOpen.gen_open | (intros; apply GlobalTheory.CompanionTheory.Ar.GenOpen.gen_open <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IsometricVerticalIntersectionEq
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num.Link

theorem divCycle_eq_off {K : Type} {ι : K → Type} {P : Ideal (MRing ι ℤ)} {f g : MRing ι ℤ} {S : Finset Nat.Primes}
    (h : ∀ W : Ideal (MvPolynomial (Σ k, ι k) ℤ), W.IsPrime → P ≤ W → IsRelevant W →
      (∀ p ∈ S, (C ((p : ℕ) : ℤ) : MvPolynomial (Σ k, ι k) ℤ) ∉ W) →
      ∃ u v : MvPolynomial (Σ k, ι k) ℤ, u ∉ W ∧ v ∉ W ∧ u * f - v * g ∈ P)
    {W : Ideal (MRing ι ℤ)}
    (hW : W.IsPrime → ∀ p ∈ S, (C ((p : ℕ) : ℤ) : MvPolynomial (Σ k, ι k) ℤ) ∉ W) :
    divCycle P f W = divCycle P g W := by
  by_cases hc : W.IsPrime ∧ P ≤ W ∧ IsRelevant W
  · obtain ⟨u, v, hu, hv, huv⟩ := h W hc.1 hc.2.1 hc.2.2 (hW hc.1)
    exact divCycle_eq_of_mul_sub_mem hu hv huv
  · have h0 : ∀ s : MRing ι ℤ, divCycle P s W = 0 := fun s => by
      by_contra hne
      exact hc (le_and_isRelevant_of_divCycle_ne_zero hne)
    rw [h0, h0]

theorem not_mem_of_mem {K : Type} {ι : K → Type} {W : Ideal (MRing ι ℤ)} (hW : W.IsPrime) {p q : Nat.Primes}
    (hpq : p ≠ q) (hp : (C ((p : ℕ) : ℤ) : MvPolynomial (Σ k, ι k) ℤ) ∈ W) :
    (C ((q : ℕ) : ℤ) : MvPolynomial (Σ k, ι k) ℤ) ∉ W := by
  intro hq
  have hcop : IsCoprime ((p : ℕ) : ℤ) ((q : ℕ) : ℤ) := by
    rw [Nat.isCoprime_iff_coprime]
    exact (Nat.coprime_primes p.2 q.2).2 fun h => hpq (Subtype.ext h)
  obtain ⟨a, b, hab⟩ := hcop
  apply hW.ne_top
  rw [Ideal.eq_top_iff_one]
  have e : (1 : MvPolynomial (Σ k, ι k) ℤ) =
      C a * C ((p : ℕ) : ℤ) + C b * C ((q : ℕ) : ℤ) := by
    rw [← C_mul, ← C_mul, ← C_add, hab, C_1]
  rw [e]
  exact W.add_mem (W.mul_mem_left _ hp) (W.mul_mem_left _ hq)

theorem not_mem_of_horizontal {K : Type} {ι : K → Type} {W : Ideal (MRing ι ℤ)} (hW : IsHorizontal W)
    (p : Nat.Primes) : (C ((p : ℕ) : ℤ) : MvPolynomial (Σ k, ι k) ℤ) ∉ W := by
  intro hp
  have h1 : ((p : ℕ) : ℤ) ∈ W.comap (C : ℤ →+* MvPolynomial (Σ k, ι k) ℤ) := hp
  rw [show W.comap (C : ℤ →+* MvPolynomial (Σ k, ι k) ℤ) = ⊥ from hW, Ideal.mem_bot] at h1
  exact p.2.ne_zero (by exact_mod_cast h1)

theorem change_line : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι ℤ)) (D : ℕ), IsArithVar P (D + 1) → ∀ (I : Ideal (MRing ι ℤ) → (n : ℕ) → (Fin n → HermLine ι) → ℝ), IsIntersectionFamily I → ∀ (S : Finset Nat.Primes) (T : LocPair ι ℤ Unit), T.IsVertOff P S → ∀ A A' : HermLine ι, IsSmoothHerm A → IsSmoothHerm A' → T.IsIsometric P (fun _ => A) (fun _ => A') → ∀ L : Fin D → HermLine ι, (∀ j, IsSmoothHerm (L j)) → I P (D + 1) (Fin.snoc L A) - I P (D + 1) (Fin.snoc L A') = ∑ p ∈ S, Real.log (p : ℕ) * ((vertAt p P (T.f ()) (List.ofFn fun j => (L j).a) : ℝ) - (vertAt p P (T.g ()) (List.ofFn fun j => (L j).a) : ℝ)) := by
  intro K _ _ ι _ P D hP I hI S T hT A A' hA hA' hiso L hL
  obtain ⟨⟨bf, bg, hf, hg, hdeg⟩, hfP, hgP, hunit⟩ := hT ()
  obtain ⟨hAa, hA'a, hnorm⟩ := hiso ()
  let B : HermLine ι := (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.sqMetric bf).tensor A.inv
  have hB : IsSmoothHerm B := ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_tensor
    (ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_sqMetric bf) (ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_inv hA)
  have hAB : IsSmoothHerm (A.tensor B) := ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_tensor hA hB
  have hAB' : IsSmoothHerm (A'.tensor B) := ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_tensor hA' hB
  have dF : ∀ k, (A.tensor B).a k = bf k := fun k => by
    simp [B, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.inv,
      ReciprocityTheory.ChartRestriction.G.Geo.HermLine.sqMetric]
  have dG : ∀ k, (A'.tensor B).a k = bg k := fun k => by
    have h1 := congrFun hdeg k
    have h2 := congrFun hAa k
    have h3 := congrFun hA'a k
    simp only [Pi.sub_apply] at h1
    simp only [B, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.inv,
      ReciprocityTheory.ChartRestriction.G.Geo.HermLine.sqMetric, Pi.add_apply, Pi.neg_apply]
    linarith
  have e1 := hI.2.1 P D L A B hP hL hA hB
  have e2 := hI.2.1 P D L A' B hP hL hA' hB
  have r1 := hI.2.2 P D L (A.tensor B) (T.f ()) bf hP hL hAB dF
    ((GroundTheory.Heights₂.Heights.Bridge.isMultiHomog_iff _ _).1 hf) hfP
  have r2 := hI.2.2 P D L (A'.tensor B) (T.g ()) bg hP hL hAB' dG
    ((GroundTheory.Heights₂.Heights.Bridge.isMultiHomog_iff _ _).1 hg) hgP
  obtain ⟨fin1, s1⟩ := GlobalTheory.T.finite_vertical_recursion K ι P D hP I bf (T.f ()) hf hfP L (A.tensor B)
  obtain ⟨fin2, s2⟩ := GlobalTheory.T.finite_vertical_recursion K ι P D hP I bg (T.g ()) hg hgP L (A'.tensor B)
  have hor : (∑ᶠ W, (divCycle P (T.f ()) W : ℝ) * Set.indicator {W | IsHorizontal W} (fun W => I W D L) W) =
      ∑ᶠ W, (divCycle P (T.g ()) W : ℝ) * Set.indicator {W | IsHorizontal W} (fun W => I W D L) W := by
    refine finsum_congr fun W => ?_
    by_cases hW : IsHorizontal W
    · rw [divCycle_eq_off hunit (fun _ p _ => not_mem_of_horizontal hW p)]
    · have : W ∉ {W | IsHorizontal W} := hW
      simp [Set.indicator_of_notMem this]
  have ar : arInt P (T.f ()) (A.tensor B) L = arInt P (T.g ()) (A'.tensor B) L := by
    refine (GlobalTheory.T.log_integral_congr_smul K ι P D _).1 _ _ fun z hz => ?_
    have h1 := hnorm z hz
    have pA := A.pos z hz.1
    have pA' := A'.pos z hz.1
    have pB := B.pos z hz.1
    simp only [ReciprocityTheory.ChartRestriction.G.Geo.logNorm, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor]
    congr 1
    rw [div_eq_div_iff (by positivity) (by positivity)]
    linear_combination (B.h z) * h1
  have hv : ∀ p : Nat.Primes, p ∉ S → vertAt p P (T.f ()) (List.ofFn fun j => (L j).a) =
      vertAt p P (T.g ()) (List.ofFn fun j => (L j).a) := by
    intro p hp
    unfold vertAt cycEval
    refine finsum_congr fun W => ?_
    by_cases hpW : (C ((p : ℕ) : ℤ) : MvPolynomial (Σ k, ι k) ℤ) ∈ W
    · rw [divCycle_eq_off hunit (fun hWp q hq => not_mem_of_mem hWp
        (fun h : p = q => hp (by rw [h]; exact hq)) hpW)]
    · simp only [if_neg hpW, mul_zero]
  have vert : (∑ᶠ p : Nat.Primes, Real.log (p : ℕ) * (vertAt p P (T.f ()) (List.ofFn fun j => (L j).a) : ℝ)) -
      (∑ᶠ p : Nat.Primes, Real.log (p : ℕ) * (vertAt p P (T.g ()) (List.ofFn fun j => (L j).a) : ℝ)) =
      ∑ p ∈ S, Real.log (p : ℕ) * ((vertAt p P (T.f ()) (List.ofFn fun j => (L j).a) : ℝ) -
        (vertAt p P (T.g ()) (List.ofFn fun j => (L j).a) : ℝ)) := by
    have hF : (Function.support fun p : Nat.Primes =>
        Real.log (p : ℕ) * (vertAt p P (T.f ()) (List.ofFn fun j => (L j).a) : ℝ)).Finite :=
      fin1.subset fun p hp h0 => hp (by simp [h0])
    have hG : (Function.support fun p : Nat.Primes =>
        Real.log (p : ℕ) * (vertAt p P (T.g ()) (List.ofFn fun j => (L j).a) : ℝ)).Finite :=
      fin2.subset fun p hp h0 => hp (by simp [h0])
    rw [← finsum_sub_distrib hF hG,
      finsum_eq_sum_of_support_subset (s := S) _ fun p hp => ?_]
    · exact Finset.sum_congr rfl fun p _ => by ring
    · by_contra hpS
      exact hp (by simp [hv p (by simpa using hpS)])
  have e3 : I P (D + 1) (Fin.snoc L A) - I P (D + 1) (Fin.snoc L A') =
      I P (D + 1) (Fin.snoc L (A.tensor B)) - I P (D + 1) (Fin.snoc L (A'.tensor B)) := by
    rw [e1, e2]; ring
  rw [e3, r1, r2, s1, s2, hor, ar, ← vert]
  ring

end GlobalTheory.CompanionTheory.Ar.Num.Link
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LogIntegralMultilinear
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top.GeoMix

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem line_ext {A B : HermLine ι} (ha : A.a = B.a) (hh : A.h = B.h) : A = B := by
  cases A
  cases B
  cases ha
  cases hh
  rfl

def oneLine (ι : K → Type) [∀ k, Fintype (ι k)] : HermLine ι :=
  HermLine.ofWeight (fun _ => (-1 : ℝ)) (fun _ _ _ => rfl)

theorem smooth_oneLine : IsSmoothHerm (oneLine ι) := by
  show ContDiffOn ℝ _ (fun _ => Real.exp (-(-1 : ℝ))) _
  exact contDiffOn_const

theorem smooth_comb {J : Type} [Fintype J] {ℓ : J → HermLine ι} (hℓ : ∀ j, IsSmoothHerm (ℓ j))
    (n : J → ℤ) : IsSmoothHerm (combLine ℓ n) := by
  refine contDiffOn_prod fun a _ => ?_
  intro z hz
  have h0 : (ℓ a).h z ≠ 0 := ((ℓ a).pos z hz).ne'
  have hf := hℓ a z hz
  have key : ∀ m : ℤ, ContDiffWithinAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => (ℓ a).h z ^ m)
      {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} z := by
    intro m
    cases m with
    | ofNat k => simpa only [Int.ofNat_eq_natCast, zpow_natCast] using hf.pow k
    | negSucc k =>
      simp only [zpow_negSucc]
      exact (hf.pow (k + 1)).inv (pow_ne_zero _ h0)
  exact key _

def extLine {J : Type} (ℓ : J → HermLine ι) : Option J → HermLine ι
  | none => oneLine ι
  | some j => ℓ j

def extExp {J : Type} (m : J → ℤ) : Option J → ℤ
  | none => 0
  | some j => m j

def lastExp {J : Type} : Option J → ℤ
  | none => 1
  | some _ => 0

theorem comb_extExp {J : Type} [Fintype J] (ℓ : J → HermLine ι) (m : J → ℤ) :
    combLine (extLine ℓ) (extExp m) = combLine ℓ m := by
  apply line_ext
  · simp [combLine, Fintype.sum_option, extLine, extExp]
  · funext z
    simp [combLine, Fintype.prod_option, extLine, extExp]

theorem comb_lastExp {J : Type} [Fintype J] (ℓ : J → HermLine ι) :
    combLine (extLine ℓ) lastExp = oneLine ι := by
  apply line_ext
  · simp [combLine, Fintype.sum_option, extLine, lastExp]
  · funext z
    simp [combLine, Fintype.prod_option, extLine, lastExp]

theorem pts_eq_II (II : IntersectionSystem) (hII : IsFullIntersectionSystem II) (P : Ideal (MRing ι))
    {e : ℕ} (L : Fin e → HermLine ι) (hP : IsArithVar P (e + 1)) (hL : ∀ j, IsSmoothHerm (L j)) :
    ptsIntegral P (fun k z => Real.log ((L k).h z)) (fun _ => 1) =
      II K ι P (e + 1) (Fin.snoc L (oneLine ι)) := by
  have h := GlobalTheory.T.arith_intersection_constant_metric II hII.1 K ι P e L (-1) hP hL
  have h' : II K ι P (e + 1) (Fin.snoc L (oneLine ι)) =
      - -1 * ptsIntegral P (fun j z => Real.log ((L j).h z)) (fun _ => 1) := h
  rw [h']
  ring

theorem pts_comb (II : IntersectionSystem) (hII : IsFullIntersectionSystem II) (P : Ideal (MRing ι))
    {e : ℕ} {J : Type} [Fintype J] [DecidableEq J] (ℓ : J → HermLine ι) (n : Fin e → J → ℤ)
    (hP : IsArithVar P (e + 1)) (hℓ : ∀ j, IsSmoothHerm (ℓ j)) :
    ptsIntegral P (fun k z => Real.log ((combLine ℓ (n k)).h z)) (fun _ => 1) =
      ∑ w : Fin e → J, (∏ k, (n k (w k) : ℝ)) *
        ptsIntegral P (fun k z => Real.log ((ℓ (w k)).h z)) (fun _ => 1) := by
  have hext : ∀ o, IsSmoothHerm (extLine ℓ o) := by
    intro o
    cases o with
    | none => exact smooth_oneLine
    | some j => exact hℓ j
  let n' : Fin (e + 1) → Option J → ℤ :=
    Fin.snoc (α := fun _ => Option J → ℤ) (fun k => extExp (n k)) lastExp
  have hn'c : ∀ k : Fin e, n' k.castSucc = extExp (n k) := fun k => by simp [n']
  have hn'l : n' (Fin.last e) = lastExp := by simp [n']
  have hcomb : (Fin.snoc (fun k => combLine ℓ (n k)) (oneLine ι) : Fin (e + 1) → HermLine ι) =
      fun k => combLine (extLine ℓ) (n' k) := by
    funext k
    refine Fin.lastCases ?_ (fun k => ?_) k
    · simp [hn'l, comb_lastExp]
    · simp [hn'c, comb_extExp]
  rw [pts_eq_II II hII P _ hP (fun k => smooth_comb hℓ _), hcomb,
    GlobalTheory.T.arith_intersection_multilinear_all II hII K ι P (e + 1) (Option J) (extLine ℓ) n' hP hext]
  symm
  let E : (Fin e → J) → (Fin (e + 1) → Option J) := fun w =>
    Fin.snoc (α := fun _ => Option J) (fun k => some (w k)) none
  have hEc : ∀ (w : Fin e → J) (k : Fin e), E w k.castSucc = some (w k) := fun w k => by simp [E]
  have hEl : ∀ w : Fin e → J, E w (Fin.last e) = none := fun w => by simp [E]
  refine Finset.sum_of_injOn E ?_ ?_ ?_ ?_
  · intro w _ w' _ h
    funext k
    have := congrFun h k.castSucc
    rw [hEc, hEc] at this
    exact Option.some.inj this
  · intro w _
    exact Finset.mem_coe.2 (Finset.mem_univ _)
  · intro v _ hv
    have hzero : ∏ k, (n' k (v k) : ℝ) = 0 := by
      by_cases hl : v (Fin.last e) = none
      · by_cases hs : ∀ k : Fin e, (v k.castSucc).isSome
        · exfalso
          apply hv
          refine ⟨fun k => (v k.castSucc).get (hs k), Finset.mem_coe.2 (Finset.mem_univ _), ?_⟩
          funext k
          refine Fin.lastCases ?_ (fun k => ?_) k
          · rw [hEl, hl]
          · rw [hEc]
            simp
        · push_neg at hs
          obtain ⟨k, hk⟩ := hs
          have hk' : v k.castSucc = none := by simpa using hk
          refine Finset.prod_eq_zero (Finset.mem_univ k.castSucc) ?_
          rw [hk', hn'c]
          simp [extExp]
      · obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.1 hl
        refine Finset.prod_eq_zero (Finset.mem_univ (Fin.last e)) ?_
        rw [hj, hn'l]
        simp [lastExp]
    rw [hzero, zero_mul]
  · intro w _
    have hlines : (fun k => extLine ℓ (E w k)) =
        (Fin.snoc (fun k => ℓ (w k)) (oneLine ι) : Fin (e + 1) → HermLine ι) := by
      funext k
      refine Fin.lastCases ?_ (fun k => ?_) k
      · simp [hEl, extLine]
      · simp [hEc, extLine]
    rw [hlines, ← pts_eq_II II hII P _ hP (fun k => hℓ _), Fin.prod_univ_castSucc]
    simp [hn'c, hn'l, hEc, hEl, extExp, lastExp]

theorem pts_perm (II : IntersectionSystem) (hII : IsFullIntersectionSystem II) (P : Ideal (MRing ι))
    {e : ℕ} (L : Fin e → HermLine ι) (σ : Equiv.Perm (Fin e)) (hP : IsArithVar P (e + 1))
    (hL : ∀ j, IsSmoothHerm (L j)) :
    ptsIntegral P (fun k z => Real.log ((L (σ k)).h z)) (fun _ => 1) =
      ptsIntegral P (fun k z => Real.log ((L k).h z)) (fun _ => 1) := by
  let τ : Equiv.Perm (Fin (e + 1)) :=
    (finSuccEquivLast.trans (Equiv.optionCongr σ)).trans finSuccEquivLast.symm
  have hτc : ∀ k : Fin e, τ k.castSucc = (σ k).castSucc := fun k => by simp [τ]
  have hτl : τ (Fin.last e) = Fin.last e := by simp [τ]
  have hcomp : (Fin.snoc (fun k => L (σ k)) (oneLine ι) : Fin (e + 1) → HermLine ι) =
      (Fin.snoc L (oneLine ι) : Fin (e + 1) → HermLine ι) ∘ τ := by
    funext k
    refine Fin.lastCases ?_ (fun k => ?_) k
    · simp [hτl]
    · simp [hτc]
  have hsm : ∀ j, IsSmoothHerm ((Fin.snoc L (oneLine ι) : Fin (e + 1) → HermLine ι) j) := by
    intro j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simpa using smooth_oneLine
    · simpa using hL k
  rw [pts_eq_II II hII P _ hP (fun k => hL _), pts_eq_II II hII P _ hP hL, hcomp]
  exact (hII.1 K ι).1 P (e + 1) _ τ hP hsm

theorem pts_deg (II : IntersectionSystem) (hII : IsFullIntersectionSystem II) (P : Ideal (MRing ι))
    {e : ℕ} (L L' : Fin e → HermLine ι) (hP : IsArithVar P (e + 1)) (hL : ∀ j, IsSmoothHerm (L j))
    (hL' : ∀ j, IsSmoothHerm (L' j)) (ha : ∀ k, (L' k).a = (L k).a) :
    ptsIntegral P (fun k z => Real.log ((L' k).h z)) (fun _ => 1) =
      ptsIntegral P (fun k z => Real.log ((L k).h z)) (fun _ => 1) := by
  have hD := GlobalTheory.T.intersection_system_degree II hII.1
  have h1 : ptsIntegral P (fun k z => Real.log ((L k).h z)) (fun _ => 1) = _ :=
    hD K ι P e L 2 hP hL Nat.prime_two
  have h2 : ptsIntegral P (fun k z => Real.log ((L' k).h z)) (fun _ => 1) = _ :=
    hD K ι P e L' 2 hP hL' Nat.prime_two
  have hdeg : (fun j => (L' j).a) = fun j => (L j).a := funext ha
  rw [h1, h2, hdeg]

end GlobalTheory.CompanionTheory.Ar.Top.GeoMix

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem geo_multilin : ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ) (J : Type) [Fintype J] [DecidableEq J] (ℓ : J → HermLine ι) (n : Fin e → J → ℤ), IsArithVar P (e + 1) → (∀ j, IsSmoothHerm (ℓ j)) → (ptsIntegral P (fun k z => Real.log ((combLine ℓ (n k)).h z)) (fun _ => 1) = ∑ w : Fin e → J, (∏ k, (n k (w k) : ℝ)) * ptsIntegral P (fun k z => Real.log ((ℓ (w k)).h z)) (fun _ => 1)) ∧ (∀ (L L' : Fin e → HermLine ι) (σ : Equiv.Perm (Fin e)), (∀ k, IsSmoothHerm (L k)) → (∀ k, IsSmoothHerm (L' k)) → (∀ k, (L' k).a = (L (σ k)).a) → ptsIntegral P (fun k z => Real.log ((L' k).h z)) (fun _ => 1) = ptsIntegral P (fun k z => Real.log ((L k).h z)) (fun _ => 1)) := by
  intro II hII K _ ι _ P e J _ _ ℓ n hP hℓ
  refine ⟨GeoMix.pts_comb II hII P ℓ n hP hℓ, ?_⟩
  intro L L' σ hL hL' ha
  rw [GeoMix.pts_deg II hII P (fun k => L (σ k)) L' hP (fun k => hL _) hL' ha]
  exact GeoMix.pts_perm II hII P L σ hP hL

end GlobalTheory.CompanionTheory.Ar.Top
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.VerticalNumberLocalCycleStatement
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vertical_number_local_cycle : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι ℤ)) (D : ℕ), IsArithVar P (D + 1) → ∀ (p : Nat.Primes) (a : K → ℕ) (f : MRing ι ℤ), IsMultiHomog f a → f ∉ P → ∀ l : List (K → ℤ), l.length = D → vertAt p P f l = cycList (divCycle (extTo (ZP p) P) (MvPolynomial.map (Int.castRingHom (ZP p)) f)) l := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.vertAt_eq_cycList | exact GlobalTheory.CompanionTheory.Ar.Num.vertAt_eq_cycList | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.vertAt_eq_cycList <;> assumption)
end

