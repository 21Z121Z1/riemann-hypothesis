import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2813
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0592
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0858
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2584
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2847
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2662
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2819
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPdivGroupForPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0659
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0191
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2367
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2680
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2805
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2844
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2405
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2666
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2803
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2761
import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeDecompositionOfIdeleApprox
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory.CMTorsion
open GlobalTheory.WeierstrassCurve (scheme toSpec mapHom)

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (finiteAdeleMap finiteCompletionMap finiteCompletionMap_coe finiteCompletionMap_mapsTo)

namespace GlobalTheory.LatDecomp

variable {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]

theorem finiteAdeleMap_algebraMap (a : K) :
    finiteAdeleMap K E (algebraMap K (Af K) a) = algebraMap E (Af E) (algebraMap K E a) :=
  FiniteAdeleRing.ext _ fun w => finiteCompletionMap_coe K E w a

theorem finiteAdeleMap_integral {z : Af K} (hz : ∀ v, Valued.v (z v) ≤ 1) (w : HeightOneSpectrum (𝓞 E)) :
    (finiteAdeleMap K E z) w ∈ w.adicCompletionIntegers E :=
  finiteCompletionMap_mapsTo K E w ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hz _))

theorem algebraMap_integral (s : 𝓞 E) (w : HeightOneSpectrum (𝓞 E)) :
    (algebraMap E (Af E) (s : E)) w ∈ w.adicCompletionIntegers E := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, FiniteAdeleRing.algebraMap_apply,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact w.valuation_le_one s

theorem exists_nat_mul_integral (a : Af E) :
    ∃ d : ℕ, d ≠ 0 ∧ ∀ w, ((d : Af E) * a) w ∈ w.adicCompletionIntegers E := by
  obtain ⟨β, hβ0, hβ⟩ := GlobalTheory.Idele.exists_mul_integral (R := 𝓞 E) (K := E) a
  have hmem : ((Ideal.absNorm (Ideal.span {β}) : ℕ) : 𝓞 E) ∈ Ideal.span {β} := Ideal.absNorm_mem _
  obtain ⟨g0, hg0⟩ := Ideal.mem_span_singleton'.1 hmem
  refine ⟨Ideal.absNorm (Ideal.span {β}), ?_, fun w => ?_⟩
  · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hβ0
  · have e : ((Ideal.absNorm (Ideal.span {β}) : ℕ) : Af E) =
        algebraMap E (Af E) ((g0 : 𝓞 E) : E) * algebraMap E (Af E) (algebraMap (𝓞 E) E β) := by
      rw [← map_mul]
      have := congrArg (fun r : 𝓞 E => algebraMap E (Af E) (r : E)) hg0
      simp only [map_natCast] at this
      rw [← this]; push_cast; rfl
    rw [e, _root_.mul_assoc]
    exact mul_mem (algebraMap_integral g0 w) ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hβ w))

end GlobalTheory.LatDecomp

namespace GlobalTheory.LatDecomp

variable {E : Type} [Field E] [NumberField E]

theorem exists_nat_mul_good {c : Ideal (OF E)} (hc : c ≠ ⊥) (y : (Af E)ˣ) (e : E) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ z : Af E, (∀ w, z w ∈ w.adicCompletionIntegers E) →
      z * algebraMap E (Af E) ((N : E) * e) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c := by
  obtain ⟨d, hd0, hd⟩ := exists_nat_mul_integral (algebraMap E (Af E) e * ((y⁻¹ : (Af E)ˣ) : Af E))
  have hN : Ideal.absNorm c ≠ 0 := fun h => hc (Ideal.absNorm_eq_zero_iff.1 h)
  refine ⟨Ideal.absNorm c * d, Nat.mul_ne_zero hN hd0, fun z hz => ?_⟩
  have h := GlobalTheory.CMVal.PicFin.mul_mem_hatO (Ideal.absNorm_mem c)
    (y := z * ((d : Af E) * (algebraMap E (Af E) e * ((y⁻¹ : (Af E)ˣ) : Af E)))) (fun w => mul_mem (hz w) (hd w))
  have e1 : z * algebraMap E (Af E) (((Ideal.absNorm c * d : ℕ) : E) * e) * ((y⁻¹ : (Af E)ˣ) : Af E) =
      algebraMap E (Af E) (algebraMap (OF E) E ((Ideal.absNorm c : ℕ) : OF E)) *
        (z * ((d : Af E) * (algebraMap E (Af E) e * ((y⁻¹ : (Af E)ˣ) : Af E)))) := by
    simp only [map_mul, map_natCast, Nat.cast_mul]
    ring
  rw [e1]; exact h

end GlobalTheory.LatDecomp

namespace GlobalTheory.LatDecomp

theorem exists_decomp : ∀ (K : Type) [Field K] [NumberField K] (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E]
    (t : (Af K)ˣ) (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ → ∀ x x' : E,
    ((upIdele K E t : Af E) * algebraMap E (Af E) x' - algebraMap E (Af E) x) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c →
    ∃ (m : ℕ) (b : Fin m → E) (a a' : Fin m → K), (∀ k (r : 𝓞 K), algebraMap K E (r : K) * b k ∈ lattice c y) ∧
      x' = ∑ k, algebraMap K E (a' k) * b k ∧ x - ∑ k, algebraMap K E (a k) * b k ∈ lattice c y ∧
      ∀ k (v : HeightOneSpectrum (𝓞 K)),
        Valued.v (((t : Af K) * algebraMap K (Af K) (a' k) - algebraMap K (Af K) (a k)) v) ≤ 1 := by
  intro K _ _ E _ _ _ _ t c y hc x x' hx
  haveI : Module.Finite K E := Module.Finite.of_restrictScalars_finite ℚ K E
  set B := Module.finBasis K E
  set yi : Af E := ((y⁻¹ : (Af E)ˣ) : Af E)
  choose N hN0 hN using fun k => exists_nat_mul_good hc y (B k)
  set b : Fin (Module.finrank K E) → E := fun k => (N k : E) * B k with hb
  set a' : Fin (Module.finrank K E) → K := fun k => B.repr x' k / (N k : K) with ha'
  have hNK : ∀ k, (N k : K) ≠ 0 := fun k => Nat.cast_ne_zero.2 (hN0 k)

  have happrox : ∀ z : Af K, ∃ a : K, ∀ v, Valued.v ((z - algebraMap K (Af K) a) v) ≤ 1 := fun z => by
    obtain ⟨a, u, hu, e⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat K 1 one_pos).1 z
    refine ⟨a, fun v => ?_⟩
    rw [e, one_smul, add_sub_cancel_left]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hu v)
  choose a ha using fun k => happrox ((t : Af K) * algebraMap K (Af K) (a' k))
  have hx' : x' = ∑ k, algebraMap K E (a' k) * b k := by
    conv_lhs => rw [← B.sum_repr x']
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.smul_def, hb, ha']
    simp only
    rw [← _root_.mul_assoc, ← map_natCast (algebraMap K E), ← map_mul, div_mul_cancel₀ _ (hNK k)]
  refine ⟨Module.finrank K E, b, a, a', fun k r => ?_, hx', ?_, ha⟩
  ·
    have hr : IsIntegral ℤ (algebraMap K E (r : K)) := (RingOfIntegers.isIntegral_coe r).algebraMap
    have h := hN k (algebraMap E (Af E) ((⟨algebraMap K E (r : K), hr⟩ : 𝓞 E) : E))
      (algebraMap_integral ⟨algebraMap K E (r : K), hr⟩)
    rw [mem_lattice, map_mul]
    exact h
  ·
    have hT : (upIdele K E t : Af E) = finiteAdeleMap K E (t : Af K) := rfl
    have hkey : algebraMap E (Af E) (x - ∑ k, algebraMap K E (a k) * b k) * yi =
        -(((upIdele K E t : Af E) * algebraMap E (Af E) x' - algebraMap E (Af E) x) * yi) +
          ∑ k, finiteAdeleMap K E ((t : Af K) * algebraMap K (Af K) (a' k) - algebraMap K (Af K) (a k)) *
            algebraMap E (Af E) (b k) * yi := by
      have e2 : ∀ k, finiteAdeleMap K E ((t : Af K) * algebraMap K (Af K) (a' k) - algebraMap K (Af K) (a k)) *
            algebraMap E (Af E) (b k) * yi =
          finiteAdeleMap K E (t : Af K) * (algebraMap E (Af E) (algebraMap K E (a' k) * b k)) * yi -
            algebraMap E (Af E) (algebraMap K E (a k) * b k) * yi := fun k => by
        simp only [map_sub, map_mul, finiteAdeleMap_algebraMap]
        ring
      rw [Finset.sum_congr rfl fun k _ => e2 k, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
        ← Finset.mul_sum, ← map_sum, ← map_sum, ← hx', hT, map_sub]
      ring
    rw [mem_lattice, hkey]
    refine add_mem (neg_mem hx) (Subring.sum_mem _ fun k _ => ?_)
    exact hN k _ (finiteAdeleMap_integral (ha k))

end GlobalTheory.LatDecomp

example : ∀ (K : Type) [Field K] [NumberField K] (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (t : (Af K)ˣ) (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ → ∀ x x' : E, ((upIdele K E t : Af E) * algebraMap E (Af E) x' - algebraMap E (Af E) x) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c → ∃ (m : ℕ) (b : Fin m → E) (a a' : Fin m → K), (∀ k (r : 𝓞 K), algebraMap K E (r : K) * b k ∈ lattice c y) ∧ x' = ∑ k, algebraMap K E (a' k) * b k ∧ x - ∑ k, algebraMap K E (a k) * b k ∈ lattice c y ∧ ∀ k (v : HeightOneSpectrum (𝓞 K)), Valued.v (((t : Af K) * algebraMap K (Af K) (a' k) - algebraMap K (Af K) (a k)) v) ≤ 1 := GlobalTheory.LatDecomp.exists_decomp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftedFunctionOnLogResolution
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PairStep.LiftFn

variable {Y : Scheme.{0}}

theorem eq_of_specializes_of_coheight {v w : Y} (h : v ⤳ w) (hv : Order.coheight v = 1)
    (hw : Order.coheight w = 1) : v = w := by
  by_contra hne
  have hlt : w < v := lt_of_le_not_ge h fun e => hne (Specializes.antisymm h e).eq
  have h₃ := Order.coheight_add_one_le hlt
  rw [hv, hw] at h₃
  exact absurd h₃ (by decide)

variable [IsIntegral Y] [IsLocallyNoetherian Y]

theorem mult_neg (F : CartierDiv Y) (z : Y) : (-F).mult z = -F.mult z := by
  have e := CartierDiv.mult_add F (-F) z
  rw [add_neg_cancel, (CartierDiv.isEqn_zero (X := Y) z).mult_eq, Units.val_one, (unitAt_one z).ord_eq_zero] at e
  omega

end GlobalTheory.PairStep.LiftFn

namespace GlobalTheory.PairStep

open LiftFn in

theorem exists_lifted_fn : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (η : RatForms p n) (m : ℕ) (G N : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) (F : CartierDiv Y), IsLogRes p n η m G s K B → (∀ U : X.Opens, IsAffineOpen U → Subsingleton (cohOn (twist (GlobalTheory.structureModule Y) (toLB (pullCart s N - F))) (s ⁻¹ᵁ U) 1)) → ∀ (y : X) (σ : Y), (∀ v w : Y, v ≠ σ → v ⤳ w → σ ⤳ w → s w ⤳ y → F.mult v ≤ 0) → s σ ⤳ y → Order.coheight σ = 1 → ∃ h : Y.functionField, (-F).RegularAt σ (h - 1) ∧ ∀ v : Y, v ≠ σ → Order.coheight v = 1 → s v ⤳ y → (-F).RegularAt v h := by
  intro X _ _ p n hp _ η m G N Y _ _ s _ K B F hres hcoh y σ hF hσy hσ
  have hpr : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp).1
  have hspr : IsProper (s ≫ p) :=
    ((isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hres.proj).1
  haveI : IsProper s := IsProper.of_comp s p
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (s ≫ p)
  haveI := hres.smooth
  haveI := SmoothOfRelativeDimension.smooth n (s ≫ p)
  haveI : GlobalTheory.IsNormalScheme Y := isNormalScheme_of_smooth (s ≫ p)

  set T : Set Y := {v | v ≠ σ ∧ 0 < F.mult v} with hTdef
  have hT : T.Finite := F.finite_support_mult.subset fun v hv => hv.2.ne'
  obtain ⟨U, e, hUa, hyU, hNe, hav⟩ := GlobalTheory.T.exists_affine_nhds_avoiding_images_of_specializations X Y s T σ y N hT
    fun v hv w hvw hσw hwy => not_le.2 hv.2 (hF v w hv.1 hvw hσw hwy)
  have hTc : IsClosed (⋃ v ∈ T, closure ({v} : Set Y)) :=
    hT.isClosed_biUnion fun _ _ => isClosed_closure
  set W₁ : Y.Opens := s ⁻¹ᵁ U ⊓ ⟨_, hTc.isOpen_compl⟩ with hW₁
  set W₂ : Y.Opens := s ⁻¹ᵁ U ⊓ ⟨_, (isClosed_closure (s := ({σ} : Set Y))).isOpen_compl⟩ with hW₂
  have hW : W₁ ⊔ W₂ = s ⁻¹ᵁ U := by
    refine le_antisymm (sup_le inf_le_left inf_le_left) fun w hw => ?_
    by_cases hwσ : w ∈ closure ({σ} : Set Y)
    · refine Or.inl ⟨hw, fun hwT => ?_⟩
      obtain ⟨v, hv, hwv⟩ := Set.mem_iUnion₂.1 hwT
      exact hav v hv w (specializes_iff_mem_closure.2 hwv) (specializes_iff_mem_closure.2 hwσ) hw
    · exact Or.inr ⟨hw, hwσ⟩
  have hc := hcoh U hUa
  rw [← hW] at hc
  set e' : Y.functionFieldˣ := fnPull s e with he'
  have key : ∀ w ∈ s ⁻¹ᵁ U, ∀ f : Y.functionField,
      (pullCart s N - F).RegularAt w f ↔ (-F).RegularAt w (f * e') := by
    intro w hw f
    obtain ⟨g, hg⟩ := F.exists_isEqn w
    rw [((isEqn_pullCart s (hNe _ hw)).sub hg).regularAt_iff, hg.neg.regularAt_iff]
    have : f * ((fnPull s e / g : Y.functionFieldˣ) : Y.functionField) =
        f * (e' : Y.functionField) * ((g⁻¹ : Y.functionFieldˣ) : Y.functionField) := by
      rw [Units.val_div_eq_div_val, Units.val_inv_eq_inv_val, he']
      ring
    rw [this]
  have hinv : ∀ x ∈ W₁ ⊓ W₂, (pullCart s N - F).RegularAt x (e' : Y.functionField)⁻¹ := by
    intro x hx
    rw [key x hx.1.1, inv_mul_cancel₀ e'.ne_zero]
    have h1 := (GlobalTheory.T.regularAt_iff_forall_specializes_ord_add_mult_nonneg Y (-F) x 1).2
    rw [Units.val_one] at h1
    refine h1 fun z hzx => ?_
    rw [(unitAt_one z).ord_eq_zero, zero_add, mult_neg]
    refine neg_nonneg.2 (not_lt.1 fun hz => ?_)
    by_cases hzσ : z = σ
    · subst hzσ
      exact hx.2.2 (specializes_iff_mem_closure.1 hzx)
    · exact hx.1.2 (Set.mem_iUnion₂.2 ⟨z, ⟨hzσ, hz⟩, specializes_iff_mem_closure.1 hzx⟩)
  obtain ⟨h₁, h₂, hsplit, hh₁, hh₂⟩ :=
    GlobalTheory.T.rational_function_split_regular_divisor Y (pullCart s N - F) W₁ W₂ hc (e' : Y.functionField)⁻¹ hinv
  have hσU : σ ∈ s ⁻¹ᵁ U := hσy.mem_open U.isOpen hyU
  refine ⟨h₂ * e', ?_, fun v hvσ hv hvy => ?_⟩
  · have hσW : σ ∈ W₁ := ⟨hσU, fun hσT => by
      obtain ⟨v, hv, hσv⟩ := Set.mem_iUnion₂.1 hσT
      exact hv.1 (eq_of_specializes_of_coheight (specializes_iff_mem_closure.2 hσv)
        (CartierDiv.coheight_eq_one_of_mult_ne_zero hv.2.ne') hσ)⟩
    have e₁ : h₂ * (e' : Y.functionField) - 1 = h₁ * e' := by
      rw [show h₂ = (e' : Y.functionField)⁻¹ + h₁ by rw [hsplit]; ring, add_mul,
        inv_mul_cancel₀ e'.ne_zero]
      ring
    rw [e₁]
    exact (key σ hσU h₁).1 (hh₁ σ hσW)
  · have hvU : v ∈ s ⁻¹ᵁ U := hvy.mem_open U.isOpen hyU
    have hvW : v ∈ W₂ := ⟨hvU, fun hvσ' =>
      hvσ (eq_of_specializes_of_coheight (specializes_iff_mem_closure.2 hvσ') hσ hv).symm⟩
    exact (key v hvU h₂).1 (hh₂ v hvW)

end GlobalTheory.PairStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleExtensionGenericFibre
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.DeRham GlobalTheory.AbDual GlobalTheory.Cris GlobalTheory.CurveRootGeometry GlobalTheory.AbDatum GlobalTheory.ConjSeq
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LBExtDVR

theorem isOpenImmersion_spMap_fractionRing (R K : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] :
    IsOpenImmersion (ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap R K)) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  haveI : IsLocalization.Away ϖ K := by
    refine IsLocalization.Away.mk ϖ ?_ ?_ ?_
    · exact IsUnit.mk0 _ (by
        simpa using (IsFractionRing.injective R K).ne_iff.2 hϖ.ne_zero)
    · intro z
      obtain ⟨⟨x, y, hy⟩, h⟩ := IsLocalization.surj (nonZeroDivisors R) z
      obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
        (nonZeroDivisors.ne_zero hy) hϖ
      refine ⟨n, x * ↑u⁻¹, ?_⟩
      simp only at h
      rw [map_mul, ← h, hu, _root_.mul_assoc, ← map_mul, ← map_pow]
      congr 2
      rw [mul_right_comm, Units.mul_inv, _root_.one_mul]
    · intro x y h
      exact ⟨0, by rw [IsFractionRing.injective R K h]⟩
  exact IsOpenImmersion.of_isLocalization ϖ

theorem exists_lineBundle_extension_genericFibre : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (X Y : Scheme.{0}) (s : X ⟶ Sp R) (t : Y ⟶ Sp K) (a : Y ⟶ X), Smooth s → QuasiCompact s → IsPullback a t s (spMap (algebraMap R K)) → ∀ L : LB Y, L.IsLB → ∃ M : LB X, M.IsLB ∧ LBIso (M.pull a) L := by
  intro R K _ _ _ _ _ _ X Y s t a hs hq hpb L hL
  haveI := isOpenImmersion_spMap_fractionRing R K
  have ha : IsOpenImmersion a := MorphismProperty.of_isPullback hpb.flip this
  haveI : IsRegularRing R := inferInstance
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  have key : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧
      UniqueFactorizationMonoid (X.presheaf.stalk x) := fun x => by
    haveI : IsRegularRing (X.presheaf.stalk x) :=
      GlobalTheory.ExtendRig.isRegularRing_stalk GlobalTheory.isRegularRing_of_smooth R s x
    haveI : IsRegularLocalRing (X.presheaf.stalk x) :=
      IsRegularLocalRing.of_isRegularRing_of_isLocalRing _
    haveI : IsDomain (X.presheaf.stalk x) := ReciprocityTheory.AnForm.R.isDomain_of_isRegularLocalRing
    exact ⟨inferInstance, GlobalTheory.uniqueFactorizationMonoid_of_isRegularRing_of_isLocalRing
      GlobalTheory.exists_hasProjectiveDimensionLE_of_isRegularLocalRing
      GlobalTheory.isPrincipal_map_away_of_hasProjectiveDimensionLE _⟩
  exact GlobalTheory.exists_lineBundle_extension_of_isDomain X Y a ha (fun x => (key x).1)
    (fun x => (key x).2) L hL

end GlobalTheory.LBExtDVR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleFamilyAgreeingSmallExtensionTang
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualOpen.SmallExt

variable {S : Scheme.{0}}

theorem spMap_comp' {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem spMap_id' (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 (Sp R) := by
  simp [spMap]

theorem surjective_spMap {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (hφ : Function.Surjective φ)
    (hn : ∀ a ∈ RingHom.ker φ, IsNilpotent a) : Surjective (spMap φ) := by
  refine ⟨fun (x : PrimeSpectrum R) ↦ ?_⟩
  have : x ∈ Set.range (PrimeSpectrum.comap φ) := by
    rw [range_comap_of_surjective _ _ hφ]
    intro a ha
    obtain ⟨n, hn⟩ := hn a ha
    exact x.isPrime.mem_of_pow_mem n (by rw [hn]; exact zero_mem _)
  exact this

theorem pull_wl_comp {A X Y Z : Over S} (f : X ⟶ Y) (g : Y ⟶ Z) (c : Pic (A ⊗ Z).left) :
    CechPic.pull (A ◁ (f ≫ g)).left c = CechPic.pull (A ◁ f).left (CechPic.pull (A ◁ g).left c) := by
  rw [MonoidalCategory.whiskerLeft_comp, Over.comp_left, pull_comp]

theorem pull_wl_id {A X : Over S} (c : Pic (A ⊗ X).left) : CechPic.pull (A ◁ 𝟙 X).left c = c := by
  rw [MonoidalCategory.whiskerLeft_id, Over.id_left, pull_id]

end GlobalTheory.DualOpen.SmallExt

open GlobalTheory.DualOpen.SmallExt in

theorem GlobalTheory.DualOpen.exists_same_of_smallExt : ∀ (S : Scheme.{0}) [IsAffine S] (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (U : Over S) (M : LB (A ⊗ U).left), Fam A M → Inj A M → TanLift A M → ∀ (C : Type) [CommRing C] [IsLocalRing C] (e : C), e ∈ IsLocalRing.maximalIdeal C → (∀ a ∈ IsLocalRing.maximalIdeal C, a * e = 0) → e ≠ 0 → ∀ (s : Sp C ⟶ S) (N : LB (A ⊗ Over.mk s).left), Fam A N → ∀ u' : Over.mk s ⟶ U, Same A N M (ptMap s (Ideal.Quotient.mk (Ideal.span {e}))) (ptMap s (Ideal.Quotient.mk (Ideal.span {e})) ≫ u') → ∃ u : Over.mk s ⟶ U, Same A N M (𝟙 _) u := by
  intro S _ A _ hA U M hMf hMi hMt C _ _ e he hme hne s N hNf u' hsame
  haveI : Smooth A.hom := hA.smooth
  obtain ⟨P, _, i, p, σ, q, hpi, hσi, hqi, hσc, hσs, hM1, hM2⟩ := GlobalTheory.T.smallExtension_dualNumber_fibreProduct_affineMilnorSquare C e he hme hne
  have calc3 := (GlobalTheory.T.additiveLineBundleFamily_calculus_rules S A).2.2.1
  set k := IsLocalRing.ResidueField C
  set π : C →+* C ⧸ Ideal.span {e} := Ideal.Quotient.mk (Ideal.span {e})
  set ρ : C →+* k := IsLocalRing.residue C
  have hfi : (dnFst k).comp (dnInl k) = RingHom.id k := RingHom.ext fun x ↦ rfl
  let TC : Over S := Over.mk s
  let TP : Over S := Over.mk (spMap i ≫ s)
  let Tε : Over S := Over.mk (spMap (dnInl k) ≫ spMap ρ ≫ s)
  let Tk : Over S := Over.mk (spMap (dnFst k) ≫ spMap (dnInl k) ≫ spMap ρ ≫ s)
  let jp : TC ⟶ TP := Over.homMk (spMap p) (by
    show spMap p ≫ spMap i ≫ s = s
    rw [← Category.assoc, ← spMap_comp', hpi, spMap_id', Category.id_comp])
  let jσ : TC ⟶ TP := Over.homMk (spMap σ) (by
    show spMap σ ≫ spMap i ≫ s = s
    rw [← Category.assoc, ← spMap_comp', hσi, spMap_id', Category.id_comp])
  let jq : Tε ⟶ TP := Over.homMk (spMap q) (by
    show spMap q ≫ spMap i ≫ s = spMap (dnInl k) ≫ spMap ρ ≫ s
    rw [← Category.assoc, ← spMap_comp', hqi, spMap_comp', Category.assoc])
  let r : TP ⟶ TC := Over.homMk (spMap i) rfl
  let kε : Tk ⟶ Tε := ptMap _ (dnFst k)
  let kc : Tk ⟶ TC := Over.homMk (spMap ρ) (by
    show spMap ρ ≫ s = spMap (dnFst k) ≫ spMap (dnInl k) ≫ spMap ρ ≫ s
    rw [← Category.assoc, ← spMap_comp', hfi, spMap_id', Category.id_comp])
  let k₀ := ptMap s π
  have hjr : jp ≫ r = 𝟙 _ := Over.OverMorphism.ext (by
    show spMap p ≫ spMap i = 𝟙 _
    rw [← spMap_comp', hpi, spMap_id'])
  have hσr : jσ ≫ r = 𝟙 _ := Over.OverMorphism.ext (by
    show spMap σ ≫ spMap i = 𝟙 _
    rw [← spMap_comp', hσi, spMap_id'])
  have hsq : kε ≫ jq = kc ≫ jp := Over.OverMorphism.ext hM2.w.symm
  have hkqr : kε ≫ jq ≫ r = kc := Over.OverMorphism.ext (by
    show spMap (dnFst k) ≫ spMap q ≫ spMap i = spMap ρ
    rw [← spMap_comp' i q, hqi, spMap_comp', ← Category.assoc, ← spMap_comp', hfi, spMap_id', Category.id_comp])
  have hεs : Function.Surjective (dnFst k) := fun x ↦ ⟨TrivSqZeroExt.inl x, rfl⟩
  have hεn : ∀ a ∈ RingHom.ker (dnFst k), IsNilpotent a := by
    intro a ha
    have h0 : a.fst = 0 := ha
    refine ⟨2, ?_⟩
    ext <;> simp [pow_two, h0]
  have hπn : ∀ a ∈ RingHom.ker π, IsNilpotent a := by
    intro a ha
    rw [Ideal.mk_ker] at ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    exact ⟨2, by rw [mul_pow, sq e, hme e he, mul_zero]⟩
  have hkεs : Surjective kε.left := surjective_spMap _ hεs hεn
  have hkεc : IsClosedImmersion kε.left := IsClosedImmersion.spec_of_surjective _ hεs
  have hk₀s : Surjective k₀.left := surjective_spMap _ Ideal.Quotient.mk_surjective hπn

  set n := cls N hNf.isLB
  set m := cls M hMf.isLB
  have hd : CechPic.pull (A ◁ k₀).left (n - CechPic.pull (A ◁ u').left m) = 0 := by
    have h := (calc3 _ _ _ N M hNf.isLB hMf.isLB _ _).1 hsame
    rw [map_sub, h, pull_wl_comp, sub_self]
  obtain ⟨d', hd'p, hd'σ⟩ := GlobalTheory.T.exists_picardClass_extend_affineMilnorSquare S A TP TC TC _ jp jσ k₀ k₀ hM1 hσc hσs hk₀s _ hd
  have h3 : CechPic.pull (A ◁ kε).left (CechPic.pull (A ◁ jq).left d') = 0 := by
    rw [← pull_wl_comp, hsq, pull_wl_comp, hd'p, map_zero]
  obtain ⟨D, hD, hDc⟩ := cls_surj (CechPic.pull (A ◁ jq).left d')
  have hDf : Fam A D := GlobalTheory.T.additiveFamily_of_trivial_mod_epsilon S A hA k (spMap (dnInl k) ≫ spMap ρ ≫ s) D hD (by rw [hDc]; exact h3)
  obtain ⟨D₂, hD₂, hD₂c⟩ := cls_surj (CechPic.pull (A ◁ jq).left d' + CechPic.pull (A ◁ (jq ≫ r ≫ u')).left m)
  have hD₂f : Fam A D₂ := (GlobalTheory.T.additiveLineBundleFamily_calculus_rules S A).2.1 Tε U Tε D M hDf hMf (𝟙 _) (jq ≫ r ≫ u') D₂ hD₂
    (Or.inl (by rw [hD₂c, pull_wl_id, hDc]))
  obtain ⟨v, hv⟩ := hMt k (spMap ρ ≫ s) D₂ hD₂f (kε ≫ jq ≫ r ≫ u') ((calc3 _ _ _ D₂ M hD₂ hMf.isLB _ _).2 (by
    rw [hD₂c, map_add, h3, zero_add, pull_wl_comp kε]))
  have hv' : CechPic.pull (A ◁ jq).left d' + CechPic.pull (A ◁ (jq ≫ r ≫ u')).left m =
      CechPic.pull (A ◁ v).left m := by
    have h := (calc3 _ _ _ D₂ M hD₂ hMf.isLB _ _).1 hv
    rwa [pull_wl_id, hD₂c] at h
  have hglue : kc ≫ u' = kε ≫ v := hMi Tk _ _ ((calc3 _ _ _ M M hMf.isLB hMf.isLB _ _).2 (by
    rw [← hkqr, Category.assoc, Category.assoc, pull_wl_comp kε (jq ≫ r ≫ u'), pull_wl_comp kε v, ← hv', map_add,
      h3, zero_add]))
  obtain ⟨V, hVa, hV0, -⟩ := exists_isAffineOpen_mem_and_subset (X := U.left) (U := ⊤)
    (x := u'.left (IsLocalRing.closedPoint C)) trivial
  have hu'V : ∀ x, u'.left x ∈ V := fun x ↦
    ((IsLocalRing.specializes_closedPoint (R := C) x).map u'.left.continuous).mem_open V.isOpen hV0
  have hvV : ∀ y, v.left y ∈ V := by
    intro y
    obtain ⟨z, rfl⟩ := hkεs.surj y
    have h := congrArg (fun f ↦ f.left z) hglue
    simp only [Over.comp_left, Scheme.Hom.comp_apply] at h
    rw [← h]
    exact hu'V _
  obtain ⟨w, hw₁, hw₂⟩ := GlobalTheory.T.glue_morphisms_into_affineOpen_milnorSquare S U TP TC Tε Tk jp jq kc kε hM2 V hVa u' v hglue hu'V hvV
  have hunit := GlobalTheory.T.abelianScheme_units_lift_along_thickening S A hA Tε Tk kε (inferInstanceAs (IsAffine (Sp (DualNumber k)))) hkεc hkεs
  have hE := GlobalTheory.T.picardClass_eq_zero_affineMilnorSquare S A TP TC Tε Tk jp jq kc kε hM2 hunit
    (CechPic.pull (A ◁ w).left m - CechPic.pull (A ◁ (r ≫ u')).left m - d') (by
      rw [map_sub, map_sub, ← pull_wl_comp, ← pull_wl_comp, hw₁, ← Category.assoc, hjr, Category.id_comp, hd'p,
        sub_self, sub_zero]) (by
      rw [map_sub, map_sub, ← pull_wl_comp, ← pull_wl_comp, hw₂, ← hv', add_sub_cancel_right, sub_self])
  have hwe : CechPic.pull (A ◁ w).left m = CechPic.pull (A ◁ (r ≫ u')).left m + d' := by
    rw [sub_sub] at hE
    exact sub_eq_zero.1 hE
  refine ⟨jσ ≫ w, (calc3 _ _ _ N M hNf.isLB hMf.isLB _ _).2 ?_⟩
  rw [pull_wl_id, pull_wl_comp, hwe, map_add, ← pull_wl_comp, ← Category.assoc, hσr, Category.id_comp, hd'σ]
  exact (add_sub_cancel _ _).symm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleFrameOfSectionUnitsOnClosedFibreStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundleFrame_of_section_units_on_closedFibre : ∀ (X Y : Scheme.{0}) (β : X ⟶ Y), IsClosedMap β.base → ∀ (L : LB X), L.IsLB → ∀ (V : Y.Opens) (s : ∀ k : L.ι, Γ(X, β ⁻¹ᵁ V ⊓ L.U k)), IsSecOver L (β ⁻¹ᵁ V) s → ∀ y : Y, y ∈ V → (∀ (z : X) (k : L.ι), β z = y → z ∈ L.U k → IsUnit (gs (𝟙 X) z (β ⁻¹ᵁ V ⊓ L.U k) (s k))) → ∃ V' : Y.Opens, y ∈ V' ∧ V' ≤ V ∧ ∃ T : ∀ k : L.ι, Γ(X, β ⁻¹ᵁ V' ⊓ L.U k)ˣ, IsFrameOver L (β ⁻¹ᵁ V') T ∧ ∀ (f : X ⟶ X) (w : LB.Iso L (L.pull f)), SecCarriedOver L (β ⁻¹ᵁ V) s f w → FrameCarried L (β ⁻¹ᵁ V') T f w := by
  first | exact @GlobalTheory.Mum.exists_frame_of_isUnit_on_fibre | exact GlobalTheory.Mum.exists_frame_of_isUnit_on_fibre | (intros; apply GlobalTheory.Mum.exists_frame_of_isUnit_on_fibre <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoPullbackCommSquare
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.SquareIso

theorem lbIso_pull_further {X Y Z : Scheme.{0}} {L : LB X} {M : LB Y} {a : Y ⟶ X} (h : LBIso M (L.pull a)) (j : Z ⟶ Y)
    {a' : Z ⟶ X} (e : a' = j ≫ a) : LBIso (M.pull j) (L.pull a') :=
  LBIso.chartPull (Geo.Tor.chartPullPull M j j rfl) (Geo.Tor.chartPullSame L _ (fun _ => a) _ j fun _ => e) h

theorem iso_pull_of_square : ∀ {X Y Z Y' : Scheme.{0}} (LA' : LB X) (LA : LB Y) (L₁ : LB Z) (L₂ : LB Y') (ψ : X ⟶ Y) (φ₁ : Y ⟶ Z) (φ₂ : X ⟶ Y') (τ : Y' ⟶ Z), LA'.IsLB → LA.IsLB → L₁.IsLB → L₂.IsLB → ψ ≫ φ₁ = φ₂ ≫ τ → (∃ w : LB.Iso LA' (LA.pull ψ), w.IsGen) → (∃ w : LB.Iso LA (L₁.pull φ₁), w.IsGen) → LBIso L₂ (L₁.pull τ) → ∃ w : LB.Iso LA' (L₂.pull φ₂), w.IsGen := by
  intro X Y Z Y' LA' LA L₁ L₂ ψ φ₁ φ₂ τ hA' hA h₁ h₂ e w₁ w₂ w₃
  have a : LBIso (LA.pull ψ) (L₁.pull (φ₂ ≫ τ)) := lbIso_pull_further w₂ ψ e.symm
  have b : LBIso (L₂.pull φ₂) (L₁.pull (φ₂ ≫ τ)) := lbIso_pull_further w₃ φ₂ rfl
  exact LBIso.trans hA' (pull_isLB h₁ _) (pull_isLB h₂ _) (LBIso.trans hA' (pull_isLB hA _) (pull_isLB h₁ _) w₁ a) b.symm

end GlobalTheory.Poinc.SquareIso
end

