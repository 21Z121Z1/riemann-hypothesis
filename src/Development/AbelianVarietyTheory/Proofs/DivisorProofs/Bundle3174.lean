import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3132
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0172
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3101
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqGenericPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1622
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3100
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3125
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3133
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0086
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1236
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0024
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0104
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1254
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3134
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesEvalAtNilpotentXEqCoordinateStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate : ∀ (k : Type) [CommRing k] (σ : Type) [Finite σ] (A : Type) [CommRing A] [Algebra k A], ∀ (x : σ → A) (hx : ∀ i, IsNilpotent (x i)) (i : σ), evA k x hx (X i) = x i := by
  first | exact @GlobalTheory.Katz.evA_X | exact GlobalTheory.Katz.evA_X | (intros; apply GlobalTheory.Katz.evA_X <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFormulaArithmeticCurveRationalFunction
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CurveProd

theorem product_formula_curve : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsArithVar q 0 → ∀ f : Y.functionField, f ≠ 0 → ∑ᶠ z, (Scheme.ord f z : ℝ) * Real.log (Nat.card (Y.residueField z)) = ∑ᶠ σ : k →+* ℂ, ∑ᶠ y : CxPts q σ, Real.log ‖ratVal f y‖ := by
  intro k _ Y _ _ q hq f hf
  obtain ⟨hAff, hFin⟩ := GlobalTheory.T.arithmeticCurve_isAffine_and_finite_int k Y q hq
  have := hAff
  have := hFin
  have : Module.Finite ℤ k := hq.finite
  have hgen : genericPoint Y ∈ (⊤ : Y.Opens) := trivial
  have : Nonempty (⊤ : Y.Opens) := ⟨⟨genericPoint Y, trivial⟩⟩
  have : CharZero Γ(Y, ⊤) := (flat_int_iff_charZero (q ≫ spMap (Int.castRingHom k))).1 hq.flat
  have : IsFractionRing Γ(Y, ⊤) Y.functionField :=
    functionField_isFractionRing_of_isAffineOpen Y ⊤ (isAffineOpen_top Y)

  have finHom : ∀ (B : Type) [CommRing B] [Module.Finite ℤ B], Finite (B →+* ℂ) := by
    intro B _ _
    obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ) (M := B)
    have hint : ∀ x : B, IsIntegral ℤ x := fun x => Algebra.IsIntegral.isIntegral x
    choose p hpm hp using hint
    let T : Set (s → ℂ) :=
      Set.pi Set.univ fun x => {z : ℂ | ((p x).map (Int.castRingHom ℂ)).IsRoot z}
    have hT : T.Finite :=
      Set.Finite.pi fun x => Polynomial.finite_setOfPred_isRoot ((hpm x).map _).ne_zero
    have hmem : ∀ φ : B →+* ℂ, (fun x : s => φ x) ∈ T := by
      intro φ x _
      show Polynomial.eval (φ (x : B)) ((p x).map (Int.castRingHom ℂ)) = 0
      rw [Polynomial.eval_map]
      rw [← show φ.comp (algebraMap ℤ B) = Int.castRingHom ℂ from RingHom.ext_int _ _,
        ← Polynomial.hom_eval₂, hp x, map_zero]
    let F : (B →+* ℂ) → T := fun φ => ⟨fun x => φ x, hmem φ⟩
    have hF : Function.Injective F := by
      intro φ ψ h
      have h' : Set.EqOn φ.toAddMonoidHom.toIntLinearMap ψ.toAddMonoidHom.toIntLinearMap (s : Set B) := by
        intro x hx
        have := congrArg (fun t : T => t.1 ⟨x, hx⟩) h
        simpa [F] using this
      have hl := LinearMap.ext_on hs h'
      ext x
      exact LinearMap.congr_fun hl x
    have : Finite T := hT.to_subtype
    exact Finite.of_injective F hF

  have finZero : ∀ c : Γ(Y, ⊤), Finite (Γ(Y, ⊤) ⧸ Ideal.span {c}) →
      {z : Y | z ∉ Y.basicOpen c}.Finite := by
    intro c _
    have hS : (Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {c})))).Finite :=
      Set.finite_range _
    refine (hS.preimage fun _ _ _ _ h => Y.toSpecΓ.isOpenEmbedding.injective h).subset ?_
    intro z hz
    have h1 : Y.toSpecΓ z ∉ PrimeSpectrum.basicOpen c := by
      intro h
      apply hz
      rw [← Scheme.toSpecΓ_preimage_basicOpen]
      exact h
    show Y.toSpecΓ z ∈ Set.range _
    apply (Set.ext_iff.1 (range_comap_of_surjective _ (Ideal.Quotient.mk (Ideal.span {c}))
      Ideal.Quotient.mk_surjective) _).2
    have h2 : c ∈ (Y.toSpecΓ z).asIdeal := by
      by_contra h
      exact h1 h
    rw [Ideal.mk_ker, PrimeSpectrum.zeroLocus_span]
    exact Set.singleton_subset_iff.2 h2

  have hgb : ∀ c : Γ(Y, ⊤), c ≠ 0 → genericPoint Y ∈ Y.basicOpen c := by
    intro c hc
    by_contra h
    apply hc
    rw [← basicOpen_eq_bot_iff (X := Y) (U := ⊤) c, ← TopologicalSpace.Opens.not_nonempty_iff_eq_bot]
    rintro ⟨x, hx⟩
    exact h (gen_mem hx)

  have hsupp : ∀ c : Γ(Y, ⊤), c ≠ 0 → (Function.support fun z =>
      (Scheme.ord (algebraMap Γ(Y, ⊤) Y.functionField c) z : ℝ) *
        Real.log (Nat.card (Y.residueField z))).Finite := by
    intro c hc
    refine (finZero c (GlobalTheory.T.log_card_quot_span_eq_finsum_log_norm_embeddings Γ(Y, ⊤) c hc).1).subset ?_
    intro z hz hzc
    apply hz
    have hu : UnitAt z (algebraMap Γ(Y, ⊤) Y.functionField c) :=
      (unitAt_fnOf_iff (U := ⊤) trivial hgen c).2 hzc
    simp only
    rw [hu.ord_eq_zero]
    simp

  have key : ∀ c : Γ(Y, ⊤), c ≠ 0 →
      ∑ᶠ z, (Scheme.ord (algebraMap Γ(Y, ⊤) Y.functionField c) z : ℝ) *
          Real.log (Nat.card (Y.residueField z)) =
        ∑ᶠ σ : k →+* ℂ, ∑ᶠ y : CxPts q σ,
          Real.log ‖ratVal (algebraMap Γ(Y, ⊤) Y.functionField c) y‖ := by
    intro c hc
    obtain ⟨hfq, hlog⟩ := GlobalTheory.T.log_card_quot_span_eq_finsum_log_norm_embeddings Γ(Y, ⊤) c hc
    have := hfq
    rw [GlobalTheory.T.affineArithmeticCurve_finsum_ord_log_eq_localLengths k Y q hq c hc, ← GlobalTheory.T.log_card_eq_finsum_length_localized_maximal Γ(Y, ⊤) (Γ(Y, ⊤) ⧸ Ideal.span {c}), hlog,
      GlobalTheory.T.affineArithmeticCurve_sum_complexPoints_log_eq_ringHoms k Y q hq c]

  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective Γ(Y, ⊤) f
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hf
  have hinj := IsFractionRing.injective Γ(Y, ⊤) Y.functionField
  have ha'0 : algebraMap Γ(Y, ⊤) Y.functionField a ≠ 0 := (map_ne_zero_iff _ hinj).2 ha0
  have hb'0 : algebraMap Γ(Y, ⊤) Y.functionField b ≠ 0 := (map_ne_zero_iff _ hinj).2 hb0
  have hord : ∀ z, Scheme.ord (algebraMap Γ(Y, ⊤) Y.functionField a /
      algebraMap Γ(Y, ⊤) Y.functionField b) z =
        Scheme.ord (algebraMap Γ(Y, ⊤) Y.functionField a) z -
          Scheme.ord (algebraMap Γ(Y, ⊤) Y.functionField b) z := by
    intro z
    have h := Scheme.ord_mul (x := z) (div_ne_zero ha'0 hb'0) hb'0
    rw [div_mul_cancel₀ _ hb'0] at h
    omega

  have hpt : ∀ (σ : k →+* ℂ) (y : CxPts q σ),
      Real.log ‖ratVal (algebraMap Γ(Y, ⊤) Y.functionField a /
        algebraMap Γ(Y, ⊤) Y.functionField b) y‖ =
        Real.log ‖ratVal (algebraMap Γ(Y, ⊤) Y.functionField a) y‖ -
          Real.log ‖ratVal (algebraMap Γ(Y, ⊤) Y.functionField b) y‖ := by
    intro σ y
    have hg : under y = genericPoint Y := GlobalTheory.TwistTop.under_eq_genericPoint hq y
    have hua : UnitAt (under y) (algebraMap Γ(Y, ⊤) Y.functionField a) := by
      rw [hg]
      exact (unitAt_fnOf_iff (U := ⊤) hgen hgen a).2 (hgb a ha0)
    have hub : UnitAt (under y) (algebraMap Γ(Y, ⊤) Y.functionField b) := by
      rw [hg]
      exact (unitAt_fnOf_iff (U := ⊤) hgen hgen b).2 (hgb b hb0)
    have huq : UnitAt (under y) (algebraMap Γ(Y, ⊤) Y.functionField a /
        algebraMap Γ(Y, ⊤) Y.functionField b) := by
      rw [div_eq_mul_inv]
      exact hua.mul hub.inv
    have hm : ratVal (algebraMap Γ(Y, ⊤) Y.functionField a) y =
        ratVal (algebraMap Γ(Y, ⊤) Y.functionField a / algebraMap Γ(Y, ⊤) Y.functionField b) y *
          ratVal (algebraMap Γ(Y, ⊤) Y.functionField b) y := by
      rw [← ratVal_mul huq.regAt hub.regAt, div_mul_cancel₀ _ hb'0]
    rw [hm, norm_mul, Real.log_mul (norm_ne_zero_iff.2 (ratVal_ne_zero huq))
      (norm_ne_zero_iff.2 (ratVal_ne_zero hub))]
    ring
  have hL : ∑ᶠ z, (Scheme.ord (algebraMap Γ(Y, ⊤) Y.functionField a /
      algebraMap Γ(Y, ⊤) Y.functionField b) z : ℝ) * Real.log (Nat.card (Y.residueField z)) =
      (∑ᶠ z, (Scheme.ord (algebraMap Γ(Y, ⊤) Y.functionField a) z : ℝ) *
          Real.log (Nat.card (Y.residueField z))) -
        ∑ᶠ z, (Scheme.ord (algebraMap Γ(Y, ⊤) Y.functionField b) z : ℝ) *
          Real.log (Nat.card (Y.residueField z)) := by
    rw [← finsum_sub_distrib (hsupp a ha0) (hsupp b hb0)]
    refine finsum_congr fun z => ?_
    rw [hord z]
    push_cast
    ring
  have hR : ∑ᶠ σ : k →+* ℂ, ∑ᶠ y : CxPts q σ, Real.log ‖ratVal (algebraMap Γ(Y, ⊤) Y.functionField a /
      algebraMap Γ(Y, ⊤) Y.functionField b) y‖ =
      (∑ᶠ σ : k →+* ℂ, ∑ᶠ y : CxPts q σ, Real.log ‖ratVal (algebraMap Γ(Y, ⊤) Y.functionField a) y‖) -
        ∑ᶠ σ : k →+* ℂ, ∑ᶠ y : CxPts q σ,
          Real.log ‖ratVal (algebraMap Γ(Y, ⊤) Y.functionField b) y‖ := by
    have : Finite (k →+* ℂ) := finHom k
    rw [← finsum_sub_distrib (Set.toFinite _) (Set.toFinite _)]
    refine finsum_congr fun σ => ?_
    have := GlobalTheory.ArchDimZero.finite_cxPts hq σ
    rw [← finsum_sub_distrib (Set.toFinite _) (Set.toFinite _)]
    exact finsum_congr fun y => hpt σ y
  rw [hL, hR, key a ha0, key b hb0]

end GlobalTheory.CurveProd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjArithCharZeroFunctionFieldInjectiveConstants
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory

theorem isArithVar_charZero_functionField_and_injective :
    ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
      IsArithVar p D → CharZero X.functionField ∧ Function.Injective (GlobalTheory.toFunctionField p) := by
  intro k _ X _ p D h
  have hΓ : CharZero Γ(X, ⊤) := h.charZero
  have hg : Function.Injective (X.presheaf.germ ⊤ (genericPoint X) trivial).hom :=
    germ_injective_of_isIntegral X _ _
  have hK : CharZero X.functionField := (RingHom.charZero_iff hg).1 hΓ
  refine ⟨hK, ?_⟩
  have := h.isDomain
  have := h.finite
  have hint : Algebra.IsIntegral ℤ k := inferInstance
  rw [injective_iff_map_eq_zero]
  intro a ha
  have hker : RingHom.ker (GlobalTheory.toFunctionField p) = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
    rw [eq_bot_iff]
    intro n hn
    rw [Ideal.mem_comap, RingHom.mem_ker, algebraMap_int_eq, eq_intCast, map_intCast, Int.cast_eq_zero] at hn
    simp [hn]
  have : a ∈ RingHom.ker (GlobalTheory.toFunctionField p) := ha
  rw [hker] at this
  exact this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjArithFunctionFieldCharZeroTrdeg
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.ArithFnField

theorem charZero_and_trdeg_functionField : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
    CharZero X.functionField ∧ Algebra.trdeg ℤ X.functionField = D := by
  intro k _ X _ p D h
  refine ⟨?_, ArithTrdeg.trdeg_functionField_eq h⟩
  have hc0 : CharZero Γ(X, ⊤) := (flat_int_iff_charZero _).1 h.flat
  exact ((X.germToFunctionField ⊤).hom.charZero_iff (X.germToFunctionField_injective ⊤)).1 hc0

end GlobalTheory.ArithFnField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjArithResidueCharFibreStructure
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.IntFib

section Dim

variable {S : Type} [TopologicalSpace S]

theorem dim_le_of_ne_univ [IrreducibleSpace S] {C : Set S} (hC : IsClosed C) (hne : C ≠ Set.univ) {D : ℕ}
    (hS : topologicalKrullDim S ≤ ((D + 1 : ℕ) : WithBot ℕ∞)) : topologicalKrullDim C ≤ D := by
  unfold topologicalKrullDim at *
  refine iSup_le fun q => ?_
  let f := IrreducibleCloseds.map (Subtype.val : C → S) continuous_subtype_val
  have hf : StrictMono f := IrreducibleCloseds.map_strictMono_of_isInducing Topology.IsInducing.subtypeVal
  let q' := q.map f hf
  let top : IrreducibleCloseds S := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ S, isClosed_univ⟩
  have hlt : q'.last < top := by
    have hsub : (q'.last : Set S) ⊆ C := by
      show closure (Subtype.val '' (q.last : Set C)) ⊆ C
      exact closure_minimal (by rintro _ ⟨t, -, rfl⟩; exact t.2) hC
    refine lt_of_le_of_ne (fun x _ => Set.mem_univ x) fun heq => hne ?_
    refine Set.eq_univ_of_univ_subset fun x _ => hsub ?_
    rw [heq]
    exact Set.mem_univ x
  have h1 := Order.LTSeries.length_le_krullDim (q'.snoc top hlt)
  have h2 : ((q.length + 1 : ℕ) : WithBot ℕ∞) ≤ ((D + 1 : ℕ) : WithBot ℕ∞) := by
    simpa [q'] using h1.trans hS
  have h3 : q.length + 1 ≤ D + 1 := by exact_mod_cast h2
  exact_mod_cast (by omega : q.length ≤ D)

theorem dim_le_of_closedPoint_notMem [T0Space S] [CompactSpace S] {T : Set S}
    (hT : ∀ s : S, IsClosed ({s} : Set S) → s ∉ T) {D : ℕ}
    (hS : topologicalKrullDim S ≤ ((D + 1 : ℕ) : WithBot ℕ∞)) : topologicalKrullDim T ≤ D := by
  unfold topologicalKrullDim at *
  refine iSup_le fun q => ?_
  let f := IrreducibleCloseds.map (Subtype.val : T → S) continuous_subtype_val
  have hf : StrictMono f := IrreducibleCloseds.map_strictMono_of_isInducing Topology.IsInducing.subtypeVal
  let q' := q.map f hf
  obtain ⟨t, ht⟩ := q.head.isIrreducible.nonempty
  have htm : (t : S) ∈ (q'.head : Set S) := subset_closure ⟨t, ht, rfl⟩
  obtain ⟨s, hs, hsc⟩ := q'.head.isClosed.exists_closed_singleton ⟨_, htm⟩
  let bot : IrreducibleCloseds S := ⟨{s}, isIrreducible_singleton, hsc⟩
  have hlt : bot < q'.head := by
    refine lt_of_le_of_ne (fun x hx => (Set.mem_singleton_iff.1 hx) ▸ hs) fun heq => ?_
    have : (t : S) ∈ (bot : Set S) := by rw [heq]; exact htm
    have hts : (t : S) = s := this
    exact hT s hsc (hts ▸ t.2)
  have h1 := Order.LTSeries.length_le_krullDim (q'.cons bot hlt)
  have h2 : ((q.length + 1 : ℕ) : WithBot ℕ∞) ≤ ((D + 1 : ℕ) : WithBot ℕ∞) := by
    simpa [q'] using h1.trans hS
  have h3 : q.length + 1 ≤ D + 1 := by exact_mod_cast h2
  exact_mod_cast (by omega : q.length ≤ D)

end Dim

variable {X : Scheme.{0}}

theorem ringChar_eq_zero_or_prime (x : X) :
    ringChar (X.residueField x) = 0 ∨ (ringChar (X.residueField x)).Prime :=
  (CharP.char_is_prime_or_zero (X.residueField x) _).symm

theorem natCast_eq_zero_iff (ℓ : ℕ) (x : X) :
    (ℓ : X.residueField x) = 0 ↔ x ∉ X.basicOpen ((ℓ : ℕ) : Γ(X, ⊤)) := by
  rw [← Scheme.evaluation_eq_zero_iff_notMem_basicOpen X x (show x ∈ (⊤ : X.Opens) from trivial)]
  simp

theorem notMem_basicOpen_of_mem_fib {ℓ : ℕ} {x : X} (hx : x ∈ fib X ℓ) :
    x ∉ X.basicOpen ((ℓ : ℕ) : Γ(X, ⊤)) := by
  rw [← natCast_eq_zero_iff, ringChar.spec]
  exact (show ringChar (X.residueField x) = ℓ from hx) ▸ dvd_refl _

theorem mem_fib_iff_of_prime {ℓ : ℕ} (hℓ : ℓ.Prime) (x : X) :
    x ∈ fib X ℓ ↔ x ∉ X.basicOpen ((ℓ : ℕ) : Γ(X, ⊤)) := by
  refine ⟨notMem_basicOpen_of_mem_fib, fun h => ?_⟩
  rw [← natCast_eq_zero_iff, ringChar.spec] at h
  rcases hℓ.eq_one_or_self_of_dvd _ h with h1 | h1
  · have h2 : ((1 : ℕ) : X.residueField x) = 0 := (ringChar.spec _ 1).2 (by rw [h1])
    simp at h2
  · exact h1

theorem isClosed_fib {ℓ : ℕ} (hℓ : ℓ ≠ 0) : IsClosed (fib X ℓ) := by
  by_cases hp : ℓ.Prime
  · have e : fib X ℓ = ((X.basicOpen ((ℓ : ℕ) : Γ(X, ⊤)) : Set X))ᶜ :=
      Set.ext fun x => mem_fib_iff_of_prime hp x
    rw [e]
    exact (X.basicOpen _).isOpen.isClosed_compl
  · have e : fib X ℓ = ∅ := Set.eq_empty_iff_forall_notMem.2 fun x hx => by
      have hx' : ringChar (X.residueField x) = ℓ := hx
      rcases ringChar_eq_zero_or_prime x with h | h
      · exact hℓ (hx'.symm.trans h)
      · exact hp (hx' ▸ h)
    rw [e]
    exact isClosed_empty

theorem mem_fib_zero_of_specializes {x y : X} (h : x ⤳ y) (hy : y ∈ fib X 0) : x ∈ fib X 0 := by
  rcases ringChar_eq_zero_or_prime x with h0 | hp
  · exact h0
  · have hx : x ∈ fib X (ringChar (X.residueField x)) := rfl
    have hy' : ringChar (X.residueField y) = ringChar (X.residueField x) :=
      h.mem_closed (isClosed_fib hp.ne_zero) hx
    exact absurd (hy'.symm.trans hy) hp.ne_zero

variable {k : Type} [CommRing k] {p : X ⟶ Sp k} {D : ℕ}

theorem fib_ne_univ [IsIntegral X] (hX : IsArithVar p D) {ℓ : ℕ} (hℓ : ℓ ≠ 0) : fib X ℓ ≠ Set.univ := by
  intro h
  have hb : X.basicOpen ((ℓ : ℕ) : Γ(X, ⊤)) = ⊥ :=
    eq_bot_iff.2 fun x hx => (notMem_basicOpen_of_mem_fib (h.symm ▸ Set.mem_univ x : x ∈ fib X ℓ) hx).elim
  have h0 := (AlgebraicGeometry.basicOpen_eq_bot_iff _).1 hb
  have := hX.charZero
  exact hℓ (Nat.cast_eq_zero.1 h0)

theorem closedPoint_notMem_fib_zero (hX : IsArithVar p D) (x : X) (hx : IsClosed ({x} : Set X)) :
    x ∉ fib X 0 := by
  intro h0
  have := hX.finite_residueField hx
  exact CharP.char_ne_zero_of_finite (X.residueField x) (ringChar (X.residueField x)) h0

theorem fib_structure : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → (∀ x : X, x ∈ fib X 0 ∨ ∃ ℓ : ℕ, ℓ.Prime ∧ x ∈ fib X ℓ) ∧
      (∀ ℓ : ℕ, ℓ ≠ 0 → IsClosed (fib X ℓ)) ∧ (∀ x y : X, x ⤳ y → y ∈ fib X 0 → x ∈ fib X 0) ∧
      (∀ ℓ : ℕ, topologicalKrullDim (fib X ℓ) ≤ D) ∧
      ∀ W : Set X, IsClosed W → ∃ S : Finset ℕ, (∀ ℓ ∈ S, ℓ.Prime) ∧
        W ⊆ closure (W ∩ fib X 0) ∪ ⋃ ℓ ∈ S, fib X ℓ := by
  intro k _ X _ p D hX
  have := hX.isNoetherian
  refine ⟨fun x => ?_, fun ℓ hℓ => isClosed_fib hℓ, fun x y h hy => mem_fib_zero_of_specializes h hy,
    fun ℓ => ?_, fun W hW => ?_⟩
  · rcases ringChar_eq_zero_or_prime x with h | h
    · exact .inl h
    · exact .inr ⟨_, h, rfl⟩
  · rcases eq_or_ne ℓ 0 with rfl | hℓ
    · exact dim_le_of_closedPoint_notMem (fun s hs => closedPoint_notMem_fib_zero hX s hs) hX.dim_eq.le
    · exact dim_le_of_ne_univ (isClosed_fib hℓ) (fib_ne_univ hX hℓ) hX.dim_eq.le
  · classical
    obtain ⟨T, hTf, hTc, hTi, rfl⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hW
    let ch : Set X → ℕ := fun t =>
      if h : IsIrreducible t then ringChar (X.residueField (IsIrreducible.genericPoint h)) else 0
    refine ⟨(hTf.toFinset.image ch).filter Nat.Prime, fun ℓ hℓ => (Finset.mem_filter.1 hℓ).2, ?_⟩
    rintro x ⟨t, ht, hxt⟩
    have hct : ch t = ringChar (X.residueField (IsIrreducible.genericPoint (hTi t ht))) := dif_pos (hTi t ht)
    have hg := IsIrreducible.isGenericPoint_genericPoint (hTi t ht) (hTc t ht)
    have hsp := hg.specializes hxt
    rcases ringChar_eq_zero_or_prime (IsIrreducible.genericPoint (hTi t ht)) with h0 | hp
    · left
      exact hsp.mem_closed isClosed_closure (subset_closure ⟨⟨t, ht, hg.mem⟩, h0⟩)
    · right
      refine Set.mem_iUnion₂.2 ⟨ch t, Finset.mem_filter.2
        ⟨Finset.mem_image.2 ⟨t, hTf.mem_toFinset.2 ht, rfl⟩, hct ▸ hp⟩, ?_⟩
      exact hsp.mem_closed (isClosed_fib (hct ▸ hp.ne_zero)) hct.symm

end GlobalTheory.IntFib
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullGramFlagCellFrameStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullGram_flagCell_frame : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ (c : AlgChart X.str σ X.dim) (A : Mat m X.Fn) (u : Cell m → Y.Fn), ∀ H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ, IsMetricOn E ⊤ H → ∀ z : CxPts Y.str σ, InCell E E' φ f A u (under z) → pullGram E H φ f hf (upM u * A.map φ) z = fun τ => upM (fun j => ratVal (u j) z) τ * H A (ptMap σ f hf z) τ * (upM (fun j => ratVal (u j) z) τ)ᴴ := by
  first | exact @GlobalTheory.FlagCell2.pullGram_cell | exact GlobalTheory.FlagCell2.pullGram_cell | (intros; apply GlobalTheory.FlagCell2.pullGram_cell <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackIsoBaseChangeOverReducedClosedFibreStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_iso_baseChange_over_reduced_closedFibre : ∀ (R : Type) [CommRing R] [IsLocalRing R] (S : Scheme.{0}) (π : S ⟶ Sp R) (G' : Over S) [GrpObj G'], Smooth G'.hom → ∀ (E : Emb π G') (T : Scheme.{0}) (t : T ⟶ S) (k : T ⟶ Sp (ResidueField R)), IsLocallyNoetherian T → IsReduced T → t ≫ π = k ≫ spMap (residue R) → ∃ (e : pullback G'.hom t ≅ pullback E.Y.hom k) (l : pullback G'.hom t ⟶ E.H.toScheme), e.hom ≫ pullback.snd _ _ = pullback.snd _ _ ∧ l ≫ E.H.ι = pullback.fst _ _ ∧ l ≫ E.f = e.hom ≫ pullback.fst _ _ ≫ E.j := by
  first | exact @GlobalTheory.Mum.Emb.pullback_iso_of_closed | exact GlobalTheory.Mum.Emb.pullback_iso_of_closed | (intros; apply GlobalTheory.Mum.Emb.pullback_iso_of_closed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticCharacterTrivialUnitIdelesStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadratic_character_trivial_unit_ideles : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ b : Neutral.B1.Ideles (maximalRealSubfield E),
    b ∈ GlobalTheory.Mem.Chr.unitIdl (maximalRealSubfield E) → (GlobalTheory.GalOfCusp.quadChar E).1 (GlobalTheory.Mem.Chr.finPartI _ b) = 1 := by
  first | exact @GlobalTheory.EtaFinUnit.quadChar_finPartI_eq_one | exact GlobalTheory.EtaFinUnit.quadChar_finPartI_eq_one | (intros; apply GlobalTheory.EtaFinUnit.quadChar_finPartI_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiPeriodNormalisedJetModularTransformStatement
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiPeriod_normalised_jet_modular_transform : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) (L : Lat F), 1 ≤ s → 0 < N → HasLevel N L → ∀ (κ : Emb F → ℕ) (γ : SL(2, ℤ)) (Ch Ch' : ℍ → ℂ) (τ : ℍ), (∃ L', HasLevel N L' ∧ L' = mulMat L (γ : Matrix (Fin 2) (Fin 2) ℤ)) → Ch (γ • τ) = (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) : ℂ) ^ 2 * Ch' τ - ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) / (2 * Real.pi * Complex.I) → hfun (2 * s) L κ Ch (γ • τ) = (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) : ℂ) ^ wt (2 * s) κ * hfun (2 * s) (mulMat L (γ : Matrix (Fin 2) (Fin 2) ℤ)) κ Ch' τ := by
  first | exact @GlobalTheory.HilbFam.hfun_slash | exact GlobalTheory.HilbFam.hfun_slash | (intros; apply GlobalTheory.HilbFam.hfun_slash <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankLeFinrankOfInjectiveModPrimePosDefFormStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_le_finrank_of_injective_mod_prime_posDef_form : ∀ (l : ℕ) [Fact l.Prime] (H T : Type) [AddCommGroup H] [AddCommGroup T] [Module ℤ_[l] T] [Module.Finite ℤ_[l] T] [Module.Free ℤ_[l] T] (Q : H → ℤ), (∀ f g, Q (f + g) + Q (f - g) = 2 * Q f + 2 * Q g) → (∀ f, 0 ≤ Q f) → (∀ f, Q f = 0 → f = 0) → ∀ φ : H →+ T, (∀ (h : H) (t : T), φ h = (l : ℤ_[l]) • t → ∃ h' : H, h = l • h') → ∀ (n : ℕ) (u : Fin n → H), LinearIndependent ℤ u → n ≤ Module.finrank ℤ_[l] T := by
  first | (exact @GlobalTheory.rank_le_finrank_of_injective_mod_prime) | (exact GlobalTheory.rank_le_finrank_of_injective_mod_prime) | (intros; apply GlobalTheory.rank_le_finrank_of_injective_mod_prime  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinementIsFactorBaseChangeCanonicalMumfordFamiStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.refinement_isFactor_baseChange_canonicalMumfordFamily : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (Q : Data R) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsSemiAbelian G → Canon Q G P → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), IsCN R' → Function.Injective ρ → ρ.Finite → ∀ (D : DegData R' (maximalIdeal R')) (ε : D.toPre.X ≃+ Q.X), Refines Q ρ D.toPre ε → ∃ (D' : DegData R' (maximalIdeal R')) (F : Factor D.toPre D'.toPre) (_ : F.Alg) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) (_ : GrpObj G') (_ : IsCommMonObj G') (U' : Unif (maximalIdeal R') D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O) (G₁ : Over (Sp R')) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (inc : G₁ ⟶ G') (pr : G' ⟶ G₁) (π : G₁.left ⟶ G.left) (π₂ : (G2 G₁).left ⟶ (G2 G).left), IsSemiAbelian G' ∧ U'.toUnifPre.OLinear F.O F.o oA oG ∧ IsSemiAbelian G₁ ∧ IsMonHom inc ∧ IsMonHom pr ∧ inc ≫ pr = 𝟙 G₁ ∧ pr ≫ inc = oG.act F.e ∧ IsGrpPullback G₁ G (spMap ρ) π ∧ IsSquare π π₂ ∧ LBIso ((abelian₂ G' U'.LG.L).pull (lift (fst G₁ G₁ ≫ inc) (snd G₁ G₁ ≫ inc ≫ oG.act F.f) : G2 G₁ ⟶ G2 G').left) (P.pull π₂) := by
  first | exact @GlobalTheory.MumBC.refine_factor_baseChange | exact GlobalTheory.MumBC.refine_factor_baseChange | (intros; apply GlobalTheory.MumBC.refine_factor_baseChange <;> assumption)
end

