import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AutomorphicArithmetic.CMTraceForms.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2112
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2207
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2200
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0036
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.VtfValPullGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0955
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0093
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2193
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0363

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthOscillationLeAtTwoCmField
section
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

set_option autoImplicit false

noncomputable section

open GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification (IsBig sumSmallSpread not_isBig_iff)

namespace GlobalTheory.RefSum

theorem extendedReal_coe_finset_sum_of_real {α : Type} (s : Finset α) (g : α → ℝ) :
    ((∑ a ∈ s, g a : ℝ) : EReal) = ∑ a ∈ s, (g a : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, EReal.coe_add, ih]

theorem oscLe_two : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (F k m M : ℕ) (Mb Sm : ℝ) (cx : Lt1 Dw → ℕ), Shape Dw F k m → ExpBd Dw k cx Mb Sm M → ∀ (p : ℕ) [Fact p.Prime] (vd : ℝ), 0 ≤ vd → UpperTheory.Depth.SplitPlaces p H F vd → OscLe Xo c p cx (F * m * (1 + vd / 2) * Mb + Sm) := by
  intro E _ _ _ H Dw l Xo c F k m M Mb Sm cx hS hE p hp vd hvd hT
  classical
  intro la
  refine ⟨0, fun T io e ho y => ?_⟩
  have hfall : ∀ f : Lt1 Dw, letI := H.starRing
      (((0 : ℝ) : EReal) ≤ nuFac p y f (cx f) ∧ (y.IsAlg → nuFac p y f (cx f) ≤ ((boundAll p (rk f) (cx f) : ℝ) : EReal))) :=
    fun f => ((GlobalTheory.T.factorDepth_between_zero_and_bound E H Dw l Xo c p la f (cx f)).1 T io e ho y)
  have hnu : letI := H.starRing; nuP p y cx = ∑ f, nuFac p y f (cx f) := rfl
  refine ⟨?_, fun hy => ?_⟩
  · simp only [Nat.cast_zero, EReal.coe_zero] at hfall ⊢
    rw [hnu]
    exact Finset.sum_nonneg fun f _ => (hfall f).1
  · obtain ⟨len, hlen0, -, hlenS, hlen⟩ :=
      GlobalTheory.T.meanUpperBound_bigFactors_placeAboveTwo E H Dw l Xo c p F vd hT T io y (not_isUnit_of_overLa la ho) hy
    set b : Lt1 Dw → ℝ := fun f => if IsBig k f then (cx f : ℝ) * len f.1 else (rk f : ℝ) * cx f with hb
    have hfb : ∀ f, letI := H.starRing; nuFac p y f (cx f) ≤ ((b f : ℝ) : EReal) := by
      intro f
      by_cases hbig : IsBig k f
      · simp only [hb, if_pos hbig]
        simpa [mul_comm] using hlen f (cx f) hbig.1
      · simp only [hb, if_neg hbig]
        have := (hfall f).2 hy
        have hB : boundAll p (rk f) (cx f) ≤ (rk f : ℝ) * cx f := by
          have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.out.two_le
          unfold boundAll
          exact div_le_self (by positivity) (by linarith)
        exact this.trans (EReal.coe_le_coe_iff.2 hB)
    have hsum : letI := H.starRing; nuP p y cx ≤ ((∑ f, b f : ℝ) : EReal) := by
      rw [hnu, extendedReal_coe_finset_sum_of_real]
      exact Finset.sum_le_sum fun f _ => hfb f
    refine hsum.trans (EReal.coe_le_coe_iff.2 ?_)
    have hsplit : ∑ f, b f = (∑ f ∈ Finset.univ.filter (IsBig k), (cx f : ℝ) * len f.1) +
        ∑ f ∈ Finset.univ.filter (fun f => ¬ IsBig k f), (rk f : ℝ) * cx f := by
      simp only [hb]; rw [Finset.sum_ite]
    have hsmall : (∑ f ∈ Finset.univ.filter (fun f => ¬ IsBig k f), (rk f : ℝ) * cx f) ≤ Sm := by
      refine le_trans (le_of_eq ?_) hE.2.2.1
      unfold sumSmallSpread
      push_cast
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext f; simp [not_isBig_iff]
    have hbig : (∑ f ∈ Finset.univ.filter (IsBig k), (cx f : ℝ) * len f.1) ≤ F * m * (1 + vd / 2) * Mb := by
      have hfib := Finset.sum_fiberwise (Finset.univ.filter (IsBig k)) (fun f : Lt1 Dw => f.1)
        (fun f => (cx f : ℝ) * len f.1)
      rw [← hfib]
      have h1 : ∀ τ : E →+* ℂ, (∑ f ∈ (Finset.univ.filter (IsBig k)).filter (fun f : Lt1 Dw => f.1 = τ), (cx f : ℝ) * len f.1)
          ≤ len τ * Mb := by
        intro τ
        have hτ := hE.2.1 τ
        have : (∑ f ∈ (Finset.univ.filter (IsBig k)).filter (fun f : Lt1 Dw => f.1 = τ), (cx f : ℝ) * len f.1)
            = len τ * ∑ f ∈ Finset.univ.filter (fun f : Lt1 Dw => IsBig k f ∧ f.1 = τ), (cx f : ℝ) := by
          rw [Finset.filter_filter, Finset.mul_sum]
          refine Finset.sum_congr (by ext f; simp) fun f hf => ?_
          rw [(Finset.mem_filter.1 hf).2.2, mul_comm]
        rw [this]
        refine mul_le_mul_of_nonneg_left ?_ (hlen0 τ)
        rw [Nat.cast_sum] at hτ
        refine le_trans (le_of_eq ?_) hτ
        exact Finset.sum_congr (by ext f; simp) fun _ _ => rfl
      have hq : (Dw.q : ℝ) ≤ m := by exact_mod_cast hS.2.1
      calc _ ≤ ∑ τ : E →+* ℂ, len τ * Mb := Finset.sum_le_sum fun τ _ => h1 τ
        _ = (∑ τ, len τ) * Mb := by rw [Finset.sum_mul]
        _ ≤ (F * Dw.q * (1 + vd / 2)) * Mb := mul_le_mul_of_nonneg_right hlenS hE.1
        _ ≤ F * m * (1 + vd / 2) * Mb := by
          apply mul_le_mul_of_nonneg_right _ hE.1
          apply mul_le_mul_of_nonneg_right _ (by linarith)
          exact mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg _)
    simp only [Nat.cast_zero, zero_add]
    rw [hsplit]
    linarith

end GlobalTheory.RefSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthOscillationLeOddSplitUnramifiedPrime
section
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OscSplit

open GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification (IsBig IsSmall IsSpread sumBig sumSmallSpread not_isBig_iff)

theorem ereal_coe_sum {α : Type} (s : Finset α) (g : α → ℝ) :
    ((∑ a ∈ s, g a : ℝ) : EReal) = ∑ a ∈ s, (g a : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, EReal.coe_add, ih]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

open Classical in

theorem card_filter_inPsi (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) :
    (Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)).card = Module.finrank ℚ E / 2 := by
  rw [← GlobalTheory.LamF.card_psiSet H, ← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun τ => by
    rw [Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩)

open Classical in

theorem sumBig_le {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {F k : ℕ} {Mb : ℝ} {cx : Lt1 Dw → ℕ}
    (hF : Module.finrank ℚ E = 2 * F)
    (h : ∀ τ : E →+* ℂ, ((∑ f ∈ Finset.univ.filter (fun f : Lt1 Dw => IsBig k f ∧ f.1 = τ), cx f : ℕ) : ℝ) ≤ Mb) :
    (sumBig k cx : ℝ) ≤ F * Mb := by
  have hc : (Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)).card = F := by
    rw [card_filter_inPsi, hF]; omega
  have e : sumBig k cx = ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ),
      ∑ f ∈ Finset.univ.filter (fun f : Lt1 Dw => IsBig k f ∧ f.1 = τ), cx f := by
    unfold sumBig
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter (IsBig k))
      (t := Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)) (g := fun f : Lt1 Dw => f.1)
      (fun f hf => Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hf).2.1⟩)]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.filter_filter]
  rw [e, Nat.cast_sum]
  refine (Finset.sum_le_sum fun τ _ => h τ).trans ?_
  rw [Finset.sum_const, hc, nsmul_eq_mul]

theorem oscLe_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (F k m M : ℕ) (Mb Sm : ℝ) (cx : Lt1 Dw → ℕ), Shape Dw F k m → ExpBd Dw k cx Mb Sm M → ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ¬ (p : ℤ) ∣ discr E → SplitInK H p → OscLe Xo c p cx ((F * m * Mb + Sm) / ((p : ℝ) - 1)) := by
  intro E _ _ _ H Dw l Xo c F k m M Mb Sm cx hS hB p hp h2 hd hs la
  classical
  obtain ⟨-, hqm, -, -, -, hF⟩ := hS
  obtain ⟨hMb, hbig, hsm, -⟩ := hB
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
    linarith
  let B : Lt1 Dw → ℝ := fun f =>
    if IsBig k f then (cx f : ℝ) * (Dw.q / ((p : ℝ) - 1)) else boundAll p (rk f) (cx f)
  have hsum : ∑ f, B f ≤ (F * m * Mb + Sm) / ((p : ℝ) - 1) := by
    have e1 : ∑ f ∈ Finset.univ.filter (IsBig k), (cx f : ℝ) * (Dw.q / ((p : ℝ) - 1)) =
        (sumBig k cx : ℝ) * Dw.q / ((p : ℝ) - 1) := by
      rw [← Finset.sum_mul, mul_div_assoc, sumBig, Nat.cast_sum]
    have e2 : ∑ f ∈ Finset.univ.filter (fun f : Lt1 Dw => ¬ IsBig k f), boundAll p (rk f) (cx f) =
        (sumSmallSpread k cx : ℝ) / ((p : ℝ) - 1) := by
      rw [sumSmallSpread, Nat.cast_sum, Finset.sum_div]
      refine Finset.sum_congr (Finset.filter_congr fun f _ => not_isBig_iff k f) fun f _ => ?_
      rw [boundAll, Nat.cast_mul]
    have h1 := sumBig_le (k := k) (cx := cx) hF hbig
    have h3 : (Dw.q : ℝ) ≤ m := by exact_mod_cast hqm
    have h4 : (sumBig k cx : ℝ) * Dw.q ≤ F * Mb * m :=
      mul_le_mul h1 h3 (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hMb)
    rw [Finset.sum_ite, e1, e2, ← add_div]
    exact div_le_div_of_nonneg_right (by linarith) hp1.le
  refine ⟨0, fun T io e ho y => ?_⟩
  have hall := fun f => (GlobalTheory.T.factorDepth_between_zero_and_bound E H Dw l Xo c p la f (cx f)).1 T io e ho y
  constructor
  · rw [Nat.cast_zero, EReal.coe_zero]
    exact Finset.sum_nonneg fun f _ => (hall f).1
  · intro ha
    rw [Nat.cast_zero, zero_add]
    refine le_trans ?_ (EReal.coe_le_coe_iff.2 hsum)
    rw [ereal_coe_sum]
    refine Finset.sum_le_sum fun f _ => ?_
    by_cases hf : IsBig k f
    · simp only [B, if_pos hf]
      exact (GlobalTheory.T.factorDepth_upperBound_oddUnramifiedPrime E H Dw l Xo c p T io y (not_isUnit_of_overLa la ho) ha h2 hd f (cx f) hf.1).1 hs
    · simp only [B, if_neg hf]
      exact (hall f).2 ha

end GlobalTheory.OscSplit

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableGen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.Cl.SymFrame
open ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.PullbackSections

theorem const_of_periodic {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} (hp : (τ.map Complex.im).PosDef)
    {f : (Fin g → ℂ) → ℂ} (hf : Differentiable ℂ f) (hper : ∀ z M N, f (z + perV τ M N) = f z) (z w : Fin g → ℂ) :
    f z = f w := by
  let P : (Fin g → ℤ) × (Fin g → ℤ) →+ (Fin g → ℂ) := AddMonoidHom.mk' (fun a => perV τ a.1 a.2) fun a b => by
    have e : ∀ M N : Fin g → ℤ, cv (M + N) = cv M + cv N := fun M N => by ext i; simp [cv]
    simp only [perV, Prod.fst_add, Prod.snd_add, e, Matrix.mulVec_add]
    abel
  refine periodic_const_range P (eq_top_iff.2 fun v _ => ?_) f hf (fun z a => hper z a.1 a.2) z w
  obtain ⟨y, hy⟩ := Matrix.mulVec_surjective_iff_isUnit.2 hp.isUnit fun i => (v i).im
  let x : Fin g → ℝ := fun i => (v i).re - (τ.map Complex.re *ᵥ y) i
  have e : v = ∑ i, x i • P (Pi.single i 1, 0) + ∑ i, y i • P (0, Pi.single i 1) := by
    have c0 : cv (0 : Fin g → ℤ) = 0 := by ext i; simp [cv]
    have c1 : ∀ i : Fin g, cv (Pi.single i 1 : Fin g → ℤ) = Pi.single i 1 := fun i => by
      ext k; by_cases h : k = i <;> simp [cv, h, Pi.single_apply]
    ext k
    have hk := congrFun hy k
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply] at hk
    simp only [P, AddMonoidHom.mk'_apply, perV, c0, c1, Matrix.mulVec_zero, add_zero, zero_add, Matrix.mulVec_single_one,
      Pi.add_apply, Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
    apply Complex.ext
    · simp [x, Matrix.mulVec, dotProduct, mul_comm]
    · simp [← hk, mul_comm]
  rw [e]
  exact Submodule.add_mem _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
    (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))

theorem autV_mul_autV {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) {a b : Fin g → ℂ} (ha : Half a) (hb : Half b)
    (M N : Fin g → ℤ) (z : Fin g → ℂ) : autV τ a b M N z * autV τ a b M N (-(z + perV τ M N)) = 1 := by
  have h : ∀ {c : Fin g → ℂ}, Half c → ∀ M : Fin g → ℤ, ∃ n : ℤ, 2 * (c ⬝ᵥ cv M) = n := fun {c} hc M => by
    classical
    refine ⟨∑ i, if c i = 0 then 0 else M i, ?_⟩
    rw [dotProduct, Finset.mul_sum, Int.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases hc i with e | e <;> simp [e, cv]
  obtain ⟨m, hm⟩ := h ha M
  obtain ⟨n, hn⟩ := h hb N
  have hk : cv N ⬝ᵥ cv M = ((N ⬝ᵥ M : ℤ) : ℂ) := by simp [dotProduct, cv]
  rw [autV, autV, ← Complex.exp_add, Complex.exp_eq_one_iff]
  refine ⟨m - n + N ⬝ᵥ M, ?_⟩
  rw [dotProduct_neg, dotProduct_add, perV, dotProduct_add, hk]
  push_cast
  rw [← hm, ← hn]
  ring

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ}
  {ν : NumOf D ℂ N} {d : AB N.toNumB g}

theorem hol_base (G : Geo ν d) (U : D.P.A.left.Opens) (f : Γ(D.P.A.left, U)ˣ) :
    IsOpen {z | ⊤ ≤ (ν.eA (d.ex z)).left ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun z => valF (ν.eA (d.ex z)).left U f.val) {z | ⊤ ≤ (ν.eA (d.ex z)).left ⁻¹ᵁ U} := by
  have e : ∀ z, ptB ν d z ≫ (snd (TF (R := R) ℂ) D.P.A).left = (ν.eA (d.ex z)).left := fun z => by
    rw [ptB, ← Over.comp_left, lift_snd]
  have h := G.hol ((snd (TF (R := R) ℂ) D.P.A).left ⁻¹ᵁ U) (pullU _ U f).val
  simp only [← e]
  refine ⟨h.1, h.2.congr fun z _ => ?_⟩
  exact (vtf_val_pullU (ptB ν d z) _ U f).symm

theorem differentiable_gen (G : Geo ν d) (hr : ν.rg ≠ 0) {K : Type} [Fintype K] {φ : K → (D.P.A.left ⟶ D.P.A.left)}
    {ε : K → ℤ} (t : LB.Gen (LB.LinComb D.P.L φ ε)) (ht : t.IsGen) (w : K → (Fin g → ℂ) → (Fin g → ℂ))
    (hw : ∀ k, Differentiable ℂ (w k)) (hφ : ∀ k z, (ν.eA (d.ex z)).left ≫ φ k = (ν.eA (d.ex (w k z))).left) :
    Differentiable ℂ fun z => vF t (ν.eA (d.ex z)).left ν.J / ∏ k, ((d.fr (w k z) : ℂ) * ν.rg) ^ ε k := by
  intro z₀
  let j : K → D.P.L.ι := fun k => ν.J ((ν.eA (d.ex z₀)).left ≫ φ k)
  obtain ⟨hS, hv⟩ := hol_base G (LB.wchart D.P.L φ j) (t.s j)
  have hJ : ∀ z, ⊤ ≤ (ν.eA (d.ex z)).left ⁻¹ᵁ LB.wchart D.P.L φ fun k => ν.J ((ν.eA (d.ex z)).left ≫ φ k) :=
    fun z q _ => Set.mem_iInter.2 fun k => ν.good ((ν.eA (d.ex z)).left ≫ φ k) (x := q) trivial
  have hk : ∀ z, ⊤ ≤ (ν.eA (d.ex z)).left ⁻¹ᵁ LB.wchart D.P.L φ j → ∀ k,
      ⊤ ≤ (ν.eA (d.ex (w k z))).left ⁻¹ᵁ D.P.L.U (j k) := fun z hz k q _ => by
    rw [← hφ]
    exact Set.mem_iInter.1 (hz (x := q) trivial) k
  have hfr : ∀ z, ⊤ ≤ (ν.eA (d.ex z)).left ⁻¹ᵁ LB.wchart D.P.L φ j → ∀ k, (d.fr (w k z) : ℂ) * ν.rg =
      valF ((ν.eA (d.ex z)).left ≫ φ k) _ (D.P.L.g (ν.J ((ν.eA (d.ex z)).left ≫ φ k)) (j k)).val * G.frG (j k) (w k z) :=
    fun z hz k => by
      rw [hφ, G.fr_eq]
      exact G.fr_compat _ _ _ fun q _ => ⟨ν.good _ (x := q) trivial, hk z hz k (x := q) trivial⟩
  have hne : ∀ k z, (d.fr (w k z) : ℂ) * ν.rg ≠ 0 := fun k z => mul_ne_zero (Units.ne_zero _) hr
  have hev : (fun z => vF t (ν.eA (d.ex z)).left ν.J / ∏ k, ((d.fr (w k z) : ℂ) * ν.rg) ^ ε k) =ᶠ[nhds z₀]
      fun z => valF (ν.eA (d.ex z)).left (LB.wchart D.P.L φ j) (t.s j).val / ∏ k, G.frG (j k) (w k z) ^ ε k := by
    filter_upwards [hS.mem_nhds (hJ z₀)] with z hz
    have e : vF t (ν.eA (d.ex z)).left ν.J = (∏ k, valF ((ν.eA (d.ex z)).left ≫ φ k) _
        (D.P.L.g (ν.J ((ν.eA (d.ex z)).left ≫ φ k)) (j k)).val ^ ε k) *
        valF (ν.eA (d.ex z)).left (LB.wchart D.P.L φ j) (t.s j).val :=
      vtf_isGen_val D.P.L φ ε t ht _ _ j fun q _ => ⟨hJ z (x := q) trivial, hz (x := q) trivial⟩
    rw [e]
    simp only [hfr z hz, mul_zpow, Finset.prod_mul_distrib]
    refine mul_div_mul_left _ _ (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ ?_)
    exact left_ne_zero_of_mul (hfr z hz k ▸ hne k z)
  refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
  have h0 : ∀ k, G.frG (j k) (w k z₀) ≠ 0 := fun k => right_ne_zero_of_mul (hfr z₀ (hJ z₀) k ▸ hne k z₀)
  have h1 : ∀ k, DifferentiableAt ℂ (fun z => G.frG (j k) (w k z)) z₀ := fun k =>
    ((G.fr_hol (j k)).differentiableAt ((hol_base G _ 1).1.mem_nhds (hk z₀ (hJ z₀) k))).comp z₀ (hw k z₀)
  have h2 : DifferentiableAt ℂ (fun z => ∏ k, G.frG (j k) (w k z) ^ ε k) z₀ :=
    by
      have hp : ∀ s : Finset K, DifferentiableAt ℂ (fun z => ∏ k ∈ s, G.frG (j k) (w k z) ^ ε k) z₀ := fun s => by
        classical
        induction s using Finset.induction_on with
        | empty => simp
        | insert a s ha ih =>
          simp only [Finset.prod_insert ha]
          exact ((h1 a).zpow (Or.inl (h0 a))).mul ih
      exact hp _
  simp only [div_eq_mul_inv]
  exact (hv.differentiableAt (hS.mem_nhds (hJ z₀))).mul
    (h2.inv (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (h0 k)))

theorem rg_ne (ν : NumOf D ℂ N) : ν.rg ≠ 0 := by
  unfold NumOf.rg vF valF
  split_ifs with h
  · exact (((Units.isUnit _).map _).map _).ne_zero
  · exact (h fun q _ => Set.mem_iInter.2 fun _ => ν.good ((TF (R := R) ℂ).hom ≫ eSec D.P.A) (x := q) trivial).elim

end GlobalTheory.MBLow.Cl.SymFrame

namespace GlobalTheory.MBLow.Cl
open SymFrame

theorem sym_of_geo : AllC fun {R} _ _ {D} _ {N} ν => ∀ (g : ℕ) (d : AB N.toNumB g), Nonempty (Geo ν d) → d.Sym := by
  rintro R _ _ _ _ D - - _ N ν g d ⟨G⟩
  have hr := rg_ne ν
  have h0 : d.ex 0 = 1 := by simpa using d.ex_add 0 0
  have hneg : ∀ z, d.ex (-z) = (d.ex z)⁻¹ := fun z =>
    eq_inv_of_mul_eq_one_left (by rw [← d.ex_add, neg_add_cancel, h0])
  have hd := differentiable_gen G hr D.sym D.sym_gen ![fun z => -z, fun z => z]
    (fun k => by fin_cases k <;> simp <;> fun_prop) (fun k z => by
      fin_cases k
      · change _ ≫ (ι[D.P.A]).left = (ν.eA (d.ex (-z))).left
        rw [hneg, map_inv, Hom.inv_def, Over.comp_left]
      · exact Category.comp_id _)
  have hF : Differentiable ℂ fun z => (N.σ (d.ex z) : ℂ) * d.fr z / d.fr (-z) := by
    convert hd using 2 with z
    rw [ν.σ_eq, Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zpow_one, _root_.zpow_neg]
    have := (d.fr z).ne_zero
    have := (d.fr (-z)).ne_zero
    field_simp
  intro x
  have hc := const_of_periodic d.pos hF (fun z M M' => by
    have h1 := d.fr_per M M' z
    have h2 := d.fr_per M M' (-(z + perV d.τ M M'))
    have h3 := autV_mul_autV d.τ d.ha d.hb M M' z
    rw [show -(z + perV d.τ M M') + perV d.τ M M' = -z by abel] at h2
    rw [d.ex_add, (d.ker _).2 ⟨M, M', rfl⟩, _root_.mul_one, div_eq_div_iff (Units.ne_zero _) (Units.ne_zero _), h1, h2]
    linear_combination (-(N.σ (d.ex z) : ℂ) * d.fr (z + perV d.τ M M') * d.fr (-z)) * h3) x 0
  rw [h0, N.σ_one, neg_zero, d.fr_zero, div_eq_iff (Units.ne_zero _)] at hc
  ext
  simpa using hc

end GlobalTheory.MBLow.Cl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberSectionValueLinearCombination
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.DualLin

theorem sp_dual_subsingleton (K : Type) [Field K] : Subsingleton (Sp (DualNumber K)) := by
  have h : ∀ p : PrimeSpectrum (DualNumber K),
      p.asIdeal = IsLocalRing.maximalIdeal (DualNumber K) := by
    intro p
    refine le_antisymm (IsLocalRing.le_maximalIdeal p.isPrime.ne_top) fun x hx => ?_
    have hn : IsNilpotent x := by
      rw [TrivSqZeroExt.isNilpotent_iff_isNilpotent_fst]
      have : ¬ IsUnit x.fst := fun hu => hx (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 hu)
      have h0 : x.fst = 0 := by simpa using this
      rw [h0]; exact IsNilpotent.zero
    obtain ⟨n, hn⟩ := hn
    exact p.isPrime.mem_of_pow_mem n (hn ▸ p.asIdeal.zero_mem)
  exact ⟨fun p q => PrimeSpectrum.ext ((h p).trans (h q).symm)⟩

theorem sE_comb : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ) (β : D.X) (s : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F β) (DegPre.famε k))) (n : ℕ) (a : Fin n → F) (σF : Fin n → LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F β) (DegPre.famε k))), (∀ j, s.f j = ∑ i, DegPre.constBF D F (a i) _ * (σF i).f j) → ∀ (r : Sp (DualNumber F) ⟶ (DegPre.BF D F).left) (J : (Sp F ⟶ D.P.A.left) → D.P.L.ι), (∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ D.P.L.U (J ψ)) → r ≫ (fst (TF (R := V) F) D.P.A).left = spMap (algebraMap F (DualNumber F)) → sE s r J = ∑ i, TrivSqZeroExt.inl (a i) * sE (σF i) r J := by
  intro V _ _ D F _ _ k β s n a σF hs r J hJ hr
  have hW : ⊤ ≤ r ⁻¹ᵁ LB.wchart D.P.L (DegPre.famφ D F β)
      (fun k' => J (redE F ≫ r ≫ DegPre.famφ D F β k')) := by
    intro y _
    haveI := sp_dual_subsingleton F
    let z : Sp F := (⟨⊥, Ideal.bot_prime⟩ : PrimeSpectrum F)
    have hy : y = (redE F).base z := Subsingleton.elim _ _
    refine Set.mem_iInter.2 fun k' => ?_
    have := hJ (redE F ≫ r ≫ DegPre.famφ D F β k') (Set.mem_univ z)
    subst hy
    simpa using this
  unfold sE
  refine (congrArg (valR r _) (hs _)).trans ((GlobalTheory.ZH.CrdCalc.valR_eq r _ hW _).trans ((map_sum _ _ _).trans
    (Finset.sum_congr rfl fun i _ => (map_mul _ _ _).trans ?_)))
  congr 1
  · refine (GlobalTheory.ZH.CrdCalc.valR_eq r _ hW _).symm.trans ?_
    rw [← TrivSqZeroExt.algebraMap_eq_inl]
    exact GlobalTheory.ZH.FormCount.valR_scal (algebraMap F (DualNumber F)) r _ hr _ hW (a i)
  · exact (GlobalTheory.ZH.CrdCalc.valR_eq r _ hW _).symm

end GlobalTheory.DualLin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualPointOverOriginLiftsTangentVectorUniformised
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

namespace GlobalTheory.MBLow.Cl

theorem tangent_lift_of_pullback : ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] (D : DegPre R) (x : KeyIn ℂ)
    (φ : x.P.A.left ⟶ D.P.A.left), IsGrpPullback x.P.A D.P.A (spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) φ →
    eSec x.P.A ≫ φ = spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R))) ≫ eSec D.P.A →
    ∀ b : TE R ℂ ⟶ D.P.A, redE ℂ ≫ b.left = (DegPre.zeroF D ℂ).left →
      ∃ b' : epsR ℂ ⟶ x.P.A, IsTangent b' ∧ b'.left ≫ φ = b.left := by
  intro R _ _ _ D x φ hφ he b hb
  have hTF : (TF (R := R) ℂ).hom = spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R))) := by
    simp only [TF, Over.mk_hom, jFK, jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hw : b.left ≫ D.P.A.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫
      spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R))) := by
    rw [Over.w b, ← hTF]; rfl
  let l := hφ.1.lift b.left (spMap (algebraMap ℂ (DualNumber ℂ))) hw
  have hl1 : l ≫ φ = b.left := hφ.1.lift_fst _ _ _
  have hl2 : l ≫ x.P.A.hom = spMap (algebraMap ℂ (DualNumber ℂ)) := hφ.1.lift_snd _ _ _
  refine ⟨Over.homMk l hl2, ?_, hl1⟩
  show spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ l = eSec x.P.A
  apply hφ.1.hom_ext
  · rw [Category.assoc, hl1, he]
    change redE ℂ ≫ b.left = _
    rw [hb, DegPre.zeroF, Over.comp_left, ← hTF]
    congr 1
  · rw [Category.assoc, hl2]
    have h1 : eSec x.P.A ≫ x.P.A.hom = 𝟙 _ := by
      simp only [eSec]
      rw [Over.w η[x.P.A]]; rfl
    rw [h1]
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp (algebraMap ℂ (DualNumber ℂ)) = RingHom.id ℂ := by
      ext z; simp
    rw [this, CommRingCat.ofHom_id, Spec.map_id]; rfl

end GlobalTheory.MBLow.Cl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundedUnitSumComponentStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_boundedUnit_sum_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (Z : Comp Xo c) (ι : Type) [Fintype ι] (G : ι → WTZ E), (∀ i, Even (G i).2) → (∀ i, ∃ s t : Rul Xo c, (s ∈ GlobalTheory.AllWt.secZ Xo c (Formalism.L2.Pj.exZ Dw (G i)) ∧ t ∈ GlobalTheory.AllWt.secZ Xo c (-Formalism.L2.Pj.exZ Dw (G i)) ∧ GlobalTheory.FlatLine.idem Z * s = s ∧ GlobalTheory.FlatLine.idem Z * t = t ∧ s * t = GlobalTheory.FlatLine.idem Z ∧ (∀ σ, GoodEmb c σ → ∃ C : ℝ, ∀ z ∈ framesOn (U σ) Z, GlobalTheory.AllWt.homN (U σ) (x) (G i) s z ≤ C ∧ GlobalTheory.AllWt.homN (U σ) (x) (-(G i)) t z ≤ C)) ∧ ∃ m : ℕ, 0 < m ∧ ∀ la, ∀ v ∈ GlobalTheory.FlatLine.valOn Z la, 0 ≤ v ((m : c.F) • s) ∧ 0 ≤ v ((m : c.F) • t)) → ∀ n : ι → ℤ, ∃ s t : Rul Xo c, (s ∈ GlobalTheory.AllWt.secZ Xo c (Formalism.L2.Pj.exZ Dw (∑ i, n i • G i)) ∧ t ∈ GlobalTheory.AllWt.secZ Xo c (-Formalism.L2.Pj.exZ Dw (∑ i, n i • G i)) ∧ GlobalTheory.FlatLine.idem Z * s = s ∧ GlobalTheory.FlatLine.idem Z * t = t ∧ s * t = GlobalTheory.FlatLine.idem Z ∧ (∀ σ, GoodEmb c σ → ∃ C : ℝ, ∀ z ∈ framesOn (U σ) Z, GlobalTheory.AllWt.homN (U σ) (x) (∑ i, n i • G i) s z ≤ C ∧ GlobalTheory.AllWt.homN (U σ) (x) (-(∑ i, n i • G i)) t z ≤ C)) ∧ ∃ m : ℕ, 0 < m ∧ ∀ la, ∀ v ∈ GlobalTheory.FlatLine.valOn Z la, 0 ≤ v ((m : c.F) • s) ∧ 0 ≤ v ((m : c.F) • t) := by
  first | exact @GlobalTheory.FlatUnitProd.exists_unit_sum | exact GlobalTheory.FlatUnitProd.exists_unit_sum | (intros; apply GlobalTheory.FlatUnitProd.exists_unit_sum <;> assumption)
end

