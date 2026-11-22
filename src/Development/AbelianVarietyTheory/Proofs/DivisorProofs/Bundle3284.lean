import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3269
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2135
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3264
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3205
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3121
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2192
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2244
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2661
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3270
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3250
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecBaseChangeOfPerf
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FinrankOfIsSecBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2569
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3261
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2782
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2856
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2787
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3192
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2643
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3271
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2580
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0084
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudeActionAdelicLattice
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowEqPowOfModEqSim

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealDatumNormalizedRationalBaseStatement
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_datum_normalized_rational_base : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.SeriesRatS → AtTw fun Fm x hx i p w j => ∀ (ρ : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (ν : ℂ),
  RealPin p.R p.cG ρ → ρ.LevelOf (Fm.D x i).nexp →
  IsNorm p.R p.v₀ (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν →
  RatBase (rdAt p w j hρ ν) →
  ∀ s h P, ρ.IsDatum ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) s h P →
    P ∈ ρ.lat ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) (smallInt (Fm.D x i)) h →
    ∀ τ : ℂ ≃+* ℂ, (∀ y, τ (Formalism.L2.Host.embLL0 (Fm.D x i) y) = Formalism.L2.Host.embLL0 (Fm.D x i) y) →
      ∃ c : ℂ, (∃ m : ℕ, m ≠ 0 ∧ c ^ m = 1) ∧
        ∃ (n : ℕ) (b : Fin n → ℂ) (g : Fin n → NX.FmK p.Sx ((j : ℕ) + 1)),
          ν • ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P = ∑ k, b k • evW p.nexp p.v₀ j (g k).val ∧
          ∑ k, τ (b k) • evW p.nexp p.v₀ j (g k).val =
            c • (ν • ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P) := by
  first | exact @GlobalTheory.BigOn.Exp.expOne_level | exact GlobalTheory.BigOn.Exp.expOne_level | (intros; apply GlobalTheory.BigOn.Exp.expOne_level <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealPartPosDefLogDetBoundOfConjugateComparableStatement
section
open Filter Topology MeasureTheory GlobalTheory.HSAmp
open scoped ComplexOrder Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPart_posDef_logDet_bound_of_conjugate_comparable : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℂ) (κ : ℝ), G.PosDef → 1 ≤ κ → (∀ c : ι → ℂ, (∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j * G i j).re ≤ κ * (∑ i, ∑ j, c i * (starRingEnd ℂ) (c j) * G i j).re) → (G.map Complex.re).PosDef ∧ |Real.log (G.map Complex.re).det - Real.log G.det.re| ≤ Fintype.card ι * Real.log (2 * κ) := by
  first | exact @GlobalTheory.RealPartDet.main | exact GlobalTheory.RealPartDet.main | (intros; apply GlobalTheory.RealPartDet.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReciprocitySideEqGenericFibrePullback
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix

theorem side_bc_eq : ∀ (k K : Type) [CommRing k] [Field K] [Algebra k K] [IsFractionRing k K] (X G : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [IsIntegral G] [IsLocallyNoetherian G] (p : X ⟶ Sp k) (q : G ⟶ Sp K) (j : G ⟶ X) (hp : IsPullback j q p (spMap (algebraMap k K))) (τ : K →+* ℂ) (e : ℕ), IsArithVar p (e + 1) → ∀ (Δ : CartierDiv X) (Δ' : CartierDiv G), (∀ x, Δ'.mult x = Δ.mult (j x)) → ∀ (N : MLine p (τ.comp (algebraMap k K))) (L : Fin e → MLine p (τ.comp (algebraMap k K))) (f g : CxPts p (τ.comp (algebraMap k K)) → ℝ), side (N.bc hp.w τ) (fun i => (L i).bc hp.w τ) (fun y => f (bcPt hp.w τ y)) (fun y => g (bcPt hp.w τ y)) Δ' = side N L f g Δ := by
  intro k K _ _ _ _ X G _ _ _ _ p q j hp τ e hA Δ Δ' hΔ N L f g
  obtain ⟨_, _, _, _, _, hinj, _, hcoh, hemp⟩ := GlobalTheory.T.generic_fiber_arithmetic_variety_integral_projective k K X G p q j hp (e + 1) hA
  have hcons : (Fin.cons (N.bc hp.w τ) (fun i => (L i).bc hp.w τ) : Fin (e + 1) → MLine q τ) =
      fun i => ((Fin.cons N L : Fin (e + 1) → MLine p (τ.comp (algebraMap k K))) i).bc hp.w τ := by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> simp
  have h1 := ((GlobalTheory.T.mixedChernMeasure_integral_eq_genericFibre k K X G p q j hp τ (e + 1) hA (Fin.cons N L)).2 f).2
  have hzero : ∀ z : X, z ∉ Set.range j → cycInt L g z = 0 := by
    intro z hz
    haveI := hemp z hz (τ.comp (algebraMap k K))
    simp [cycInt, Mix.int, MeasureTheory.integral_of_isEmpty]
  unfold side
  rw [hcons, h1]
  congr 1
  calc ∑ᶠ x, (Δ'.mult x : ℝ) * cycInt (fun i => (L i).bc hp.w τ) (fun y => g (bcPt hp.w τ y)) x
      = ∑ᶠ x, (Δ.mult (j x) : ℝ) * cycInt L g (j x) := by
        refine finsum_congr fun x => ?_
        rw [hΔ]
        by_cases h : Δ.mult (j x) = 0
        · simp [h]
        · rw [GlobalTheory.T.horizontal_prime_divisor_integral_eq_generic_fibre k K X G p q j hp τ e hA L g x
            (by rw [← hcoh]; exact CartierDiv.coheight_eq_one_of_mult_ne_zero h)]
    _ = ∑ᶠ z ∈ Set.range j, (Δ.mult z : ℝ) * cycInt L g z := (finsum_mem_range (f := fun z => (Δ.mult z : ℝ) * cycInt L g z) hinj).symm
    _ = ∑ᶠ z, (Δ.mult z : ℝ) * cycInt L g z := by
        rw [finsum_mem_def]
        refine finsum_congr fun z => ?_
        by_cases hz : z ∈ Set.range j
        · simp [hz]
        · simp [hz, hzero z hz]

end GlobalTheory.Mix
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReferenceWeightOfTheta
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

namespace GlobalTheory.RefSum.ToWeight

theorem sum_padicValNat_log_le (N : ℕ) (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) :
    ∑ q ∈ S, (padicValNat q N : ℝ) * Real.log q ≤ Real.log N := by
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum]
  calc ∑ q ∈ S, (padicValNat q N : ℝ) * Real.log q = ∑ q ∈ S, (N.factorization q : ℝ) * Real.log q :=
        Finset.sum_congr rfl fun q hq => by rw [Nat.factorization_def N (hS q hq)]
    _ ≤ ∑ q ∈ S ∪ N.factorization.support, (N.factorization q : ℝ) * Real.log q :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left fun q _ _ =>
          mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
    _ = _ := (Finset.sum_subset Finset.subset_union_right fun q _ hq => by
          rw [Finsupp.notMem_support_iff.1 hq]; simp).symm

theorem sum_different_le (E : Type) [Field E] [NumberField E] (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) :
    ∑ q ∈ S, (different_vp E q : ℝ) * Real.log q ≤ lrd E := by
  have hn : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  have h := sum_padicValNat_log_le (discr E).natAbs S hS
  have e1 : lrd E = Real.log ((discr E).natAbs : ℝ) / Module.finrank ℚ E := by
    unfold lrd
    rw [rootDiscr_def, Real.log_rpow (by exact_mod_cast abs_pos.2 (discr_ne_zero E)), Nat.cast_natAbs]
    field_simp
  rw [e1, le_div_iff₀ hn, Finset.sum_mul]
  refine le_of_eq_of_le (Finset.sum_congr rfl fun q _ => ?_) h
  unfold different_vp
  push_cast
  field_simp

theorem different_nonneg (E : Type) [Field E] [NumberField E] (q : ℕ) : (0 : ℝ) ≤ (different_vp E q : ℝ) := by
  unfold different_vp
  push_cast
  positivity

theorem primeSum_add (E : Type) [Field E] [NumberField E] {S B : Finset ℕ} {e : ℕ → ℝ} {s a : ℝ} (h : PrimeSum S e s)
    (hB : ∀ q ∈ B, q.Prime) (ha : 0 ≤ a) :
    PrimeSum (S ∪ B) (fun q => e q + if q ∈ B then a * (different_vp E q : ℝ) + 1 else 0) (s + (a * lrd E + logSum B)) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun q hq => (Finset.mem_union.1 hq).elim (h1 q) (hB q), fun q => add_nonneg (h2 q) ?_, fun q hq => ?_, ?_⟩
  · have := different_nonneg E q
    split_ifs
    · positivity
    · exact le_rfl
  · rw [Finset.mem_union, not_or] at hq
    simp [h3 q hq.1, hq.2]
  · simp only [add_mul, Finset.sum_add_distrib]
    refine add_le_add ?_ ?_
    · rw [← Finset.sum_subset Finset.subset_union_left fun q _ hq => by rw [h3 q hq, zero_mul]]
      exact h4
    · rw [← Finset.sum_subset Finset.subset_union_right fun q _ hq => by rw [if_neg hq, zero_mul]]
      rw [Finset.sum_congr rfl fun q hq => show (if q ∈ B then a * (different_vp E q : ℝ) + 1 else 0) * Real.log q =
        a * ((different_vp E q : ℝ) * Real.log q) + Real.log q by rw [if_pos hq]; ring,
        Finset.sum_add_distrib, ← Finset.mul_sum]
      exact add_le_add (mul_le_mul_of_nonneg_left (sum_different_le E B hB) ha) le_rfl

theorem size_le {f r l n m d σ c : ℝ} (hf : 1 ≤ f) (hr : 1 ≤ r) (hl : 1 ≤ l) (hm0 : 0 ≤ m) (hm : 2 * m ≤ n)
    (hn : n ≤ 20 * f * r ^ 2) (hd : d ≤ 3 * l) (hc : 0 ≤ c) (hσ : σ ≤ c * (f * r * l)) :
    m * (f * r) * d + σ ≤ (30 + c) * (f * r * l) ^ 12 := by
  have hz : 1 ≤ f * r * l := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hf hr) hl
  have h1 : f * r * l ≤ (f * r * l) ^ 12 := le_self_pow₀ hz (by norm_num)
  have h3 : (f * r * l) ^ 3 ≤ (f * r * l) ^ 12 := pow_le_pow_right₀ hz (by norm_num)
  have h4 : f ^ 2 * r ^ 3 * l ≤ f ^ 3 * r ^ 3 * l ^ 3 :=
    mul_le_mul (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hf (by norm_num)) (by positivity))
      (le_self_pow₀ hl (by norm_num)) (by positivity) (by positivity)
  have h5 : m * (f * r) * d ≤ m * (f * r) * (3 * l) := mul_le_mul_of_nonneg_left hd (by positivity)
  have h6 : m * (f * r * (3 * l)) ≤ 10 * f * r ^ 2 * (f * r * (3 * l)) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have h7 := mul_le_mul_of_nonneg_left h1 hc
  nlinarith

theorem refW_of_refTheta : Hypotheses2 → Size → FlatDeg → RefTheta → RefW := fun hP hS hF hT =>
  Closed.imp (Closed.and (Closed.and hT (GlobalTheory.BadLog.logSum_badPrimes_le hS))
      (Closed.and hF (Closed.and (GlobalTheory.T.length_unit_size_bounds hS) (GlobalTheory.T.quotient_weight_gap_bounds hS))))
    fun Fm _ _ ⟨⟨⟨C₁, h₁, hT⟩, C₂, h₂, hB⟩, ⟨_, _, hF⟩, ⟨_, _, hZ⟩, _, _, hW⟩ => by
      obtain ⟨x0, h⟩ := ((hT.and hB).and hF).and (hZ.and hW)
      refine ⟨C₁ + (30 + C₂), by positivity, x0, fun x hx hle ι p hp i hi Y hY u1 hq => ?_⟩
      obtain ⟨⟨⟨hT, hB⟩, hF⟩, hZ, hW⟩ := h x hx hle ι p hp
      obtain ⟨S, e, s, hS, hs, he⟩ := hT i hi Y hY u1 hq
      obtain ⟨z1, z2, z3, z4, z5, z6⟩ := hZ i
      obtain ⟨w1, w2, -, -, -, -, -, -, w3⟩ := hW i hi u1 hq
      have hB := hB i hi Y hY
      have hm : 2 * ((nCol (dat p i) / 2 : ℕ) : ℝ) ≤ nCol (dat p i) := by exact_mod_cast Nat.mul_div_le _ 2
      have hsz := size_le (by exact_mod_cast z5) (by exact_mod_cast z6) z2 (Nat.cast_nonneg _) hm z4 z3 h₂ hB
      refine ⟨_, _, _, primeSum_add (Fm.D x ι).host.E (B := badPrimes p.T.Q.H Y.d.l₂)
        (a := ((nCol (dat p i) / 2 : ℕ) : ℝ) * ((Fm.D x ι).R.f * (Fm.D x ι).R.r)) hS badPrimes_prime (by positivity), ?_,
        fun q hq' => ?_⟩
      · have a1 := mul_le_mul_of_nonneg_left hsz (Nat.cast_nonneg (lenT p i (Fm.parT x hx ι).PP))
        have a2 := mul_le_mul_of_nonneg_left z1 (show (0 : ℝ) ≤ 30 + C₂ by positivity)
        unfold zBase at a2
        linarith
      · refine (GlobalTheory.T.reference_exponent_prime_bound hP _ p.T _ Y _ _ p.fw.laws ⟨Nat.le_add_left _ _, hi.le⟩ hY.1 w1 w2 ⟨_, hF i hi Y hY⟩ u1
          (shift (dat p i) u1 (nCol (dat p i))) (nCol (dat p i) / 2) (1 / 2500) q hq').trans ?_
        rw [EReal.coe_add]
        exact add_le_add (w3 ▸ he q hq') le_rfl

end GlobalTheory.RefSum.ToWeight

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionBasesTransferTotalSpaceIsoStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sectionBases_transfer_totalSpaceIso : ∀ {S S' : Scheme.{0}} (A : Over S) [GrpObj A] (Ag : Over S') [GrpObj Ag] (φ : Ag.left ⟶ A.left) (L : LB A.left), L.IsLB → ∀ (k : ℤ) (R : Type) [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S') (y : Spec (CommRingCat.of R) ⟶ S) (h : (Over.mk x ⊗ Ag).left ⟶ (Over.mk y ⊗ A).left) (hc : ∀ _ : Fin 1, (snd (Over.mk x) Ag).left ≫ φ = h ≫ (snd (Over.mk y) A).left), IsIso h → h ≫ (fst (Over.mk y) A).left = (fst (Over.mk x) Ag).left → ∀ (m : ℕ) (b : Fin m → LB.Sec (LPow A L k (Over.mk y))) (b' : Fin m → LB.Sec (LPow Ag (L.pull φ) k (Over.mk x))), (∀ i, b' i = GlobalTheory.SecTwist.pullSec (chartPullLinComb L φ (fun _ : Fin 1 => (snd (Over.mk x) Ag).left) (fun _ : Fin 1 => (snd (Over.mk y) A).left) (fun _ => k) h hc) (b i)) → LinearIndependent Γ((Over.mk y).left, ⊤) (fun i => (SecM.ofSec A (b i) : SecM A L k (Over.mk y))) → Submodule.span Γ((Over.mk y).left, ⊤) (Set.range fun i => (SecM.ofSec A (b i) : SecM A L k (Over.mk y))) = ⊤ → LinearIndependent Γ((Over.mk x).left, ⊤) (fun i => (SecM.ofSec Ag (b' i) : SecM Ag (L.pull φ) k (Over.mk x))) ∧ Submodule.span Γ((Over.mk x).left, ⊤) (Set.range fun i => (SecM.ofSec Ag (b' i) : SecM Ag (L.pull φ) k (Over.mk x))) = ⊤ := by
  first | (exact @GlobalTheory.SecBasisTransfer.bases_transfer) | (exact GlobalTheory.SecBasisTransfer.bases_transfer) | (intros; apply GlobalTheory.SecBasisTransfer.bases_transfer  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionQuotientsTranscendenceBasisBasepointFreeStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sectionQuotients_transcendenceBasis_basepointFree : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → (∀ j, x j ≠ 0) ∧ AlgebraicIndependent ℤ (fun j : Fin D => x j.succ / x 0) ∧ FiniteDimensional (ratF x) X.functionField := by
  first | exact @GlobalTheory.HSAmp.gens_quot_trBasis | exact GlobalTheory.HSAmp.gens_quot_trBasis | (intros; apply GlobalTheory.HSAmp.gens_quot_trBasis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianDescendsNearClosedFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem smooth_of_charts_cover : ∀ (Y G U : Scheme.{0}) (J : Type) (ψ : J → (U ⟶ G)) (g : G ⟶ Y) (h : U ⟶ Y), (∀ j, IsOpenImmersion (ψ j)) → (∀ x : G, ∃ j, x ∈ Set.range (ψ j)) → (∀ j, ψ j ≫ g = h) → Smooth h → Smooth g := by
  intro Y G U J ψ g h ho hc hw hs
  let 𝒰 : G.OpenCover := Scheme.Cover.mkOfCovers J (fun _ => U) ψ (fun x => by
    obtain ⟨j, hj⟩ := hc x; exact ⟨j, hj⟩) ho
  haveI : IsZariskiLocalAtSource @Smooth.{0} := HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_openCover (P := @Smooth) 𝒰 ?_
  intro j
  have h2 : 𝒰.f j ≫ g = h := hw j
  rw [h2]; exact hs

theorem descends_near_closed_fibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ N : Near π G', N.Law → ∀ φ, N.Datum φ → ∃ (G : Over (Sp R)) (β : G'.left ⟶ G.left) (i : N.U ⟶ G), Smooth G.hom ∧ IsPullback β G'.hom G.hom π ∧ IsOpenImmersion i.left ∧ N.u ≫ β = pullback.fst _ _ ≫ i.left ∧ pullback.fst G'.hom (pullback.fst π π) ≫ β = φ.hom.left ≫ pullback.fst G'.hom (pullback.snd π π) ≫ β := by
  intro R _ _ _ hA S π hp hs hS G' _ _ hG N hL φ hφ
  obtain ⟨n, a, x, hx, hcov⟩ := GlobalTheory.T.finite_section_translates_cover_semiAbelian R hA S π hp hs hS G' hG N hL
  haveI : IsNoetherianRing R := hA.1
  haveI : IsIntegrallyClosed R := hA.2.2.1
  haveI : Smooth N.U.hom := N.smooth
  obtain ⟨G, β, ψ, hψ, hcovG, hpb, hφβ⟩ := GlobalTheory.T.exists_descent_of_charts_pulled_back_from_flat R S G'.left π G'.hom hp hs hS φ.hom.left (Over.w φ.hom)
    N.U inferInstance (Option (Fin n)) (N.chart x) (fun j => (GlobalTheory.T.chart_isOpenImmersion_over_base S π G' N n x j).1)
    (fun j => (GlobalTheory.T.chart_isOpenImmersion_over_base S π G' N n x j).2) (GlobalTheory.T.smoothNeighbourhood_translates_cover_group S π G' N n x hcov)
    (GlobalTheory.T.descentDatum_carries_translateChart S π G' N n a x (fun i => (hx i).2) φ hφ)
  refine ⟨G, β, Over.homMk (ψ none) (hψ none).2.1, ?_, hpb, (hψ none).1, ?_, hφβ⟩
  · exact smooth_of_charts_cover _ _ _ _ ψ G.hom N.U.hom (fun j => (hψ j).1) hcovG (fun j => (hψ j).2.1) N.smooth
  · simpa using (hψ none).2.2

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianGroupActionStarAdjointBundle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum GlobalTheory.MumFam

namespace GlobalTheory.MumFam

theorem gAdj_act_star : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG → ∀ x : O, GAdj U.LG.L U.LG.L (oG.act x) (oG.act (Star.star x)) := by
  intro R _ _ _ hR D A G _ _ hG U O _ _ _ o oA oG hlin x
  have hL : ∀ a : O, LinHom U.toUnifPre U.toUnifPre (o.onB.act a)
      (DistribMulAction.toAddMonoidHom D.toPre.X (Star.star a)) (oG.act a) := fun a =>
    ⟨oG.hom a, fun e => hlin.q_lin e a, fun e => by
      obtain ⟨t, ht, hi⟩ := hlin.i_lin e a
      exact ⟨t, ht, hi⟩⟩
  have hE := (GlobalTheory.Mum.endData_symm_and_ofOAct R D.toPre).2 O o x
  have h₁ := linHom_iff_linEnd.1 (hL x)
  have h₂ := linHom_iff_linEnd.1 (hL (Star.star x))
  rw [star_star] at h₂
  exact GlobalTheory.Mum.linEnd_adjoint_lbIso R hR D A G hG U _ _ _ _ hE _ _ h₁ h₂

end GlobalTheory.MumFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearPDivGroupHomChartConstantCoeffSubstStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semilinearPDivGroupHom_chart_constantCoeff_subst : ∀ (p : ℕ) (k k' : Type) [CommRing k] [CommRing k'] (σ : k →+* k') (d e : ℕ) (G : PDivGroup p k) (G' : PDivGroup p k') (c : Chart G d) (c' : Chart G' e) (s : SemiHom σ G' G) (φ : Fin d → MvPowerSeries (Fin e) k'), (∀ n j, c'.ev n (φ j) = s.app n (c.x n j)) → (∀ j, constantCoeff (φ j) = 0) ∧ ∀ n g, c'.ev n (subst φ (MvPowerSeries.map σ g)) = s.app n (c.ev n g) := by
  first | exact @GlobalTheory.Katz.semiHom_constantCoeff_and_ev | exact GlobalTheory.Katz.semiHom_constantCoeff_and_ev | (intros; apply GlobalTheory.Katz.semiHom_constantCoeff_and_ev <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelThetaConstantsProjectivelyIntegralAnyBaseStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelThetaConstants_projectively_integral_anyBase : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (P : PolAV F.X) (rig : LB.Gen (P.L.pull (eSec P.A))) (m N : ℕ) (f : F.X ⟶ PSpace (cycAway n) N), ThAt F W P rig m f → GlobalTheory.Poinc.ThetaInt F W f := by
  first | exact @GlobalTheory.SiegTh.ThIntAll.thetaInt_all | exact GlobalTheory.SiegTh.ThIntAll.thetaInt_all | (intros; apply GlobalTheory.SiegTh.ThIntAll.thetaInt_all <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelThetaConstantsProjectivelyIntegralStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelThetaConstants_projectively_integral : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (P : PolAV F.X) (rig : LB.Gen (P.L.pull (eSec P.A))) (m N : ℕ) (f : F.X ⟶ PSpace (cycAway n) N), ThAt F W P rig m f → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (β : cycAway n →+* o) (S : ThetaSys o Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X), SysAt F W β S ρ u → ∀ (M : RatModel o Ω) (h : M.Z ⟶ PSpace (cycAway n) N), Geo.Tor.IsNormalScheme M.Z → M.pt ≫ h = spMap S.R.val.toRingHom ≫ u ≫ f → M.HasDiv S.th := by
  first | exact @GlobalTheory.SiegTh.ThInt.thetaInt | exact GlobalTheory.SiegTh.ThInt.thetaInt | (intros; apply GlobalTheory.SiegTh.ThInt.thetaInt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudeActionAdelicLatticeStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.similitude_action_adelic_lattice : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (N : ℕ), 0 < N → N.Coprime p → ∀ t : SimSys D N N, ∃ h ∈ L.KN N, ∀ n : ℕ, 0 < n → n.Coprime p → ∀ x : D.La, ∃ w ∈ LaHat D, L.actG h (inAf D x) = inAf D (t.g n x) + n • w := by
  first | (exact @GlobalTheory.AdelicSim.exists_mem_KN) | (exact GlobalTheory.AdelicSim.exists_mem_KN) | (intros; apply GlobalTheory.AdelicSim.exists_mem_KN <;> assumption)
end

