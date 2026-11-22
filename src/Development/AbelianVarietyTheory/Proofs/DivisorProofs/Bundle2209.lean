import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2049
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Foundations.NonnegOfMemCStarSet
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0458
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0305
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRepBasisCharpoly
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0467
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0798
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0676
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0508
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankEqOfInverse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1710
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1792
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1845
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1723
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2181
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2180
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1200
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleExternalTensorPowerGroupPower
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0038
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0041
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0061
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.Bundle0004
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0080
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0212
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegTwoLeGapKap
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

set_option autoImplicit false

namespace GlobalTheory.HSApp.GapArith

theorem gap_add {N : ℕ} (v w : Fin N → ℤ) (k : ℕ) : gap (v + w) k = gap v k + gap w k := by
  unfold gap
  split_ifs
  · simp only [Pi.add_apply]; ring
  · simp

theorem gap_nsmul {N : ℕ} (n : ℕ) (v : Fin N → ℤ) (k : ℕ) : gap (n • v) k = (n : ℤ) * gap v k := by
  unfold gap
  split_ifs
  · simp only [Pi.smul_apply, nsmul_eq_mul]; ring
  · simp

theorem neg_two_le_gap_kap {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : Datum H) (τ : Psi H) {k : ℕ} (h : k + 1 < Dw.p + Dw.q) : -2 ≤ gap (FlagTan.kap Dw τ) k := by
  simp only [gap, dif_pos h, FlagTan.kap]
  split_ifs <;> push_cast <;> omega

theorem gaps_main (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (P : WtPar Dw) : WtBig P → GapGe 1 P.u₁ ∧ GapGe 1 P.u₂ ∧ ∀ i : ℕ, GapGe 1 (P.wt i) := by
  intro hB
  have hD : 1 ≤ dimFlag Dw := hB.one_le
  have h4 : ∀ (τ : Psi H) (k : ℕ), k + 1 < Dw.p + Dw.q → 4 ≤ gap (P.u₁ τ) k := by
    intro τ k hk
    have h := hB.gaps τ k hk
    have hb : 4 ≤ (dimFlag Dw + 3) * ((dimFlag Dw + 1).choose 2 + 4 * (Dw.p + Dw.q) + dimFlag Dw + 3) :=
      Nat.le_trans (by omega : 4 ≤ (dimFlag Dw + 3) * 1)
        (Nat.mul_le_mul_left _ (by omega))
    have hb' : (4 : ℤ) ≤ (((dimFlag Dw + 3) * ((dimFlag Dw + 1).choose 2 + 4 * (Dw.p + Dw.q) + dimFlag Dw + 3) : ℕ) : ℤ) := by
      exact_mod_cast hb
    exact hb'.trans h
  have hu₂ : ∀ (τ : Psi H) (k : ℕ), gap (P.u₂ τ) k = gap (P.u₁ τ) k + gap (P.rem τ) k := by
    intro τ k
    exact gap_add _ _ _
  have hwt : ∀ (i : ℕ) (τ : Psi H) (k : ℕ), gap (P.wt i τ) k =
      gap (FlagTan.kap Dw τ) k + gap (P.u₂ τ) k + (dimFlag Dw : ℤ) * gap (P.u₁ τ) k + (i : ℤ) * gap (P.u₁ τ) k := by
    intro i τ k
    have e : P.wt i τ = FlagTan.kap Dw τ + P.u₂ τ + dimFlag Dw • P.u₁ τ + i • P.u₁ τ := rfl
    rw [e, gap_add, gap_add, gap_add, gap_nsmul, gap_nsmul]
  refine ⟨fun τ k hk => by have := h4 τ k hk; omega, fun τ k hk => ?_, fun i τ k hk => ?_⟩
  · have := h4 τ k hk
    have := (P.gap_rem τ k).1
    rw [hu₂]; omega
  · have a := h4 τ k hk
    have b := (P.gap_rem τ k).1
    have c := neg_two_le_gap_kap Dw τ hk
    rw [hwt, hu₂]
    have d : (4 : ℤ) ≤ (dimFlag Dw : ℤ) * gap (P.u₁ τ) k := by
      have : (1 : ℤ) ≤ dimFlag Dw := by exact_mod_cast hD
      nlinarith
    have e : (0 : ℤ) ≤ (i : ℤ) * gap (P.u₁ τ) k := by positivity
    omega

end GlobalTheory.HSApp.GapArith
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdConjDifferentAndSum
section
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

namespace GlobalTheory.DifferentGalois

theorem ord_conjDifferent_and_sum : ∀ (E K : Type) [Field E] [NumberField E] [IsGalois ℚ E] [Field K] [NumberField K] (i : E →+* K) (q : ℕ) (w : HeightOneSpectrum (𝓞 K)), q.Prime → ((q : ℕ) : 𝓞 K) ∈ w.asIdeal → (ord_vw w (conjDifferent i) : ℝ) = (different_vp E q : ℝ) * (vAdd w (q : K) : ℝ) ∧ ∑ p ∈ (discr E).natAbs.primeFactors, (different_vp E p : ℝ) * Real.log p = lrd E := by
  intro E K _ _ _ _ _ i q w hq hm
  refine ⟨?_, ?_⟩
  · have hd : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (discr_ne_zero E)
    have h1 := DefectSumCompare.vla_discAt i w
    have h2 := GlobalTheory.FlatLine.vla_span (K := K) (x := ((discr E).natAbs : ℕ)) (Nat.cast_ne_zero.2 hd) w
    have h3 := GlobalTheory.FlatLine.vAdd_natCast (K := K) hq hd hm
    have h5 : ((Module.finrank ℚ E * ord_vw w (conjDifferent i) : ℕ) : ℤ) =
        padicValNat q (discr E).natAbs * vAdd w (q : K) := by
      rw [← h1, ← h3]; exact h2
    have h7 := congrArg (Int.cast : ℤ → ℝ) h5
    simp only [Int.cast_mul, Int.cast_natCast, Nat.cast_mul] at h7
    have hE : (Module.finrank ℚ E : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
    rw [different_vp]
    push_cast
    field_simp
    linarith
  · have hd : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (discr_ne_zero E)
    have hE : (Module.finrank ℚ E : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
    have h1 := DefectSumCompare.log_discr_eq E
    have h2 : Real.log |((discr E : ℤ) : ℝ)| = Real.log ((discr E).natAbs : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    rw [h2, Real.log_nat_eq_sum_factorization, Finsupp.sum, Nat.support_factorization] at h1
    have h3 : ∀ p ∈ (discr E).natAbs.primeFactors, ((different_vp E p : ℚ) : ℝ) * Real.log p =
        ((discr E).natAbs.factorization p * Real.log p) / (Module.finrank ℚ E : ℝ) := by
      intro p hp
      rw [different_vp, Nat.factorization_def _ (Nat.prime_of_mem_primeFactors hp)]
      push_cast
      ring
    rw [Finset.sum_congr rfl h3, ← Finset.sum_div, h1]
    field_simp

end GlobalTheory.DifferentGalois
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PhiAt
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSApp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c)

def PhiAt (y : Y₀ X Z) (ν : Valuation ((Y₀ X Z).presheaf.stalk y) (WithZero (Multiplicative ℤ))) (φ : ℝ) : Prop :=
  ∃ (T : CDVR) (io : c.F →+* T.Fr) (y' : IntFr Xo c T io) (g : (Y₀ X Z).presheaf.stalk y →+* T.V) (ρ φT : ℝ),
    0 < ρ ∧ GlobalTheory.SlopeRec.HasPhi y' φT ∧ φ = ρ * φT ∧
    (letI := io.toAlgebra; X.ptY y'.1 =
      Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ X Z).fromSpecStalk y ≫ inc₀ X Z) ∧
    ∀ a, ν a ≠ 0 → -((WithZero.log (ν a) : ℤ) : ℝ) = ρ * (vV T.V (algebraMap T.V T.Fr (g a)) : ℝ)

theorem PhiAt.nonneg {y : Y₀ X Z} {ν : Valuation ((Y₀ X Z).presheaf.stalk y) (WithZero (Multiplicative ℤ))} {φ : ℝ}
    (h : PhiAt X Z y ν φ) : 0 ≤ φ := by
  obtain ⟨T, io, y', g, ρ, φT, hρ, hφ, rfl, -, -⟩ := h
  exact mul_nonneg hρ.le hφ.nonneg

end GlobalTheory.HSApp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceShiftOfDieudonne
section
set_option autoImplicit false

noncomputable section

open GlobalTheory GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv GlobalTheory.HTLat GlobalTheory.CompHt GlobalTheory.PDivGroup Matrix TensorProduct NumberField CategoryTheory

namespace GlobalTheory.PlaceShiftGlue

theorem bar_rt_ne {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) :
    IsCMField.complexConj E (H.rt : E) ≠ (H.rt : E) := by
  intro h
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h1 := IsCMField.complexEmbedding_complexConj E φ (H.rt : E)
  rw [h] at h1
  have h2 : φ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
    rw [← map_pow, RingOfIntegers.coe_eq_algebraMap, ← map_pow, H.rt_sq]; simp
  obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 h1.symm
  rw [hr] at h2
  have h3 : r ^ 2 = -(H.d : ℝ) := by exact_mod_cast h2
  have h4 : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  nlinarith [sq_nonneg r]

open Classical in

theorem sum_two_weights {ι : Type} [Finite ι] (S : ι → Prop) (n : ι → ℕ) (κ : ι → ℝ) (κ₀ : ℝ) (a q : ℕ)
    (hn : ∀ i, n i = if S i then a else q) :
    ((a + q : ℕ) : ℝ) * κ₀ + ∑ᶠ i, (n i : ℝ) * κ i =
      a * (κ₀ + ∑ᶠ i, if S i then κ i else 0) + q * (κ₀ + ∑ᶠ i, if S i then 0 else κ i) := by
  haveI := Fintype.ofFinite ι
  simp only [finsum_eq_sum_of_fintype, mul_add, Finset.mul_sum]
  have : ∑ i, (n i : ℝ) * κ i =
      ∑ i, (a : ℝ) * (if S i then κ i else 0) + ∑ i, (q : ℝ) * (if S i then 0 else κ i) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hn]
    split_ifs <;> simp
  rw [this]
  push_cast
  ring

theorem exists_height_eq {p : ℕ} [Fact p.Prime] {Λ : Type} [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ]
    [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ] {h : ℕ}
    (ρ : Λ →ₐ[ℤ_[p]] Matrix (Fin h) (Fin h) ℤ_[p]) : ∃ N, h = Module.finrank ℤ_[p] Λ * N := by
  haveI : Module.Free ℤ_[p] Λ := inferInstance
  obtain ⟨N, -, hN, -⟩ := GlobalTheory.DetInv.rep_free_charpoly p Λ h _ (Module.finBasis ℤ_[p] Λ) ρ
  exact ⟨N, hN.trans (mul_comm _ _)⟩

open Classical in

theorem shift_at_point (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]
    (E : Type) [Field E] [NumberField E] [StarRing (𝓞 E)] (P : Point p v O (𝓞 E)) (ε : PreTilt O p)
    (hε : IsPrimitiveRoot (root ε).untilt p) (h : ℕ) (D : Datum ε h (ℤ_[p] ⊗[ℤ] 𝓞 E))
    (φ : P.V ≃ₗ[C] (Fin h → C))
    (hD : IsTie P D (Algebra.TensorProduct.includeRight : 𝓞 E →ₐ[ℤ] ℤ_[p] ⊗[ℤ] 𝓞 E).toRingHom φ)
    (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ]
    [FaithfulSMul ℤ_[p] Λ] (π : ℤ_[p] ⊗[ℤ] 𝓞 E →ₐ[ℤ_[p]] Λ) (e : ℤ_[p] ⊗[ℤ] 𝓞 E) (he : IsIdempotentElem e)
    (hπ : Function.Surjective π) (hk : RingHom.ker π = Ideal.span {1 - e}) (t₀ : Λ →+* O) (γ : O ≃+* O)
    (κ₀ : ℝ) (κ : (Λ →+* O) → ℝ)
    (hκ : ∀ (N h : ℕ), h = Module.finrank ℤ_[p] Λ * N → ∀ (D : Datum ε h Λ), ∃ r : NNReal, r ≠ 0 ∧
      IsShift C v D ((γ : O →+* O).comp t₀) r ∧
      Real.log r = N * κ₀ + ∑ᶠ σ, (D.lieRank ((γ : O →+* O).comp σ) : ℝ) * κ σ)
    (τ τ' : E →+* C) (hτ : ∀ a : 𝓞 E, γ (t₀ (π (1 ⊗ₜ a))) = embO P.integers τ a)
    (hτ' : (embO P.integers τ).comp (starRingEnd (𝓞 E)) = embO P.integers τ')
    (rt : 𝓞 E) (hrt : τ' (rt : E) ≠ τ (rt : E)) (a q : ℕ)
    (hrank : ∀ ψ : E →+* C, Module.finrank C (P.eigW (embO P.integers ψ)) =
      if ψ (rt : E) = τ (rt : E) then a else q)
    (x : Fin a → P.V) (y : Fin q → P.V) (g : Matrix (Fin a) (Fin a) C) (g' : Matrix (Fin q) (Fin q) C)
    (hx : Submodule.span O (Set.range x) = P.wRec (embO P.integers τ))
    (hy : Submodule.span O (Set.range y) = P.wRec ((embO P.integers τ).comp (starRingEnd (𝓞 E))))
    (hg : IsLatBasis C (P.latTQuot (σ := fun φ' : E →+* C => embO P.integers φ') (isSplitting_embO P.integers) τ)
      (fun i => ∑ j, g i j • x j))
    (hg' : IsLatBasis C (P.latTSub ((embO P.integers τ).comp (starRingEnd (𝓞 E)))) (fun i => ∑ j, g' i j • y j)) :
    Real.log (v g.det) - Real.log (v g'.det) =
      a * (κ₀ + ∑ᶠ σ : Λ →+* O, if σ (π (1 ⊗ₜ rt)) = t₀ (π (1 ⊗ₜ rt)) then κ σ else 0) +
      q * (κ₀ + ∑ᶠ σ : Λ →+* O, if σ (π (1 ⊗ₜ rt)) = t₀ (π (1 ⊗ₜ rt)) then 0 else κ σ) := by
  have hv := P.integers
  obtain ⟨hT, hH, hex, heig⟩ := GlobalTheory.T.datum_tie_number_field_point p C v O E P ε h D φ hε hD
  obtain ⟨h', D', iT, pT, iM, pM, hsp⟩ := GlobalTheory.T.idempotent_quotient_datum_compat p C v O hv ε hε _ Λ π e he hπ hk h D
  have hss := GlobalTheory.DetInv.part_rank_dim_shift p C v O hv ε hε _ Λ π e he hπ hk h h' D D' iT pT iM pM hsp hT hH
  obtain ⟨N, hN⟩ := exists_height_eq D'.ρT
  obtain ⟨r, hr0, hr, hlog⟩ := hκ N h' hN D'
  have hdim := (GlobalTheory.eig_decomp_T_H p C v O hv ε hε Λ N h' hN D').1.2.2 ((γ : O →+* O).comp t₀)
  obtain ⟨-, hd, hsh⟩ := hss ((γ : O →+* O).comp t₀)
  have ha : Module.finrank C (P.eigW (embO P.integers τ)) = a := by rw [hrank, if_pos rfl]
  have hq : Module.finrank C (P.eigW ((embO P.integers τ).comp (starRingEnd (𝓞 E)))) = q := by
    rw [hτ', hrank, if_neg hrt]
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.datum_tie_hodge_tate_kernel p C v O E P ε h D φ hε hD _ τ r (RingHom.ext hτ) (hsh r hr) a q x y g g'
    ha hq hx hy hg hg'
  have hNa : N = a + q := by rw [← hdim, hd, h3]
  haveI := (GlobalTheory.card_ringHom_to_integers_eq_finrank p C v O hv Λ).1
  have hlie : ∀ σ : Λ →+* O, D'.lieRank ((γ : O →+* O).comp σ) =
      if σ (π (1 ⊗ₜ rt)) = t₀ (π (1 ⊗ₜ rt)) then a else q := fun σ => by
    obtain ⟨ψ, hψ⟩ := hex (((γ : O →+* O).comp σ).comp (π : ℤ_[p] ⊗[ℤ] 𝓞 E →+* Λ))
    rw [(hss _).1, (heig _ ψ hψ).2.2.2, hrank]
    have e1 : γ (σ (π (1 ⊗ₜ rt))) = embO P.integers ψ rt := RingHom.congr_fun hψ rt
    refine if_congr ?_ rfl rfl
    rw [← algebraMap_embO P.integers ψ, ← algebraMap_embO P.integers τ, ← e1, ← hτ,
      hv.hom_inj.eq_iff, γ.injective.eq_iff]
  have hg0 : ((v g'.det : NNReal) : ℝ) ≠ 0 := by
    exact_mod_cast (Valuation.ne_zero_iff v).2 h2
  have hr0' : (r : ℝ) ≠ 0 := by exact_mod_cast hr0
  rw [h1, NNReal.coe_mul, Real.log_mul hr0' hg0, add_sub_cancel_right, hlog, hNa]
  exact sum_two_weights _ (fun σ => D'.lieRank ((γ : O →+* O).comp σ)) κ κ₀ a q hlie

theorem placeShift (hSW : GlobalTheory.Published.ScholzeWeinsteinB) (hPD : GlobalTheory.Published.PrismaticDieudonneHodge)
    (hK : GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.HodgeTateKernelAtPoint) : GlobalTheory.FlatCM.PlaceShiftSt := by
  classical
  intro E _ _ _ H _ ℓ _ w
  by_cases hw : ∃ τ₀ : E →+* ℂ_[ℓ], ∀ a : 𝓞 E, a ∈ w.asIdeal ↔ ‖τ₀ (a : E)‖ < 1
  swap
  · exact ⟨0, 0, fun τ hτ => (hw ⟨τ, hτ⟩).elim⟩
  obtain ⟨τ₀, hτ₀⟩ := hw
  obtain ⟨i1, i2, ε, hv, hε⟩ := PadicComplexHost.main ℓ
  obtain ⟨Λ, _, _, _, _, _, _, π, e, t₀, he, hπ, hk, ht₀, hall⟩ := GlobalTheory.PlaceRing.exists_placeRing E ℓ (embO hv τ₀)
  obtain ⟨κ₀, κ, hκ⟩ := GlobalTheory.T.dvr_embedding_determinant_value ℓ ℂ_[ℓ] Valued.v 𝓞_ℂ_[ℓ] hv ε hε Λ t₀
  refine ⟨κ₀ + ∑ᶠ σ : Λ →+* 𝓞_ℂ_[ℓ],
      @ite ℝ (σ (π (1 ⊗ₜ H.rt)) = t₀ (π (1 ⊗ₜ H.rt))) (Classical.propDecidable _) (κ σ) 0,
    κ₀ + ∑ᶠ σ : Λ →+* 𝓞_ℂ_[ℓ],
      @ite ℝ (σ (π (1 ⊗ₜ H.rt)) = t₀ (π (1 ⊗ₜ H.rt))) (Classical.propDecidable _) 0 (κ σ), fun τ hτ => ?_⟩
  letI := H.starRing; letI := algPadicInt ℓ; letI := algPadicField ℓ; haveI := towerPadic ℓ
  intro _ P a q hrank x x' g g' hx hx' hg hg'
  have hc : ∀ (ψ : E →+* ℂ_[ℓ]) (b : 𝓞 E), ((embO hv ψ b : 𝓞_ℂ_[ℓ]) : ℂ_[ℓ]) = ψ b := fun ψ b =>
    algebraMap_embO hv ψ b
  obtain ⟨t, ht⟩ := hall (embO hv τ) fun b => by rw [hc, hc, ← hτ, ← hτ₀]
  obtain ⟨γ, hγ, rfl⟩ := GlobalTheory.EmbConj.exists_isIsom_comp ℓ Λ t₀ t
  have hε' : GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.IsPrimitiveSystem ε := Dieudonne.isPrimitiveRoot_untilt_root hε
  have hS := GlobalTheory.T.hodgeTateSandwich_of_prismaticDieudonne hPD ℓ ℂ_[ℓ] Valued.v 𝓞_ℂ_[ℓ] hv ε hε'
  have hP := (hK ℓ ℂ_[ℓ] Valued.v 𝓞_ℂ_[ℓ] (𝓞 E) P).2.2.2
  obtain ⟨h, D, φ, hD⟩ := GlobalTheory.T.hodge_tate_sandwich_star_rep ℓ ℂ_[ℓ] Valued.v 𝓞_ℂ_[ℓ] ε hε' hS (𝓞 E) P hP
    (GlobalTheory.T.hodge_tate_sandwich_lattice_rep hSW ℓ ℂ_[ℓ] Valued.v 𝓞_ℂ_[ℓ] ε hε' hS (𝓞 E) P hP)
  rw [← PadicComplexHost.valuation_coe_eq_norm, ← PadicComplexHost.valuation_coe_eq_norm]
  refine shift_at_point ℓ ℂ_[ℓ] Valued.v 𝓞_ℂ_[ℓ] E P ε hε h D φ hD Λ π e he hπ hk t₀ γ κ₀ κ (hκ γ hγ)
    τ (τ.comp (IsCMField.complexConj E).toAlgHom.toRingHom) ht ?_ H.rt ?_ a q hrank _ _ g g' hx hx' hg hg'
  · refine RingHom.ext fun b => hv.hom_inj ?_
    rw [RingHom.comp_apply, algebraMap_embO, algebraMap_embO]
    exact congrArg τ (H.bar_eq b)
  · exact fun h0 => bar_rt_ne H (τ.injective h0)

end GlobalTheory.PlaceShiftGlue

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationFormAdjointCmActionModuliPoint
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PolAdjointRing

theorem polForm_adjoint : GlobalTheory.Published.AbelianDeRham → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {A : Over (Sp S)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left}, IsGrpPullback A Xo.univ.t.G x π → ∀ (a : OAct (𝓞 E) A), (∀ z, (a.act z).left ≫ π = π ≫ (Xo.univ.t.act.act z).left) → ∀ {ψ : LinearMap.BilinForm S (HdR A)}, IsPolForm (dp0 S) (𝟙 _) A (Xo.univ.t.PP.L.pull π) ψ → IsAdjointFor a (fun z => H.bar z) ψ := by
  intro P E _ _ _ H Dw l Xo S _ x A _ π hπ a ha ψ hψ z u v
  have hA := PolPull.isAbelianScheme_of_isGrpPullback (ObjDim.isAbelianScheme Xo.univ) hπ
  have gA := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ.1
    (ObjDim.smoothOfRelativeDimension Xo.univ)
  have := hA.comm
  have := a.hom
  exact GlobalTheory.PolAdjoint.adjoint_of_lbIso P.1 hA gA (pull_isLB Xo.univ.t.PP.isLB π) hψ (a.act z)
    (a.act (H.bar z)) (GlobalTheory.PolAdjoint.lbIso_cube hπ _ (ha z) (ha (H.bar z)) (Xo.univ.t.adj z)) u v

end GlobalTheory.PolAdjointRing
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowMulIntersectionLeOfNefClassOnClosedStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pow_mul_intersection_le_of_nef_class_on_closed : GlobalTheory.Published.NefNumerics → ∀ (k : Type) [Field k] (X : Scheme.{0}) (q : X ⟶ Sp k), IsProjOver q → letI := algebraΓOfHom q; ∀ (N N' N₀ : LB X) (hN : N.IsLB) (hN' : N'.IsLB) (h₀ : N₀.IsLB) (a b : ℕ) (Z : Closeds X) (e : ℕ), IsNef k N → IsNef k N' → cls N₀ h₀ = a • cls N hN + b • cls N' hN' → topologicalKrullDim (Z : Set X) = e → (a : ℤ) ^ e * interNumRed k Z (fun _ : Fin e => N) ≤ interNumRed k Z (fun _ : Fin e => N₀) := by
  first | exact @GlobalTheory.mixExp_interNumRed | exact GlobalTheory.mixExp_interNumRed | (intros; apply GlobalTheory.mixExp_interNumRed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelMulArchimedeanMemNhds
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
open MeasureTheory Formalism.L2.Theta Formalism.BasicNotions.TH ReciprocityTheory.ChartRestriction.G.FD Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped Topology TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LevelNbhd

open GlobalTheory.GfCut

variable {D : D7}

def finIdem (D : D7) : AE D := algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 1)

theorem finIdem_mul : finIdem D * finIdem D = finIdem D := by
  unfold finIdem
  rw [← map_mul]
  congr 1
  show ((0 : Ainf D.host.F) * 0, (1 : Af D.host.F) * 1) = (0, 1)
  simp

theorem cA_finIdem : cA D (finIdem D) = finIdem D := by
  unfold finIdem
  simp [cA, sigR, Algebra.TensorProduct.algebraMap_apply]

theorem fst_finIdem :
    (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom (finIdem D) = 0 := by
  show fstA D.host.F (pairA D.host.F 0 1) ⊗ₜ[D.host.F] (AlgHom.id D.host.F D.host.E) 1 = 0
  rw [show fstA D.host.F (pairA D.host.F 0 1) = 0 from rfl, TensorProduct.zero_tmul]

theorem snd_finIdem :
    (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom (finIdem D) = 1 := by
  show sndA D.host.F (pairA D.host.F 0 1) ⊗ₜ[D.host.F] (AlgHom.id D.host.F D.host.E) 1 = 1
  rw [show sndA D.host.F (pairA D.host.F 0 1) = 1 from rfl]
  rfl

def finPartGL (V : HSp D) (g : GA D V) : GL (Fin V.rank) (AE D) :=
  ⟨finIdem D • Formalism.L2.Theta.mt V g + (1 - finIdem D) • 1,
    finIdem D • ((matHom V g)⁻¹).1 + (1 - finIdem D) • 1,
    idem_mul _ finIdem_mul _ _ (matHom V g).mul_inv, idem_mul _ finIdem_mul _ _ (matHom V g).inv_mul⟩

theorem finPartGL_mem (V : HSp D) (g : GA D V) : finPartGL V g ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := by
  have hgU : Formalism.UG.cT (cA D) (Formalism.L2.Theta.mt V g) * V.gram.map (incA D) * Formalism.L2.Theta.mt V g =
      V.gram.map (incA D) :=
    (show HR (AF D.host.F) D.sp.cm.sig V.gram from g).2
  have hKU := idem_unitary (cA D) _ cA_finIdem finIdem_mul _ _ hgU
  exact hKU

def finPartG (V : HSp D) (g : GA D V) : GA D V :=
  (⟨finPartGL V g, finPartGL_mem V g⟩ : HR (AF D.host.F) D.sp.cm.sig V.gram)

theorem finPartG_mem_GfC (V : HSp D) (g : GA D V) : finPartG V g ∈ GfC V := by
  show infHom V (finPartG V g) = 1
  apply Units.ext
  change (finIdem D • Formalism.L2.Theta.mt V g + (1 - finIdem D) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))).map _ = 1
  rw [map_idem, fst_finIdem, zero_smul, zero_add, sub_zero, one_smul]

theorem finHom_finPartG (V : HSp D) (g : GA D V) : finHom V (finPartG V g) = finHom V g := by
  apply Units.ext
  change (finIdem D • Formalism.L2.Theta.mt V g + (1 - finIdem D) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))).map _ = _
  rw [map_idem, snd_finIdem, one_smul, sub_self, zero_smul, add_zero]
  rfl

theorem inv_finPartG_mul_mem_GinfC (V : HSp D) (g : GA D V) : (finPartG V g)⁻¹ * g ∈ GinfC V := by
  show finHom V ((finPartG V g)⁻¹ * g) = 1
  rw [map_mul, map_inv, finHom_finPartG, inv_mul_cancel]

theorem finCong_finPartG_iff {V : HSp D} {N : ℕ} (g : GA D V) :
    GlobalTheory.Member.FinCong V N (finPartG V g) ↔ GlobalTheory.Member.FinCong V N g := by
  unfold GlobalTheory.Member.FinCong
  rw [finHom_finPartG]

theorem level_mul_inf_mem_nhds : ∀ (D : D7) (V : HSp D) (N : ℕ) (Kf : Subgroup (GA D V)), 0 < N →
    IsLevelK V N Kf → ∀ g₀ : GA D V,
      {g : GA D V | ∃ k ∈ Kf, ∃ h ∈ GinfC V, g = g₀ * k * h} ∈ 𝓝 g₀ := by
  intro D V N Kf hN hK g₀
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hU := GlobalTheory.Member.PrincLevel.finCong_mem_nhds V hN
  have ht : Filter.Tendsto (fun x : GA D V => g₀⁻¹ * x) (𝓝 g₀) (𝓝 1) := by
    have := (continuous_mul_left g₀⁻¹).tendsto g₀
    rwa [inv_mul_cancel] at this
  refine Filter.mem_of_superset (ht hU) fun x hx => ?_
  have hx' : GlobalTheory.Member.FinCong V N (g₀⁻¹ * x) := hx
  refine ⟨finPartG V (g₀⁻¹ * x), (hK _).2 ⟨finPartG_mem_GfC V _, (finCong_finPartG_iff _).2 hx'⟩,
    (finPartG V (g₀⁻¹ * x))⁻¹ * (g₀⁻¹ * x), inv_finPartG_mul_mem_GinfC V _, ?_⟩
  group

end GlobalTheory.LevelNbhd
end
end

