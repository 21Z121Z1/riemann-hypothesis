import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0005
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0318
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCosetOfIsTensor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoefficientBound
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0575
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0501
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0325
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0560
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowEqSpan
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0062
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0626
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0623
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0363
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2050
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1833
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Hilbert90IntegralIdelesOfMovedPrimes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1060
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1885
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1784
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1646
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCosetIndicatorReadingSphericalOffModulus
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ClassSumPin
import Formalism.LocalRingCardinality.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0493
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0158
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0553
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1797
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1639
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2024
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2051
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1481
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1123
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2053
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthCond
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TraceLatticeLeThetaLatticeAtPlace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0325

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedTensorFactorCoeffValuationLossLeAwayPrime
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)
open MeasureTheory ValuativeRel GlobalTheory.UnfoldLoss

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

noncomputable section

namespace GlobalTheory.MovedTwist

open Formalism.L2.Host GlobalTheory.IndefiniteRowSideFullHecke.CentralInvolutionRing GlobalTheory.ChiUnit

theorem unitOff_loc {L : Type} [Field L] [NumberField L] (χ : HChar L) {I : Type} [Fintype I] {φ : I → L →+* ℂ} {n : I → ℤ}
    (hinf : χ.HasInf φ n) (v : HeightOneSpectrum (𝓞 L)) {q : ℕ} (hq : (q : 𝓞 L) ∈ v.asIdeal) (x : (v.adicCompletion L)ˣ) :
    UnitOff q ((χ.loc v x : ℂˣ) : ℂ) := by
  obtain ⟨N, hN, hu⟩ := GlobalTheory.Corev.UnrPow.exists_pow_unrAt L χ
  have hinf' : (χ ^ N).HasInf φ fun i => n i * N := fun k => by
    have e : (χ ^ N).inf k = χ.inf k ^ N := rfl
    rw [e, Units.val_pow_eq_pow_val, hinf k, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [zpow_mul, zpow_natCast]
  have hv := GlobalTheory.ValUnit.unitOff_val L (χ ^ N) I φ _ v q hinf' (by simp [hu]) (fun w x hx _ => hu w x hx) (hu v) hq
  refine unitOff_of_pow hN ?_
  have e : ((χ.loc v x : ℂˣ) : ℂ) ^ N = (((χ ^ N).loc v x : ℂˣ) : ℂ) := by
    rw [← Units.val_pow_eq_pow_val]; rfl
  rw [e]
  set u : (v.adicCompletion L)ˣ := atFin v (unif v) with hudef
  have h0 : Valued.v (x : v.adicCompletion L) ≠ 0 := by simp
  have hu1 : Valued.v (u : v.adicCompletion L) = WithZero.exp (-1 : ℤ) := unif_spec v
  have hx : Valued.v (x : v.adicCompletion L) = WithZero.exp (WithZero.log (Valued.v (x : v.adicCompletion L))) :=
    (WithZero.exp_log h0).symm
  obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v (((x * u ^ m : (v.adicCompletion L)ˣ)) : v.adicCompletion L) = 1 := by
    refine ⟨WithZero.log (Valued.v (x : v.adicCompletion L)), ?_⟩
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hx, hu1, ← WithZero.exp_zsmul, ← WithZero.exp_add]
    simp
  have hx' : x = (x * u ^ m) * u ^ (-m) := by
    rw [mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]
  rw [hx', map_mul, hu v _ hm, one_mul, map_zpow, Units.val_zpow_eq_zpow_val]
  exact unitOff_zpow hv _

theorem unitOff_sqrt_absNorm {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L)) {q : ℕ} (hq0 : q ≠ 0)
    (hq : (q : 𝓞 L) ∈ v.asIdeal) : UnitOff q ((Real.sqrt (Ideal.absNorm v.asIdeal) : ℝ) : ℂ) := by
  refine unitOff_of_pow two_pos ?_
  rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]
  have h := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 hq)
  rw [Ideal.absNorm_span_natCast] at h
  obtain ⟨b, hb⟩ := h
  have hi : ∀ a : ℕ, IsIntegral ℤ (a : ℂ) := fun a => by
    simpa using isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (a : ℤ))
  refine unitOff_of_mul_eq (m := Module.finrank ℤ (𝓞 L)) (hi _) (hi b) ?_ hq0
  rw [← Nat.cast_mul, ← hb, Nat.cast_pow]

variable {D : D7}

theorem unitOff_apow_half {P : Pl D.host.E} {q : ℕ} (hq0 : q ≠ 0) (hq : (q : 𝓞 D.host.E) ∈ P.asIdeal) (x : (Kw P)ˣ) (z : ℤ) :
    UnitOff q (apow x ((z : ℂ) / 2)) := by
  obtain ⟨n, hn⟩ := GlobalTheory.MovedField.exists_zpow_unit P x
  have h1 : valuation (Kw P) (((x * unifAt P ^ n : (Kw P)ˣ)) : Kw P) = 1 := (Good.isEquiv_Kw P).eq_one_iff_eq_one.2 hn
  have hx : x = (x * unifAt P ^ n) * unifAt P ^ (-n) := by
    rw [mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]
  rw [hx, apow_mul, apow_of_valuation_eq_one h1, one_mul, apow_zpow, (isUnif_unifAt P).apow_eq,
    GlobalTheory.LFun.SatBoundGL.resCard_completion]
  have e1 : -(((-n : ℤ) : ℂ) * ((z : ℂ) / 2)) = ((((n * z : ℤ) : ℝ) / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [e1, GlobalTheory.MovedField.natCast_cpow_half]
  exact unitOff_zpow (unitOff_sqrt_absNorm P hq0 hq) _

theorem lossLe_unit_mul {w : PlL D} {q : ℕ} (hw : (q : 𝓞 D.what₂.LL) ∉ w.asIdeal) {u z : ℂ} {c : ℝ}
    (hu : u ∈ D.what₂.embLL.fieldRange) (hq : UnitOff q u) (hz : LossLe w z c) : LossLe w (u * z) c := by
  obtain ⟨y, rfl⟩ := hu
  obtain ⟨y', rfl, h'⟩ := hz
  refine ⟨y * y', map_mul _ _ _, ?_⟩
  by_cases h0 : y' = 0
  · exact Or.inl (by rw [h0, mul_zero])
  have h' := h'.resolve_left h0
  obtain ⟨hy, k, hk, -⟩ := hq
  have hy0 : y ≠ 0 := fun e => hy (by rw [e, map_zero])
  have hq0 : (q : D.what₂.LL) ≠ 0 := by
    have : q ≠ 0 := fun e => hw (by rw [e, Nat.cast_zero]; exact zero_mem _)
    exact_mod_cast this
  have hint : IsIntegral ℤ ((q : D.what₂.LL) ^ k * y) := by
    rw [← isIntegral_algHom_iff D.what₂.embLL.toIntAlgHom D.what₂.embLL.injective]
    simpa using hk
  have hqk : ((q ^ k : ℕ) : 𝓞 D.what₂.LL) ∉ w.asIdeal := fun h => hw (w.isPrime.mem_of_pow_mem k (by simpa using h))
  have h1 : vw w ((q ^ k : ℕ) : D.what₂.LL) = 0 := by
    have h0 : ((q ^ k : ℕ) : 𝓞 D.what₂.LL) ≠ 0 := fun e => hqk (e ▸ zero_mem _)
    have h1 := Formalism.EigenvalueLevelCeiling.intValuation_eq_exp' w _ h0
    rw [(w.intValuation_eq_one_iff).2 hqk, ← WithZero.exp_zero] at h1
    have h2 := WithZero.exp_injective h1
    have h3 : (((q ^ k : ℕ) : 𝓞 D.what₂.LL) : D.what₂.LL) = ((q ^ k : ℕ) : D.what₂.LL) := by simp
    rw [h3] at h2
    omega
  have h2 : 0 ≤ vw w ((q : D.what₂.LL) ^ k * y) := Formalism.DivisionValues.ValuationRepresentative.vw_int_nonneg w (⟨_, hint⟩ : 𝓞 D.what₂.LL)
  rw [Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ (pow_ne_zero _ hq0) hy0, ← Nat.cast_pow, h1, zero_add] at h2
  refine Or.inr ?_
  rw [Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ hy0 h0, Int.cast_add]
  have h3 : (0 : ℝ) ≤ (vw w y : ℝ) := by exact_mod_cast h2
  linarith

def UnitIn (K : Subfield ℂ) (q : ℕ) (u : ℂ) : Prop := u ∈ K ∧ UnitOff q u

theorem UnitIn.mul {K : Subfield ℂ} {q : ℕ} {u v : ℂ} (h : UnitIn K q u) (h' : UnitIn K q v) : UnitIn K q (u * v) :=
  ⟨mul_mem h.1 h'.1, unitOff_mul h.2 h'.2⟩

theorem UnitIn.inv {K : Subfield ℂ} {q : ℕ} {u : ℂ} (h : UnitIn K q u) : UnitIn K q u⁻¹ := ⟨inv_mem h.1, unitOff_inv h.2⟩

theorem UnitIn.pow {K : Subfield ℂ} {q : ℕ} {u : ℂ} (h : UnitIn K q u) (n : ℕ) : UnitIn K q (u ^ n) :=
  ⟨pow_mem h.1 n, unitOff_pow h.2 n⟩

theorem unitIn_one (K : Subfield ℂ) (q : ℕ) : UnitIn K q 1 := ⟨one_mem K, unitOff_one q⟩

theorem unitIn_prod {α : Type*} {K : Subfield ℂ} {q : ℕ} (f : α → ℂ) :
    ∀ l : List α, (∀ a ∈ l, UnitIn K q (f a)) → UnitIn K q (l.map f).prod
  | [], _ => by simpa using unitIn_one K q
  | a :: l, h => by
    rw [List.map_cons, List.prod_cons]
    exact (h a List.mem_cons_self).mul (unitIn_prod f l fun b hb => h b (List.mem_cons_of_mem _ hb))

end GlobalTheory.MovedTwist

open GlobalTheory.MovedTwist GlobalTheory.MovedField Formalism.L2.Host GlobalTheory.ChiUnit in

theorem GlobalTheory.MovedTwist.moved_lossLe : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A) (CF b : ℝ),
    HidaSetting large₂ R F → ch.Is → ch.AtScale CF b → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ∀ β ∈ ch.S.supp t Φ, ∀ (P : locPl ch.G t),
    (P : Pl D.host.E) ∉ ch.G.pl.W0 → ∀ (w : PlL D), ((Formalism.EigenvalueLevelCeiling.plc (P : Pl D.host.E) : ℕ) : 𝓞 D.what₂.LL) ∉ w.asIdeal →
    ∀ (c : ℝ), 0 ≤ c → (∀ z, LossLe w (Tflip ch.W ch.S.B t Φ P z) c) →
    ∀ z, LossLe w (moved (locGrid ch.G t P) (keepAt ch.G P) ((repsAt ch.G t P).elt (β P)) (Tflip ch.W ch.S.B t Φ P) z) c := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch large₂ F CF b hS _ _ hF t Φ β _ P hP w hw c _ hT z
  set K : Subfield ℂ := D.what₂.embLL.fieldRange with hKdef
  set q : ℕ := Formalism.EigenvalueLevelCeiling.plc (P : Pl D.host.E) with hqdef
  have hq0 : q ≠ 0 := (Formalism.EigenvalueLevelCeiling.plc_prime _).ne_zero
  have hq : (q : 𝓞 D.host.E) ∈ (P : Pl D.host.E).asIdeal := Formalism.EigenvalueLevelCeiling.plc_mem _
  have hK : ∀ y : ℂ, y ∈ Set.range D.what₂.embLL ↔ y ∈ K := fun y => by
    rw [Set.mem_range, hKdef, RingHom.mem_fieldRange]
  have hsq : ((Real.sqrt (Ideal.absNorm (P : Pl D.host.E).asIdeal) : ℝ) : ℂ) ∈ K :=
    (hK _).1 (hF.sqrt P.1 (.inr ⟨t, P.2⟩))
  have hmu : ∀ j (x : (Kw P.1)ˣ), UnitIn K q (((locGrid ch.G t P).mu j x : ℂˣ) : ℂ) := fun j x => by
    show UnitIn K q ((((GlobalTheory.FunObj.muBase _ j * _).loc _) x : ℂˣ) : ℂ)
    rw [HChar.loc_mul, Units.val_mul]
    refine UnitIn.mul ?_ ⟨(hK _).1 (hF.chars.xi t _ x), ?_⟩
    · rcases j with _ | j
      · simpa [GlobalTheory.FunObj.muBase] using unitIn_one K q
      · rw [GlobalTheory.FunObj.muBase]
        split_ifs with hj
        · obtain ⟨n, -, hn⟩ := (R.toLevCh.C.isMu0 ⟨j, hj⟩).inf
          exact ⟨(hK _).1 (hF.chars.mu0 ⟨j, hj⟩ _ x), unitOff_loc _ hn _ hq x⟩
        · simpa using unitIn_one K q
    · obtain ⟨n, hn, ho⟩ := hS.core.lev.xi_fin t
      refine unitOff_of_pow_eq_one q hn ?_
      have : ((R.toLevCh.xiH t) ^ n).loc P.1 x = 1 := by rw [show (R.toLevCh.xiH t) ^ n = 1 from ho]; rfl
      rw [← Units.val_pow_eq_pow_val]
      exact congrArg Units.val this
  have hchi : ∀ i, 1 ≤ i → i ≤ D.R.m → ∀ x : (Kw P.1)ˣ, UnitIn K q (((locGrid ch.G t P).chi i x : ℂˣ) : ℂ) :=
    fun i h1 h2 x => ⟨(hK _).1 (hF.chars.chi i h1 h2 _ x), unitOff_loc _ (ch.G.ch.inf i h1 h2) _ hq x⟩
  have heta : ∀ x : (Kw P.1)ˣ, UnitIn K q (((locGrid ch.G t P).eta x : ℂˣ) : ℂ) := fun x => by
    have hu := R.toLevCh.C.isEta.unr P.1
    obtain ⟨y, hy⟩ := hF.chars.eta P.1 hu
    exact ⟨loc_mem_of_unrAt hu (hy ▸ (hK _).1 ⟨y, rfl⟩) hsq x, unitOff_loc _ R.toLevCh.C.isEta.inf _ hq x⟩
  have hkap : ∀ e ∈ oppositePath D.R.m, ∀ X (x : (Kw P.1)ˣ), UnitIn K q (((locGrid ch.G t P).kappa e X x : ℂˣ) : ℂ) := by
    intro e he X x
    rw [Grid.kappa, MonoidHom.div_apply, MonoidHom.pow_apply, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val, div_eq_mul_inv]
    refine UnitIn.mul ?_ ((heta x).pow _).inv
    rcases GlobalTheory.FunObj.mem_oppositePath.1 he with ⟨i, hi, rfl⟩ | ⟨j, -, rfl⟩
    · exact hchi _ (by show 1 ≤ D.R.m - i; omega) (by show D.R.m - i ≤ D.R.m; omega) x
    · exact hmu _ x
  have hap : ∀ (x : (Kw P.1)ˣ) (n : ℕ), UnitIn K q (apow x ((n : ℂ) / 2)) ∧ UnitIn K q (apow x (-(n : ℂ) / 2)) := fun x n =>
    ⟨⟨by simpa using apow_half_mem hsq x n, by simpa using unitOff_apow_half hq0 hq x n⟩,
      by simpa using apow_half_mem hsq x (-n), by simpa using unitOff_apow_half hq0 hq x (-n)⟩
  have hedge : ∀ g, ∀ e ∈ oppositePath D.R.m, UnitIn K q ((locGrid ch.G t P).edgeFactor .one g e) := by
    intro g e he
    rw [Grid.edgeFactor, Units.val_inv_eq_inv_val]
    exact (((hkap e he _ _).mul (hkap e he _ _).inv).mul (hap _ _).1).mul (hap _ _).2
  have hk : keepAt ch.G (P : Pl D.host.E) = true := by
    classical
    simp [keepAt, hP]
  have hg := unitIn_prod _ _ (hedge ((repsAt ch.G t P).elt (β P)))
  simp only [moved, Grid.pathAct, hk, if_true, one_mul]
  exact lossLe_unit_mul hw hg.1 hg.2 (hT _)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NFunAddOneLtEExpAddCen
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.FrobeniusOrbits
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open GlobalTheory.ChiGrid Formalism.L2.Host

namespace GlobalTheory.BigTop.Fun

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts}

theorem natCast_mem_of_under {w : HeightOneSpectrum (𝓞 D.host.E)} {p : ℕ}
    (h : ((p : ℕ) : 𝓞 D.host.F) ∈ (w.under (𝓞 D.host.F)).asIdeal) : ((p : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := by
  have h1 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (p : 𝓞 D.host.F) ∈ w.asIdeal := h
  rwa [map_natCast] at h1

theorem natCast_mem_under {w : HeightOneSpectrum (𝓞 D.host.E)} {p : ℕ}
    (h : ((p : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal) : ((p : ℕ) : 𝓞 D.host.F) ∈ (w.under (𝓞 D.host.F)).asIdeal := by
  show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (p : 𝓞 D.host.F) ∈ w.asIdeal
  rwa [map_natCast]

theorem nFun_add_one_lt_eExp_add_cen (C : ℝ) (j a : Fin D.R.m) (g : D.R.Psi) :
    (BlochKatoReduction.Gen.NFun D.R : ℚ) + 1 < eExp D j g + (cen D C (D.eTau.symm g) (a.1 + 1) : ℚ) := by
  have h1 := GlobalTheory.LamTie.e_add_v_two_pos (D.hc (D.eTau.symm g)) (sLen D) (gap D C) 0 j
  have h2 := Int.lt_floor_add_one
    ((GlobalTheory.SignedHC.GridData.ofHCParam (D.hc (D.eTau.symm g)) (sLen D) (gap D C) 0).mid (a.1 + 1))
  have h3 := (GlobalTheory.SignedHC.GridData.ofHCParam (D.hc (D.eTau.symm g)) (sLen D) (gap D C) 0).mid_eq (i := a.1 + 1) (by omega)
  have h4 : (GlobalTheory.SignedHC.GridData.ofHCParam (D.hc (D.eTau.symm g)) (sLen D) (gap D C) 0).a (a.1 + 1) =
      ((GlobalTheory.SignedHC.GridData.ofHCParam (D.hc (D.eTau.symm g)) (sLen D) (gap D C) 0).v 2 : ℚ) + 1 / 2 +
        ((D.R.m : ℚ) + 1 - ((a.1 + 1 : ℕ) : ℚ)) * (gap D C : ℚ) := rfl
  have h5 : ((GlobalTheory.SignedHC.GridData.ofHCParam (D.hc (D.eTau.symm g)) (sLen D) (gap D C) 0).ga : ℚ) = gap D C := rfl
  have h6 := (isLeast_gap D C).1.2.1
  have h7 : bigN D ≤ bigN D ^ 3 := Nat.le_self_pow (by norm_num) _
  have h8 : ((bigN D + 2 : ℕ) : ℚ) ≤ gap D C := by exact_mod_cast (by omega)
  have h9 : ((a.1 + 1 : ℕ) : ℚ) ≤ D.R.m := by exact_mod_cast a.2
  have h10 : (0 : ℚ) ≤ gap D C := by positivity
  have h11 : (gap D C : ℚ) ≤ ((D.R.m : ℚ) + 1 - ((a.1 + 1 : ℕ) : ℚ)) * (gap D C : ℚ) := by nlinarith
  have h12 : BlochKatoReduction.Gen.NFun D.R = bigN D := GlobalTheory.LamTie.nFun_eq_bigN D
  rw [h12]
  unfold eExp cen
  push_cast at h8
  linarith

theorem lamOf_ok (G : GridData Lc sc) (hP : GlobalTheory.LamTie.PlacesOk D.host (q0 D) (G.pl.w G.pl.v0)) : (lamOf G).Ok := by
  have hw0 : (G.pl.w G.pl.v0).under (𝓞 D.host.F) = G.pl.v0 := G.pl.under_w (G.pl.mem_S0_of_sum_eq.2 (Or.inl rfl))
  have hS1 : ∀ w : HeightOneSpectrum (𝓞 D.host.E), GlobalTheory.LamTie.Over4 D.host w → w.under (𝓞 D.host.F) ∈ S1 D := by
    intro w h
    rw [S1_mem_OmF]
    rcases h with ⟨k, hk⟩ | hk | hk
    · fin_cases k
      · exact Or.inl (natCast_mem_under hk)
      · exact Or.inr (Or.inl (natCast_mem_under hk))
    · exact Or.inr (Or.inr (Or.inl (natCast_mem_under hk)))
    · exact Or.inr (Or.inr (Or.inr (natCast_mem_under hk)))
  have hOv : ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) ∈ S1 D → GlobalTheory.LamTie.Over4 D.host w := by
    intro w h
    rcases (S1_mem_OmF D).1 h with h | h | h | h
    · exact Or.inl ⟨0, natCast_mem_of_under h⟩
    · exact Or.inl ⟨1, natCast_mem_of_under h⟩
    · exact Or.inr (Or.inl (natCast_mem_of_under h))
    · exact Or.inr (Or.inr (natCast_mem_of_under h))
  refine ⟨hP, fun a => ?_, fun j a g => nFun_add_one_lt_eExp_add_cen sc.cGap j a g⟩
  have a1 : 1 ≤ a.1 + 1 := by omega
  have a2 : a.1 + 1 ≤ D.R.m := a.2
  refine ⟨GlobalTheory.ChrEqUnique.isUnitary_of_chrEq D _ _ (G.ch.chi_eq _ a1 a2), G.ch.triv _ a1 a2, lamOf_hasInfQ G a,
    fun w h4 h0 => ?_, fun w h4 => ?_, fun w he => ?_⟩
  · refine G.ch.unr _ a1 a2 w fun hw => ?_
    rcases G.pl.mem_S0_of_sum_eq.1 hw with h | h
    · exact h0 (h.trans hw0.symm)
    · exact h4 (hOv w h)
  · obtain ⟨l2, l1⟩ := G.ch.lev1 _ a1 a2 w (hS1 w h4)
    exact GlobalTheory.LamTie.GridCharacters.expAt_succ (n := 1) l2 l1
  · have e : w.under (𝓞 D.host.F) = G.pl.v0 := (show w.under (𝓞 D.host.F) = (G.pl.w G.pl.v0).under (𝓞 D.host.F) from he).trans hw0
    obtain ⟨l1, l0⟩ := G.ch.lev0 _ a1 a2 w e
    exact GlobalTheory.LamTie.GridCharacters.expAt_succ (n := 0) l1 fun h => l0 (((G.ch.chiH _).unrAt_iff w).2 h)

end GlobalTheory.BigTop.Fun

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonSplitSupportedFinitePartIntegralInertStatement
section
open NumberField IsDedekindDomain
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonSplitSupported_finitePart_integral_inert : ∀ {D : Formalism.BasicNotions.D7} (V : Formalism.BasicNotions.TH.HSp D) (hG : V.gram = 1) (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F), GlobalTheory.WeilParts.NonSplitAt D v ε → ∀ g : Formalism.L2.Theta.GA D V, GlobalTheory.WeilParts.SuppPl ε V g → (∀ y : Fin V.rank → TensorProduct D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E, y ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E ((Formalism.MainNotions.StandardLatticesGL3.stdL D V.rank : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) : Set (Fin V.rank → D.host.E)) ↔ (Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram g).mulVec y ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E ((Formalism.MainNotions.StandardLatticesGL3.stdL D V.rank : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) : Set (Fin V.rank → D.host.E))) → Formalism.MainNotions.StandardLatticesGL3.SuppInert D (GlobalTheory.BotClassDict.finStd V hG g : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) ∧ Formalism.MainNotions.StandardLatticesGL3.IntG D (GlobalTheory.BotClassDict.finStd V hG g : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) := by
  first | exact @GlobalTheory.InertLocalPoint.suppInert_and_intG | exact GlobalTheory.InertLocalPoint.suppInert_and_intG | (intros; apply GlobalTheory.InertLocalPoint.suppInert_and_intG <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizedPartOfClassSum
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind GlobalTheory.BigTop

namespace GlobalTheory.Fc.Ind

theorem pNmj_of_pDiv_of_classSumPin :
    ∀ (D : D7) (O : Obj D) (c : ℝ) (b : Part D O c),
      PDiv D O c b → GlobalTheory.ExportPin.ClassSumPin b.pt → PNmj D O c b :=
  fun D O _ b hdiv hpin =>
    GlobalTheory.T.lattice_family_adoption_fourth D _ _ _ _ _ _ _ O.ex _ _ _ _ _ _ b.B b.pins b.Rr O.ex.nch_tie hdiv hpin

end GlobalTheory.Fc.Ind
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OnClausesWithErrorOfSplitPart
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn
open GlobalTheory.CharRealise

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BigOn

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)

set_option maxHeartbeats 4000000 in

theorem iw_split_eq (j : Fin D.R.m) (t : p.P.A3.fam3.base3.Tup) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) :
    (p.S false).Iw j t w = (S2 p).Iw j t w := by
  show ((p.R.toCx3 p.F).data p.F.cr false).Iw j t w = _
  rw [toCx3_eq_one p.R p.F p.phsOne]
  rfl

set_option maxHeartbeats 4000000 in

theorem d_split_eq : (p.S false).D = (S2 p).D := by
  show ((p.R.toCx3 p.F).data p.F.cr false).D = _
  rw [toCx3_eq_one p.R p.F p.phsOne]
  rfl

set_option maxHeartbeats 4000000 in

theorem onWith_of_split : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Csz : ℝ) (p : PtAt ex Csz), ∀ (C CH : ℝ) (err : HeightOneSpectrum (𝓞 D.what₂.LL) → Fin D.R.m → ℝ), ONwith (S2 p) ((R2 p).num (F2 p) C CH) err → ONwith (p.S false) (p.N C CH) err ∧ (p.S false).D = (S2 p).D := by
  intro D L hT Gi Gl Kc Y cX ex Csz p C CH err h
  obtain ⟨h1, h2, h3⟩ := h
  have eD := d_split_eq p
  refine ⟨⟨fun w hw => ?_, fun w hw j => h2 w hw j, fun j => h3 j⟩, eD⟩
  have := h1 w hw
  simp only [iw_split_eq p, eD]
  exact this

end GlobalTheory.BigOn

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelExtensionSecond
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdTh.SerAll

open NumberField Matrix Complex MeasureTheory IsDedekindDomain in
open scoped TensorProduct Classical ComplexConjugate in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar in

theorem _root_.GlobalTheory.AdTh.SerAll.lieFac_eq_pow {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) {x : ℝ} (hx : 0 < x)
    (a : (E →+* ℂ) × ℕ → ℕ) :
    _root_.Formalism.L2.Pj.lieFac Dw x a = (Real.sqrt (2 * Real.pi * x))⁻¹ ^ _root_.GlobalTheory.PtId.degW Dw a := by
  have hy : 0 < 2 * Real.pi * x := by positivity
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hy.le, ← Real.rpow_natCast, ← Real.rpow_mul hy.le,
    Real.rpow_def_of_pos hy]
  unfold _root_.Formalism.L2.Pj.lieFac _root_.GlobalTheory.PtId.degW
  congr 1
  push_cast
  ring

set_option maxHeartbeats 1000000 in

theorem exists_serOf : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.Char F → TieIn T R κ v₀ → IoExt R → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ∀ cc, CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.U ((i : ℕ) + 1) O.s0) O.dict O.mu (T.x₀ ((i : ℕ) + 1) O.s0) (R.ωP i A.μ0) (R.vacP i) cc → ∃ u : ℂ, ‖u‖ = 1 ∧ SerOf O (κ i) (v₀ i (sg0 D A)) (u • cc) 1 := by
  intro _ D G _ _ Pl0 T0 A T _ R F κ v₀ hR hT hI i Tp tup O hP cc hcc
  have hs : O.s0 = T.toCore.σ₀ := sOv_eq _ _ _
  obtain ⟨h1, h2, -⟩ := GlobalTheory.PtId.dict_cast T hT.laws _ (inR i) O.s0 (hs ▸ T.toCore.good_σ₀) (Wc D i) O.hV (rank_Wc i)
  obtain ⟨δ, hδ⟩ := GlobalTheory.T.lattice_isometry_sign_third D G Pl0 T0 A _ R F hR i hP.lift.std _ _ (iotaW T i) h1 h2
  obtain ⟨ka, hka, hio⟩ := GlobalTheory.T.oscillator_model_extension_first D G Pl0 T0 A T R F κ v₀ hR hT hI i Tp tup O hP
  obtain ⟨c0, hc0, hcov⟩ := GlobalTheory.T.oscillator_model_values_fifth D G Pl0 T0 A T R F κ v₀ hR hT i Tp tup O hP
  have hd : ‖((δ : ℤ) : ℂ)‖ = 1 := by
    rcases Int.units_eq_one_or δ with rfl | rfl <;> simp
  have hu : ‖ka * (-((δ : ℤ) : ℂ)) ^ GlobalTheory.PtId.degW (T.Q.Dw ((i : ℕ) + 1)) (wtA (κ i)) * c0⁻¹‖ = 1 := by
    rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_inv, hka, hc0, hd]
    simp
  refine ⟨_, hu, fun k => ?_, norm_one, fun t h J' hrep y x hpl f _ hf g => ?_⟩
  · rw [Pi.smul_apply, smul_eq_mul, norm_mul, hu, hcc.1 k, one_mul]
  have hne : c0 ≠ 0 := norm_ne_zero_iff.1 (hc0 ▸ one_ne_zero)
  have hx : 0 < xiR D := norm_pos_iff.2 ((_root_.map_ne_zero _).2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D))
  have key := GlobalTheory.PtId.exact_identity hR hT O hP hio hδ hcov hcc t h J' hrep y x hpl f hf g
  refine mul_left_cancel₀ hne ?_
  rw [one_mul, key, lieFac_eq_pow _ hx, GlobalTheory.PtId.cmpConst, Pi.smul_apply, smul_eq_mul, neg_pow]
  have hre : rdU (GlobalTheory.PtId.unfO O) f (O.dict g).1 (O.dict g).2 =
      rdU (unfBC O.hle (T.U ((i : ℕ) + 1)) (inC O.c')) f (O.dict g).1 (O.dict g).2 := rfl
  rw [hre]
  generalize rdU (unfBC O.hle (T.U ((i : ℕ) + 1)) (inC O.c')) f (O.dict g).1 (O.dict g).2 = z
  rw [Complex.ofReal_pow, Complex.ofReal_inv]
  generalize ((Real.sqrt (2 * Real.pi * xiR D) : ℝ) : ℂ)⁻¹ ^ GlobalTheory.PtId.degW (T.Q.Dw ((i : ℕ) + 1)) (wtA (κ i)) = s
  have e : c0 * c0⁻¹ = 1 := mul_inv_cancel₀ hne
  linear_combination (-(ka * ((-1) ^ GlobalTheory.PtId.degW (T.Q.Dw ((i : ℕ) + 1)) (wtA (κ i)) * ((δ : ℤ) : ℂ) ^ GlobalTheory.PtId.degW (T.Q.Dw ((i : ℕ) + 1)) (wtA (κ i))) * cc (O.dict g).1 * s * O.mu g * z)) * e

end GlobalTheory.AdTh.SerAll
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairFunctionalNonvanishingStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_functional_nonvanishing : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ (Λ : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ) (c : Fin n → AE F E),
    (fun k => piW B.τ₁ (c k)) ≠ 0 →
    (∀ z : Fin d → AE F E, At (evFin F B.v₁) z → (∀ l, piW (B.τ₁.comp σ) (z l) = 0) →
      ∀ Ψ ∈ schA F (Fin n × Fin d), Λ (M.co.rho B.ψ (Matrix.vecMulVec c z) Ψ) = Λ Ψ) →
    ∀ Φ ∈ M.So B.ψ B.τ₁, Λ Φ = 0 := by
  first | exact @GlobalTheory.ThKSoKill.so_kill | exact GlobalTheory.ThKSoKill.so_kill | (intros; apply GlobalTheory.ThKSoKill.so_kill <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PtRealised
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Top GlobalTheory.Fc

namespace GlobalTheory.Fc.Ind

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem pt_realised {D : D7} {O : Obj D} {c : ℝ} (b : Part D O c) : b.pt.Realised :=
  ⟨b.R, b.S, b.B, b.pins, b.Rr, b.recPins, rfl⟩

theorem pt_pb {D : D7} {O : Obj D} {c : ℝ} (b : Part D O c) : b.pt.T.pb = b.pt.R.C.P.pb :=
  GlobalTheory.PinsFixHalf.pb_eq_of_pins b.pt.T b.pt.R.toRealDat b.pt.κ b.pt.v₀ b.pt.O b.pt.charW.base.lev b.pt.fw.laws b.pt.pins

theorem pt_ties0 : ∀ (D : D7) (O : Obj D) (c : ℝ) (b : Part D O c), b.pt.Realised ∧ b.pt.T.pb = b.pt.R.C.P.pb :=
  fun _ _ _ b => ⟨pt_realised b, pt_pb b⟩

end GlobalTheory.Fc.Ind

example : ∀ (D : D7) (O : Obj D) (c : ℝ) (b : Ind.Part D O c), b.pt.Realised ∧ b.pt.T.pb = b.pt.R.C.P.pb := GlobalTheory.Fc.Ind.pt_ties0
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedPlacesBoundChainTwoRunChainStatement
section
open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies GlobalTheory.BigOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedPlacesBoundChain_twoRunChain : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (R : RealDat D A J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie J R κ v₀) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (EX : ErrX D) (r : TwoRuns J G) (c : OnConst) (O : OnObj ((R.toCx F).data F.cr false) (Mir R) c), IsRec Tp hK EX F fw r O → ∀ (s : ℕ) (N : IndefNum A.fam.base) (C : ℝ), A.fam.Ok s → R.grp_levels F → R.grp_chiW → R.IsModels → R.tup_mu_conj → R.thP_thG → R.LUnif → BaseLinks R F → TwistedRational R F (fun _ => 1) → RankRows ((R.toCx F).data F.cr false) → LeafLevelSq O (Res R) D.R.f → LeafYBound O → LeafSup O → LeafSpan O → LeafLemmaS O → HasIndexBound O → LeafData O → GlobalTheory.TraceClassRank.RankAtPlaces O → LeafIdentity O → LeafTW2 O → HasTwistBound O → LeafShareI O → LeafBadShare O → LeafDepthGood N O → LeafDepthRam N O → LeafDepth2 N O → LeafDepthLevel N O → LeafPage O → LeafSizes O → LeafX O → LeafBad O → HasExpBound N O → c.CE ≤ C → ErrorConstantMatchesDefinition N O C → ∃ err, ONwith ((R.toCx F).data F.cr false) N err := by
  first | exact @GlobalTheory.OnAtPlacesBase.on_base_atPlaces | exact GlobalTheory.OnAtPlacesBase.on_base_atPlaces | (intros; apply GlobalTheory.OnAtPlacesBase.on_base_atPlaces <;> assumption)
end

