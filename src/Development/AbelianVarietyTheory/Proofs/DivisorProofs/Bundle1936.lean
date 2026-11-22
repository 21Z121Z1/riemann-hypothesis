import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1848
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralActionUnitCharacterEigen
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0288
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairNormPadicValuationBound
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.Bundle0003
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0365
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0005
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0318
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCosetOfIsTensor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoefficientBound
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0575
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0501
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0325
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1613
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1623
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.WeilDatumDoubleSpaceActsUnitScalarSeesawCM
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1917
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1833
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1829
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteWeilRepEqLatticeIntertwinerMulCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1916
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1876
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFinitePureTensors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1456

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitDetCharIndicatorMulIntegralFrame
section
open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

noncomputable section

namespace GlobalTheory.StdRead.CharMul

variable {D : D7}

theorem det_int {n : ℕ} {N : Matrix (Fin n) (Fin n) (EAf D)} (h : IsIntM N) :
    N.det ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  rw [Matrix.det_apply]
  refine Subring.sum_mem _ fun σ _ => ?_
  rw [Units.smul_def]
  exact Subring.zsmul_mem _ (Subring.prod_mem _ fun i _ => h (σ i) i) _

theorem ring_mul {R : Type} [CommRing R] {ε : R} (h : ε * ε = ε) (a b : R) :
    (1 - ε + ε * a) * (1 - ε + ε * b) = 1 - ε + ε * (a * b) := by
  linear_combination (1 - a - b + a * b) * h

theorem det_mul' {R : Type} [CommRing R] {k : ℕ} (A B : Matrix (Fin k) (Fin k) R) :
    (HMul.hMul A B).det = A.det * B.det :=
  Matrix.det_mul A B

theorem det_gl {R : Type} [CommRing R] {k : ℕ} (β : GL (Fin k) R) : β.val.det * (β⁻¹).val.det = 1 := by
  rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]

theorem isUnitDet_mul {e : AE D} (he : e * e = e) {k : ℕ} {A B C : Matrix (Fin k) (Fin k) (EAf D)}
    (h : C.det = A.det * B.det) {x y : (AE D)ˣ} (hx : IsUnitDet e A x) (hy : IsUnitDet e B y) :
    IsUnitDet e C (x * y) := by
  obtain ⟨hx1, hx2, hx3⟩ := hx
  obtain ⟨hy1, hy2, hy3⟩ := hy
  refine ⟨?_, ?_, ?_⟩
  · rw [Units.val_mul, map_mul, hx1, hy1, one_mul]
  · rw [Units.val_mul, map_mul, hx2, hy2, h]
    exact ring_mul (by rw [← map_mul, he]) _ _
  · rw [mul_inv_rev, Units.val_mul, map_mul]
    exact Subring.mul_mem _ hy3 hx3

private lemma eq_lr_take_drop_of_map_fst_eq_replicate {D : D7} : ∃ Ψ : AE D ≃+* (TensorProduct D.host.F D.host.E (Ainf D.host.F)) × EAf D,
    ∀ z, infPart D z = Algebra.TensorProduct.comm D.host.F D.host.E (Ainf D.host.F) (Ψ z).1 ∧
      toEAf D z = (Ψ z).2 := by
  refine ⟨((Algebra.TensorProduct.comm D.host.F (AF D.host.F) D.host.E).trans
    (Algebra.TensorProduct.prodRight D.host.F D.host.F D.host.E (Ainf D.host.F) (Af D.host.F))).toRingEquiv,
    fun z => ?_⟩
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => exact ⟨rfl, rfl⟩
  | add z z' h1 h2 =>
    constructor
    · simp only [map_add, Prod.fst_add, h1.1, h2.1]
    · simp only [map_add, Prod.snd_add, h1.2, h2.2]

private lemma units_eq_of_res_eq_of_le_iSup {D : D7} {z z' : AE D} (hi : infPart D z = infPart D z') (ht : toEAf D z = toEAf D z') :
    z = z' := by
  obtain ⟨Ψ, hΨ⟩ := eq_lr_take_drop_of_map_fst_eq_replicate (D := D)
  apply Ψ.injective
  refine Prod.ext ((Algebra.TensorProduct.comm D.host.F D.host.E (Ainf D.host.F)).injective ?_) ?_
  · rw [← (hΨ z).1, ← (hΨ z').1, hi]
  · rw [← (hΨ z).2, ← (hΨ z').2, ht]

private lemma exists_unit_infPart_one_toEAf_eq {D : D7} {u w : EAf D} (huw : u * w = 1) :
    ∃ x : (AE D)ˣ, infPart D (x : AE D) = 1 ∧ toEAf D (x : AE D) = u ∧ toEAf D ((x⁻¹ : (AE D)ˣ) : AE D) = w := by
  obtain ⟨Ψ, hΨ⟩ := eq_lr_take_drop_of_map_fst_eq_replicate (D := D)
  have hwu : w * u = 1 := by rw [mul_comm, huw]
  refine ⟨⟨Ψ.symm (1, u), Ψ.symm (1, w), ?_, ?_⟩, ?_, ?_, ?_⟩
  · apply Ψ.injective
    simp [huw]
  · apply Ψ.injective
    simp [hwu]
  · show infPart D (Ψ.symm (1, u)) = 1
    rw [(hΨ _).1, RingEquiv.apply_symm_apply, map_one]
  · show toEAf D (Ψ.symm (1, u)) = u
    rw [(hΨ _).2, RingEquiv.apply_symm_apply]
  · show toEAf D (Ψ.symm (1, w)) = w
    rw [(hΨ _).2, RingEquiv.apply_symm_apply]

theorem exists_isUnitDet {e : AE D} (he : e * e = e) (hE : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) {k : ℕ}
    {A : Matrix (Fin k) (Fin k) (EAf D)} {v : EAf D} (hv : v ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (h : A.det * v = 1) : ∃ x, IsUnitDet e A x := by
  have hε : toEAf D e * toEAf D e = toEAf D e := by rw [← map_mul, he]
  obtain ⟨x, hx1, hx2, hx3⟩ := exists_unit_infPart_one_toEAf_eq (u := 1 - toEAf D e + toEAf D e * A.det)
    (w := 1 - toEAf D e + toEAf D e * v) (by rw [ring_mul hε, h, mul_one, sub_add_cancel])
  refine ⟨x, hx1, hx2, ?_⟩
  rw [hx3]
  exact Subring.add_mem _ (Subring.sub_mem _ (Subring.one_mem _) hE) (Subring.mul_mem _ hE hv)

private lemma isUnitDet_unique' {D : D7} {e : AE D} {k : ℕ} {M : Matrix (Fin k) (Fin k) (EAf D)} {x x' : (AE D)ˣ}
    (hx : IsUnitDet e M x) (hx' : IsUnitDet e M x') : x = x' :=
  Units.ext (units_eq_of_res_eq_of_le_iSup (hx.1.trans hx'.1.symm) (hx.2.1.trans hx'.2.1.symm))

private lemma unitChar_eq_inv_of_isUnitDet {D : D7} (ν : (AE D)ˣ →* Circle) {e : AE D} {k : ℕ} {M : Matrix (Fin k) (Fin k) (EAf D)}
    {x : (AE D)ˣ} (hx : IsUnitDet e M x) : unitChar ν e M = (((ν x)⁻¹ : Circle) : ℂ) := by
  have hex : ∃ x, IsUnitDet e M x := ⟨x, hx⟩
  unfold unitChar
  rw [dif_pos hex, isUnitDet_unique' hex.choose_spec hx]

theorem unitChar_mul : ∀ {D : D7} (ν : (AE D)ˣ →* Circle) (e : AE D), e * e = e → toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E →
  ∀ {k : ℕ} (N : Matrix (Fin k) (Fin k) (EAf D)) (β : GL (Fin k) (EAf D)), IsIntM β.val → IsIntM (β⁻¹).val →
  unitChar ν e (HMul.hMul N β.val) = unitChar ν e N * unitChar ν e β.val := by
  intro D ν e he hE k N β hβ hβ'
  obtain ⟨y, hy⟩ := exists_isUnitDet he hE (det_int hβ') (det_gl β)
  obtain ⟨y', hy'⟩ := exists_isUnitDet he hE (det_int hβ) (by rw [mul_comm]; exact det_gl β)
  by_cases hN : ∃ x, IsUnitDet e N x
  · obtain ⟨x, hx⟩ := hN
    rw [unitChar_eq_inv_of_isUnitDet ν (isUnitDet_mul he (det_mul' N β.val) hx hy), unitChar_eq_inv_of_isUnitDet ν hx, unitChar_eq_inv_of_isUnitDet ν hy,
      map_mul, mul_inv, Circle.coe_mul]
  · have hNβ : ¬ ∃ x, IsUnitDet e (HMul.hMul N β.val) x := by
      rintro ⟨z, hz⟩
      exact hN ⟨_, isUnitDet_mul he (by rw [det_mul', mul_assoc, det_gl, mul_one]) hz hy'⟩
    unfold unitChar
    rw [dif_neg hN, dif_neg hNβ, zero_mul]

end GlobalTheory.StdRead.CharMul

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationProportionalityRatioLeBottomPairs
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormSum.LemmaC

open GlobalTheory.NormVal

theorem integralOver_cast {D : D7} {p m n : ℕ} (e : n = m) (h : GA D n) (hi : IntegralOver D p h) :
    IntegralOver D p (e ▸ h : GA D m) := by
  subst e; exact hi

theorem exists_cast_eq {D : D7} {p m n : ℕ} (e : n = m) (h' : GA D m) :
    ∃ h : GA D n, (e ▸ h : GA D m) = h' ∧ (IntegralOver D p h' → IntegralOver D p h) := by
  subst e; exact ⟨h', rfl, id⟩

theorem bd_intCast (p : ℕ) [Fact p.Prime] (n : ℤ) : Bd p 1 ((n : ℤ) : ℂ) := by
  have hm : ((n : ℤ) : ℂ) ∈ Qbar := intCast_mem _ n
  refine ⟨hm, fun lam => ?_⟩
  rw [lamC_of_mem lam hm]
  have e1 : (⟨(n : ℂ), hm⟩ : Qbar) = (n : Qbar) := Subtype.ext (by simp)
  rw [e1, map_intCast]
  exact IsUltrametricDist.norm_intCast_le_one _ n

set_option maxHeartbeats 1000000 in

theorem vw_le_of_bottom_pairs : ∀ (D : D7) (N : ℕ) (B : ℝ) (Q : ℕ) (S : Finset ℕ) (del_vp : ℕ → ℝ) (b : ℝ), GlobalTheory.NormSum.Inp D →
    GlobalTheory.NormSum.Exponents S del_vp b → GlobalTheory.NormSum.CoordInt D N B Q del_vp →
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (w : Formalism.PairingDivisionLocalBalance.Pl K) (p : ℕ) [Fact p.Prime],
    (p : 𝓞 K) ∈ w.asIdeal → ∀ (δ t0 : ℂ) (Q₁ Q₂ : ℕ), padicValNat p Q₁ ≤ padicValNat p Q →
    padicValNat p Q₂ ≤ padicValNat p Q →
    ∀ (P₁ P₁' : Pair D ⊤ δ t0 Q₁) (P₂ P₂' : Pair D ⊤ δ t0 Q₂), P₁.Small N B → P₁'.Small N B → P₂.Small N B →
    P₂'.Small N B → ∀ (hd₁ : P₁'.d = P₁.d) (hd₂ : P₂'.d = P₂.d) (b₁ b₂ v : ℂ)
    (M₁ : Tup D P₁.a P₁.d P₁.n → Tup D P₁'.a P₁'.d P₁'.n → ℤ) (M₂ : Tup D P₂'.a P₂'.d P₂'.n → Tup D P₂.a P₂.d P₂.n → ℤ),
    (∀ (h : GA D P₁.d) T, starRingEnd ℂ (P₁.coord h T) = b₁ * ∑ T', (M₁ T T' : ℂ) * P₁'.coord (hd₁ ▸ h) T') →
    (∀ (h : GA D P₂.d) T', P₂'.coord (hd₂ ▸ h) T' * b₂ = ∑ T, (M₂ T' T : ℂ) * starRingEnd ℂ (P₂.coord h T)) →
    b₂ ≠ 0 → v ∈ Qbar → (∀ lam : Qbar →+* ℂ_[p], ‖lamC lam v‖ = 1) →
    ∀ (γ z z' : K), b₁ = σ γ * b₂ * v → σ z = (P₁.norm : ℂ) → σ z' = (P₂'.norm : ℂ) → z ≠ 0 → z' ≠ 0 →
    (vw w γ : ℝ) ≤ vw w z + vw w z' + 6 * Formalism.PairingDivisionLocalBalance.wt S del_vp w := by
  intro D N B Q S del_vp b hI hE hC K _ _ _ σ w p _ hw δ t0 Q₁ Q₂ hQ₁ hQ₂ P₁ P₁' P₂ P₂' hs₁ hs₁' hs₂ hs₂' hd₁ hd₂ b₁ b₂ v M₁ M₂ hr₁ hr₂ hb₂ hv hv1 γ z z' hγ hz hz' hz0 hz0'
  have hp : p.Prime := Fact.out
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hp0 : (0 : ℝ) < p := by linarith
  set e : ℝ := del_vp p with he
  set r : ℝ := (p : ℝ) ^ e with hr
  have hr0 : 0 ≤ r := by positivity

  have hgam : ∀ {Q' : ℕ} (P : Pair D ⊤ δ t0 Q'), padicValNat p Q' ≤ padicValNat p Q → P.Small N B →
      ∀ g, Bd p r ((gam D P.J g : ℂ)⁻¹) := fun P hQ' hS g => by
    obtain ⟨-, h2, -⟩ := hC δ t0 p _ hQ' P hS
    exact (Bd.inv_nat (h2 g).1 dvd_rfl).mono (Real.rpow_le_rpow_of_exponent_le hp1 (h2 g).2)

  have hco : ∀ {Q' : ℕ} (P : Pair D ⊤ δ t0 Q'), padicValNat p Q' ≤ padicValNat p Q → P.Small N B →
      ∀ g, IntegralOver D p g → ∀ T, Bd p r (P.coord g T) := fun P hQ' hS g hg T =>
    (hC δ t0 p _ hQ' P hS).2.2 g hg T

  have hb₁ : b₁ ≠ 0 := by
    rintro rfl
    have h0 : P₁.norm = 0 := by
      unfold Pair.norm
      refine finsum_eq_zero_of_forall_eq_zero fun q => ?_
      have : P₁.sq q.out = 0 := by
        unfold Pair.sq
        refine Finset.sum_eq_zero fun T _ => ?_
        have := hr₁ q.out T
        rw [zero_mul, map_eq_zero] at this
        rw [this, norm_zero]; norm_num
      rw [this, mul_zero]
    apply hz0
    apply σ.injective
    rw [hz, h0, map_zero, Complex.ofReal_zero]
  have hγ0 : γ ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_mul, zero_mul] at hγ
    exact hb₁ hγ
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hγ
    exact hb₁ hγ

  have hA : Bd p (r * (r * (1 * r))) ((P₁.norm : ℂ) * b₁⁻¹) := by
    obtain ⟨h1, -, -⟩ := hC δ t0 p Q₁ hQ₁ P₁ hs₁
    choose s hs1 hs2 using h1
    rw [(GlobalTheory.T.definiteThetaPair_terms_norms_independent_representatives D hI ⊤ δ t0 Q₁ P₁.crv P₁.pt0 P₁ P₁.level_pos).2.2.2.1 s hs1]
    refine finsum_induction (fun x : ℝ => Bd p (r * (r * (1 * r))) ((x : ℂ) * b₁⁻¹)) ?_
      (fun x y hx hy => ?_) (fun q => ?_)
    · beta_reduce; rw [Complex.ofReal_zero, zero_mul]; exact Bd.zero (by positivity)
    · beta_reduce at hx hy ⊢; rw [Complex.ofReal_add, add_mul]; exact hx.add hy
    · beta_reduce; rw [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast, mul_assoc]
      refine Bd.mul (hgam P₁ hQ₁ hs₁ _) ?_
      unfold Pair.sq
      rw [Complex.ofReal_sum, Finset.sum_mul]
      refine Finset.sum_induction _ _ (fun x y => Bd.add) (Bd.zero (by positivity)) (fun T _ => ?_)
      have e1 : ((‖P₁.coord (s q) T‖ ^ 2 : ℝ) : ℂ) * b₁⁻¹ =
          P₁.coord (s q) T * ∑ T', (M₁ T T' : ℂ) * P₁'.coord (hd₁.symm ▸ s q) T' := by
        rw [Complex.ofReal_pow, ← Complex.mul_conj', hr₁]
        field_simp
      rw [e1]
      refine (hco P₁ hQ₁ hs₁ _ (hs2 q) T).mul ?_
      refine Finset.sum_induction _ _ (fun x y => Bd.add) (Bd.zero (by positivity)) (fun T' _ => ?_)
      exact (bd_intCast p _).mul (hco P₁' hQ₁ hs₁' _ (integralOver_cast hd₁.symm _ (hs2 q)) T')

  have hB : Bd p (r * (r * (1 * r))) ((P₂'.norm : ℂ) * b₂) := by
    obtain ⟨h1, -, -⟩ := hC δ t0 p Q₂ hQ₂ P₂' hs₂'
    choose s hs1 hs2 using h1
    rw [(GlobalTheory.T.definiteThetaPair_terms_norms_independent_representatives D hI ⊤ δ t0 Q₂ P₂'.crv P₂'.pt0 P₂' P₂'.level_pos).2.2.2.1 s hs1]
    refine finsum_induction (fun x : ℝ => Bd p (r * (r * (1 * r))) ((x : ℂ) * b₂)) ?_
      (fun x y hx hy => ?_) (fun q => ?_)
    · beta_reduce; rw [Complex.ofReal_zero, zero_mul]; exact Bd.zero (by positivity)
    · beta_reduce at hx hy ⊢; rw [Complex.ofReal_add, add_mul]; exact hx.add hy
    · beta_reduce; rw [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast, mul_assoc]
      refine Bd.mul (hgam P₂' hQ₂ hs₂' _) ?_
      unfold Pair.sq
      rw [Complex.ofReal_sum, Finset.sum_mul]
      refine Finset.sum_induction _ _ (fun x y => Bd.add) (Bd.zero (by positivity)) (fun T' _ => ?_)
      obtain ⟨h, hh, hi⟩ := exists_cast_eq (p := p) hd₂.symm (s q)
      have e1 : ((‖P₂'.coord (s q) T'‖ ^ 2 : ℝ) : ℂ) * b₂ =
          (starRingEnd ℂ) (P₂'.coord (s q) T') * ∑ T, (M₂ T' T : ℂ) * (starRingEnd ℂ) (P₂.coord h T) := by
        rw [← hr₂ h T', hh, Complex.ofReal_pow, ← Complex.mul_conj']
        ring
      rw [e1]
      refine (hco P₂' hQ₂ hs₂' _ (hs2 q) T').conj.mul ?_
      refine Finset.sum_induction _ _ (fun x y => Bd.add) (Bd.zero (by positivity)) (fun T _ => ?_)
      exact (bd_intCast p _).mul (hco P₂ hQ₂ hs₂ _ (hi (hs2 q)) T).conj

  set x : K := z * z' * γ⁻¹ with hx
  have hx0 : x ≠ 0 := mul_ne_zero (mul_ne_zero hz0 hz0') (inv_ne_zero hγ0)
  have hσx : σ x = ((P₁.norm : ℂ) * b₁⁻¹) * ((P₂'.norm : ℂ) * b₂) * v := by
    have hσγ : σ γ ≠ 0 := (map_ne_zero σ).2 hγ0
    rw [hx, map_mul, map_mul, map_inv₀, hz, hz', hγ]
    field_simp
  have hX : Bd p (r * (r * (1 * r)) * (r * (r * (1 * r))) * 1) (σ x) := by
    rw [hσx]
    exact (hA.mul hB).mul ⟨hv, fun lam => (hv1 lam).le⟩
  have hpow : r * (r * (1 * r)) * (r * (r * (1 * r))) * 1 = (p : ℝ) ^ (6 * e) := by
    rw [mul_comm 6 e, Real.rpow_mul hp0.le, hr]
    norm_num
    ring
  have key := GlobalTheory.PadicPlaceBound.neg_mul_vw_le_vw K σ x p w (6 * e) hx0 hw fun lam =>
    (hX.2 lam).trans (le_of_eq hpow)
  have hvx : (Formalism.DivisionValues.vw w x : ℝ) = Formalism.DivisionValues.vw w z + Formalism.DivisionValues.vw w z' - Formalism.DivisionValues.vw w γ := by
    rw [hx, Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ (mul_ne_zero hz0 hz0') (inv_ne_zero hγ0),
      Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ hz0 hz0', Formalism.DivisionValues.ValuationRepresentative.vw_inv]
    push_cast; ring
  rw [hE.wt_eq hp w hw]
  rw [hvx] at key
  linarith

end GlobalTheory.NormSum.LemmaC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VariablesUniformizerPowerLatticeBasisOpenVolumeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)
open MeasureTheory ValuativeRel GlobalTheory.UnfoldLoss

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.variablesUniformizerPowerLattice_basis_open_volume : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (G : Grid k) (ν : Measure k), IsUnitVol ν → ∀ ϖ : kˣ, IsUnif ϖ →
    (∀ s ∈ nhds (0 : Vars G), ∃ n : ℕ, (varLat G ϖ n : Set (Vars G)) ⊆ s) ∧
    ∀ n : ℕ, IsOpen (varLat G ϖ n : Set (Vars G)) ∧ varsVol G ν (varLat G ϖ n : Set (Vars G)) ≠ ⊤ ∧
      (varsVol G ν).real (varLat G ϖ n : Set (Vars G)) = ((resCard k : ℝ)⁻¹) ^ (n * varCount G) := by
  first | exact @GlobalTheory.UnfoldLoss.LatVol.varLat_basis_open_vol | exact GlobalTheory.UnfoldLoss.LatVol.varLat_basis_open_vol | (intros; apply GlobalTheory.UnfoldLoss.LatVol.varLat_basis_open_vol <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumDoubleSpaceActsUnitScalarSeesawCM
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.weilDatum_doubleSpace_acts_unitScalar_seesaw_CM : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle)
        (ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ)),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
      ∀ ωd : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) →*
          Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS (nT + nT) → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)
          (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∀ (h : Formalism.IndefR.DatumF.GAF σ JT) (hd : Formalism.IndefR.DatumF.GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)),
        Formalism.IndefR.DatumF.mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) hd =
          Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (Formalism.IndefR.DatumF.mtF σ JT h) 0 0 1) →
      ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ f₁ f₂ : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ,
        Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₁ → Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₂ →
        ωd (1, hd) (GlobalTheory.DblTargetDelta.deltaT f₁ f₂) = c • GlobalTheory.DblTargetDelta.deltaT (ω (1, h) f₁) f₂ := by
  first | exact @PositivityTheory.ThKW.weil_rep_unitary_pair_equivariant | exact PositivityTheory.ThKW.weil_rep_unitary_pair_equivariant | (intros; apply PositivityTheory.ThKW.weil_rep_unitary_pair_equivariant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumSplitSupportedEqIntertwinerMulHalfDetChStatement
section
open NumberField MeasureTheory IsDedekindDomain
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.BotClassDict (finQ)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilDatum_splitSupported_eq_intertwiner_mul_halfDetChar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
  (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
  ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
  IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ lam : ℕ →* ℂ, GlobalTheory.FinWeil.GoodNorm (GlobalTheory.FinWeil.sgO D) lam →
  (∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → Formalism.MainNotions.StandardLatticesGL3.InertQ D q → ¬ q ∣ n) → lam n = (Real.sqrt n : ℂ)) →
  ∀ (w : 𝓞 D.host.E) (Om : GA D S × GA D T →* Module.End ℂ (GlobalTheory.FinWeilO.thetaSub ψ S T)),
  GlobalTheory.FinWeilO.IsLatRep hψ.1 ΛS ΛT w lam Om → ∀ ε : AE D, GlobalTheory.RatAut.IsHalfIdem D ε →
  ∀ (g : GA D S) (h : GA D T), SuppAt ε S g → SuppAt ε T h → ∀ x y : (AE D)ˣ, IsDetAt ε S g x → IsDetAt ε T h y →
  ∀ f : GlobalTheory.FinWeilO.thetaSub ψ S T,
    om (g, h) f = ((splitFacO χS χT x y : Circle) : ℂ) • (Om (g, h) f : WO S T → ℂ) := by
  first | exact @GlobalTheory.SplitWeilDict.splitWeil_eq | exact GlobalTheory.SplitWeilDict.splitWeil_eq | (intros; apply GlobalTheory.SplitWeilDict.splitWeil_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenInjectiveExtendsStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_eigen_injective_extends : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M M₁ : Model σ X W), M.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, Set.InjOn e (schA F (Fin n × Fin d) : Set _) → ∀ (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d)) (ev : ∀ v : Pl F, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d → Fv F v) → ℂ), (∀ v, ev v (M.vac v) = M₁.vac v) → (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) → Function.Injective ei := by
  first | exact @GlobalTheory.EvInj.ei_injective | exact GlobalTheory.EvInj.ei_injective | (intros; apply GlobalTheory.EvInj.ei_injective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenSurjectiveExtends
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.AdelicU GlobalTheory.LFun

namespace GlobalTheory.ArchSurj

theorem exists_point_ne_zero {F : Type} [Field F] [NumberField F] {κ : Type} (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ)
    (hne : ∀ v, φ v ≠ 0)
    (hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) :
    ∃ y : κ → Af F, ∀ v, φ v (fun i => y i v) ≠ 0 := by
  have key : ∀ v : Pl F, ∃ z : κ → Fv F v, φ v z ≠ 0 ∧
      (φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 → ∀ i, z i ∈ v.adicCompletionIntegers F) := by
    intro v
    obtain ⟨z, hz⟩ := Function.ne_iff.mp (hne v)
    refine ⟨z, hz, fun h => ?_⟩
    rw [h] at hz
    exact Set.mem_of_indicator_ne_zero hz
  choose z hz hz' using key
  exact ⟨fun i => ⟨fun v => z v i, hstd.mono fun v hv => hz' v hv i⟩, hz⟩

theorem surjective_arch : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M M₁ : Model σ X W), M.IsGood B.ψ → M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, Set.SurjOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) → ∀ (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d)) (ev : ∀ v : Pl F, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d → Fv F v) → ℂ), (∀ v, ev v (M.vac v) = M₁.vac v ∧ (SB _).map (ev v) = SB _) → (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) → Function.Surjective ei := by
  intro F E _ _ _ _ _ σ B n d X W M M₁ hM hM₁ e hsurj ei ev hev he h
  have h₁ : pure h M₁.vac ∈ schA F (Fin n × Fin d) :=
    GlobalTheory.TensUniq.pure_mem_schA h M₁.vac (fun v => (hM₁.vac v).1) hM₁.std
  obtain ⟨Ψ, hΨ, heΨ⟩ := hsurj h₁
  obtain ⟨T, m, f, φ, hSB, hstd, hsum⟩ := GlobalTheory.SchADecomp.exists_sum_pure F _ Ψ hΨ
  have hvac : ∀ i, ∀ᶠ v in Filter.cofinite, φ i v = M.vac v := by
    intro i
    filter_upwards [hM.std, T.eventually_cofinite_notMem] with v hv hT
    rw [hv, hstd i v hT]
  have hid : pure h M₁.vac = ∑ i, pure (ei (f i)) fun v => ev v (φ i v) := by
    rw [← heΨ, hsum, map_sum]
    exact Finset.sum_congr rfl fun i _ => he (f i) (φ i) (hSB i) (hvac i)
  obtain ⟨y, hy⟩ := exists_point_ne_zero M₁.vac (fun v => (hM₁.vac v).2.1) hM₁.std
  set c : ℂ := ∏ᶠ v, M₁.vac v (fun j => y j v) with hc
  have hc0 : c ≠ 0 := finprod_induction (fun a : ℂ => a ≠ 0) one_ne_zero (fun _ _ => mul_ne_zero) hy
  set cs : Fin m → ℂ := fun i => ∏ᶠ v, ev v (φ i v) (fun j => y j v) with hcs
  refine ⟨∑ i, (cs i / c) • f i, ?_⟩
  refine DFunLike.ext _ _ fun x => ?_
  let a : Fin n × Fin d → AF F := fun j => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x j), y j)
  have hI : (fun j => evI F (a j)) = x := by
    funext j
    exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply (x j)
  have hx : h x * c = ∑ i, ei (f i) x * cs i := by
    have := congrFun hid a
    rw [Finset.sum_apply] at this
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, hI] at this
    exact this
  rw [map_sum]
  have hs : (∑ i, ei ((cs i / c) • f i)) x = ∑ i, (cs i / c) * ei (f i) x := by
    rw [SchwartzMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]; rfl
  rw [hs]
  apply mul_right_cancel₀ hc0
  rw [hx, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp

end GlobalTheory.ArchSurj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepScalarCharOfSignatureStatement
section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_rep_scalar_char_of_signature : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E) {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (r s r' s' : ℕ),
    B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ →
    ∀ c : Pl F → Matrix (Fin n) (Fin d) (AE F E) → ℂ,
      (∀ v, ∀ γ ∈ latAtV X W v, ∀ f : SInf F (Fin n × Fin d), M.co.rho B.ψ γ (pure f M.vac) = c v γ • pure f M.vac) →
      ∀ Ψ ∈ schA F (Fin n × Fin d), (∀ v, ∀ γ ∈ latAtV X W v, M.co.rho B.ψ γ Ψ = c v γ • Ψ) →
        ∃ f₁ : SInf F (Fin n × Fin d), Ψ = pure f₁ M.vac := by
  first | exact @GlobalTheory.VacLine.vac_line | exact GlobalTheory.VacLine.vac_line | (intros; apply GlobalTheory.VacLine.vac_line <;> assumption)
end

