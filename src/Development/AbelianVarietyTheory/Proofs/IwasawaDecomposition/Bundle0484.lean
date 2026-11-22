import Mathlib
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0469
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovesOfSelfDual
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0221
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0161
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0107
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanRangeEmb4EqTop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0471
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0473
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0463

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormalisedFamilySatisfiesEquivarianceLaws
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Ker GlobalTheory.ThetaMove.Moved

namespace GlobalTheory.Mem.NatEqui

variable {D : D7}

theorem chi_smulLat {χ : IdE D → ℂ} (hχ : IsChi D χ) {n : ℕ} {L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (hL : SD D L) : letI := D.host.cmStar
    ∀ γ : Matrix.unitaryGroup (Fin n) D.host.E,
      χ (detId D (stdL D n) (SDLat.smulLat (γ : Matrix (Fin n) (Fin n) D.host.E) L)) =
        (∏ τ : D.what₂.Tau, (embT D τ (γ : Matrix (Fin n) (Fin n) D.host.E).det)⁻¹) * χ (detId D (stdL D n) L) := by
  letI := D.host.cmStar
  intro γ
  have hst : ∀ x : D.host.E, star x = D.host.conj x := GlobalTheory.NormSum.AdLattice.star_eq_conj D
  let z : unitary D.host.E := ⟨_, Matrix.det_of_mem_unitary γ.2⟩
  rw [GlobalTheory.Mem.Col2.ChiFacLaw.detId_image D (stdL D n) L (SDLat.smulLat (γ : Matrix (Fin n) (Fin n) D.host.E) L)
    (γ : Matrix (Fin n) (Fin n) D.host.E)
    (star (γ : Matrix (Fin n) (Fin n) D.host.E)) γ.2.2 (fun x hx => ⟨x, hx, rfl⟩) ?_,
    hχ.1 _ _ (GlobalTheory.Mem.Col2.ChiFacLaw.norm_one_span D z.1 (by rw [← hst]; exact z.2.2))
      (GlobalTheory.RelDetIdeal.detId_normOne_mul D n _ _ _ (sd_stdL D n) hL hL).1, hχ.2 z]
  rintro _ ⟨y, hy, rfl⟩
  change (star (γ : Matrix (Fin n) (Fin n) D.host.E)).mulVec ((γ : Matrix (Fin n) (Fin n) D.host.E).mulVec y) ∈ L
  rwa [Matrix.mulVec_mulVec, γ.2.1, Matrix.one_mulVec]

theorem sd_smulLat {n : ℕ} {L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (hL : SD D L) : letI := D.host.cmStar
    ∀ γ : Matrix.unitaryGroup (Fin n) D.host.E, SD D (SDLat.smulLat (γ : Matrix (Fin n) (Fin n) D.host.E) L) := by
  intro γ
  obtain ⟨g, hg⟩ := GlobalTheory.TrueTheta.exists_moves_of_selfDual D n L hL
  obtain ⟨γA, hγ⟩ := GlobalTheory.TrueTheta.exists_rat γ
  exact GlobalTheory.VacuumScalar.sd_of_moves (GlobalTheory.TrueTheta.moves_smulLat hγ hg)

theorem chiFac_ne_zero {χ : IdE D → ℂ} (hχ : IsChi D χ) {N N' : ℕ} {L L'} (h : SD D L) (h' : SD D L') :
    Base.chiFac χ N N' L L' ≠ 0 :=
  mul_ne_zero (zpow_ne_zero _ (chi_detId_ne_zero hχ (sd_stdL D N) h))
    (zpow_ne_zero _ (chi_detId_ne_zero hχ (sd_stdL D N') h'))

theorem chiFac_right {χ : IdE D → ℂ} (hχ : IsChi D χ) {N N' : ℕ} (L) {L' L''} (h' : SD D L') (h'' : SD D L'') :
    Base.chiFac χ N N' L L'' = χ (detId D L' L'') ^ (-((N / 2 : ℕ) : ℤ)) * Base.chiFac χ N N' L L' := by
  unfold Base.chiFac
  rw [chi_detId_mul hχ (sd_stdL D N') h' h'', mul_zpow]
  ring

theorem chiFac_left {χ : IdE D → ℂ} (hχ : IsChi D χ) {N N' : ℕ} {L L₁} (L') (h : SD D L) (h₁ : SD D L₁) :
    Base.chiFac χ N N' L₁ L' = χ (detId D L L₁) ^ (((N' / 2 : ℕ) : ℤ)) * Base.chiFac χ N N' L L' := by
  unfold Base.chiFac
  rw [chi_detId_mul hχ (sd_stdL D N) h h₁, mul_zpow]
  ring

theorem eqP : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ),
    IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → B.EqP χ := by
  intro D cc δ B χ hc hδ hχ
  letI := D.host.cmStar
  have hC : Crv D cc δ := ⟨hc, hδ⟩
  obtain ⟨χ', e, hχ', hv, q1, q2, q3⟩ := GlobalTheory.T.exists_thetaVectorFamily_of_curveDatum D cc δ hC
  have key : ∀ N N', Even N → Even N' → ∃ a : ℂ, ∀ L L', SD D L → SD D L' → B.eNat χ N N' L L' =
      fun z => (a * (Base.chiFac χ N N' L L' / Base.chiFac χ' N N' L L')) * e N N' L L' z := by
    intro N N' hN hN'
    have s := sd_stdL D N
    have s' := sd_stdL D N'
    obtain ⟨v1, v2, -⟩ := hv N N' _ _ ⟨hN, hN', s, s'⟩
    obtain ⟨a, ha⟩ := (GlobalTheory.ThetaLine.theta_line D (GlobalTheory.InducedType.induced_type D).1 cc δ hC N N' _
      (Or.inr ⟨_, _, s, s', rfl⟩)).1 _
      (GlobalTheory.Mem.Col2.WeilVac.thZero_mem B (GlobalTheory.FourthRootStd.stdOK_of_crv D cc δ B hC) N N') _ v1 v2
    refine ⟨a, fun L L' h h' => funext fun z => ?_⟩
    have e3 := q3 N N' ⟨_, s⟩ ⟨L, h⟩ ⟨_, s'⟩ hN hN'
    have e2 := congrFun (q2 N N' ⟨L, h⟩ ⟨_, s'⟩ ⟨L', h'⟩ hN hN') z
    dsimp only at e2 e3
    rw [e3, iop_mul, ← mul_assoc, mul_comm (χ' _ ^ _)] at e2
    have hh : B.thHalf N N' L = fun w => a * Iop D (tor0 D cc δ) (La D (tor0 D cc δ) (stdL D N) (stdL D N'))
        (La D (tor0 D cc δ) L (stdL D N')) (e N N' (stdL D N) (stdL D N')) w := by
      funext w
      rw [Base.thHalf, ha]
      exact iop_mul D _ _ _ a _ w
    have h0 := chiFac_ne_zero hχ' h h'
    change Base.chiFac χ N N' L L' * B.thMoved N N' L L' z = _
    rw [Base.thMoved, hh, iop_mul, e2]
    change _ = a * (_ / Base.chiFac χ' N N' L L') * (Base.chiFac χ' N N' L L' * _)
    field_simp
  refine ⟨fun N N' L L' hN hN' γ γ' => ?_, fun N N' L L' L'' hN hN' => ?_, fun N N' L L₁ L' hN hN' => ?_⟩
  · obtain ⟨a, ha⟩ := key N N' hN hN'
    rw [ha _ _ L.2 L'.2, ha _ _ (sd_smulLat L.2 γ) (sd_smulLat L'.2 γ'), ← q1 N N' L L' hN hN' γ γ']
    have h1 := chiFac_ne_zero hχ' (sd_smulLat L.2 γ) (sd_smulLat L'.2 γ')
    have h0 := chiFac_ne_zero hχ' L.2 L'.2
    funext z
    change _ * pull D _ _ _ (e N N' L.1 L'.1) z = _
    congr 2
    rw [div_eq_div_iff h0 h1]
    unfold Base.chiFac
    rw [chi_smulLat hχ L.2, chi_smulLat hχ L'.2, chi_smulLat hχ' L.2, chi_smulLat hχ' L'.2]
    simp only [mul_zpow]
    ring
  · obtain ⟨a, ha⟩ := key N N' hN hN'
    rw [ha _ _ L.2 L'.2, ha _ _ L.2 L''.2, q2 N N' L L' L'' hN hN']
    funext z
    have h1 := zpow_ne_zero (-((N / 2 : ℕ) : ℤ)) (chi_detId_ne_zero hχ' L'.2 L''.2)
    rw [iop_mul, chiFac_right hχ _ L'.2 L''.2, chiFac_right hχ' _ L'.2 L''.2]
    have h0 := chiFac_ne_zero hχ' L.2 L'.2
    generalize χ' _ ^ _ = u at h1 ⊢
    field_simp
  · obtain ⟨a, ha⟩ := key N N' hN hN'
    rw [ha _ _ L.2 L'.2, ha _ _ L₁.2 L'.2, q3 N N' L L₁ L' hN hN']
    funext z
    have h1 := zpow_ne_zero (((N' / 2 : ℕ) : ℤ)) (chi_detId_ne_zero hχ' L.2 L₁.2)
    rw [iop_mul, chiFac_left hχ _ L.2 L₁.2, chiFac_left hχ' _ L.2 L₁.2]
    have h0 := chiFac_ne_zero hχ' L.2 L'.2
    generalize χ' _ ^ _ = u at h1 ⊢
    field_simp

end GlobalTheory.Mem.NatEqui
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NumberFieldGLDenseInCompletionGLTwoSided
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.DenseGL

variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))

theorem approx (x : P.adicCompletion E) (M : ℤ) :
    ∃ e : E, Valued.v (x - algebraMap E (P.adicCompletion E) e) ≤ WithZero.exp (-M) := by
  have hd := HeightOneSpectrum.denseRange_algebraMap (K := E) P
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer (K := E) P
  set c : P.adicCompletion E := algebraMap E (P.adicCompletion E) (π ^ M.toNat) with hc
  have hvc : Valued.v c = WithZero.exp (-(M.toNat : ℤ)) := by
    have hv : ∀ k : E, Valued.v (algebraMap E (P.adicCompletion E) k) = P.valuation E k :=
      fun k => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P k
    rw [hc, hv, map_pow, hπ,
      ← WithZero.exp_nsmul]
    congr 1
    simp
  have hc0 : Valued.v c ≠ 0 := by rw [hvc]; exact WithZero.exp_ne_zero
  have hN : {y : P.adicCompletion E | Valued.v (x - y) < Valued.v c} ∈ nhds x := by
    have ho := (Valued.isOpen_ball (P.adicCompletion E) (Valued.v.restrict c)).preimage
      (continuous_const.sub continuous_id : Continuous fun y : P.adicCompletion E => x - y)
    simp only [Set.preimage_ofPred_eq, Valuation.restrict_lt_iff] at ho
    refine ho.mem_nhds ?_
    show Valued.v (x - x) < _
    rw [sub_self, map_zero]
    exact zero_lt_iff.2 hc0
  obtain ⟨e, he⟩ := hd.mem_nhds hN
  refine ⟨e, le_of_lt (lt_of_lt_of_le he ?_)⟩
  rw [hvc, WithZero.exp_le_exp]
  have := Int.self_le_toNat M
  omega

theorem bound {n : ℕ} (B : Matrix (Fin n) (Fin n) (P.adicCompletion E)) :
    ∃ L : ℕ, ∀ r k, Valued.v (B r k) ≤ WithZero.exp (L : ℤ) := by
  obtain ⟨c, hc⟩ := Finite.bddAbove_range (fun p : Fin n × Fin n => Valued.v (B p.1 p.2))
  refine ⟨(WithZero.log (max c 1)).toNat, fun r k => ?_⟩
  have h1 : Valued.v (B r k) ≤ max c 1 := (hc ⟨(r, k), rfl⟩).trans (le_max_left _ _)
  have h0 : max c 1 ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
  refine h1.trans ?_
  rw [← WithZero.exp_log h0, WithZero.exp_le_exp, WithZero.log_exp]
  exact Int.self_le_toNat _

end GlobalTheory.DenseGL

namespace GlobalTheory.DenseGL

variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))

def smallIdeal : Ideal (P.adicCompletionIntegers E) where
  carrier := {x | Valued.v (x : P.adicCompletion E) < 1}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Subring.coe_add] at *
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ha hb)
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq, smul_eq_mul] at *
    have hc : Valued.v (c : P.adicCompletion E) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 c.2
    rw [show ((c * x : P.adicCompletionIntegers E) : P.adicCompletion E) = c * x from rfl, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' hc) hx

theorem one_add_small {n : ℕ} (X : Matrix (Fin n) (Fin n) (P.adicCompletion E))
    (hX : ∀ r s, Valued.v (X r s) < 1) :
    Valued.v (1 + X).det = 1 ∧ ∀ r s, Valued.v ((1 + X)⁻¹ r s) ≤ 1 := by
  set O := P.adicCompletionIntegers E
  have hmem : ∀ r s, X r s ∈ O := fun r s =>
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hX r s).le
  let X' : Matrix (Fin n) (Fin n) O := fun r s => ⟨X r s, hmem r s⟩
  have hmap : O.subtype.mapMatrix (1 + X') = 1 + X := by
    rw [map_add, map_one]; rfl
  have hq : (Ideal.Quotient.mk (smallIdeal P)).mapMatrix (1 + X') = 1 := by
    rw [map_add, map_one, add_eq_left]
    ext r s
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hX r s)
  have hd : (1 + X').det - 1 ∈ smallIdeal P := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, RingHom.map_det, hq, Matrix.det_one, map_one,
      sub_self]
  have hdet : Valued.v (1 + X).det = 1 := by
    rw [← hmap, ← RingHom.map_det]
    have h1 : (O.subtype (1 + X').det) = 1 + (((1 + X').det - 1 : O) : P.adicCompletion E) := by
      simp [O]
    rw [h1]
    exact Valuation.map_one_add_of_lt _ hd
  refine ⟨hdet, fun r s => ?_⟩
  have hdet0 : (1 + X).det ≠ 0 := fun h => by rw [h, map_zero] at hdet; exact zero_ne_one hdet
  rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀, hdet,
    inv_one, one_mul, ← hmap, ← RingHom.map_adjugate]
  exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 ((1 + X').adjugate r s).2

end GlobalTheory.DenseGL

namespace GlobalTheory.DenseGL

theorem entry_le {n : ℕ} {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] (B C : Matrix (Fin n) (Fin n) K)
    (a b : WithZero (Multiplicative ℤ)) (hB : ∀ r k, Valued.v (B r k) ≤ a) (hC : ∀ k s, Valued.v (C k s) ≤ b) (r s : Fin n) :
    Valued.v ((B * C) r s) ≤ a * b := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun k _ => ?_
  rw [map_mul]
  exact mul_le_mul' (hB r k) (hC k s)

theorem dense_two_sided : ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (n N : ℕ) (A : GL (Fin n) (P.adicCompletion E)), ∃ γ : GL (Fin n) E, ∀ r s, Valued.v (((A⁻¹).1 * γ.1.map (algebraMap E (P.adicCompletion E)) - 1) r s) ≤ WithZero.exp (-(N : ℤ)) ∧ Valued.v (((γ⁻¹).1.map (algebraMap E (P.adicCompletion E)) * A.1 - 1) r s) ≤ WithZero.exp (-(N : ℤ)) := by
  intro E _ _ P n N A
  set f := algebraMap E (P.adicCompletion E)
  set B := (A⁻¹).1 with hBdef
  have hBA : B * A.1 = 1 := Units.inv_mul A
  obtain ⟨L, hL⟩ := bound P B
  choose C hC using fun r s => approx P (A.1 r s) ((N : ℤ) + 1 + L)
  let Cm : Matrix (Fin n) (Fin n) E := Matrix.of C
  set C' := Cm.map f with hC'
  set X := B * C' - 1 with hXdef
  have hXe : X = B * (C' - A.1) := by rw [Matrix.mul_sub, hBA]
  have hsmall : ∀ r s, Valued.v (X r s) ≤ WithZero.exp (-((N : ℤ) + 1)) := by
    intro r s
    rw [hXe]
    refine (entry_le B (C' - A.1) _ (WithZero.exp (-((N : ℤ) + 1 + L))) hL (fun k s => ?_) r s).trans (le_of_eq ?_)
    · show Valued.v (f (C k s) - A.1 k s) ≤ _
      rw [Valuation.map_sub_swap]
      exact hC k s
    · rw [← WithZero.exp_add]; congr 1; ring
  have hN1 : WithZero.exp (-((N : ℤ) + 1)) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have hNN : WithZero.exp (-((N : ℤ) + 1)) ≤ WithZero.exp (-(N : ℤ)) := by
    rw [WithZero.exp_le_exp]; omega
  have hX1 : ∀ r s, Valued.v (X r s) < 1 := fun r s => (hsmall r s).trans_lt hN1
  obtain ⟨hdet, hint⟩ := one_add_small P X hX1
  have hY : 1 + X = B * C' := by rw [hXdef]; abel
  have hCdet : Cm.det ≠ 0 := by
    intro h0
    have : (1 + X).det = 0 := by
      rw [hY, Matrix.det_mul, hC', ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero,
        mul_zero]
    rw [this, map_zero] at hdet
    exact zero_ne_one hdet
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero Cm hCdet, fun r s => ⟨?_, ?_⟩⟩
  · exact (hsmall r s).trans hNN
  · set γ := Matrix.GeneralLinearGroup.mkOfDetNeZero Cm hCdet
    have hγ : γ.1 = Cm := rfl
    set D := (γ⁻¹).1.map f
    have hCD : C' * D = 1 := by
      rw [hC', ← hγ, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero f) (map_one f)]
    have hYZ : (1 + X) * (D * A.1) = 1 := by
      rw [hY, Matrix.mul_assoc, ← Matrix.mul_assoc C', hCD, Matrix.one_mul, hBA]
    have hZ : D * A.1 = (1 + X)⁻¹ := (Matrix.inv_eq_right_inv hYZ).symm
    have hZY : (D * A.1) * (1 + X) = 1 := by
      rw [hZ]; exact Matrix.nonsing_inv_mul _ (by
        refine isUnit_iff_ne_zero.2 fun h => ?_; rw [h, map_zero] at hdet; exact zero_ne_one hdet)
    have hdiff : D * A.1 - 1 = -((D * A.1) * X) := by
      rw [Matrix.mul_add, Matrix.mul_one] at hZY
      rw [← hZY]; abel
    rw [hdiff, Matrix.neg_apply, Valuation.map_neg]
    refine (entry_le _ X 1 _ (by rw [hZ]; exact hint) hsmall r s).trans ?_
    rw [one_mul]; exact hNN

end GlobalTheory.DenseGL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddSmulPow
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MatNthRoot

variable {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {N : ℕ}

def Bnd (r : WithZero (Multiplicative ℤ)) (X : Matrix (Fin N) (Fin N) (P.adicCompletion E)) : Prop :=
  ∀ i j, Valued.v (X i j) ≤ r

theorem v_natCast_le_one (m : ℕ) : Valued.v ((m : P.adicCompletion E)) ≤ 1 := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Nat.cast_succ]
    exact (Valuation.map_add _ _ _).trans (max_le ih (by simp))

variable {r s : WithZero (Multiplicative ℤ)} {X Y : Matrix (Fin N) (Fin N) (P.adicCompletion E)}

theorem bnd_add (hX : Bnd r X) (hY : Bnd r Y) : Bnd r (X + Y) := fun i j =>
  (Valuation.map_add _ _ _).trans (max_le (hX i j) (hY i j))

theorem bnd_neg (hX : Bnd r X) : Bnd r (-X) := fun i j => by
  rw [Matrix.neg_apply, Valuation.map_neg]; exact hX i j

theorem bnd_sub (hX : Bnd r X) (hY : Bnd r Y) : Bnd r (X - Y) := by
  rw [sub_eq_add_neg]; exact bnd_add hX (bnd_neg hY)

theorem bnd_smul (a : P.adicCompletion E) (hX : Bnd r X) : Bnd (Valued.v a * r) (a • X) := fun i j => by
  rw [Matrix.smul_apply, smul_eq_mul, Valuation.map_mul]; exact mul_le_mul' le_rfl (hX i j)

theorem bnd_mul (hX : Bnd r X) (hY : Bnd s Y) : Bnd (r * s) (X * Y) := fun i j => by
  rw [Matrix.mul_apply]
  exact Valuation.map_sum_le _ fun k _ => by rw [Valuation.map_mul]; exact mul_le_mul' (hX i k) (hY k j)

theorem bnd_mono (h : r ≤ s) (hX : Bnd r X) : Bnd s X := fun i j => (hX i j).trans h

theorem bnd_zero : Bnd r (0 : Matrix (Fin N) (Fin N) (P.adicCompletion E)) := fun i j => by simp

theorem bnd_one : Bnd 1 (1 : Matrix (Fin N) (Fin N) (P.adicCompletion E)) := fun i j => by
  rw [Matrix.one_apply]; split_ifs <;> simp

theorem bnd_sum {ι : Type} (t : Finset ι) (f : ι → Matrix (Fin N) (Fin N) (P.adicCompletion E))
    (h : ∀ k ∈ t, Bnd r (f k)) : Bnd r (∑ k ∈ t, f k) := fun i j => by
  rw [Matrix.sum_apply]; exact Valuation.map_sum_le _ fun k hk => h k hk i j

theorem bnd_pow (hX : Bnd 1 X) : ∀ k : ℕ, Bnd 1 (X ^ k)
  | 0 => by rw [pow_zero]; exact bnd_one
  | k + 1 => by rw [pow_succ]; simpa only [one_mul] using bnd_mul (bnd_pow hX k) hX

theorem bnd_pow_sub (hX : Bnd 1 X) (hY : Bnd 1 Y) (hXY : Bnd r (X - Y)) :
    ∀ k : ℕ, Bnd r (X ^ k - Y ^ k)
  | 0 => by rw [pow_zero, pow_zero, sub_self]; exact bnd_zero
  | k + 1 => by
    have e : X ^ (k + 1) - Y ^ (k + 1) = X ^ k * (X - Y) + (X ^ k - Y ^ k) * Y := by
      rw [pow_succ, pow_succ]; noncomm_ring
    rw [e]
    exact bnd_add (by simpa only [one_mul] using bnd_mul (bnd_pow hX k) hXY)
      (by simpa only [mul_one] using bnd_mul (bnd_pow_sub hX hY hXY k) hY)

noncomputable def tail (n : ℕ) (c : P.adicCompletion E) (X : Matrix (Fin N) (Fin N) (P.adicCompletion E)) :
    Matrix (Fin N) (Fin N) (P.adicCompletion E) :=
  ∑ k ∈ Finset.range (n - 1), ((n.choose (k + 2) : P.adicCompletion E) * ((n : P.adicCompletion E) * c) ^ k) • X ^ (k + 2)

theorem v_coef_le_one (n k : ℕ) {c : P.adicCompletion E} (hc : Valued.v c ≤ 1) :
    Valued.v ((n.choose (k + 2) : P.adicCompletion E) * ((n : P.adicCompletion E) * c) ^ k) ≤ 1 := by
  rw [Valuation.map_mul, Valuation.map_pow, Valuation.map_mul]
  exact mul_le_one' (v_natCast_le_one _) (pow_le_one' (mul_le_one' (v_natCast_le_one _) hc) _)

theorem bnd_tail (n : ℕ) {c : P.adicCompletion E} (hc : Valued.v c ≤ 1) (hX : Bnd 1 X) :
    Bnd 1 (tail n c X) :=
  bnd_sum _ _ fun k _ => bnd_mono (by simpa only [mul_one] using v_coef_le_one n k hc)
    (bnd_smul _ (bnd_pow hX _))

theorem bnd_tail_sub (n : ℕ) {c : P.adicCompletion E} (hc : Valued.v c ≤ 1) (hX : Bnd 1 X) (hY : Bnd 1 Y)
    (hXY : Bnd r (X - Y)) : Bnd r (tail n c X - tail n c Y) := by
  unfold tail
  rw [← Finset.sum_sub_distrib]
  refine bnd_sum _ _ fun k _ => ?_
  rw [← smul_sub]
  exact bnd_mono (by simpa only [one_mul] using mul_le_mul' (v_coef_le_one n k hc) (le_refl r))
    (bnd_smul _ (bnd_pow_sub hX hY hXY _))

theorem one_add_smul_pow (n : ℕ) (hn : 0 < n) (c : P.adicCompletion E)
    (X : Matrix (Fin N) (Fin N) (P.adicCompletion E)) :
    (1 + ((n : P.adicCompletion E) * c) • X) ^ n =
      1 + ((n : P.adicCompletion E) ^ 2 * c) • (X + c • tail n c X) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [add_comm (1 : Matrix _ _ _), (Commute.one_right _).add_pow]
  simp only [one_pow, mul_one]
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [tail, Nat.add_sub_cancel, smul_add, Finset.smul_sum, smul_smul, smul_pow]
  have hc : ∀ (j : ℕ) (Z : Matrix (Fin N) (Fin N) (P.adicCompletion E)),
      Z * ((j : ℕ) : Matrix (Fin N) (Fin N) (P.adicCompletion E)) = (j : P.adicCompletion E) • Z := by
    intro j Z
    rw [← Nat.cast_comm, ← nsmul_eq_mul, Nat.cast_smul_eq_nsmul]
  simp only [hc, smul_smul]
  have hs : ∀ x ∈ Finset.range m,
      (((m + 1).choose (x + 1 + 1) : P.adicCompletion E) * (((m + 1 : ℕ) : P.adicCompletion E) * c) ^ (x + 1 + 1)) •
        X ^ (x + 1 + 1) =
      (((m + 1 : ℕ) : P.adicCompletion E) ^ 2 * c * (c * (((m + 1).choose (x + 2) : P.adicCompletion E) *
        (((m + 1 : ℕ) : P.adicCompletion E) * c) ^ x))) • X ^ (x + 2) := by
    intro x _
    rw [show x + 1 + 1 = x + 2 by omega]
    congr 1
    ring
  rw [Finset.sum_congr rfl hs]
  simp only [zero_add, Nat.choose_zero_right, Nat.choose_one_right, pow_zero, pow_one, Nat.cast_one,
    one_mul, one_smul]
  have e : ((m + 1 : ℕ) : P.adicCompletion E) * (((m + 1 : ℕ) : P.adicCompletion E) * c) =
      ((m + 1 : ℕ) : P.adicCompletion E) ^ 2 * c := by ring
  rw [e]
  abel

end GlobalTheory.MatNthRoot

namespace GlobalTheory.MatNthRoot

variable {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {N : ℕ}

theorem exists_nthRoot : ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (N n : ℕ)
    (c : P.adicCompletion E) (A : Matrix (Fin N) (Fin N) (P.adicCompletion E)), 0 < n → Valued.v c < 1 →
    (∀ i j, Valued.v ((A - 1) i j) ≤ Valued.v ((n : P.adicCompletion E) ^ 2 * c)) →
    ∃ M : Matrix (Fin N) (Fin N) (P.adicCompletion E),
      (∀ i j, Valued.v ((M - 1) i j) ≤ Valued.v ((n : P.adicCompletion E) * c)) ∧ M ^ n = A := by
  intro E _ _ P N n c A hn hc hA
  have hc1 : Valued.v c ≤ 1 := hc.le
  rcases eq_or_ne c 0 with rfl | hc0
  · refine ⟨1, fun i j => by simp, ?_⟩
    rw [one_pow]
    have hA1 : A - 1 = 0 := Matrix.ext fun i j => by
      have h := hA i j
      rwa [mul_zero, Valuation.map_zero, le_zero_iff, Valuation.zero_iff] at h
    exact (sub_eq_zero.1 hA1).symm
  have hn0 : (n : P.adicCompletion E) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  set s : P.adicCompletion E := (n : P.adicCompletion E) ^ 2 * c with hs
  have hs0 : s ≠ 0 := mul_ne_zero (pow_ne_zero _ hn0) hc0
  set Y : Matrix (Fin N) (Fin N) (P.adicCompletion E) := s⁻¹ • (A - 1) with hYdef
  have hY : Bnd 1 Y := fun i j => by
    rw [hYdef, Matrix.smul_apply, smul_eq_mul, Valuation.map_mul]
    calc Valued.v s⁻¹ * Valued.v ((A - 1) i j) ≤ Valued.v s⁻¹ * Valued.v s := mul_le_mul' le_rfl (hA i j)
      _ = 1 := by rw [← Valuation.map_mul, inv_mul_cancel₀ hs0, Valuation.map_one]
  let f : Matrix (Fin N) (Fin N) (P.adicCompletion E) → Matrix (Fin N) (Fin N) (P.adicCompletion E) :=
    fun X => Y - c • tail n c X
  have hf1 : ∀ X, Bnd 1 X → Bnd 1 (f X) := fun X hX =>
    bnd_sub hY (bnd_mono (by simpa only [mul_one] using hc1) (bnd_smul c (bnd_tail n hc1 hX)))
  have hfl : ∀ X Z r, Bnd 1 X → Bnd 1 Z → Bnd r (X - Z) → Bnd (Valued.v c * r) (f X - f Z) := by
    intro X Z r hX hZ hXZ
    have e : f X - f Z = -(c • (tail n c X - tail n c Z)) := by
      simp only [f, smul_sub]; abel
    rw [e]
    exact bnd_neg (bnd_smul c (bnd_tail_sub n hc1 hX hZ hXZ))
  have hb : ∀ k : ℕ, Bnd 1 (f^[k] 0) := by
    intro k
    induction k with
    | zero => exact bnd_zero
    | succ k ih => rw [Function.iterate_succ_apply']; exact hf1 _ ih
  have hd : ∀ k : ℕ, Bnd (Valued.v c ^ k) (f^[k + 1] 0 - f^[k] 0) := by
    intro k
    induction k with
    | zero => rw [pow_zero]; exact bnd_sub (hb 1) (hb 0)
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      have := hfl _ _ _ (hb (k + 1)) (hb k) ih
      rwa [← Function.iterate_succ_apply' f k 0, ← pow_succ'] at this
  have hcau : ∀ i j, CauchySeq fun k => (f^[k] 0) i j := by
    intro i j
    refine cauchySeq_of_le_geometric ‖c‖ 1 (Valued.toNormedField.norm_lt_one_iff.2 hc) fun k => ?_
    rw [dist_eq_norm', one_mul, ← norm_pow]
    refine Valued.toNormedField.norm_le_iff.2 ?_
    rw [Valuation.map_pow]
    have := hd k i j
    rwa [Matrix.sub_apply] at this
  choose L hL using fun i j => cauchySeq_tendsto_of_complete (hcau i j)
  set L' : Matrix (Fin N) (Fin N) (P.adicCompletion E) := Matrix.of L with hL'
  have hT : Filter.Tendsto (fun k => f^[k] 0) Filter.atTop (nhds L') :=
    tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => hL i j
  have hfc : Continuous f := by
    simp only [f, tail]
    fun_prop
  have hfix : f L' = L' := by
    have h1 : Filter.Tendsto (fun k => f^[k + 1] 0) Filter.atTop (nhds L') :=
      hT.comp (Filter.tendsto_add_atTop_nat 1)
    have h2 : Filter.Tendsto (fun k => f^[k + 1] 0) Filter.atTop (nhds (f L')) := by
      simp only [Function.iterate_succ_apply']
      exact (hfc.tendsto L').comp hT
    exact tendsto_nhds_unique h2 h1
  have hLb : Bnd 1 L' := by
    intro i j
    have hm := (Valued.isClosed_valuationSubring (P.adicCompletion E)).mem_of_tendsto (hL i j)
      (Filter.Eventually.of_forall fun k => (Valuation.mem_valuationSubring_iff _ _).2 (hb k i j))
    exact (Valuation.mem_valuationSubring_iff _ _).1 hm
  refine ⟨1 + ((n : P.adicCompletion E) * c) • L', fun i j => ?_, ?_⟩
  · rw [add_sub_cancel_left, Matrix.smul_apply, smul_eq_mul, Valuation.map_mul]
    simpa only [mul_one] using mul_le_mul' (le_refl (Valued.v ((n : P.adicCompletion E) * c))) (hLb i j)
  · rw [one_add_smul_pow n hn c L']
    have e : L' + c • tail n c L' = Y := by
      nth_rewrite 1 [← hfix]
      simp only [f]
      abel
    rw [e, hYdef, smul_smul, ← hs, mul_inv_cancel₀ hs0, one_smul, add_sub_cancel]

end GlobalTheory.MatNthRoot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymmetricFrameWeightedEdgeSumReindexStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricFrame_weightedEdgeSum_reindex : ∀ (Q : Type) [AddCommGroup Q] (ρ k r : ℕ) (hr : r = k + 2 * ρ + 1) (s : Bool) (F : Fin r → Fin r → Q), (∑ i : Fin r, ∑ j : Fin r, if symEdge ρ k i j then GlobalTheory.Mem.SymChar.wtA ρ k s i j • F i j else 0) = (∑ a : Fin ρ, F ⟨a.1, by have := a.2; omega⟩ ⟨if a.1 + 1 < ρ then a.1 + 1 else ρ + k, by have := a.2; split_ifs <;> omega⟩) + ∑ i : Fin k, if h : i.1 + 1 < k then (if s then F ⟨ρ + i.1, by omega⟩ ⟨ρ + i.1 + 1, by omega⟩ else 0) else 0 := by
  first | exact @GlobalTheory.Mem.SymChar.EdgeReindex.sum_symEdge_wtA | exact GlobalTheory.Mem.SymChar.EdgeReindex.sum_symEdge_wtA | (intros; apply GlobalTheory.Mem.SymChar.EdgeReindex.sum_symEdge_wtA <;> assumption)
end

