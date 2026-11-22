import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2079
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0031
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FinPartDetAtInvInt
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0971
import Development.AbelianVarietyTheory.Definitions.Divisors.LiftFrameEmbeddingBase
import Formalism.SharpRestriction.GlobalSchurBounds.MainSup
import Formalism.PieriBlockIdeals.PieriColumnMinors.ParameterBounds
import Formalism.LocalToGlobal.Divisibility.InertPartitionLePartF
import Formalism.LocalToGlobal.Divisibility.RowLatLemmas
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0021
import Development.AutomorphicArithmetic.PrimeDiscriminants.ExcSet

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueMatrixDatumFourierExpansionGaussSum
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.ResidueFourier

section Local

variable {k : Type} [Field k] [Fintype k]

theorem sum_char_trace {n r : ℕ} {ψ : AddChar k ℂ} (hψ : ψ.IsPrimitive) (w : Matrix (Fin n) (Fin r) k) :
    ∑ x : Matrix (Fin r) (Fin n) k, ψ (Matrix.trace (x * w)) =
      if w = 0 then ((Nat.card k : ℂ) ^ (n * r)) else 0 := by
  let L : Matrix (Fin r) (Fin n) k →+ k :=
    AddMonoidHom.mk' (fun x => Matrix.trace (x * w)) (fun a b => by rw [Matrix.add_mul, Matrix.trace_add])
  have h := AddChar.sum_eq_ite (ψ.compAddMonoidHom L)
  have h2 : ψ.compAddMonoidHom L = 0 ↔ w = 0 := by
    constructor
    · intro h0
      ext i j
      by_contra hne
      refine hψ hne ?_
      ext t
      have := DFunLike.congr_fun h0 (Matrix.single j i t)
      change ψ (Matrix.trace (Matrix.single j i t * w)) = 1 at this
      rw [Matrix.trace_single_mul, smul_eq_mul] at this
      rw [AddChar.mulShift_apply, mul_comm]
      exact this
    · rintro rfl
      ext x
      change ψ (Matrix.trace (x * (0 : Matrix (Fin n) (Fin r) k))) = 1
      simp
  refine Eq.trans h ?_
  by_cases hw : w = 0
  · rw [if_pos (h2.2 hw), if_pos hw, Nat.card_eq_fintype_card]
    have : Fintype.card (Matrix (Fin r) (Fin n) k) = Fintype.card k ^ (n * r) := by
      change Fintype.card (Fin r → Fin n → k) = _
      simp [pow_mul]
    rw [this]; push_cast; rfl
  · rw [if_neg (fun h => hw (h2.1 h)), if_neg hw]

theorem inversion {n r : ℕ} {ψ : AddChar k ℂ} (hψ : ψ.IsPrimitive) (f : Matrix (Fin n) (Fin r) k → ℂ)
    (u : Matrix (Fin n) (Fin r) k) :
    f u = ∑ x : Matrix (Fin r) (Fin n) k,
      (((Nat.card k : ℂ) ^ (n * r))⁻¹ * ∑ v, f v * ψ (Matrix.trace (-x * v))) * ψ (Matrix.trace (x * u)) := by
  have hc : ((Nat.card k : ℂ) ^ (n * r)) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 Nat.card_pos.ne')
  have h1 : ∀ x : Matrix (Fin r) (Fin n) k,
      (((Nat.card k : ℂ) ^ (n * r))⁻¹ * ∑ v, f v * ψ (Matrix.trace (-x * v))) * ψ (Matrix.trace (x * u)) =
      ∑ v, ((Nat.card k : ℂ) ^ (n * r))⁻¹ * f v * ψ (Matrix.trace (x * (u - v))) := fun x => by
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [mul_assoc, mul_assoc, mul_assoc, ← AddChar.map_add_eq_mul, ← Matrix.trace_add, Matrix.mul_sub, Matrix.neg_mul,
      neg_add_eq_sub]
  simp only [h1]
  rw [Finset.sum_comm, Finset.sum_eq_single u]
  · rw [← Finset.mul_sum, sum_char_trace hψ, if_pos (sub_self u)]
    field_simp
  · intro v _ hv
    rw [← Finset.mul_sum, sum_char_trace hψ, if_neg (fun h => hv (sub_eq_zero.1 h).symm), mul_zero]
  · simp

def embTop (n : ℕ) {r : ℕ} (g : Matrix (Fin r) (Fin r) k) : Matrix (Fin n) (Fin r) k :=
  fun i j => if h : i.val < r then g ⟨i.val, h⟩ j else 0

omit [Fintype k] in
theorem topL_embTop {n r : ℕ} (h : r ≤ n) (g : Matrix (Fin r) (Fin r) k) : topL r (embTop n g) = g := by
  ext i j
  have : i.val < n := lt_of_lt_of_le i.2 h
  simp [topL, embTop, this]

omit [Fintype k] in
theorem lowZero_embTop {n r : ℕ} (g : Matrix (Fin r) (Fin r) k) : LowZero r (embTop n g) := by
  intro i j hi _
  simp [embTop, not_lt.2 hi]

omit [Fintype k] in
theorem embTop_topL {n r : ℕ} {u : Matrix (Fin n) (Fin r) k} (hu : LowZero r u) : embTop n (topL r u) = u := by
  ext i j
  by_cases hi : i.val < r
  · simp [topL, embTop, hi]
  · simp [embTop, hi, hu i j (not_lt.1 hi) j.2]

omit [Fintype k] in
theorem trace_embTop {n r : ℕ} (h : r ≤ n) (x : Matrix (Fin r) (Fin n) k) (g : Matrix (Fin r) (Fin r) k) :
    Matrix.trace (x * embTop n g) = Matrix.trace (topL r x * g) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fin.sum_univ_add]
  have h2 : ∀ i : Fin r, i.val < r + t := fun i => lt_of_lt_of_le i.2 h
  simp [embTop, topL, h2]
  rfl

theorem transform {n r : ℕ} (h : r ≤ n) {ψ : AddChar k ℂ} (hψ : ψ.IsPrimitive) {ξ : kˣ →* ℂˣ} (hξ : ξ ≠ 1)
    (x : Matrix (Fin r) (Fin n) k) :
    ∑ v : Matrix (Fin n) (Fin r) k,
      (if h : LowZero r v ∧ IsUnit (topL r v).det then ((ξ h.2.unit : ℂˣ) : ℂ) ^ (-1 : ℤ) else 0) * ψ (Matrix.trace (x * v)) =
      (∑ g : GL (Fin r) k, (((ξ (Matrix.GeneralLinearGroup.det g))⁻¹ : ℂˣ) : ℂ) *
        ψ (Matrix.trace (g : Matrix (Fin r) (Fin r) k))) *
      (if h : IsUnit (topL r x).det then ((ξ h.unit : ℂˣ) : ℂ) else 0) := by
  obtain ⟨h0, h1⟩ := GlobalTheory.matrixGaussSum_singular_and_invertible k ℂ ψ ξ r hψ hξ
  have step : ∑ v : Matrix (Fin n) (Fin r) k,
      (if h : LowZero r v ∧ IsUnit (topL r v).det then ((ξ h.2.unit : ℂˣ) : ℂ) ^ (-1 : ℤ) else 0) * ψ (Matrix.trace (x * v)) =
      ∑ g : GL (Fin r) k, (((ξ (Matrix.GeneralLinearGroup.det g))⁻¹ : ℂˣ) : ℂ) *
        ψ (Matrix.trace (topL r x * (g : Matrix (Fin r) (Fin r) k))) := by
    symm
    apply Finset.sum_of_injOn (fun g : GL (Fin r) k => embTop n (g : Matrix (Fin r) (Fin r) k))
    · intro a _ b _ hab
      have := congrArg (topL r) hab
      simp only [topL_embTop h] at this
      exact Units.ext this
    · intro a _
      simp
    · intro u _ hu
      rw [dif_neg, zero_mul]
      rintro ⟨hl, hd⟩
      exact hu ⟨((Matrix.isUnit_iff_isUnit_det _).2 hd).unit, by simp, embTop_topL hl⟩
    · intro g _
      have hx : IsUnit (topL r (embTop n (g : Matrix (Fin r) (Fin r) k))).det := by
        rw [topL_embTop h]; exact (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
      have hdet : hx.unit = Matrix.GeneralLinearGroup.det g := Units.ext (by simp [topL_embTop h])
      rw [dif_pos ⟨lowZero_embTop _, hx⟩, trace_embTop h, hdet, zpow_neg_one, Units.val_inv_eq_inv_val]
  rw [step]
  by_cases hy : IsUnit (topL r x).det
  · have hm := (Matrix.isUnit_iff_isUnit_det _).2 hy
    have hdet : Matrix.GeneralLinearGroup.det (hm.unit : GL (Fin r) k) = hy.unit :=
      Units.ext (by simp [Matrix.GeneralLinearGroup.det])
    have key := h1 hm.unit
    rw [hdet] at key
    simp only [IsUnit.unit_spec, one_mul] at key
    rw [key, dif_pos hy, mul_comm]
  · have hz : (topL r x).det = 0 := by simpa using hy
    rw [h0 _ hz, dif_neg hy, mul_zero]

end Local

theorem dite_prod {ι : Type} (Q : Finset ι) (p : ι → Prop) (f : ∀ i, p i → ℂ) :
    (if h : ∀ i ∈ Q, p i then ∏ i ∈ Q.attach, f i.1 (h i.1 i.2) else 0) =
      ∏ i ∈ Q.attach, if h : p i.1 then f i.1 h else 0 := by
  split_ifs with h
  · exact Finset.prod_congr rfl fun i _ => (dif_pos (h i.1 i.2)).symm
  · push_neg at h
    obtain ⟨i, hi, hp⟩ := h
    exact (Finset.prod_eq_zero (Finset.mem_attach Q ⟨i, hi⟩) (dif_neg hp)).symm

theorem omegaQ_fourier : ∀ (D : D7) [∀ PP : Pl D.host.E, Fintype (kP PP)] (Q : Finset (Pl D.host.E)) (n r : ℕ), r ≤ n → ∀ (ψP : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), (∀ PP ∈ Q, (ψP PP).IsPrimitive) → (∀ PP ∈ Q, ξ PP ≠ 1) → ∃ c : (∀ PP : ↥Q, Matrix (Fin r) (Fin n) (kP PP.1)) → ℂ, (∀ u : ∀ PP : Pl D.host.E, Matrix (Fin n) (Fin r) (kP PP), omegaQ Q r ξ (-1) u = ∑ x, c x * ∏ PP ∈ Q.attach, ψP PP.1 (Matrix.trace (x PP * u PP.1))) ∧ ∀ (x : ∀ PP : ↥Q, Matrix (Fin r) (Fin n) (kP PP.1)) (y : ∀ PP : Pl D.host.E, Matrix (Fin r) (Fin n) (kP PP)), (∀ PP : ↥Q, y PP.1 = x PP) → c (-x) = (∏ PP ∈ Q.attach, ((Nat.card (kP PP.1) : ℂ) ^ (n * r))⁻¹ * ∑ g : GL (Fin r) (kP PP.1), (((ξ PP.1 (Matrix.GeneralLinearGroup.det g))⁻¹ : ℂˣ) : ℂ) * ψP PP.1 (Matrix.trace (g : Matrix (Fin r) (Fin r) (kP PP.1)))) * omegaFlat Q r ξ y := by
  intro D _ Q n r hrn ψP ξ hψ hξ
  let f : ∀ PP : Pl D.host.E, Matrix (Fin n) (Fin r) (kP PP) → ℂ := fun PP v =>
    if h : LowZero r v ∧ IsUnit (topL r v).det then ((ξ PP h.2.unit : ℂˣ) : ℂ) ^ (-1 : ℤ) else 0
  let c : ∀ PP : Pl D.host.E, Matrix (Fin r) (Fin n) (kP PP) → ℂ := fun PP x =>
    ((Nat.card (kP PP) : ℂ) ^ (n * r))⁻¹ * ∑ v, f PP v * ψP PP (Matrix.trace (-x * v))
  refine ⟨fun x => ∏ PP ∈ Q.attach, c PP.1 (x PP), fun u => ?_, fun x y hxy => ?_⟩
  · have h1 : omegaQ Q r ξ (-1) u = ∏ PP ∈ Q.attach, f PP.1 (u PP.1) := by
      unfold omegaQ
      convert dite_prod Q (fun PP => LowZero r (u PP) ∧ IsUnit (topL r (u PP)).det)
        (fun PP h => ((ξ PP h.2.unit : ℂˣ) : ℂ) ^ (-1 : ℤ))
    have h2 : ∀ PP : ↥Q, f PP.1 (u PP.1) = ∑ x, c PP.1 x * ψP PP.1 (Matrix.trace (x * u PP.1)) := fun PP => by
      letI := Ideal.Quotient.field PP.1.asIdeal
      exact inversion (k := kP PP.1) (hψ PP.1 PP.2) (f PP.1) (u PP.1)
    rw [h1]
    simp only [h2, ← Finset.prod_mul_distrib, Finset.attach_eq_univ]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  · have h1 : omegaFlat Q r ξ y = ∏ PP ∈ Q.attach, if h : IsUnit (topL r (y PP.1)).det then ((ξ PP.1 h.unit : ℂˣ) : ℂ) else 0 := by
      unfold omegaFlat
      convert dite_prod Q (fun PP => IsUnit (topL r (y PP)).det) (fun PP h => ((ξ PP h.unit : ℂˣ) : ℂ))
    rw [h1, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun PP _ => ?_
    rw [hxy PP, mul_assoc]
    simp only [c, Pi.neg_apply, neg_neg]
    congr 1
    letI := Ideal.Quotient.field PP.1.asIdeal
    convert transform (k := kP PP.1) hrn (hψ PP.1 PP.2) (hξ PP.1 PP.2) (x PP)

end GlobalTheory.ResidueFourier
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalarDilationElementSupportDetPullback
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open Formalism.IndefR.Fin Formalism.IndefR.Fin.LevelGroupLemmas
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DilScalar

variable {D : D7}

theorem int_mul {x y : Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D) (hy : y ∈ intAE D) :
    x * y ∈ intAE D := by
  refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intAE D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, v, rfl⟩
    refine AddSubgroup.subset_closure ⟨a * b, fun w => ?_, u * v, ?_⟩
    · rw [map_mul]; exact mul_mem (ha w) (hb w)
    · rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl
  · intro x _; rw [zero_mul]; exact zero_mem _
  · intro x _; rw [mul_zero]; exact zero_mem _
  · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
  · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
  · intro x y _ _ h; rw [neg_mul]; exact neg_mem h
  · intro x y _ _ h; rw [mul_neg]; exact neg_mem h

theorem incA_int (x : 𝓞 D.host.E) : finPart D (incA D (x : D.host.E)) ∈ intAE D :=
  AddSubgroup.subset_closure ⟨1, fun _ => one_mem _, x, rfl⟩

theorem idemAt_mul_int {e : AE D} {P : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt e P)
    {y : D.host.E} (hv : P.valuation D.host.E y ≤ 1) : finPart D (e * incA D y) ∈ intAE D := by
  obtain ⟨a, b, hab⟩ := P.exists_primeCompl_mul_eq_of_integer _ hv
  have hb : (b : 𝓞 D.host.E) ∉ P.asIdeal := b.2
  have hb0 : (b : 𝓞 D.host.E) ≠ 0 := fun h => hb (h ▸ zero_mem _)
  have hb1 : ((b : 𝓞 D.host.E) : D.host.E) ≠ 0 := by exact_mod_cast hb0
  have hi : finPart D (e * incA D (((b : 𝓞 D.host.E) : D.host.E)⁻¹)) ∈ intAE D := by
    by_contra hc
    exact hb ((he.2 _ hb0).2 hc)
  have hq : y = (a : D.host.E) * ((b : 𝓞 D.host.E) : D.host.E)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ hb1]
    exact hab
  have h := int_mul (incA_int (D := D) a) hi
  rw [← RingHom.map_mul, mul_left_comm, ← map_mul (incA D), ← hq] at h
  exact h

theorem val_uniformiser (P : HeightOneSpectrum (𝓞 D.host.E)) {ϖ : 𝓞 D.host.E}
    (h1 : ϖ ∈ P.asIdeal) (h2 : ϖ ∉ P.asIdeal ^ 2) :
    P.valuation D.host.E (ϖ : D.host.E) = WithZero.exp (-1 : ℤ) := by
  rw [P.valuation_of_algebraMap]
  have a1 : P.intValuation ϖ ≤ WithZero.exp (-((1 : ℕ) : ℤ)) :=
    (P.intValuation_le_pow_iff_mem ϖ 1).2 (by rw [pow_one]; exact h1)
  have a2 : ¬ P.intValuation ϖ ≤ WithZero.exp (-((2 : ℕ) : ℤ)) :=
    fun h => h2 ((P.intValuation_le_pow_iff_mem ϖ 2).1 h)
  have a0 : P.intValuation ϖ ≠ 0 := fun h => a2 (h ▸ zero_le')
  rw [← WithZero.exp_log a0] at a1 a2 ⊢
  rw [WithZero.exp_le_exp] at a1 a2
  congr 1
  omega

theorem idemSum_dil_int {e : AE D} {Q : Finset (Pl D.host.E)} (he : IsIdemSum e Q) {N : ℕ}
    (hN : ∀ PP ∈ Q, (N : 𝓞 D.host.E) ∈ PP.asIdeal) {ϖ : 𝓞 D.host.E}
    (hϖ : ∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) :
    finPart D (e * incA D ((N : D.host.E) * (ϖ : D.host.E)⁻¹)) ∈ intAE D := by
  obtain ⟨⟨es, hes, hsum⟩, -⟩ := he
  rw [hsum, Finset.sum_mul, map_sum]
  refine sum_mem fun PP hPP => idemAt_mul_int (hes PP hPP) ?_
  have v1 := val_uniformiser (D := D) PP (hϖ PP hPP).1 (hϖ PP hPP).2
  have v2 : PP.valuation D.host.E (N : D.host.E) ≤ WithZero.exp (-1 : ℤ) := by
    rw [← map_natCast (algebraMap (𝓞 D.host.E) D.host.E) N, PP.valuation_of_algebraMap]
    have := (PP.intValuation_le_pow_iff_mem (N : 𝓞 D.host.E) 1).2 (by rw [pow_one]; exact hN PP hPP)
    simpa using this
  rw [map_mul, map_inv₀, v1]
  calc PP.valuation D.host.E (N : D.host.E) * (WithZero.exp (-1 : ℤ))⁻¹
      ≤ WithZero.exp (-1 : ℤ) * (WithZero.exp (-1 : ℤ))⁻¹ := by gcongr
    _ = 1 := mul_inv_cancel₀ WithZero.exp_ne_zero

end GlobalTheory.DilScalar

set_option maxHeartbeats 1000000 in
open GlobalTheory.DilScalar in

theorem GlobalTheory.DilScalar.scalar_dil_facts : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), ∀ (Q : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Q → ∀ N : ℕ, N ≠ 0 → (∀ PP ∈ Q, (N : 𝓞 D.host.E) ∈ PP.asIdeal) → ∀ ϖ : 𝓞 D.host.E, (ϖ : D.host.E) ≠ 0 → (∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) → ∀ z : GA D S, mt S z = Matrix.diagonal (fun _ => e * incA D ((ϖ : D.host.E)⁻¹) + cA D e * cA D (incA D (ϖ : D.host.E)) + (1 - e - cA D e)) → SuppAt e S z ∧ (∃ x : (AE D)ˣ, IsDetAt (cA D e) S z x) ∧ (∀ Ψ : WO S T → ℂ, (∀ t, Ψ t ≠ 0 → IsHalf e t) → actPull (z, (1 : GA D T)) Ψ = fun x => Ψ (x.map fun w => incA D ((ϖ : D.host.E)⁻¹) * w)) ∧ (∀ Φ, IsSBHalf e (latAll S T ΛS ΛT) Φ → IsSBHalf e (latAll S T ΛS ΛT) (actPull (z, (1 : GA D T)) Φ)) ∧ ∀ t : WO S T, IsHalf e t → actO S T z⁻¹ 1 t ∈ latAll S T ΛS ΛT → t ∈ latAll S T ΛS ΛT := by
  intro D S T ΛS ΛT Q e he N hN0 hN ϖ hϖ0 hϖ z hz
  have hee : e * e = e := idemSum_sq he
  have hec : e * cA D e = 0 := he.2
  have hcc : cA D e * cA D e = cA D e := by rw [← map_mul, hee]
  have hXP : incA D ((ϖ : D.host.E)⁻¹) * incA D (ϖ : D.host.E) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hϖ0, map_one]
  have hYZ : cA D (incA D (ϖ : D.host.E)) * cA D (incA D ((ϖ : D.host.E)⁻¹)) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ hϖ0, map_one, map_one]
  have hea : e * (e * incA D ((ϖ : D.host.E)⁻¹) + cA D e * cA D (incA D (ϖ : D.host.E)) + (1 - e - cA D e)) =
      e * incA D ((ϖ : D.host.E)⁻¹) := by
    linear_combination (incA D ((ϖ : D.host.E)⁻¹) - 1) * hee + (cA D (incA D (ϖ : D.host.E)) - 1) * hec
  have hab : (e * incA D ((ϖ : D.host.E)⁻¹) + cA D e * cA D (incA D (ϖ : D.host.E)) + (1 - e - cA D e)) *
      (e * incA D (ϖ : D.host.E) + cA D e * cA D (incA D ((ϖ : D.host.E)⁻¹)) + (1 - e - cA D e)) = 1 := by
    linear_combination (incA D ((ϖ : D.host.E)⁻¹) * incA D (ϖ : D.host.E) - incA D ((ϖ : D.host.E)⁻¹)
        - incA D (ϖ : D.host.E) + 1) * hee
      + (cA D (incA D (ϖ : D.host.E)) * cA D (incA D ((ϖ : D.host.E)⁻¹)) - cA D (incA D (ϖ : D.host.E))
        - cA D (incA D ((ϖ : D.host.E)⁻¹)) + 1) * hcc
      + (incA D ((ϖ : D.host.E)⁻¹) * cA D (incA D ((ϖ : D.host.E)⁻¹)) + cA D (incA D (ϖ : D.host.E)) * incA D (ϖ : D.host.E)
        - incA D ((ϖ : D.host.E)⁻¹) - incA D (ϖ : D.host.E) - cA D (incA D (ϖ : D.host.E))
        - cA D (incA D ((ϖ : D.host.E)⁻¹)) + 2) * hec
      + e * hXP + cA D e * hYZ

  have hPint : finPart D (incA D (ϖ : D.host.E)) ∈ intAE D := incA_int ϖ
  have hPmem : ∀ u ∈ latAll S T ΛS ΛT, incA D (ϖ : D.host.E) • u ∈ latAll S T ΛS ΛT :=
    GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ hPint

  have hact : ∀ t : WO S T, actO S T z⁻¹ 1 t =
      t.map fun w => w * (e * incA D ((ϖ : D.host.E)⁻¹) + cA D e * cA D (incA D (ϖ : D.host.E)) + (1 - e - cA D e)) := by
    intro t
    have h0 : actO S T z⁻¹ 1 t = HMul.hMul (t : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (mt S z) := by
      rw [actO_eq, inv_inv, mt_one']; exact congrArg (fun M : Matrix (Fin T.rank) (Fin S.rank) (AE D) => HMul.hMul M (mt S z))
        (Matrix.one_mul (t : Matrix (Fin T.rank) (Fin S.rank) (AE D)))
    rw [h0, hz]
    ext i j
    simp only [Matrix.mul_diagonal, Matrix.map_apply]
  have hmapA : ∀ t : WO S T, IsHalf e t →
      (t.map fun w => w * (e * incA D ((ϖ : D.host.E)⁻¹) + cA D e * cA D (incA D (ϖ : D.host.E)) + (1 - e - cA D e))) =
        t.map fun w => incA D ((ϖ : D.host.E)⁻¹) * w := by
    intro t ht
    ext i j
    simp only [Matrix.map_apply]
    linear_combination (incA D ((ϖ : D.host.E)⁻¹) -
      (e * incA D ((ϖ : D.host.E)⁻¹) + cA D e * cA D (incA D (ϖ : D.host.E)) + (1 - e - cA D e))) * ht i j + t i j * hea
  have halfA : ∀ t : WO S T, IsHalf e (t.map fun w => w * (e * incA D ((ϖ : D.host.E)⁻¹) +
      cA D e * cA D (incA D (ϖ : D.host.E)) + (1 - e - cA D e))) → IsHalf e t := by
    intro t h i j
    have h1 := h i j
    simp only [Matrix.map_apply] at h1
    linear_combination (e * incA D (ϖ : D.host.E) + cA D e * cA D (incA D ((ϖ : D.host.E)⁻¹)) + (1 - e - cA D e)) * h1
      - (e * t i j - t i j) * hab
  have halfX : ∀ t : WO S T, IsHalf e (t.map fun w => incA D ((ϖ : D.host.E)⁻¹) * w) → IsHalf e t := by
    intro t h i j
    have h1 := h i j
    simp only [Matrix.map_apply] at h1
    linear_combination incA D (ϖ : D.host.E) * h1 - (e * t i j - t i j) * hXP
  have hpull : ∀ Ψ : WO S T → ℂ, (∀ t, Ψ t ≠ 0 → IsHalf e t) →
      actPull (z, (1 : GA D T)) Ψ = fun x => Ψ (x.map fun w => incA D ((ϖ : D.host.E)⁻¹) * w) := by
    intro Ψ hΨ
    funext t
    show Ψ (actO S T z⁻¹ (1 : GA D T)⁻¹ t) = _
    rw [inv_one, hact]
    by_cases hh : IsHalf e t
    · rw [hmapA t hh]
    · have h1 : Ψ (t.map fun w => w * (e * incA D ((ϖ : D.host.E)⁻¹) + cA D e * cA D (incA D (ϖ : D.host.E)) +
          (1 - e - cA D e))) = 0 := by
        by_contra h0
        exact hh (halfA t (hΨ _ h0))
      have h2 : Ψ (t.map fun w => incA D ((ϖ : D.host.E)⁻¹) * w) = 0 := by
        by_contra h0
        exact hh (halfX t (hΨ _ h0))
      rw [h1, h2]
  refine ⟨?_, ?_, hpull, ?_, ?_⟩
  ·
    intro i j
    rw [hz]
    by_cases h : i = j
    · subst h
      rw [Matrix.sub_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      linear_combination (incA D ((ϖ : D.host.E)⁻¹) - 1) * hee + (cA D (incA D (ϖ : D.host.E)) - 1) * hcc +
        (incA D ((ϖ : D.host.E)⁻¹) + cA D (incA D (ϖ : D.host.E)) - 2) * hec
    · rw [Matrix.sub_apply, Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h, sub_zero, mul_zero]
  ·
    have hdet : (mt S z).det * (mt S z⁻¹).det = 1 := by
      rw [← Matrix.det_mul, ← mt_mul', mul_inv_cancel, mt_one', Matrix.det_one]
    refine ⟨⟨cA D e * (mt S z).det + (1 - cA D e), cA D e * (mt S z⁻¹).det + (1 - cA D e), ?_, ?_⟩, rfl⟩
    · linear_combination (cA D e * cA D e) * hdet + (2 - (mt S z).det - (mt S z⁻¹).det) * hcc
    · linear_combination (cA D e * cA D e) * hdet + (2 - (mt S z).det - (mt S z⁻¹).det) * hcc
  ·
    intro Φ hΦ
    have hsupp := hΦ.1
    obtain ⟨_, k, hk, hinv, hcpt⟩ := hΦ
    rw [hpull Φ hsupp]
    have hint := idemSum_dil_int he hN hϖ
    refine ⟨fun t ht => halfX t (hsupp _ ht), N * k, Nat.mul_pos (Nat.pos_of_ne_zero hN0) hk,
      fun u hu hue t => ?_, fun t ht => ?_⟩
    · have key : (t + (N * k) • u).map (fun w => incA D ((ϖ : D.host.E)⁻¹) * w) =
          t.map (fun w => incA D ((ϖ : D.host.E)⁻¹) * w) +
            k • ((e * incA D ((N : D.host.E) * (ϖ : D.host.E)⁻¹)) • u) := by
        ext i j
        simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, nsmul_eq_mul, smul_eq_mul, map_mul,
          map_natCast, Nat.cast_mul]
        linear_combination (-((k : AE D) * (N : AE D) * incA D ((ϖ : D.host.E)⁻¹))) * hue i j
      dsimp only
      rw [key]
      refine hinv _ (GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ hint u hu) (fun i j => ?_) _
      simp only [Matrix.smul_apply, smul_eq_mul]
      linear_combination (incA D ((N : D.host.E) * (ϖ : D.host.E)⁻¹) * u i j) * hee
    · have h1 := hPmem _ (hcpt _ ht)
      have h2 : incA D (ϖ : D.host.E) • k • t.map (fun w => incA D ((ϖ : D.host.E)⁻¹) * w) = k • t := by
        ext i j
        simp only [Matrix.map_apply, Matrix.smul_apply, nsmul_eq_mul, smul_eq_mul]
        linear_combination ((k : AE D) * t i j) * hXP
      rw [h2] at h1
      rw [mul_smul]
      exact nsmul_mem h1 N
  ·
    intro t ht hmem
    rw [hact, hmapA t ht] at hmem
    have h1 := hPmem _ hmem
    convert h1 using 1
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
    linear_combination (-t i j) * hXP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetAtOfSizeAt
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim

namespace GlobalTheory.BigTop.Fun.SetFromSize

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem finite_tup (p : PtAt ex Csz) : Finite p.P.T := by
  classical
  have h1 := p.charW.tup.mu_off
  have h2 := p.charW.tup.mu_used
  have : (Set.univ : Set p.P.T) ⊆ insert p.P.A3.A.μ0 (p.R.mu '' (p.R.twPl : Set _)) := fun t _ => by
    rcases h2 t with h | ⟨w, rfl⟩
    · exact Or.inl h
    · by_cases hw : w ∈ p.R.twPl
      · exact Or.inr ⟨w, hw, rfl⟩
      · exact Or.inl (h1 w hw)
  exact Set.finite_univ_iff.1 ((((p.R.twPl).finite_toSet.image _).insert _).subset this)

set_option maxHeartbeats 1600000 in

theorem setting_of_size (p : PtAt ex Csz) (hp : p.Rows) (hs : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows L) (he : GlobalTheory.GLq.ESerTie D) :
    HidaSetting L p.R.toRealDat p.F.lv2 where
  size := hs
  eser := he
  host := p.host
  hF := p.hF
  core := (GlobalTheory.OneMapBridge.heckeChoiceClauses_of_weakCharacterisation_at_face D _ _ _ _ _ _ p.R p.F p.charW hp.exAt).1
  mu_off := p.charW.tup.mu_off
  mu_used := p.charW.tup.mu_used
  mu_ne := p.charW.tup.mu_ne
  mu_conj := p.charW.tup.mu_conj
  mu_on := p.charW.tup.mu_on
  grp := p.charW.base.grp.record
  guard := p.qGuard
  fin := finite_tup p
  fullY := p.charW.fullY
  fullX := p.charW.fullX
  std := p.stdChar
  stdX := p.stdX
  betaX := p.betaStd.2

end GlobalTheory.BigTop.Fun.SetFromSize

namespace GlobalTheory.BigTop.Fun

theorem setAt_of_sizeAt (h : SizeAt) : SetAt :=
  h.imp fun _ _ _ a => evPt_imp a fun _ _ _ p hp b he => SetFromSize.setting_of_size p hp b he

end GlobalTheory.BigTop.Fun

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

namespace GlobalTheory.ExpTie

theorem not_dvd_discr_host (D : D7) {l : ℕ} (hl : l.Prime) (hS : l ∉ Formalism.MainNotions.JumpSetsAlt.excSet D) :
    ¬ ((l : ℕ) : ℤ) ∣ NumberField.discr D.host.E :=
  UpperTheory.ExcSet.not_dvd_discr D hl hS

theorem smallSt : SmallSt := by
  unfold SmallSt InRange AtPts
  refine Formalism.MainNotions.Closed.of_all fun Fm CH => ?_
  refine GlobalTheory.BigTop.EvPt.of_forall fun x hx i p hR _ => ?_
  intro j P W hD hN w _ hWR
  have hC := Formalism.IndefR.Links.complex_data_conditions_base_level_of_primitive_links hR.ok hR.sep p.charW hR.prim
  have hst := DefFam3.toSub2_stable hC.stable
  have hin := DefFam3.toSub2_inBlock hR.prim.block
  refine ⟨Formalism.EigenvalueLevelCeiling.plc_prime w, ?_, ?_, fun k => DefFam.stable_lifts hst j _ k, DefFam.inBlock_lifts hin j _⟩
  · exact (Formalism.CohomologicalDescent.LogSmallConstantBounds.paramsLargePrime_holds P hN.1 hN.2.1 _ hWR.1).2.2.2.2.2.1
  · refine not_dvd_discr_host _ (Formalism.EigenvalueLevelCeiling.plc_prime w) ?_
    rw [← hD.special]
    exact hWR.2.2.2

end GlobalTheory.ExpTie
end

